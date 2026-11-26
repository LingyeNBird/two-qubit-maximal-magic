#include <iostream>
#include <vector>
#include <cmath>
#include <array>
#include <map>
#include <set>
#include <random>
#include <iomanip>
#include <algorithm>
#include <fstream>
#include <numeric>
#include <string>

struct Edge { int u, v; };
const Edge EDGES[15] = {
    {0,1},{0,2},{0,3},{0,4},{0,5},
    {1,2},{1,3},{1,4},{1,5},
    {2,3},{2,4},{2,5},
    {3,4},{3,5},
    {4,5}
};
using Mat6 = std::array<std::array<double, 6>, 6>;
using RMat = std::vector<std::vector<double>>;
using Monom = std::vector<int>;

double pf4(const Mat6& A, int a, int b, int c, int d) {
    return A[a][b]*A[c][d] - A[a][c]*A[b][d] + A[a][d]*A[b][c];
}
double pf6(const Mat6& A) {
    double s = 0;
    for(int j=1;j<6;j++) {
        int r[4], idx=0;
        for(int k=1;k<6;k++) if(k!=j) r[idx++] = k;
        s += ((j%2==1) ? 1.0 : -1.0) * A[0][j] * pf4(A, r[0], r[1], r[2], r[3]);
    }
    return s;
}

std::vector<Mat6> gen_mub_pos() {
    std::vector<std::array<std::pair<int,int>, 3>> matchings;
    for(int j=1;j<6;j++) {
        std::vector<int> rem;
        for(int k=1;k<6;k++) if(k!=j) rem.push_back(k);
        int a=rem[0], b=rem[1], c=rem[2], d=rem[3];
        matchings.push_back({{{0,j},{a,b},{c,d}}});
        matchings.push_back({{{0,j},{a,c},{b,d}}});
        matchings.push_back({{{0,j},{a,d},{b,c}}});
    }
    std::vector<Mat6> res;
    for(const auto& m : matchings) {
        std::vector<int> nz_edges;
        for(int e=0;e<15;e++) {
            bool is_z = false;
            for(auto [u,v] : m) if(EDGES[e].u==u && EDGES[e].v==v) is_z = true;
            if(!is_z) nz_edges.push_back(e);
        }
        for(int mask=0; mask < (1<<12); mask++) {
            Mat6 A{};
            for(int k=0;k<12;k++) {
                double val = ((mask>>k)&1) ? 0.5 : -0.5;
                int u = EDGES[nz_edges[k]].u, v = EDGES[nz_edges[k]].v;
                A[u][v] = val; A[v][u] = -val;
            }
            bool ok = true;
            for(int i=0;i<6 && ok;i++) for(int j=i+1;j<6;j++) {
                double s=0; for(int k=0;k<6;k++) s += A[i][k]*A[j][k];
                if(std::abs(s) > 1e-9) { ok = false; break; }
            }
            if(ok && pf6(A) > 0) res.push_back(A);
        }
    }
    return res;
}

Mat6 rand_A(std::mt19937& rng) {
    std::normal_distribution<double> nd(0.0, 1.0);
    double Q[6][6];
    for(int i=0;i<6;i++) {
        for(int j=0;j<6;j++) Q[i][j] = nd(rng);
        for(int p=0;p<i;p++) {
            double ip=0; for(int j=0;j<6;j++) ip += Q[i][j]*Q[p][j];
            for(int j=0;j<6;j++) Q[i][j] -= ip*Q[p][j];
        }
        double n2=0; for(int j=0;j<6;j++) n2 += Q[i][j]*Q[i][j];
        double inv = 1.0/std::sqrt(n2);
        for(int j=0;j<6;j++) Q[i][j] *= inv;
    }
    Mat6 A{};
    for(int i=0;i<6;i++) for(int j=0;j<6;j++) {
        double s=0;
        for(int k=0;k<3;k++) s += Q[i][2*k]*Q[j][2*k+1] - Q[i][2*k+1]*Q[j][2*k];
        A[i][j] = s;
    }
    if(pf6(A) < 0) for(int k=0;k<6;k++) { A[0][k]=-A[0][k]; A[k][0]=-A[k][0]; }
    return A;
}

double eval_I4(const Mat6& A) {
    double s=0; for(int e=0;e<15;e++) { double x=A[EDGES[e].u][EDGES[e].v]; s+=x*x*x*x; } return s;
}

std::vector<Monom> gen_A_monoms(int maxdeg, const std::vector<int>& allowed_masks) {
    std::vector<Monom> res;
    std::set<int> aset(allowed_masks.begin(), allowed_masks.end());
    Monom cur;
    auto dfs = [&](auto& self, int start_e, int rem, int mask) -> void {
        if(aset.count(mask)) res.push_back(cur);
        if(rem == 0) return;
        for(int e=start_e; e<15; e++) {
            cur.push_back(e);
            int nmask = mask ^ (1 << EDGES[e].u) ^ (1 << EDGES[e].v);
            self(self, e, rem - 1, nmask);
            cur.pop_back();
        }
    };
    dfs(dfs, 0, maxdeg, 0);
    return res;
}

double eval_monom(const Mat6& A, const Monom& m) {
    double v=1.0; for(int e : m) v *= A[EDGES[e].u][EDGES[e].v]; return v;
}

Mat6 apply_signed_perm(const Mat6& A, const std::array<int,6>& p, const std::array<int,6>& s) {
    Mat6 B{};
    for(int i=0;i<6;i++) for(int j=0;j<6;j++) B[i][j] = s[i]*s[j]*A[p[i]][p[j]];
    return B;
}

void jacobi_sym(const RMat& H_in, std::vector<double>& evals, RMat& evecs) {
    int n = (int)H_in.size();
    std::vector<double> M(n*n), V(n*n, 0.0);
    for(int i=0;i<n;i++) { V[i*n+i]=1.0; for(int j=0;j<n;j++) M[i*n+j]=H_in[i][j]; }
    for(int sweep=0; sweep<16; sweep++) {
        double off=0; for(int p=0;p<n;p++) for(int q=p+1;q<n;q++) off += M[p*n+q]*M[p*n+q];
        if(off < 1e-30) break;
        for(int p=0;p<n;p++) for(int q=p+1;q<n;q++) {
            double mpq = M[p*n+q];
            if(std::abs(mpq) < 1e-16*(std::abs(M[p*n+p])+std::abs(M[q*n+q])+1e-30)) continue;
            double tau = (M[q*n+q] - M[p*n+p]) / (2.0*mpq);
            double t = (tau >= 0 ? 1.0 : -1.0) / (std::abs(tau) + std::sqrt(1.0 + tau*tau));
            double c = 1.0/std::sqrt(1.0 + t*t), s = t*c, h = t*mpq;
            M[p*n+p] -= h; M[q*n+q] += h; M[p*n+q] = M[q*n+p] = 0.0;
            for(int k=0;k<n;k++) if(k!=p && k!=q) {
                double mkp=M[k*n+p], mkq=M[k*n+q];
                M[k*n+p] = M[p*n+k] = c*mkp - s*mkq; M[k*n+q] = M[q*n+k] = s*mkp + c*mkq;
            }
            for(int k=0;k<n;k++) {
                double vkp=V[k*n+p], vkq=V[k*n+q];
                V[k*n+p] = c*vkp - s*vkq; V[k*n+q] = s*vkp + c*vkq;
            }
        }
    }
    evals.resize(n); evecs.assign(n, std::vector<double>(n));
    for(int i=0;i<n;i++) { evals[i]=M[i*n+i]; for(int j=0;j<n;j++) evecs[i][j]=V[j*n+i]; }
}

std::vector<double> solve_nnls(const std::vector<std::vector<double>>& cols, const std::vector<double>& b) {
    int n = (int)cols.size(), m = (int)b.size();
    std::vector<double> x(n, 0.0); std::vector<bool> passive(n, false);
    auto solve_ls = [&](const std::vector<int>& P) {
        int k = (int)P.size();
        std::vector<std::vector<double>> G(k, std::vector<double>(k+1, 0.0));
        for(int i=0;i<k;i++) {
            for(int j=0;j<k;j++) {
                double s=0; for(int r=0;r<m;r++) s += cols[P[i]][r]*cols[P[j]][r];
                G[i][j] = s + (i==j ? 1e-18 : 0.0);
            }
            double s=0; for(int r=0;r<m;r++) s += cols[P[i]][r]*b[r];
            G[i][k] = s;
        }
        for(int i=0;i<k;i++) {
            int piv=i; for(int r=i+1;r<k;r++) if(std::abs(G[r][i]) > std::abs(G[piv][i])) piv=r;
            std::swap(G[i], G[piv]);
            if(std::abs(G[i][i]) < 1e-22) continue;
            double inv=1.0/G[i][i]; for(int j=i;j<=k;j++) G[i][j]*=inv;
            for(int r=0;r<k;r++) if(r!=i) { double f=G[r][i]; for(int j=i;j<=k;j++) G[r][j]-=f*G[i][j]; }
        }
        std::vector<double> z(k); for(int i=0;i<k;i++) z[i]=G[i][k];
        return z;
    };
    for(int outer=0; outer<5*n+50; outer++) {
        std::vector<double> res = b;
        for(int j=0;j<n;j++) if(x[j]>0) for(int r=0;r<m;r++) res[r] -= cols[j][r]*x[j];
        int best_j=-1; double best_w=1e-14;
        for(int j=0;j<n;j++) if(!passive[j]) {
            double w=0; for(int r=0;r<m;r++) w += cols[j][r]*res[r];
            if(w > best_w) { best_w=w; best_j=j; }
        }
        if(best_j==-1) break;
        passive[best_j]=true;
        for(int inner=0; inner<5*n+20; inner++) {
            std::vector<int> P; for(int j=0;j<n;j++) if(passive[j]) P.push_back(j);
            auto z = solve_ls(P);
            double min_z=1e9; for(double v : z) min_z=std::min(min_z, v);
            if(min_z > 0.0) { std::fill(x.begin(),x.end(),0.0); for(size_t i=0;i<P.size();i++) x[P[i]]=z[i]; break; }
            double alpha=1e9;
            for(size_t i=0;i<P.size();i++) if(z[i]<=0.0) { double d=x[P[i]]-z[i]; if(d>1e-20) alpha=std::min(alpha, x[P[i]]/d); }
            if(alpha>1.0) alpha=1.0;
            for(size_t i=0;i<P.size();i++) { x[P[i]]+=alpha*(z[i]-x[P[i]]); if(x[P[i]]<=1e-15){x[P[i]]=0;passive[P[i]]=false;} }
        }
    }
    return x;
}

std::string monom_str(const Monom& m) {
    std::string s;
    for(int e : m) s += "a" + std::to_string(EDGES[e].u) + std::to_string(EDGES[e].v);
    return s;
}

int main(int argc, char** argv) {
    std::string out_path = (argc > 1) ? std::string(argv[1]) : "cert_polys.txt";

    auto mub_pos = gen_mub_pos();
    std::mt19937 rng(999);
    std::vector<Mat6> rand_As;
    for(int i=0;i<250;i++) rand_As.push_back(rand_A(rng));

    auto monoms = gen_A_monoms(4, {3, 60});
    int nM = (int)monoms.size(), nR = (int)rand_As.size();
    RMat eval_R(nM, std::vector<double>(nR));
    for(int j=0;j<nM;j++) for(int i=0;i<nR;i++) eval_R[j][i] = eval_monom(rand_As[i], monoms[j]);

    std::vector<int> order(nM); for(int i=0;i<nM;i++) order[i]=i;
    std::stable_sort(order.begin(), order.end(), [&](int a, int b){ return monoms[a].size() < monoms[b].size(); });

    RMat col_basis; std::vector<int> kept;
    for(int j : order) {
        auto col = eval_R[j];
        for(const auto& b : col_basis) {
            double ip=0; for(int i=0;i<nR;i++) ip += b[i]*col[i];
            for(int i=0;i<nR;i++) col[i] -= ip*b[i];
        }
        double n2=0; for(int i=0;i<nR;i++) n2 += col[i]*col[i];
        if(n2 > 1e-10) {
            double inv=1.0/std::sqrt(n2); for(int i=0;i<nR;i++) col[i]*=inv;
            col_basis.push_back(std::move(col)); kept.push_back(j);
        }
    }
    int dim = (int)kept.size();

    // Facial reduction: RREF on all 480 extremizers -> 46-dim sparse integer basis K_int
    RMat E(mub_pos.size(), std::vector<double>(dim));
    for(size_t i=0;i<mub_pos.size();i++)
        for(int j=0;j<dim;j++) E[i][j] = eval_monom(mub_pos[i], monoms[kept[j]]);
    std::vector<int> piv_col;
    int row = 0;
    for(int col=0; col<dim && row<(int)E.size(); col++) {
        int piv=-1; double best=1e-9;
        for(int r=row; r<(int)E.size(); r++) if(std::abs(E[r][col])>best) { best=std::abs(E[r][col]); piv=r; }
        if(piv==-1) continue;
        std::swap(E[row], E[piv]);
        double inv=1.0/E[row][col]; for(int j=col;j<dim;j++) E[row][j]*=inv;
        for(int r=0;r<(int)E.size();r++) if(r!=row && std::abs(E[r][col])>1e-12) {
            double f=E[r][col]; for(int j=col;j<dim;j++) E[r][j]-=f*E[row][j];
        }
        piv_col.push_back(col); row++;
    }
    std::set<int> pset(piv_col.begin(), piv_col.end());
    std::vector<int> free_cols;
    for(int j=0;j<dim;j++) if(!pset.count(j)) free_cols.push_back(j);

    RMat K_int;
    for(int fc : free_cols) {
        std::vector<double> v(dim, 0.0);
        v[fc] = 1.0;
        for(size_t r=0; r<piv_col.size(); r++) v[piv_col[r]] = -E[r][fc];
        int mult = 24;
        for(int m : {1, 2, 3, 4, 6, 8, 12, 24}) {
            bool ok = true;
            for(int j=0;j<dim;j++) if(std::abs(v[j]*m - std::round(v[j]*m)) > 1e-6) { ok = false; break; }
            if(ok) { mult = m; break; }
        }
        for(int j=0;j<dim;j++) v[j] = std::round(v[j]*mult);
        K_int.push_back(v);
    }
    int rk = (int)K_int.size();

    // Build S6+-averaged moment matrices M[m] in the 46-dim K_int basis
    std::vector<Mat6> tst;
    Mat6 J{}; J[0][1]=1; J[1][0]=-1; J[2][3]=1; J[3][2]=-1; J[4][5]=1; J[5][4]=-1;
    tst.push_back(J);
    for(int i=0;i<11;i++) tst.push_back(rand_A(rng));
    int nT = (int)tst.size();
    std::vector<double> tgt;
    for(const auto& A : tst) tgt.push_back(eval_I4(A) - 0.75);
    std::vector<std::array<int,6>> S6;
    { std::array<int,6> p={0,1,2,3,4,5}; do { S6.push_back(p); } while(std::next_permutation(p.begin(), p.end())); }

    std::vector<RMat> M(nT, RMat(rk, std::vector<double>(rk, 0.0)));
    for(int m=0;m<nT;m++) {
        for(const auto& p : S6) {
            int inv=0; for(int i=0;i<6;i++) for(int j=i+1;j<6;j++) if(p[i]>p[j]) inv++;
            std::array<int,6> s = {(inv&1)?-1:1, 1, 1, 1, 1, 1};
            Mat6 B = apply_signed_perm(tst[m], p, s);
            std::vector<double> mv(dim);
            for(int j=0;j<dim;j++) mv[j] = eval_monom(B, monoms[kept[j]]);
            std::vector<double> c(rk, 0.0);
            for(int i=0;i<rk;i++) { double ss=0; for(int j=0;j<dim;j++) ss+=K_int[i][j]*mv[j]; c[i]=ss; }
            for(int i=0;i<rk;i++) for(int j=i;j<rk;j++) M[m][i][j] += c[i]*c[j]/720.0;
        }
        for(int i=0;i<rk;i++) for(int j=0;j<i;j++) M[m][i][j] = M[m][j][i];
    }

    auto ray_of = [&](const std::vector<double>& u) {
        std::vector<double> nr(nT, 0.0);
        for(int m=0;m<nT;m++) {
            double s=0; for(int i=0;i<rk;i++) { double t=0; for(int j=0;j<rk;j++) t+=M[m][i][j]*u[j]; s+=u[i]*t; }
            nr[m]=s;
        }
        return nr;
    };

    std::vector<std::vector<double>> rays, ray_u;
    {
        std::vector<double> u0(rk, 0.0); u0[0] = 1.0;
        rays.push_back(ray_of(u0)); ray_u.push_back(u0);
    }
    double eps0 = 0.02;
    std::vector<double> tgt_rem = tgt;
    for(int m=0;m<nT;m++) tgt_rem[m] -= eps0 * rays[0][m];

    // Pure rank-1 Frank-Wolfe / simplicial decomposition on tgt_rem
    std::vector<double> best_w, best_rsc;
    for(int outer=0; outer<60; outer++) {
        int nR = (int)rays.size();
        std::vector<std::vector<double>> R = rays;
        std::vector<double> rsc(nR);
        for(int r=0;r<nR;r++) {
            double n2=0; for(int m=0;m<nT;m++) n2+=R[r][m]*R[r][m];
            rsc[r] = (n2>1e-24)?1.0/std::sqrt(n2):0.0;
            for(int m=0;m<nT;m++) R[r][m]*=rsc[r];
        }
        auto w = solve_nnls(R, tgt_rem);
        std::vector<double> res(nT, 0.0);
        for(int m=0;m<nT;m++) { res[m]=-tgt_rem[m]; for(int r=0;r<nR;r++) res[m]+=w[r]*R[r][m]; }
        double e2=0, t2=0; for(int m=0;m<nT;m++) { e2+=res[m]*res[m]; t2+=tgt_rem[m]*tgt_rem[m]; }
        double rel = std::sqrt(e2/t2);
        if(rel < 1e-13) {
            std::cout << "PURE RANK-1 CONVERGED at outer=" << outer << " rel_err=" << std::scientific << rel << "\n";
            best_w = w; best_rsc = rsc;
            break;
        }
        RMat H(rk, std::vector<double>(rk, 0.0));
        for(int m=0;m<nT;m++) for(int i=0;i<rk;i++) for(int j=0;j<rk;j++) H[i][j] += res[m]*M[m][i][j];
        std::vector<double> evals; RMat evecs;
        jacobi_sym(H, evals, evecs);
        int bi=0; for(int i=1;i<rk;i++) if(evals[i]<evals[bi]) bi=i;
        if(evals[bi] >= -1e-14) { std::cout << "Stopped at rel=" << rel << "\n"; break; }
        rays.push_back(ray_of(evecs[bi])); ray_u.push_back(evecs[bi]);
    }

    std::vector<std::vector<double>> active_u;
    active_u.push_back(ray_u[0]);
    for(size_t r=1; r<best_w.size(); r++) {
        if(best_w[r]*best_rsc[r] > 1e-11) active_u.push_back(ray_u[r]);
    }
    std::cout << "Number of active rank-1 polynomials (incl K[0]): " << active_u.size() << "\n";

    for(int S : {2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 30, 50}) {
        std::vector<std::vector<double>> rounded_rays;
        std::vector<std::vector<int>> rounded_u;
        for(size_t idx=0; idx<active_u.size(); idx++) {
            std::vector<int> ui(rk, 0);
            if(idx == 0) { ui[0] = 1; }
            else {
                double mx = 0; for(double x : active_u[idx]) mx = std::max(mx, std::abs(x));
                for(int k=0;k<rk;k++) ui[k] = (int)std::llround(active_u[idx][k] / mx * S);
            }
            std::vector<double> ud(rk); for(int k=0;k<rk;k++) ud[k] = (double)ui[k];
            rounded_u.push_back(ui);
            rounded_rays.push_back(ray_of(ud));
        }
        int nR = (int)rounded_rays.size();
        std::vector<std::vector<double>> R = rounded_rays;
        std::vector<double> rsc(nR);
        for(int r=0;r<nR;r++) {
            double n2=0; for(int m=0;m<nT;m++) n2+=R[r][m]*R[r][m];
            rsc[r] = (n2>1e-24)?1.0/std::sqrt(n2):0.0;
            for(int m=0;m<nT;m++) R[r][m]*=rsc[r];
        }
        auto w = solve_nnls(R, tgt);
        std::vector<double> res(nT, 0.0);
        for(int m=0;m<nT;m++) { res[m]=-tgt[m]; for(int r=0;r<nR;r++) res[m]+=w[r]*R[r][m]; }
        double e2=0, t2=0; for(int m=0;m<nT;m++) { e2+=res[m]*res[m]; t2+=tgt[m]*tgt[m]; }
        double rel = std::sqrt(e2/t2);
        double min_w = 1e9;
        for(int r=0;r<nR;r++) min_w = std::min(min_w, w[r]*rsc[r]);
        std::cout << "Round scale S=" << std::setw(2) << S << ": rel_err=" << std::scientific << std::setprecision(3) << rel
                  << "  w[K0]=" << std::fixed << std::setprecision(6) << w[0]*rsc[0]
                  << "  min_w=" << min_w << "\n";
        if(rel < 1e-12 && w[0]*rsc[0] > 1e-6) {
            std::ofstream fout(out_path);
            int cnt = 0;
            for(int r=0;r<nR;r++) {
                if(w[r]*rsc[r] < 1e-12) continue;
                cnt++;
                std::vector<long long> poly(dim, 0);
                for(int k=0;k<rk;k++) if(rounded_u[r][k] != 0)
                    for(int j=0;j<dim;j++) poly[j] += (long long)rounded_u[r][k] * (long long)std::llround(K_int[k][j]);
                long long g = 0;
                for(long long c : poly) g = std::gcd(g, std::abs(c));
                if(g > 1) for(long long& c : poly) c /= g;
                int nnz = 0;
                for(long long c : poly) if(c != 0) nnz++;
                std::cout << "  Q_" << cnt << " (nnz=" << nnz << ", approx_w=" << w[r]*rsc[r]*g*g << "): ";
                int printed = 0;
                for(int j=0;j<dim;j++) if(poly[j] != 0) {
                    fout << poly[j] << " ";
                    for(size_t t=0;t<monoms[kept[j]].size();t++) fout << (t?",":"") << monoms[kept[j]][t];
                    fout << ";";
                    if(printed < 10) { std::cout << std::showpos << poly[j] << "*" << monom_str(monoms[kept[j]]) << " "; printed++; }
                }
                if(nnz > 10) std::cout << "...";
                std::cout << std::noshowpos << "\n";
                fout << "\n";
            }
            fout.close();
            std::cout << "Saved exact integer polynomials to " << out_path << "\n";
            break;
        }
    }
    return 0;
}
