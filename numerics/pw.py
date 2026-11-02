# Pointwise inequality and mixture identities (paper, Appendix A):
#   2tR - t(2+t)q + 1 <= h_rho(R,q) = (R + (1-R) rho)/(rho + q(1-rho)),  rho = 1/(1+t)^2
#   sum_k w_k G_k(q) = 1/D,  sum_k w_k (1-q)^(k-1) = rho/D,  D = rho + q(1-rho)
# (mechanised in Sim_C5_Core.ec; this is the quick numerical check)
mind = 1e9; maxerr = 0.0
for i in range(1, 400):
    t = i/20; rho = 1/(1+t)**2
    for j in range(0, 501):
        q = j/500; D = rho + q*(1-rho)
        for R in (0, 1):
            mind = min(mind, (R + (1-R)*rho)/D - (2*t*R - t*(2+t)*q + 1))
        if i % 40 == 0 and j % 50 == 0:       # series by running sums
            G = H = 0.0; Gk = 0.0; wk = rho; pk = 1.0
            for k in range(1, 20000):
                Gk += pk                       # G_k = sum_{a<k} (1-q)^a
                G += wk*Gk; H += wk*pk         # pk = (1-q)^(k-1)
                wk *= 1-rho; pk *= 1-q
            maxerr = max(maxerr, abs(G - 1/D), abs(H - rho/D))
print("min of h_rho - lhs:", mind, "(must be >= 0; 0 = tight)")
print("max error of the mixture identities:", maxerr)
