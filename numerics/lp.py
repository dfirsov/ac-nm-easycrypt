# LP relaxation (paper, Appendix A): over all distributions of run outcomes
#   halt, refuse, or open with (R, q) in {0,1} x grid,
# subject to the first-hit constraints  E[v g_k] + Pr[halt] <= 1  for k = 1..K,
# maximise the C5_t violation  Real - (1 + t/2) B - V/(2t).
# Result (2026-10-30): no violation for t <= 1; for larger t a small violation
# only while K is small compared with (1+t)^2 (t = 4: 0.1 at K = 5, 0.002 at
# K = 10, 0 from K = 20). This is the truncation of the geometric weights.
import numpy as np
from scipy.optimize import linprog
grid = np.linspace(0, 1, 201)
def solve(t, K):
    types = [("halt", None, None), ("refuse", None, None)] + [("open", R, q) for R in (0, 1) for q in grid]
    obj = []; A = []
    for kind, R, q in types:
        if kind == "halt": obj.append(0.0)
        elif kind == "refuse": obj.append(-1/(2*t))
        else: obj.append(R - (1 + t/2)*q)
    for k in range(1, K+1):
        row = []
        for kind, R, q in types:
            if kind == "halt": row.append(1.0)
            elif kind == "refuse": row.append(0.0)
            else: row.append(R*sum((1-q)**a for a in range(k)) + (1-R)*(1-q)**(k-1))
        A.append(row)
    res = linprog(-np.array(obj), A_ub=np.array(A), b_ub=np.ones(K),
                  A_eq=np.ones((1, len(types))), b_eq=[1.0], bounds=(0, None), method="highs")
    return -res.fun
for t in [0.5, 1, 2, 4]:
    print("t =", t, " ".join(f"K={K}: {solve(t, K):.4f}" for K in [5, 10, 20, 40]))
