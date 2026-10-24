# Open Problem 1: Pairs between lattice points

**Stage:** `3-formalized`
**Module:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/ContinuumCrossingRatioBridgeAndMultiAtomWindowLaw.lean`
**Verification:** `lake --old env lean GaloisForLFunctions/ArithmeticIncidencePositivity/ContinuumCrossingRatioBridgeAndMultiAtomWindowLaw.lean` (exit code 0, zero warnings/errors, zero `sorry`/axioms)

## 1. Problem Statement
For a crossing pair $(-a, \log n - a)$ that is not a lattice point ($a \in (0, \log n)$ arbitrary in the continuum), the divisor-lattice Gram identity does not apply directly, because $e^a$ is not an integer divisor of $n$. Open Problem 1 (§7.1, Research Topics 1 and 6 of `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md`) asks to bound the anti-diagonal atom $\Lambda(n) n^{-1/2}$ on a continuum crossing pair $(-a, \log n - a)$ by the same-side atoms at the ratios reachable from it and by the variance (the polar weight and the even strip gain), together with complete multi-atom window laws and axis-interval bounds on the unpaid set $(0, L_n) \cup (\log n - L_n, \log n)$.

## 2. Formalized Theorems and Complete Mathematical Resolution

### Part I — Exact Polar Payment Zone for Continuum Crossing Pairs and Cubic Lipschitz Suppression on the Unpaid Axis Intervals
- `unpaidInnerEnd_vonMangoldtAtom_eq`: For $n \ge 2$, the inner endpoint of the unpaid set for the anti-diagonal atom $\Lambda(n) n^{-1/2}$ alone is $\frac{2\Lambda(n)}{n - 1}$.
- `level_paid_on_middle_interval`: On the middle interval $[c, s - c]$ between the symmetric threshold points where $P_s(c) = E$, the polar weight pays the level $E$ pointwise ($E \le P_s(a)$).
- `unpaidSet_vonMangoldtAtom_eq`: For every prime power $n \ge 2$ outside `atomDominatedModuli = {2, 3, 4, 5, 7}` with $\Lambda(n) > 0$, there exists a threshold $c \in (0, \tfrac{1}{2}\log n)$ where $P_{\log n}(c) = \Lambda(n) n^{-1/2}$ such that:
  1. $\text{unpaidSet}(\log n, \Lambda(n) n^{-1/2}) = (0, c) \cup (\log n - c, \log n)$.
  2. At every continuum point $a \in [c, \log n - c]$, the polar weight pays the atom pointwise: $\Lambda(n) n^{-1/2} \le P_{\log n}(a)$.
- `integral_unpaidAxis_sq_le_cube` & `abs_le_mul_of_odd_lipschitz`: For any continuous odd $K$-Lipschitz test $F$ ($F(0) = 0$, $|F(a)| \le K a$) and any $c \ge 0$, the axis mass obeys $\int_0^c F(a)^2 \, da \le \frac{K^2 c^3}{3}$.
- `two_mul_integral_unpaidAxis_crossing_le`: For any continuous odd $K$-Lipschitz test $F$, any $c \ge 0$, any shift $L \in \mathbb{R}$, and any weight $\gamma > 0$,
  $$2 \int_0^c F(a) F(L - a) \, da \le \gamma^{-1} \frac{K^2 c^3}{3} + \gamma \int_{L - c}^L F(a)^2 \, da.$$

### Part II — Pointwise and Integrated Continuum Crossing-to-Ratio Bridge via Intermediate Same-Side Ratio Shifts
- `sq_sub_le_harmonic_step` & `sq_sub_le_one_add_mul`: For all $A, B$ with $A + B > 0$ and $u, w, v \in \mathbb{R}$, $\frac{AB}{A + B}(u - v)^2 \le A(u - w)^2 + B(w - v)^2$, and for $\theta > 0$, $(u - v)^2 \le (1 + \theta)(u - w)^2 + (1 + \theta^{-1})(w - v)^2$.
- `reflectedOddPart_sq_le_ratio_arch_step`: At every continuum point $a \in \mathbb{R}$, for every shift $L \in \mathbb{R}$, every intermediate ratio shift $\log m$, and every $\theta > 0$,
  $$4 \, \text{reflectedOddPart}(F, L, a)^2 \le (1 + \theta)(F(a) - F(a + \log m))^2 + (1 + \theta^{-1})(F(a + \log m) - F(L - a))^2.$$
- `continuum_crossing_le_variance_and_ratio_arch`: For odd $F$, at every continuum crossing pair $(-a, L - a)$,
  $$2 F(-a) F(L - a) + (F(a)^2 + F(L - a)^2) \le (1 + \theta)(F(a) - F(a + \log m))^2 + (1 + \theta^{-1})(F(a + \log m) - F(L - a))^2,$$
  decomposing the continuum crossing product into the pair variance $F(a)^2 + F(L - a)^2$, the same-side ratio jump at lag $\log m$, and the archimedean jump at distance $|L - \log m - 2a|$.
- `oddStripCost_le_ratio_and_arch_shift`: Integrating over $S_n = [\log n - r, r]$ ($\log n \le 2r$) bounds `oddStripCost F r n` by the same-side ratio jump integral at lag $\log m$ and the archimedean jump integral along $a + \log m \leftrightarrow \log n - a$.

### Part III — Weighted Two-Atom Ratio-Lag Law and Complete Multi-Atom Window Certificates at $r = 23/40$
- `sq_weighted_two_atom_le`: For any continuous compactly supported $F : \mathbb{R} \to \mathbb{R}$, weights $w_1, w_2 \in \mathbb{R}$, and shifts $a, b \in \mathbb{R}$,
  $$(w_1 A_F(a) + w_2 A_F(b))^2 \le A_F(0) \Big((w_1^2 + w_2^2) A_F(0) + 2 w_1 w_2 A_F(b - a)\Big).$$
- `sq_weighted_two_atom_sub_le` & `sq_weighted_two_atom_polarization`: Sign-flipped companion and the ratio-free polarization ceiling
  $$(w_1 A_F(a) + w_2 A_F(b))^2 + (w_1 A_F(a) - w_2 A_F(b))^2 \le 2 (w_1^2 + w_2^2) A_F(0)^2.$$
- `primeSideCharge_eq_two_three_twentyThreeFortieths`, `sq_primeSideCharge_twentyThreeFortieths_le`, & `vonMangoldtAtom_two_sq_add_three_sq_lt`: At $r = 23/40$, prices `primeSideCharge F` directly by $A_F(0)$ and the single same-side ratio lag $A_F(\log 3 - \log 2)$ with $\Lambda_2^2 + \Lambda_3^2 < 643/1000$.
- `fullZeroForm_ge_twentyThreeFortieths_complete`: Complete two-prime incidence ledger floor at $r = 23/40$ with $(1/62)\int_{S_2} F^2$ of positive strip mass to spare.

### Part IV — All-Aperture Multi-Atom Ratio-Comb Pricing of the Ledger
- `sq_primeSideCharge_le_mass_mul_combEnergy`: At every aperture $r \ge 0$, bounds $(\text{primeSideCharge } F)^2$ by $A_F(0)$ times the diagonal variance $(\sum_{n \in \text{relevantShifts } r} \Lambda_n^2) A_F(0)$ plus the same-side ratio correlations $\sum_{n \ne m} \Lambda_n \Lambda_m A_F(\log m - \log n)$.
- `fullZeroForm_eq_incidenceBudget_sub_primeSideCharge`, `two_mul_le_of_sq_le_mul`, & `fullZeroForm_ge_incidenceBudget_sub_combEnergy`: All-aperture incidence ledger identity and multi-atom ratio-comb lower bound on `fullZeroForm F`.
