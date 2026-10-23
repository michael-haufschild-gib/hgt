# Self-Dual Reflective Dirichlet-Polynomial Closure in the Guth–Maynard / Chen–Gupta–Li $S_2$ Tower

This directory formalizes **Mechanism 5 (Self-Dual Reflective Dirichlet-Polynomial Closure in the
Guth–Maynard / Chen–Gupta–Li $S_2$ Tower)** from `docs/reports/review-2110/argon.md` (§1.6):

1. [`SelfDualPrincipalReflectionIdentity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ReflectiveDirichletPolynomialS2/SelfDualPrincipalReflectionIdentity.lean):
   - **Signed Positive- and Negative-Frequency Principal Reflection Identities
     (`sum_fourier_pos_eq_mellin_headPoly_integral`,
     `sum_fourier_neg_eq_conj_mellin_headPoly_integral`):**
     For any smooth bump `w : CGLRealSmoothBump`, scale `N > 0`, time `t : ℝ`, and cutoff `M : ℕ`,
     the positive- and negative-frequency Poisson sums $\sum_{m=1}^M \hat{h}_t(\pm mN)$ factorize
     inside the Mellin vertical line integral into the unweighted Dirichlet head polynomial
     $D_M(\pm t - y) = \sum_{m=1}^M m^{-i(\pm t - y)}$ (`cglGMHeadPoly`) times the stationary-phase
     factor $K(\pm t - y; \log N, \log(2MN))$.
   - **Self-Dual Scale Product & Length Equalization
     (`selfDual_reflection_scale_product`, `selfDual_ceiling_length_bounds`):**
     At the self-dual scale $N = |t|^{(1+\epsilon)/2}$, the reflected length
     $M = \lceil |t|^{1+\epsilon}/N \rceil = \lceil N \rceil$ satisfies $N \le M < N + 1$.
   - **Conjugation Symmetry & Explicit Lemma 6.2 Reflection Bound
     (`gmNonzero_conj_symm_and_lemma62_bound`):**
     Packages $A(-\tau) = \overline{A(\tau)}$, $\|D_M(-\tau)\| = \|D_M(\tau)\|$, and
     `cglGM_lemma62_zeta`.

2. [`CubicTraceS2ReflectionReduction.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ReflectiveDirichletPolynomialS2/CubicTraceS2ReflectionReduction.lean):
   - **Exact $q = 1$ Plane-Diagonal Decomposition of the Chen–Gupta–Li Cubic Trace $S_2$
     (`cglTraceS2_modulusOne_eq_diag_add_offDiag`):**
     For any packet of $R$ rows at modulus $q = 1$ with distinct row times forming $W$, the $S_2$
     component of the Chen–Gupta–Li cubic Gram trace decomposes identically into the diagonal
     quadratic form $3N^3 \hat{h}_0(0)\sum_{x,y \in W} \|A(x-y)\|^2$ plus the off-diagonal triple
     sum.
   - **Single-Dyadic-Block Reflection Reduction (`cglTraceS2_modulusOne_le_single_dyadic_block`):**
     Bounds the $q = 1$ Chen–Gupta–Li cubic trace $S_2$ by a single dyadic block
     $2^j \le M \le (2T)^{1+\epsilon}/N + 1$ of the unweighted Heath–Brown pair sum
     `hbPairSum W (dyadicSegmentBlock M j) 1`.
   - **Full Off-Diagonal Nonzero Frequency Split (`cglOffDiagonalNonzero_modulusOne_split_and_bound`)**.

3. [`ShortWindowDispersionAtSeventeenThirtieths.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ReflectiveDirichletPolynomialS2/ShortWindowDispersionAtSeventeenThirtieths.lean):
   - **Unconditional `30/13` Zero-Density & Uniform `17/30` Short-Interval Prime Package
     (`guthMaynard_thirtyThirteenths_and_seventeenThirtieths_window`)**.
   - **Smooth-Tapered + Centred Prime Row Cross-Scale Dispersion up to $Q \le P^{30/17 - \delta}$
     (`exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le_seventeenThirtieths`,
     `exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le_of_range`):**
     Couples smooth-tapered higher-order Bernoulli elimination with the Guth–Maynard $17/30$
     short-interval prime theorem across $P^{1+\delta} \le Q \le P^{30/17 - \delta}$.
   - **Balanced-Regime Three-Way Equivalence with the Quasi-Riemann Hypothesis
     (`moebius_and_prime_powerWindowSaving_iff_quasiRH`):**
     `MoebiusPowerWindowSaving ↔ PrimePowerWindowSaving ↔ zetaZeroAbscissa < 1`.

4. [`MasterReflectiveDirichletPolynomialS2Theorem.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ReflectiveDirichletPolynomialS2/MasterReflectiveDirichletPolynomialS2Theorem.lean):
   - **Master Synthesis (`reflective_dirichlet_polynomial_s2_master_theorem`)**.
