import GaloisForLFunctions.BiScaleUncertainty.StationaryResolventMarkovPositivityAndNodalDefectProducer

/-!
# Euler–Poisson Chiral Drift Operator, Directed Endpoint Decomposition, Pythagorean Prime-Shift Bound, and Weight Perturbation Rigidity on `SourceGraph`

This module answers the foundational question of how the **Euler product**
($-\zeta'/\zeta(s) = \sum_{n=2}^\infty \Lambda(n) n^{-s}$) and **Poisson summation**
($\Theta(-x) = \Theta(x)$) interlock on `SourceGraph` / `MassSpace` in ways that **fail** for
perturbed positive weights $\tilde{\Lambda}(n) \ge 0$:

## Mathematical Overview

1. **The Antisymmetrized (Chiral) Euler–Poisson Identity and `oddPrimeDriftOperator` (§1)**:
   - While adding the one-sided complete theta source equation (`oneSided_source_equation`) at $x$
     and $-x$ yields the even harmonic identity (`theta_harmonic_identity`) governing
     `primeDiagonalOperator`, **subtracting** `oneSided_source_equation (-x)` from
     `oneSided_source_equation x` cancels all local diagonal constants (`-archConstantReal * Θ(x)`
     and `ν(u) Θ(x)`) identically and yields the chiral drift identity (`theta_odd_source_identity`):
     $$\int_0^\infty \operatorname{oddArchTerm}(x, u)\,du + \operatorname{oddPrimeKernelSum}(x)
       = 2x\,\Theta(x) + \int_0^\infty \operatorname{oddPolarTerm}(x, u)\,du,$$
     where by `polar_halfLine_sum` the polar integral has the closed form
     $$\int_0^\infty \operatorname{oddPolarTerm}(x, u)\,du
       = \cosh(x/2) - 2\int_0^\infty 2\cosh(u/2)\,\Theta(x+u)\,du$$
     (`integral_oddPolarTerm_eq`).
   - We prove that $\operatorname{oddPrimeKernelSum}(x)$ is strictly positive on $(0, \infty)$
     (`oddPrimeKernelSum_pos`), odd (`oddPrimeKernelSum_neg`), and bounded in absolute value by
     $\operatorname{primeKernelSum}(x)$ (`abs_oddPrimeKernelSum_le_primeKernelSum`).
   - Consequently, $\operatorname{oddPrimeDriftPotential}(x) := \operatorname{oddPrimeKernelSum}(x)/\cosh(x/2)$
     defines a bounded self-adjoint multiplication operator
     `oddPrimeDriftOperator : MassSpace →L[ℝ] MassSpace` with norm bound
     $\|\operatorname{oddPrimeDriftPotential}(x)\| \le \operatorname{primeDiagonalPotentialBound}$.

2. **Directed Edge-Endpoint Decomposition on `allPrimeMeasure`, Chiral Difference–Sum Factorization,
   and the Pythagorean Prime-Shift Uncertainty Bound (§2)**:
   - On `allPrimeMeasure`, while the **sum** of endpoint squares gives `primeDiagonalOperator`
     (`integral_allPrime_left_sq_add_right_sq`), the **difference** of right and left endpoint
     squares gives `oddPrimeDriftOperator`:
     $$\int e,\, \bigl(u(\operatorname{right} e)^2 - u(\operatorname{left} e)^2\bigr)\,d\mathrm{allPrimeMeasure}(e)
       = \langle \operatorname{oddPrimeDriftOperator} u, u\rangle_{\mathrm{MassSpace}}$$
     (`integral_allPrime_right_sq_sub_left_sq`), isolating the individual right and left endpoint
     norms as $\frac{1}{2}(\langle \operatorname{primeDiagonalOperator} u, u\rangle \pm \langle \operatorname{oddPrimeDriftOperator} u, u\rangle)$
     (`integral_allPrime_right_sq`, `integral_allPrime_left_sq`).
   - Polarizing yields the sesquilinear endpoint-difference formula
     `inner_oddPrimeDriftOperator_eq_integral`, the chiral edge difference–sum factorization
     $$\langle \operatorname{oddPrimeDriftOperator} u, u\rangle_{\mathrm{MassSpace}}
       = -\int e,\, \operatorname{difference} u\,e \cdot \bigl(u(\operatorname{left} e) + u(\operatorname{right} e)\bigr)\,d\mathrm{allPrimeMeasure}(e)$$
     (`inner_oddPrimeDriftOperator_self_eq_neg_diff_mul_sum`), and the ground-state flux identity
     $$\langle \operatorname{oddPrimeDriftOperator} u, \mathbf{1}_L\rangle_{\mathrm{MassSpace}}
       = -\int e,\, \operatorname{difference} u\,e\,d\mathrm{allPrimeMeasure}(e)$$
     (`inner_oddPrimeDriftOperator_oneL_eq_neg_integral_difference`).
   - Optimizing the nonnegative quadratic form
     $\int e,\, \bigl(\operatorname{difference} u\,e - t(u(\operatorname{left} e) + u(\operatorname{right} e))\bigr)^2\,d\mathrm{allPrimeMeasure}(e) \ge 0$
     proves the **Pythagorean Prime-Shift Uncertainty Bound**:
     $$\langle \operatorname{primeShiftOperator} u, u\rangle_{\mathrm{MassSpace}}^2
       + \langle \operatorname{oddPrimeDriftOperator} u, u\rangle_{\mathrm{MassSpace}}^2
       \le \langle \operatorname{primeDiagonalOperator} u, u\rangle_{\mathrm{MassSpace}}^2$$
     (`sq_inner_primeShiftOperator_add_sq_oddPrimeDriftOperator_le`), strictly sharpening
     $|\langle \operatorname{primeShiftOperator} u, u\rangle| \le \langle \operatorname{primeDiagonalOperator} u, u\rangle$
     whenever $\langle \operatorname{oddPrimeDriftOperator} u, u\rangle \ne 0$, together with the
     ground-state chiral flux lower bound on `primeGenerator`
     (`two_mul_sq_inner_oddPrimeDriftOperator_oneL_le`).

3. **Nodal Lobe Disjointness, Parity Anticommutation, and Equal-and-Opposite Chiral Lobe Drift (§3)**:
   - Because `oddPrimeDriftOperator` is a local multiplication operator, its cross pairing between
     `posGraph q` and `negGraph q` vanishes identically
     (`inner_oddPrimeDriftOperator_posGraph_negGraph`), so
     $$\langle \operatorname{oddPrimeDriftOperator} q.\mathrm{fst}, (\operatorname{absGraph} q).\mathrm{fst}\rangle_{\mathrm{MassSpace}}
       = \langle \operatorname{oddPrimeDriftOperator} (\operatorname{posGraph} q).\mathrm{fst}, (\operatorname{posGraph} q).\mathrm{fst}\rangle
         - \langle \operatorname{oddPrimeDriftOperator} (\operatorname{negGraph} q).\mathrm{fst}, (\operatorname{negGraph} q).\mathrm{fst}\rangle.$$
   - Because $\operatorname{oddPrimeDriftPotential}(-x) = -\operatorname{oddPrimeDriftPotential}(x)$,
     `oddPrimeDriftOperator` anticommutes with `reflectMass`
     (`inner_oddPrimeDriftOperator_reflectMass`), so $\langle \operatorname{oddPrimeDriftOperator} u, u\rangle = 0$
     for every even or odd $u$. Consequently, for every even or odd $q \in \mathrm{SourceGraph}$,
     its positive and negative lobes carry **equal and opposite** chiral drift, and on **both**
     nodal lobes the prime shift form satisfies the tightened Pythagorean bound
     $$\langle \operatorname{primeShiftOperator} (\operatorname{posGraph} q).\mathrm{fst}, (\operatorname{posGraph} q).\mathrm{fst}\rangle^2
       + \frac{1}{4}\langle \operatorname{oddPrimeDriftOperator} q.\mathrm{fst}, (\operatorname{absGraph} q).\mathrm{fst}\rangle^2
       \le \langle \operatorname{primeDiagonalOperator} (\operatorname{posGraph} q).\mathrm{fst}, (\operatorname{posGraph} q).\mathrm{fst}\rangle^2$$
     (`posGraph_primeShift_sq_add_quarter_absGraph_drift_sq_le`).

4. **Order and Single-Mode Perturbation Rigidity of the Even and Odd Euler–Poisson Identities (§4)**:
   - For any perturbed weight $w : \mathbb{N} \to \mathbb{R}$ that majorizes (or is majorized by)
     `vonMangoldtAtom` with $w(n_0) \ne \operatorname{vonMangoldtAtom}(n_0)$ at some $n_0 \ge 2$,
     the weighted symmetric kernel sum strictly violates `theta_harmonic_identity` at **every**
     $x \in \mathbb{R}$ (`weightedSymKernelSum_gt_primeKernelSum`,
     `weightedSymKernelSum_ne_harmonic_rhs`), and the weighted antisymmetric kernel sum strictly
     violates `theta_odd_source_identity` at **every** $x > 0$
     (`weightedOddKernelSum_gt_oddPrimeKernelSum`, `weightedOddKernelSum_ne_odd_source_rhs`).
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

open _root_.RHTower
open _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.CHMDClosedJump
open _root_.RHTower.CHMDTranslation
open _root_.RHTower.ThetaSourceWard
open _root_.RHTower.CHMDPolar

/-! ## Section 1: The Antisymmetrized (Chiral) Euler–Poisson Identity and `oddPrimeDriftOperator` -/

theorem oddPrimeKernelSum_neg (x : ℝ) :
    oddPrimeKernelSum (-x) = -oddPrimeKernelSum x := by
  unfold oddPrimeKernelSum
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  rw [show -x - Real.log n = -(x + Real.log n) by ring,
    show -x + Real.log n = -(x - Real.log n) by ring,
    WeilExcess.riemannKernelReal_neg, WeilExcess.riemannKernelReal_neg]
  ring

theorem oddPrimeKernelSum_zero : oddPrimeKernelSum 0 = 0 := by
  have h := oddPrimeKernelSum_neg 0
  rw [neg_zero] at h
  linarith

theorem vonMangoldtAtom_two_pos : 0 < vonMangoldtAtom 2 := by
  unfold vonMangoldtAtom
  rw [if_pos (by decide : 2 ≤ 2)]
  have hvm : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 := by
    simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  rw [hvm]
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

/-- Strict positivity of the antisymmetrized prime shift sum `oddPrimeKernelSum x` on `(0, ∞)`. -/
theorem oddPrimeKernelSum_pos {x : ℝ} (hx : 0 < x) : 0 < oddPrimeKernelSum x := by
  have hterm2 : 0 < vonMangoldtAtom 2 *
      (riemannKernelReal (x - Real.log (2 : ℕ)) - riemannKernelReal (x + Real.log (2 : ℕ))) := by
    refine mul_pos vonMangoldtAtom_two_pos ?_
    exact riemannKernelReal_sub_pos hx (Real.log_pos (by norm_num))
  have hle : vonMangoldtAtom 2 *
      (riemannKernelReal (x - Real.log (2 : ℕ)) - riemannKernelReal (x + Real.log (2 : ℕ))) ≤
      oddPrimeKernelSum x := by
    unfold oddPrimeKernelSum
    simpa using (summable_oddPrimeKernelSum x).sum_le_tsum ({2} : Finset ℕ)
      (fun n _ => oddPrimeKernelSum_term_nonneg hx n)
  exact lt_of_lt_of_le hterm2 hle

theorem oddPrimeKernelSum_le_primeKernelSum_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    oddPrimeKernelSum x ≤ primeKernelSum x := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · rw [oddPrimeKernelSum_zero]
    exact primeKernelSum_nonneg 0
  · unfold oddPrimeKernelSum primeKernelSum
    refine (summable_oddPrimeKernelSum x).tsum_le_tsum (fun n => ?_) (summable_primeKernelSum x)
    refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
    linarith [riemannKernelReal_pos (x + Real.log n)]

theorem primeKernelSum_neg (x : ℝ) : primeKernelSum (-x) = primeKernelSum x := by
  unfold primeKernelSum
  refine tsum_congr fun n => ?_
  rw [show -x + Real.log n = -(x - Real.log n) by ring,
    show -x - Real.log n = -(x + Real.log n) by ring,
    WeilExcess.riemannKernelReal_neg, WeilExcess.riemannKernelReal_neg]
  ring

/-- Global pointwise domination `|oddPrimeKernelSum x| ≤ primeKernelSum x` for all `x ∈ ℝ`. -/
theorem abs_oddPrimeKernelSum_le_primeKernelSum (x : ℝ) :
    |oddPrimeKernelSum x| ≤ primeKernelSum x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg (hx.eq_or_lt.elim (fun h => by rw [← h, oddPrimeKernelSum_zero])
      oddPrimeKernelSum_nonneg)]
    exact oddPrimeKernelSum_le_primeKernelSum_of_nonneg hx
  · have hnx : 0 ≤ -x := neg_nonneg.mpr hx
    have h1 := oddPrimeKernelSum_le_primeKernelSum_of_nonneg hnx
    rw [oddPrimeKernelSum_neg, primeKernelSum_neg] at h1
    have h2 : oddPrimeKernelSum x ≤ 0 := by
      have h3 : 0 ≤ oddPrimeKernelSum (-x) :=
        hnx.eq_or_lt.elim (fun h => by rw [← h, oddPrimeKernelSum_zero]) oddPrimeKernelSum_nonneg
      rw [oddPrimeKernelSum_neg] at h3
      linarith
    rwa [abs_of_nonpos h2]

theorem tsum_primeWeight_sub_neg (x : ℝ) :
    (∑' n : ℕ, (primeWeight n (-x) - primeWeight n x)) =
      oddPrimeKernelSum x * riemannKernelReal x := by
  rw [(summable_primeWeight (-x)).tsum_sub (summable_primeWeight x)]
  have hl : (∑' n : ℕ, primeWeight n x) =
      riemannKernelReal x * ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x + Real.log n) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by unfold primeWeight; ring
  have hr : (∑' n : ℕ, primeWeight n (-x)) =
      riemannKernelReal x * ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x - Real.log n) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    unfold primeWeight
    rw [WeilExcess.riemannKernelReal_neg,
      show -x + Real.log n = -(x - Real.log n) by ring, WeilExcess.riemannKernelReal_neg]
    ring
  rw [hr, hl, ← mul_sub,
    ← (summable_primeShift_left x).tsum_sub (summable_primeShift_right x), mul_comm]
  congr 1
  exact tsum_congr fun n => by ring

theorem measurable_oddPrimeKernelSum : Measurable oddPrimeKernelSum := by
  unfold oddPrimeKernelSum
  refine Measurable.tsum fun n => ?_
  exact (continuous_const.mul
    ((continuous_riemannKernelReal.comp (continuous_id.sub continuous_const)).sub
      (continuous_riemannKernelReal.comp (continuous_id.add continuous_const)))).measurable

/-- Closed-form identity for the antisymmetrized polar integral in `theta_odd_source_identity`:
by `polar_halfLine_sum`, the two half-line polar integrals sum to `cosh(x / 2)`, so their
difference equals `cosh(x / 2) - 2 ∫_{u > 0} 2 cosh(u / 2) Θ(x + u) du`. -/
theorem integral_oddPolarTerm_eq (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), oddPolarTerm x u) =
      Real.cosh (x / 2) -
        2 * ∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x + u) := by
  have hsum := polar_halfLine_sum x
  have h1 := (integrable_cosh_mul_theta_shift (-x)).integrableOn (s := Ioi (0 : ℝ))
  have h2 := (integrable_cosh_mul_theta_shift x).integrableOn (s := Ioi (0 : ℝ))
  have hneg : (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (-x + u)) =
      ∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x - u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [show -x + u = -(x - u) by ring, WeilExcess.riemannKernelReal_neg]
  have hdiff : (∫ u in Ioi (0 : ℝ), oddPolarTerm x u) =
      (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x - u)) -
        ∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x + u) := by
    rw [← hneg, ← integral_sub h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [oddPolarTerm]
    rw [show -x + u = -(x - u) by ring, WeilExcess.riemannKernelReal_neg]
    ring
  linarith

/-- The bounded odd prime drift multiplier
`oddPrimeDriftPotential x = oddPrimeKernelSum x / cosh(x / 2)`. -/
def oddPrimeDriftPotential (x : ℝ) : ℝ :=
  oddPrimeKernelSum x / Real.cosh (x / 2)

theorem oddPrimeDriftPotential_neg (x : ℝ) :
    oddPrimeDriftPotential (-x) = -oddPrimeDriftPotential x := by
  unfold oddPrimeDriftPotential
  rw [oddPrimeKernelSum_neg, neg_div, neg_div, Real.cosh_neg]

theorem oddPrimeDriftPotential_zero : oddPrimeDriftPotential 0 = 0 := by
  unfold oddPrimeDriftPotential
  rw [oddPrimeKernelSum_zero, zero_div]

theorem oddPrimeDriftPotential_pos {x : ℝ} (hx : 0 < x) : 0 < oddPrimeDriftPotential x :=
  div_pos (oddPrimeKernelSum_pos hx) (Real.cosh_pos (x / 2))

theorem oddPrimeDriftPotential_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ oddPrimeDriftPotential x :=
  hx.eq_or_lt.elim (fun h => by rw [← h, oddPrimeDriftPotential_zero])
    (fun h => (oddPrimeDriftPotential_pos h).le)

theorem abs_oddPrimeDriftPotential_le_primeDiagonalPotential (x : ℝ) :
    |oddPrimeDriftPotential x| ≤ primeDiagonalPotential x := by
  unfold oddPrimeDriftPotential primeDiagonalPotential
  rw [abs_div, abs_of_pos (Real.cosh_pos (x / 2))]
  exact div_le_div_of_nonneg_right (abs_oddPrimeKernelSum_le_primeKernelSum x)
    (Real.cosh_pos (x / 2)).le

theorem norm_oddPrimeDriftPotential_le (x : ℝ) :
    ‖oddPrimeDriftPotential x‖ ≤ primeDiagonalPotentialBound := by
  rw [Real.norm_eq_abs]
  exact (abs_oddPrimeDriftPotential_le_primeDiagonalPotential x).trans
    (primeKernelSum_div_cosh_le x)

theorem measurable_oddPrimeDriftPotential : Measurable oddPrimeDriftPotential :=
  measurable_oddPrimeKernelSum.div
    (Real.continuous_cosh.comp (continuous_id.div_const 2)).measurable

/-- **Exact Chiral Euler–Poisson Formula for `oddPrimeDriftPotential`**:
for every `x : ℝ`, `oddPrimeDriftPotential x` is uniquely determined by the linear drift
`2 x Θ(x)`, the odd polar integral, and the odd archimedean integral. -/
theorem oddPrimeDriftPotential_eq_euler_poisson (x : ℝ) :
    oddPrimeDriftPotential x =
      (2 * x * riemannKernelReal x + (∫ u in Ioi (0 : ℝ), oddPolarTerm x u) -
        ∫ u in Ioi (0 : ℝ), oddArchTerm x u) / Real.cosh (x / 2) := by
  unfold oddPrimeDriftPotential
  have h := theta_odd_source_identity x
  congr 1
  linarith

/-- **The Bounded Self-Adjoint Chiral Prime Drift Operator on `MassSpace`**:
multiplies by `oddPrimeDriftPotential x = oddPrimeKernelSum x / cosh(x / 2)`. -/
def oddPrimeDriftOperator : MassSpace →L[ℝ] MassSpace :=
  lpBoundedMulCLM measurable_oddPrimeDriftPotential primeDiagonalPotentialBound_nonneg
    norm_oddPrimeDriftPotential_le

theorem oddPrimeDriftOperator_ae (u : MassSpace) :
    oddPrimeDriftOperator u =ᵐ[massMeasure] fun x => oddPrimeDriftPotential x * u x :=
  lpBoundedMulCLM_coeFn _ _ _ u

theorem oddPrimeDriftOperator_symmetric (u v : MassSpace) :
    ⟪oddPrimeDriftOperator u, v⟫_ℝ = ⟪u, oddPrimeDriftOperator v⟫_ℝ :=
  lpBoundedMulCLM_inner_real _ _ _ (fun _ => rfl) u v

theorem oddPrimeDriftOperator_isSelfAdjoint : IsSelfAdjoint oddPrimeDriftOperator :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr oddPrimeDriftOperator_symmetric

theorem inner_oddPrimeDriftOperator (u v : MassSpace) :
    ⟪oddPrimeDriftOperator u, v⟫_ℝ =
      ∫ x, oddPrimeDriftPotential x * u x * v x ∂massMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [oddPrimeDriftOperator_ae u] with x hx
  simp only [hx, RCLike.inner_apply', conj_trivial]

theorem inner_oddPrimeDriftOperator_self (u : MassSpace) :
    ⟪oddPrimeDriftOperator u, u⟫_ℝ =
      ∫ x, oddPrimeDriftPotential x * u x ^ 2 ∂massMeasure := by
  rw [inner_oddPrimeDriftOperator]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem inner_oddPrimeDriftOperator_self_eq_volume (u : MassSpace) :
    ⟪oddPrimeDriftOperator u, u⟫_ℝ =
      ∫ x, oddPrimeKernelSum x * riemannKernelReal x * u x ^ 2 := by
  rw [inner_oddPrimeDriftOperator_self, integral_mass]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold massDensity oddPrimeDriftPotential
  have hch : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos (x / 2)).ne'
  field_simp [hch]

theorem abs_inner_oddPrimeDriftOperator_self_le_primeDiagonal (u : MassSpace) :
    |⟪oddPrimeDriftOperator u, u⟫_ℝ| ≤ ⟪primeDiagonalOperator u, u⟫_ℝ := by
  rw [inner_oddPrimeDriftOperator_self, inner_primeDiagonalOperator_self]
  have hint_d : Integrable (fun x => primeDiagonalPotential x * u x ^ 2) massMeasure := by
    refine (L2.integrable_inner (primeDiagonalOperator u) u).congr ?_
    filter_upwards [primeDiagonalOperator_ae u] with x hx
    simp only [hx, RCLike.inner_apply', conj_trivial]
    ring
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hint_d ?_
  filter_upwards [] with x
  change |oddPrimeDriftPotential x * u x ^ 2| ≤ primeDiagonalPotential x * u x ^ 2
  rw [abs_mul, abs_of_nonneg (sq_nonneg (u x))]
  exact mul_le_mul_of_nonneg_right (abs_oddPrimeDriftPotential_le_primeDiagonalPotential x)
    (sq_nonneg _)

/-! ## Section 2: Directed Edge-Endpoint Decomposition on `allPrimeMeasure`, Chiral Difference–Sum Factorization, and the Pythagorean Prime-Shift Bound -/

/-- **Directed Edge-Endpoint Difference Formula on `allPrimeMeasure`**:
while the sum of endpoint squares gives `⟪primeDiagonalOperator u, u⟫_ℝ`, the difference of right
and left endpoint squares gives `⟪oddPrimeDriftOperator u, u⟫_ℝ`. -/
theorem integral_allPrime_right_sq_sub_left_sq (u : MassSpace) :
    (∫ e, (u (right e) ^ 2 - u (left e) ^ 2) ∂allPrimeMeasure) =
      ⟪oddPrimeDriftOperator u, u⟫_ℝ := by
  have haeL : AEMeasurable left allPrimeMeasure := measurable_snd.aemeasurable
  have haeR : AEMeasurable right allPrimeMeasure := (measurable_snd.add measurable_fst).aemeasurable
  have hmeasL : Measurable fun x : ℝ => ∑' n : ℕ, primeWeight n x :=
    Measurable.tsum fun n => (CHMDDoobGraph.continuous_primeWeight n).measurable
  have hmeasR : Measurable fun x : ℝ => ∑' n : ℕ, primeWeight n (-x) :=
    Measurable.tsum fun n => ((CHMDDoobGraph.continuous_primeWeight n).comp continuous_neg).measurable
  have hL : (∫ e, u (left e) ^ 2 ∂allPrimeMeasure) =
      ∫ x, (∑' n : ℕ, primeWeight n x) * u x ^ 2 := by
    have hm : AEStronglyMeasurable (fun x : ℝ => u x ^ 2) (Measure.map left allPrimeMeasure) :=
      ((Lp.aestronglyMeasurable u).pow 2).mono_ac
        (Measure.absolutelyContinuous_of_le_smul map_allPrime_left_le)
    change (∫ e, (fun x : ℝ => u x ^ 2) (left e) ∂allPrimeMeasure) = _
    rw [← integral_map haeL hm, Measure.map_sum haeL]
    simp_rw [map_prime_left]
    rw [← withDensity_tsum (fun n => (CHMDDoobGraph.continuous_primeWeight n).measurable.ennreal_ofReal),
      tsum_ofReal_primeWeight,
      integral_weighted volume hmeasL
        (Eventually.of_forall fun x => tsum_nonneg fun n => primeWeight_nonneg n x)]
  have hR : (∫ e, u (right e) ^ 2 ∂allPrimeMeasure) =
      ∫ x, (∑' n : ℕ, primeWeight n (-x)) * u x ^ 2 := by
    have hm : AEStronglyMeasurable (fun x : ℝ => u x ^ 2) (Measure.map right allPrimeMeasure) :=
      ((Lp.aestronglyMeasurable u).pow 2).mono_ac
        (Measure.absolutelyContinuous_of_le_smul map_allPrime_right_le)
    change (∫ e, (fun x : ℝ => u x ^ 2) (right e) ∂allPrimeMeasure) = _
    rw [← integral_map haeR hm, Measure.map_sum haeR]
    simp_rw [map_prime_right]
    rw [← withDensity_tsum (fun n => show Measurable
        (fun x : ℝ => ENNReal.ofReal (primeWeight n (-x))) from
          ((CHMDDoobGraph.continuous_primeWeight n).comp continuous_neg).measurable.ennreal_ofReal),
      tsum_ofReal_primeWeight_neg,
      integral_weighted volume hmeasR
        (Eventually.of_forall fun x => tsum_nonneg fun n => primeWeight_nonneg n (-x))]
  have hintL : Integrable (fun x => (∑' n : ℕ, primeWeight n x) * u x ^ 2) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => u x ^ 2) (Measure.map left allPrimeMeasure) :=
      ((Lp.aestronglyMeasurable u).pow 2).mono_ac
        (Measure.absolutelyContinuous_of_le_smul map_allPrime_left_le)
    have hi := (integrable_map_measure hm haeL).mpr (integrable_allPrime_left_sq u)
    rw [Measure.map_sum haeL] at hi
    simp_rw [map_prime_left] at hi
    rw [← withDensity_tsum (fun n => (CHMDDoobGraph.continuous_primeWeight n).measurable.ennreal_ofReal),
      tsum_ofReal_primeWeight] at hi
    exact (integrable_weighted_iff volume hmeasL
      (Eventually.of_forall fun x => tsum_nonneg fun n => primeWeight_nonneg n x) _).mp hi
  have hintR : Integrable (fun x => (∑' n : ℕ, primeWeight n (-x)) * u x ^ 2) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => u x ^ 2) (Measure.map right allPrimeMeasure) :=
      ((Lp.aestronglyMeasurable u).pow 2).mono_ac
        (Measure.absolutelyContinuous_of_le_smul map_allPrime_right_le)
    have hi := (integrable_map_measure hm haeR).mpr (integrable_allPrime_right_sq u)
    rw [Measure.map_sum haeR] at hi
    simp_rw [map_prime_right] at hi
    rw [← withDensity_tsum (fun n => show Measurable
        (fun x : ℝ => ENNReal.ofReal (primeWeight n (-x))) from
          ((CHMDDoobGraph.continuous_primeWeight n).comp continuous_neg).measurable.ennreal_ofReal),
      tsum_ofReal_primeWeight_neg] at hi
    exact (integrable_weighted_iff volume hmeasR
      (Eventually.of_forall fun x => tsum_nonneg fun n => primeWeight_nonneg n (-x)) _).mp hi
  rw [integral_sub (integrable_allPrime_right_sq u) (integrable_allPrime_left_sq u),
    hR, hL, ← integral_sub hintR hintL, inner_oddPrimeDriftOperator_self_eq_volume]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← sub_mul, ← (summable_primeWeight (-x)).tsum_sub (summable_primeWeight x),
    tsum_primeWeight_sub_neg x]

/-- Exact individual right-endpoint norm on `allPrimeMeasure`. -/
theorem integral_allPrime_right_sq (u : MassSpace) :
    (∫ e, u (right e) ^ 2 ∂allPrimeMeasure) =
      (⟪primeDiagonalOperator u, u⟫_ℝ + ⟪oddPrimeDriftOperator u, u⟫_ℝ) / 2 := by
  have hsum := integral_allPrime_left_sq_add_right_sq u
  have hdiff := integral_allPrime_right_sq_sub_left_sq u
  rw [integral_add (integrable_allPrime_left_sq u) (integrable_allPrime_right_sq u)] at hsum
  rw [integral_sub (integrable_allPrime_right_sq u) (integrable_allPrime_left_sq u)] at hdiff
  linarith

/-- Exact individual left-endpoint norm on `allPrimeMeasure`. -/
theorem integral_allPrime_left_sq (u : MassSpace) :
    (∫ e, u (left e) ^ 2 ∂allPrimeMeasure) =
      (⟪primeDiagonalOperator u, u⟫_ℝ - ⟪oddPrimeDriftOperator u, u⟫_ℝ) / 2 := by
  have hsum := integral_allPrime_left_sq_add_right_sq u
  have hdiff := integral_allPrime_right_sq_sub_left_sq u
  rw [integral_add (integrable_allPrime_left_sq u) (integrable_allPrime_right_sq u)] at hsum
  rw [integral_sub (integrable_allPrime_right_sq u) (integrable_allPrime_left_sq u)] at hdiff
  linarith

theorem integrable_allPrime_left_mul_left (u v : MassSpace) :
    Integrable (fun e => u (left e) * v (left e)) allPrimeMeasure :=
  (memLp_allPrime_left (Lp.memLp u)).integrable_mul (memLp_allPrime_left (Lp.memLp v))

theorem integrable_allPrime_right_mul_right (u v : MassSpace) :
    Integrable (fun e => u (right e) * v (right e)) allPrimeMeasure :=
  (memLp_allPrime_right (Lp.memLp u)).integrable_mul (memLp_allPrime_right (Lp.memLp v))

/-- **Polarized `allPrimeMeasure` Endpoint-Difference Formula for `oddPrimeDriftOperator`**:
for all `u, v : MassSpace`,
`⟪oddPrimeDriftOperator u, v⟫_ℝ = ∫ e, (u (right e) * v (right e) - u (left e) * v (left e)) ∂allPrimeMeasure`. -/
theorem inner_oddPrimeDriftOperator_eq_integral (u v : MassSpace) :
    ⟪oddPrimeDriftOperator u, v⟫_ℝ =
      ∫ e, (u (right e) * v (right e) - u (left e) * v (left e)) ∂allPrimeMeasure := by
  have hpol : 2 * ⟪oddPrimeDriftOperator u, v⟫_ℝ =
      ⟪oddPrimeDriftOperator (u + v), u + v⟫_ℝ -
        ⟪oddPrimeDriftOperator u, u⟫_ℝ - ⟪oddPrimeDriftOperator v, v⟫_ℝ := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right,
      real_inner_comm v (oddPrimeDriftOperator u), oddPrimeDriftOperator_symmetric v u]
    ring
  have h_uv := (integral_allPrime_right_sq_sub_left_sq (u + v)).symm
  have h_u := (integral_allPrime_right_sq_sub_left_sq u).symm
  have h_v := (integral_allPrime_right_sq_sub_left_sq v).symm
  have hint_u : Integrable (fun e => u (right e) ^ 2 - u (left e) ^ 2) allPrimeMeasure :=
    (integrable_allPrime_right_sq u).sub (integrable_allPrime_left_sq u)
  have hint_v : Integrable (fun e => v (right e) ^ 2 - v (left e) ^ 2) allPrimeMeasure :=
    (integrable_allPrime_right_sq v).sub (integrable_allPrime_left_sq v)
  have hint_uv : Integrable
      (fun e => (u (right e) ^ 2 - u (left e) ^ 2) + (v (right e) ^ 2 - v (left e) ^ 2))
      allPrimeMeasure := hint_u.add hint_v
  have hint_cross : Integrable
      (fun e => u (right e) * v (right e) - u (left e) * v (left e)) allPrimeMeasure :=
    (integrable_allPrime_right_mul_right u v).sub (integrable_allPrime_left_mul_left u v)
  have hint_cross2 : Integrable
      (fun e => 2 * (u (right e) * v (right e) - u (left e) * v (left e))) allPrimeMeasure :=
    hint_cross.const_mul 2
  have h_add_ae : (fun e => (u + v) (right e) ^ 2 - (u + v) (left e) ^ 2) =ᵐ[allPrimeMeasure]
      fun e => (u (right e) ^ 2 - u (left e) ^ 2) + (v (right e) ^ 2 - v (left e) ^ 2) +
        2 * (u (right e) * v (right e) - u (left e) * v (left e)) := by
    filter_upwards [nonsingular_allPrime_left.ae_eq_comp (Lp.coeFn_add u v),
      nonsingular_allPrime_right.ae_eq_comp (Lp.coeFn_add u v)] with e hl hr
    simp only [Function.comp_apply, Pi.add_apply] at hl hr
    rw [hl, hr]
    ring
  have h_int_add : (∫ e, ((u + v) (right e) ^ 2 - (u + v) (left e) ^ 2) ∂allPrimeMeasure) =
      (∫ e, (u (right e) ^ 2 - u (left e) ^ 2) ∂allPrimeMeasure) +
        (∫ e, (v (right e) ^ 2 - v (left e) ^ 2) ∂allPrimeMeasure) +
        2 * ∫ e, (u (right e) * v (right e) - u (left e) * v (left e)) ∂allPrimeMeasure := by
    rw [integral_congr_ae h_add_ae, integral_add hint_uv hint_cross2,
      integral_add hint_u hint_v, integral_const_mul]
  linarith

/-- **Chiral Edge Difference–Sum Factorization (`R^* R - L^* L = -D^* S`)**:
for every `u : MassSpace`,
`⟪oddPrimeDriftOperator u, u⟫_ℝ = -∫ e, difference u e * (u (left e) + u (right e)) ∂allPrimeMeasure`. -/
theorem inner_oddPrimeDriftOperator_self_eq_neg_diff_mul_sum (u : MassSpace) :
    ⟪oddPrimeDriftOperator u, u⟫_ℝ =
      -∫ e, difference u e * (u (left e) + u (right e)) ∂allPrimeMeasure := by
  rw [← integral_allPrime_right_sq_sub_left_sq u, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with e
  change u (right e) ^ 2 - u (left e) ^ 2 =
    -((u (left e) - u (right e)) * (u (left e) + u (right e)))
  ring

theorem oneL_ae : (oneL : ℝ → ℝ) =ᵐ[massMeasure] fun _ : ℝ => (1 : ℝ) :=
  (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp

/-- **Exact Ground-State Chiral Flux Identity**:
for every `u : MassSpace`, pairing `oddPrimeDriftOperator u` against `oneL` equals minus the total
prime-edge difference integral `-∫ e, difference u e ∂allPrimeMeasure`. -/
theorem inner_oddPrimeDriftOperator_oneL_eq_neg_integral_difference (u : MassSpace) :
    ⟪oddPrimeDriftOperator u, oneL⟫_ℝ =
      -∫ e, difference u e ∂allPrimeMeasure := by
  rw [inner_oddPrimeDriftOperator_eq_integral u oneL, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [nonsingular_allPrime_left.ae_eq_comp oneL_ae,
    nonsingular_allPrime_right.ae_eq_comp oneL_ae] with e hl hr
  have hl' : oneL (left e) = 1 := hl
  have hr' : oneL (right e) = 1 := hr
  change u (right e) * oneL (right e) - u (left e) * oneL (left e) =
    -(u (left e) - u (right e))
  rw [hl', hr']
  ring

/-- The sum of endpoint values satisfies
`∫ e, (u (left e) + u (right e)) ^ 2 ∂allPrimeMeasure = ⟪primeDiagonalOperator u, u⟫_ℝ + ⟪primeShiftOperator u, u⟫_ℝ`. -/
theorem integral_allPrime_left_add_right_sq (u : MassSpace) :
    (∫ e, (u (left e) + u (right e)) ^ 2 ∂allPrimeMeasure) =
      ⟪primeDiagonalOperator u, u⟫_ℝ + ⟪primeShiftOperator u, u⟫_ℝ := by
  have hint_sum : Integrable (fun e => u (left e) ^ 2 + u (right e) ^ 2) allPrimeMeasure :=
    (integrable_allPrime_left_sq u).add (integrable_allPrime_right_sq u)
  have hint_cross : Integrable (fun e => 2 * (u (left e) * u (right e))) allPrimeMeasure :=
    (integrable_allPrime_left_mul_right u u).const_mul 2
  rw [← integral_allPrime_left_sq_add_right_sq u, inner_primeShiftOperator_self_eq_integral,
    ← integral_const_mul, ← integral_add hint_sum hint_cross]
  apply integral_congr_ae
  filter_upwards [] with e
  ring

/-- Parameterized quadratic nonnegativity of `(difference u e - t * (u (left e) + u (right e)))²`
on `allPrimeMeasure`. -/
theorem primeGenerator_add_two_mul_oddPrimeDrift_add_sq_nonneg (u : MassSpace) (t : ℝ) :
    0 ≤ ⟪primeGenerator u, u⟫_ℝ + 2 * t * ⟪oddPrimeDriftOperator u, u⟫_ℝ +
      t ^ 2 * (⟪primeDiagonalOperator u, u⟫_ℝ + ⟪primeShiftOperator u, u⟫_ℝ) := by
  have hint_diff : Integrable (fun e => difference u e ^ 2) allPrimeMeasure :=
    (memLp_allPrime_difference (Lp.memLp u)).integrable_sq
  have hint_mid : Integrable (fun e => u (right e) ^ 2 - u (left e) ^ 2) allPrimeMeasure :=
    (integrable_allPrime_right_sq u).sub (integrable_allPrime_left_sq u)
  have hint_mid2 : Integrable
      (fun e => (2 * t) * (u (right e) ^ 2 - u (left e) ^ 2)) allPrimeMeasure :=
    hint_mid.const_mul (2 * t)
  have hint_dm : Integrable
      (fun e => difference u e ^ 2 + (2 * t) * (u (right e) ^ 2 - u (left e) ^ 2))
      allPrimeMeasure := hint_diff.add hint_mid2
  have hint_sum : Integrable (fun e => (u (left e) + u (right e)) ^ 2) allPrimeMeasure := by
    refine ((integrable_allPrime_left_sq u).add (integrable_allPrime_right_sq u) |>.add
      ((integrable_allPrime_left_mul_right u u).const_mul 2)).congr ?_
    filter_upwards [] with e
    dsimp only [Pi.add_apply]
    ring
  have hint_sum2 : Integrable
      (fun e => t ^ 2 * (u (left e) + u (right e)) ^ 2) allPrimeMeasure :=
    hint_sum.const_mul (t ^ 2)
  have h1 : (∫ e, difference u e ^ 2 ∂allPrimeMeasure) = ⟪primeGenerator u, u⟫_ℝ := by
    rw [inner_primeGenerator_eq_integral]
    simp only [← pow_two]
  have hnonneg : 0 ≤ ∫ e, (difference u e - t * (u (left e) + u (right e))) ^ 2 ∂allPrimeMeasure :=
    integral_nonneg fun _ => sq_nonneg _
  have heq : (fun e => (difference u e - t * (u (left e) + u (right e))) ^ 2) =
      fun e => (difference u e ^ 2 + (2 * t) * (u (right e) ^ 2 - u (left e) ^ 2)) +
        t ^ 2 * (u (left e) + u (right e)) ^ 2 := by
    funext e
    change ((u (left e) - u (right e)) - t * (u (left e) + u (right e))) ^ 2 =
      (u (left e) - u (right e)) ^ 2 + (2 * t) * (u (right e) ^ 2 - u (left e) ^ 2) +
        t ^ 2 * (u (left e) + u (right e)) ^ 2
    ring
  rw [heq, integral_add hint_dm hint_sum2, integral_add hint_diff hint_mid2,
    integral_const_mul, integral_const_mul,
    h1, integral_allPrime_right_sq_sub_left_sq u,
    integral_allPrime_left_add_right_sq u] at hnonneg
  exact hnonneg

/-- **Chiral Difference–Sum Uncertainty Inequality**:
for every `u : MassSpace`,
`⟪oddPrimeDriftOperator u, u⟫_ℝ ^ 2 ≤ ⟪primeGenerator u, u⟫_ℝ * (⟪primeDiagonalOperator u, u⟫_ℝ + ⟪primeShiftOperator u, u⟫_ℝ)`. -/
theorem sq_inner_oddPrimeDriftOperator_self_le (u : MassSpace) :
    ⟪oddPrimeDriftOperator u, u⟫_ℝ ^ 2 ≤
      ⟪primeGenerator u, u⟫_ℝ *
        (⟪primeDiagonalOperator u, u⟫_ℝ + ⟪primeShiftOperator u, u⟫_ℝ) := by
  set A := ⟪primeDiagonalOperator u, u⟫_ℝ + ⟪primeShiftOperator u, u⟫_ℝ
  set B := ⟪oddPrimeDriftOperator u, u⟫_ℝ
  set C := ⟪primeGenerator u, u⟫_ℝ
  have hA : 0 ≤ A := by
    dsimp [A]
    rw [← integral_allPrime_left_add_right_sq u]
    exact integral_nonneg fun _ => sq_nonneg _
  rcases eq_or_lt_of_le hA with hA0 | hA_pos
  · have hq := primeGenerator_add_two_mul_oddPrimeDrift_add_sq_nonneg u
    have hB0 : B = 0 := by
      by_contra hBne
      have h := hq (-(C + 1) / (2 * B))
      change 0 ≤ C + 2 * (-(C + 1) / (2 * B)) * B + (-(C + 1) / (2 * B)) ^ 2 * A at h
      rw [← hA0, mul_zero, add_zero] at h
      have hmul : 2 * (-(C + 1) / (2 * B)) * B = -(C + 1) := by
        field_simp [hBne]
      linarith
    rw [hB0, ← hA0]
    simp
  · have hq := primeGenerator_add_two_mul_oddPrimeDrift_add_sq_nonneg u (-B / A)
    change 0 ≤ C + 2 * (-B / A) * B + (-B / A) ^ 2 * A at hq
    have hmul := mul_le_mul_of_nonneg_left hq hA_pos.le
    have hid : A * (C + 2 * (-B / A) * B + (-B / A) ^ 2 * A) = A * C - B ^ 2 := by
      field_simp [hA_pos.ne']
      ring
    rw [mul_zero, hid] at hmul
    linarith

/-- **The Pythagorean Prime-Shift Uncertainty Bound**:
for every `u : MassSpace`,
`⟪primeShiftOperator u, u⟫_ℝ ^ 2 + ⟪oddPrimeDriftOperator u, u⟫_ℝ ^ 2 ≤ ⟪primeDiagonalOperator u, u⟫_ℝ ^ 2`.
In particular, whenever `⟪oddPrimeDriftOperator u, u⟫_ℝ ≠ 0`, `|⟪primeShiftOperator u, u⟫_ℝ|` is
strictly smaller than `⟪primeDiagonalOperator u, u⟫_ℝ`. -/
theorem sq_inner_primeShiftOperator_add_sq_oddPrimeDriftOperator_le (u : MassSpace) :
    ⟪primeShiftOperator u, u⟫_ℝ ^ 2 + ⟪oddPrimeDriftOperator u, u⟫_ℝ ^ 2 ≤
      ⟪primeDiagonalOperator u, u⟫_ℝ ^ 2 := by
  have h1 := sq_inner_oddPrimeDriftOperator_self_le u
  have h2 : ⟪primeGenerator u, u⟫_ℝ =
      ⟪primeDiagonalOperator u, u⟫_ℝ - ⟪primeShiftOperator u, u⟫_ℝ := by
    rw [← primeDiagonal_sub_primeShift_eq_primeGenerator, sub_apply,
      inner_sub_left]
  rw [h2] at h1
  nlinarith

/-- **Ground-State Chiral Flux Lower Bound on `primeGenerator`**:
for every `u : MassSpace`,
`2 * ⟪oddPrimeDriftOperator u, oneL⟫_ℝ ^ 2 ≤ ⟪primeDiagonalOperator oneL, oneL⟫_ℝ * ⟪primeGenerator u, u⟫_ℝ`. -/
theorem two_mul_sq_inner_oddPrimeDriftOperator_oneL_le (u : MassSpace) :
    2 * ⟪oddPrimeDriftOperator u, oneL⟫_ℝ ^ 2 ≤
      ⟪primeDiagonalOperator oneL, oneL⟫_ℝ * ⟪primeGenerator u, u⟫_ℝ := by
  set D := ⟪primeDiagonalOperator oneL, oneL⟫_ℝ
  set F := ⟪oddPrimeDriftOperator u, oneL⟫_ℝ
  set G := ⟪primeGenerator u, u⟫_ℝ
  have hq : ∀ t : ℝ, 0 ≤ G - 2 * t * F + (t ^ 2 / 2) * D := by
    intro t
    have hint_diff : Integrable (fun e => difference u e ^ 2) allPrimeMeasure :=
      (memLp_allPrime_difference (Lp.memLp u)).integrable_sq
    have hint_mid : Integrable (fun e => u (right e) * oneL (right e) -
        u (left e) * oneL (left e)) allPrimeMeasure :=
      (integrable_allPrime_right_mul_right u oneL).sub (integrable_allPrime_left_mul_left u oneL)
    have hint_mid2 : Integrable
        (fun e => (2 * t) * (u (right e) * oneL (right e) - u (left e) * oneL (left e)))
        allPrimeMeasure := hint_mid.const_mul (2 * t)
    have hint_dm : Integrable
        (fun e => difference u e ^ 2 -
          (2 * t) * (u (right e) * oneL (right e) - u (left e) * oneL (left e)))
        allPrimeMeasure := hint_diff.sub hint_mid2
    have hint_one : Integrable (fun e => oneL (left e) ^ 2 + oneL (right e) ^ 2) allPrimeMeasure :=
      (integrable_allPrime_left_sq oneL).add (integrable_allPrime_right_sq oneL)
    have hint_one2 : Integrable
        (fun e => (t ^ 2 / 2) * (oneL (left e) ^ 2 + oneL (right e) ^ 2))
        allPrimeMeasure := hint_one.const_mul (t ^ 2 / 2)
    have hG : (∫ e, difference u e ^ 2 ∂allPrimeMeasure) = G := by
      dsimp [G]
      rw [inner_primeGenerator_eq_integral]
      simp only [← pow_two]
    have hF : (∫ e, (u (right e) * oneL (right e) - u (left e) * oneL (left e)) ∂allPrimeMeasure) = F :=
      (inner_oddPrimeDriftOperator_eq_integral u oneL).symm
    have hD : (∫ e, (oneL (left e) ^ 2 + oneL (right e) ^ 2) ∂allPrimeMeasure) = D :=
      integral_allPrime_left_sq_add_right_sq oneL
    have hnonneg : 0 ≤ ∫ e,
        ((difference u e ^ 2 - (2 * t) * (u (right e) * oneL (right e) - u (left e) * oneL (left e))) +
          (t ^ 2 / 2) * (oneL (left e) ^ 2 + oneL (right e) ^ 2)) ∂allPrimeMeasure := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [nonsingular_allPrime_left.ae_eq_comp oneL_ae,
        nonsingular_allPrime_right.ae_eq_comp oneL_ae] with e hl hr
      have hl' : oneL (left e) = 1 := hl
      have hr' : oneL (right e) = 1 := hr
      change 0 ≤ (difference u e ^ 2 - (2 * t) * (u (right e) * oneL (right e) - u (left e) * oneL (left e))) +
        (t ^ 2 / 2) * (oneL (left e) ^ 2 + oneL (right e) ^ 2)
      rw [hl', hr']
      have hid : (difference u e ^ 2 - (2 * t) * (u (right e) * 1 - u (left e) * 1)) +
          (t ^ 2 / 2) * (1 ^ 2 + 1 ^ 2) = (difference u e + t) ^ 2 := by
        change ((u (left e) - u (right e)) ^ 2 - (2 * t) * (u (right e) * 1 - u (left e) * 1)) +
          (t ^ 2 / 2) * (1 ^ 2 + 1 ^ 2) = (u (left e) - u (right e) + t) ^ 2
        ring
      rw [hid]
      exact sq_nonneg _
    rw [integral_add hint_dm hint_one2, integral_sub hint_diff hint_mid2,
      integral_const_mul, integral_const_mul, hG, hF, hD] at hnonneg
    exact hnonneg
  have hD_nonneg : 0 ≤ D := primeDiagonalOperator_isPositive.inner_nonneg_left oneL
  rcases eq_or_lt_of_le hD_nonneg with hD0 | hD_pos
  · have hF0 : F = 0 := by
      by_contra hFne
      have h := hq ((G + 1) / (2 * F))
      rw [← hD0, mul_zero, add_zero] at h
      have hmul : 2 * ((G + 1) / (2 * F)) * F = G + 1 := by field_simp [hFne]
      linarith
    rw [hF0, ← hD0]
    simp
  · have h := hq (2 * F / D)
    have hmul := mul_le_mul_of_nonneg_left h hD_pos.le
    have hid : D * (G - 2 * (2 * F / D) * F + (2 * F / D) ^ 2 / 2 * D) = D * G - 2 * F ^ 2 := by
      field_simp [hD_pos.ne']
      ring
    rw [mul_zero, hid] at hmul
    linarith

/-! ## Section 3: Nodal Lobe Disjointness, Parity Anticommutation, and Equal-and-Opposite Chiral Lobe Drift -/

/-- Because `oddPrimeDriftOperator` is a pointwise multiplication operator, its bilinear form
vanishes identically between `posGraph q` and `negGraph q`. -/
theorem inner_oddPrimeDriftOperator_posGraph_negGraph (q : SourceGraph) :
    ⟪oddPrimeDriftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = 0 := by
  rw [inner_oddPrimeDriftOperator]
  have hae : (fun x => oddPrimeDriftPotential x * (posGraph q).val.fst x * (negGraph q).val.fst x)
      =ᵐ[massMeasure] fun _ => (0 : ℝ) := by
    filter_upwards [posGraph_fst_ae q, negGraph_fst_ae q] with x hp hn
    rw [hp, hn, mul_assoc, posFun_mul_negFun, mul_zero]
  rw [integral_congr_ae hae, integral_zero]

/-- Nodal lobe decomposition of `⟪oddPrimeDriftOperator q.val.fst, q.val.fst⟫_ℝ`. -/
theorem inner_oddPrimeDriftOperator_self_eq_posGraph_add_negGraph (q : SourceGraph) :
    ⟪oddPrimeDriftOperator q.val.fst, q.val.fst⟫_ℝ =
      ⟪oddPrimeDriftOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ +
        ⟪oddPrimeDriftOperator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
  have hsub : q.val.fst = (posGraph q).val.fst - (negGraph q).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_sub_negGraph q).symm
  have hcross2 : ⟪oddPrimeDriftOperator (negGraph q).val.fst, (posGraph q).val.fst⟫_ℝ = 0 := by
    rw [oddPrimeDriftOperator_symmetric, real_inner_comm,
      inner_oddPrimeDriftOperator_posGraph_negGraph]
  conv_lhs => rw [hsub]
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    inner_oddPrimeDriftOperator_posGraph_negGraph q, hcross2]
  ring

/-- Nodal lobe decomposition of `⟪oddPrimeDriftOperator q.val.fst, (absGraph q).val.fst⟫_ℝ`:
pairing `oddPrimeDriftOperator q.val.fst` against `|q.val.fst|` extracts the **difference** of the
positive and negative lobe drifts. -/
theorem inner_oddPrimeDriftOperator_absGraph_eq_posGraph_sub_negGraph (q : SourceGraph) :
    ⟪oddPrimeDriftOperator q.val.fst, (absGraph q).val.fst⟫_ℝ =
      ⟪oddPrimeDriftOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ -
        ⟪oddPrimeDriftOperator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
  have hsub : q.val.fst = (posGraph q).val.fst - (negGraph q).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_sub_negGraph q).symm
  have hadd : (absGraph q).val.fst = (posGraph q).val.fst + (negGraph q).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_add_negGraph q).symm
  have hcross2 : ⟪oddPrimeDriftOperator (negGraph q).val.fst, (posGraph q).val.fst⟫_ℝ = 0 := by
    rw [oddPrimeDriftOperator_symmetric, real_inner_comm,
      inner_oddPrimeDriftOperator_posGraph_negGraph]
  rw [hsub, hadd, map_sub, inner_sub_left, inner_add_right, inner_add_right,
    inner_oddPrimeDriftOperator_posGraph_negGraph q, hcross2]
  ring

/-- **Operator-Level Parity Anticommutation of `oddPrimeDriftOperator`**:
because `oddPrimeDriftPotential (-x) = -oddPrimeDriftPotential x`, `oddPrimeDriftOperator`
anticommutes with the parity reflection `reflectMass` on `MassSpace`. -/
theorem reflectMass_oddPrimeDriftOperator (u : MassSpace) :
    reflectMass (oddPrimeDriftOperator u) = -oddPrimeDriftOperator (reflectMass u) := by
  rw [Lp.ext_iff]
  have hcomp := measurePreserving_neg_mass.quasiMeasurePreserving.ae (oddPrimeDriftOperator_ae u)
  filter_upwards [reflectMass_coeFn (oddPrimeDriftOperator u), hcomp,
    Lp.coeFn_neg (oddPrimeDriftOperator (reflectMass u)),
    oddPrimeDriftOperator_ae (reflectMass u), reflectMass_coeFn u] with x hx1 hx2 hx3 hx4 hx5
  rw [hx1, hx2, hx3, Pi.neg_apply, hx4, hx5, oddPrimeDriftPotential_neg]
  ring

/-- **Bilinear Parity Anticommutation of `oddPrimeDriftOperator`**:
for all `u, v : MassSpace`,
`⟪oddPrimeDriftOperator (reflectMass u), reflectMass v⟫_ℝ = -⟪oddPrimeDriftOperator u, v⟫_ℝ`. -/
theorem inner_oddPrimeDriftOperator_reflectMass (u v : MassSpace) :
    ⟪oddPrimeDriftOperator (reflectMass u), reflectMass v⟫_ℝ =
      -⟪oddPrimeDriftOperator u, v⟫_ℝ := by
  have h := reflectMass.inner_map_map (oddPrimeDriftOperator u) v
  rw [reflectMass_oddPrimeDriftOperator, inner_neg_left] at h
  linarith

/-- For every even vector `u` (`reflectMass u = u`), `⟪oddPrimeDriftOperator u, u⟫_ℝ = 0`. -/
theorem inner_oddPrimeDriftOperator_self_eq_zero_of_even {u : MassSpace}
    (heven : reflectMass u = u) :
    ⟪oddPrimeDriftOperator u, u⟫_ℝ = 0 := by
  have h := inner_oddPrimeDriftOperator_reflectMass u u
  rw [heven] at h
  linarith

/-- For every odd vector `u` (`reflectMass u = -u`), `⟪oddPrimeDriftOperator u, u⟫_ℝ = 0`. -/
theorem inner_oddPrimeDriftOperator_self_eq_zero_of_odd {u : MassSpace}
    (hodd : reflectMass u = -u) :
    ⟪oddPrimeDriftOperator u, u⟫_ℝ = 0 := by
  have h := inner_oddPrimeDriftOperator_reflectMass u u
  rw [hodd, map_neg, inner_neg_left, inner_neg_right, neg_neg] at h
  linarith

/-- **Equal-and-Opposite Nodal Lobe Drift for Parity-Definite Graph Vectors**:
whenever `⟪oddPrimeDriftOperator q.val.fst, q.val.fst⟫_ℝ = 0` (in particular, for every even or odd
vector `q`), the positive and negative lobes have equal and opposite chiral prime drift, and
`⟪oddPrimeDriftOperator q.val.fst, (absGraph q).val.fst⟫_ℝ = 2 * ⟪oddPrimeDriftOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ`. -/
theorem posGraph_and_negGraph_oddPrimeDrift_of_self_eq_zero {q : SourceGraph}
    (h0 : ⟪oddPrimeDriftOperator q.val.fst, q.val.fst⟫_ℝ = 0) :
    ⟪oddPrimeDriftOperator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ =
        -⟪oddPrimeDriftOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ ∧
      ⟪oddPrimeDriftOperator q.val.fst, (absGraph q).val.fst⟫_ℝ =
        2 * ⟪oddPrimeDriftOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ := by
  have hsum := inner_oddPrimeDriftOperator_self_eq_posGraph_add_negGraph q
  have hdiff := inner_oddPrimeDriftOperator_absGraph_eq_posGraph_sub_negGraph q
  exact ⟨by linarith, by linarith⟩

/-- **Tightened Pythagorean Prime-Shift Bound on Both Nodal Lobes**:
for any `q : SourceGraph` with `⟪oddPrimeDriftOperator q.val.fst, q.val.fst⟫_ℝ = 0` (including every
even or odd eigenvector), **both** `posGraph q` and `negGraph q` have their prime shift form
strictly tightened by `(1 / 4) * ⟪oddPrimeDriftOperator q.val.fst, (absGraph q).val.fst⟫_ℝ ^ 2`. -/
theorem posGraph_and_negGraph_primeShift_sq_add_quarter_absGraph_drift_sq_le {q : SourceGraph}
    (h0 : ⟪oddPrimeDriftOperator q.val.fst, q.val.fst⟫_ℝ = 0) :
    ⟪primeShiftOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ ^ 2 +
        (1 / 4 : ℝ) * ⟪oddPrimeDriftOperator q.val.fst, (absGraph q).val.fst⟫_ℝ ^ 2 ≤
      ⟪primeDiagonalOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ ^ 2 ∧
    ⟪primeShiftOperator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ^ 2 +
        (1 / 4 : ℝ) * ⟪oddPrimeDriftOperator q.val.fst, (absGraph q).val.fst⟫_ℝ ^ 2 ≤
      ⟪primeDiagonalOperator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ^ 2 := by
  obtain ⟨hneg, habs⟩ := posGraph_and_negGraph_oddPrimeDrift_of_self_eq_zero h0
  have hp := sq_inner_primeShiftOperator_add_sq_oddPrimeDriftOperator_le (posGraph q).val.fst
  have hn := sq_inner_primeShiftOperator_add_sq_oddPrimeDriftOperator_le (negGraph q).val.fst
  rw [habs]
  constructor
  · nlinarith
  · rw [hneg] at hn
    nlinarith

/-! ## Section 4: Order and Single-Mode Perturbation Rigidity of the Even and Odd Euler–Poisson Identities -/

/-- Weighted symmetric kernel sum `∑' n, w n * (Θ(x + log n) + Θ(x - log n))` for an arbitrary
arithmetic weight `w : ℕ → ℝ`. -/
def weightedSymKernelSum (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, w n * (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))

/-- Weighted antisymmetric (chiral) kernel sum `∑' n, w n * (Θ(x - log n) - Θ(x + log n))` for an
arbitrary arithmetic weight `w : ℕ → ℝ`. -/
def weightedOddKernelSum (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, w n * (riemannKernelReal (x - Real.log n) - riemannKernelReal (x + Real.log n))

theorem weightedSymKernelSum_vonMangoldtAtom (x : ℝ) :
    weightedSymKernelSum vonMangoldtAtom x = primeKernelSum x := rfl

theorem weightedOddKernelSum_vonMangoldtAtom (x : ℝ) :
    weightedOddKernelSum vonMangoldtAtom x = oddPrimeKernelSum x := rfl

/-- **Order Rigidity of the Even Euler–Poisson Harmonic Identity**:
if a summable weight `w : ℕ → ℝ` satisfies `vonMangoldtAtom n ≤ w n` for all `n` and
`vonMangoldtAtom n₀ < w n₀` for some `n₀ : ℕ`, then at **every** point `x ∈ ℝ`,
`weightedSymKernelSum w x` is strictly greater than `primeKernelSum x` and therefore strictly
violates `theta_harmonic_identity`. -/
theorem weightedSymKernelSum_gt_primeKernelSum {w : ℕ → ℝ} {n₀ : ℕ}
    (hle : ∀ n, vonMangoldtAtom n ≤ w n) (hlt : vonMangoldtAtom n₀ < w n₀)
    (x : ℝ) (hsum : Summable fun n : ℕ =>
      w n * (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))) :
    primeKernelSum x < weightedSymKernelSum w x ∧
      weightedSymKernelSum w x ≠
        Real.cosh (x / 2) - 2 * archConstantReal * riemannKernelReal x +
          ∫ u in Ioi (0 : ℝ), symArchTerm x u := by
  have hdiff_sum : Summable fun n : ℕ =>
      (w n - vonMangoldtAtom n) *
        (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n)) := by
    refine (hsum.sub (summable_primeKernelSum x)).congr fun n => by ring
  have hterm_pos : 0 < (w n₀ - vonMangoldtAtom n₀) *
      (riemannKernelReal (x + Real.log n₀) + riemannKernelReal (x - Real.log n₀)) :=
    mul_pos (sub_pos.mpr hlt) (add_pos (riemannKernelReal_pos _) (riemannKernelReal_pos _))
  have htsum_ge : (w n₀ - vonMangoldtAtom n₀) *
      (riemannKernelReal (x + Real.log n₀) + riemannKernelReal (x - Real.log n₀)) ≤
      weightedSymKernelSum w x - primeKernelSum x := by
    have h1 := hdiff_sum.sum_le_tsum ({n₀} : Finset ℕ) fun n _ =>
      mul_nonneg (sub_nonneg.mpr (hle n))
        (add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le)
    simp only [Finset.sum_singleton] at h1
    have h2 : (∑' n : ℕ, (w n - vonMangoldtAtom n) *
        (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))) =
        weightedSymKernelSum w x - primeKernelSum x := by
      unfold weightedSymKernelSum primeKernelSum
      rw [← hsum.tsum_sub (summable_primeKernelSum x)]
      exact tsum_congr fun n => by ring
    linarith
  have hstrict : primeKernelSum x < weightedSymKernelSum w x := by linarith
  refine ⟨hstrict, ?_⟩
  rw [← theta_harmonic_identity x]
  exact hstrict.ne'

/-- **Order Rigidity of the Odd (Chiral) Euler–Poisson Drift Identity**:
if a summable weight `w : ℕ → ℝ` satisfies `vonMangoldtAtom n ≤ w n` for all `n` and
`vonMangoldtAtom n₀ < w n₀` for some `n₀ ≥ 2`, then at **every** positive point `x > 0`,
`weightedOddKernelSum w x` is strictly greater than `oddPrimeKernelSum x` and therefore strictly
violates `theta_odd_source_identity`. -/
theorem weightedOddKernelSum_gt_oddPrimeKernelSum {w : ℕ → ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hle : ∀ n, vonMangoldtAtom n ≤ w n) (hlt : vonMangoldtAtom n₀ < w n₀)
    {x : ℝ} (hx : 0 < x) (hsum : Summable fun n : ℕ =>
      w n * (riemannKernelReal (x - Real.log n) - riemannKernelReal (x + Real.log n))) :
    oddPrimeKernelSum x < weightedOddKernelSum w x ∧
      (∫ u in Ioi (0 : ℝ), oddArchTerm x u) + weightedOddKernelSum w x ≠
        2 * x * riemannKernelReal x + ∫ u in Ioi (0 : ℝ), oddPolarTerm x u := by
  have hdiff_sum : Summable fun n : ℕ =>
      (w n - vonMangoldtAtom n) *
        (riemannKernelReal (x - Real.log n) - riemannKernelReal (x + Real.log n)) := by
    refine (hsum.sub (summable_oddPrimeKernelSum x)).congr fun n => by ring
  have hlog : 0 < Real.log (n₀ : ℝ) := Real.log_pos (by exact_mod_cast hn₀)
  have hterm_pos : 0 < (w n₀ - vonMangoldtAtom n₀) *
      (riemannKernelReal (x - Real.log n₀) - riemannKernelReal (x + Real.log n₀)) :=
    mul_pos (sub_pos.mpr hlt) (riemannKernelReal_sub_pos hx hlog)
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ (w n - vonMangoldtAtom n) *
      (riemannKernelReal (x - Real.log n) - riemannKernelReal (x + Real.log n)) := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · exact mul_nonneg (sub_nonneg.mpr (hle n))
        (riemannKernelReal_sub_pos hx (Real.log_pos (by exact_mod_cast hn))).le
  have htsum_ge : (w n₀ - vonMangoldtAtom n₀) *
      (riemannKernelReal (x - Real.log n₀) - riemannKernelReal (x + Real.log n₀)) ≤
      weightedOddKernelSum w x - oddPrimeKernelSum x := by
    have h1 := hdiff_sum.sum_le_tsum ({n₀} : Finset ℕ) fun n _ => hterm_nonneg n
    simp only [Finset.sum_singleton] at h1
    have h2 : (∑' n : ℕ, (w n - vonMangoldtAtom n) *
        (riemannKernelReal (x - Real.log n) - riemannKernelReal (x + Real.log n))) =
        weightedOddKernelSum w x - oddPrimeKernelSum x := by
      unfold weightedOddKernelSum oddPrimeKernelSum
      rw [← hsum.tsum_sub (summable_oddPrimeKernelSum x)]
      exact tsum_congr fun n => by ring
    linarith
  have hstrict : oddPrimeKernelSum x < weightedOddKernelSum w x := by linarith
  refine ⟨hstrict, ?_⟩
  have hodd := theta_odd_source_identity x
  intro heq
  linarith

end GaloisForLFunctions.BiScaleUncertainty
