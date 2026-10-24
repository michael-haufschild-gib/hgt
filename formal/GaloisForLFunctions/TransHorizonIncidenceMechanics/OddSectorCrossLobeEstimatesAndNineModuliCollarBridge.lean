import GaloisForLFunctions.TransHorizonIncidenceMechanics.OddPolarAbsorptionBoundaryAndCompensatedHorizon
import GaloisForLFunctions.TransHorizonIncidenceMechanics.OddEigenvectorNodalModulusBalanceAndFourthBandStepLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge
import GaloisForLFunctions.RHTower.CHMDResolventNodalCrossPositivityAndBalancedRayleighExcess
import GaloisForLFunctions.RHTower.CHMDEvenSectorPointSpectrum
import GaloisForLFunctions.ArithmeticIncidencePositivity.TotalAntiDiagonalClassification
import GaloisForLFunctions.ArithmeticIncidencePositivity.UnpaidAxisIntervals

/-!
# Odd-Sector Cross-Lobe Estimates, Unconditional Cosh/Sinh Defect Bounds, and the Nine-Moduli Collar Bridge

This module resolves **Open Problem 7.4 (The odd sector)** and **Research Topic 7.9.3 (The odd-sector
collar and the nine moduli)** of the Trans-Horizon Incidence Mechanics programme:

1. **Term-by-Term Matching of the Odd-Sector Collar Potential with the Nine Moduli and Unpaid Axis
   Intervals of Arithmetic Incidence Positivity (§1):**
   - For the secondary odd ground profile $M(x) = \operatorname{oddProfile}(a, x)$ ($a > 0$) and any
     even test profile $w : \mathbb{R} \to \mathbb{R}$, at every crossing pair $(-x, s - x)$ along the
     anti-diagonal of sum $s > 0$ ($x \in (0, s)$), the pair-side archimedean crossing density
     `archCrossingDensity (oddProfile a) w (-x, s - x)` and polar variance density
     `varianceDensity (oddProfile a) w (-x, s - x)` coincide identically with
     `archLevyDensity s * oddProfileCollarDiffSq a w s x` and
     `crossingPolarWeight s x * oddProfileCollarDiffSq a w s x`
     (`archCrossingDensity_oddProfile_eq`, `varianceDensity_oddProfile_eq`), so the net
     (archimedean + prime-atom minus polar) collar density at $s = \log d$ ($d \ge 2$) is
     `totalAntiDiagonalKernel d x * oddProfileCollarDiffSq a w (Real.log d) x`
     (`totalAntiDiagonal_oddProfileCollarDiffSq_eq`).
   - For any continuous midpoint-symmetric weight $K(t - x) = K(x)$ on $[0, t]$, the $K$-weighted
     ground-state collar-mixed integral diagonalizes identically to twice the 1-point diagonal
     integral against `oddProfile a x * collarMixedDiagKernel a t x * w x ^ 2`
     (`integral_symmetric_mul_oddProfileCollarMixed_eq_two_mul_diag`), specializing directly to
     `crossingPolarWeight (Real.log d)`, `atomAntiDiagonalKernel d`, and `totalAntiDiagonalKernel d`.
   - The 1-point odd-profile diagonal collar-mixed potential
     `oddProfile a x * collarMixedDiagKernel a (Real.log d) x` is strictly positive on $(0, \log d)$,
     so its atom-minus-pole excess is positive on all of $(0, \log d)$ **if and only if**
     $d \in \operatorname{atomDominatedModuli} = \{2, 3, 4, 5, 7\}$
     (`atomAntiDiagonal_oddProfile_diag_pos_on_Ioo_iff`), and its total (archimedean + atom minus
     pole) excess is positive on all of $(0, \log d)$ **if and only if**
     $d \in \operatorname{totalDominatedModuli} = \{2, 3, 4, 5, 7, 8, 9, 11, 13\}$ (**the nine
     moduli**, `totalAntiDiagonal_oddProfile_diag_pos_on_Ioo_iff`).
   - For every $d \ge 23$, on the paid middle interval $[L_d, \log d - L_d]$ where
     $L_d = \operatorname{unpaidOuterEnd}(\log d, \operatorname{antiDiagonalLevel} d) < \frac{1}{4}\log d$,
     the polar weight dominates $\operatorname{antiDiagonalLevel} d$ pointwise on both
     `oddProfileCollarDiffSq` and the 1-point diagonal collar-mixed potential
     (`totalAntiDiagonal_oddProfile_nonpos_on_paid_middle_of_twenty_three_le`), confining all
     unpaid excess to the two axis intervals $(0, L_d) \cup (\log d - L_d, \log d)$.

2. **Unconditional Pointwise and Integrated Bounds on the Compensated Local Cosh/Sinh Correction (§2):**
   - Using the unconditional linear drop bound `riemannKernelReal_sub_le_linear_of_nonneg`, we
     discharge the derivative-bound premise `hM` across $[-R, R]$ with the explicit analytic constant
     `thetaDerivBound a R = 2 * π * (Real.exp (2 * (a + R)) + 2) * riemannKernelReal 0` and ratio
     `unconditionalCoshSinhRatio a R = coshSinhPolarRatio a (thetaDerivBound a R) R`
     (`unconditional_oddProfile_le_sinh`, `unconditional_oddPolarFunction_mul_cosh_le_sinh`).
   - Consequently, for every $a > 0$, $R \ge 0$, $\theta \in \mathbb{R}$, and every continuous
     compactly supported even profile $w$ vanishing on $[R, \infty)$, the compensated local
     cosh/sinh correction `oddPolarDefect a θ w` satisfies the unconditional upper bound
     $$\operatorname{oddPolarDefect}(a, \theta, w)
       \le \max\bigl(\operatorname{unconditionalCoshSinhRatio}(a, R) - \theta, 0\bigr)
         \cdot \operatorname{oddSinhPotential}(a, w)$$
     (`unconditional_oddPolarDefect_le_oddSinhPotential`), and vanishes identically whenever
     $\operatorname{unconditionalCoshSinhRatio}(a, R) \le \theta$
     (`unconditional_oddPolarDefect_eq_zero_of_le`).

3. **Odd-Sector Cross-Lobe Estimates, Individual-Lobe Polar Laws, Cross-Lobe Weil Polarization, and
   the Four-Term Positive-Lobe Excess (§3):**
   - For every odd graph vector $p : \operatorname{SourceGraph}$ (`reflectGraph p = -p`), its
     modulus `absGraph p` is orthogonal to every odd mass vector $z$ (`reflectMass z = -z`, including
     `tanhL` and `oddPolarVectorAt a ha`), while `posGraph p` and `negGraph p` carry opposite
     half-moments $\pm \frac{1}{2}\langle p.\text{fst}, z\rangle_{\mathbb{R}}$
     (`odd_lobe_inner_odd_mass`, `odd_lobe_tanhL_and_oddPolarVectorAt_identities`). For every odd
     eigenvector `resolvent w = μ • w`, both individual lobes `posGraph (rieszLift w)` and
     `negGraph (rieszLift w)` satisfy the exact odd-polar balance against `oddPolarVectorAt a ha`
     and `tanhL` (`odd_eigenvector_posGraph_and_negGraph_oddPolarVectorAt_pairing`).
   - On the odd sector, `weilForm` and `weilBilin` polarize across the nodal lobes:
     $$\operatorname{weilForm}(\operatorname{absGraph} p)
       = \operatorname{sourceEnergy}(\operatorname{primGraph}(\operatorname{absGraph} p)),\qquad
       \operatorname{weilForm}(\operatorname{absGraph} p) - \operatorname{weilForm}(p)
       = 4\operatorname{weilBilin}(\operatorname{posGraph} p, \operatorname{negGraph} p)$$
     (`odd_weilForm_and_weilBilin_lobe_polarization`).
   - For every odd eigenvector `resolvent w = μ • w` ($\mu > 0$, `reflectMass w = -w`) with
     $q = \operatorname{rieszLift} w$, we establish the exact four-term positive-lobe excess identity
     (`= ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2`) and the unconditional two-sided cross-lobe
     sandwich
     $$0 \le 4\mu^2 \langle \operatorname{primeShiftOperator}(\operatorname{posGraph} q).\text{fst}, (\operatorname{negGraph} q).\text{fst}\rangle_{\mathbb{R}}
       \le -4\mu^2 \operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)
       \le 4\langle \operatorname{resolvent}(\operatorname{posGraph} q).\text{fst}, (\operatorname{negGraph} q).\text{fst}\rangle_{\mathbb{R}}
       \le (1 - \mu)\|q.\text{fst}\|^2$$
     (`odd_eigenvector_four_term_excess_and_cross_lobe_sandwich`,
     `odd_eigenvector_cross_lobe_strict_bounds_of_ne_zero`).
-/

open Finset MeasureTheory Set Filter Topology Real
open scoped InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.ThetaSourceWard _root_.RHTower.PhiDivisorEnergy
open _root_.RHTower.CHMDPrimeCuts _root_.RHTower.CHMDPrimeChainSource
open GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ## §1. Term-by-Term Matching of the Odd-Sector Collar Potential with the Nine Moduli and Unpaid Axis Intervals -/

/-- At any crossing pair `(-x, s - x)` (`x ∈ (0, s)`, `a > 0`), the product of the odd profile
`oddProfile a` at the two endpoints is negative and its absolute value equals
`oddProfile a x * oddProfile a (s - x)`. -/
theorem abs_oddProfile_mul_crossing_eq {a s x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (0 : ℝ) s) :
    |oddProfile a (-x) * oddProfile a (s - x)| = oddProfile a x * oddProfile a (s - x) := by
  have hx1 : 0 < oddProfile a x := oddProfile_pos ha hx.1
  have hx2 : 0 < oddProfile a (s - x) := oddProfile_pos ha (sub_pos.mpr hx.2)
  rw [oddProfile_neg, neg_mul, abs_neg, abs_of_pos (mul_pos hx1 hx2)]

/-- **Exact Matching of `archCrossingDensity` and `oddProfileCollarDiffSq` on `(0, s)`:**
For any `a > 0`, even profile `w : ℝ → ℝ`, `s > 0`, and `x ∈ (0, s)`, the pair-side archimedean
crossing energy density `archCrossingDensity (oddProfile a) w (-x, s - x)` equals
`archLevyDensity s * oddProfileCollarDiffSq a w s x`. -/
theorem archCrossingDensity_oddProfile_eq {a s x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (0 : ℝ) s)
    {w : ℝ → ℝ} (heven : ∀ u, w (-u) = w u) :
    archCrossingDensity (oddProfile a) w (-x, s - x) =
      archLevyDensity s * oddProfileCollarDiffSq a w s x := by
  have hs : 0 < s := hx.1.trans hx.2
  unfold archCrossingDensity oddProfileCollarDiffSq
  rw [show -x - (s - x) = -s by ring, abs_neg, abs_of_pos hs,
    abs_oddProfile_mul_crossing_eq ha hx, heven x]
  ring

/-- **Exact Matching of `varianceDensity` and `crossingPolarWeight * oddProfileCollarDiffSq` on `(0, s)`:**
For any `a > 0`, even profile `w : ℝ → ℝ`, and `s, x : ℝ`, the pair-side polar variance energy
density `varianceDensity (oddProfile a) w (-x, s - x)` equals
`crossingPolarWeight s x * oddProfileCollarDiffSq a w s x`. -/
theorem varianceDensity_oddProfile_eq (a s x : ℝ) {w : ℝ → ℝ} (heven : ∀ u, w (-u) = w u) :
    varianceDensity (oddProfile a) w (-x, s - x) =
      crossingPolarWeight s x * oddProfileCollarDiffSq a w s x := by
  unfold varianceDensity crossingPolarWeight oddProfileCollarDiffSq
  rw [oddProfile_neg, neg_div, Real.sinh_neg, heven x]
  ring

/-- The prime-atom anti-diagonal kernel of `n` at the point `(-a, log n - a)`: prime atom minus
polar weight. -/
def atomAntiDiagonalKernel (n : ℕ) (a : ℝ) : ℝ :=
  vonMangoldtAtom n - crossingPolarWeight (Real.log n) a

theorem atomAntiDiagonalKernel_symm (n : ℕ) (a : ℝ) :
    atomAntiDiagonalKernel n (Real.log n - a) = atomAntiDiagonalKernel n a := by
  unfold atomAntiDiagonalKernel
  rw [crossingPolarWeight_symm]

theorem totalAntiDiagonalKernel_symm (n : ℕ) (a : ℝ) :
    totalAntiDiagonalKernel n (Real.log n - a) = totalAntiDiagonalKernel n a := by
  unfold totalAntiDiagonalKernel
  rw [crossingPolarWeight_symm]

/-- **Pointwise Identity for the Total (Archimedean + Prime-Atom Minus Polar) Collar Density:**
For any `a > 0`, `d ≥ 2`, `x ∈ (0, Real.log d)`, and even profile `w : ℝ → ℝ`, the net crossing
energy density on the anti-diagonal of `d` equals
`totalAntiDiagonalKernel d x * oddProfileCollarDiffSq a w (Real.log d) x`, while the prime-atom
minus polar collar density equals
`atomAntiDiagonalKernel d x * oddProfileCollarDiffSq a w (Real.log d) x`. -/
theorem totalAntiDiagonal_oddProfileCollarDiffSq_eq {a : ℝ} (ha : 0 < a) {d : ℕ}
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (Real.log d)) {w : ℝ → ℝ} (heven : ∀ u, w (-u) = w u) :
    archCrossingDensity (oddProfile a) w (-x, Real.log d - x) +
        vonMangoldtAtom d * oddProfileCollarDiffSq a w (Real.log d) x -
        varianceDensity (oddProfile a) w (-x, Real.log d - x) =
      totalAntiDiagonalKernel d x * oddProfileCollarDiffSq a w (Real.log d) x ∧
    vonMangoldtAtom d * oddProfileCollarDiffSq a w (Real.log d) x -
        varianceDensity (oddProfile a) w (-x, Real.log d - x) =
      atomAntiDiagonalKernel d x * oddProfileCollarDiffSq a w (Real.log d) x := by
  rw [archCrossingDensity_oddProfile_eq ha hx heven, varianceDensity_oddProfile_eq a (Real.log d) x heven]
  unfold totalAntiDiagonalKernel atomAntiDiagonalKernel
  exact ⟨by ring, by ring⟩

/-- **Weighted Midpoint-Reflection Diagonalization of `oddProfileCollarMixed`:**
For any continuous midpoint-symmetric kernel `K : ℝ → ℝ` (`∀ x, K (t - x) = K x`) and any continuous
profile `w : ℝ → ℝ` (`0 ≤ t`), the `K`-weighted collar-mixed integral over `(0, t)` collapses
identically to twice the `K`-weighted 1-point diagonal potential against
`oddProfile a x * collarMixedDiagKernel a t x * w x ^ 2`. -/
theorem integral_symmetric_mul_oddProfileCollarMixed_eq_two_mul_diag (a : ℝ)
    {K w : ℝ → ℝ} (hK : Continuous K) (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t)
    (hsym : ∀ x, K (t - x) = K x) :
    (∫ x in Ioo (0 : ℝ) t, K x * oddProfileCollarMixed a w t x) =
      2 * ∫ x in Ioo (0 : ℝ) t,
        K x * (oddProfile a x * collarMixedDiagKernel a t x * w x ^ 2) := by
  set g : ℝ → ℝ := fun x => K x * (oddProfile a x * collarMixedDiagKernel a t x * w x ^ 2)
  have hg_cont : Continuous g := by
    dsimp [g, collarMixedDiagKernel]
    exact hK.mul (((continuous_oddProfile a).mul
      ((continuous_riemannKernelReal.comp (continuous_const.sub continuous_id)).mul
        ((continuous_oddPolarFunction a).add
          ((continuous_oddPolarFunction a).comp (continuous_const.sub continuous_id))))).mul
      (hw.pow 2))
  have hg_int : IntegrableOn g (Ioo (0 : ℝ) t) :=
    hg_cont.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hg_refl_int : IntegrableOn (fun x => g (t - x)) (Ioo (0 : ℝ) t) :=
    (hg_cont.comp (continuous_const.sub continuous_id)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hcongr : EqOn (fun x => K x * oddProfileCollarMixed a w t x)
      (fun x => g x + g (t - x)) (Ioo (0 : ℝ) t) := by
    intro x _
    dsimp [g]
    rw [hsym x, oddProfileCollarMixed_eq_diag_add_reflect a w t x]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_add hg_int hg_refl_int,
    setIntegral_Ioo_reflect_self hg_cont ht]
  ring

/-- **Exact 1-Point Diagonalization of the Polar-Paid, Atom-Minus-Pole, and Total-Minus-Pole
Collar-Mixed Integrals:**
For every `a : ℝ`, continuous `w : ℝ → ℝ`, and `d : ℕ`, the integrals of `oddProfileCollarMixed`
against `crossingPolarWeight (Real.log d)`, `atomAntiDiagonalKernel d`, and
`totalAntiDiagonalKernel d` over `(0, Real.log d)` each equal twice the corresponding 1-point
diagonal integral against `oddProfile a x * collarMixedDiagKernel a (Real.log d) x * w x ^ 2`. -/
theorem integral_antiDiagonalKernels_mul_oddProfileCollarMixed_eq_two_mul_diag
    (a : ℝ) {w : ℝ → ℝ} (hw : Continuous w) (d : ℕ) :
    (∫ x in Ioo (0 : ℝ) (Real.log d),
        crossingPolarWeight (Real.log d) x * oddProfileCollarMixed a w (Real.log d) x) =
      2 * (∫ x in Ioo (0 : ℝ) (Real.log d),
        crossingPolarWeight (Real.log d) x *
          (oddProfile a x * collarMixedDiagKernel a (Real.log d) x * w x ^ 2)) ∧
    (∫ x in Ioo (0 : ℝ) (Real.log d),
        atomAntiDiagonalKernel d x * oddProfileCollarMixed a w (Real.log d) x) =
      2 * (∫ x in Ioo (0 : ℝ) (Real.log d),
        atomAntiDiagonalKernel d x *
          (oddProfile a x * collarMixedDiagKernel a (Real.log d) x * w x ^ 2)) ∧
    (∫ x in Ioo (0 : ℝ) (Real.log d),
        totalAntiDiagonalKernel d x * oddProfileCollarMixed a w (Real.log d) x) =
      2 * (∫ x in Ioo (0 : ℝ) (Real.log d),
        totalAntiDiagonalKernel d x *
          (oddProfile a x * collarMixedDiagKernel a (Real.log d) x * w x ^ 2)) := by
  have ht : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d
  have hcont_polar : Continuous (crossingPolarWeight (Real.log d)) :=
    continuous_crossingPolarWeight (Real.log d)
  have hcont_atom : Continuous (atomAntiDiagonalKernel d) :=
    continuous_const.sub hcont_polar
  have hcont_total : Continuous (totalAntiDiagonalKernel d) :=
    continuous_const.sub hcont_polar
  refine ⟨integral_symmetric_mul_oddProfileCollarMixed_eq_two_mul_diag a hcont_polar hw ht
      (crossingPolarWeight_symm (Real.log d)),
    integral_symmetric_mul_oddProfileCollarMixed_eq_two_mul_diag a hcont_atom hw ht
      (atomAntiDiagonalKernel_symm d),
    integral_symmetric_mul_oddProfileCollarMixed_eq_two_mul_diag a hcont_total hw ht
      (totalAntiDiagonalKernel_symm d)⟩

/-- For `a > 0` and `x ∈ (0, t)`, the 1-point odd-profile diagonal collar-mixed weight
`oddProfile a x * collarMixedDiagKernel a t x` is strictly positive. -/
theorem oddProfile_mul_collarMixedDiagKernel_pos {a t x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo (0 : ℝ) t) :
    0 < oddProfile a x * collarMixedDiagKernel a t x := by
  have h1 : 0 < oddProfile a x := oddProfile_pos ha hx.1
  have h2 : 0 < oddPolarFunction a x := oddPolarFunction_pos ha hx.1
  have h3 : 0 < oddPolarFunction a (t - x) := oddPolarFunction_pos ha (sub_pos.mpr hx.2)
  unfold collarMixedDiagKernel
  exact mul_pos h1 (mul_pos (riemannKernelReal_pos (t - x)) (add_pos h2 h3))

/-- **Atom-Dominated Five-Moduli Law for the 1-Point Odd-Profile Collar-Mixed Potential:**
For `a > 0` and `d ≥ 2`, the prime-atom minus polar 1-point diagonal collar-mixed potential
`atomAntiDiagonalKernel d x * (oddProfile a x * collarMixedDiagKernel a (Real.log d) x)` is
strictly positive on the entire open anti-diagonal `x ∈ (0, Real.log d)` **if and only if**
`d ∈ atomDominatedModuli` (`{2, 3, 4, 5, 7}`). -/
theorem atomAntiDiagonal_oddProfile_diag_pos_on_Ioo_iff {a : ℝ} (ha : 0 < a) {d : ℕ}
    (hd : 2 ≤ d) :
    (∀ x ∈ Set.Ioo (0 : ℝ) (Real.log d),
      0 < atomAntiDiagonalKernel d x *
        (oddProfile a x * collarMixedDiagKernel a (Real.log d) x)) ↔
      d ∈ atomDominatedModuli := by
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have hmid_mem : Real.log d / 2 ∈ Set.Ioo (0 : ℝ) (Real.log d) := ⟨by linarith, by linarith⟩
  constructor
  · intro h
    by_contra hnot
    have hle := vonMangoldtAtom_le_crossingPolarWeight_midpoint hd hnot
    have hpos_mid := h (Real.log d / 2) hmid_mem
    have hdiag_pos := oddProfile_mul_collarMixedDiagKernel_pos ha hmid_mem
    have hatom_pos : 0 < atomAntiDiagonalKernel d (Real.log d / 2) :=
      pos_of_mul_pos_left hpos_mid hdiag_pos.le
    unfold atomAntiDiagonalKernel at hatom_pos
    linarith
  · intro hmem x hx
    have hatom_pos : 0 < atomAntiDiagonalKernel d x :=
      sub_pos.mpr (crossingPolarWeight_lt_vonMangoldtAtom hmem x)
    exact mul_pos hatom_pos (oddProfile_mul_collarMixedDiagKernel_pos ha hx)

/-- **Nine-Moduli Law for the Total (Archimedean + Atom Minus Polar) 1-Point Odd-Profile
Collar-Mixed Potential (`totalAntiDiagonal_oddProfile_diag_pos_on_Ioo_iff`):**
For `a > 0` and `d ≥ 2`, the total (archimedean + prime-atom minus polar) 1-point diagonal
collar-mixed potential
`totalAntiDiagonalKernel d x * (oddProfile a x * collarMixedDiagKernel a (Real.log d) x)` is
strictly positive on the entire open anti-diagonal `x ∈ (0, Real.log d)` **if and only if**
`d ∈ totalDominatedModuli` (`{2, 3, 4, 5, 7, 8, 9, 11, 13}`, the **nine moduli**). -/
theorem totalAntiDiagonal_oddProfile_diag_pos_on_Ioo_iff {a : ℝ} (ha : 0 < a) {d : ℕ}
    (hd : 2 ≤ d) :
    (∀ x ∈ Set.Ioo (0 : ℝ) (Real.log d),
      0 < totalAntiDiagonalKernel d x *
        (oddProfile a x * collarMixedDiagKernel a (Real.log d) x)) ↔
      d ∈ totalDominatedModuli := by
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have hmid_mem : Real.log d / 2 ∈ Set.Ioo (0 : ℝ) (Real.log d) := ⟨by linarith, by linarith⟩
  constructor
  · intro h
    by_contra hnot
    have hle := totalAntiDiagonalKernel_midpoint_nonpos hd hnot
    have hpos_mid := h (Real.log d / 2) hmid_mem
    have hdiag_pos := oddProfile_mul_collarMixedDiagKernel_pos ha hmid_mem
    have htot_pos : 0 < totalAntiDiagonalKernel d (Real.log d / 2) :=
      pos_of_mul_pos_left hpos_mid hdiag_pos.le
    linarith
  · intro hmem x hx
    have htot_pos : 0 < totalAntiDiagonalKernel d x :=
      (totalAntiDiagonalKernel_pos_forall_iff hd).mpr hmem x
    exact mul_pos htot_pos (oddProfile_mul_collarMixedDiagKernel_pos ha hx)

/-- Outside the nine moduli (`d ≥ 2`, `d ∉ totalDominatedModuli`), at the midpoint
`x = Real.log d / 2` the polar weight pays the combined archimedean + prime-atom level on both
`oddProfileCollarDiffSq` and the 1-point diagonal collar-mixed potential. -/
theorem totalAntiDiagonal_oddProfile_midpoint_nonpos_of_not_mem {a : ℝ} (ha : 0 < a)
    {d : ℕ} (hd : 2 ≤ d) (hnot : d ∉ totalDominatedModuli) (w : ℝ → ℝ) :
    totalAntiDiagonalKernel d (Real.log d / 2) *
        oddProfileCollarDiffSq a w (Real.log d) (Real.log d / 2) ≤ 0 ∧
      totalAntiDiagonalKernel d (Real.log d / 2) *
        (oddProfile a (Real.log d / 2) *
          collarMixedDiagKernel a (Real.log d) (Real.log d / 2) *
          w (Real.log d / 2) ^ 2) ≤ 0 := by
  have hmid : totalAntiDiagonalKernel d (Real.log d / 2) ≤ 0 :=
    totalAntiDiagonalKernel_midpoint_nonpos hd hnot
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have hx : Real.log d / 2 ∈ Set.Ioo (0 : ℝ) (Real.log d) := ⟨by linarith, by linarith⟩
  have hcol_nn : 0 ≤ oddProfileCollarDiffSq a w (Real.log d) (Real.log d / 2) := by
    unfold oddProfileCollarDiffSq
    exact mul_nonneg (mul_nonneg (oddProfile_pos ha hx.1).le
      (oddProfile_pos ha (sub_pos.mpr hx.2)).le) (sq_nonneg _)
  have hdiag_nn : 0 ≤ oddProfile a (Real.log d / 2) *
      collarMixedDiagKernel a (Real.log d) (Real.log d / 2) * w (Real.log d / 2) ^ 2 :=
    mul_nonneg (oddProfile_mul_collarMixedDiagKernel_pos ha hx).le (sq_nonneg _)
  exact ⟨mul_nonpos_of_nonpos_of_nonneg hmid hcol_nn,
    mul_nonpos_of_nonpos_of_nonneg hmid hdiag_nn⟩

/-- **Unpaid Axis-Interval Confinement of the Odd-Profile Collar Potentials for `d ≥ 23`:**
For every `a > 0` and `d ≥ 23`, let `L_d = unpaidOuterEnd (Real.log d) (antiDiagonalLevel d)` and
`ℓ_d = 2 * ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) + ArithmeticFunction.vonMangoldt d) / ((d : ℝ) - 1)`.
Then:
1. For every `x ∈ [L_d, Real.log d - L_d] ∩ (0, Real.log d)` (the paid middle interval), the polar
   weight dominates `antiDiagonalLevel d` pointwise on both `oddProfileCollarDiffSq` and the
   1-point diagonal collar-mixed potential:
   `totalAntiDiagonalKernel d x * oddProfileCollarDiffSq a w (Real.log d) x ≤ 0` and
   `totalAntiDiagonalKernel d x * (oddProfile a x * collarMixedDiagKernel a (Real.log d) x * w x ^ 2) ≤ 0`.
2. For every `x ∈ (0, min ℓ_d (Real.log d)) ∪ (Real.log d - min ℓ_d (Real.log d), Real.log d)`
   (the inner unpaid axis intervals),
   `0 < totalAntiDiagonalKernel d x * (oddProfile a x * collarMixedDiagKernel a (Real.log d) x)`. -/
theorem totalAntiDiagonal_oddProfile_nonpos_on_paid_middle_of_twenty_three_le
    {a : ℝ} (ha : 0 < a) {d : ℕ} (hd : 23 ≤ d) (w : ℝ → ℝ) :
    let s := Real.log (d : ℝ)
    let c := antiDiagonalLevel d
    let L := unpaidOuterEnd s c
    let ℓ := 2 * ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) + ArithmeticFunction.vonMangoldt d) /
      ((d : ℝ) - 1)
    (∀ x ∈ Set.Icc L (s - L), x ∈ Set.Ioo (0 : ℝ) s →
      totalAntiDiagonalKernel d x * oddProfileCollarDiffSq a w s x ≤ 0 ∧
      totalAntiDiagonalKernel d x *
        (oddProfile a x * collarMixedDiagKernel a s x * w x ^ 2) ≤ 0) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) (min ℓ s) ∪ Set.Ioo (s - min ℓ s) s,
      0 < totalAntiDiagonalKernel d x * (oddProfile a x * collarMixedDiagKernel a s x)) := by
  intro s c L ℓ
  refine ⟨?_, ?_⟩
  · intro x hx hx_Ioo
    have hpaid : totalAntiDiagonalKernel d x ≤ 0 := by
      by_contra hlt
      have hpos : 0 < totalAntiDiagonalKernel d x := not_le.mp hlt
      have hnear := totalAntiDiagonalKernel_pos_imp_near_axis hd hx_Ioo.1 hx_Ioo.2 hpos
      rcases hnear with h1 | h2
      · linarith [hx.1]
      · linarith [hx.2]
    have hcol_nn : 0 ≤ oddProfileCollarDiffSq a w s x := by
      unfold oddProfileCollarDiffSq
      exact mul_nonneg (mul_nonneg (oddProfile_pos ha hx_Ioo.1).le
        (oddProfile_pos ha (sub_pos.mpr hx_Ioo.2)).le) (sq_nonneg _)
    have hdiag_nn : 0 ≤ oddProfile a x * collarMixedDiagKernel a s x * w x ^ 2 :=
      mul_nonneg (oddProfile_mul_collarMixedDiagKernel_pos ha hx_Ioo).le (sq_nonneg _)
    exact ⟨mul_nonpos_of_nonpos_of_nonneg hpaid hcol_nn,
      mul_nonpos_of_nonpos_of_nonneg hpaid hdiag_nn⟩
  · intro x hx
    have hd2 : 2 ≤ d := by omega
    have hℓ_eq : unpaidInnerEnd s c = ℓ := unpaidInnerEnd_level_eq hd2
    have hx' : x ∈ Set.Ioo (0 : ℝ) (min (unpaidInnerEnd s c) s) ∪
        Set.Ioo (s - min (unpaidInnerEnd s c) s) s := by
      simpa [hℓ_eq] using hx
    have hunp : x ∈ unpaidSet s c := innerEnds_subset_unpaid_level hd2 hx'
    have hx_Ioo : x ∈ Set.Ioo (0 : ℝ) s := ⟨hunp.1, hunp.2.1⟩
    have hkern_pos : 0 < totalAntiDiagonalKernel d x :=
      ((mem_unpaidSet_level_iff d x).mp hunp).2.2
    exact mul_pos hkern_pos (oddProfile_mul_collarMixedDiagKernel_pos ha hx_Ioo)

/-- **Canonical Three-Regime Partition of Any Finite Modulus Sum (`2 ≤ d`):**
Every finite sum over a set `S : Finset ℕ` of moduli `d ≥ 2` splits into:
1. the **nine totally unpaid moduli** `S.filter (· ∈ totalDominatedModuli)` (`{2, 3, 4, 5, 7, 8, 9, 11, 13}`),
2. the **transitional shell** `S.filter (fun d => d ∉ totalDominatedModuli ∧ d < 23)` (`d ∈ [6, 22] \ totalDominatedModuli`), and
3. the **axis-confined regime** `S.filter (fun d => d ∉ totalDominatedModuli ∧ 23 ≤ d)`. -/
theorem sum_moduli_split_nine_transitional_and_axis_confined (S : Finset ℕ) (F : ℕ → ℝ) :
    (∑ d ∈ S, F d) =
      (∑ d ∈ S.filter (· ∈ totalDominatedModuli), F d) +
      (∑ d ∈ S.filter (fun d => d ∉ totalDominatedModuli ∧ d < 23), F d) +
      (∑ d ∈ S.filter (fun d => d ∉ totalDominatedModuli ∧ 23 ≤ d), F d) := by
  have h1 := (Finset.sum_filter_add_sum_filter_not S (· ∈ totalDominatedModuli) F).symm
  have h2 := (Finset.sum_filter_add_sum_filter_not
    (S.filter (· ∉ totalDominatedModuli)) (· < 23) F).symm
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : S.filter (fun a => a ∉ totalDominatedModuli ∧ ¬a < 23) =
      S.filter (fun d => d ∉ totalDominatedModuli ∧ 23 ≤ d) := by
    ext d
    simp only [Finset.mem_filter, not_lt]
  rw [h3] at h2
  linarith

/-! ## §2. Unconditional Pointwise and Integrated Bounds on the Compensated Local Cosh/Sinh Correction (`oddPolarDefect`) -/

/-- Explicit unconditional analytic bound on the linear drop slope of `riemannKernelReal` across
`[0, a + R]`, derived directly from `riemannKernelReal_sub_le_linear_of_nonneg`:
`thetaDerivBound a R = 2 * π * (Real.exp (2 * (a + R)) + 2) * riemannKernelReal 0`. -/
def thetaDerivBound (a R : ℝ) : ℝ :=
  2 * π * (Real.exp (2 * (a + R)) + 2) * riemannKernelReal 0

theorem thetaDerivBound_pos (a R : ℝ) : 0 < thetaDerivBound a R := by
  unfold thetaDerivBound
  have h1 : 0 < Real.exp (2 * (a + R)) + 2 := by positivity
  have h2 : 0 < riemannKernelReal 0 := riemannKernelReal_pos 0
  positivity

/-- Explicit unconditional `cosh`-to-`sinh` polar absorption ratio on `[-R, R]`:
`unconditionalCoshSinhRatio a R = coshSinhPolarRatio a (thetaDerivBound a R) R`. -/
def unconditionalCoshSinhRatio (a R : ℝ) : ℝ :=
  coshSinhPolarRatio a (thetaDerivBound a R) R

theorem unconditionalCoshSinhRatio_pos {a : ℝ} (ha : 0 < a) (R : ℝ) :
    0 < unconditionalCoshSinhRatio a R := by
  unfold unconditionalCoshSinhRatio coshSinhPolarRatio
  have hM := thetaDerivBound_pos a R
  have hch : 0 < Real.cosh (R / 2) := Real.cosh_pos _
  have hΘ : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hsh : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (half_pos ha)
  positivity

/-- **Unconditional Linear Drop Bound on `riemannKernelReal (x - a) - riemannKernelReal (x + a)`:**
For every `a > 0`, `R ≥ 0`, and `x ∈ [0, R]`, without any derivative bound hypothesis,
`riemannKernelReal (x - a) - riemannKernelReal (x + a) ≤ 2 * thetaDerivBound a R * x`. -/
theorem riemannKernelReal_shift_diff_le_thetaDerivBound {a R x : ℝ}
    (ha : 0 < a) (hx : x ∈ Icc (0 : ℝ) R) :
    riemannKernelReal (x - a) - riemannKernelReal (x + a) ≤
      2 * thetaDerivBound a R * x := by
  have habs_eq : riemannKernelReal (x - a) = riemannKernelReal |x - a| := by
    rcases le_or_gt 0 (x - a) with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, WeilExcess.riemannKernelReal_neg]
  have hv₁ : 0 ≤ |x - a| := abs_nonneg _
  have hv : |x - a| ≤ x + a := abs_le.mpr ⟨by linarith [hx.1], by linarith [ha]⟩
  have hdrop := riemannKernelReal_sub_le_linear_of_nonneg hv₁ hv
  have hlen : x + a - |x - a| ≤ 2 * x := by
    have h1 : a - x ≤ |x - a| := by
      rw [abs_sub_comm]
      exact le_abs_self (a - x)
    linarith
  have hexp : Real.exp (2 * (x + a)) + 2 ≤ Real.exp (2 * (a + R)) + 2 := by
    linarith [Real.exp_le_exp.mpr (show 2 * (x + a) ≤ 2 * (a + R) by linarith [hx.2])]
  have hθ : riemannKernelReal |x - a| ≤ riemannKernelReal 0 :=
    strictAntiOn_riemannKernelReal_Ici.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv₁) hv₁
  have hcoeff : 2 * π * (Real.exp (2 * (x + a)) + 2) * riemannKernelReal |x - a| ≤
      thetaDerivBound a R := by
    unfold thetaDerivBound
    have h1 : 2 * π * (Real.exp (2 * (x + a)) + 2) ≤ 2 * π * (Real.exp (2 * (a + R)) + 2) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    exact mul_le_mul h1 hθ (riemannKernelReal_pos _).le (by positivity)
  rw [habs_eq]
  calc riemannKernelReal |x - a| - riemannKernelReal (x + a)
      ≤ 2 * π * (Real.exp (2 * (x + a)) + 2) * riemannKernelReal |x - a| *
          (x + a - |x - a|) := hdrop
    _ ≤ thetaDerivBound a R * (2 * x) :=
        mul_le_mul hcoeff hlen (sub_nonneg.mpr hv) (thetaDerivBound_pos a R).le
    _ = 2 * thetaDerivBound a R * x := by ring

/-- **Unconditional Origin-Vanishing `sinh` Dominance of `oddProfile a` on `[0, R]`:**
For every `a > 0`, `R ≥ 0`, and `x ∈ [0, R]`,
`oddProfile a x ≤ (2 * thetaDerivBound a R / Real.sinh (a / 2)) * Real.sinh (x / 2)`. -/
theorem unconditional_oddProfile_le_sinh {a R x : ℝ} (ha : 0 < a) (hx : x ∈ Icc (0 : ℝ) R) :
    oddProfile a x ≤
      2 * thetaDerivBound a R / Real.sinh (a / 2) * Real.sinh (x / 2) := by
  have hdiff := riemannKernelReal_shift_diff_le_thetaDerivBound ha hx
  have hx_sinh : x ≤ 2 * Real.sinh (x / 2) := by
    have h := self_le_sinh (div_nonneg hx.1 (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  have hsh_pos : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (half_pos ha)
  unfold oddProfile
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sinh (a / 2))]
  calc riemannKernelReal (x - a) - riemannKernelReal (x + a)
      ≤ 2 * thetaDerivBound a R * x := hdiff
    _ ≤ 2 * thetaDerivBound a R * (2 * Real.sinh (x / 2)) :=
        mul_le_mul_of_nonneg_left hx_sinh (mul_pos zero_lt_two (thetaDerivBound_pos a R)).le
    _ = 2 * thetaDerivBound a R / Real.sinh (a / 2) * Real.sinh (x / 2) *
          (2 * Real.sinh (a / 2)) := by
        field_simp [hsh_pos.ne']

/-- **Unconditional Pointwise Dominance of `oddPolarFunction a x * cosh(x / 2)` on `[0, R]`:**
For every `a > 0`, `R ≥ 0`, and `x ∈ [0, R]`,
`oddPolarFunction a x * Real.cosh (x / 2) ≤ unconditionalCoshSinhRatio a R * Real.sinh (x / 2)`. -/
theorem unconditional_oddPolarFunction_mul_cosh_le_sinh {a R x : ℝ} (ha : 0 < a)
    (hx : x ∈ Icc (0 : ℝ) R) :
    oddPolarFunction a x * Real.cosh (x / 2) ≤
      unconditionalCoshSinhRatio a R * Real.sinh (x / 2) := by
  have hm := unconditional_oddProfile_le_sinh ha hx
  have hΘ_mono : riemannKernelReal R ≤ riemannKernelReal x :=
    strictAntiOn_riemannKernelReal_Ici.antitoneOn (mem_Ici.mpr hx.1)
      (mem_Ici.mpr (hx.1.trans hx.2)) hx.2
  have hΘR : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hsh : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (half_pos ha)
  have hch : Real.cosh (x / 2) ≤ Real.cosh (R / 2) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (div_nonneg hx.1 (by norm_num)),
      abs_of_nonneg (div_nonneg (hx.1.trans hx.2) (by norm_num))]
    linarith [hx.2]
  have hm_nonneg : 0 ≤ oddProfile a x := by
    rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
    · rw [oddProfile_zero]
    · exact (oddProfile_pos ha hx_pos).le
  rw [oddPolarFunction_eq_oddProfile_div]
  calc oddProfile a x / riemannKernelReal x * Real.cosh (x / 2)
      ≤ oddProfile a x / riemannKernelReal R * Real.cosh (R / 2) :=
        mul_le_mul (div_le_div_of_nonneg_left hm_nonneg hΘR hΘ_mono)
          hch (Real.cosh_pos _).le (div_nonneg hm_nonneg hΘR.le)
    _ ≤ (2 * thetaDerivBound a R / Real.sinh (a / 2) * Real.sinh (x / 2)) /
          riemannKernelReal R * Real.cosh (R / 2) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hm hΘR.le) (Real.cosh_pos _).le
    _ = unconditionalCoshSinhRatio a R * Real.sinh (x / 2) := by
        unfold unconditionalCoshSinhRatio coshSinhPolarRatio
        field_simp [hΘR.ne', hsh.ne']

/-- For every `a > 0` and `x : ℝ`, `0 ≤ oddProfile a x * Real.sinh (x / 2)`. -/
theorem oddProfile_mul_sinh_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 ≤ oddProfile a x * Real.sinh (x / 2) := by
  rcases lt_trichotomy x 0 with hlt | rfl | hgt
  · have h1 : oddProfile a x < 0 := by
      have := oddProfile_pos ha (neg_pos.mpr hlt)
      rw [oddProfile_neg] at this
      linarith
    have h2 : Real.sinh (x / 2) < 0 := Real.sinh_neg_iff.mpr (by linarith)
    exact mul_nonneg_of_nonpos_of_nonpos h1.le h2.le
  · simp [oddProfile_zero]
  · exact mul_nonneg (oddProfile_pos ha hgt).le (Real.sinh_pos_iff.mpr (half_pos hgt)).le

/-- **Unconditional Pointwise Upper Bound on `oddPolarDefectDensity` Across `[-R, R]`:**
For every `a > 0`, `R ≥ 0`, `θ : ℝ`, and `x ∈ [-R, R]`,
`oddPolarDefectDensity a θ x ≤ (unconditionalCoshSinhRatio a R - θ) * (oddProfile a x * Real.sinh (x / 2))`
and
`max (oddPolarDefectDensity a θ x) 0 ≤ max (unconditionalCoshSinhRatio a R - θ) 0 * (oddProfile a x * Real.sinh (x / 2))`. -/
theorem oddPolarDefectDensity_le_on_Icc {a R x : ℝ} (ha : 0 < a) (θ : ℝ)
    (hx : x ∈ Set.Icc (-R) R) :
    oddPolarDefectDensity a θ x ≤
        (unconditionalCoshSinhRatio a R - θ) * (oddProfile a x * Real.sinh (x / 2)) ∧
      max (oddPolarDefectDensity a θ x) 0 ≤
        max (unconditionalCoshSinhRatio a R - θ) 0 *
          (oddProfile a x * Real.sinh (x / 2)) := by
  have hx_abs : |x| ∈ Set.Icc (0 : ℝ) R := ⟨abs_nonneg x, abs_le.mpr hx⟩
  have hdom := unconditional_oddPolarFunction_mul_cosh_le_sinh ha hx_abs
  have hm_abs : 0 ≤ oddProfile a |x| := by
    rcases eq_or_lt_of_le hx_abs.1 with h0 | hpos
    · rw [← h0, oddProfile_zero]
    · exact (oddProfile_pos ha hpos).le
  have hmul := mul_le_mul_of_nonneg_left hdom hm_abs
  have heven_lhs : oddProfile a |x| * (oddPolarFunction a |x| * Real.cosh (|x| / 2)) =
      riemannKernelReal x * oddPolarFunction a x ^ 2 * Real.cosh (x / 2) := by
    have h1 : oddProfile a |x| = riemannKernelReal |x| * oddPolarFunction a |x| := by
      rw [oddPolarFunction_eq_oddProfile_div, mul_div_cancel₀ _ (riemannKernelReal_pos |x|).ne']
    rw [h1]
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      ring
    · rw [abs_of_neg h, WeilExcess.riemannKernelReal_neg, oddPolarFunction_neg,
        neg_div, Real.cosh_neg]
      ring
  have heven_rhs : oddProfile a |x| * (unconditionalCoshSinhRatio a R * Real.sinh (|x| / 2)) =
      unconditionalCoshSinhRatio a R * (oddProfile a x * Real.sinh (x / 2)) := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      ring
    · rw [abs_of_neg h, oddProfile_neg, neg_div, Real.sinh_neg]
      ring
  rw [heven_lhs, heven_rhs] at hmul
  have hle1 : oddPolarDefectDensity a θ x ≤
      (unconditionalCoshSinhRatio a R - θ) * (oddProfile a x * Real.sinh (x / 2)) := by
    unfold oddPolarDefectDensity
    linarith
  have hnn : 0 ≤ max (unconditionalCoshSinhRatio a R - θ) 0 *
      (oddProfile a x * Real.sinh (x / 2)) :=
    mul_nonneg (le_max_right _ _) (oddProfile_mul_sinh_nonneg ha x)
  have hle2 : max (oddPolarDefectDensity a θ x) 0 ≤
      max (unconditionalCoshSinhRatio a R - θ) 0 *
        (oddProfile a x * Real.sinh (x / 2)) := by
    refine max_le ?_ hnn
    exact hle1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (oddProfile_mul_sinh_nonneg ha x))
  exact ⟨hle1, hle2⟩

/-- **Unconditional Quantitative Upper Bound on `oddPolarDefect a θ w` for All `θ : ℝ`:**
For every `a > 0`, `R ≥ 0`, `θ : ℝ`, and every continuous compactly supported even profile `w`
supported in `(-R, R)` (`∀ u, R ≤ u → w u = 0`), the compensated local cosh/sinh correction is
bounded unconditionally by
`oddPolarDefect a θ w ≤ max (unconditionalCoshSinhRatio a R - θ) 0 * oddSinhPotential a w`. -/
theorem unconditional_oddPolarDefect_le_oddSinhPotential {a R : ℝ} (ha : 0 < a) (θ : ℝ)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) (hsupp : ∀ u, R ≤ u → w u = 0) :
    oddPolarDefect a θ w ≤
      max (unconditionalCoshSinhRatio a R - θ) 0 * oddSinhPotential a w := by
  unfold oddPolarDefect oddSinhPotential
  rw [← integral_const_mul]
  have hw2c : HasCompactSupport (fun x : ℝ => w x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hwc ⊢
    filter_upwards [hwc] with x hx; simp [hx]
  have hint1 : Integrable (fun x => max (oddPolarDefectDensity a θ x) 0 * w x ^ 2) :=
    (((continuous_oddPolarDefectDensity a θ).max continuous_const).mul
      (hw.pow 2)).integrable_of_hasCompactSupport hw2c.mul_left
  have hint2 : Integrable (fun x => max (unconditionalCoshSinhRatio a R - θ) 0 *
      (oddProfile a x * Real.sinh (x / 2) * w x ^ 2)) :=
    (continuous_const.mul (((continuous_oddProfile a).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))).mul
      (hw.pow 2))).integrable_of_hasCompactSupport hw2c.mul_left.mul_left
  refine integral_mono hint1 hint2 fun x => ?_
  by_cases hxR : R ≤ |x|
  · have hw0 : w x = 0 := by
      rcases le_or_gt 0 x with h | h
      · exact hsupp x ((abs_of_nonneg h) ▸ hxR)
      · rw [← heven x]
        exact hsupp (-x) ((abs_of_neg h) ▸ hxR)
    simp [hw0]
  · have hx_Icc : x ∈ Set.Icc (-R) R := abs_le.mp (not_le.mp hxR).le
    have hpt := (oddPolarDefectDensity_le_on_Icc ha θ hx_Icc).2
    have hmul := mul_le_mul_of_nonneg_right hpt (sq_nonneg (w x))
    linarith

/-- **Unconditional Exact Vanishing of `oddPolarDefect a θ w` and Cosh-to-Sinh Absorption for
`unconditionalCoshSinhRatio a R ≤ θ`:**
For every `a > 0`, `R ≥ 0`, `θ : ℝ` with `unconditionalCoshSinhRatio a R ≤ θ`, and every continuous
compactly supported even profile `w` supported in `(-R, R)`:
1. `oddPolarDefect a θ w = 0`,
2. `phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) ≤ θ * oddSinhPotential a w`. -/
theorem unconditional_oddPolarDefect_eq_zero_of_le {a R θ : ℝ} (ha : 0 < a)
    (hθ : unconditionalCoshSinhRatio a R ≤ θ)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) (hsupp : ∀ u, R ≤ u → w u = 0) :
    oddPolarDefect a θ w = 0 ∧
      phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) ≤ θ * oddSinhPotential a w := by
  have hle := unconditional_oddPolarDefect_le_oddSinhPotential ha θ hw hwc heven hsupp
  have hmax : max (unconditionalCoshSinhRatio a R - θ) 0 = 0 :=
    max_eq_right (sub_nonpos.mpr hθ)
  rw [hmax, zero_mul] at hle
  have hdef0 : oddPolarDefect a θ w = 0 :=
    le_antisymm hle (oddPolarDefect_nonneg a θ w)
  have hbal := coshMass_sub_sinh_eq_defect_sub_reserve a θ hw hwc
  have hres := oddPolarReserve_nonneg a θ w
  exact ⟨hdef0, by linarith⟩

/-! ## §3. Odd-Sector Cross-Lobe Estimates, Individual-Lobe Polar Laws, Cross-Lobe Weil Polarization, and the Four-Term Positive-Lobe Excess -/

/-- **Universal Odd-Sector Lobe Pairing with Any Odd Mass Vector:**
For every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`) and every odd mass vector
`z : MassSpace` (`reflectMass z = -z`):
1. `⟪(negGraph p).val.fst, z⟫_ℝ = -⟪(posGraph p).val.fst, z⟫_ℝ`,
2. `⟪(absGraph p).val.fst, z⟫_ℝ = 0`,
3. `⟪(posGraph p).val.fst, z⟫_ℝ = (1 / 2) * ⟪p.val.fst, z⟫_ℝ`,
4. `⟪(negGraph p).val.fst, z⟫_ℝ = -(1 / 2) * ⟪p.val.fst, z⟫_ℝ`. -/
theorem odd_lobe_inner_odd_mass {p : SourceGraph} (hp : reflectGraph p = -p)
    {z : MassSpace} (hz : reflectMass z = -z) :
    ⟪(negGraph p).val.fst, z⟫_ℝ = -⟪(posGraph p).val.fst, z⟫_ℝ ∧
      ⟪(absGraph p).val.fst, z⟫_ℝ = 0 ∧
      ⟪(posGraph p).val.fst, z⟫_ℝ = (1 / 2 : ℝ) * ⟪p.val.fst, z⟫_ℝ ∧
      ⟪(negGraph p).val.fst, z⟫_ℝ = -(1 / 2 : ℝ) * ⟪p.val.fst, z⟫_ℝ := by
  have h1 := reflectMass.inner_map_map (posGraph p).val.fst z
  have h2 : reflectMass (posGraph p).val.fst = (negGraph p).val.fst := by
    rw [← reflectGraph_fst, reflectGraph_posGraph_of_odd hp]
  rw [h2, hz, inner_neg_right] at h1
  have hneg : ⟪(negGraph p).val.fst, z⟫_ℝ = -⟪(posGraph p).val.fst, z⟫_ℝ := by linarith
  have hadd : (absGraph p).val.fst = (posGraph p).val.fst + (negGraph p).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_add_negGraph p).symm
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_sub_negGraph p).symm
  have habs : ⟪(absGraph p).val.fst, z⟫_ℝ = 0 := by
    rw [hadd, inner_add_left, hneg, add_neg_cancel]
  have hp_eq : ⟪p.val.fst, z⟫_ℝ = 2 * ⟪(posGraph p).val.fst, z⟫_ℝ := by
    rw [hsub, inner_sub_left, hneg]
    ring
  exact ⟨hneg, habs, by linarith, by linarith⟩

/-- **Odd-Sector Lobe Pairing Identities for `tanhL` and `oddPolarVectorAt a ha`:**
For every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`) and every admissible shift `a`:
1. `⟪(absGraph p).val.fst, tanhL⟫_ℝ = 0`,
2. `⟪(posGraph p).val.fst, tanhL⟫_ℝ = (1 / 2) * ⟪p.val.fst, tanhL⟫_ℝ`,
3. `⟪(negGraph p).val.fst, tanhL⟫_ℝ = -(1 / 2) * ⟪p.val.fst, tanhL⟫_ℝ`,
4. `⟪(absGraph p).val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ = 0`,
5. `⟪(posGraph p).val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ = (1 / 2) * ⟪p.val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ`,
6. `⟪(negGraph p).val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ = -(1 / 2) * ⟪p.val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ`. -/
theorem odd_lobe_tanhL_and_oddPolarVectorAt_identities {p : SourceGraph} (hp : reflectGraph p = -p)
    (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    ⟪(absGraph p).val.fst, tanhL⟫_ℝ = 0 ∧
      ⟪(posGraph p).val.fst, tanhL⟫_ℝ = (1 / 2 : ℝ) * ⟪p.val.fst, tanhL⟫_ℝ ∧
      ⟪(negGraph p).val.fst, tanhL⟫_ℝ = -(1 / 2 : ℝ) * ⟪p.val.fst, tanhL⟫_ℝ ∧
      ⟪(absGraph p).val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ = 0 ∧
      ⟪(posGraph p).val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ =
        (1 / 2 : ℝ) * ⟪p.val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ ∧
      ⟪(negGraph p).val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ =
        -(1 / 2 : ℝ) * ⟪p.val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ := by
  obtain ⟨_, ht_abs, ht_pos, ht_neg⟩ := odd_lobe_inner_odd_mass hp reflectMass_tanhL
  have hψ_odd : reflectMass (oddPolarVectorAt a ha).val.fst = -(oddPolarVectorAt a ha).val.fst :=
    mem_oddSector.mp (oddPolarVectorAt_fst_mem_oddSector a ha)
  obtain ⟨_, hψ_abs, hψ_pos, hψ_neg⟩ := odd_lobe_inner_odd_mass hp hψ_odd
  exact ⟨ht_abs, ht_pos, ht_neg, hψ_abs, hψ_pos, hψ_neg⟩

/-- **Individual-Lobe Odd-Polar Balance for Odd Eigenvectors (`odd_eigenvector_posGraph_and_negGraph_oddPolarVectorAt_pairing`):**
For every odd eigenvector `resolvent w = μ • w` (`reflectMass w = -w`) with `q = rieszLift w` and
every nonzero admissible shift `a`, **both individual nodal lobes** `posGraph q` and `negGraph q`
satisfy the exact odd-polar eigenvector balance:
1. `(2 * μ - 1) * ⟪(posGraph q).val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ + μ * ⟪(posGraph q).val.fst, tanhL⟫_ℝ = 0`,
2. `(2 * μ - 1) * ⟪(negGraph q).val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ + μ * ⟪(negGraph q).val.fst, tanhL⟫_ℝ = 0`. -/
theorem odd_eigenvector_posGraph_and_negGraph_oddPolarVectorAt_pairing
    {a : ℝ} (hane : a ≠ 0) (ha : 1 < 2 * Real.exp (-2 * |a|))
    {μ : ℝ} {w : MassSpace} (hodd : reflectMass w = -w) (heig : resolvent w = μ • w) :
    let q := rieszLift w
    (2 * μ - 1) * ⟪(posGraph q).val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ +
        μ * ⟪(posGraph q).val.fst, tanhL⟫_ℝ = 0 ∧
      (2 * μ - 1) * ⟪(negGraph q).val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ +
        μ * ⟪(negGraph q).val.fst, tanhL⟫_ℝ = 0 := by
  intro q
  have hq_odd : reflectGraph q = -q := by
    change reflectGraph (rieszLift w) = -rieszLift w
    rw [← rieszLift_reflectMass, hodd, ← neg_one_smul ℝ w, rieszLift_smul, neg_one_smul]
  obtain ⟨_, ht_pos, ht_neg, _, hψ_pos, hψ_neg⟩ :=
    odd_lobe_tanhL_and_oddPolarVectorAt_identities hq_odd a ha
  have hpair := eigenvector_oddPolarVectorAt_pairing hane ha heig
  have hq_fst : q.val.fst = μ • w := heig
  have hq_pair : (2 * μ - 1) * ⟪q.val.fst, (oddPolarVectorAt a ha).val.fst⟫_ℝ +
      μ * ⟪q.val.fst, tanhL⟫_ℝ = 0 := by
    rw [hq_fst, real_inner_smul_left, real_inner_smul_left]
    linear_combination μ * hpair
  rw [hψ_pos, ht_pos, hψ_neg, ht_neg]
  exact ⟨by linarith, by linarith⟩

/-- **Odd-Sector Cross-Lobe `weilBilin` and `weilForm` Polarization Laws (`odd_weilForm_and_weilBilin_lobe_polarization`):**
For every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`):
1. `weilForm (absGraph p) = sourceEnergy (primGraph (absGraph p))`,
2. `weilForm (posGraph p) = weilForm (negGraph p)`,
3. `weilBilin (posGraph p) (negGraph p) = sourcePair (posGraph p) (negGraph p) + (1 / 2) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 + (1 / 2) * ⟪p.val.fst, tanhL⟫_ℝ ^ 2`,
4. `weilForm (absGraph p) - weilForm p = 4 * weilBilin (posGraph p) (negGraph p)`,
5. `weilForm (absGraph p) + weilForm p = 4 * weilForm (posGraph p)`. -/
theorem odd_weilForm_and_weilBilin_lobe_polarization {p : SourceGraph}
    (hp : reflectGraph p = -p) :
    weilForm (absGraph p) = sourceEnergy (primGraph (absGraph p)) ∧
      weilForm (posGraph p) = weilForm (negGraph p) ∧
      weilBilin (posGraph p) (negGraph p) =
        sourcePair (posGraph p) (negGraph p) +
          (1 / 2 : ℝ) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 +
          (1 / 2 : ℝ) * ⟪p.val.fst, tanhL⟫_ℝ ^ 2 ∧
      weilForm (absGraph p) - weilForm p =
        4 * weilBilin (posGraph p) (negGraph p) ∧
      weilForm (absGraph p) + weilForm p =
        4 * weilForm (posGraph p) := by
  obtain ⟨ht_abs, ht_pos, ht_neg⟩ := (odd_lobe_inner_odd_mass hp reflectMass_tanhL).2
  have hp_fst_odd : reflectMass p.val.fst = -p.val.fst := by
    rw [← reflectGraph_fst, hp]
    rfl
  have hp_oneL : ⟪p.val.fst, oneL⟫_ℝ = 0 := inner_oneL_eq_zero_of_odd hp_fst_odd
  obtain ⟨h1_eq, h1_pos, h1_neg⟩ := inner_posGraph_oneL_eq_inner_negGraph_oneL hp_oneL
  have hw_abs : weilForm (absGraph p) = sourceEnergy (primGraph (absGraph p)) := by
    unfold weilForm
    rw [ht_abs, sourceEnergy_primGraph]
    ring
  have hE_eq := sourceEnergy_posGraph_eq_negGraph_of_odd hp
  have hw_pos : weilForm (posGraph p) =
      sourceEnergy (posGraph p) +
        (1 / 2 : ℝ) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 -
        (1 / 2 : ℝ) * ⟪p.val.fst, tanhL⟫_ℝ ^ 2 := by
    unfold weilForm
    rw [h1_pos, ht_pos]
    ring
  have hw_neg : weilForm (negGraph p) =
      sourceEnergy (posGraph p) +
        (1 / 2 : ℝ) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 -
        (1 / 2 : ℝ) * ⟪p.val.fst, tanhL⟫_ℝ ^ 2 := by
    unfold weilForm
    rw [← hE_eq, h1_neg, ht_neg]
    ring
  have hw_p : weilForm p = sourceEnergy p - 2 * ⟪p.val.fst, tanhL⟫_ℝ ^ 2 := by
    unfold weilForm
    rw [hp_oneL]
    ring
  have hwb : weilBilin (posGraph p) (negGraph p) =
      sourcePair (posGraph p) (negGraph p) +
        (1 / 2 : ℝ) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 +
        (1 / 2 : ℝ) * ⟪p.val.fst, tanhL⟫_ℝ ^ 2 := by
    unfold weilBilin
    have hsp : ⟪posGraph p, negGraph p⟫_ℝ - 2 * ⟪(posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ =
        sourcePair (posGraph p) (negGraph p) := by
      rw [sourcePair_eq_graph_inner]
      rfl
    rw [hsp, h1_pos, ← h1_eq, ht_pos, ht_neg]
    ring
  have hE_abs := sourceEnergy_absGraph_eq p
  have hE_pos_q := sourceEnergy_posGraph_eq_quarter_absGraph_add_self_of_odd hp
  have hprim_abs := sourceEnergy_primGraph (absGraph p)
  refine ⟨hw_abs, hw_pos.trans hw_neg.symm, hwb, ?_, ?_⟩
  · linarith
  · linarith

/-- For every `u : MassSpace`, `⟪resolvent u, u⟫_ℝ ≤ ‖u‖ ^ 2`. -/
theorem inner_resolvent_le_norm_sq (u : MassSpace) :
    ⟪resolvent u, u⟫_ℝ ≤ ‖u‖ ^ 2 := by
  have hnorm : ‖resolvent u‖ ≤ 1 * ‖u‖ :=
    (resolvent.le_opNorm u).trans (mul_le_mul_of_nonneg_right norm_resolvent_le (norm_nonneg u))
  calc ⟪resolvent u, u⟫_ℝ ≤ ‖resolvent u‖ * ‖u‖ := real_inner_le_norm _ _
    _ ≤ (1 * ‖u‖) * ‖u‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg u)
    _ = ‖u‖ ^ 2 := by ring

/-- **Exact Four-Term Positive-Lobe Excess Identity & Unconditional Two-Sided Cross-Lobe Sandwich
on the Odd Sector (`odd_eigenvector_four_term_excess_and_cross_lobe_sandwich`):**
For every odd eigenvector `resolvent w = μ • w` (`0 < μ`, `reflectMass w = -w`) with
`q = rieszLift w`:
1. **Exact four-term positive-lobe excess identity:**
   `(stationaryEnergy (thetaProduct (posGraph q).val.fst) + ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ - ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) - ((1 / 2) * ‖q.val.fst‖ ^ 2 - ⟪groundPotentialOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ) = ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2`,
2. **Unconditional two-sided cross-lobe sandwich:**
   `0 ≤ 4 * μ ^ 2 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`,
   `4 * μ ^ 2 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤ -4 * μ ^ 2 * sourcePair (posGraph q) (negGraph q)`,
   `-4 * μ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤ 4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`,
   `4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤ (1 - μ) * ‖q.val.fst‖ ^ 2`, and
   `-4 * sourcePair (posGraph q) (negGraph q) ≤ ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`. -/
theorem odd_eigenvector_four_term_excess_and_cross_lobe_sandwich
    {μ : ℝ} (hμ : 0 < μ) {w : MassSpace} (hodd : reflectMass w = -w)
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    (stationaryEnergy (thetaProduct (posGraph q).val.fst) +
        ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) -
        ((1 / 2 : ℝ) * ‖q.val.fst‖ ^ 2 -
          ⟪groundPotentialOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ) =
      ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 ∧
    0 ≤ 4 * μ ^ 2 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ∧
    4 * μ ^ 2 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤
      -4 * μ ^ 2 * sourcePair (posGraph q) (negGraph q) ∧
    -4 * μ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤
      4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ∧
    4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤
      (1 - μ) * ‖q.val.fst‖ ^ 2 ∧
    -4 * sourcePair (posGraph q) (negGraph q) ≤
      ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 := by
  intro q
  have hq_odd : reflectGraph q = -q := (odd_eigenvector_lobe_energy_and_snd_sq hμ.ne' hodd heig).1
  obtain ⟨hpos_sq, _⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hq_odd
  have h5 := posGraph_five_term_jump_eq_diagonals_of_eigenvector hμ.ne' heig
  have hdiag := arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential (posGraph q).val.fst
  have hexcess :
      (stationaryEnergy (thetaProduct (posGraph q).val.fst) +
          ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ -
          ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) -
          ((1 / 2 : ℝ) * ‖q.val.fst‖ ^ 2 -
            ⟪groundPotentialOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ) =
        ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 := by
    change _ = _ at h5
    rw [hpos_sq] at h5 hdiag
    have hid : ((2 * μ - 1) / μ) * ((1 / 2 : ℝ) * ‖q.val.fst‖ ^ 2) +
        ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 = 0 := by
      field_simp [hμ.ne']
      ring
    linarith
  obtain ⟨_, hprime_nn, _, hprime_le⟩ :=
    stationary_and_primeShift_le_neg_sourcePair_posGraph_negGraph q
  have hμ2 : 0 ≤ 4 * μ ^ 2 := by positivity
  have h1 : 0 ≤ 4 * μ ^ 2 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ :=
    mul_nonneg hμ2 hprime_nn
  have h2 : 4 * μ ^ 2 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤
      -4 * μ ^ 2 * sourcePair (posGraph q) (negGraph q) := by
    have := mul_le_mul_of_nonneg_left hprime_le hμ2
    linarith
  have hres_low := (neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph hμ heig).2
  have h3 : -4 * μ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤
      4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
    linarith [hres_low]
  have habs_res := inner_resolvent_absGraph_of_eigenvector heig
  have habs_le : ⟪resolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ ≤ ‖q.val.fst‖ ^ 2 := by
    refine (inner_resolvent_le_norm_sq (absGraph q).val.fst).trans ?_
    rw [norm_absGraph_fst_sq]
  have h4 : 4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤
      (1 - μ) * ‖q.val.fst‖ ^ 2 := by
    change ⟪resolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ = _ at habs_res
    linarith
  have h5_bound := (neg_four_sourcePair_posGraph_negGraph_le_of_eigenvector hμ.ne' heig).1
  exact ⟨hexcess, h1, h2, h3, h4, h5_bound⟩

/-- **Automatic Strict Cross-Lobe Positivity for Every Nonzero Odd Eigenvector:**
Because every odd vector `w` is automatically orthogonal to `oneL`, for every nonzero odd
eigenvector `resolvent w = μ • w` (`0 < μ`, `w ≠ 0`, `reflectMass w = -w`) with `q = rieszLift w`:
1. `0 < -⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ`,
2. `⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ < -sourcePair (posGraph q) (negGraph q)`,
3. `0 < -μ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤ ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`. -/
theorem odd_eigenvector_cross_lobe_strict_bounds_of_ne_zero
    {μ : ℝ} (hμ : 0 < μ) {w : MassSpace} (hw0 : w ≠ 0) (hodd : reflectMass w = -w)
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    0 < -⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ ∧
      ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ <
        -sourcePair (posGraph q) (negGraph q) ∧
      0 < -μ ^ 2 * sourcePair (posGraph q) (negGraph q) ∧
      -μ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤
        ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
  intro q
  have hprim : ⟪w, oneL⟫_ℝ = 0 := inner_oneL_eq_zero_of_odd hodd
  have hq_fst : q.val.fst = μ • w := heig
  have hq0 : q ≠ 0 := by
    intro h
    have hf : q.val.fst = 0 := by rw [h]; rfl
    rw [hq_fst, smul_eq_zero] at hf
    exact hw0 (hf.resolve_left hμ.ne')
  have hq_prim : ⟪q.val.fst, oneL⟫_ℝ = 0 := by
    rw [hq_fst, real_inner_smul_left, hprim, mul_zero]
  obtain ⟨hpos_ne, hneg_ne⟩ := posGraph_ne_zero_and_negGraph_ne_zero_of_primitive hq0 hq_prim
  have hstat := neg_pos.mpr (inner_fullGroundEquiv_posGraph_negGraph_snd_neg_of_ne_zero hpos_ne hneg_ne)
  have hlt := primeShift_lt_neg_sourcePair_posGraph_negGraph_of_ne_zero hpos_ne hneg_ne
  obtain ⟨hpos_sp, _⟩ := inner_resolvent_posGraph_negGraph_pos_of_primitive_eigenvector
    hμ hw0 hprim heig
  have hle := (neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph hμ heig).2
  exact ⟨hstat, hlt, hpos_sp, hle⟩

/-- **Cross-Lobe `weilBilin` Exclusion Criterion for `RiemannHypothesis` on the Odd Sector:**
If for every nonzero odd eigenvector `resolvent w = μ • w` (`1 / 2 < μ`, `reflectMass w = -w`) with
`q = rieszLift w` and `u_0 = (primGraph (absGraph q)).val.fst`:
1. `⟪resolvent u_0, u_0⟫_ℝ ≤ (1 / 2) * ‖u_0‖ ^ 2`, and
2. the cross-lobe Weil pairing satisfies
   `weilBilin (posGraph q) (negGraph q) ≤ (1 / 2) * ⟪q.val.fst, tanhL⟫_ℝ ^ 2`
   (which is `weilBilin (posGraph q) (negGraph q) ≤ 0` on `ker ⟪·, tanhL⟫_ℝ`),
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_odd_eigenvector_cross_lobe_weilBilin_le_tanhL_sq
    (hray : ∀ (μ : ℝ) (w : MassSpace),
      1 / 2 < μ → w ≠ 0 → reflectMass w = -w → resolvent w = μ • w →
        ⟪resolvent (primGraph (absGraph (rieszLift w))).val.fst,
            (primGraph (absGraph (rieszLift w))).val.fst⟫_ℝ ≤
          (1 / 2 : ℝ) * ‖(primGraph (absGraph (rieszLift w))).val.fst‖ ^ 2)
    (hwb : ∀ (μ : ℝ) (w : MassSpace),
      1 / 2 < μ → w ≠ 0 → reflectMass w = -w → resolvent w = μ • w →
        weilBilin (posGraph (rieszLift w)) (negGraph (rieszLift w)) ≤
          (1 / 2 : ℝ) * ⟪(rieszLift w).val.fst, tanhL⟫_ℝ ^ 2) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_odd_eigenvector_oneL_defect_le_neg_four_sourcePair hray ?_
  intro μ w hμ hw0 hodd heig
  have hμ0 : 0 < μ := by linarith
  have hq_odd : reflectGraph (rieszLift w) = -rieszLift w :=
    (odd_eigenvector_lobe_energy_and_snd_sq hμ0.ne' hodd heig).1
  have hpol := (odd_weilForm_and_weilBilin_lobe_polarization hq_odd).2.2.1
  have hle := hwb μ w hμ hw0 hodd heig
  linarith

end GaloisForLFunctions.TransHorizonIncidenceMechanics

end
