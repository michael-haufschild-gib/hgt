import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.Stage1DualSixthFreeEnergy
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane

/-!
# Stage-1 `parentPoisson` energy at `Q = {0}` via dual sixth-power-free factored moments

This module closes the Stage-1 tiny-bin `parentPoisson` energy estimate on `17/25 ≤ r ≤ 19/26`:

1. **Analytic & algebraic bridges (`mellin_childLogTest_strip_decay`,
   `scaleProfile_childLogTest_rawMoment`, `canonicalPrimeAmplitude_eq_rayPrimePolynomial_of_gt_four`,
   `targetRow_deletedBase_coeff`):**
   Connects the unpunctured `targetRow (deletedBase data).inverse u_free` dyadic polynomial and
   prime-slot `canonicalPrimeAmplitude` factors from `Stage1DualSixthFreeEnergy` to:
   - `HeckeInverseAmplification.no_slot_endpoint` (sixth-power amplification without prime slots),
   - `DetectorDictionaryInverseMarkedReference.deleted_source_energy` at `j = 1` (Stage-0 slot
     keeping in Case 2),
   - `HeckeDyadic.buffered_polynomial_bound` + `HeckePrimeRay.ray_prime_bin_bound` +
     `uncalibrated_subset_slot_row_count` (buffered zero-level partition in Case 3).

2. **Factored sixth-power-free `L^2` bound (`dual_sixth_free_factored_energy`):**
   Bounds the normalized `L^2` sum over `u_free ∈ S_free` (`rowNorm u_free ≤ U ^ H_free`) of
   `inputConjugateRow ... X' u_free.val * ∏ j ∈ T', slotCharSum ... j u_free.val` by
   `C * U ^ (1 - 3 * ell - 5 * u_sel - x6 + ε_out) * (1 + |s|) ^ (2 * deg)` for `|s| ≤ S_cut`,
   together with a polynomial-in-`U` coarse bound for arbitrary `s : ℝ`.

3. **Cell-summed `parentPoisson` bound at `Q = {0}` (`dual_parentPoisson_q0_cell_energy`):**
   Combines `parentPoisson_eq_rowMajorantBall_sum`, the `z = 0` slice, `inputConjugateRow_q0_clean`
   + `gcdElement_fiber_card_le`, sixth-power factoring `w₁ = g₆ ^ 6 * u₀.val` +
   `inputConjugateRow_mul_sixth_pow`, multi-prime `L^2` unpuncturing
   `inputConjugateRow_markedRadial_unpuncture_total_scale` + `puncture_card_pow_1024_le_divisors`,
   `exists_bad12_base_transfer_on_pool` + `bad12FreeSplit_fiber_card_le`, and
   `markedRadial_fourier_l2_le_factored`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Classical Topology ContDiff SchwartzMap FourierTransform ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

namespace Stage1ParentPoissonEnergy

open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open CubicSieve CenteredMomentFourier
open FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment InverseMoment
open InverseSecondPrincipalCaller InverseFirstPriorityParents InversePrioritySecondSource
open InversePrincipalEnergy UniqueFactorizationMonoid
open InverseInitialArithmetic RayFourExpansion
open CanonicalCoefficientClass IdealDivisorBound
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands Parameters
open HeckeDetectorRawFiber HeckeDetectorFiberPartition HeckeDetectorBatch
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection
open HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorRowwisePolynomial
open HeckeDetectorCoefficientTransfer HeckePrimeRay
open DetectorDictionaryInverseRawInput DetectorDictionaryInverseRawInitialGates
open DetectorDictionaryInverseRawReference DetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedPhysicalRows InverseInitialMarkedDictionary
open InverseInitialDetectorSource InverseInitialPhysicalSlots InverseInitialExcludedPool
open JointLogSeparation Stage1CubeBins Stage1DualRowMoments Stage1ReciprocityAndUnpuncture
open Stage1DualSixthFreeEnergy SubSevenEighthsHighTransport SubSevenEighthsZeroFree
open GaloisForLFunctions.FamilyContinuationTheory
open GaloisForLFunctions.FamilyContinuationTheory.Budget

local notation "O" => Eisenstein.O

/-! ### Part I: Plain-`ℝ` exponent certificates and analytic dictionary helpers -/

/-- Plain-`ℝ` exponent bound for the low-conductor (`H_sub ≤ 3/100`) and small-`H_free`
(`H_free ≤ max (1/10) (r_unm + 10 * t_dual)`) branches using `no_slot_endpoint` and trivial
Cauchy-Schwarz `U ^ z_T` on prime slots: across `r ∈ [17/25, 19/26]`, `θ ∈ [0, 1]`,
`0 ≤ z_Jv ≤ ell ≤ 3/500`, `x₆ ≥ 0`, `V₀ ≥ 0`, `z_J ≥ 0`, `z_coll ≥ 0`, and `t_dual ≤ 1/1000`,
if either `H_sub ≤ 3/100` (with `H_free ≥ -t_dual`) or `H_sub = H_free ≤ max (1/10) (r_unm + 10 * t_dual)`
(with `H_sub ≥ 0`), then `3 * ell + 5 * u_sel + x6 + max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + z_T ≤ 1 - 1 / 40`. -/
theorem stage1_low_or_small_H_exponent
    {r θ ell z_Jv x6 V₀ z_J z_coll H_sub t_dual : ℝ}
    (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (_hell0 : 0 ≤ ell) (hell1 : ell ≤ 3 / 500)
    (hJv0 : 0 ≤ z_Jv) (hJv : z_Jv ≤ ell)
    (_hx6 : 0 ≤ x6) (hV0 : 0 ≤ V₀) (hzJ0 : 0 ≤ z_J) (hzc0 : 0 ≤ z_coll)
    (ht0 : 0 ≤ t_dual) (ht1 : t_dual ≤ 1 / 1000) :
    let u_sel := θ * stage1Width r
    let H_th := (1 - θ) * 1 + θ * stage1DualScale r
    let z_rem_th := (1 - θ) * ((1 - r) / 2) + θ * stage1RemWidth r
    let H_free := H_th - 6 * ell - 6 * x6
    let r_unm := r - V₀ - 3 * ell + z_Jv - z_coll
    let r_pos := max 0 r_unm
    let z_T := z_rem_th - z_Jv - z_J - z_coll
    0 ≤ z_T → 0 ≤ H_sub → -t_dual ≤ H_free →
    (H_sub ≤ 3 / 100 ∨ (H_sub = H_free ∧ H_free ≤ max (1 / 10) (r_unm + 10 * t_dual))) →
    3 * ell + 5 * u_sel + x6 + max H_sub ((H_sub + 5 * r_pos) / 6) + z_T ≤ 1 - 1 / 40 := by
  intro u_sel H_th z_rem_th H_free r_unm r_pos z_T hzT0 hHsub0 hHfree_lo hbranch
  have hdz0 : 0 ≤ stage1Line r - (1 - r) / 2 := by unfold stage1Line; linarith
  set w : ℝ := θ * (stage1Line r - (1 - r) / 2)
  have hw0 : 0 ≤ w := mul_nonneg hθ0 hdz0
  have hw1 : w ≤ 269 / 500 - 69 * r / 125 - (1 - r) / 2 := by
    have h1 : w ≤ stage1Line r - (1 - r) / 2 := mul_le_of_le_one_left hdz0 hθ1
    unfold stage1Line at h1; exact h1
  have hu_eq : u_sel = (11 / 3) * w := by dsimp [u_sel, w]; unfold stage1Width; ring
  have hH_eq : H_free = 1 - 22 * w - 6 * ell - 6 * x6 := by
    dsimp [H_free, H_th, w]; unfold stage1DualScale stage1Width; ring
  have hzT_eq : z_T = (1 - r) / 2 - (8 / 3) * w - z_Jv - z_J - z_coll := by
    dsimp [z_T, z_rem_th, w]; unfold stage1RemWidth stage1Width; ring
  have hrpos_le : r_pos ≤ r - 2 * ell := by
    dsimp [r_pos, r_unm]; apply max_le <;> linarith
  have hx6_cap : 6 * x6 ≤ 1 - 22 * w - 6 * ell + t_dual := by linarith [hHfree_lo, hH_eq]
  rcases hbranch with hlow | ⟨rfl, hsmall⟩
  · rcases le_total H_sub ((H_sub + 5 * r_pos) / 6) with hm_l | hm_r
    · rw [max_eq_right hm_l]
      have : 3 * ell + 5 * ((11 / 3) * w) + x6 + (H_sub + 5 * r_pos) / 6 +
          ((1 - r) / 2 - (8 / 3) * w - z_Jv - z_J - z_coll) ≤ 1 - 1 / 40 := by linarith
      linarith [hu_eq, hzT_eq]
    · rw [max_eq_left hm_r]
      have : 3 * ell + 5 * ((11 / 3) * w) + x6 + H_sub +
          ((1 - r) / 2 - (8 / 3) * w - z_Jv - z_J - z_coll) ≤ 1 - 1 / 40 := by linarith
      linarith [hu_eq, hzT_eq]
  · rcases le_total (1 / 10) (r_unm + 10 * t_dual) with hm1 | hm2
    · have hHf_le : H_free ≤ r_unm + 10 * t_dual := by rwa [max_eq_right hm1] at hsmall
      have hr_nn : 0 ≤ r_unm + 10 * t_dual := by linarith
      have hrpos_lo : r_unm ≤ r_pos := le_max_right 0 r_unm
      -- Note `x6 + H_free / 6 = (1 - 22 * w - 6 * ell) / 6` identically!
      have hxH : x6 + H_free / 6 = (1 - 22 * w - 6 * ell) / 6 := by linarith [hH_eq]
      have hmax_le : max H_free ((H_free + 5 * r_pos) / 6) ≤
          (H_free + 5 * r_pos) / 6 + (25 / 3) * t_dual := by
        apply max_le <;> linarith
      linarith [hu_eq, hzT_eq, hxH, hmax_le, hrpos_le]
    · have hHf_le : H_free ≤ 1 / 10 := by rwa [max_eq_left hm2] at hsmall
      have hxH : x6 + H_free / 6 = (1 - 22 * w - 6 * ell) / 6 := by linarith [hH_eq]
      rcases le_total H_free ((H_free + 5 * r_pos) / 6) with hm_l | hm_r
      · rw [max_eq_right hm_l]
        have : 3 * ell + 5 * ((11 / 3) * w) + (1 - 22 * w - 6 * ell) / 6 + (5 / 6) * r_pos +
            ((1 - r) / 2 - (8 / 3) * w - z_Jv - z_J - z_coll) ≤ 1 - 1 / 40 := by linarith
        linarith [hu_eq, hzT_eq, hxH]
      · rw [max_eq_left hm_r]
        have : 3 * ell + 5 * ((11 / 3) * w) + x6 + H_free +
            ((1 - r) / 2 - (8 / 3) * w - z_Jv - z_J - z_coll) ≤ 1 - 1 / 40 := by linarith
        linarith [hu_eq, hzT_eq]

/-- Mellin shift for `childLogTest W₀ s`: on `(0, ∞)`, `kernelLogPhase s (Real.log x) = x ^ (2πs i)`,
so `mellin (childLogTest W₀ s) z = mellin W₀ (z + (2 * π * s : ℝ) * I)`. -/
lemma mellin_childLogTest_eq (W₀ : ℝ → ℂ) (s : ℝ) (z : ℂ) :
    mellin (childLogTest W₀ s) z =
      mellin W₀ (z + ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx_pos : 0 < x := hx
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  have hph : kernelLogPhase s (Real.log x) =
      (x : ℂ) ^ (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hx_ne, ← Complex.ofReal_log hx_pos.le]
    unfold kernelLogPhase
    congr 1; push_cast; ring
  dsimp only
  rw [smul_eq_mul, smul_eq_mul, childLogTest, hph]
  calc (x : ℂ) ^ (z - 1) * (W₀ x * (x : ℂ) ^ (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I))
      = ((x : ℂ) ^ (z - 1) * (x : ℂ) ^ (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) * W₀ x := by ring
    _ = (x : ℂ) ^ (z + ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I - 1) * W₀ x := by
        rw [← Complex.cpow_add _ _ hx_ne]; congr 2; ring

/-- Uniform Mellin vertical strip decay for `childLogTest W₀ s` with explicit polynomial growth
`(1 + |s|) ^ j`, derived from `compact_source_mellin_strip_decay`. -/
theorem mellin_childLogTest_strip_decay
    (W₀ : ℝ → ℂ) {af bf : ℝ} (haf : 0 < af)
    (hsupp : Function.support W₀ ⊆ Set.Icc af bf) (hW₀ : ContDiff ℝ ∞ W₀)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C_m : ℝ, 0 < C_m ∧ ∀ (s : ℝ), ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellin (childLogTest W₀ s) ((σ : ℂ) + t * Complex.I)‖ ≤
        C_m * (1 + |s|) ^ j := by
  obtain ⟨C₀, hC₀, hdecay⟩ :=
    compact_source_mellin_strip_decay W₀ af bf haf hsupp hW₀ lo hi j
  refine ⟨C₀ * (1 + 2 * Real.pi) ^ j, by positivity, ?_⟩
  intro s σ hσ t
  rw [mellin_childLogTest_eq]
  have hshift : (σ : ℂ) + t * Complex.I + ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I =
      (σ : ℂ) + ((t + 2 * Real.pi * s : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hshift]
  have hbound := hdecay σ hσ (t + 2 * Real.pi * s)
  have habs : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |s|) * (1 + |t + 2 * Real.pi * s|) := by
    have htri : |t| ≤ |t + 2 * Real.pi * s| + |2 * Real.pi * s| := by
      have := abs_sub_le t (t + 2 * Real.pi * s) 0
      rw [sub_zero, sub_zero, show t - (t + 2 * Real.pi * s) = -(2 * Real.pi * s) by ring,
        abs_neg] at this
      linarith [this]
    have h2pi : |2 * Real.pi * s| = 2 * Real.pi * |s| := by
      rw [abs_mul, abs_of_pos Real.two_pi_pos]
    rw [h2pi] at htri
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    nlinarith [abs_nonneg s, abs_nonneg (t + 2 * Real.pi * s),
      mul_nonneg (abs_nonneg s) (abs_nonneg (t + 2 * Real.pi * s))]
  have hpow := pow_le_pow_left₀ (by positivity) habs j
  calc
    (1 + |t|) ^ j * ‖mellin W₀ ((σ : ℂ) + ↑(t + 2 * Real.pi * s) * Complex.I)‖
      ≤ ((1 + 2 * Real.pi) * (1 + |s|) * (1 + |t + 2 * Real.pi * s|)) ^ j *
          ‖mellin W₀ ((σ : ℂ) + ↑(t + 2 * Real.pi * s) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = ((1 + 2 * Real.pi) ^ j * (1 + |s|) ^ j) *
          ((1 + |t + 2 * Real.pi * s|) ^ j *
            ‖mellin W₀ ((σ : ℂ) + ↑(t + 2 * Real.pi * s) * Complex.I)‖) := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ ((1 + 2 * Real.pi) ^ j * (1 + |s|) ^ j) * C₀ :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = C₀ * (1 + 2 * Real.pi) ^ j * (1 + |s|) ^ j := by ring

/-- Pointwise identity for `scaleProfile (childLogTest W₀ t)` on `(0, ∞)` when `W₀` is smooth and
supported in `[af, bf]` (`0 < af`). -/
lemma scaleProfile_childLogTest_eq_on_pos
    (W₀ : ℝ → ℂ) (hW₀ : ContDiff ℝ ∞ W₀) (t : ℝ) {y : ℝ} (hy : 0 < y) :
    scaleProfile (childLogTest W₀ t) y =
      (-(1 / 2 : ℂ) - ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) * childLogTest W₀ t y -
        childLogTest (fun x => (x : ℂ) * deriv W₀ x) t y := by
  have hdW : HasDerivAt W₀ (deriv W₀ y) y :=
    (hW₀.differentiable (by simp)).differentiableAt.hasDerivAt
  have hd_log : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy.ne'
  let c : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
  have hd_arg : HasDerivAt (fun x : ℝ => c * (Real.log x : ℂ)) (c * (y⁻¹ : ℝ)) y := by
    have h1 : HasDerivAt (fun x : ℝ => (Real.log x : ℂ)) ((y⁻¹ : ℝ) : ℂ) y :=
      hd_log.ofReal_comp
    simpa only [smul_eq_mul, mul_comm c] using h1.const_mul c
  have heq_ph : (fun x : ℝ => kernelLogPhase t (Real.log x)) =
      fun x : ℝ => Complex.exp (c * (Real.log x : ℂ)) := by
    funext x; unfold kernelLogPhase; dsimp [c]; congr 1; push_cast; ring
  have hd_exp : HasDerivAt (fun x : ℝ => Complex.exp (c * (Real.log x : ℂ)))
      (Complex.exp (c * (Real.log y : ℂ)) * (c * (y⁻¹ : ℝ))) y := hd_arg.cexp
  have hval_ph : kernelLogPhase t (Real.log y) = Complex.exp (c * (Real.log y : ℂ)) :=
    congrFun heq_ph y
  have hd_ph : HasDerivAt (fun x : ℝ => kernelLogPhase t (Real.log x))
      (kernelLogPhase t (Real.log y) * (c * (y⁻¹ : ℝ))) y := by
    rw [heq_ph, hval_ph]; exact hd_exp
  have hd_prod : HasDerivAt (childLogTest W₀ t)
      (deriv W₀ y * kernelLogPhase t (Real.log y) +
        W₀ y * (kernelLogPhase t (Real.log y) * (c * (y⁻¹ : ℝ)))) y :=
    hdW.mul hd_ph
  have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hy_inv : (y : ℂ) * ((y⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hy.ne', Complex.ofReal_one]
  unfold scaleProfile
  rw [hd_prod.deriv]
  unfold childLogTest
  dsimp [c]
  calc
    -(W₀ y * kernelLogPhase t (Real.log y)) / 2 -
        (y : ℂ) * (deriv W₀ y * kernelLogPhase t (Real.log y) +
          W₀ y * (kernelLogPhase t (Real.log y) * ((((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) * (y⁻¹ : ℝ))))
      = -(W₀ y * kernelLogPhase t (Real.log y)) / 2 -
          (y : ℂ) * deriv W₀ y * kernelLogPhase t (Real.log y) -
          ((y : ℂ) * (y⁻¹ : ℝ)) * (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) *
            (W₀ y * kernelLogPhase t (Real.log y)) := by ring
    _ = _ := by rw [hy_inv, one_mul]; ring

/-- Linearity of `HeckeDyadic.polynomial χ true V D 0 0` in `V` on `(0, ∞)`: if `V y = c₁ * V₁ y + c₂ * V₂ y`
for all `y > 0` (`0 < D`), then `‖polynomial χ true V D 0 0‖^2 ≤ 2 ‖c₁‖^2 ‖P₁‖^2 + 2 ‖c₂‖^2 ‖P₂‖^2`. -/
lemma polynomial_linear_norm_sq_le
    (χ : Character) {V V₁ V₂ : ℝ → ℂ} {c₁ c₂ : ℂ} {D b_hi : ℝ} (hD : 0 < D)
    (hV₁ : ∀ y, V₁ y ≠ 0 → y ≤ b_hi) (hV₂ : ∀ y, V₂ y ≠ 0 → y ≤ b_hi)
    (hlin : ∀ y, 0 < y → V y = c₁ * V₁ y + c₂ * V₂ y) :
    ‖HeckeDyadic.polynomial χ true V D 0 0‖ ^ 2 ≤
      2 * ‖c₁‖ ^ 2 * ‖HeckeDyadic.polynomial χ true V₁ D 0 0‖ ^ 2 +
      2 * ‖c₂‖ ^ 2 * ‖HeckeDyadic.polynomial χ true V₂ D 0 0‖ ^ 2 := by
  let N_hi : ℕ := ⌊max 0 b_hi * D⌋₊
  let S_id := HeckeInverseAmplification.idealsUpTo N_hi
  have hcover (W : ℝ → ℂ) (hW : ∀ y, W y ≠ 0 → y ≤ b_hi) :
      (∑' I : Ideal O, (moebius I : ℂ) * idealCoeff χ I *
        (W ((I.absNorm : ℝ) / D) * (((I.absNorm : ℝ) / D : ℝ) : ℂ) ^ (-HeckeDyadic.shift 0 0))) =
      ∑ I ∈ S_id, (moebius I : ℂ) * idealCoeff χ I *
        (W ((I.absNorm : ℝ) / D) * (((I.absNorm : ℝ) / D : ℝ) : ℂ) ^ (-HeckeDyadic.shift 0 0)) := by
    apply tsum_eq_sum
    intro I hnS
    by_cases hsq : Squarefree I
    · by_cases hWy : W ((I.absNorm : ℝ) / D) = 0
      · simp [hWy]
      · exfalso; apply hnS
        rw [HeckeInverseAmplification.mem_idealsUpTo]
        have hy_le : (I.absNorm : ℝ) ≤ max 0 b_hi * D :=
          ((div_le_iff₀ hD).mp (hW _ hWy)).trans
            (mul_le_mul_of_nonneg_right (le_max_right 0 b_hi) hD.le)
        exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero),
          Nat.le_floor hy_le⟩
    · simp [moebius_of_not_squarefree hsq]
  -- Restrict `V` via `Squarefree I` (`I ≠ 0`, so `(I.absNorm : ℝ) / D > 0`).
  have hcover_V :
      (∑' I : Ideal O, (moebius I : ℂ) * idealCoeff χ I *
        (V ((I.absNorm : ℝ) / D) * (((I.absNorm : ℝ) / D : ℝ) : ℂ) ^ (-HeckeDyadic.shift 0 0))) =
      ∑ I ∈ S_id, (moebius I : ℂ) * idealCoeff χ I *
        (V ((I.absNorm : ℝ) / D) * (((I.absNorm : ℝ) / D : ℝ) : ℂ) ^ (-HeckeDyadic.shift 0 0)) := by
    apply tsum_eq_sum
    intro I hnS
    by_cases hsq : Squarefree I
    · have hI_pos : 0 < (I.absNorm : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero)
      have hy_pos : 0 < (I.absNorm : ℝ) / D := div_pos hI_pos hD
      by_cases hVy : V ((I.absNorm : ℝ) / D) = 0
      · simp [hVy]
      · exfalso; apply hnS
        rw [hlin _ hy_pos] at hVy
        have hy_le : (I.absNorm : ℝ) / D ≤ b_hi := by
          by_contra hgt
          have h1 : V₁ ((I.absNorm : ℝ) / D) = 0 := by by_contra hne; exact hgt (hV₁ _ hne)
          have h2 : V₂ ((I.absNorm : ℝ) / D) = 0 := by by_contra hne; exact hgt (hV₂ _ hne)
          exact hVy (by simp [h1, h2])
        have hN_le : (I.absNorm : ℝ) ≤ max 0 b_hi * D :=
          ((div_le_iff₀ hD).mp hy_le).trans
            (mul_le_mul_of_nonneg_right (le_max_right 0 b_hi) hD.le)
        rw [HeckeInverseAmplification.mem_idealsUpTo]
        exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero),
          Nat.le_floor hN_le⟩
    · simp [moebius_of_not_squarefree hsq]
  have heq_pol :
      HeckeDyadic.polynomial χ true V D 0 0 =
        c₁ * HeckeDyadic.polynomial χ true V₁ D 0 0 +
          c₂ * HeckeDyadic.polynomial χ true V₂ D 0 0 := by
    rw [InverseInitialExcludedPolynomial.polynomial_all_ideals,
      InverseInitialExcludedPolynomial.polynomial_all_ideals,
      InverseInitialExcludedPolynomial.polynomial_all_ideals,
      hcover_V, hcover V₁ hV₁, hcover V₂ hV₂]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    have hI_pos : 0 < (I.absNorm : ℝ) := by
      exact_mod_cast (HeckeInverseAmplification.mem_idealsUpTo.mp hI).1
    rw [hlin _ (div_pos hI_pos hD)]
    ring
  rw [heq_pol]
  have htri := norm_add_le (c₁ * HeckeDyadic.polynomial χ true V₁ D 0 0)
    (c₂ * HeckeDyadic.polynomial χ true V₂ D 0 0)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  rw [norm_mul, norm_mul] at hsq
  nlinarith [sq_nonneg (‖c₁‖ * ‖HeckeDyadic.polynomial χ true V₁ D 0 0‖ -
    ‖c₂‖ * ‖HeckeDyadic.polynomial χ true V₂ D 0 0‖)]

/-- Simultaneous `RawMoment` bound for `orientedProfile true (childLogTest wFresh s)` AND its
`scaleProfile`, feeding directly into `HeckeInverseAmplification.no_slot_endpoint`. -/
theorem scaleProfile_childLogTest_rawMoment
    (wFresh : 𝓢(ℝ, ℂ)) {af bf : ℝ} (haf : 0 < af) (habf : af ≤ bf)
    (hs_w : Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf)
    {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    ∃ J_raw : ℕ, ∀ data : RowData, ∃ C_raw : ℝ, 0 < C_raw ∧ ∀ s : ℝ,
      let W_s := orientedProfile true (childLogTest wFresh s)
      RawMoment data W_s c κ (C_raw * (1 + |s|) ^ (2 * J_raw)) ∧
        RawMoment data (scaleProfile W_s) c κ (C_raw * (1 + |s|) ^ (2 * J_raw)) := by
  have hbf_pos : 0 < bf := haf.trans_le habf
  have hcs_conj : HasCompactSupport (fun x : ℝ => star (wFresh x)) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := af) (b := bf)) ?_
    intro x hx; exact hs_w (by simpa using hx)
  have hsm_conj : ContDiff ℝ ∞ (fun x : ℝ => star (wFresh x)) :=
    Complex.conjCLE.contDiff.comp (wFresh.smooth ⊤)
  let wConj : 𝓢(ℝ, ℂ) := hcs_conj.toSchwartzMap hsm_conj
  have hwConj_eq (x : ℝ) : wConj x = star (wFresh x) := rfl
  have hs_conj : Function.support (wConj : ℝ → ℂ) ⊆ Set.Icc af bf := by
    intro x hx; rw [Function.mem_support, hwConj_eq, star_ne_zero] at hx; exact hs_w hx
  have hcs_der : HasCompactSupport (fun x : ℝ => (x : ℂ) * deriv (wConj : ℝ → ℂ) x) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := af) (b := bf)) ?_
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hn
    have hd0 : deriv (wConj : ℝ → ℂ) x = 0 :=
      deriv_of_notMem_tsupport (fun hm => hn ((closure_minimal hs_conj isClosed_Icc) hm))
    exact hx (by simp [hd0])
  have hsm_der : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ) * deriv (wConj : ℝ → ℂ) x) :=
    Complex.ofRealCLM.contDiff.mul (contDiff_infty_iff_deriv.mp (wConj.smooth ⊤)).2
  let wDer : 𝓢(ℝ, ℂ) := hcs_der.toSchwartzMap hsm_der
  have hwDer_eq (x : ℝ) : wDer x = (x : ℂ) * deriv (wConj : ℝ → ℂ) x := rfl
  have hs_der : Function.support (wDer : ℝ → ℂ) ⊆ Set.Icc af bf := by
    intro x hx
    rw [Function.mem_support, hwDer_eq] at hx
    by_contra hn
    have hd0 : deriv (wConj : ℝ → ℂ) x = 0 :=
      deriv_of_notMem_tsupport (fun hm => hn ((closure_minimal hs_conj isClosed_Icc) hm))
    exact hx (by simp [hd0])
  obtain ⟨J₀, hraw₀⟩ := raw_reference_moment wConj af bf c κ haf hbf_pos hs_conj hc hκ
  obtain ⟨J₁, hraw₁⟩ := raw_reference_moment wDer af bf c κ haf hbf_pos hs_der hc hκ
  let J_raw := max J₀ J₁ + 1
  refine ⟨J_raw, ?_⟩
  intro data
  obtain ⟨C₀, hC₀, hm₀⟩ := hraw₀ data
  obtain ⟨C₁, hC₁, hm₁⟩ := hraw₁ data
  let C_raw : ℝ := 2 * (1 + 2 * Real.pi) ^ 2 * (C₀ + C₁)
  refine ⟨C_raw, by dsimp [C_raw]; positivity, ?_⟩
  intro s
  have hor_eq : orientedProfile true (childLogTest wFresh s) = childLogTest wConj (-s) := by
    funext x
    unfold orientedProfile childLogTest kernelLogPhase
    rw [if_pos rfl, hwConj_eq, map_mul]
    congr 1
    rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1; push_cast; ring
  have h1s : 1 ≤ 1 + |s| := by linarith [abs_nonneg s]
  have hnorm_neg : 1 + ‖-s‖ = 1 + |s| := by rw [norm_neg, Real.norm_eq_abs]
  have hJ₀_le : 2 * J₀ ≤ 2 * J_raw := by dsimp [J_raw]; omega
  have hJ₁_le : 2 * J₁ ≤ 2 * J_raw := by dsimp [J_raw]; omega
  constructor
  · rw [hor_eq]
    intro H D hH hD hHD rows hrows
    have hb := hm₀ (-s) H D hH hD hHD rows hrows
    rw [hnorm_neg] at hb
    apply hb.trans
    have hpow := pow_le_pow_right₀ h1s hJ₀_le
    have hC_le : C₀ ≤ C_raw := by
      dsimp [C_raw]
      have : 1 ≤ (1 + 2 * Real.pi) ^ 2 := one_le_pow₀ (by linarith [Real.pi_pos])
      nlinarith [hC₀, hC₁]
    gcongr
  · rw [hor_eq]
    intro H D hH hD hHD rows hrows
    have hb₀ := hm₀ (-s) H D hH hD hHD rows hrows
    have hb₁ := hm₁ (-s) H D hH hD hHD rows hrows
    rw [hnorm_neg] at hb₀ hb₁
    let c_sc : ℂ := -(1 / 2 : ℂ) - ((2 * Real.pi * (-s) : ℝ) : ℂ) * Complex.I
    have hc_sc_norm : ‖c_sc‖ ≤ (1 + 2 * Real.pi) * (1 + |s|) := by
      dsimp [c_sc]
      have htri : ‖-(1 / 2 : ℂ) - ((2 * Real.pi * (-s) : ℝ) : ℂ) * Complex.I‖ ≤
          ‖-(1 / 2 : ℂ)‖ + ‖((2 * Real.pi * (-s) : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
      have h1 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      have h2 : ‖((2 * Real.pi * (-s) : ℝ) : ℂ) * Complex.I‖ = 2 * Real.pi * |s| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_mul, abs_of_pos Real.two_pi_pos, abs_neg]
      rw [h1, h2] at htri
      linarith [Real.pi_pos, abs_nonneg s]
    have hpt (v : NonzeroElement) :
        ‖HeckeDyadic.polynomial (data.character v) true (scaleProfile (childLogTest wConj (-s))) D 0 0‖ ^ 2 ≤
          2 * ‖c_sc‖ ^ 2 * ‖HeckeDyadic.polynomial (data.character v) true (childLogTest wConj (-s)) D 0 0‖ ^ 2 +
          2 * ‖(-1 : ℂ)‖ ^ 2 * ‖HeckeDyadic.polynomial (data.character v) true (childLogTest wDer (-s)) D 0 0‖ ^ 2 := by
      apply polynomial_linear_norm_sq_le (data.character v) hD
        (fun y hy => (hs_conj (fun hz => hy (by simp [childLogTest, hz]))).2)
        (fun y hy => (hs_der (fun hz => hy (by simp [childLogTest, hz]))).2)
      intro y hy
      rw [scaleProfile_childLogTest_eq_on_pos wConj (wConj.smooth ⊤) (-s) hy]
      dsimp [c_sc]
      have hwD : (fun x : ℝ => (x : ℂ) * deriv (wConj : ℝ → ℂ) x) = (wDer : ℝ → ℂ) :=
        funext (fun x => (hwDer_eq x).symm)
      rw [hwD]
      ring
    calc
      (∑ v ∈ rows, ‖HeckeDyadic.polynomial (data.character v) true
          (scaleProfile (childLogTest wConj (-s))) D 0 0‖ ^ 2)
        ≤ ∑ v ∈ rows, (2 * ‖c_sc‖ ^ 2 *
            ‖HeckeDyadic.polynomial (data.character v) true (childLogTest wConj (-s)) D 0 0‖ ^ 2 +
            2 * ‖(-1 : ℂ)‖ ^ 2 *
            ‖HeckeDyadic.polynomial (data.character v) true (childLogTest wDer (-s)) D 0 0‖ ^ 2) :=
          Finset.sum_le_sum (fun v _ => hpt v)
      _ = 2 * ‖c_sc‖ ^ 2 * (∑ v ∈ rows,
            ‖HeckeDyadic.polynomial (data.character v) true (childLogTest wConj (-s)) D 0 0‖ ^ 2) +
          2 * (∑ v ∈ rows,
            ‖HeckeDyadic.polynomial (data.character v) true (childLogTest wDer (-s)) D 0 0‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, norm_neg, norm_one, one_pow, mul_one]
      _ ≤ 2 * ((1 + 2 * Real.pi) * (1 + |s|)) ^ 2 *
            (C₀ * (1 + |s|) ^ (2 * J₀) * H * (H * max 1 D) ^ κ) +
          2 * (C₁ * (1 + |s|) ^ (2 * J₁) * H * (H * max 1 D) ^ κ) := by
          apply add_le_add
          · exact mul_le_mul
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hc_sc_norm 2) (by norm_num))
              hb₀ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
          · exact mul_le_mul_of_nonneg_left hb₁ (by norm_num)
      _ ≤ C_raw * (1 + |s|) ^ (2 * J_raw) * H * (H * max 1 D) ^ κ := by
          have hp0 : (1 + |s|) ^ 2 * (1 + |s|) ^ (2 * J₀) ≤ (1 + |s|) ^ (2 * J_raw) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ h1s (by dsimp [J_raw]; omega)
          have hp1 : (1 + |s|) ^ (2 * J₁) ≤ (1 + |s|) ^ (2 * J_raw) :=
            pow_le_pow_right₀ h1s hJ₁_le
          have hHK : 0 ≤ H * (H * max 1 D) ^ κ := by positivity
          have hpi1 : 1 ≤ (1 + 2 * Real.pi) ^ 2 := one_le_pow₀ (by linarith [Real.pi_pos])
          have hsub : 2 * (1 + 2 * Real.pi) ^ 2 * C₀ * ((1 + |s|) ^ 2 * (1 + |s|) ^ (2 * J₀)) +
              2 * C₁ * (1 + |s|) ^ (2 * J₁) ≤ C_raw * (1 + |s|) ^ (2 * J_raw) := by
            dsimp [C_raw]
            have t1 := mul_le_mul_of_nonneg_left hp0 (show 0 ≤ 2 * (1 + 2 * Real.pi) ^ 2 * C₀ by positivity)
            have t2 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 2 * C₁ by positivity)
            have t3 : 2 * C₁ * (1 + |s|) ^ (2 * J_raw) ≤
                2 * (1 + 2 * Real.pi) ^ 2 * C₁ * (1 + |s|) ^ (2 * J_raw) := by
              have : 0 ≤ C₁ * (1 + |s|) ^ (2 * J_raw) := by positivity
              nlinarith
            linarith
          have hmul := mul_le_mul_of_nonneg_right hsub hHK
          calc
            2 * ((1 + 2 * Real.pi) * (1 + |s|)) ^ 2 *
                (C₀ * (1 + |s|) ^ (2 * J₀) * H * (H * max 1 D) ^ κ) +
              2 * (C₁ * (1 + |s|) ^ (2 * J₁) * H * (H * max 1 D) ^ κ)
              = (2 * (1 + 2 * Real.pi) ^ 2 * C₀ * ((1 + |s|) ^ 2 * (1 + |s|) ^ (2 * J₀)) +
                  2 * C₁ * (1 + |s|) ^ (2 * J₁)) * (H * (H * max 1 D) ^ κ) := by ring
            _ ≤ C_raw * (1 + |s|) ^ (2 * J_raw) * (H * (H * max 1 D) ^ κ) := hmul
            _ = C_raw * (1 + |s|) ^ (2 * J_raw) * H * (H * max 1 D) ^ κ := by ring

/-- When `9 < D_s` and `Function.support V ⊆ [1, 2]`, every prime `P` in the support of
`canonicalPrimeAmplitude M H u_free.val V 2 D_s ζ` has `P.absNorm ≥ D_s > 9`, hence misses
`fixedBadPrimes` (`absNorm ∈ {3, 4}`), so `canonicalPrimeAmplitude` equals
`rayPrimePolynomial M H (rawRow u_free).inverse V 2 D_s (1 - ζ.re) ζ.im`. -/
theorem canonicalPrimeAmplitude_eq_rayPrimePolynomial_of_gt_nine
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (V : ℝ → ℂ) (hV : ∀ x, V x ≠ 0 → x ∈ Set.Icc (1 : ℝ) 2)
    (u_free : FreeRow) {D_s : ℝ} (hD9 : 9 < D_s) (ζ : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H u_free.val V 2 D_s ζ =
      rayPrimePolynomial M H (rawRow u_free).inverse V 2 D_s (1 - ζ.re) ζ.im := by
  have hDs_pos : 0 < D_s := by linarith
  unfold HeckePrimeRow.canonicalPrimeAmplitude rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_, hpr, _⟩ := Finset.mem_filter.mp hP
  by_cases hVP : V ((P.absNorm : ℝ) / D_s) = 0
  · unfold HeckePrimeAnnular.annularWeight; simp [hVP]
  · have hN_ge : D_s ≤ (P.absNorm : ℝ) := by
      have h1 := (le_div_iff₀ hDs_pos).mp (hV _ hVP).1
      linarith
    have hN_gt9 : 9 < P.absNorm := by exact_mod_cast hD9.trans_le hN_ge
    have hnot_bad : P ∉ CanonicalRowCompletion.fixedBadPrimes := by
      intro hbad
      unfold CanonicalRowCompletion.fixedBadPrimes at hbad
      rcases Finset.mem_insert.mp hbad with rfl | h2
      · have h3 := absNorm_span_lambda_eq_three
        change (Ideal.span {lambda} : Ideal O).absNorm = 3 at h3
        change 9 < (Ideal.span {lambda} : Ideal O).absNorm at hN_gt9
        omega
      · rw [Finset.mem_singleton] at h2
        subst h2
        have h4 := absNorm_span_two_eq_four
        have htwo : (cubicTwoIdeal : Ideal O) = Ideal.span {(2 : O)} :=
          Ideal.span_singleton_neg (2 : O)
        rw [htwo] at hN_gt9
        omega
    have hraw := rawRow_prime_outside CanonicalRowCompletion.fixedBadPrimes
      CanonicalRowCompletion.fixedBadPrimes_prime Finset.Subset.rfl u_free ⟨P, hpr⟩ hnot_bad
    have hinv : idealCoeff (rawRow u_free).inverse P = star (CanonicalRowCompletion.idealRowHom u_free.val P) := by
      rw [idealCoeff_inverse_conj, hraw]; rfl
    have hshift : -HeckeDyadic.shift (1 - ζ.re) ζ.im = ζ - 1 := by
      apply Complex.ext <;> simp [HeckeDyadic.shift]
    unfold HeckePrimeAnnular.annularWeight
    rw [hinv, hshift]
    change star _ * _ * _ = _
    ring

/-- Exact coefficient conjugation between `targetRow (deletedBase data).inverse u_free` and
`(data.character ⟨u_free.val, u_free.property.1⟩).excludePrimes (excluded data) _`, valid at
**every** ideal `I : Ideal O`. -/
theorem targetRow_deletedBase_coeff (data : RowData) (u_free : FreeRow) (I : Ideal O) :
    idealCoeff (targetRow (deletedBase data).inverse u_free) I =
      conj (idealCoeff ((data.character ⟨u_free.val, u_free.property.1⟩).excludePrimes
        (excluded data) (reflectionExcludedPrimes_prime (basePeriod data))) I) := by
  rw [DetectorDictionaryInverseRawInitialGates.actual_deleted_row data ⟨u_free.val, u_free.property.1⟩ I, map_mul]
  by_cases hI0 : I = 0
  · rw [hI0, map_zero (idealCoeff _), map_zero (idealCoeff _),
      map_zero (CanonicalRowCompletion.idealRowHom _), map_zero, zero_mul]
  · by_cases hout : InverseInitialExcludedPool.outside (excluded data) I
    · have hraw_I : idealCoeff (rawRow u_free) I = CanonicalRowCompletion.idealRowHom u_free.val I := by
        have hf1 := congrArg (fun G : Ideal O →*₀ ℂ => G I) (IdealEuler.primeValueHom_eq (idealCoeff (rawRow u_free)))
        have hf2 := congrArg (fun G : Ideal O →*₀ ℂ => G I)
          (IdealEuler.primeValueHom_eq (CanonicalRowCompletion.idealRowHom u_free.val))
        rw [← hf1, ← hf2]
        change (if I = 0 then 0 else ((normalizedFactors I).map (idealCoeff (rawRow u_free))).prod) =
          (if I = 0 then 0 else ((normalizedFactors I).map (CanonicalRowCompletion.idealRowHom u_free.val)).prod)
        rw [if_neg hI0, if_neg hI0]
        congr 1
        apply Multiset.map_congr rfl
        intro P hP
        have hpP : Prime P := prime_of_normalized_factor P hP
        have hP_not_excl : P ∉ excluded data := fun hmem =>
          hout P hmem (dvd_of_mem_normalizedFactors hP)
        have hP_not_bad : P ∉ CanonicalRowCompletion.fixedBadPrimes :=
          fun hbad => hP_not_excl (reflectionExcludedPrimes_bad (basePeriod data) hbad)
        exact rawRow_prime_outside CanonicalRowCompletion.fixedBadPrimes
          CanonicalRowCompletion.fixedBadPrimes_prime Finset.Subset.rfl u_free ⟨P, hpP⟩ hP_not_bad
      change idealCoeff ((deletedBase data).inverse.product (rawRow u_free).inverse) I = _
      rw [idealCoeff_product, idealCoeff_inverse_conj, idealCoeff_inverse_conj, hraw_I]
    · have hz_del : idealCoeff (deletedBase data) I = 0 :=
        InverseInitialExcludedOverlap.deleted_zero_outside (baseCharacter data) (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data)) I hout
      change idealCoeff ((deletedBase data).inverse.product (rawRow u_free).inverse) I = _
      rw [idealCoeff_product, idealCoeff_inverse_conj, hz_del]
      simp only [map_zero, zero_mul]

/-- `zeroMaximum` is bounded above by `detectorMaximum` on any nonprincipal family. -/
lemma zeroMaximum_le_detectorMaximum {ι : Type*} [Fintype ι]
    (χ : ι → Character) (hχ : ∀ j, (χ j).residue ≠ 1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum χ hχ T ≤ detectorMaximum χ T :=
  (detectorMaximum_eq_nonprincipal χ hχ T).symm.le

/-- Trivial Cauchy-Schwarz bound on `‖canonicalPrimeAmplitude M H w V 2 D_s ζ‖^2` when `1 ≤ D_s`,
`ζ.re ≤ 1`, `‖V x‖ ≤ 1`, and `Function.support V ⊆ [1, 2]`: at most `9604 * D_s`. -/
lemma canonicalPrimeAmplitude_norm_sq_le_trivial
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (V : ℝ → ℂ) (hV_supp : ∀ x, V x ≠ 0 → x ∈ Set.Icc (1 : ℝ) 2)
    (hV_norm : ∀ x, ‖V x‖ ≤ 1)
    {D_s : ℝ} (hDs1 : 1 ≤ D_s) {ζ : ℂ} (hζ : ζ.re ≤ 1) (w : O) :
    ‖HeckePrimeRow.canonicalPrimeAmplitude M H w V 2 D_s ζ‖ ^ 2 ≤ 9604 * D_s := by
  have hDs_pos : 0 < D_s := zero_lt_one.trans_le hDs1
  have hamp := InverseInitialPhysicalSlots.amplitude_eq_live M H w V 2 D_s 1 ζ hDs_pos
  simp only [Real.rpow_one] at hamp
  rw [hamp, norm_mul, mul_pow]
  have hnorm_D : ‖((D_s ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 = D_s⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hDs_pos _),
      ← Real.rpow_natCast, ← Real.rpow_mul hDs_pos.le]
    norm_num; exact Real.rpow_neg_one D_s
  rw [hnorm_D]
  let L_s := livePrimes M H V 2 D_s
  have hcard_sharp : (L_s.card : ℝ) ≤ 98 * D_s := by
    have hinj : Set.InjOn cubicIdealGenerator (L_s : Set (Ideal O)) := by
      intro I _ J _ hIJ
      rw [← span_cubicIdealGenerator I, ← span_cubicIdealGenerator J, hIJ]
    rw [← Finset.card_image_of_injOn hinj]
    calc ((L_s.image cubicIdealGenerator).card : ℝ)
        ≤ 49 * (2 * D_s) := by
          apply card_finset_norm_sq_le_49_mul (L_s.image cubicIdealGenerator) (by linarith)
          intro z hz
          obtain ⟨P, hPL, rfl⟩ := Finset.mem_image.mp hz
          rw [ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator]
          exact (livePrime_data M H V 1 2 D_s hDs_pos hV_supp P hPL).2.2.2
      _ = 98 * D_s := by ring
  have hterm : ∀ P ∈ L_s,
      ‖primeProfile V D_s ζ P * star (CanonicalRowCompletion.idealRowHom w P)‖ ≤ 1 := by
    intro P hPL
    have hd := livePrime_data M H V 1 2 D_s hDs_pos hV_supp P hPL
    rw [norm_mul, norm_star]
    have h1 : ‖primeProfile V D_s ζ P‖ ≤ 1 := by
      unfold primeProfile
      rw [norm_mul]
      have hy1 : 1 ≤ (P.absNorm : ℝ) / D_s := (one_le_div hDs_pos).mpr (by linarith [hd.2.2.1])
      have hy_pos : 0 < (P.absNorm : ℝ) / D_s := zero_lt_one.trans_le hy1
      have hcpow : ‖(((P.absNorm : ℝ) / D_s : ℝ) : ℂ) ^ (ζ - 1)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hy_pos]
        exact Real.rpow_le_one_of_one_le_of_nonpos hy1 (by simp; linarith)
      exact (mul_le_mul (hV_norm _) hcpow (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have h2 : ‖CanonicalRowCompletion.idealRowHom w P‖ ≤ 1 :=
      CanonicalRowCompletion.idealRowHom_norm w P
    exact (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hsum_le : ‖∑ P ∈ L_s, primeProfile V D_s ζ P * star (CanonicalRowCompletion.idealRowHom w P)‖ ≤
      (L_s.card : ℝ) := by
    calc _ ≤ ∑ P ∈ L_s, ‖primeProfile V D_s ζ P * star (CanonicalRowCompletion.idealRowHom w P)‖ :=
          norm_sum_le L_s _
      _ ≤ ∑ _P ∈ L_s, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (L_s.card : ℝ) := by simp
  calc
    D_s⁻¹ * ‖∑ P ∈ L_s, primeProfile V D_s ζ P * star (CanonicalRowCompletion.idealRowHom w P)‖ ^ 2
      ≤ D_s⁻¹ * (L_s.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsum_le 2) (inv_nonneg.mpr hDs_pos.le)
    _ ≤ D_s⁻¹ * (98 * D_s) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard_sharp 2)
          (inv_nonneg.mpr hDs_pos.le)
    _ = 9604 * D_s := by field_simp [hDs_pos.ne']; ring

/-- When `0 < X'` and `bf * X' < 1` (`Function.support W ⊆ [af, bf]`), every subset `U` has
`primeProductNorm p U ≥ 1 > bf * X'`, so `W (primeProductNorm p U / X') = 0` and
`inputConjugateRow` vanishes identically. -/
lemma inputConjugateRow_eq_zero_of_mul_lt_one
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)
    (pool : Finset ι) (Ψ₀ : O →* ℂ) (m c d : O)
    (W : ℝ → ℂ) {bf X' : ℝ} (hX' : 0 < X') (hW : ∀ y, W y ≠ 0 → y ≤ bf)
    (hlt : bf * X' < 1) (w : O) :
    inputConjugateRow p χ pool Ψ₀ m c d
      (fun U => W (primeProductNorm p U / X')) w = 0 := by
  unfold inputConjugateRow supportConjugateSum
  apply Finset.sum_eq_zero
  intro U _
  have hnorm1 : 1 ≤ primeProductNorm p U := by
    unfold primeProductNorm
    rw [map_prod, norm_prod, ← Finset.prod_pow]
    apply Finset.one_le_prod
    intro i _
    rw [ringComplex_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (hp i)))
  have hW0 : W (primeProductNorm p U / X') = 0 := by
    by_contra hne
    have hle : primeProductNorm p U ≤ bf * X' := (div_le_iff₀ hX').mp (hW _ hne)
    linarith
  simp [secondInputCoefficient, hW0]

/-- When `0 < X'` and `bf * X' < 1`, every nonzero ideal `I : Ideal O` has `I.absNorm / X' > bf`, so
`HeckeDyadic.polynomial χ true W X' 0 0 = 0`. -/
lemma polynomial_eq_zero_of_mul_lt_one (χ : Character) (W : ℝ → ℂ) {bf X' : ℝ}
    (hX' : 0 < X') (hW : ∀ y, W y ≠ 0 → y ≤ bf) (hlt : bf * X' < 1) :
    HeckeDyadic.polynomial χ true W X' 0 0 = 0 := by
  rw [InverseInitialExcludedPolynomial.polynomial_all_ideals]
  convert mul_zero _
  convert tsum_zero with I
  by_cases hI0 : I = 0
  · rw [hI0, map_zero (idealCoeff χ)]; ring
  · have hge1 : 1 ≤ (I.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
    have hw0 : W ((I.absNorm : ℝ) / X') = 0 := by
      by_contra hne
      have := (div_le_iff₀ hX').mp (hW _ hne)
      linarith
    rw [hw0]; ring

/-- Unit-scale (`1 ≤ bf * X'` and `X' ≤ 1`) squared norm bound on `HeckeDyadic.polynomial`, derived
from `polynomial_coarse_norm_le`. -/
lemma polynomial_unit_scale_norm_sq_le (χ : Character) (W : ℝ → ℂ) {bf B_w X' : ℝ}
    (hX' : 0 < X') (hbf0 : 0 ≤ bf) (hBw0 : 0 ≤ B_w)
    (hW : ∀ y, W y ≠ 0 → y ≤ bf) (hBw : ∀ y, ‖W y‖ ≤ B_w)
    (hlo : 1 ≤ bf * X') (hhi : X' ≤ 1) :
    ‖HeckeDyadic.polynomial χ true W X' 0 0‖ ^ 2 ≤ bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 := by
  have hX_inv : (X')⁻¹ ≤ bf := (inv_le_iff_one_le_mul₀ hX').mpr hlo
  have hc := polynomial_coarse_norm_le χ W hX' hbf0 hBw0 hW hBw
  have h1 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have hXrpow : ((X') ^ (-(1 / 2 : ℝ))) ^ 2 = (X')⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX'.le]; norm_num; exact Real.rpow_neg_one X'
  rw [mul_pow, hXrpow] at h1
  have hbr : 1 + bf * X' ≤ 1 + bf := by linarith [mul_le_of_le_one_right hbf0 hhi]
  have hbr2 : (1 + bf * X') ^ 2 ≤ (1 + bf) ^ 2 := pow_le_pow_left₀ (by positivity) hbr 2
  have hbw_le : B_w * (49 * (1 + bf * X') ^ 2) ≤ B_w * 49 * (1 + bf) ^ 2 := by nlinarith
  exact h1.trans (mul_le_mul hX_inv (pow_le_pow_left₀ (by positivity) hbw_le 2) (sq_nonneg _) hbf0)

/-- Unit-scale smooth bump `w_one` supported inside `[1/2, b_one]` with `b_one < 2` and `w_one 1 = 1`:
at scale `1` (`U ^ (0 : ℝ)`), the only nonzero ideal `I : Ideal O` in the support of `w_one` is
`I = 1`, so `HeckeDyadic.polynomial χ true (childLogTest w_one 0) 1 0 0 = 1` for every `χ`! -/
theorem exists_unit_polynomial_window {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) :
    ∃ (w_one : ℝ → ℂ) (a_one b_one : ℝ),
      0 < a_one ∧ a_one ≤ b_one ∧ b_one < 2 ∧
      Function.support w_one ⊆ Set.Icc a_one b_one ∧
      ContDiff ℝ ∞ w_one ∧
      ∀ χ : Character,
        HeckeDyadic.polynomial χ true (childLogTest w_one 0) 1 0 0 = 1 := by
  have hne : ∃ x₀ : ℝ, F.w x₀ ≠ 0 := Function.ne_iff.mp F.nonzero
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀_mem : x₀ ∈ Set.Ioo (1 : ℝ) 2 := F.support hx₀
  have hx₀_pos : 0 < x₀ := zero_lt_one.trans hx₀_mem.1
  let w_one : ℝ → ℂ := fun y => ((F.w (x₀ * y) : ℝ) : ℂ) / ((F.w x₀ : ℝ) : ℂ)
  let a_one : ℝ := 1 / x₀
  let b_one : ℝ := 2 / x₀
  have ha_pos : 0 < a_one := div_pos zero_lt_one hx₀_pos
  have hab : a_one ≤ b_one := div_le_div_of_nonneg_right (by norm_num) hx₀_pos.le
  have hb_lt2 : b_one < 2 := (div_lt_iff₀ hx₀_pos).mpr (by linarith [hx₀_mem.1])
  have hsupp : Function.support w_one ⊆ Set.Icc a_one b_one := by
    intro y hy
    have hwy : F.w (x₀ * y) ≠ 0 := by
      intro hz; apply hy; dsimp [w_one]; rw [hz]; simp
    have hm := F.support hwy
    dsimp [a_one, b_one]
    exact ⟨(div_le_iff₀ hx₀_pos).mpr (by linarith only [hm.1]),
      (le_div_iff₀ hx₀_pos).mpr (by linarith only [hm.2])⟩
  have hsm : ContDiff ℝ ∞ w_one := by
    have h1 : ContDiff ℝ ∞ (fun y : ℝ => ((F.w (x₀ * y) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (F.smooth.comp (contDiff_const.mul contDiff_id))
    exact h1.div_const _
  refine ⟨w_one, a_one, b_one, ha_pos, hab, hb_lt2, hsupp, hsm, ?_⟩
  intro χ
  rw [InverseInitialExcludedPolynomial.polynomial_all_ideals]
  have h1_cpow : ((1 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by simp
  have hshift0 : -HeckeDyadic.shift 0 0 = 0 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  have hchild0 : childLogTest w_one 0 = w_one := by
    funext y; simp [childLogTest, kernelLogPhase]
  rw [h1_cpow, one_mul, hchild0]
  rw [tsum_eq_single (1 : Ideal O)]
  · have hw1 : w_one 1 = 1 := by
      dsimp [w_one]; rw [mul_one]
      exact div_self (Complex.ofReal_ne_zero.mpr hx₀)
    have hnorm1 : ((1 : Ideal O).absNorm : ℝ) / 1 = 1 := by simp
    have hm1 : UniqueFactorizationMonoid.moebius (1 : Ideal O) = 1 :=
      UniqueFactorizationMonoid.moebius_one
    have hc1 : idealCoeff χ 1 = 1 := map_one (idealCoeff χ)
    rw [hm1, hc1, hnorm1, hw1, hshift0, Complex.cpow_zero]
    norm_num
  · intro I hI1
    by_cases hI0 : I = 0
    · rw [hI0, map_zero (idealCoeff χ)]; ring
    · have hge1 : 1 ≤ I.absNorm :=
        Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
      have hne1_norm : I.absNorm ≠ 1 := fun hn1 =>
        hI1 ((Ideal.absNorm_eq_one_iff.mp hn1).trans Ideal.one_eq_top.symm)
      have hge2 : 2 ≤ (I.absNorm : ℝ) := by exact_mod_cast (show 2 ≤ I.absNorm by omega)
      have hw0 : w_one (I.absNorm : ℝ) = 0 := by
        by_contra hne_w
        have hle := (hsupp hne_w).2
        linarith
      rw [div_one, hw0]; ring

/-! ### Part II: Factored sixth-power-free `L^2` bound (`dual_sixth_free_factored_energy`) -/

/-- `RowData` wrapper whose `.character ⟨u.val, u.property.1⟩` equals `(targetRow η u).inverse` on
every ideal, allowing `HeckeInverseAmplification.no_slot_endpoint` to apply directly to
`targetRow η u` without any finite-prime deletion sum. -/
def dualTargetRowData (η : Character) : RowData where
  η := (fixedSourcePrincipal ∅ (by simp)).product η.inverse
  m := rowMaskElement
  f := 1
  m_ne_zero := rowMaskElement_ne_zero
  f_ne_zero := one_ne_zero
  lambda_dvd := dvd_mul_left _ _
  two_dvd := dvd_mul_right _ _

lemma targetRow_conj_dualTargetRowData (η : Character) (u : FreeRow) (J : Ideal O) :
    idealCoeff (targetRow η u) J =
      conj (idealCoeff ((dualTargetRowData η).character ⟨u.val, u.property.1⟩) J) := by
  by_cases hJ0 : J = 0
  · rw [hJ0, map_zero (idealCoeff _), map_zero (idealCoeff _), map_zero]
  · have hg0 : cubicIdealGenerator J ≠ 0 := cubicIdealGenerator_ne_zero J hJ0
    have hspan : Ideal.span {cubicIdealGenerator J} = J := span_cubicIdealGenerator J
    have h1 : idealCoeff ((dualTargetRowData η).character ⟨u.val, u.property.1⟩) J =
        idealCoeff (targetRow η u).inverse J := by
      conv_lhs => rw [← hspan]
      conv_rhs => rw [← hspan]
      rw [idealCoeff_span _ hg0, idealCoeff_span _ hg0,
        RowData.character_spec (dualTargetRowData η) ⟨u.val, u.property.1⟩,
        inverse_target_elementCoeff η u]
      rfl
    rw [h1, idealCoeff_inverse_conj, RingHomCompTriple.comp_apply, RingHom.id_apply]

/-- Rewrites each normalized unpunctured `(inputConjugateRow * ∏ slotCharSum)` summand as a product
of `HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u_free)` and
`∏ canonicalPrimeAmplitude`. -/
theorem dual_factored_product_eq_dyadic
    {σ : Type*} [DecidableEq σ]
    {Δ : ℝ} {D_dual : Parameters.HighData Δ} (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (data : RowData) (Dpool : ℕ)
    (wFresh : 𝓢(ℝ, ℂ)) {bf : ℝ} (hbf : ∀ y, wFresh y ≠ 0 → y ≤ bf)
    (s : ℝ) {X' : ℝ} (hX' : 0 < X') (hDpool_X : bf * X' ≤ (Dpool : ℝ))
    (T' : Finset σ) (Z_slot : σ → ℝ)
    (hZ_pos : ∀ j ∈ T', 0 < Z_slot j)
    (hDpool_Z : ∀ j ∈ T', 2 * Z_slot j ≤ (Dpool : ℝ))
    (hlarge_Z : ∀ j ∈ T', ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j)
    (ζ_base : ℂ) (hζ_re : ζ_base.re ≤ 1)
    (lists : σ → Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals
      (reflectionExcludedPrimes (InverseInitialExcludedPeriod.deletedPeriod (basePeriod data))) Dpool)))
    (a : σ → primePool (CanonicalRowCompletion.outsideSquarefreeIdeals
      (reflectionExcludedPrimes (InverseInitialExcludedPeriod.deletedPeriod (basePeriod data))) Dpool) → ℂ)
    (hlists : ∀ j ∈ T', lists j = InverseInitialCommonLists.poolList
      (CanonicalRowCompletion.outsideSquarefreeIdeals
        (reflectionExcludedPrimes (InverseInitialExcludedPeriod.deletedPeriod (basePeriod data))) Dpool)
      (InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j)))
    (ha : ∀ j ∈ T', ∀ q ∈ lists j,
      a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val / star (idealCoeff (deletedBase data) q.val))
    (u_free : FreeRow) :
    let q_per := InverseInitialExcludedPeriod.deletedPeriod (basePeriod data)
    let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
    let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
      (reflectionExcludedPrimes_bad q_per)
    letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
      fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
    let base := elementCharacter
      (InverseInitialConjugateEnergy.conjugateIdealCharacter
        (idealCoeff (deletedBase data)).toMonoidHom)
    let a_tw : σ → primePool F_pool → ℂ := fun j q =>
      a j q * kernelLogPhase s (Real.log (‖ringComplex (poolPrimary F_pool q)‖ ^ 2 / Z_slot j))
    let ζ_tw : ℂ := ζ_base + ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I
    (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
      ‖inputConjugateRow (poolPrimary F_pool)
          (fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j))
          Finset.univ base 1 1 1
          (fun U => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U / X')) u_free.val *
        ∏ j ∈ T', slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
          lists a_tw base j u_free.val‖ ^ 2 =
      ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u_free) true
          (childLogTest wFresh s) X' 0 0 *
        ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u_free.val
          F_dual.W 2 (Z_slot j) ζ_tw‖ ^ 2 := by
  intro q_per F_pool hFa base a_tw ζ_tw
  letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
    fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
  have hchild_supp : ∀ y, childLogTest wFresh s y ≠ 0 → y ≤ bf :=
    fun y hy => hbf y (fun hz => hy (by simp [childLogTest, hz]))
  have hpol := inputConjugateRow_eq_targetRow_polynomial data Dpool
    (childLogTest wFresh s) hX' hchild_supp hDpool_X u_free
  have hζ_tw_re : ζ_tw.re ≤ 1 := by
    dsimp [ζ_tw]; simp [hζ_re]
  have hslot_eq : ∀ j ∈ T',
      (((Z_slot j) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa) lists a_tw base j u_free.val =
      HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u_free.val F_dual.W 2 (Z_slot j) ζ_tw := by
    intro j hj
    apply slotCharSum_eq_canonicalPrimeAmplitude F_dual data Dpool (hZ_pos j hj) (hDpool_Z j hj)
      (hlarge_Z j hj) ζ_tw hζ_tw_re j lists a_tw (hlists j hj)
    intro q hq
    have hqL : q.val ∈ InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j) := by
      rw [hlists j hj] at hq
      exact (Finset.mem_filter.mp hq).2
    have hq_ne : q.val ≠ 0 :=
      (deleted_source_live_prime F_dual data F_dual.modulus ⊤ (Z_slot j) (hZ_pos j hj)
        ζ_base hζ_re (hlarge_Z j hj) q.val hqL).1.ne_zero
    have hnorm_q : ‖ringComplex (poolPrimary F_pool q)‖ ^ 2 = (q.val.absNorm : ℝ) := by
      rw [ringComplex_norm_sq_eq_absNorm_span, poolPrimary_span F_pool hFa q]
    dsimp [a_tw, ζ_tw]
    rw [ha j hj q hq, hnorm_q, div_mul_eq_mul_div,
      primeProfile_mul_kernelLogPhase F_dual.W (hZ_pos j hj) ζ_base s hq_ne]; rfl
  have hnorm_X : ‖(((X') ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ^ 2 = (X')⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hX' _),
      ← Real.rpow_natCast, ← Real.rpow_mul hX'.le]
    norm_num; exact Real.rpow_neg_one X'
  have hnorm_Z : ‖∏ j ∈ T', (((Z_slot j) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ^ 2 =
      (∏ j ∈ T', Z_slot j)⁻¹ := by
    have hpt_Z : ∀ j ∈ T', ‖(((Z_slot j) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ^ 2 = (Z_slot j)⁻¹ := by
      intro j hj
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hZ_pos j hj) _),
        ← Real.rpow_natCast, ← Real.rpow_mul (hZ_pos j hj).le]
      norm_num; exact Real.rpow_neg_one (Z_slot j)
    rw [norm_prod, ← Finset.prod_pow, Finset.prod_congr rfl hpt_Z, Finset.prod_inv_distrib]
  let A_pol := inputConjugateRow (poolPrimary F_pool)
    (fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j))
    Finset.univ base 1 1 1
    (fun U => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U / X')) u_free.val
  let B_slot := ∏ j ∈ T', slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
    lists a_tw base j u_free.val
  have hprod_slot : (∏ j ∈ T', (((Z_slot j) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * B_slot =
      ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u_free.val
        F_dual.W 2 (Z_slot j) ζ_tw := by
    dsimp [B_slot]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hslot_eq
  calc
    (X' * ∏ j ∈ T', Z_slot j)⁻¹ * ‖A_pol * B_slot‖ ^ 2
      = (X')⁻¹ * (∏ j ∈ T', Z_slot j)⁻¹ * (‖A_pol‖ ^ 2 * ‖B_slot‖ ^ 2) := by
          rw [mul_inv, norm_mul, mul_pow]
    _ = (‖(((X') ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ^ 2 * ‖A_pol‖ ^ 2) *
          (‖∏ j ∈ T', (((Z_slot j) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ^ 2 * ‖B_slot‖ ^ 2) := by
          rw [hnorm_X, hnorm_Z]; ring
    _ = ‖((((X') ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * A_pol) *
          ((∏ j ∈ T', (((Z_slot j) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * B_slot)‖ ^ 2 := by
          rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow]
    _ = _ := by
          dsimp only [A_pol]
          rw [hpol, hprod_slot]

/-- Coarse `s`-uniform `L^2` bound (`≤ C_coarse * U ^ (K + 8)`) on the unpunctured factored sum,
used to truncate the `|s| > S_cut` Schwartz tail in `markedRadial_fourier_l2_le_factored`. -/
theorem dual_factored_coarse_bound
    {σ : Type*} [DecidableEq σ]
    {Δ : ℝ} {D_dual : Parameters.HighData Δ} (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (wFresh : 𝓢(ℝ, ℂ)) {bf B_w : ℝ} (hbf0 : 0 < bf) (hBw0 : 0 ≤ B_w)
    (hbf : ∀ y, wFresh y ≠ 0 → y ≤ bf) (hBw : ∀ y, ‖wFresh y‖ ≤ B_w)
    (K : ℕ) (data : RowData) {U X' : ℝ} (hU1 : 1 ≤ U) (hX' : 0 < X') (hX'_hi : X' ≤ U ^ (2 : ℝ))
    (T' : Finset σ) (hT_card : T'.card ≤ K)
    (Z_slot : σ → ℝ) (hZ1 : ∀ j ∈ T', 1 ≤ Z_slot j) (hZ_hi : ∀ j ∈ T', Z_slot j ≤ U)
    (ζ : ℂ) (hζ_re : ζ.re ≤ 1)
    (S_free : Finset FreeRow) (hS_norm : ∀ u ∈ S_free, rowNorm u ≤ U ^ (2 : ℝ))
    (s : ℝ) :
    (∑ u ∈ S_free,
      ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
          (childLogTest wFresh s) X' 0 0 *
        ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (Z_slot j) ζ‖ ^ 2) ≤
      (49 * bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * (9604 : ℝ) ^ K + 1) *
        U ^ ((K : ℝ) + 10) := by
  have hU_pos : 0 < U := zero_lt_one.trans_le hU1
  have hchild_supp : ∀ y, childLogTest wFresh s y ≠ 0 → y ≤ bf :=
    fun y hy => hbf y (fun hz => hy (by simp [childLogTest, hz]))
  have hchild_norm : ∀ y, ‖childLogTest wFresh s y‖ ≤ B_w := by
    intro y; unfold childLogTest; rw [norm_mul, kernelLogPhase_norm, mul_one]; exact hBw y
  by_cases hlt : bf * X' < 1
  · have hsum0 : (∑ u ∈ S_free,
        ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (Z_slot j) ζ‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      rw [polynomial_eq_zero_of_mul_lt_one _ _ hX' hchild_supp hlt, zero_mul, norm_zero, sq, zero_mul]
    rw [hsum0]
    positivity
  · have hbfX : 1 ≤ bf * X' := not_lt.mp hlt
    have hX_inv : (X')⁻¹ ≤ bf := (inv_le_iff_one_le_mul₀ hX').mpr hbfX
    have hFW_norm : ∀ x, ‖F_dual.W x‖ ≤ 1 := by
      intro x; rw [F_dual.complex_eq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (F_dual.bounded x).1]
      exact (F_dual.bounded x).2
    have hcard_S : (S_free.card : ℝ) ≤ 49 * U ^ (2 : ℝ) := by
      apply card_finset_injective_norm_sq_le_49_mul (fun u : FreeRow => u.val) Subtype.val_injective
        S_free (Real.one_le_rpow hU1 (by norm_num))
      intro u hu
      rw [ringComplex_norm_sq_eq_absNorm_span]
      exact hS_norm u hu
    have hpt : ∀ u ∈ S_free,
        ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (Z_slot j) ζ‖ ^ 2 ≤
        (bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * (9604 : ℝ) ^ K) * U ^ ((K : ℝ) + 8) := by
      intro u _
      rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
      have hc_pol := polynomial_coarse_norm_le (targetRow (deletedBase data).inverse u)
        (childLogTest wFresh s) hX' hbf0.le hBw0 hchild_supp hchild_norm
      have hc_pol_sq : ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
          (childLogTest wFresh s) X' 0 0‖ ^ 2 ≤
          bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * U ^ (8 : ℝ) := by
        have h1 := pow_le_pow_left₀ (norm_nonneg _) hc_pol 2
        have hXrpow : ((X') ^ (-(1 / 2 : ℝ))) ^ 2 = (X')⁻¹ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX'.le]; norm_num; exact Real.rpow_neg_one X'
        rw [mul_pow, hXrpow] at h1
        have hU2_ge1 : 1 ≤ U ^ (2 : ℝ) := Real.one_le_rpow hU1 (by norm_num)
        have hbr : 1 + bf * X' ≤ (1 + bf) * U ^ (2 : ℝ) := by
          calc 1 + bf * X' ≤ 1 * U ^ (2 : ℝ) + bf * U ^ (2 : ℝ) :=
                add_le_add (by linarith) (mul_le_mul_of_nonneg_left hX'_hi hbf0.le)
            _ = (1 + bf) * U ^ (2 : ℝ) := by ring
        have hbr4 : (1 + bf * X') ^ 4 ≤ (1 + bf) ^ 4 * U ^ (8 : ℝ) := by
          calc (1 + bf * X') ^ 4 ≤ ((1 + bf) * U ^ (2 : ℝ)) ^ 4 :=
                pow_le_pow_left₀ (by positivity) hbr 4
            _ = (1 + bf) ^ 4 * (U ^ (2 : ℝ)) ^ 4 := mul_pow _ _ 4
            _ = (1 + bf) ^ 4 * U ^ (8 : ℝ) := by
                rw [← Real.rpow_natCast (U ^ (2 : ℝ)) 4, ← Real.rpow_mul hU_pos.le]; norm_num
        calc _ ≤ (X')⁻¹ * (B_w * (49 * (1 + bf * X') ^ 2)) ^ 2 := h1
          _ = (X')⁻¹ * (B_w * 49) ^ 2 * (1 + bf * X') ^ 4 := by ring
          _ ≤ bf * (B_w * 49) ^ 2 * ((1 + bf) ^ 4 * U ^ (8 : ℝ)) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right hX_inv (sq_nonneg _)) hbr4
                (by positivity) (by positivity)
          _ = bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * U ^ (8 : ℝ) := by ring
      have hprod_amp : (∏ j ∈ T', ‖HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (Z_slot j) ζ‖ ^ 2) ≤ (9604 : ℝ) ^ K * U ^ (K : ℝ) := by
        calc _ ≤ ∏ _j ∈ T', (9604 * U) := Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun j hj =>
              (canonicalPrimeAmplitude_norm_sq_le_trivial F_dual.modulus ⊤ F_dual.W
                F_dual.complex_support hFW_norm (hZ1 j hj) hζ_re u.val).trans
                (mul_le_mul_of_nonneg_left (hZ_hi j hj) (by norm_num)))
          _ = (9604 * U) ^ T'.card := by rw [Finset.prod_const]
          _ ≤ (9604 * U) ^ K := pow_le_pow_right₀ (by linarith) hT_card
          _ = (9604 : ℝ) ^ K * U ^ (K : ℝ) := by rw [mul_pow, Real.rpow_natCast]
      calc _ ≤ (bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * U ^ (8 : ℝ)) * ((9604 : ℝ) ^ K * U ^ (K : ℝ)) :=
            mul_le_mul hc_pol_sq hprod_amp (Finset.prod_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
        _ = (bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * (9604 : ℝ) ^ K) * (U ^ (8 : ℝ) * U ^ (K : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hU_pos]; congr 2; ring
    calc
      (∑ u ∈ S_free, ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (Z_slot j) ζ‖ ^ 2)
        ≤ ∑ _u ∈ S_free, (bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * (9604 : ℝ) ^ K) * U ^ ((K : ℝ) + 8) :=
          Finset.sum_le_sum hpt
      _ = (S_free.card : ℝ) * ((bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * (9604 : ℝ) ^ K) * U ^ ((K : ℝ) + 8)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (49 * U ^ (2 : ℝ)) * ((bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * (9604 : ℝ) ^ K) * U ^ ((K : ℝ) + 8)) :=
          mul_le_mul_of_nonneg_right hcard_S (by positivity)
      _ = (49 * bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * (9604 : ℝ) ^ K) * (U ^ (2 : ℝ) * U ^ ((K : ℝ) + 8)) := by
          ring
      _ ≤ _ := by
          rw [← Real.rpow_add hU_pos, show (2 : ℝ) + ((K : ℝ) + 8) = (K : ℝ) + 10 by ring]
          exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hU_pos.le _)

/-- Branch 1 (`no_slot_endpoint` + trivial prime-slot Cauchy-Schwarz): bounds any subset
`R_sub : Finset FreeRow` with `rowNorm u ≤ U ^ H_sub` (`0 ≤ H_sub ≤ 1`) and `X' ≤ U ^ r_unm`
(`r_unm ≤ 1`) by `C_ns * U ^ (max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + z_T + 1 / 100) * (1 + |s|)^(2 * J_ns)`. -/
theorem dual_no_slot_branch_bound
    {Δ : ℝ} {D_dual : Parameters.HighData Δ} (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (wFresh : 𝓢(ℝ, ℂ)) {af bf B_w : ℝ} (haf : 0 < af) (habf : af ≤ bf) (hBw0 : 0 ≤ B_w)
    (hs_w : Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf) (hBw : ∀ y, ‖wFresh y‖ ≤ B_w)
    (K : ℕ) :
    ∃ J_ns : ℕ, ∀ data : RowData, ∃ C_ns U_ns : ℝ, 0 < C_ns ∧ 1 < U_ns ∧
      ∀ U : ℝ, U_ns ≤ U →
      ∀ {σ : Type} [DecidableEq σ] (T' : Finset σ), T'.card ≤ K →
      ∀ (Z_slot : σ → ℝ) {z_T : ℝ}, 0 ≤ z_T →
        (∀ j ∈ T', 1 ≤ Z_slot j) → (∏ j ∈ T', Z_slot j) ≤ U ^ z_T →
      ∀ {H_sub r_unm X' : ℝ}, 0 ≤ H_sub → H_sub ≤ 1 → r_unm ≤ 1 →
        0 < X' → X' ≤ U ^ r_unm →
      ∀ (ζ : ℂ), ζ.re ≤ 1 →
      ∀ (R_sub : Finset FreeRow), (∀ u ∈ R_sub, rowNorm u ≤ U ^ H_sub) →
      ∀ s : ℝ,
        (∑ u ∈ R_sub,
          ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
              (childLogTest wFresh s) X' 0 0 *
            ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (Z_slot j) ζ‖ ^ 2) ≤
          C_ns * U ^ (max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + z_T + 1 / 100) *
            (1 + |s|) ^ (2 * J_ns) := by
  have hbf_pos : 0 < bf := haf.trans_le habf
  obtain ⟨c_ns, κ_ns, K_ns, hc_ns, _, hκ_ns, hK_ns, hns_ev⟩ :=
    HeckeInverseAmplification.no_slot_endpoint F_dual.modulus ⊤ le_top F_dual.S
      F_dual.w F_dual.smooth F_dual.compact F_dual.positive_support
      (fun y => (F_dual.bounded y).1) F_dual.nonzero 1 2 1
      (by norm_num) (by norm_num) (by norm_num) F_dual.support
      (fun y => (F_dual.bounded y).2) 200 (1 / 200) (by norm_num) (by norm_num)
  obtain ⟨J_raw, hraw_all⟩ :=
    scaleProfile_childLogTest_rawMoment wFresh haf habf hs_w hc_ns hκ_ns
  obtain ⟨U_ev, hU_ev⟩ := eventually_atTop.mp hns_ev
  refine ⟨J_raw, ?_⟩
  intro data
  let data_tgt := dualTargetRowData (deletedBase data).inverse
  obtain ⟨C_raw, hC_raw, hraw⟩ := hraw_all data_tgt
  let U_ns : ℝ := max 2 ((max 2 U_ev) ^ (200 : ℝ))
  have hU_ns1 : 1 < U_ns := lt_of_lt_of_le one_lt_two (le_max_left _ _)
  let C_triv : ℝ := 49 * bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2
  have hCtriv_nn : 0 ≤ C_triv := by dsimp [C_triv]; positivity
  let C_ns : ℝ := (C_raw * K_ns + C_triv + 1) * (9604 : ℝ) ^ K
  refine ⟨C_ns, U_ns, by dsimp [C_ns]; positivity, hU_ns1, ?_⟩
  intro U hU σ _ T' hT_card Z_slot z_T hzT0 hZ1 hZ_prod H_sub r_unm X'
    hHsub0 hHsub1 hrunm1 hX' hX'_le ζ hζ_re R_sub hR_norm s
  have hU1 : 1 < U := hU_ns1.trans_le hU
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have h1s : 1 ≤ (1 + |s|) ^ (2 * J_raw) := one_le_pow₀ (by linarith [abs_nonneg s])
  have hFW_norm : ∀ x, ‖F_dual.W x‖ ≤ 1 := by
    intro x; rw [F_dual.complex_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (F_dual.bounded x).1]
    exact (F_dual.bounded x).2
  have hprod_amp : ∀ u : FreeRow,
      ‖∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
        F_dual.W 2 (Z_slot j) ζ‖ ^ 2 ≤ (9604 : ℝ) ^ K * U ^ z_T := by
    intro u
    rw [norm_prod, ← Finset.prod_pow]
    calc (∏ j ∈ T', ‖HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (Z_slot j) ζ‖ ^ 2)
        ≤ ∏ j ∈ T', (9604 * Z_slot j) := Finset.prod_le_prod (fun _ _ => sq_nonneg _)
            (fun j hj => canonicalPrimeAmplitude_norm_sq_le_trivial F_dual.modulus ⊤ F_dual.W
              F_dual.complex_support hFW_norm (hZ1 j hj) hζ_re u.val)
      _ = (9604 : ℝ) ^ T'.card * ∏ j ∈ T', Z_slot j := by rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ (9604 : ℝ) ^ K * U ^ z_T := mul_le_mul (pow_le_pow_right₀ (by norm_num) hT_card)
            hZ_prod (Finset.prod_nonneg (fun j hj => (zero_lt_one.trans_le (hZ1 j hj)).le)) (by positivity)
  have hchild_supp : ∀ y, childLogTest wFresh s y ≠ 0 → y ≤ bf :=
    fun y hy => (hs_w (fun hz => hy (by simp [childLogTest, hz]))).2
  have hchild_norm : ∀ y, ‖childLogTest wFresh s y‖ ≤ B_w := by
    intro y; unfold childLogTest; rw [norm_mul, kernelLogPhase_norm, mul_one]; exact hBw y
  -- Bound `∑ u ∈ R_sub, ‖polynomial (targetRow ...) ... X'‖ ^ 2` across all three `X'` ranges.
  have hpol_sum :
      (∑ u ∈ R_sub, ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
          (childLogTest wFresh s) X' 0 0‖ ^ 2) ≤
        (C_raw * K_ns + C_triv + 1) *
          U ^ (max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + 1 / 100) *
          (1 + |s|) ^ (2 * J_raw) := by
    by_cases hlt_bf : bf * X' < 1
    · have hsum0 : (∑ u ∈ R_sub, ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
          (childLogTest wFresh s) X' 0 0‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro u _
        rw [polynomial_eq_zero_of_mul_lt_one _ _ hX' hchild_supp hlt_bf, norm_zero, sq, zero_mul]
      rw [hsum0]
      positivity
    · by_cases hX1 : X' < 1
      · have hbfX : 1 ≤ bf * X' := not_lt.mp hlt_bf
        have hcard_R : (R_sub.card : ℝ) ≤ 49 * U ^ H_sub := by
          apply card_finset_injective_norm_sq_le_49_mul (fun u : FreeRow => u.val) Subtype.val_injective
            R_sub (Real.one_le_rpow hU1.le hHsub0)
          intro u hu; rw [ringComplex_norm_sq_eq_absNorm_span]; exact hR_norm u hu
        have hpt_u : ∀ u ∈ R_sub,
            ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                (childLogTest wFresh s) X' 0 0‖ ^ 2 ≤
              bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 :=
          fun u _ => polynomial_unit_scale_norm_sq_le _ _ hX' hbf_pos.le hBw0 hchild_supp hchild_norm hbfX hX1.le
        have hH_le_exp : U ^ H_sub ≤ U ^ (max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + 1 / 100) :=
          Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith [le_max_left H_sub ((H_sub + 5 * max 0 r_unm) / 6)])
        calc (∑ u ∈ R_sub, ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                (childLogTest wFresh s) X' 0 0‖ ^ 2)
            ≤ (R_sub.card : ℝ) * (bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2) := by
              calc _ ≤ ∑ _u ∈ R_sub, bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 := Finset.sum_le_sum hpt_u
                _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (49 * U ^ H_sub) * (bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2) :=
              mul_le_mul_of_nonneg_right hcard_R (by positivity)
          _ = C_triv * U ^ H_sub := by dsimp [C_triv]; ring
          _ ≤ (C_raw * K_ns + C_triv + 1) *
                U ^ (max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + 1 / 100) * 1 := by
              rw [mul_one]
              exact mul_le_mul (by linarith [mul_nonneg hC_raw.le hK_ns]) hH_le_exp
                (Real.rpow_nonneg hU_pos.le _) (by dsimp [C_triv]; positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left h1s (by dsimp [C_triv]; positivity)
      · -- Main case `1 ≤ X'`: apply `no_slot_endpoint` at `U_row := U ^ (max (1/200) H_sub)`.
        have hX_ge1 : 1 ≤ X' := not_lt.mp hX1
        let H_eff : ℝ := max (1 / 200) H_sub
        have hHeff_lo : 1 / 200 ≤ H_eff := le_max_left _ _
        have hHeff_pos : 0 < H_eff := by linarith
        have hHeff_hi : H_eff ≤ H_sub + 1 / 200 := max_le (by linarith) (by linarith)
        let U_row : ℝ := U ^ H_eff
        have hUrow_pos : 0 < U_row := Real.rpow_pos_of_pos hU_pos _
        have hUrow_ge : U_ev ≤ U_row := by
          have h1 : (max 2 U_ev) ^ (200 : ℝ) ≤ U := (le_max_right _ _).trans hU
          have h2 : max 2 U_ev ≤ U ^ (1 / 200 : ℝ) := by
            calc max 2 U_ev = ((max 2 U_ev) ^ (200 : ℝ)) ^ (1 / 200 : ℝ) := by
                  rw [← Real.rpow_mul (by positivity)]; norm_num
              _ ≤ U ^ (1 / 200 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
          exact (le_max_right 2 U_ev).trans (h2.trans (Real.rpow_le_rpow_of_exponent_le hU1.le hHeff_lo))
        let r_act : ℝ := Real.logb U X'
        have hract0 : 0 ≤ r_act := Real.logb_nonneg hU1 hX_ge1
        have hract_le : r_act ≤ r_unm := by
          rw [Real.logb_le_iff_le_rpow hU1 hX']; exact hX'_le
        have hract_pos_le : r_act ≤ max 0 r_unm := hract_le.trans (le_max_right 0 r_unm)
        have hract1 : r_act ≤ 1 := hract_le.trans hrunm1
        let r_rel : ℝ := r_act / H_eff
        have hrrel0 : 0 ≤ r_rel := div_nonneg hract0 hHeff_pos.le
        have hrrel200 : r_rel ≤ 200 := (div_le_iff₀ hHeff_pos).mpr (by linarith)
        have hUrow_r : U_row ^ r_rel = X' := by
          dsimp [U_row, r_rel]
          rw [← Real.rpow_mul hU_pos.le, mul_div_cancel₀ _ hHeff_pos.ne']
          exact Real.rpow_logb hU_pos hU1.ne' hX'
        let W_s := orientedProfile true (childLogTest wFresh s)
        have hWs_supp : Function.support W_s ⊆ Set.Icc af bf := by
          intro y hy; apply hs_w; intro hz; exact hy (by simp [W_s, orientedProfile, childLogTest, hz])
        have hWs_sm : ContDiff ℝ ∞ W_s := by
          have hc : ContDiff ℝ ∞ (childLogTest wFresh s) :=
            InverseInitialOriginalHeight.child_smooth wFresh af bf haf hs_w (wFresh.smooth ⊤) s
          exact Complex.conjCLE.contDiff.comp hc
        have hR_Urow : ∀ u ∈ R_sub, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U_row := fun u hu =>
          (hR_norm u hu).trans (Real.rpow_le_rpow_of_exponent_le hU1.le (le_max_right _ _))
        obtain ⟨hm0, hm1⟩ := hraw s
        have hb_ns := hU_ev U_row hUrow_ge r_rel data_tgt R_sub W_s af bf
          (C_raw * (1 + |s|) ^ (2 * J_raw)) hrrel0 hrrel200 (by positivity)
          haf hbf_pos.le hWs_supp hWs_sm hR_Urow hm0 hm1
        rw [hUrow_r] at hb_ns
        have hnorm_eq : ∀ u ∈ R_sub,
            ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                (childLogTest wFresh s) X' 0 0‖ =
              ‖HeckeDyadic.polynomial (data_tgt.character ⟨u.val, u.property.1⟩) true W_s X' 0 0‖ := by
          intro u _
          have hn := norm_of_oriented_coefficients (targetRow (deletedBase data).inverse u)
            (data_tgt.character ⟨u.val, u.property.1⟩) true
            (fun J => by simpa using targetRow_conj_dualTargetRowData (deletedBase data).inverse u J)
            true (childLogTest wFresh s) X' 0 0 hX'
          simpa [W_s, orientedFrequency] using hn
        have hexp_le : H_eff * (sourceExponent r_rel + 1 / 200) ≤
            max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + 1 / 100 := by
          have h1 : H_eff * sourceExponent r_rel = max H_eff ((H_eff + 5 * r_act) / 6) := by
            unfold sourceExponent
            rw [mul_max_of_nonneg _ _ hHeff_pos.le, mul_one]
            congr 1; dsimp [r_rel]; field_simp [hHeff_pos.ne']
          rw [mul_add, h1]
          have hHeff_100 : H_eff * (1 / 200) ≤ 1 / 200 := by
            have : H_eff ≤ 1 := max_le (by norm_num) hHsub1
            linarith
          rcases le_total H_eff ((H_eff + 5 * r_act) / 6) with hm_l | hm_r
          · rw [max_eq_right hm_l]
            linarith [le_max_right H_sub ((H_sub + 5 * max 0 r_unm) / 6)]
          · rw [max_eq_left hm_r]
            linarith [le_max_left H_sub ((H_sub + 5 * max 0 r_unm) / 6)]
        calc
          (∑ u ∈ R_sub, ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                (childLogTest wFresh s) X' 0 0‖ ^ 2)
            = ∑ u ∈ R_sub, ‖HeckeDyadic.polynomial (data_tgt.character ⟨u.val, u.property.1⟩) true
                W_s X' 0 0‖ ^ 2 :=
              Finset.sum_congr rfl (fun u hu => congrArg (fun x : ℝ => x ^ 2) (hnorm_eq u hu))
          _ ≤ C_raw * (1 + |s|) ^ (2 * J_raw) * K_ns * U_row ^ (sourceExponent r_rel + 1 / 200) := hb_ns
          _ = C_raw * K_ns * U ^ (H_eff * (sourceExponent r_rel + 1 / 200)) * (1 + |s|) ^ (2 * J_raw) := by
              dsimp [U_row]; rw [← Real.rpow_mul hU_pos.le]; ring
          _ ≤ (C_raw * K_ns + C_triv + 1) *
                U ^ (max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + 1 / 100) *
                (1 + |s|) ^ (2 * J_raw) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul (by linarith)
                (Real.rpow_le_rpow_of_exponent_le hU1.le hexp_le)
                (Real.rpow_nonneg hU_pos.le _) (by positivity)
  calc
    (∑ u ∈ R_sub, ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
          (childLogTest wFresh s) X' 0 0 *
        ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (Z_slot j) ζ‖ ^ 2)
      ≤ ∑ u ∈ R_sub, ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0‖ ^ 2 * ((9604 : ℝ) ^ K * U ^ z_T) := by
          apply Finset.sum_le_sum; intro u _
          rw [norm_mul, mul_pow]
          exact mul_le_mul_of_nonneg_left (hprod_amp u) (sq_nonneg _)
    _ = (∑ u ∈ R_sub, ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0‖ ^ 2) * ((9604 : ℝ) ^ K * U ^ z_T) :=
          (Finset.sum_mul _ _ _).symm
    _ ≤ ((C_raw * K_ns + C_triv + 1) *
          U ^ (max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + 1 / 100) *
          (1 + |s|) ^ (2 * J_raw)) * ((9604 : ℝ) ^ K * U ^ z_T) :=
          mul_le_mul_of_nonneg_right hpol_sum (by positivity)
    _ = C_ns * (U ^ (max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + 1 / 100) * U ^ z_T) *
          (1 + |s|) ^ (2 * J_raw) := by dsimp [C_ns]; ring
    _ = _ := by
          rw [← Real.rpow_add hU_pos]
          congr 2; ring

/-- Uniform pointwise `canonicalPrimeAmplitude` bound `(U ^ (D.ell j / d_outer)) ^ ((2*a - 1)/2 + D_dual.t)`
on buffered detector bins `(i_bin, a)` (`1 ≤ i_bin ≤ n_bins`, `51/100 ≤ a ≤ 1`) for all rows `u`
with `Z_dual ^ (1/100) ≤ rowNorm u ≤ U ^ H_free` (`3/100 ≤ H_free ≤ 1`, `1/2 ≤ d_outer ≤ 5/6`),
absorbing the constant `C_ray` of `ray_prime_bin_bound` via `upper_allowance_eventually`. -/
theorem dual_ray_prime_bin_supply
    {Δ Δ_dual : ℝ} (D : Parameters.HighData Δ) (D_dual : Parameters.HighData Δ_dual)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    {τ_dual : ℝ} (hτ_pos : 0 < τ_dual) (hτ_le : 2 * τ_dual ≤ D_dual.t)
    (n_bins : ℕ) :
    ∀ data : RowData, ∃ U_ray : ℝ, 1 < U_ray ∧
      ∀ U : ℝ, U_ray ≤ U →
      ∀ {d_outer H_free : ℝ}, 1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        3 / 100 ≤ H_free → H_free ≤ 1 →
      let Z_dual := U ^ (3 / (2 * d_outer))
      ∀ {i_bin : ℕ} {a : ℝ}, 1 ≤ i_bin → i_bin ≤ n_bins → 51 / 100 ≤ a → a ≤ 1 →
      ∀ u : FreeRow, Z_dual ^ (1 / 100 : ℝ) ≤ rowNorm u → rowNorm u ≤ U ^ H_free →
        detectorMaximum (sourceDetectorFamily F_dual.S F_dual.exclusions.prime
          (deletedBase data).inverse u (rayCubeFamily F_dual.modulus ⊤ le_top u))
          (3 * (i_bin + 1 : ℕ) * Z_dual ^ τ_dual) < a + 2 * D_dual.e →
      ∀ ζ : ℂ, ζ.re = 17 / 50 → |ζ.im| ≤ Z_dual ^ τ_dual →
      ∀ j : Fin D.N,
        ‖HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ≤
        (U ^ (D.ell j / d_outer)) ^ ((2 * a - 1) / 2 + D_dual.t) := by
  letI : Fintype (RayQuotient.Characters F_dual.modulus ⊤) := Fintype.ofFinite _
  obtain ⟨C_ray, hC_ray, hray⟩ :=
    HeckePrimeRay.ray_prime_bin_bound F_dual.modulus ⊤ le_top F_dual.W 1 2 zero_lt_one
      F_dual.complex_support (F_dual.W.smooth ⊤)
      D_dual.t (4 / 5) τ_dual D_dual.ε D_dual.e D_dual.κ (200 * D_dual.t) 0 1
      D_dual.t_pos.le (by norm_num) hτ_pos D_dual.epsilon_pos D_dual.e_pos D_dual.e_small
      D_dual.kappa_pos (by linarith [D_dual.t_pos]) D_dual.phase_budget
  have hallow := HeckePrimeAmplitudeBins.upper_allowance_eventually
    C_ray (1 / 100) D_dual.rmin D_dual.ε D_dual.t (by norm_num) D_dual.t_pos D_dual.epsilon_gap
  intro data
  have hnp_ev := freeRow_nonprincipal_eventually F_dual.modulus ⊤ le_top
    F_dual.S F_dual.exclusions.prime (deletedBase data).inverse (1 / 100) (by norm_num)
  have hZ_gates : ∀ᶠ Z : ℝ in atTop,
      2 < Z ∧
      2 ≤ Z ^ (1 / 100 : ℝ) ∧
      2 < Z ^ τ_dual ∧
      ((ProbeHighRowFamily.conductorConstant : ℝ) * (F_dual.modulus.absNorm : ℝ)) ≤
        Z ^ D_dual.t ∧
      (3 + (3 * n_bins + 2 : ℕ) * Z ^ τ_dual) ^ 2 ≤ Z ^ (2 * D_dual.t) ∧
      (∀ j : Fin D.N, 9 < Z ^ (D_dual.ell (emb j)) ∧
        2 * (|Real.log 1| + |Real.log 2|) + 1 ≤ Real.log (Z ^ (D_dual.ell (emb j)))) := by
    have h1 : ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ^ (1 / 100 : ℝ) :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).eventually (eventually_ge_atTop 2)
    have h2 : ∀ᶠ Z : ℝ in atTop, 2 < Z ^ τ_dual :=
      (tendsto_rpow_atTop hτ_pos).eventually (eventually_gt_atTop 2)
    have h3 : ∀ᶠ Z : ℝ in atTop,
        ((ProbeHighRowFamily.conductorConstant : ℝ) * (F_dual.modulus.absNorm : ℝ)) ≤
          Z ^ D_dual.t :=
      (tendsto_rpow_atTop D_dual.t_pos).eventually (eventually_ge_atTop _)
    have h4 : ∀ᶠ Z : ℝ in atTop,
        (3 + (3 * n_bins + 2 : ℕ) * Z ^ τ_dual) ^ 2 ≤ Z ^ (2 * D_dual.t) := by
      have hexp_gt : 0 < D_dual.t - τ_dual := by linarith [D_dual.t_pos]
      have hsub : ∀ᶠ Z : ℝ in atTop, (3 + (3 * n_bins + 2 : ℕ) : ℝ) ≤ Z ^ (D_dual.t - τ_dual) :=
        (tendsto_rpow_atTop hexp_gt).eventually (eventually_ge_atTop _)
      filter_upwards [hsub, eventually_ge_atTop (1 : ℝ)] with Z hZs hZ1
      have hZp : 0 < Z := zero_lt_one.trans_le hZ1
      have h1_le_Zt : 1 ≤ Z ^ τ_dual := Real.one_le_rpow hZ1 hτ_pos.le
      have hsum_le : 3 + (3 * n_bins + 2 : ℕ) * Z ^ τ_dual ≤ Z ^ D_dual.t := by
        calc 3 + (3 * n_bins + 2 : ℕ) * Z ^ τ_dual
            ≤ (3 + (3 * n_bins + 2 : ℕ) : ℝ) * Z ^ τ_dual := by nlinarith
          _ ≤ Z ^ (D_dual.t - τ_dual) * Z ^ τ_dual :=
              mul_le_mul_of_nonneg_right hZs (Real.rpow_nonneg hZp.le _)
          _ = Z ^ D_dual.t := by rw [← Real.rpow_add hZp]; congr 1; ring
      calc (3 + (3 * n_bins + 2 : ℕ) * Z ^ τ_dual) ^ 2
          ≤ (Z ^ D_dual.t) ^ 2 := pow_le_pow_left₀ (by positivity) hsum_le 2
        _ = Z ^ (2 * D_dual.t) := by
            rw [← Real.rpow_natCast (Z ^ D_dual.t) 2, ← Real.rpow_mul hZp.le]; congr 1; ring
    have h5 : ∀ᶠ Z : ℝ in atTop, ∀ j : Fin D.N,
        9 < Z ^ (D_dual.ell (emb j)) ∧
          2 * (|Real.log 1| + |Real.log 2|) + 1 ≤ Real.log (Z ^ (D_dual.ell (emb j))) := by
      rw [Filter.eventually_all]
      intro j
      have hj_pos : 0 < D_dual.ell (emb j) := (D_dual.slots_bounds (emb j)).1
      let B_log := max 10 (Real.exp (2 * (|Real.log 1| + |Real.log 2|) + 1))
      filter_upwards [(tendsto_rpow_atTop hj_pos).eventually (eventually_ge_atTop B_log)] with Z hZB
      have hgt9 : 9 < Z ^ (D_dual.ell (emb j)) := lt_of_lt_of_le (by dsimp [B_log]; linarith [le_max_left 10 (Real.exp (2 * (|Real.log 1| + |Real.log 2|) + 1))]) hZB
      refine ⟨hgt9, ?_⟩
      have hexp_le : Real.exp (2 * (|Real.log 1| + |Real.log 2|) + 1) ≤ Z ^ (D_dual.ell (emb j)) :=
        (le_max_right _ _).trans hZB
      exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp_le
    filter_upwards [eventually_gt_atTop (2 : ℝ), h1, h2, h3, h4, h5] with Z hz0 hz1 hz2 hz3 hz4 hz5
    exact ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp (hallow.and (hnp_ev.and hZ_gates))
  let U_ray : ℝ := max 2 (max 2 Z₀)
  refine ⟨U_ray, lt_of_lt_of_le one_lt_two (le_max_left _ _), ?_⟩
  intro U hU d_outer H_free hd_lo hd_hi hHf_lo hHf_hi Z_dual i_bin a hi_lo hi_hi ha_lo ha_hi
    u hu_lo hu_hi hnext ζ hζ_re hζ_im j
  have hU_gt1 : 1 < U := (lt_of_lt_of_le one_lt_two (le_max_left _ _)).trans_le hU
  have hU_pos : 0 < U := zero_lt_one.trans hU_gt1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have hexp_Zd : 1 ≤ 3 / (2 * d_outer) := (one_le_div (by positivity)).mpr (by linarith only [hd_hi])
  have hZd_ge_U : U ≤ Z_dual := by
    calc U = U ^ (1 : ℝ) := (Real.rpow_one U).symm
      _ ≤ U ^ (3 / (2 * d_outer)) := Real.rpow_le_rpow_of_exponent_le hU_gt1.le hexp_Zd
  have hZd_ge_Z₀ : Z₀ ≤ Z_dual :=
    ((le_max_right 2 Z₀).trans ((le_max_right 2 _).trans hU)).trans hZd_ge_U
  obtain ⟨hallowZ, hnpZ, hZ2, hZ100, hZτ, hZcond, hZht, hZslot⟩ := hZ₀ Z_dual hZd_ge_Z₀
  have hZd1 : 1 < Z_dual := one_lt_two.trans hZ2
  have hZd_pos : 0 < Z_dual := zero_lt_one.trans hZd1
  let d_ray : ℝ := (2 / 3) * d_outer * H_free + D_dual.t
  have hd_ray_lo : 1 / 100 ≤ d_ray := by
    have ht0 := D_dual.t_pos
    dsimp only [d_ray]; nlinarith only [hd_lo, hHf_lo, ht0]
  have hd_ray_pos : 0 < d_ray := by linarith only [hd_ray_lo]
  have hd_ray_hi : d_ray ≤ 4 / 5 := by
    have ht1 := D_dual.t_small
    dsimp only [d_ray]; nlinarith only [hd_lo, hd_hi, hHf_lo, hHf_hi, ht1]
  have h2_Zd_d : 2 ≤ Z_dual ^ d_ray :=
    hZ100.trans (Real.rpow_le_rpow_of_exponent_le hZd1.le hd_ray_lo)
  let r_j : ℝ := D_dual.ell (emb j) / d_ray
  have hrj_lo : D_dual.rmin ≤ r_j := by
    dsimp only [r_j]
    rw [le_div_iff₀ hd_ray_pos]
    have hb := (D_dual.slots_bounds (emb j)).2.1
    have hrmin0 := D_dual.rmin_pos
    nlinarith only [hb, hrmin0, hd_ray_hi]
  have hrj_hi : r_j ≤ D_dual.t := by
    dsimp only [r_j]
    rw [div_le_iff₀ hd_ray_pos]
    have hb := (D_dual.slots_bounds (emb j)).2.2
    have ht0 := D_dual.t_pos
    nlinarith only [hb, ht0, hd_ray_lo]
  have hscale_eq : (Z_dual ^ d_ray) ^ r_j = U ^ (D.ell j / d_outer) := by
    dsimp only [Z_dual, r_j]
    rw [← Real.rpow_mul hZd_pos.le, mul_div_cancel₀ _ hd_ray_pos.ne', hemb j,
      ← Real.rpow_mul hU_pos.le]
    congr 1; field_simp [hd_pos.ne']
  have hscale_Zd : Z_dual ^ (D_dual.ell (emb j)) = U ^ (D.ell j / d_outer) := by
    dsimp only [Z_dual]; rw [hemb j, ← Real.rpow_mul hU_pos.le]; congr 1; field_simp [hd_pos.ne']
  obtain ⟨hgt9_Zd, hlog_Zd⟩ := hZslot j
  rw [hscale_Zd] at hgt9_Zd
  have hlog_eq : 2 * (|Real.log 1| + |Real.log 2|) + 1 ≤ Real.log ((Z_dual ^ d_ray) ^ r_j) := by
    rwa [hscale_eq, ← hscale_Zd]
  have hnp_ray : ∀ θ : RayQuotient.Characters F_dual.modulus ⊤,
      (HeckePrimeRay.twistedFamily F_dual.modulus ⊤ le_top (rawRow u).inverse θ).residue ≠ 1 :=
    fun θ => hnpZ u hu_lo (Sum.inr θ)
  have hmax_ray : HeckeDetectorZeros.zeroMaximum
      (HeckePrimeRay.twistedFamily F_dual.modulus ⊤ le_top (rawRow u).inverse) hnp_ray
      (3 * (i_bin + 1 : ℕ) * Z_dual ^ τ_dual) < a + 2 * D_dual.e :=
    (ProbeRayCharacterFamily.source_nonprincipal_maximum_dominates F_dual.S F_dual.exclusions.prime
      (deletedBase data).inverse u (rayCubeFamily F_dual.modulus ⊤ le_top u) hnp_ray _).trans_lt hnext
  have hcond_ray : ∀ θ : RayQuotient.Characters F_dual.modulus ⊤,
      ((HeckePrimeRay.twistedFamily F_dual.modulus ⊤ le_top (rawRow u).inverse θ).modulus.absNorm : ℝ) ≤
        Z_dual ^ d_ray := by
    intro θ
    have hc_nat := ProbeRayCharacterFamily.raw_twisted_conductor F_dual.modulus ⊤ le_top u θ
    have hc_real : ((HeckePrimeRay.twistedFamily F_dual.modulus ⊤ le_top (rawRow u).inverse θ).modulus.absNorm : ℝ) ≤
        ((ProbeHighRowFamily.conductorConstant : ℝ) * (F_dual.modulus.absNorm : ℝ)) * rowNorm u := by
      unfold rowNorm; exact_mod_cast hc_nat
    have hZd_UH : Z_dual ^ D_dual.t * U ^ H_free = Z_dual ^ d_ray := by
      have h1 : Z_dual ^ ((2 / 3) * d_outer * H_free) = U ^ H_free := by
        dsimp only [Z_dual]; rw [← Real.rpow_mul hU_pos.le]; congr 1; field_simp [hd_pos.ne']
      dsimp only [d_ray]
      rw [Real.rpow_add hZd_pos, h1, mul_comm]
    exact hc_real.trans ((mul_le_mul hZcond hu_hi (by unfold rowNorm; positivity)
      (Real.rpow_nonneg hZd_pos.le _)).trans_eq hZd_UH)
  have hfreq_ray : |ζ.im| + Z_dual ^ τ_dual / 2 ≤ (3 * i_bin + 2 : ℕ) * Z_dual ^ τ_dual := by
    have h2_le : (2 : ℝ) ≤ (3 * i_bin + 2 : ℕ) := by exact_mod_cast (show 2 ≤ 3 * i_bin + 2 by omega)
    have h5 : (3 : ℝ) / 2 ≤ (3 * i_bin + 2 : ℕ) := by linarith only [h2_le]
    have hZt_pos : 0 < Z_dual ^ τ_dual := Real.rpow_pos_of_pos hZd_pos _
    nlinarith only [h5, hZt_pos, hζ_im]
  have hht_ray : (3 + (3 * i_bin + 2 : ℕ) * Z_dual ^ τ_dual) ^ 2 ≤ (Z_dual ^ d_ray) ^ (200 * D_dual.t) := by
    have hmono : (3 * i_bin + 2 : ℕ) ≤ (3 * n_bins + 2 : ℕ) := by omega
    have hZt_nn : 0 ≤ Z_dual ^ τ_dual := Real.rpow_nonneg hZd_pos.le _
    have h1 : (3 + (3 * i_bin + 2 : ℕ) * Z_dual ^ τ_dual) ^ 2 ≤
        (3 + (3 * n_bins + 2 : ℕ) * Z_dual ^ τ_dual) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hmono) hZt_nn) 3
    have h2 : Z_dual ^ (2 * D_dual.t) ≤ (Z_dual ^ d_ray) ^ (200 * D_dual.t) := by
      rw [← Real.rpow_mul hZd_pos.le]
      have ht0 := D_dual.t_pos
      exact Real.rpow_le_rpow_of_exponent_le hZd1.le (by nlinarith only [hd_ray_lo, ht0])
    exact (h1.trans hZht).trans h2
  rw [canonicalPrimeAmplitude_eq_rayPrimePolynomial_of_gt_nine F_dual.modulus ⊤ F_dual.W
    F_dual.complex_support u hgt9_Zd ζ, ← hscale_eq]
  have hb := hray Z_dual d_ray hZd1.le hd_ray_pos.le hd_ray_hi h2_Zd_d hZτ
    (rawRow u).inverse hnp_ray a i_bin ha_lo ha_hi hmax_ray
    r_j (1 - ζ.re) ζ.im (D_dual.rmin_pos.le.trans hrj_lo) hrj_hi
    (by rw [hζ_re]; norm_num) (by rw [hζ_re]; norm_num)
    hlog_eq hcond_ray hfreq_ray hht_ray
  have hal := hallowZ d_ray r_j ((2 * a - 1) / 2) hd_ray_lo hrj_lo
  have hcap_eq : a - 1 / 2 = (2 * a - 1) / 2 := by ring
  rw [hcap_eq] at hb
  exact hb.trans hal

/-- Eventual pairwise disjointness of `livePrimes F_dual.modulus ⊤ F_dual.W 2 (U ^ (D.ell j / d_outer))`
across `j : Fin D.N` uniformly for `d_outer ∈ [1/2, 5/6]`, using `D.slots_injective` and
`Function.support F_dual.w ⊆ (1, 2)`. -/
lemma dual_livePrimes_disjoint_eventually
    {Δ Δ_dual : ℝ} (D : Parameters.HighData Δ) (D_dual : Parameters.HighData Δ_dual)
    (F_dual : ProbeFinalAssembly.SourceData D_dual) :
    ∃ U_disj : ℝ, 1 < U_disj ∧ ∀ U : ℝ, U_disj ≤ U →
      ∀ {d_outer : ℝ}, 1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
      ((Finset.univ : Finset (Fin D.N)) : Set (Fin D.N)).PairwiseDisjoint
        (fun j => InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2
          (U ^ (D.ell j / d_outer))) := by
  have hev : ∀ᶠ U : ℝ in atTop, ∀ p : Fin D.N × Fin D.N,
      p.1 ≠ p.2 → 2 ≤ U ^ |D.ell p.1 - D.ell p.2| := by
    rw [Filter.eventually_all]
    rintro ⟨j₁, j₂⟩
    by_cases hne : j₁ = j₂
    · subst hne; exact Filter.Eventually.of_forall (fun _ h => (h rfl).elim)
    · have hpos : 0 < |D.ell j₁ - D.ell j₂| :=
        abs_pos.mpr (sub_ne_zero.mpr (D.slots_injective.ne hne))
      exact ((tendsto_rpow_atTop hpos).eventually (eventually_ge_atTop 2)).mono
        (fun _ h _ => h)
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev
  refine ⟨max 2 U₀, lt_of_lt_of_le one_lt_two (le_max_left _ _), ?_⟩
  intro U hU d_outer hd_lo hd_hi j₁ _ j₂ _ hne
  have hU1 : 1 < U := (lt_of_lt_of_le one_lt_two (le_max_left _ _)).trans_le hU
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have hsep : 2 ≤ U ^ (|D.ell j₁ - D.ell j₂| / d_outer) := by
    have h1 := hU₀ U ((le_max_right 2 U₀).trans hU) (j₁, j₂) hne
    have hexp : |D.ell j₁ - D.ell j₂| ≤ |D.ell j₁ - D.ell j₂| / d_outer := by
      rw [le_div_iff₀ hd_pos]
      have habs0 : 0 ≤ |D.ell j₁ - D.ell j₂| := abs_nonneg _
      nlinarith only [habs0, hd_hi]
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hU1.le hexp)
  change Disjoint _ _
  rw [Finset.disjoint_left]
  intro P hP₁ hP₂
  have hw₁ : F_dual.w ((P.absNorm : ℝ) / U ^ (D.ell j₁ / d_outer)) ≠ 0 := by
    have hm : F_dual.W ((P.absNorm : ℝ) / U ^ (D.ell j₁ / d_outer)) ≠ 0 :=
      (Finset.mem_filter.mp hP₁).2
    rw [F_dual.complex_eq] at hm
    exact Complex.ofReal_ne_zero.mp hm
  have hw₂ : F_dual.w ((P.absNorm : ℝ) / U ^ (D.ell j₂ / d_outer)) ≠ 0 := by
    have hm : F_dual.W ((P.absNorm : ℝ) / U ^ (D.ell j₂ / d_outer)) ≠ 0 :=
      (Finset.mem_filter.mp hP₂).2
    rw [F_dual.complex_eq] at hm
    exact Complex.ofReal_ne_zero.mp hm
  have hI₁ := F_dual.support hw₁
  have hI₂ := F_dual.support hw₂
  have hX₁_pos : 0 < U ^ (D.ell j₁ / d_outer) := Real.rpow_pos_of_pos hU_pos _
  have hX₂_pos : 0 < U ^ (D.ell j₂ / d_outer) := Real.rpow_pos_of_pos hU_pos _
  have hN₁_lo : U ^ (D.ell j₁ / d_outer) < (P.absNorm : ℝ) := by
    simpa only [one_mul] using (lt_div_iff₀ hX₁_pos).mp hI₁.1
  have hN₁_hi : (P.absNorm : ℝ) < 2 * U ^ (D.ell j₁ / d_outer) := (div_lt_iff₀ hX₁_pos).mp hI₁.2
  have hN₂_lo : U ^ (D.ell j₂ / d_outer) < (P.absNorm : ℝ) := by
    simpa only [one_mul] using (lt_div_iff₀ hX₂_pos).mp hI₂.1
  have hN₂_hi : (P.absNorm : ℝ) < 2 * U ^ (D.ell j₂ / d_outer) := (div_lt_iff₀ hX₂_pos).mp hI₂.2
  rcases lt_trichotomy (D.ell j₁) (D.ell j₂) with hlt | heq | hgt
  · have habs : |D.ell j₁ - D.ell j₂| = D.ell j₂ - D.ell j₁ := by
      rw [abs_of_neg (sub_neg.mpr hlt)]; ring
    have hmul : 2 * U ^ (D.ell j₁ / d_outer) ≤ U ^ (D.ell j₂ / d_outer) := by
      calc 2 * U ^ (D.ell j₁ / d_outer)
          ≤ U ^ (|D.ell j₁ - D.ell j₂| / d_outer) * U ^ (D.ell j₁ / d_outer) :=
            mul_le_mul_of_nonneg_right hsep hX₁_pos.le
        _ = U ^ (D.ell j₂ / d_outer) := by
            rw [← Real.rpow_add hU_pos, habs]; congr 1; ring
    linarith only [hN₁_hi, hN₂_lo, hmul]
  · exact hne (D.slots_injective heq)
  · have habs : |D.ell j₁ - D.ell j₂| = D.ell j₁ - D.ell j₂ := abs_of_pos (sub_pos.mpr hgt)
    have hmul : 2 * U ^ (D.ell j₂ / d_outer) ≤ U ^ (D.ell j₁ / d_outer) := by
      calc 2 * U ^ (D.ell j₂ / d_outer)
          ≤ U ^ (|D.ell j₁ - D.ell j₂| / d_outer) * U ^ (D.ell j₂ / d_outer) :=
            mul_le_mul_of_nonneg_right hsep hX₂_pos.le
        _ = U ^ (D.ell j₁ / d_outer) := by
            rw [← Real.rpow_add hU_pos, habs]; congr 1; ring
    linarith only [hN₂_hi, hN₁_lo, hmul]

/-- **Case 2 buffered-bin bound (`0 ≤ 2*a - 1 ≤ 11/25` or `z_J + z_coll ≥ z_J_cap(θ)`):**
Combines greedy slot keeping `T_keep ⊆ T'` (`exists_subset_sum_interval`), Stage-0
`deleted_source_energy` at `j = 1` (`shiftedExponent = r`) on `U_H := U ^ H_free` (using `w_one`
when `1/bf ≤ X' < 1`), `dual_ray_prime_bin_supply` on the dropped slots `T' \ T_keep`, and
`stage1_case2_keep_bound` to achieve `1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t`. -/
theorem dual_case2_bin_bound
    {Δ Δ_dual : ℝ} (D : Parameters.HighData Δ) (D_dual : Parameters.HighData Δ_dual)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (wFresh : 𝓢(ℝ, ℂ)) {af bf B_w : ℝ} (haf : 0 < af) (habf : af ≤ bf) (hBw0 : 0 ≤ B_w)
    (hs_w : Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf) (hBw : ∀ y, ‖wFresh y‖ ≤ B_w)
    {τ_dual : ℝ} (hτ_pos : 0 < τ_dual) (hτ_le : 2 * τ_dual ≤ D_dual.t)
    (n_bins : ℕ) :
    ∃ J_c2 : ℕ, ∀ data : RowData, ∃ C_c2 U_c2 : ℝ, 0 < C_c2 ∧ 1 < U_c2 ∧
      ∀ U : ℝ, U_c2 ≤ U →
      ∀ {d_outer r θ ell z_Jv x6 V₀ z_J z_coll X' : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        17 / 25 ≤ r → r ≤ 19 / 26 →
        0 ≤ θ → θ ≤ 1 →
        0 ≤ ell → ell ≤ 3 / 500 →
        0 ≤ z_Jv → z_Jv ≤ ell →
        0 ≤ x6 → 0 ≤ V₀ → 0 ≤ z_J → 0 ≤ z_coll →
      let u_sel := θ * stage1Width r
      let H_th := (1 - θ) * 1 + θ * stage1DualScale r
      let z_rem_th := (1 - θ) * ((1 - r) / 2) + θ * stage1RemWidth r
      let H_free := H_th - 6 * ell - 6 * x6
      let r_unm := r - V₀ - 3 * ell + z_Jv - z_coll
      let z_T_cap := z_rem_th - z_Jv - z_J - z_coll
      max (1 / 10) (r_unm + 10 * D_dual.t) < H_free → H_free ≤ 1 →
      0 < X' → X' ≤ U ^ r_unm →
      ∀ (T' : Finset (Fin D.N)), (∑ j ∈ T', D.ell j / d_outer) ≤ z_T_cap →
      let Z_dual := U ^ (3 / (2 * d_outer))
      ∀ {i_bin : ℕ} {a : ℝ}, 1 ≤ i_bin → i_bin ≤ n_bins → 51 / 100 ≤ a → a ≤ 1 →
        (2 * a - 1 ≤ 11 / 25 ∨
          (2 * a - 1 ≤ 3 / 4 ∧ θ * (25 / 3) * (stage1Line r - (1 - r) / 2) ≤ z_J + z_coll)) →
      ∀ (rows_bin : Finset FreeRow),
        (∀ u ∈ rows_bin, Z_dual ^ (1 / 100 : ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U ^ H_free) →
        (∀ u ∈ rows_bin, detectorMaximum
          (sourceDetectorFamily F_dual.S F_dual.exclusions.prime (deletedBase data).inverse u
            (rayCubeFamily F_dual.modulus ⊤ le_top u))
          (3 * (i_bin + 1 : ℕ) * Z_dual ^ τ_dual) < a + 2 * D_dual.e) →
      ∀ (ζ : ℂ), ζ.re = 17 / 50 → |ζ.im| ≤ Z_dual ^ τ_dual →
      ∀ s : ℝ,
        (∑ u ∈ rows_bin,
          ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
              (childLogTest wFresh s) X' 0 0 *
            ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) ≤
          C_c2 * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_c2) := by
  have hbf_pos : 0 < bf := haf.trans_le habf
  have hcs_conj : HasCompactSupport (fun x : ℝ => star (wFresh x)) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := af) (b := bf)) ?_
    intro x hx; exact hs_w (by simpa using hx)
  have hsm_conj : ContDiff ℝ ∞ (fun x : ℝ => star (wFresh x)) :=
    Complex.conjCLE.contDiff.comp (wFresh.smooth ⊤)
  let wConj : ℝ → ℂ := fun x => star (wFresh x)
  have hs_conj : Function.support wConj ⊆ Set.Icc af bf := by
    intro x hx; rw [Function.mem_support] at hx; exact hs_w (star_ne_zero.mp hx)
  obtain ⟨w_one, a_one, b_one, ha_one, hab_one, _, hs_one, hsm_one, hpol_one⟩ :=
    exists_unit_polynomial_window F_dual
  obtain ⟨deg₁, hdel₁⟩ := deleted_source_energy F_dual wConj af bf haf habf hs_conj hsm_conj
    D_dual.t D_dual.t_pos D.N
  obtain ⟨deg₀, hdel₀⟩ := deleted_source_energy F_dual w_one a_one b_one ha_one hab_one
    hs_one hsm_one D_dual.t D_dual.t_pos D.N
  have hray_all := dual_ray_prime_bin_supply D D_dual emb hemb F_dual hτ_pos hτ_le n_bins
  obtain ⟨U_disj, hU_disj1, hdisj_all⟩ := dual_livePrimes_disjoint_eventually D D_dual F_dual
  let J_c2 : ℕ := max deg₁ deg₀
  refine ⟨J_c2, ?_⟩
  intro data
  obtain ⟨C₁, U₁, hC₁, hU₁, hm₁⟩ := hdel₁ data
  obtain ⟨C₀, U₀, hC₀, hU₀, hm₀⟩ := hdel₀ data
  obtain ⟨U_ray, hU_ray1, hray⟩ := hray_all data
  have hell_min_pos : ∀ j : Fin D.N, 0 < D.ell j / (5 / 6 : ℝ) :=
    fun j => div_pos (D.slots_bounds j).1 (by norm_num)
  have hmod_ev : ∀ᶠ U : ℝ in atTop, ∀ j : Fin D.N,
      ((deletedBase data).modulus.absNorm : ℝ) < U ^ (D.ell j / (5 / 6 : ℝ)) := by
    rw [Filter.eventually_all]
    intro j
    exact (tendsto_rpow_atTop (hell_min_pos j)).eventually (eventually_gt_atTop _)
  obtain ⟨U_mod, hU_mod⟩ := eventually_atTop.mp hmod_ev
  let U_c2 : ℝ := max (max U_ray U_disj) (max U_mod ((max U₁ U₀) ^ (10 : ℝ)))
  have hU_c2_1 : 1 < U_c2 := lt_of_lt_of_le hU_ray1 ((le_max_left _ _).trans (le_max_left _ _))
  let C_unit : ℝ := bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 + 1
  have hCunit_pos : 0 < C_unit := by
    have : 0 ≤ bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 := mul_nonneg hbf_pos.le (sq_nonneg _)
    dsimp only [C_unit]; linarith
  let C_c2 : ℝ := C_unit * (C₁ + C₀ + 1)
  have hCc2_pos : 0 < C_c2 := mul_pos hCunit_pos (by linarith [hC₁, hC₀])
  refine ⟨C_c2, U_c2, hCc2_pos, hU_c2_1, ?_⟩
  intro U hU d_outer r θ ell z_Jv x6 V₀ z_J z_coll X'
    hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hx6 hV0 hzJ0 hzc0
    u_sel H_th z_rem_th H_free r_unm z_T_cap hHf_gt hHf_hi hX' hX'_le
    T' hzT_le Z_dual i_bin a hi_lo hi_hi ha_lo ha_hi hcase rows_bin hrows_norm hnext
    ζ hζ_re hζ_im s
  have hU1 : 1 < U := hU_c2_1.trans_le hU
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have hHf_lo10 : 1 / 10 < H_free := (le_max_left _ _).trans_lt hHf_gt
  have hHf_lo3 : 3 / 100 ≤ H_free := by linarith only [hHf_lo10]
  have hHf_pos : 0 < H_free := by linarith only [hHf_lo10]
  have hchild_supp : ∀ y, childLogTest wFresh s y ≠ 0 → y ≤ bf :=
    fun y hy => (hs_w (fun hz => hy (by simp only [childLogTest, hz, zero_mul]))).2
  have hchild_norm : ∀ y, ‖childLogTest wFresh s y‖ ≤ B_w := by
    intro y; unfold childLogTest; rw [norm_mul, kernelLogPhase_norm, mul_one]; exact hBw y
  by_cases hlt_bf : bf * X' < 1
  · have hsum0 : (∑ u ∈ rows_bin,
        ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      rw [polynomial_eq_zero_of_mul_lt_one _ _ hX' hchild_supp hlt_bf, zero_mul, norm_zero, sq, zero_mul]
    rw [hsum0]
    exact mul_nonneg (mul_nonneg hCc2_pos.le (Real.rpow_nonneg hU_pos.le _)) (by positivity)
  · -- Construct greedy kept subset `T_keep ⊆ T'` with mesh `D_dual.t`.
    let w_slot : Fin D.N → ℝ := fun j => D.ell j / d_outer
    have hw_nn : ∀ j ∈ T', 0 ≤ w_slot j :=
      fun j _ => div_nonneg (D.slots_bounds j).1.le hd_pos.le
    have hw_mesh : ∀ j ∈ T', w_slot j ≤ D_dual.t := by
      intro j _
      dsimp only [w_slot]
      rw [div_le_iff₀ hd_pos]
      have hb_emb := (D_dual.slots_bounds (emb j)).2.2
      have hemb_j := hemb j
      have ht0 := D_dual.t_pos
      have hb_dual : D.ell j ≤ (3 / 400) * D_dual.t := by linarith only [hb_emb, hemb_j]
      nlinarith only [hb_dual, hd_lo, ht0]
    let z_T_act : ℝ := ∑ j ∈ T', w_slot j
    have hzT_act0 : 0 ≤ z_T_act := Finset.sum_nonneg hw_nn
    let r_pos : ℝ := max 0 r_unm
    have hrpos_lt : r_pos + 10 * D_dual.t < H_free := by
      dsimp only [r_pos]
      rcases le_total 0 r_unm with h0 | h0
      · rw [max_eq_right h0]; exact (le_max_right _ _).trans_lt hHf_gt
      · rw [max_eq_left h0]
        have ht1 := D_dual.t_small
        linarith only [hHf_lo10, ht1]
    let b_cap : ℝ := min ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8)
    have hb_cap_gt : 3 * D_dual.t < b_cap := by
      dsimp only [b_cap]
      have ht0 := D_dual.t_pos
      apply lt_min
      · linarith only [hrpos_lt, ht0]
      · have hrpos0 : 0 ≤ r_pos := le_max_left 0 r_unm
        linarith only [hrpos_lt, hrpos0, ht0]
    let cap_act : ℝ := min z_T_act b_cap
    have hT_keep_ex : ∃ T_keep ⊆ T',
        cap_act - 2 * D_dual.t ≤ ∑ j ∈ T_keep, w_slot j ∧
          ∑ j ∈ T_keep, w_slot j < b_cap := by
      have ht0 := D_dual.t_pos
      by_cases hsmall_cap : cap_act ≤ 2 * D_dual.t
      · exact ⟨∅, Finset.empty_subset _, by simp only [Finset.sum_empty]; linarith only [hsmall_cap],
          by simp only [Finset.sum_empty]; linarith only [hb_cap_gt, ht0]⟩
      · have hgt : 2 * D_dual.t < cap_act := not_le.mp hsmall_cap
        have hcap_le_zT : cap_act ≤ z_T_act := min_le_left _ _
        obtain ⟨T_keep, hsub, hlo, hhi⟩ := exists_subset_sum_interval
          (mesh := D_dual.t) (target := cap_act - 2 * D_dual.t) T' w_slot ht0.le
          hw_nn hw_mesh (by linarith only [hgt]) (by linarith only [hcap_le_zT, ht0])
        refine ⟨T_keep, hsub, hlo, ?_⟩
        have hcb : cap_act ≤ b_cap := min_le_right _ _
        linarith only [hhi, hcb, ht0]
    obtain ⟨T_keep, hTk_sub, hTk_lo, hTk_lt⟩ := hT_keep_ex
    let z_keep : ℝ := ∑ j ∈ T_keep, w_slot j
    have hz_keep0 : 0 ≤ z_keep := Finset.sum_nonneg (fun j hj => hw_nn j (hTk_sub hj))
    -- Pointwise bound on dropped slots `T' \ T_keep` via `dual_ray_prime_bin_supply`.
    have hray_u : ∀ u ∈ rows_bin,
        ‖∏ j ∈ T' \ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (U ^ (w_slot j)) ζ‖ ^ 2 ≤
        U ^ (((2 * a - 1) + 2 * D_dual.t) * (z_T_act - z_keep)) := by
      intro u hu
      rw [norm_prod, ← Finset.prod_pow]
      have h1 : ∀ j ∈ T' \ T_keep,
          ‖HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (U ^ (w_slot j)) ζ‖ ^ 2 ≤
          U ^ (((2 * a - 1) + 2 * D_dual.t) * w_slot j) := by
        intro j _
        have hrj := hray U (((le_max_left _ _).trans (le_max_left _ _)).trans hU)
          hd_lo hd_hi hHf_lo3 hHf_hi hi_lo hi_hi ha_lo ha_hi
          u (hrows_norm u hu).1 (hrows_norm u hu).2 (hnext u hu) ζ hζ_re hζ_im j
        have hsq := pow_le_pow_left₀ (norm_nonneg _) hrj 2
        refine hsq.trans_eq ?_
        dsimp only [w_slot]
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Real.rpow_nonneg hU_pos.le _),
          ← Real.rpow_mul hU_pos.le]
        congr 1; ring
      have hsdiff_sum : (∑ j ∈ T' \ T_keep, w_slot j) = z_T_act - z_keep := by
        have hs := Finset.sum_sdiff (f := w_slot) hTk_sub
        dsimp only [z_T_act, z_keep]
        linarith only [hs]
      calc (∏ j ∈ T' \ T_keep, ‖HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (w_slot j)) ζ‖ ^ 2)
          ≤ ∏ j ∈ T' \ T_keep, U ^ (((2 * a - 1) + 2 * D_dual.t) * w_slot j) :=
            Finset.prod_le_prod (fun _ _ => sq_nonneg _) h1
        _ = U ^ (∑ j ∈ T' \ T_keep, ((2 * a - 1) + 2 * D_dual.t) * w_slot j) :=
            (Real.rpow_sum_of_pos hU_pos _ _).symm
        _ = _ := by rw [← Finset.mul_sum, hsdiff_sum]
    -- Bound the kept sum `∑ u ∈ rows_bin, ‖polynomial ... X' * ∏_{j ∈ T_keep} amp‖^2` via `deleted_source_energy` at `j = 1`.
    let U_H : ℝ := U ^ H_free
    have hUH_gt1 : 1 < U_H := Real.one_lt_rpow hU1 hHf_pos
    have hUH_pos : 0 < U_H := zero_lt_one.trans hUH_gt1
    have hUH_ge : max U₁ U₀ ≤ U_H := by
      have h1 : (max U₁ U₀) ^ (10 : ℝ) ≤ U :=
        ((le_max_right _ _).trans (le_max_right _ _)).trans hU
      have h2 : max U₁ U₀ ≤ U ^ (1 / 10 : ℝ) := by
        have hpos_m : 0 < max U₁ U₀ := zero_lt_one.trans (lt_of_lt_of_le hU₁ (le_max_left _ _))
        calc max U₁ U₀ = ((max U₁ U₀) ^ (10 : ℝ)) ^ (1 / 10 : ℝ) := by
              rw [← Real.rpow_mul hpos_m.le]; norm_num
          _ ≤ U ^ (1 / 10 : ℝ) :=
              Real.rpow_le_rpow (Real.rpow_nonneg hpos_m.le _) h1 (by norm_num)
      exact h2.trans (Real.rpow_le_rpow_of_exponent_le hU1.le hHf_lo10.le)
    let ell_H : T_keep → ℝ := fun j => w_slot j.val / H_free
    have hell_H0 : ∀ j : T_keep, 0 ≤ ell_H j :=
      fun j => div_nonneg (hw_nn j.val (hTk_sub j.property)) hHf_pos.le
    have hUH_ell : ∀ j : T_keep, U_H ^ (ell_H j) = U ^ (w_slot j.val) := by
      intro j; dsimp only [U_H, ell_H]; rw [← Real.rpow_mul hU_pos.le, mul_div_cancel₀ _ hHf_pos.ne']
    have hsum_ell_H : (∑ j : T_keep, ell_H j) = z_keep / H_free := by
      dsimp only [ell_H, z_keep]
      rw [← Finset.sum_div]
      exact congrArg (fun x => x / H_free) (Finset.sum_coe_sort T_keep (fun j => w_slot j))
    have hdisj_keep : ((Finset.univ : Finset T_keep) : Set T_keep).PairwiseDisjoint
        (fun j => InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (U_H ^ (ell_H j))) := by
      intro j₁ _ j₂ _ hne
      simp only [hUH_ell]
      exact hdisj_all U (((le_max_right _ _).trans (le_max_left _ _)).trans hU) hd_lo hd_hi
        (Finset.mem_univ j₁.val) (Finset.mem_univ j₂.val) (fun hv => hne (Subtype.ext hv))
    have hlarge_keep : ∀ j : T_keep, ((deletedBase data).modulus.absNorm : ℝ) < U_H ^ (ell_H j) := by
      intro j
      rw [hUH_ell]
      have hm := hU_mod U (((le_max_left _ _).trans (le_max_right _ _)).trans hU) j.val
      have hexp : D.ell j.val / (5 / 6 : ℝ) ≤ w_slot j.val := by
        dsimp only [w_slot]
        exact div_le_div_of_nonneg_left (D.slots_bounds j.val).1.le hd_pos hd_hi
      exact hm.trans_le (Real.rpow_le_rpow_of_exponent_le hU1.le hexp)
    have h1_mem_div : (1 : Ideal O) ∈ idealDivisors (∏ P ∈ excluded data, P) := by
      have hsq := InverseInitialExcludedPolynomial.prime_product_squarefree (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))
      exact (mem_idealDivisors hsq.ne_zero).mpr (one_dvd _)
    have hshift1 (r_H : ℝ) : shiftedExponent data U_H r_H 1 = r_H := by
      unfold shiftedExponent
      rw [map_one Ideal.absNorm, Nat.cast_one, Real.logb_one, sub_zero]
    let rows_O : Finset O := rows_bin.image Subtype.val
    have hrows_O_norm : ∀ x ∈ rows_O, ‖ringComplex x‖ ^ 2 ≤ U_H := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      rw [ringComplex_norm_sq_eq_absNorm_span]
      exact (hrows_norm u hu).2
    have hcard_Tk : Fintype.card T_keep ≤ D.N := by
      rw [Fintype.card_coe]
      exact (Finset.card_le_univ T_keep).trans_eq (Fintype.card_fin D.N)
    have h1s_deg₁ : ((1 + ‖-s‖) ^ deg₁) ^ 2 ≤ (1 + |s|) ^ (2 * J_c2) := by
      rw [norm_neg, Real.norm_eq_abs, ← pow_mul]
      have habs0 := abs_nonneg s
      exact pow_le_pow_right₀ (by linarith only [habs0]) (by dsimp only [J_c2]; omega)
    have h1s_deg₀ : ((1 + ‖(0 : ℝ)‖) ^ deg₀) ^ 2 ≤ (1 + |s|) ^ (2 * J_c2) := by
      simp only [norm_zero, add_zero, one_pow]
      have habs0 := abs_nonneg s
      exact one_le_pow₀ (by linarith only [habs0])
    have hkept_sum :
        (∑ u ∈ rows_bin,
          ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
              (childLogTest wFresh s) X' 0 0 *
            ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (w_slot j)) ζ‖ ^ 2) ≤
        C_c2 * U_H ^ (1 + D_dual.t) * (1 + |s|) ^ (2 * J_c2) := by
      by_cases hX1 : X' < 1
      · have hbfX : 1 ≤ bf * X' := not_lt.mp hlt_bf
        have hpol_u : ∀ u ∈ rows_bin,
            ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
              (childLogTest wFresh s) X' 0 0‖ ^ 2 ≤ C_unit := by
          intro u _
          have hb1 := polynomial_unit_scale_norm_sq_le (targetRow (deletedBase data).inverse u)
            (childLogTest wFresh s) hX' hbf_pos.le hBw0 hchild_supp hchild_norm hbfX hX1.le
          dsimp only [C_unit]; linarith only [hb1]
        have hcap1_0 : (0 : ℝ) + 2 * (∑ j : T_keep, ell_H j) < 1 := by
          rw [zero_add, hsum_ell_H, mul_div_assoc', div_lt_one hHf_pos]
          have hlt1 : z_keep < (H_free - r_pos) / 2 := hTk_lt.trans_le (min_le_left _ _)
          have hrpos0 : 0 ≤ r_pos := le_max_left 0 r_unm
          linarith only [hlt1, hrpos0]
        have hcap2_0 : 2 * (0 : ℝ) + 8 * (∑ j : T_keep, ell_H j) < 3 := by
          rw [mul_zero, zero_add, hsum_ell_H, mul_div_assoc', div_lt_iff₀ hHf_pos]
          have hlt2 : z_keep < (3 * H_free - 2 * r_pos) / 8 := hTk_lt.trans_le (min_le_right _ _)
          have hrpos0 : 0 ≤ r_pos := le_max_left 0 r_unm
          linarith only [hlt2, hrpos0]
        have hdel_val :
            (∑ x ∈ rows_O,
              ‖deletedSelectedSource data F_dual.modulus ⊤ (childLogTest w_one 0) (fun _ => F_dual.W)
                U_H 0 0 0 b_one (fun _ => 2) ell_H (fun _ => ζ) x‖ ^ 2) ≤
            C₀ * U_H ^ (1 + D_dual.t) * ((1 + ‖(0 : ℝ)‖) ^ deg₀) ^ 2 := by
          simpa only [hshift1 0] using hm₀ U_H ((le_max_right U₁ U₀).trans hUH_ge) hcard_Tk
            F_dual.modulus ⊤ ell_H (fun _ => ζ) hell_H0 (fun _ => by rw [hζ_re]; norm_num)
            hdisj_keep hlarge_keep 0 le_rfl hcap1_0 hcap2_0 1 h1_mem_div rows_O hrows_O_norm 0
        have hnorm_id : ∀ u ∈ rows_bin,
            ‖∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (w_slot j)) ζ‖ =
            ‖deletedSelectedSource data F_dual.modulus ⊤ (childLogTest w_one 0) (fun _ => F_dual.W)
              U_H 0 0 0 b_one (fun _ => 2) ell_H (fun _ => ζ) u.val‖ := by
          intro u _
          have hpol1 : HeckeDyadic.polynomial ((data.character ⟨u.val, u.property.1⟩).excludePrimes
              (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)))
              true (childLogTest w_one 0) (U_H ^ (0 : ℝ)) 0 0 = 1 := by
            rw [Real.rpow_zero]; exact hpol_one _
          have hd_init := deleted_physical_slots_norm_initial data ⟨u.val, u.property.1⟩
            F_dual.modulus ⊤ (childLogTest w_one 0) (fun _ : T_keep => F_dual.W)
            U_H 0 0 0 b_one (fun _ => 1) (fun _ => 2) ell_H (fun _ => ζ) hUH_pos
            (fun y hy => (hs_one (fun hz => hy (by simp only [childLogTest, hz, zero_mul]))).2)
            (fun _ => F_dual.complex_support) (fun j => by rw [one_mul]; exact hlarge_keep j)
          rw [hpol1, one_mul] at hd_init
          have hprod_coe : (∏ j : T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U_H ^ (ell_H j)) ζ) =
              ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
                F_dual.W 2 (U ^ (w_slot j)) ζ := by
            simp_rw [hUH_ell]
            exact Finset.prod_coe_sort T_keep
              (fun j => HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val F_dual.W 2 (U ^ (w_slot j)) ζ)
          rwa [hprod_coe] at hd_init
        let f_src0 : O → ℝ := fun x =>
          ‖deletedSelectedSource data F_dual.modulus ⊤ (childLogTest w_one 0) (fun _ => F_dual.W)
            U_H 0 0 0 b_one (fun _ => 2) ell_H (fun _ => ζ) x‖ ^ 2
        have hsum_img : (∑ u ∈ rows_bin, f_src0 u.val) = ∑ x ∈ rows_O, f_src0 x :=
          (Finset.sum_image (f := f_src0) (g := Subtype.val) (fun _ _ _ _ h => Subtype.ext h)).symm
        calc (∑ u ∈ rows_bin,
              ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                  (childLogTest wFresh s) X' 0 0 *
                ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
                  F_dual.W 2 (U ^ (w_slot j)) ζ‖ ^ 2)
            ≤ ∑ u ∈ rows_bin, C_unit * f_src0 u.val := by
              apply Finset.sum_le_sum; intro u hu
              rw [norm_mul, mul_pow, hnorm_id u hu]
              exact mul_le_mul_of_nonneg_right (hpol_u u hu) (sq_nonneg _)
          _ = C_unit * ∑ x ∈ rows_O, f_src0 x := by
              rw [← Finset.mul_sum, hsum_img]
          _ ≤ C_unit * (C₀ * U_H ^ (1 + D_dual.t) * ((1 + ‖(0 : ℝ)‖) ^ deg₀) ^ 2) :=
              mul_le_mul_of_nonneg_left hdel_val hCunit_pos.le
          _ ≤ C_c2 * U_H ^ (1 + D_dual.t) * (1 + |s|) ^ (2 * J_c2) := by
              have hC_le : C_unit * C₀ ≤ C_c2 := by
                dsimp only [C_c2]; nlinarith only [hC₁, hC₀, hCunit_pos]
              calc C_unit * (C₀ * U_H ^ (1 + D_dual.t) * ((1 + ‖(0 : ℝ)‖) ^ deg₀) ^ 2)
                  = (C_unit * C₀) * U_H ^ (1 + D_dual.t) * ((1 + ‖(0 : ℝ)‖) ^ deg₀) ^ 2 := by ring
                _ ≤ C_c2 * U_H ^ (1 + D_dual.t) * (1 + |s|) ^ (2 * J_c2) :=
                    mul_le_mul (mul_le_mul_of_nonneg_right hC_le (Real.rpow_nonneg hUH_pos.le _))
                      h1s_deg₀ (sq_nonneg _) (mul_nonneg hCc2_pos.le (Real.rpow_nonneg hUH_pos.le _))
      · -- Main case `1 ≤ X' ≤ U ^ r_unm`: invoke `deleted_source_energy` on `wConj` at `r_H = log_{U_H} X'`.
        have hX_ge1 : 1 ≤ X' := not_lt.mp hX1
        let r_act : ℝ := Real.logb U X'
        have hract0 : 0 ≤ r_act := Real.logb_nonneg hU1 hX_ge1
        have hract_pos : r_act ≤ r_pos :=
          ((Real.logb_le_iff_le_rpow hU1 hX').mpr hX'_le).trans (le_max_right 0 r_unm)
        let r_H : ℝ := r_act / H_free
        have hrH0 : 0 ≤ r_H := div_nonneg hract0 hHf_pos.le
        have hUH_r : U_H ^ r_H = X' := by
          dsimp only [U_H, r_H]
          rw [← Real.rpow_mul hU_pos.le, mul_div_cancel₀ _ hHf_pos.ne']
          exact Real.rpow_logb hU_pos hU1.ne' hX'
        have hcap1 : r_H + 2 * (∑ j : T_keep, ell_H j) < 1 := by
          rw [hsum_ell_H]
          have hlt1 : z_keep < (H_free - r_pos) / 2 := hTk_lt.trans_le (min_le_left _ _)
          have hsum_num : r_act + 2 * z_keep < H_free := by linarith only [hlt1, hract_pos]
          calc r_act / H_free + 2 * (z_keep / H_free)
              = (r_act + 2 * z_keep) / H_free := by ring
            _ < 1 := (div_lt_one hHf_pos).mpr hsum_num
        have hcap2 : 2 * r_H + 8 * (∑ j : T_keep, ell_H j) < 3 := by
          rw [hsum_ell_H]
          have hlt2 : z_keep < (3 * H_free - 2 * r_pos) / 8 := hTk_lt.trans_le (min_le_right _ _)
          have hsum_num : 2 * r_act + 8 * z_keep < 3 * H_free := by linarith only [hlt2, hract_pos]
          calc 2 * (r_act / H_free) + 8 * (z_keep / H_free)
              = (2 * r_act + 8 * z_keep) / H_free := by ring
            _ < 3 := (div_lt_iff₀ hHf_pos).mpr hsum_num
        have hdel_val :
            (∑ x ∈ rows_O,
              ‖deletedSelectedSource data F_dual.modulus ⊤ (childLogTest wConj (-s)) (fun _ => F_dual.W)
                U_H r_H 0 0 bf (fun _ => 2) ell_H (fun _ => ζ) x‖ ^ 2) ≤
            C₁ * U_H ^ (1 + D_dual.t) * ((1 + ‖-s‖) ^ deg₁) ^ 2 := by
          simpa only [hshift1 r_H] using hm₁ U_H ((le_max_left U₁ U₀).trans hUH_ge) hcard_Tk
            F_dual.modulus ⊤ ell_H (fun _ => ζ) hell_H0 (fun _ => by rw [hζ_re]; norm_num)
            hdisj_keep hlarge_keep r_H hrH0 hcap1 hcap2 1 h1_mem_div rows_O hrows_O_norm (-s)
        have hor_eq : orientedProfile true (childLogTest wFresh s) = childLogTest wConj (-s) := by
          funext x
          unfold orientedProfile childLogTest kernelLogPhase
          rw [if_pos rfl]
          dsimp only [wConj]
          rw [map_mul]
          congr 1
          rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
          congr 1; push_cast; ring
        have hnorm_id : ∀ u ∈ rows_bin,
            ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                (childLogTest wFresh s) X' 0 0 *
              ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
                F_dual.W 2 (U ^ (w_slot j)) ζ‖ =
            ‖deletedSelectedSource data F_dual.modulus ⊤ (childLogTest wConj (-s)) (fun _ => F_dual.W)
              U_H r_H 0 0 bf (fun _ => 2) ell_H (fun _ => ζ) u.val‖ := by
          intro u _
          have hn := norm_of_oriented_coefficients (targetRow (deletedBase data).inverse u)
            ((data.character ⟨u.val, u.property.1⟩).excludePrimes (excluded data)
              (reflectionExcludedPrimes_prime (basePeriod data)))
            true (fun J => by simpa using targetRow_deletedBase_coeff data u J)
            true (childLogTest wFresh s) X' 0 0 hX'
          simp only [orientedFrequency, neg_zero, ite_self, hor_eq, ← hUH_r] at hn
          have hd_init := deleted_physical_slots_norm_initial data ⟨u.val, u.property.1⟩
            F_dual.modulus ⊤ (childLogTest wConj (-s)) (fun _ : T_keep => F_dual.W)
            U_H r_H 0 0 bf (fun _ => 1) (fun _ => 2) ell_H (fun _ => ζ) hUH_pos
            (fun y hy => (hs_conj (fun hz => hy (by simp only [childLogTest, hz, zero_mul]))).2)
            (fun _ => F_dual.complex_support) (fun j => by rw [one_mul]; exact hlarge_keep j)
          have hprod_coe : (∏ j : T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U_H ^ (ell_H j)) ζ) =
              ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
                F_dual.W 2 (U ^ (w_slot j)) ζ := by
            simp_rw [hUH_ell]
            exact Finset.prod_coe_sort T_keep
              (fun j => HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val F_dual.W 2 (U ^ (w_slot j)) ζ)
          rw [norm_mul, ← hUH_r, hn, ← hprod_coe, ← norm_mul, hd_init]
        let f_src1 : O → ℝ := fun x =>
          ‖deletedSelectedSource data F_dual.modulus ⊤ (childLogTest wConj (-s)) (fun _ => F_dual.W)
            U_H r_H 0 0 bf (fun _ => 2) ell_H (fun _ => ζ) x‖ ^ 2
        have hsum_img : (∑ u ∈ rows_bin, f_src1 u.val) = ∑ x ∈ rows_O, f_src1 x :=
          (Finset.sum_image (f := f_src1) (g := Subtype.val) (fun _ _ _ _ h => Subtype.ext h)).symm
        calc (∑ u ∈ rows_bin,
              ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                  (childLogTest wFresh s) X' 0 0 *
                ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
                  F_dual.W 2 (U ^ (w_slot j)) ζ‖ ^ 2)
            = ∑ x ∈ rows_O, f_src1 x := by
              rw [← hsum_img]
              exact Finset.sum_congr rfl (fun u hu => congrArg (fun x : ℝ => x ^ 2) (hnorm_id u hu))
          _ ≤ C₁ * U_H ^ (1 + D_dual.t) * ((1 + ‖-s‖) ^ deg₁) ^ 2 := hdel_val
          _ ≤ C_c2 * U_H ^ (1 + D_dual.t) * (1 + |s|) ^ (2 * J_c2) := by
              have hC_le : C₁ ≤ C_c2 := by
                have hCu1 : 1 ≤ C_unit := by
                  have hnn : 0 ≤ bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 := mul_nonneg hbf_pos.le (sq_nonneg _)
                  dsimp only [C_unit]; linarith only [hnn]
                dsimp only [C_c2]; nlinarith only [hC₁, hC₀, hCu1]
              exact mul_le_mul (mul_le_mul_of_nonneg_right hC_le (Real.rpow_nonneg hUH_pos.le _))
                h1s_deg₁ (sq_nonneg _) (mul_nonneg hCc2_pos.le (Real.rpow_nonneg hUH_pos.le _))
    -- Combine `hkept_sum`, `hray_u`, and `stage1_case2_keep_bound` via `z_J' := z_J + (z_T_cap - z_T_act)`.
    let δ_drop : ℝ := z_T_cap - z_T_act
    have hδ_drop0 : 0 ≤ δ_drop := sub_nonneg.mpr hzT_le
    let z_J' : ℝ := z_J + δ_drop
    have hzJ'0 : 0 ≤ z_J' := add_nonneg hzJ0 hδ_drop0
    have hcase' : 2 * a - 1 ≤ 11 / 25 ∨
        (2 * a - 1 ≤ 3 / 4 ∧ θ * (25 / 3) * (stage1Line r - (1 - r) / 2) ≤ z_J' + z_coll) :=
      hcase.imp id (fun ⟨h1, h2⟩ => ⟨h1, by dsimp only [z_J']; linarith only [h2, hδ_drop0]⟩)
    have hzT'_eq : z_rem_th - z_Jv - z_J' - z_coll = z_T_act := by
      dsimp only [z_J', δ_drop, z_T_cap]; ring
    have hν0 : 0 ≤ 2 * a - 1 := by linarith only [ha_lo]
    have hν1 : 2 * a - 1 ≤ 1 := by linarith only [ha_hi]
    have hexp_c2 := stage1_case2_keep_bound (z_keep := z_keep) (mesh_err := 2 * D_dual.t)
      hr0 hr1 hθ0 hθ1 hell0 hJv0 hJv hx6 hV0 hzJ'0 hzc0 hν0 hcase'
      (show 0 ≤ z_rem_th - z_Jv - z_J' - z_coll by rw [hzT'_eq]; exact hzT_act0)
      (show min (z_rem_th - z_Jv - z_J' - z_coll)
          (min ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8)) - 2 * D_dual.t ≤ z_keep by
        rw [hzT'_eq]; exact hTk_lo)
    rw [hzT'_eq] at hexp_c2
    have hdrop_le1 : z_T_act - z_keep ≤ 1 := by
      have h1 : z_T_act ≤ (1 / 6 : ℝ) / d_outer := by
        dsimp only [z_T_act, w_slot]
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right
          ((Finset.sum_le_univ_sum_of_nonneg (fun j => (D.slots_bounds j).1.le)).trans_eq D.slots_sum)
          hd_pos.le
      have h2 : (1 / 6 : ℝ) / d_outer ≤ 1 / 3 := (div_le_iff₀ hd_pos).mpr (by linarith only [hd_lo])
      linarith only [h1, h2, hz_keep0]
    have hexp_tot : H_free * (1 + D_dual.t) + ((2 * a - 1) + 2 * D_dual.t) * (z_T_act - z_keep) ≤
        1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t := by
      have ht0 := D_dual.t_pos
      have h1 : H_free * D_dual.t ≤ D_dual.t := mul_le_of_le_one_left ht0.le hHf_hi
      have h2 : 2 * D_dual.t * (z_T_act - z_keep) ≤ 2 * D_dual.t :=
        mul_le_of_le_one_right (by linarith only [ht0]) hdrop_le1
      have h3 : (2 * a - 1) * (2 * D_dual.t) ≤ 2 * D_dual.t :=
        mul_le_of_le_one_left (by linarith only [ht0]) hν1
      have hlin1 : H_free * (1 + D_dual.t) = H_free + H_free * D_dual.t := by ring
      have hlin2 : ((2 * a - 1) + 2 * D_dual.t) * (z_T_act - z_keep) =
          (2 * a - 1) * (z_T_act - z_keep) + 2 * D_dual.t * (z_T_act - z_keep) := by ring
      dsimp only [u_sel, H_free, H_th] at hexp_c2 hlin1 ⊢
      linarith only [hexp_c2, h1, h2, h3, hlin1, hlin2, ht0]
    have hprod_split : ∀ u : FreeRow,
        (∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (U ^ (w_slot j)) ζ) =
        (∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (U ^ (w_slot j)) ζ) *
        (∏ j ∈ T' \ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (U ^ (w_slot j)) ζ) := by
      intro u
      rw [mul_comm, Finset.prod_sdiff hTk_sub]
    calc
      (∑ u ∈ rows_bin,
        ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (U ^ (w_slot j)) ζ‖ ^ 2)
        ≤ ∑ u ∈ rows_bin,
            ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                (childLogTest wFresh s) X' 0 0 *
              ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
                F_dual.W 2 (U ^ (w_slot j)) ζ‖ ^ 2 *
            U ^ (((2 * a - 1) + 2 * D_dual.t) * (z_T_act - z_keep)) := by
          apply Finset.sum_le_sum; intro u hu
          rw [hprod_split u, ← mul_assoc, norm_mul, mul_pow]
          exact mul_le_mul_of_nonneg_left (hray_u u hu) (sq_nonneg _)
      _ = (∑ u ∈ rows_bin,
            ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                (childLogTest wFresh s) X' 0 0 *
              ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
                F_dual.W 2 (U ^ (w_slot j)) ζ‖ ^ 2) *
          U ^ (((2 * a - 1) + 2 * D_dual.t) * (z_T_act - z_keep)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (C_c2 * U_H ^ (1 + D_dual.t) * (1 + |s|) ^ (2 * J_c2)) *
            U ^ (((2 * a - 1) + 2 * D_dual.t) * (z_T_act - z_keep)) :=
          mul_le_mul_of_nonneg_right hkept_sum (Real.rpow_nonneg hU_pos.le _)
      _ = C_c2 * (U ^ (H_free * (1 + D_dual.t)) *
            U ^ (((2 * a - 1) + 2 * D_dual.t) * (z_T_act - z_keep))) *
          (1 + |s|) ^ (2 * J_c2) := by
          dsimp only [U_H]; rw [← Real.rpow_mul hU_pos.le]; ring
      _ ≤ C_c2 * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_c2) := by
          rw [← Real.rpow_add hU_pos]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1.le hexp_tot) hCc2_pos.le)
            (by positivity)

/-- Pointwise buffered `HeckeDyadic.polynomial` bound in Case 3 (`1 ≤ bf * X'` and `X' ≤ U ^ r_unm`),
isolated over polymorphic `D_dual : HighData Δ_dual` via `polynomial_norm_sq_le_excludePrimes_sum`,
`buffered_polynomial_bound`, and `target_complexity_power_bound`. -/
theorem dual_case3_pointwise_polynomial_bound
    {Δ_dual : ℝ} (D_dual : Parameters.HighData Δ_dual)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (wFresh : 𝓢(ℝ, ℂ)) {af bf B_w : ℝ} (haf : 0 < af) (habf : af ≤ bf) (hBw0 : 0 ≤ B_w)
    (hs_w : Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf) (hBw : ∀ y, ‖wFresh y‖ ≤ B_w)
    {τ_dual : ℝ} (hτ_pos : 0 < τ_dual) (hτ_le : 2 * τ_dual ≤ D_dual.t)
    (n_bins : ℕ) :
    ∃ J_c3 : ℕ, ∀ data : RowData, ∃ C_pol U_pol : ℝ, 0 < C_pol ∧ 1 < U_pol ∧
      ∀ U : ℝ, U_pol ≤ U →
      ∀ {d_outer H_free r_unm X' : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        H_free ≤ 1 → -(1 / 10000 : ℝ) ≤ r_unm → r_unm ≤ 1 →
        0 < X' → X' ≤ U ^ r_unm →
      let Z_dual := U ^ (3 / (2 * d_outer))
      ∀ {i_bin : ℕ} {a : ℝ}, 1 ≤ i_bin → i_bin ≤ n_bins →
        51 / 100 ≤ a → a ≤ 1 →
      ∀ u : FreeRow, Z_dual ^ (1 / 100 : ℝ) ≤ rowNorm u → rowNorm u ≤ U ^ H_free →
        detectorMaximum
          (sourceDetectorFamily F_dual.S F_dual.exclusions.prime (deletedBase data).inverse u
            (rayCubeFamily F_dual.modulus ⊤ le_top u))
          (3 * (i_bin + 1 : ℕ) * Z_dual ^ τ_dual) < a + 2 * D_dual.e →
      ∀ s : ℝ,
        ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
          (childLogTest wFresh s) X' 0 0‖ ^ 2 ≤
          C_pol * U ^ ((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000) *
            (1 + |s|) ^ (2 * J_c3) := by
  letI : Fintype (RayQuotient.Characters F_dual.modulus ⊤) := Fintype.ofFinite _
  have hbf_pos : 0 < bf := haf.trans_le habf
  obtain ⟨C_buf, hC_buf, hbuf⟩ :=
    HeckeDyadic.buffered_polynomial_bound D_dual.e D_dual.t D_dual.e_pos D_dual.e_small D_dual.t_pos
  let n_rect : ℕ := ⌈(4 : ℝ) / τ_dual⌉₊ + 2
  obtain ⟨C_m2, hC_m2, hm2⟩ :=
    mellin_childLogTest_strip_decay wFresh haf hs_w (wFresh.smooth ⊤) 0 2 2
  obtain ⟨C_mn, hC_mn, hmn⟩ :=
    mellin_childLogTest_strip_decay wFresh haf hs_w (wFresh.smooth ⊤) 0 2 (n_rect + 2)
  let J_c3 : ℕ := n_rect + 2
  refine ⟨J_c3, ?_⟩
  intro data
  let η_base := (deletedBase data).inverse
  have hnp_ev := freeRow_nonprincipal_eventually F_dual.modulus ⊤ le_top
    F_dual.S F_dual.exclusions.prime η_base (1 / 100) (by norm_num)
  have hZ_extra : ∀ᶠ Z : ℝ in atTop,
      2 < Z ^ τ_dual ∧
      (3 + (3 * n_bins + 2 : ℕ) * Z ^ τ_dual) ≤ Z ^ D_dual.t := by
    have h1 : ∀ᶠ Z : ℝ in atTop, 2 < Z ^ τ_dual :=
      (tendsto_rpow_atTop hτ_pos).eventually (eventually_gt_atTop 2)
    have h2 : ∀ᶠ Z : ℝ in atTop, (3 + (3 * n_bins + 2 : ℕ) : ℝ) ≤ Z ^ (D_dual.t - τ_dual) :=
      (tendsto_rpow_atTop (by linarith [D_dual.t_pos])).eventually (eventually_ge_atTop _)
    filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with Z hz1 hz2 hz_ge1
    have hZp : 0 < Z := zero_lt_one.trans_le hz_ge1
    have hZt1 : 1 ≤ Z ^ τ_dual := Real.one_le_rpow hz_ge1 hτ_pos.le
    refine ⟨hz1, ?_⟩
    calc (3 + (3 * n_bins + 2 : ℕ) * Z ^ τ_dual)
        ≤ (3 + (3 * n_bins + 2 : ℕ) : ℝ) * Z ^ τ_dual := by nlinarith
      _ ≤ Z ^ (D_dual.t - τ_dual) * Z ^ τ_dual :=
          mul_le_mul_of_nonneg_right hz2 (Real.rpow_nonneg hZp.le _)
      _ = Z ^ D_dual.t := by rw [← Real.rpow_add hZp]; congr 1; ring
  obtain ⟨Z_np, hZ_np⟩ := eventually_atTop.mp (hnp_ev.and hZ_extra)
  let U_pol : ℝ := max 2 Z_np
  have hU_pol1 : 1 < U_pol := lt_of_lt_of_le one_lt_two (le_max_left _ _)
  let D_excl := idealDivisors F_dual.modulus
  let C_excl : ℝ := (D_excl.card : ℝ) ^ 2 + 1
  have hCexcl_pos : 0 < C_excl := by
    have : 0 ≤ (D_excl.card : ℝ) ^ 2 := sq_nonneg _
    dsimp only [C_excl]; linarith
  let C_S_cond : ℝ := C_buf *
    (2 * (ProbeRowRadicalConductor.fixedConductorConstant F_dual.S : ℝ) ^ 2) ^ D_dual.t *
    (η_base.modulus.absNorm : ℝ) ^ (2 * D_dual.t)
  have hCS_nn : 0 ≤ C_S_cond :=
    mul_nonneg (mul_nonneg hC_buf.le (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  let M_coef : ℝ := C_m2 * (C_S_cond + 1) + 4 * C_mn * (C_S_cond + 1) +
    C_mn * |HeckeReciprocalBound.bound 2| + 1
  have hMcoef_pos : 0 < M_coef := by
    have : 0 ≤ C_mn * |HeckeReciprocalBound.bound 2| := mul_nonneg hC_mn.le (abs_nonneg _)
    dsimp only [M_coef]; nlinarith [hC_m2, hC_mn, hCS_nn]
  let C_pol_1 : ℝ := bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 + M_coef ^ 2
  have hCpol1_pos : 0 < C_pol_1 := by
    have : 0 ≤ bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 := mul_nonneg hbf_pos.le (sq_nonneg _)
    dsimp only [C_pol_1]; nlinarith [sq_pos_of_pos hMcoef_pos]
  let C_pol : ℝ := C_excl * C_pol_1
  refine ⟨C_pol, U_pol, mul_pos hCexcl_pos hCpol1_pos, hU_pol1, ?_⟩
  intro U hU d_outer H_free r_unm X' hd_lo hd_hi hHf_hi hrunm_lo hrunm1 hX' hX'_le
    Z_dual i_bin a hi_lo hi_hi ha_lo ha_hi u hu_lo hu_hi hnext s
  have hU1 : 1 < U := hU_pol1.trans_le hU
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have hexp_Zd : 1 ≤ 3 / (2 * d_outer) := (one_le_div (by positivity)).mpr (by linarith only [hd_hi])
  have hZd_ge_U : U ≤ Z_dual :=
    (Real.rpow_one U).symm.trans_le (Real.rpow_le_rpow_of_exponent_le hU1.le hexp_Zd)
  have hZd_np : Z_np ≤ Z_dual := ((le_max_right 2 Z_np).trans hU).trans hZd_ge_U
  obtain ⟨hnpZ, hZd_τ2, hZd_ht⟩ := hZ_np Z_dual hZd_np
  have hZd1 : 1 < Z_dual := hU1.trans_le hZd_ge_U
  have hZd_pos : 0 < Z_dual := zero_lt_one.trans hZd1
  have hchild_supp : ∀ y, childLogTest wFresh s y ≠ 0 → y ≤ bf :=
    fun y hy => (hs_w (fun hz => hy (by simp only [childLogTest, hz, zero_mul]))).2
  have hchild_supp_Icc : Function.support (childLogTest wFresh s) ⊆ Set.Icc af bf :=
    fun y hy => hs_w (fun hz => hy (by simp only [childLogTest, hz, zero_mul]))
  have hchild_sm : ContDiff ℝ ∞ (childLogTest wFresh s) :=
    InverseInitialOriginalHeight.child_smooth wFresh af bf haf hs_w (wFresh.smooth ⊤) s
  have hchild_norm : ∀ y, ‖childLogTest wFresh s y‖ ≤ B_w := by
    intro y; unfold childLogTest; rw [norm_mul, kernelLogPhase_norm, mul_one]; exact hBw y
  have h1s_J : 1 ≤ (1 + |s|) ^ (2 * J_c3) := by
    have habs0 := abs_nonneg s
    exact one_le_pow₀ (by linarith only [habs0])
  let fam_u := sourceDetectorFamily F_dual.S F_dual.exclusions.prime η_base u
    (rayCubeFamily F_dual.modulus ⊤ le_top u)
  have hnp_u : ∀ k_lbl, (fam_u k_lbl).residue ≠ 1 := hnpZ u hu_lo
  have hmax_u : HeckeDetectorZeros.zeroMaximum fam_u hnp_u (3 * (i_bin + 1 : ℕ) * Z_dual ^ τ_dual) <
      a + 2 * D_dual.e :=
    (zeroMaximum_le_detectorMaximum fam_u hnp_u _).trans_lt hnext
  have hdecomp := polynomial_norm_sq_le_excludePrimes_sum (targetRow η_base u)
    F_dual.S F_dual.exclusions.prime (childLogTest wFresh s) hX' hchild_supp
  change ‖HeckeDyadic.polynomial (targetRow η_base u) true (childLogTest wFresh s) X' 0 0‖ ^ 2 ≤
    (D_excl.card : ℝ) * ∑ j_ex ∈ D_excl,
      ‖HeckeDyadic.polynomial (fam_u (Sum.inl false)) true (childLogTest wFresh s)
        (X' / (j_ex.absNorm : ℝ)) 0 0‖ ^ 2 at hdecomp
  have he_pos := D_dual.e_pos
  have he_small := D_dual.e_small
  have ht_pos := D_dual.t_pos
  have ht_small := D_dual.t_small
  have hj_bound : ∀ j_ex ∈ D_excl,
      ‖HeckeDyadic.polynomial (fam_u (Sum.inl false)) true (childLogTest wFresh s)
        (X' / (j_ex.absNorm : ℝ)) 0 0‖ ^ 2 ≤
      C_pol_1 * U ^ ((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000) *
        (1 + |s|) ^ (2 * J_c3) := by
    intro j_ex hj_ex
    let X'' := X' / (j_ex.absNorm : ℝ)
    have hj_ge1 : 1 ≤ (j_ex.absNorm : ℝ) := by
      have hj0 : j_ex ≠ 0 := ne_zero_of_dvd_ne_zero (NeZero.ne F_dual.modulus)
        ((mem_idealDivisors (NeZero.ne F_dual.modulus)).mp hj_ex)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
    have hX''_pos : 0 < X'' := div_pos hX' (zero_lt_one.trans_le hj_ge1)
    have hX''_le : X'' ≤ U ^ r_unm := (div_le_self hX'.le hj_ge1).trans hX'_le
    have h1_le_Uexp : 1 ≤ U ^ ((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000) := by
      apply Real.one_le_rpow hU1.le
      have h1 : -(1 / 10000 : ℝ) ≤ (2 * a - 1) * r_unm := by
        rcases le_total 0 r_unm with hrp | hrn
        · have hnn := mul_nonneg (show 0 ≤ 2 * a - 1 by linarith only [ha_lo]) hrp
          linarith only [hnn]
        · have hnp := mul_le_mul_of_nonpos_right (show 2 * a - 1 ≤ 1 by linarith only [ha_hi]) hrn
          linarith only [hnp, hrunm_lo]
      linarith only [h1, he_pos, ht_pos]
    by_cases hlt'' : bf * X'' < 1
    · rw [polynomial_eq_zero_of_mul_lt_one _ _ hX''_pos hchild_supp hlt'', norm_zero, sq, zero_mul]
      exact mul_nonneg (mul_nonneg hCpol1_pos.le (Real.rpow_nonneg hU_pos.le _)) (by positivity)
    · by_cases hX''1 : X'' < 1
      · have hbfX'' : 1 ≤ bf * X'' := not_lt.mp hlt''
        have h2 : ‖HeckeDyadic.polynomial (fam_u (Sum.inl false)) true (childLogTest wFresh s) X'' 0 0‖ ^ 2 ≤
            C_pol_1 := by
          have hb1 := polynomial_unit_scale_norm_sq_le (fam_u (Sum.inl false))
            (childLogTest wFresh s) hX''_pos hbf_pos.le hBw0 hchild_supp hchild_norm hbfX'' hX''1.le
          have hsqM := sq_nonneg M_coef
          dsimp only [C_pol_1]; linarith only [hb1, hsqM]
        calc _ ≤ C_pol_1 * 1 * 1 := by rw [mul_one, mul_one]; exact h2
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h1_le_Uexp hCpol1_pos.le) h1s_J
              zero_le_one (mul_nonneg hCpol1_pos.le (Real.rpow_nonneg hU_pos.le _))
      · have hX''_ge1 : 1 ≤ X'' := not_lt.mp hX''1
        let T_dual := Z_dual ^ τ_dual
        have hT_pos : 0 < T_dual := Real.rpow_pos_of_pos hZd_pos _
        have hfreq0 : |(0 : ℝ)| + T_dual ≤ (3 * i_bin + 2 : ℕ) * T_dual := by
          rw [abs_zero, zero_add]
          have h1_le : (1 : ℝ) ≤ (3 * i_bin + 2 : ℕ) := by exact_mod_cast (show 1 ≤ 3 * i_bin + 2 by omega)
          exact le_mul_of_one_le_left hT_pos.le h1_le
        have hm2_line : ∀ t : ℝ,
            (1 + |t|) ^ 2 * ‖mellin (childLogTest wFresh s) (((a + 6 * D_dual.e - 0 : ℝ) : ℂ) + t * Complex.I)‖ ≤
              C_m2 * (1 + |s|) ^ 2 :=
          fun t => hm2 s (a + 6 * D_dual.e - 0) ⟨by linarith only [ha_lo, he_pos], by linarith only [ha_hi, he_small]⟩ t
        have hmn_strip : ∀ x ∈ Set.Icc (a + 6 * D_dual.e - 0) (2 - 0), ∀ t : ℝ,
            (1 + |t|) ^ (n_rect + 2) * ‖mellin (childLogTest wFresh s) ((x : ℂ) + t * Complex.I)‖ ≤
              C_mn * (1 + |s|) ^ (n_rect + 2) :=
          fun x hx t => hmn s x ⟨by linarith only [hx.1, ha_lo, he_pos], by linarith only [hx.2]⟩ t
        have hb_pol := hbuf fam_u hnp_u T_dual a i_bin hZd_τ2 ha_lo ha_hi hmax_u
          (Sum.inl false) true (childLogTest wFresh s) af bf haf hchild_supp_Icc hchild_sm
          X'' 0 0 T_dual (C_m2 * (1 + |s|) ^ 2) (C_mn * (1 + |s|) ^ (n_rect + 2)) n_rect
          hX''_ge1 hT_pos.le hfreq0 (by positivity) (by positivity) hm2_line hmn_strip
        let H_ht := (3 * i_bin + 2 : ℕ) * T_dual
        have hK_le : C_buf * (HeckeReciprocalGrowth.presentationComplexity (fam_u (Sum.inl false)) H_ht) ^ D_dual.t ≤
            (C_S_cond + 1) * U ^ (8 * D_dual.t) := by
          have htcp := ProbeHighRowFamily.target_complexity_power_bound F_dual.S F_dual.exclusions.prime
            η_base u H_ht D_dual.t (by positivity) ht_pos.le
          have hu_le_U : rowNorm u ^ (2 * D_dual.t) ≤ U ^ (2 * D_dual.t) :=
            Real.rpow_le_rpow (by unfold rowNorm; positivity)
              (hu_hi.trans ((Real.rpow_le_rpow_of_exponent_le hU1.le hHf_hi).trans_eq (Real.rpow_one U)))
              (by linarith only [ht_pos])
          have hht_le_U : (3 + H_ht) ^ (2 * D_dual.t) ≤ U ^ (6 * D_dual.t) := by
            have hmono : (3 * i_bin + 2 : ℕ) ≤ (3 * n_bins + 2 : ℕ) := by omega
            have h1 : 3 + H_ht ≤ Z_dual ^ D_dual.t :=
              (add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hmono) hT_pos.le) 3).trans hZd_ht
            have hZd_U3 : Z_dual ≤ U ^ (3 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hU1.le ((div_le_iff₀ (by positivity)).mpr (by linarith only [hd_lo]))
            have h2 : 3 + H_ht ≤ U ^ (3 * D_dual.t) :=
              h1.trans ((Real.rpow_le_rpow hZd_pos.le hZd_U3 ht_pos.le).trans_eq
                (by rw [← Real.rpow_mul hU_pos.le]))
            have h3_ge1 : (1 : ℝ) ≤ 3 + H_ht := by
              have hnn : 0 ≤ H_ht := by dsimp only [H_ht]; positivity
              linarith only [hnn]
            exact (Real.rpow_le_rpow_of_exponent_le h3_ge1 (show 2 * D_dual.t ≤ 1 by linarith only [ht_small])).trans
              ((Real.rpow_one _).trans_le (h2.trans (Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [ht_pos]))))
          calc C_buf * (HeckeReciprocalGrowth.presentationComplexity (fam_u (Sum.inl false)) H_ht) ^ D_dual.t
              ≤ C_buf * ((2 * (ProbeRowRadicalConductor.fixedConductorConstant F_dual.S : ℝ) ^ 2) ^ D_dual.t *
                  (η_base.modulus.absNorm : ℝ) ^ (2 * D_dual.t) *
                  rowNorm u ^ (2 * D_dual.t) * (3 + H_ht) ^ (2 * D_dual.t)) :=
                mul_le_mul_of_nonneg_left htcp hC_buf.le
            _ = C_S_cond * (rowNorm u ^ (2 * D_dual.t) * (3 + H_ht) ^ (2 * D_dual.t)) := by
                dsimp only [C_S_cond]; ring
            _ ≤ (C_S_cond + 1) * (U ^ (2 * D_dual.t) * U ^ (6 * D_dual.t)) :=
                mul_le_mul (by linarith only [hCS_nn])
                  (mul_le_mul hu_le_U hht_le_U
                    (Real.rpow_nonneg (by dsimp only [H_ht]; positivity) _)
                    (Real.rpow_nonneg hU_pos.le _))
                  (mul_nonneg (Real.rpow_nonneg (by unfold rowNorm; positivity) _)
                    (Real.rpow_nonneg (by dsimp only [H_ht]; positivity) _))
                  (by linarith only [hCS_nn])
            _ = (C_S_cond + 1) * U ^ (8 * D_dual.t) := by
                rw [← Real.rpow_add hU_pos]; congr 2; ring
        have htail_U : (X'') ^ (3 / 2 : ℝ) / (1 + T_dual) ^ n_rect ≤ U ^ (-2 : ℝ) := by
          have hX''_U : X'' ≤ U := hX''_le.trans ((Real.rpow_le_rpow_of_exponent_le hU1.le hrunm1).trans_eq (Real.rpow_one U))
          have hX''_32 : (X'') ^ (3 / 2 : ℝ) ≤ U ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow hX''_pos.le hX''_U (by norm_num)
          have hU_τ : U ^ τ_dual ≤ 1 + T_dual := by
            have h1 : U ^ τ_dual ≤ T_dual := Real.rpow_le_rpow hU_pos.le hZd_ge_U hτ_pos.le
            linarith only [h1]
          have hpow_T : U ^ (4 : ℝ) ≤ (1 + T_dual) ^ n_rect := by
            have hnr_ge : 4 ≤ τ_dual * (n_rect : ℝ) := by
              have h1 : (4 : ℝ) / τ_dual ≤ (⌈(4 : ℝ) / τ_dual⌉₊ : ℝ) := Nat.le_ceil _
              have h2 : (⌈(4 : ℝ) / τ_dual⌉₊ : ℝ) ≤ (n_rect : ℝ) := by
                dsimp only [n_rect]; exact_mod_cast Nat.le_add_right _ 2
              have h3 := (div_le_iff₀ hτ_pos).mp (h1.trans h2)
              linarith only [h3]
            calc U ^ (4 : ℝ) ≤ U ^ (τ_dual * (n_rect : ℝ)) :=
                  Real.rpow_le_rpow_of_exponent_le hU1.le hnr_ge
              _ = (U ^ τ_dual) ^ n_rect := by rw [Real.rpow_mul hU_pos.le, Real.rpow_natCast]
              _ ≤ (1 + T_dual) ^ n_rect := pow_le_pow_left₀ (Real.rpow_nonneg hU_pos.le _) hU_τ n_rect
          calc (X'') ^ (3 / 2 : ℝ) / (1 + T_dual) ^ n_rect
              ≤ U ^ (3 / 2 : ℝ) / U ^ (4 : ℝ) :=
                div_le_div₀ (Real.rpow_nonneg hU_pos.le _) hX''_32 (Real.rpow_pos_of_pos hU_pos _) hpow_T
            _ = U ^ ((3 / 2 : ℝ) - 4) := (Real.rpow_sub hU_pos _ _).symm
            _ ≤ U ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hU1.le (by norm_num)
        have hmain_exp : (X'') ^ (a + 6 * D_dual.e - 1 / 2) * U ^ (8 * D_dual.t) ≤
            U ^ (((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t) / 2) := by
          have hpos_a : 0 ≤ a + 6 * D_dual.e - 1 / 2 := by linarith only [ha_lo, he_pos]
          calc (X'') ^ (a + 6 * D_dual.e - 1 / 2) * U ^ (8 * D_dual.t)
              ≤ (U ^ r_unm) ^ (a + 6 * D_dual.e - 1 / 2) * U ^ (8 * D_dual.t) :=
                mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hX''_pos.le hX''_le hpos_a)
                  (Real.rpow_nonneg hU_pos.le _)
            _ = U ^ (r_unm * (a + 6 * D_dual.e - 1 / 2) + 8 * D_dual.t) := by
                rw [← Real.rpow_mul hU_pos.le, ← Real.rpow_add hU_pos]
            _ ≤ _ := by
                apply Real.rpow_le_rpow_of_exponent_le hU1.le
                have hr_e : r_unm * (6 * D_dual.e) ≤ 6 * D_dual.e :=
                  mul_le_of_le_one_left (by linarith only [he_pos]) hrunm1
                have hlin : r_unm * (a + 6 * D_dual.e - 1 / 2) =
                    (2 * a - 1) * r_unm / 2 + r_unm * (6 * D_dual.e) := by ring
                linarith only [hlin, hr_e, ht_pos]
        have htail_exp : U ^ (-2 : ℝ) * U ^ (8 * D_dual.t) ≤
            U ^ (((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t) / 2) := by
          rw [← Real.rpow_add hU_pos]
          apply Real.rpow_le_rpow_of_exponent_le hU1.le
          have hm1 : -1 ≤ (2 * a - 1) * r_unm := by
            rcases le_total 0 r_unm with hp | hn
            · have hnn := mul_nonneg (show 0 ≤ 2 * a - 1 by linarith only [ha_lo]) hp
              linarith only [hnn]
            · have hnp := mul_le_mul_of_nonpos_right (show 2 * a - 1 ≤ 1 by linarith only [ha_hi]) hn
              linarith only [hnp, hrunm_lo]
          linarith only [hm1, ht_pos, he_pos]
        have hnorm_1 : ‖HeckeDyadic.polynomial (fam_u (Sum.inl false)) true (childLogTest wFresh s) X'' 0 0‖ ≤
            M_coef * U ^ (((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t) / 2) *
              (1 + |s|) ^ J_c3 := by
          have habs0 := abs_nonneg s
          have h1s_2 : (1 + |s|) ^ 2 ≤ (1 + |s|) ^ J_c3 :=
            pow_le_pow_right₀ (by linarith only [habs0]) (by dsimp only [J_c3, n_rect]; omega)
          have h2a_abs : |2 - a - 6 * D_dual.e| ≤ 2 :=
            abs_le.mpr ⟨by linarith only [ha_hi, he_small], by linarith only [ha_lo, he_pos]⟩
          have hpi_pos : 0 < Real.pi := Real.pi_pos
          let U_half := U ^ (((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t) / 2)
          let S_pow := (1 + |s|) ^ J_c3
          have hUh_pos : 0 < U_half := Real.rpow_pos_of_pos hU_pos _
          have hSp_pos : 0 < S_pow := by dsimp only [S_pow]; positivity
          let K_act := C_buf * (HeckeReciprocalGrowth.presentationComplexity (fam_u (Sum.inl false)) H_ht) ^ D_dual.t
          have hK_nn : 0 ≤ K_act := mul_nonneg hC_buf.le (Real.rpow_nonneg (by
            unfold HeckeReciprocalGrowth.presentationComplexity HeckeLogarithmic.complexity; positivity) _)
          have ht1 : C_m2 * (1 + |s|) ^ 2 * (X'') ^ (a + 6 * D_dual.e - 1 / 2) * K_act * Real.pi ≤
              C_m2 * (C_S_cond + 1) * U_half * S_pow * (2 * Real.pi) := by
            have hp1 : (X'') ^ (a + 6 * D_dual.e - 1 / 2) * K_act ≤ (C_S_cond + 1) * U_half := by
              calc (X'') ^ (a + 6 * D_dual.e - 1 / 2) * K_act
                  ≤ (X'') ^ (a + 6 * D_dual.e - 1 / 2) * ((C_S_cond + 1) * U ^ (8 * D_dual.t)) :=
                    mul_le_mul_of_nonneg_left hK_le (Real.rpow_nonneg hX''_pos.le _)
                _ = (C_S_cond + 1) * ((X'') ^ (a + 6 * D_dual.e - 1 / 2) * U ^ (8 * D_dual.t)) := by ring
                _ ≤ (C_S_cond + 1) * U_half := mul_le_mul_of_nonneg_left hmain_exp (by linarith only [hCS_nn])
            have hp2 : C_m2 * (1 + |s|) ^ 2 ≤ C_m2 * S_pow := mul_le_mul_of_nonneg_left h1s_2 hC_m2.le
            have hp3 := mul_le_mul hp2 hp1 (mul_nonneg (Real.rpow_nonneg hX''_pos.le _) hK_nn)
              (mul_nonneg hC_m2.le hSp_pos.le)
            calc C_m2 * (1 + |s|) ^ 2 * (X'') ^ (a + 6 * D_dual.e - 1 / 2) * K_act * Real.pi
                = ((C_m2 * (1 + |s|) ^ 2) * ((X'') ^ (a + 6 * D_dual.e - 1 / 2) * K_act)) * Real.pi := by ring
              _ ≤ ((C_m2 * S_pow) * ((C_S_cond + 1) * U_half)) * (2 * Real.pi) :=
                  mul_le_mul hp3 (by linarith only [hpi_pos]) hpi_pos.le
                    (mul_nonneg (mul_nonneg hC_m2.le hSp_pos.le) (mul_nonneg (by linarith only [hCS_nn]) hUh_pos.le))
              _ = C_m2 * (C_S_cond + 1) * U_half * S_pow * (2 * Real.pi) := by ring
          have ht2 : 2 * (C_mn * S_pow * (X'') ^ (3 / 2 : ℝ) * K_act / (1 + T_dual) ^ n_rect) * |2 - a - 6 * D_dual.e| ≤
              4 * C_mn * (C_S_cond + 1) * U_half * S_pow * (2 * Real.pi) := by
            have hp1 : (X'') ^ (3 / 2 : ℝ) * K_act / (1 + T_dual) ^ n_rect ≤ (C_S_cond + 1) * U_half := by
              calc (X'') ^ (3 / 2 : ℝ) * K_act / (1 + T_dual) ^ n_rect
                  = ((X'') ^ (3 / 2 : ℝ) / (1 + T_dual) ^ n_rect) * K_act := by ring
                _ ≤ U ^ (-2 : ℝ) * ((C_S_cond + 1) * U ^ (8 * D_dual.t)) :=
                    mul_le_mul htail_U hK_le hK_nn (Real.rpow_nonneg hU_pos.le _)
                _ = (C_S_cond + 1) * (U ^ (-2 : ℝ) * U ^ (8 * D_dual.t)) := by ring
                _ ≤ (C_S_cond + 1) * U_half := mul_le_mul_of_nonneg_left htail_exp (by linarith only [hCS_nn])
            have hpi3 := Real.pi_gt_three
            have h2pi_gt1 : 1 ≤ 2 * Real.pi := by linarith only [hpi3]
            have hp2 : C_mn * S_pow * ((X'') ^ (3 / 2 : ℝ) * K_act / (1 + T_dual) ^ n_rect) ≤
                C_mn * (C_S_cond + 1) * U_half * S_pow := by
              calc _ ≤ C_mn * S_pow * ((C_S_cond + 1) * U_half) :=
                    mul_le_mul_of_nonneg_left hp1 (mul_nonneg hC_mn.le hSp_pos.le)
                _ = _ := by ring
            calc 2 * (C_mn * S_pow * (X'') ^ (3 / 2 : ℝ) * K_act / (1 + T_dual) ^ n_rect) * |2 - a - 6 * D_dual.e|
                = (2 * |2 - a - 6 * D_dual.e|) * (C_mn * S_pow * ((X'') ^ (3 / 2 : ℝ) * K_act / (1 + T_dual) ^ n_rect)) := by ring
              _ ≤ 4 * (C_mn * (C_S_cond + 1) * U_half * S_pow) :=
                  mul_le_mul (by linarith only [h2a_abs]) hp2
                    (mul_nonneg (mul_nonneg hC_mn.le hSp_pos.le)
                      (div_nonneg (mul_nonneg (Real.rpow_nonneg hX''_pos.le _) hK_nn) (by positivity)))
                    (by norm_num)
              _ ≤ 4 * C_mn * (C_S_cond + 1) * U_half * S_pow * (2 * Real.pi) := by
                  have hprod_nn : 0 ≤ 4 * C_mn * (C_S_cond + 1) * U_half * S_pow :=
                    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith only [hCS_nn])) hUh_pos.le) hSp_pos.le
                  calc 4 * (C_mn * (C_S_cond + 1) * U_half * S_pow)
                      = 4 * C_mn * (C_S_cond + 1) * U_half * S_pow * 1 := by ring
                    _ ≤ 4 * C_mn * (C_S_cond + 1) * U_half * S_pow * (2 * Real.pi) :=
                        mul_le_mul_of_nonneg_left h2pi_gt1 hprod_nn
          have ht3 : (C_mn * S_pow * (X'') ^ (3 / 2 : ℝ) * HeckeReciprocalBound.bound 2) / (1 + T_dual) ^ n_rect * Real.pi ≤
              C_mn * |HeckeReciprocalBound.bound 2| * U_half * S_pow * (2 * Real.pi) := by
            have hU8_ge1 : 1 ≤ U ^ (8 * D_dual.t) := Real.one_le_rpow hU1.le (by linarith only [ht_pos])
            have hp1 : (X'') ^ (3 / 2 : ℝ) / (1 + T_dual) ^ n_rect ≤ U_half :=
              htail_U.trans ((le_mul_of_one_le_right (Real.rpow_nonneg hU_pos.le _) hU8_ge1).trans htail_exp)
            have hb2_le : HeckeReciprocalBound.bound 2 ≤ |HeckeReciprocalBound.bound 2| := le_abs_self _
            calc (C_mn * S_pow * (X'') ^ (3 / 2 : ℝ) * HeckeReciprocalBound.bound 2) / (1 + T_dual) ^ n_rect * Real.pi
                ≤ (C_mn * S_pow * (X'') ^ (3 / 2 : ℝ) * |HeckeReciprocalBound.bound 2|) / (1 + T_dual) ^ n_rect * Real.pi := by
                  gcongr
              _ = C_mn * |HeckeReciprocalBound.bound 2| * S_pow * ((X'') ^ (3 / 2 : ℝ) / (1 + T_dual) ^ n_rect) * Real.pi := by ring
              _ ≤ C_mn * |HeckeReciprocalBound.bound 2| * S_pow * U_half * (2 * Real.pi) := by
                  apply mul_le_mul (mul_le_mul_of_nonneg_left hp1
                    (mul_nonneg (mul_nonneg hC_mn.le (abs_nonneg _)) hSp_pos.le)) (by linarith only [hpi_pos])
                    hpi_pos.le (mul_nonneg (mul_nonneg (mul_nonneg hC_mn.le (abs_nonneg _)) hSp_pos.le) hUh_pos.le)
              _ = C_mn * |HeckeReciprocalBound.bound 2| * U_half * S_pow * (2 * Real.pi) := by ring
          refine hb_pol.trans ?_
          have hsum_3 := add_le_add (add_le_add ht1 ht2) ht3
          have hsum_3' :
              C_m2 * (1 + |s|) ^ 2 * (X'') ^ (a + 6 * D_dual.e - 1 / 2) * K_act * Real.pi +
                2 * (C_mn * S_pow * (X'') ^ (3 / 2 : ℝ) * K_act / (1 + T_dual) ^ n_rect) * |2 - a - 6 * D_dual.e| +
                (C_mn * S_pow * (X'') ^ (3 / 2 : ℝ) * HeckeReciprocalBound.bound 2) / (1 + T_dual) ^ n_rect * Real.pi ≤
              (C_m2 * (C_S_cond + 1) + 4 * C_mn * (C_S_cond + 1) + C_mn * |HeckeReciprocalBound.bound 2|) *
                U_half * S_pow * (2 * Real.pi) :=
            hsum_3.trans_eq (by ring)
          calc (1 / (2 * Real.pi)) *
                (C_m2 * (1 + |s|) ^ 2 * (X'') ^ (a + 6 * D_dual.e - 1 / 2) * K_act * Real.pi +
                  2 * (C_mn * S_pow * (X'') ^ (3 / 2 : ℝ) * K_act / (1 + T_dual) ^ n_rect) * |2 - a - 6 * D_dual.e| +
                  (C_mn * S_pow * (X'') ^ (3 / 2 : ℝ) * HeckeReciprocalBound.bound 2) / (1 + T_dual) ^ n_rect * Real.pi)
              ≤ (1 / (2 * Real.pi)) *
                  ((C_m2 * (C_S_cond + 1) + 4 * C_mn * (C_S_cond + 1) + C_mn * |HeckeReciprocalBound.bound 2|) *
                    U_half * S_pow * (2 * Real.pi)) :=
                mul_le_mul_of_nonneg_left hsum_3' (by positivity)
            _ = (C_m2 * (C_S_cond + 1) + 4 * C_mn * (C_S_cond + 1) + C_mn * |HeckeReciprocalBound.bound 2|) *
                  U_half * S_pow := by field_simp [hpi_pos.ne']
            _ ≤ M_coef * U_half * S_pow := by
                have hM_le : C_m2 * (C_S_cond + 1) + 4 * C_mn * (C_S_cond + 1) +
                    C_mn * |HeckeReciprocalBound.bound 2| ≤ M_coef := by
                  dsimp only [M_coef]; linarith only []
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hM_le hUh_pos.le) hSp_pos.le
        have hsq_norm := pow_le_pow_left₀ (norm_nonneg _) hnorm_1 2
        refine hsq_norm.trans ?_
        have hMc_le : M_coef ^ 2 ≤ C_pol_1 := by
          have hnn : 0 ≤ bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 := mul_nonneg hbf_pos.le (sq_nonneg _)
          dsimp only [C_pol_1]; linarith only [hnn]
        have hU_sq : (U ^ (((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t) / 2)) ^ 2 ≤
            U ^ ((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hU_pos.le]
          exact Real.rpow_le_rpow_of_exponent_le hU1.le (by ring_nf; norm_num)
        have hS_sq : ((1 + |s|) ^ J_c3) ^ 2 = (1 + |s|) ^ (2 * J_c3) := by rw [← pow_mul, mul_comm]
        calc (M_coef * U ^ (((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t) / 2) * (1 + |s|) ^ J_c3) ^ 2
            = M_coef ^ 2 * (U ^ (((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t) / 2)) ^ 2 *
                ((1 + |s|) ^ J_c3) ^ 2 := by ring
          _ ≤ C_pol_1 * U ^ ((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000) *
                (1 + |s|) ^ (2 * J_c3) := by
              rw [hS_sq]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul hMc_le hU_sq (sq_nonneg _) hCpol1_pos.le) (by positivity)
  calc ‖HeckeDyadic.polynomial (targetRow η_base u) true (childLogTest wFresh s) X' 0 0‖ ^ 2
      ≤ (D_excl.card : ℝ) * ∑ _j_ex ∈ D_excl,
          C_pol_1 * U ^ ((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000) *
            (1 + |s|) ^ (2 * J_c3) :=
        hdecomp.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hj_bound) (Nat.cast_nonneg _))
    _ = (D_excl.card : ℝ) ^ 2 * C_pol_1 *
          U ^ ((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000) *
          (1 + |s|) ^ (2 * J_c3) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by dsimp only [C_excl]; linarith only []) hCpol1_pos.le)
            (Real.rpow_nonneg hU_pos.le _))
          (by positivity)

/-- **Case 3 buffered-bin bound (`11/25 ≤ 2*a - 1 ≤ 3/4` and `z_J + z_coll ≤ z_J_cap(θ)`):**
Combines `dual_case3_pointwise_polynomial_bound` on `polynomial (targetRow ...)` with
`dual_ray_prime_bin_supply`, `HeckePrimeAmplitudeBins.product_upper`,
`uncalibrated_subset_slot_row_count` (supplied via `stage1_convex_slot_supply_with_ell`), and
`stage1_convex_large_value_with_ell` (`-1/2000` saving!). -/
theorem dual_case3_bin_bound
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (wFresh : 𝓢(ℝ, ℂ)) {af bf B_w : ℝ} (haf : 0 < af) (habf : af ≤ bf) (hBw0 : 0 ≤ B_w)
    (hs_w : Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf) (hBw : ∀ y, ‖wFresh y‖ ≤ B_w)
    (n_bins : ℕ) :
    ∃ (τ_dual : ℝ) (J_c3 : ℕ), 0 < τ_dual ∧ 2 * τ_dual ≤ D_dual.t ∧
      ∀ data : RowData, ∃ C_c3 U_c3 : ℝ, 0 < C_c3 ∧ 1 < U_c3 ∧
      ∀ U : ℝ, U_c3 ≤ U →
      ∀ {d_outer r θ ell z_Jv x6 V₀ z_J z_coll X' : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        17 / 25 ≤ r → r ≤ 19 / 26 →
        0 ≤ θ → θ ≤ 1 →
        0 ≤ ell → ell ≤ 3 / 500 →
        0 ≤ z_Jv → z_Jv ≤ ell →
        0 ≤ x6 → 0 ≤ V₀ → 0 ≤ z_J → 0 ≤ z_coll →
      let u_sel := θ * stage1Width r
      let H_th := (1 - θ) * 1 + θ * stage1DualScale r
      let z_rem_th := (1 - θ) * ((1 - r) / 2) + θ * stage1RemWidth r
      let H_free := H_th - 6 * ell - 6 * x6
      let r_unm := r - V₀ - 3 * ell + z_Jv - z_coll
      let z_T := z_rem_th - z_Jv - z_J - z_coll
      3 / 100 ≤ H_free → H_free ≤ 1 → r_unm ≤ 1 →
      0 < X' → X' ≤ U ^ r_unm →
      z_J + z_coll ≤ θ * (25 / 3) * (stage1Line r - (1 - r) / 2) →
      ∀ (T' : Finset (Fin D.N)), z_T = ∑ j ∈ T', D.ell j / d_outer →
      let Z_dual := U ^ (3 / (2 * d_outer))
      ∀ {i_bin : ℕ} {a : ℝ}, 1 ≤ i_bin → i_bin ≤ n_bins →
        11 / 25 ≤ 2 * a - 1 → 2 * a - 1 ≤ 3 / 4 →
      ∀ (rows_bin : Finset FreeRow),
        (∀ u ∈ rows_bin, Z_dual ^ (1 / 100 : ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U ^ H_free) →
        (∀ u ∈ rows_bin, detectorMaximum
          (sourceDetectorFamily F_dual.S F_dual.exclusions.prime (deletedBase data).inverse u
            (rayCubeFamily F_dual.modulus ⊤ le_top u))
          (3 * (i_bin + 1 : ℕ) * Z_dual ^ τ_dual) < a + 2 * D_dual.e) →
        (∀ u ∈ rows_bin, a ≤ detectorMaximum
          (sourceDetectorFamily F_dual.S F_dual.exclusions.prime (deletedBase data).inverse u
            (rayCubeFamily F_dual.modulus ⊤ le_top u))
          ((3 * i_bin : ℕ) * Z_dual ^ τ_dual)) →
      ∀ (ζ : ℂ), ζ.re = 17 / 50 → |ζ.im| ≤ Z_dual ^ τ_dual →
      ∀ s : ℝ,
        (∑ u ∈ rows_bin,
          ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
              (childLogTest wFresh s) X' 0 0 *
            ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) ≤
          C_c3 * U ^ (1 - 3 * ell - 5 * u_sel - x6) * (1 + |s|) ^ (2 * J_c3) := by
  letI : Fintype (RayQuotient.Characters F_dual.modulus ⊤) := Fintype.ofFinite _
  have hbf_pos : 0 < bf := haf.trans_le habf
  obtain ⟨τ_dual, K_cnt, hτ_pos, hτ_le, hK_cnt, hcnt_all⟩ :=
    uncalibrated_subset_slot_row_count hβ51 D_dual hfine_dual F_dual n_bins
  have hray_all := dual_ray_prime_bin_supply D D_dual emb hemb F_dual hτ_pos hτ_le n_bins
  obtain ⟨J_c3, hpol_all⟩ := dual_case3_pointwise_polynomial_bound D_dual F_dual
    wFresh haf habf hBw0 hs_w hBw hτ_pos hτ_le n_bins
  refine ⟨τ_dual, J_c3, hτ_pos, hτ_le, ?_⟩
  intro data
  let η_base := (deletedBase data).inverse
  obtain ⟨C0_cnt, hC0_cnt, hcnt_ev⟩ := hcnt_all η_base
  obtain ⟨Z_cnt, hZ_cnt⟩ := eventually_atTop.mp hcnt_ev
  obtain ⟨U_ray, hU_ray1, hray⟩ := hray_all data
  obtain ⟨C_pol, U_pol, hC_pol, hU_pol1, hpol_bound⟩ := hpol_all data
  have hbf_ev : ∀ᶠ U : ℝ in atTop, U ^ (-(1 / 10000 : ℝ)) ≤ bf⁻¹ := by
    have h1 : ∀ᶠ U : ℝ in atTop, bf ≤ U ^ (1 / 10000 : ℝ) :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10000)).eventually (eventually_ge_atTop bf)
    filter_upwards [h1, eventually_gt_atTop (1 : ℝ)] with U hUb hU1
    have hUp : 0 < U := zero_lt_one.trans hU1
    rw [Real.rpow_neg hUp.le]
    exact inv_anti₀ hbf_pos hUb
  obtain ⟨U_bf, hU_bf⟩ := eventually_atTop.mp hbf_ev
  let U_c3 : ℝ := max (max U_ray U_bf) (max 2 (max Z_cnt U_pol))
  have hU_c3_1 : 1 < U_c3 := lt_of_lt_of_le hU_ray1 ((le_max_left _ _).trans (le_max_left _ _))
  let M_lbl_max : ℕ := 4 + ⌈(1 : ℝ) / D_dual.t⌉₊
  let C_bins : ℝ := (M_lbl_max : ℝ) ^ D_dual.N
  have hCbins_pos : 0 < C_bins := by dsimp only [C_bins, M_lbl_max]; positivity
  let C_c3 : ℝ := C_pol * C_bins * K_cnt * C0_cnt + 1
  have hCc3_pos : 0 < C_c3 := by
    have : 0 ≤ C_pol * C_bins * K_cnt * C0_cnt :=
      mul_nonneg (mul_nonneg (mul_nonneg hC_pol.le hCbins_pos.le) hK_cnt.le) hC0_cnt.le
    dsimp only [C_c3]; linarith
  refine ⟨C_c3, U_c3, hCc3_pos, hU_c3_1, ?_⟩
  intro U hU d_outer r θ ell z_Jv x6 V₀ z_J z_coll X'
    hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hx6 hV0 hzJ0 hzc0
    u_sel H_th z_rem_th H_free r_unm z_T hHf_lo hHf_hi hrunm1 hX' hX'_le hzJ_cap
    T' hzT_sum Z_dual i_bin a hi_lo hi_hi hν_lo hν_hi rows_bin hrows_norm hnext hcurr
    ζ hζ_re hζ_im s
  have hU1 : 1 < U := hU_c3_1.trans_le hU
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have ha_lo : 51 / 100 ≤ a := by linarith only [hν_lo]
  have ha_hi : a ≤ 1 := by linarith only [hν_hi]
  have ht_pos := D_dual.t_pos
  have ht_small := D_dual.t_small
  have heps_pos := D_dual.epsilon_pos
  have he_pos := D_dual.e_pos
  have hchild_supp : ∀ y, childLogTest wFresh s y ≠ 0 → y ≤ bf :=
    fun y hy => (hs_w (fun hz => hy (by simp only [childLogTest, hz, zero_mul]))).2
  by_cases hlt_bf : bf * X' < 1
  · have hsum0 : (∑ u ∈ rows_bin,
        ‖HeckeDyadic.polynomial (targetRow η_base u) true (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      rw [polynomial_eq_zero_of_mul_lt_one _ _ hX' hchild_supp hlt_bf, zero_mul, norm_zero, sq, zero_mul]
    rw [hsum0]
    exact mul_nonneg (mul_nonneg hCc3_pos.le (Real.rpow_nonneg hU_pos.le _)) (by positivity)
  · have hbfX : 1 ≤ bf * X' := not_lt.mp hlt_bf
    have hrunm_lo : -(1 / 10000 : ℝ) ≤ r_unm := by
      have h1 : U ^ (-(1 / 10000 : ℝ)) ≤ bf⁻¹ :=
        hU_bf U (((le_max_right _ _).trans (le_max_left _ _)).trans hU)
      have h2 : bf⁻¹ ≤ X' := (inv_le_iff_one_le_mul₀ hbf_pos).mpr (by rwa [mul_comm])
      exact (Real.rpow_le_rpow_left_iff hU1).mp ((h1.trans h2).trans hX'_le)
    have hexp_Zd : 1 ≤ 3 / (2 * d_outer) := (one_le_div (by positivity)).mpr (by linarith only [hd_hi])
    have hZd_ge_U : U ≤ Z_dual :=
      (Real.rpow_one U).symm.trans_le (Real.rpow_le_rpow_of_exponent_le hU1.le hexp_Zd)
    have hZd_cnt : Z_cnt ≤ Z_dual :=
      ((le_max_left Z_cnt U_pol).trans ((le_max_right 2 _).trans ((le_max_right _ _).trans hU))).trans hZd_ge_U
    have hU_ge_pol : U_pol ≤ U :=
      ((le_max_right Z_cnt U_pol).trans ((le_max_right 2 _).trans (le_max_right _ _))).trans hU
    obtain ⟨hZd1, hcntZ⟩ := hZ_cnt Z_dual hZd_cnt
    have hZd_pos : 0 < Z_dual := zero_lt_one.trans hZd1
    have hpol_pt : ∀ u ∈ rows_bin,
        ‖HeckeDyadic.polynomial (targetRow η_base u) true (childLogTest wFresh s) X' 0 0‖ ^ 2 ≤
          C_pol * U ^ ((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000) *
            (1 + |s|) ^ (2 * J_c3) :=
      fun u hu => hpol_bound U hU_ge_pol hd_lo hd_hi hHf_hi hrunm_lo hrunm1 hX' hX'_le
        hi_lo hi_hi ha_lo ha_hi u (hrows_norm u hu).1 (hrows_norm u hu).2 (hnext u hu) s
    -- Step 2: Partition `rows_bin` by `BinLabel S_rem' ((2*a - 1)/2) D_dual.t` and apply `uncalibrated_subset_slot_row_count`.
    let S_rem' : Finset (Fin D_dual.N) := T'.map emb
    have hsup0 := stage1_convex_slot_supply_with_ell hr0 hr1 hθ0 hθ1 hell0 hell1 hJv hx6
      hν_lo hν_hi (x := 0) le_rfl (by norm_num) hzJ_cap
    have hzT_pos : 0 < z_T := by
      have hw0 := (stage1_inv_plain_width_nonneg hν_lo hν_hi (x := 0) le_rfl (by norm_num)).1
      have hHf_w0 : 0 ≤ H_free * ((1 - stage1Crossing (2 * a - 1) 0) / 2) :=
        mul_nonneg (by linarith only [hHf_lo]) hw0
      have hsup0_1 : H_free * ((1 - stage1Crossing (2 * a - 1) 0) / 2) + 1 / 2500 ≤
          z_rem_th - z_Jv - (z_J + z_coll) := by
        have h1 := hsup0.1
        rwa [mul_div_assoc] at h1
      have hrew : z_rem_th - z_Jv - (z_J + z_coll) = z_T := by dsimp only [z_T]; ring
      rw [hrew] at hsup0_1
      linarith only [hsup0_1, hHf_w0]
    have hT_ne : T'.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hzT_sum
      linarith only [hzT_pos, hzT_sum]
    have hS_ne : S_rem'.Nonempty := hT_ne.map
    let d_dual : ℝ := (2 / 3) * d_outer * H_free
    let d_ray : ℝ := d_dual + D_dual.t
    have hd_ray_lo : 1 / 100 ≤ d_ray := by
      dsimp only [d_ray, d_dual]; nlinarith only [hd_lo, hHf_lo, ht_pos]
    have hd_ray_pos : 0 < d_ray := by linarith only [hd_ray_lo]
    have hd_ray_hi : d_ray ≤ 4 / 5 := by
      dsimp only [d_ray, d_dual]; nlinarith only [hd_lo, hd_hi, hHf_lo, hHf_hi, ht_small]
    let U_d : ℝ := Z_dual ^ d_ray
    have hUd_gt1 : 1 < U_d := Real.one_lt_rpow hZd1 hd_ray_pos
    have hUd_pos : 0 < U_d := zero_lt_one.trans hUd_gt1
    let widths_d : Fin D_dual.N → ℝ := fun k => D_dual.ell k / d_ray
    have hUd_width_eq : ∀ j : Fin D.N, U_d ^ (widths_d (emb j)) = U ^ (D.ell j / d_outer) := by
      intro j
      dsimp only [U_d, Z_dual, widths_d]
      rw [← Real.rpow_mul hZd_pos.le, mul_div_cancel₀ _ hd_ray_pos.ne', hemb j,
        ← Real.rpow_mul hU_pos.le]
      congr 1; field_simp [hd_pos.ne']
    have hsum_widths_d : (∑ k ∈ S_rem', widths_d k) = ((2 / 3) * d_outer / d_ray) * z_T := by
      dsimp only [S_rem', widths_d]
      rw [Finset.sum_map, hzT_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hemb j]
      field_simp [hd_pos.ne', hd_ray_pos.ne']
    let phys_fn := physical F_dual.modulus ⊤ (fun u : FreeRow => u.val)
      (fun _ x => (F_dual.w x : ℂ)) (fun _ => 2) widths_d (fun _ => ζ) U_d
    have hphys_eq : ∀ u : FreeRow, ∀ j : Fin D.N,
        phys_fn u (emb j) = HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ := by
      intro u j
      dsimp only [phys_fn, physical]
      have hW_eq : (fun x : ℝ => (F_dual.w x : ℂ)) = (F_dual.W : ℝ → ℂ) :=
        funext (fun x => (F_dual.complex_eq x).symm)
      rw [hW_eq, hUd_width_eq j]
    let lbl_of : FreeRow → BinLabel S_rem' ((2 * a - 1) / 2) D_dual.t :=
      HeckeDetectorFiberPartition.amplitudeLabel S_rem' U_d ((2 * a - 1) / 2) D_dual.t
        D_dual.t_pos widths_d phys_fn
    have hcard_labels : (HeckePrimeAmplitudeBins.labels ((2 * a - 1) / 2) D_dual.t).card ≤ M_lbl_max := by
      unfold HeckePrimeAmplitudeBins.labels
      let S_img : Finset ℝ := (Finset.Icc (0 : ℤ) ⌈((2 * a - 1) / 2) / D_dual.t⌉).image
        (fun n : ℤ => D_dual.t * (n : ℝ))
      change (insert 0 (insert ((2 * a - 1) / 2) S_img)).card ≤ M_lbl_max
      have h1 : (insert 0 (insert ((2 * a - 1) / 2) S_img)).card ≤
          2 + (Finset.Icc (0 : ℤ) ⌈((2 * a - 1) / 2) / D_dual.t⌉).card := by
        have hc0 := Finset.card_insert_le (0 : ℝ) (insert ((2 * a - 1) / 2) S_img)
        have hc1 := Finset.card_insert_le ((2 * a - 1) / 2) S_img
        have hc2 : S_img.card ≤ (Finset.Icc (0 : ℤ) ⌈((2 * a - 1) / 2) / D_dual.t⌉).card :=
          Finset.card_image_le
        omega
      have hceil_le : ⌈((2 * a - 1) / 2) / D_dual.t⌉ ≤ (⌈(1 : ℝ) / D_dual.t⌉₊ : ℤ) := by
        apply Int.ceil_le.mpr
        have hle1 : ((2 * a - 1) / 2) / D_dual.t ≤ (1 : ℝ) / D_dual.t :=
          div_le_div_of_nonneg_right (by linarith only [hν_hi]) ht_pos.le
        exact hle1.trans (Nat.le_ceil _)
      have hIcc_card : (Finset.Icc (0 : ℤ) ⌈((2 * a - 1) / 2) / D_dual.t⌉).card ≤
          1 + ⌈(1 : ℝ) / D_dual.t⌉₊ := by
        have hsub : Finset.Icc (0 : ℤ) ⌈((2 * a - 1) / 2) / D_dual.t⌉ ⊆
            Finset.Icc (0 : ℤ) (⌈(1 : ℝ) / D_dual.t⌉₊ : ℤ) :=
          Finset.Icc_subset_Icc_right hceil_le
        refine (Finset.card_le_card hsub).trans ?_
        rw [Int.card_Icc]
        omega
      dsimp only [M_lbl_max]; omega
    have hcard_BinLabel : (Fintype.card (BinLabel S_rem' ((2 * a - 1) / 2) D_dual.t) : ℝ) ≤ C_bins := by
      have hc : Fintype.card (BinLabel S_rem' ((2 * a - 1) / 2) D_dual.t) ≤ M_lbl_max ^ D_dual.N := by
        rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_coe]
        calc (HeckePrimeAmplitudeBins.labels ((2 * a - 1) / 2) D_dual.t).card ^ S_rem'.card
            ≤ M_lbl_max ^ S_rem'.card := Nat.pow_le_pow_left hcard_labels _
          _ ≤ M_lbl_max ^ D_dual.N := Nat.pow_le_pow_right (by dsimp only [M_lbl_max]; omega)
              ((Finset.card_le_univ S_rem').trans_eq (Fintype.card_fin D_dual.N))
      dsimp only [C_bins]; exact_mod_cast hc
    have hbin_sum : ∀ bin_rem : BinLabel S_rem' ((2 * a - 1) / 2) D_dual.t,
        let rows_f := rows_bin.filter (fun u => lbl_of u = bin_rem)
        (∑ u ∈ rows_f, ‖∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) ≤
        K_cnt * C0_cnt * U ^ (1 - 3 * ell - 5 * u_sel - x6 -
          ((2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000)) := by
      intro bin_rem rows_f
      by_cases hne_f : rows_f.Nonempty
      · obtain ⟨u_wit, hu_wit⟩ := hne_f
        let q_rem := weightedMean S_rem' widths_d (binValue S_rem' ((2 * a - 1) / 2) D_dual.t bin_rem)
        let δ := 2 * a - 1
        let x_rem := q_rem / δ
        have hδ_pos : 0 < δ := by dsimp only [δ]; linarith only [hν_lo]
        have hδ_56 : δ ≤ 5 / 6 := by dsimp only [δ]; linarith only [hν_hi]
        have hw_pos_d : ∀ k ∈ S_rem', 0 < widths_d k :=
          fun k _ => div_pos (D_dual.slots_bounds k).1 hd_ray_pos
        have hL_rem_pos : 0 < ∑ k ∈ S_rem', widths_d k := Finset.sum_pos hw_pos_d hS_ne
        have hbins_f : ∀ u ∈ rows_f, ∀ k ∈ S_rem',
            HeckePrimeAmplitudeBins.amplitude (U_d ^ (widths_d k)) ((2 * a - 1) / 2) D_dual.t
              (phys_fn u k) = binValue S_rem' ((2 * a - 1) / 2) D_dual.t bin_rem k := by
          intro u hu k hk
          have he := (Finset.mem_filter.mp hu).2
          have hv := congrArg (fun f : BinLabel S_rem' ((2 * a - 1) / 2) D_dual.t => (f ⟨k, hk⟩).val) he
          simpa only [lbl_of, HeckeDetectorFiberPartition.amplitudeLabel, binValue, dif_pos hk] using hv
        have hq_bounds : 0 ≤ q_rem ∧ q_rem ≤ δ / 2 := by
          dsimp only [q_rem, δ]
          apply weightedMean_bounds S_rem' widths_d _ (2 * a - 1)
            (fun k hk => (hw_pos_d k hk).le) hL_rem_pos
          intro k hk
          rw [← hbins_f u_wit hu_wit k hk]
          exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith only [hν_lo])
        have hx0 : 0 ≤ x_rem := div_nonneg hq_bounds.1 hδ_pos.le
        have hx1 : x_rem ≤ 1 / 2 := (div_le_iff₀ hδ_pos).mpr (by linarith only [hq_bounds.2])
        have hsup_x := stage1_convex_slot_supply_with_ell hr0 hr1 hθ0 hθ1 hell0 hell1 hJv hx6
          hν_lo hν_hi hx0 hx1 hzJ_cap
        have hzT_rew : z_rem_th - z_Jv - (z_J + z_coll) = z_T := by dsimp only [z_T]; ring
        have hsup_x1 : H_free * (1 - stage1Crossing δ x_rem) / 2 + 1 / 2500 ≤ z_T := by
          have h1 := hsup_x.1; rwa [hzT_rew] at h1
        have hsup_x2 : H_free * (1 - 2 * ((1 + δ * rowP x_rem / (2 * rowJ δ x_rem)) - stage1Crossing δ x_rem)) *
            (2 / 9) + 1 / 2500 ≤ z_T := by
          have h2 := hsup_x.2; rwa [hzT_rew] at h2
        let tstar := Endpoint.balancedCutoff δ (1 / 2 - x_rem)
        have htstar_eq : tstar = 1 + δ * rowP x_rem / (2 * rowJ δ x_rem) := by
          have hden : Endpoint.balanceDenominator δ (1 / 2 - x_rem) = rowJ δ x_rem := by
            unfold Endpoint.balanceDenominator Endpoint.denominator Endpoint.primeWeight rowJ rowD rowP
            ring
          have hpw : Endpoint.primeWeight (1 / 2 - x_rem) = rowP x_rem := by
            unfold Endpoint.primeWeight rowP; ring
          dsimp only [tstar]; unfold Endpoint.balancedCutoff; rw [hden, hpw]
        have hqx : δ * x_rem = q_rem := by dsimp only [x_rem]; field_simp [hδ_pos.ne']
        have htb : 1 ≤ tstar ∧ tstar ≤ 3 / 2 := by
          have hc := HeckeDetectorAdaptiveCutoff.cutoff_bounds δ q_rem hδ_pos.le
          rw [HeckeDetectorAdaptiveCutoff.cutoff_eq_balanced δ q_rem hδ_pos hδ_56 hq_bounds.1 hq_bounds.2] at hc
          exact hc
        have hsc : crossing x_rem tstar = stage1Crossing δ x_rem :=
          (stage1_crossing_and_count_eq hδ_pos.le hδ_56 hx0 hx1).1
        have hcb_all := crossing_bounds hx0 hx1 htb.1 htb.2
        have hsup_inv_d : (1 - stage1Crossing δ x_rem) / 2 + 2 * D_dual.t ≤ ∑ k ∈ S_rem', widths_d k := by
          rw [hsum_widths_d]
          let W₁ := (1 - stage1Crossing δ x_rem) / 2
          have hW₁_hi : W₁ ≤ 1 := by
            have hcb1 := hcb_all.1
            dsimp only [W₁]
            linarith only [hcb1, hsc]
          have hmul_d : (W₁ + 2 * D_dual.t) * d_ray ≤ (2 / 3) * d_outer * z_T := by
            have h1 : H_free * W₁ + 1 / 2500 ≤ z_T := by
              dsimp only [W₁]; rwa [← mul_div_assoc]
            have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (2 / 3) * d_outer by positivity)
            have h3 : (2 / 3) * d_outer * (H_free * W₁ + 1 / 2500) =
                d_dual * W₁ + (2 / 3) * d_outer * (1 / 2500) := by dsimp only [d_dual]; ring
            rw [h3] at h2
            have h4 : (W₁ + 2 * D_dual.t) * d_ray =
                d_dual * W₁ + D_dual.t * W₁ + 2 * D_dual.t * d_ray := by dsimp only [d_ray]; ring
            nlinarith only [h2, h4, ht_pos, ht_small, hd_lo, hd_ray_hi, hW₁_hi]
          exact (le_div_iff₀ hd_ray_pos).mpr hmul_d |>.trans_eq (by ring)
        have hsup_pl_d : (1 - 2 * (tstar - stage1Crossing δ x_rem)) * (2 / 9) + 2 * D_dual.t ≤
            ∑ k ∈ S_rem', widths_d k := by
          rw [hsum_widths_d]
          let W₂ := (1 - 2 * (tstar - stage1Crossing δ x_rem)) * (2 / 9)
          have hW₂_hi : W₂ ≤ 1 := by
            have hcb3 := hcb_all.2.2.1
            dsimp only [W₂]
            linarith only [hcb3, hsc]
          have hmul_d : (W₂ + 2 * D_dual.t) * d_ray ≤ (2 / 3) * d_outer * z_T := by
            have h1 : H_free * W₂ + 1 / 2500 ≤ z_T := by
              dsimp only [W₂]; rw [htstar_eq, ← mul_assoc]; exact hsup_x2
            have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (2 / 3) * d_outer by positivity)
            have h3 : (2 / 3) * d_outer * (H_free * W₂ + 1 / 2500) =
                d_dual * W₂ + (2 / 3) * d_outer * (1 / 2500) := by dsimp only [d_dual]; ring
            rw [h3] at h2
            have h4 : (W₂ + 2 * D_dual.t) * d_ray =
                d_dual * W₂ + D_dual.t * W₂ + 2 * D_dual.t * d_ray := by dsimp only [d_ray]; ring
            nlinarith only [h2, h4, ht_pos, ht_small, hd_lo, hd_ray_hi, hW₂_hi]
          exact (le_div_iff₀ hd_ray_pos).mpr hmul_d |>.trans_eq (by ring)
        have hZd_UH : U ^ H_free = Z_dual ^ (d_ray - D_dual.t) := by
          have hd_sub : d_ray - D_dual.t = (2 / 3) * d_outer * H_free := by dsimp only [d_ray, d_dual]; ring
          rw [hd_sub]; dsimp only [Z_dual]; rw [← Real.rpow_mul hU_pos.le]; congr 1; field_simp [hd_pos.ne']
        have hζ_im_2τ : |ζ.im| ≤ Z_dual ^ (2 * τ_dual) :=
          hζ_im.trans (Real.rpow_le_rpow_of_exponent_le hZd1.le (by linarith only [hτ_pos]))
        have hcard_f := hcntZ d_ray hd_ray_lo hd_ray_hi a i_bin hi_hi hν_lo hν_hi
          S_rem' hS_ne (fun _ => ζ) (fun _ => hζ_re) (fun _ => hζ_im_2τ) bin_rem
          hsup_inv_d hsup_pl_d rows_f
          (fun u hu => ⟨(hrows_norm u (Finset.mem_filter.mp hu).1).1,
            hZd_UH ▸ (hrows_norm u (Finset.mem_filter.mp hu).1).2⟩)
          (fun u hu => hnext u (Finset.mem_filter.mp hu).1)
          (fun u hu => hcurr u (Finset.mem_filter.mp hu).1)
          hbins_f
        have hprod_f : ∀ u ∈ rows_f,
            ‖∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2 ≤
            U ^ ((2 * δ * x_rem + 2 * D_dual.t) * z_T) := by
          intro u hu
          have hu_bin : u ∈ rows_bin := (Finset.mem_filter.mp hu).1
          have hmap_prod : (∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ) = ∏ k ∈ S_rem', phys_fn u k := by
            dsimp only [S_rem']
            rw [Finset.prod_map]
            exact Finset.prod_congr rfl (fun j _ => (hphys_eq u j).symm)
          have hQ_upper : ∀ k ∈ S_rem', ‖phys_fn u k‖ ≤ (U_d ^ (widths_d k)) ^ ((2 * a - 1) / 2 + D_dual.t) := by
            intro k hk
            obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hk
            rw [hphys_eq u j, hUd_width_eq j]
            exact hray U (((le_max_left _ _).trans (le_max_left _ _)).trans hU)
              hd_lo hd_hi hHf_lo hHf_hi hi_lo hi_hi ha_lo ha_hi
              u (hrows_norm u hu_bin).1 (hrows_norm u hu_bin).2 (hnext u hu_bin) ζ hζ_re hζ_im j
          have hpu := HeckePrimeAmplitudeBins.product_upper S_rem' widths_d (phys_fn u)
            U_d ((2 * a - 1) / 2) D_dual.t hUd_gt1 D_dual.t_pos hw_pos_d hQ_upper
          have hsum_amp : (∑ k ∈ S_rem', widths_d k *
              HeckePrimeAmplitudeBins.amplitude (U_d ^ (widths_d k)) ((2 * a - 1) / 2) D_dual.t (phys_fn u k)) =
              q_rem * ∑ k ∈ S_rem', widths_d k := by
            have h1 : (∑ k ∈ S_rem', widths_d k *
                HeckePrimeAmplitudeBins.amplitude (U_d ^ (widths_d k)) ((2 * a - 1) / 2) D_dual.t (phys_fn u k)) =
                ∑ k ∈ S_rem', widths_d k * binValue S_rem' ((2 * a - 1) / 2) D_dual.t bin_rem k :=
              Finset.sum_congr rfl (fun k hk => by rw [hbins_f u hu k hk])
            rw [h1]
            dsimp only [q_rem]; unfold weightedMean
            exact (div_mul_cancel₀ _ hL_rem_pos.ne').symm
          rw [hsum_amp] at hpu
          have hsq := pow_le_pow_left₀ (norm_nonneg _) (hmap_prod ▸ hpu) 2
          refine hsq.trans_eq ?_
          dsimp only [U_d, Z_dual]
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Real.rpow_nonneg hZd_pos.le _),
            ← Real.rpow_mul hZd_pos.le, ← Real.rpow_mul hU_pos.le, hsum_widths_d, ← hqx]
          congr 1
          field_simp [hd_pos.ne', hd_ray_pos.ne']
          ring
        have hZd_exp : Z_dual ^ (d_ray * Budget.rowCount δ x_rem + 200 * D_dual.ε + 20 * D_dual.t + subDelta) ≤
            U ^ (H_free * Budget.rowCount δ x_rem + 3 * (D_dual.t + 200 * D_dual.ε + 20 * D_dual.t + subDelta)) := by
          have hrc_le1 : Budget.rowCount δ x_rem ≤ 1 := by
            have hJ := rowJ_pos hδ_pos.le hδ_56 hx1
            have htb2 := htb.2
            rw [htstar_eq] at htb2
            have hdiv_le : δ * rowP x_rem / (2 * rowJ δ x_rem) ≤ 1 / 2 := by linarith only [htb2]
            have hmul_le := (div_le_iff₀ (show (0 : ℝ) < 2 * rowJ δ x_rem by linarith only [hJ])).mp hdiv_le
            have h56_2δ : 5 / 6 - δ ≤ 2 * δ := by dsimp only [δ]; linarith only [hν_lo]
            have hP_nn : 0 ≤ rowP x_rem := by
              unfold rowP; exact mul_nonneg (by linarith only [hx1]) (by linarith only [hx0, hx1])
            unfold Budget.rowCount
            have hterm_le : (5 / 6 - δ) * δ * rowP x_rem / (2 * rowJ δ x_rem) ≤ δ := by
              rw [div_le_iff₀ (show (0 : ℝ) < 2 * rowJ δ x_rem by linarith only [hJ])]
              calc (5 / 6 - δ) * δ * rowP x_rem
                  = (5 / 6 - δ) * (δ * rowP x_rem) := by ring
                _ ≤ (2 * δ) * (δ * rowP x_rem) :=
                    mul_le_mul_of_nonneg_right h56_2δ (mul_nonneg hδ_pos.le hP_nn)
                _ ≤ (2 * δ) * (1 / 2 * (2 * rowJ δ x_rem)) :=
                    mul_le_mul_of_nonneg_left hmul_le (by linarith only [hδ_pos])
                _ = δ * (2 * rowJ δ x_rem) := by ring
            linarith only [hterm_le]
          have hd_split : d_ray * Budget.rowCount δ x_rem ≤
              d_dual * Budget.rowCount δ x_rem + D_dual.t := by
            dsimp only [d_ray]; rw [add_mul]
            exact add_le_add_right (mul_le_of_le_one_right ht_pos.le hrc_le1) _
          have h3_div : (3 / (2 * d_outer)) ≤ 3 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hd_lo])
          have h3d : (3 / (2 * d_outer)) * d_dual = H_free := by dsimp only [d_dual]; field_simp [hd_pos.ne']
          have herr_nn : 0 ≤ D_dual.t + 200 * D_dual.ε + 20 * D_dual.t + subDelta := by
            have := subDelta_pos; positivity
          dsimp only [Z_dual]
          rw [← Real.rpow_mul hU_pos.le]
          apply Real.rpow_le_rpow_of_exponent_le hU1.le
          have hmul1 : (3 / (2 * d_outer)) *
              (d_ray * Budget.rowCount δ x_rem + 200 * D_dual.ε + 20 * D_dual.t + subDelta) ≤
              (3 / (2 * d_outer)) *
                (d_dual * Budget.rowCount δ x_rem + D_dual.t + 200 * D_dual.ε + 20 * D_dual.t + subDelta) :=
            mul_le_mul_of_nonneg_left
              (show d_ray * Budget.rowCount δ x_rem + 200 * D_dual.ε + 20 * D_dual.t + subDelta ≤
                  d_dual * Budget.rowCount δ x_rem + D_dual.t + 200 * D_dual.ε + 20 * D_dual.t + subDelta
                by linarith only [hd_split])
              (show (0 : ℝ) ≤ 3 / (2 * d_outer) by positivity)
          have hmul2 : (3 / (2 * d_outer)) * (D_dual.t + 200 * D_dual.ε + 20 * D_dual.t + subDelta) ≤
              3 * (D_dual.t + 200 * D_dual.ε + 20 * D_dual.t + subDelta) :=
            mul_le_mul_of_nonneg_right h3_div herr_nn
          have hlin1 : (3 / (2 * d_outer)) * (d_dual * Budget.rowCount δ x_rem + D_dual.t +
              200 * D_dual.ε + 20 * D_dual.t + subDelta) =
              ((3 / (2 * d_outer)) * d_dual) * Budget.rowCount δ x_rem +
                (3 / (2 * d_outer)) * (D_dual.t + 200 * D_dual.ε + 20 * D_dual.t + subDelta) := by ring
          rw [h3d] at hlin1
          linarith only [hmul1, hmul2, hlin1]
        have hcert_lv := stage1_convex_large_value_with_ell hr0 hr1 hθ0 hθ1 hell0 hJv0 hJv
          hx6 hV0 hzJ0 hzc0 hν_lo hν_hi hx0 hx1
        have hzT_le1 : z_T ≤ 1 / 3 := by
          rw [hzT_sum, ← Finset.sum_div]
          exact ((div_le_div_of_nonneg_right
            ((Finset.sum_le_univ_sum_of_nonneg (fun j => (D.slots_bounds j).1.le)).trans_eq D.slots_sum)
            hd_pos.le).trans ((div_le_iff₀ hd_pos).mpr (by linarith only [hd_lo])))
        have hexp_f : (H_free * Budget.rowCount δ x_rem +
              3 * (D_dual.t + 200 * D_dual.ε + 20 * D_dual.t + subDelta)) +
            ((2 * δ * x_rem + 2 * D_dual.t) * z_T) ≤
            1 - 3 * ell - 5 * u_sel - x6 -
              (δ * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000) := by
          have hsubD : subDelta = 1 / 100000000 := rfl
          have h2z : 2 * D_dual.t * z_T ≤ D_dual.t := by nlinarith only [ht_pos, hzT_le1]
          have hlin_z : (2 * δ * x_rem + 2 * D_dual.t) * z_T =
              2 * x_rem * δ * z_T + 2 * D_dual.t * z_T := by ring
          dsimp only [u_sel, H_free, H_th, r_unm, z_T, z_rem_th, δ] at hcert_lv h2z hlin_z ⊢
          linarith only [hcert_lv, hsubD, h2z, hlin_z, h2000_eps, h2000_e, ht_small, heps_pos, he_pos, ht_pos]
        calc
          (∑ u ∈ rows_f, ‖∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2)
            ≤ ∑ _u ∈ rows_f, U ^ ((2 * δ * x_rem + 2 * D_dual.t) * z_T) := Finset.sum_le_sum hprod_f
          _ = (rows_f.card : ℝ) * U ^ ((2 * δ * x_rem + 2 * D_dual.t) * z_T) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (K_cnt * C0_cnt * Z_dual ^ (d_ray * Budget.rowCount δ x_rem + 200 * D_dual.ε + 20 * D_dual.t + subDelta)) *
                U ^ ((2 * δ * x_rem + 2 * D_dual.t) * z_T) :=
              mul_le_mul_of_nonneg_right hcard_f (Real.rpow_nonneg hU_pos.le _)
          _ ≤ (K_cnt * C0_cnt * U ^ (H_free * Budget.rowCount δ x_rem +
                3 * (D_dual.t + 200 * D_dual.ε + 20 * D_dual.t + subDelta))) *
              U ^ ((2 * δ * x_rem + 2 * D_dual.t) * z_T) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hZd_exp (mul_nonneg hK_cnt.le hC0_cnt.le))
                (Real.rpow_nonneg hU_pos.le _)
          _ = K_cnt * C0_cnt * U ^ ((H_free * Budget.rowCount δ x_rem +
                3 * (D_dual.t + 200 * D_dual.ε + 20 * D_dual.t + subDelta)) +
                ((2 * δ * x_rem + 2 * D_dual.t) * z_T)) := by
              rw [mul_assoc, ← Real.rpow_add hU_pos]
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1.le hexp_f)
              (mul_nonneg hK_cnt.le hC0_cnt.le)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne_f, Finset.sum_empty]
        exact mul_nonneg (mul_nonneg hK_cnt.le hC0_cnt.le) (Real.rpow_nonneg hU_pos.le _)
    have hpart_amp :
        (∑ u ∈ rows_bin, ‖∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) =
        ∑ bin_rem : BinLabel S_rem' ((2 * a - 1) / 2) D_dual.t,
          ∑ u ∈ rows_bin.filter (fun u => lbl_of u = bin_rem),
            ‖∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
    let E_pol := (2 * a - 1) * r_unm + 12 * D_dual.e + 20 * D_dual.t + 1 / 10000
    let E_amp := 1 - 3 * ell - 5 * u_sel - x6 - E_pol
    have hamp_tot :
        (∑ u ∈ rows_bin, ‖∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
          F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) ≤
        C_bins * K_cnt * C0_cnt * U ^ E_amp := by
      rw [hpart_amp]
      calc _ ≤ ∑ _bin : BinLabel S_rem' ((2 * a - 1) / 2) D_dual.t, (K_cnt * C0_cnt * U ^ E_amp) :=
            Finset.sum_le_sum (fun b _ => hbin_sum b)
        _ = (Fintype.card (BinLabel S_rem' ((2 * a - 1) / 2) D_dual.t) : ℝ) *
              (K_cnt * C0_cnt * U ^ E_amp) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ C_bins * (K_cnt * C0_cnt * U ^ E_amp) :=
            mul_le_mul_of_nonneg_right hcard_BinLabel
              (mul_nonneg (mul_nonneg hK_cnt.le hC0_cnt.le) (Real.rpow_nonneg hU_pos.le _))
        _ = _ := by ring
    calc
      (∑ u ∈ rows_bin,
        ‖HeckeDyadic.polynomial (targetRow η_base u) true (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2)
        ≤ ∑ u ∈ rows_bin,
            (C_pol * U ^ E_pol * (1 + |s|) ^ (2 * J_c3)) *
            ‖∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2 := by
          apply Finset.sum_le_sum; intro u hu
          rw [norm_mul, mul_pow]
          exact mul_le_mul_of_nonneg_right (hpol_pt u hu) (sq_nonneg _)
      _ = (C_pol * U ^ E_pol * (1 + |s|) ^ (2 * J_c3)) *
            ∑ u ∈ rows_bin, ‖∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2 :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (C_pol * U ^ E_pol * (1 + |s|) ^ (2 * J_c3)) *
            (C_bins * K_cnt * C0_cnt * U ^ E_amp) :=
          mul_le_mul_of_nonneg_left hamp_tot
            (mul_nonneg (mul_nonneg hC_pol.le (Real.rpow_nonneg hU_pos.le _)) (by positivity))
      _ = (C_pol * C_bins * K_cnt * C0_cnt) * (U ^ E_pol * U ^ E_amp) *
            (1 + |s|) ^ (2 * J_c3) := by ring
      _ ≤ C_c3 * U ^ (1 - 3 * ell - 5 * u_sel - x6) * (1 + |s|) ^ (2 * J_c3) := by
          rw [← Real.rpow_add hU_pos, show E_pol + E_amp = 1 - 3 * ell - 5 * u_sel - x6 by dsimp only [E_amp]; ring]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by dsimp only [C_c3]; linarith only []) (Real.rpow_nonneg hU_pos.le _))
            (by positivity)

/-- **Master unpunctured sixth-power-free factored `L^2` bound (`dual_sixth_free_factored_energy`):**
Synthesizes `dual_no_slot_branch_bound` (for `H_free ≤ max (1/10) (r_unm + 10 t_dual)` and the low
dyadic tail `rowNorm u < Z_dual ^ (1/100)`), `exists_detector_buffered_bin` +
`detectorMaximum_le_seven_eighths`, `dual_case2_bin_bound`, and `dual_case3_bin_bound` into a single
uniform `L^2` bound `≤ C_sf * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_sf)`. -/
theorem dual_sixth_free_factored_energy
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (wFresh : 𝓢(ℝ, ℂ)) {af bf B_w : ℝ} (haf : 0 < af) (habf : af ≤ bf) (hBw0 : 0 ≤ B_w)
    (hs_w : Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf) (hBw : ∀ y, ‖wFresh y‖ ≤ B_w) :
    ∃ (τ_dual : ℝ) (J_sf : ℕ), 0 < τ_dual ∧ 2 * τ_dual ≤ D_dual.t ∧
      ∀ data : RowData, ∃ C_sf U_sf : ℝ, 0 < C_sf ∧ 1 < U_sf ∧
      ∀ U : ℝ, U_sf ≤ U →
      ∀ {d_outer r θ ell z_Jv x6 V₀ z_J z_coll X' : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        17 / 25 ≤ r → r ≤ 19 / 26 →
        0 ≤ θ → θ ≤ 1 →
        0 ≤ ell → ell ≤ 3 / 500 →
        0 ≤ z_Jv → z_Jv ≤ ell →
        0 ≤ x6 → 0 ≤ V₀ → 0 ≤ z_J → 0 ≤ z_coll →
      let u_sel := θ * stage1Width r;
      let H_th := (1 - θ) * 1 + θ * stage1DualScale r;
      let z_rem_th := (1 - θ) * ((1 - r) / 2) + θ * stage1RemWidth r;
      let H_free := H_th - 6 * ell - 6 * x6;
      let r_unm := r - V₀ - 3 * ell + z_Jv - z_coll;
      let z_T_cap := z_rem_th - z_Jv - z_J - z_coll;
      (-D_dual.t) ≤ H_free →
      0 < X' → X' ≤ U ^ r_unm →
      ∀ (T' : Finset (Fin D.N)), (∑ j ∈ T', D.ell j / d_outer) ≤ z_T_cap →
      let Z_dual := U ^ (3 / (2 * d_outer));
      ∀ (S_free : Finset FreeRow), (∀ u ∈ S_free, rowNorm u ≤ U ^ (max 0 H_free)) →
      ∀ (ζ : ℂ), ζ.re = 17 / 50 → |ζ.im| ≤ Z_dual ^ τ_dual →
      ∀ s : ℝ,
        (∑ u ∈ S_free,
          ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
              (childLogTest wFresh s) X' 0 0 *
            ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) ≤
          C_sf * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_sf) := by
  letI : Fintype (RayQuotient.Characters F_dual.modulus ⊤) := Fintype.ofFinite _
  let n_bins : ℕ := ⌊(49 / 100 : ℝ) / D_dual.e⌋₊ + 1
  have hn_bins_pos : 0 < n_bins := Nat.succ_pos _
  have hn_bins_width : (49 / 100 : ℝ) ≤ (n_bins : ℝ) * D_dual.e := by
    have hlt : (49 / 100 : ℝ) / D_dual.e < (n_bins : ℝ) := by
      dsimp only [n_bins]; push_cast; exact Nat.lt_floor_add_one _
    exact (div_lt_iff₀ D_dual.e_pos).mp hlt |>.le
  obtain ⟨J_ns, hns_all⟩ := dual_no_slot_branch_bound F_dual wFresh haf habf hBw0 hs_w hBw D.N
  obtain ⟨τ_dual, J_c3, hτ_pos, hτ_le, hc3_all⟩ :=
    dual_case3_bin_bound hβ51 D D_dual h2000_eps h2000_e hfine_dual emb hemb F_dual
      wFresh haf habf hBw0 hs_w hBw n_bins
  obtain ⟨J_c2, hc2_all⟩ :=
    dual_case2_bin_bound D D_dual emb hemb F_dual wFresh haf habf hBw0 hs_w hBw hτ_pos hτ_le n_bins
  let J_sf : ℕ := max J_ns (max J_c2 J_c3)
  refine ⟨τ_dual, J_sf, hτ_pos, hτ_le, ?_⟩
  intro data
  obtain ⟨C_ns, U_ns, hC_ns, hU_ns1, hns⟩ := hns_all data
  obtain ⟨C_c2, U_c2, hC_c2, hU_c2_1, hc2⟩ := hc2_all data
  obtain ⟨C_c3, U_c3, hC_c3, hU_c3_1, hc3⟩ := hc3_all data
  have hT_ev : ∀ᶠ Z : ℝ in atTop, 2 < Z ^ τ_dual :=
    (tendsto_rpow_atTop hτ_pos).eventually (eventually_gt_atTop 2)
  obtain ⟨Z_T, hZ_T⟩ := eventually_atTop.mp hT_ev
  let U_sf : ℝ := max (max U_ns U_c2) (max U_c3 (max 2 Z_T))
  have hU_sf1 : 1 < U_sf := lt_of_lt_of_le hU_ns1 ((le_max_left _ _).trans (le_max_left _ _))
  let N_grid : ℝ := ((n_bins * (n_bins + 1) : ℕ) : ℝ)
  let C_sf : ℝ := C_ns + N_grid * (C_c2 + C_c3) + 1
  refine ⟨C_sf, U_sf, by dsimp only [C_sf, N_grid]; positivity, hU_sf1, ?_⟩
  intro U hU d_outer r θ ell z_Jv x6 V₀ z_J z_coll X'
    hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hx6 hV0 hzJ0 hzc0
    u_sel H_th z_rem_th H_free r_unm z_T_cap hHf_lo_t hX' hX'_le T' hzT_le Z_dual
    S_free hS_norm ζ hζ_re hζ_im s
  have hU1 : 1 < U := hU_sf1.trans_le hU
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have ht_pos := D_dual.t_pos
  have ht_small := D_dual.t_small
  have he_pos := D_dual.e_pos
  have hHf_hi : H_free ≤ 1 := by
    have hdz0 : 0 ≤ stage1Line r - (1 - r) / 2 := by unfold stage1Line; linarith only [hr0, hr1]
    have hw0 : 0 ≤ stage1Width r := by unfold stage1Width; exact mul_nonneg (by norm_num) hdz0
    have hsc1 : stage1DualScale r ≤ 1 := by unfold stage1DualScale; linarith only [hw0]
    have hHth1 : H_th ≤ 1 := by
      dsimp only [H_th]
      nlinarith only [hθ0, hθ1, hsc1]
    dsimp only [H_free]; linarith only [hHth1, hell0, hx6]
  have hrunm1 : r_unm ≤ 1 := by dsimp only [r_unm]; linarith only [hr1, hV0, hJv, hell0, hzc0]
  let z_T_act : ℝ := ∑ j ∈ T', D.ell j / d_outer
  have hzT_act0 : 0 ≤ z_T_act :=
    Finset.sum_nonneg (fun j _ => div_nonneg (D.slots_bounds j).1.le hd_pos.le)
  let z_J' : ℝ := z_J + (z_T_cap - z_T_act)
  have hzJ'0 : 0 ≤ z_J' := add_nonneg hzJ0 (sub_nonneg.mpr hzT_le)
  have hzT'_eq : z_rem_th - z_Jv - z_J' - z_coll = z_T_act := by
    dsimp only [z_J', z_T_cap]; ring
  have hZ1_slot : ∀ j ∈ T', 1 ≤ U ^ (D.ell j / d_outer) :=
    fun j _ => Real.one_le_rpow hU1.le (div_nonneg (D.slots_bounds j).1.le hd_pos.le)
  have hZ_prod : (∏ j ∈ T', U ^ (D.ell j / d_outer)) ≤ U ^ z_T_act :=
    (Real.rpow_sum_of_pos hU_pos _ _).symm.le
  have hcard_T' : T'.card ≤ D.N := (Finset.card_le_univ T').trans_eq (Fintype.card_fin D.N)
  have habs_s := abs_nonneg s
  have h1s_ns : (1 + |s|) ^ (2 * J_ns) ≤ (1 + |s|) ^ (2 * J_sf) :=
    pow_le_pow_right₀ (by linarith only [habs_s]) (by dsimp only [J_sf]; omega)
  have h1s_c2 : (1 + |s|) ^ (2 * J_c2) ≤ (1 + |s|) ^ (2 * J_sf) :=
    pow_le_pow_right₀ (by linarith only [habs_s]) (by dsimp only [J_sf]; omega)
  have h1s_c3 : (1 + |s|) ^ (2 * J_c3) ≤ (1 + |s|) ^ (2 * J_sf) :=
    pow_le_pow_right₀ (by linarith only [habs_s]) (by dsimp only [J_sf]; omega)
  -- Helper wrapping `dual_no_slot_branch_bound` + `stage1_low_or_small_H_exponent` for both `H_sub ≤ 3/100` and small `H_free`.
  have hns_wrap : ∀ (R_sub : Finset FreeRow) (H_sub : ℝ),
      0 ≤ H_sub → H_sub ≤ 1 →
      (H_sub ≤ 3 / 100 ∨ (H_sub = H_free ∧ H_free ≤ max (1 / 10) (r_unm + 10 * D_dual.t))) →
      (∀ u ∈ R_sub, rowNorm u ≤ U ^ H_sub) →
      (∑ u ∈ R_sub,
        ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) ≤
      C_ns * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_sf) := by
    intro R_sub H_sub hHs0 hHs1 hbr hR_norm
    have hb := hns U (((le_max_left _ _).trans (le_max_left _ _)).trans hU)
      T' hcard_T' (fun j => U ^ (D.ell j / d_outer)) hzT_act0 hZ1_slot hZ_prod
      hHs0 hHs1 hrunm1 hX' hX'_le ζ (by rw [hζ_re]; norm_num) R_sub hR_norm s
    have hexp := stage1_low_or_small_H_exponent hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv
      hx6 hV0 hzJ'0 hzc0 ht_pos.le (ht_small.trans (by norm_num))
      (show 0 ≤ z_rem_th - z_Jv - z_J' - z_coll by rw [hzT'_eq]; exact hzT_act0)
      hHs0 hHf_lo_t hbr
    rw [hzT'_eq] at hexp
    have hexp_le : max H_sub ((H_sub + 5 * max 0 r_unm) / 6) + z_T_act + 1 / 100 ≤
        1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t := by
      dsimp only [u_sel, H_free, H_th, r_unm, z_rem_th] at hexp ⊢
      linarith only [hexp, ht_pos]
    exact hb.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1.le hexp_le) hC_ns.le)
      h1s_ns (by positivity) (mul_nonneg hC_ns.le (Real.rpow_nonneg hU_pos.le _)))
  have hCns_le : C_ns ≤ C_sf := by
    have hnn : 0 ≤ N_grid * (C_c2 + C_c3) :=
      mul_nonneg (by dsimp only [N_grid]; positivity) (by linarith only [hC_c2, hC_c3])
    dsimp only [C_sf]; linarith only [hnn]
  have hCsf_pos : 0 < C_sf := lt_of_lt_of_le hC_ns hCns_le
  by_cases hsmall_Hf : H_free ≤ max (1 / 10) (r_unm + 10 * D_dual.t)
  · -- Branch A: `H_free ≤ max (1/10) (r_unm + 10 * D_dual.t)` (`H_free ≤ 0` or `0 < H_free`).
    by_cases hHf_nonpos : H_free ≤ 0
    · have hmax0 : max 0 H_free = 0 := max_eq_left hHf_nonpos
      have hb := hns_wrap S_free 0 le_rfl zero_le_one (Or.inl (by norm_num))
        (fun u hu => hmax0 ▸ hS_norm u hu)
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCns_le (Real.rpow_nonneg hU_pos.le _))
        (by positivity))
    · have hHf_pos : 0 < H_free := not_le.mp hHf_nonpos
      have hmaxH : max 0 H_free = H_free := max_eq_right hHf_pos.le
      have hb := hns_wrap S_free H_free hHf_pos.le hHf_hi (Or.inr ⟨rfl, hsmall_Hf⟩)
        (fun u hu => hmaxH ▸ hS_norm u hu)
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCns_le (Real.rpow_nonneg hU_pos.le _))
        (by positivity))
  · -- Branch B: `max (1/10) (r_unm + 10 * D_dual.t) < H_free ≤ 1`.
    have hHf_gt : max (1 / 10) (r_unm + 10 * D_dual.t) < H_free := not_le.mp hsmall_Hf
    have hHf_lo10 : 1 / 10 < H_free := (le_max_left _ _).trans_lt hHf_gt
    have hHf_lo3 : 3 / 100 ≤ H_free := by linarith only [hHf_lo10]
    have hmaxH : max 0 H_free = H_free := max_eq_right (by linarith only [hHf_lo10])
    let S_low := S_free.filter (fun u => rowNorm u < Z_dual ^ (1 / 100 : ℝ))
    let S_high := S_free.filter (fun u => Z_dual ^ (1 / 100 : ℝ) ≤ rowNorm u)
    have hsplit_S : ∀ f : FreeRow → ℝ,
        (∑ u ∈ S_free, f u) = (∑ u ∈ S_low, f u) + (∑ u ∈ S_high, f u) := by
      intro f
      dsimp only [S_low, S_high]
      have h := Finset.sum_filter_add_sum_filter_not S_free (fun u => rowNorm u < Z_dual ^ (1 / 100 : ℝ)) f
      simp only [not_lt] at h
      exact h.symm
    have hlow_norm : ∀ u ∈ S_low, rowNorm u ≤ U ^ (3 / 100 : ℝ) := by
      intro u hu
      have hlt : rowNorm u < Z_dual ^ (1 / 100 : ℝ) := (Finset.mem_filter.mp hu).2
      have hZd_100 : Z_dual ^ (1 / 100 : ℝ) ≤ U ^ (3 / 100 : ℝ) := by
        dsimp only [Z_dual]
        rw [← Real.rpow_mul hU_pos.le]
        apply Real.rpow_le_rpow_of_exponent_le hU1.le
        rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ (by positivity)]
        linarith only [hd_lo]
      exact hlt.le.trans hZd_100
    have hlow_bound := hns_wrap S_low (3 / 100) (by norm_num) (by norm_num) (Or.inl le_rfl) hlow_norm
    -- Partition `S_high` into buffered detector bins `(i_bin, k_bin)` via `exists_detector_buffered_bin`!
    let T_dual := Z_dual ^ τ_dual
    have hexp_Zd : 1 ≤ 3 / (2 * d_outer) := (one_le_div (by positivity)).mpr (by linarith only [hd_hi])
    have hZd_ge_U : U ≤ Z_dual :=
      (Real.rpow_one U).symm.trans_le (Real.rpow_le_rpow_of_exponent_le hU1.le hexp_Zd)
    have hT_gt2 : 2 < T_dual :=
      hZ_T Z_dual (((le_max_right 2 Z_T).trans ((le_max_right _ _).trans (le_max_right _ _))).trans
        (hU.trans hZd_ge_U))
    let fam (u : FreeRow) := sourceDetectorFamily F_dual.S F_dual.exclusions.prime
      (deletedBase data).inverse u (rayCubeFamily F_dual.modulus ⊤ le_top u)
    have hbin_ex : ∀ u : FreeRow, ∃ p : ℕ × ℕ,
        1 ≤ p.1 ∧ p.1 ≤ n_bins ∧ p.2 ≤ n_bins ∧
        let a := 51 / 100 + D_dual.e * (p.2 : ℝ)
        a ≤ 1 ∧
        a ≤ detectorMaximum (fam u) (3 * (p.1 : ℝ) * T_dual) ∧
        detectorMaximum (fam u) (3 * (p.1 + 1 : ℕ) * T_dual) < a + 2 * D_dual.e := by
      intro u
      obtain ⟨i_b, k_b, hi1, hi2, ha1, halo, _, hnext_b, _, _⟩ :=
        ProbeHighRowFamily.exists_detector_buffered_bin (fam u) T_dual D_dual.e
          hT_gt2 he_pos n_bins hn_bins_pos hn_bins_width
      have hk_le : k_b ≤ n_bins := by
        have h1 : D_dual.e * (k_b : ℝ) ≤ 49 / 100 := by linarith only [ha1]
        have h2 : D_dual.e * (k_b : ℝ) ≤ D_dual.e * (n_bins : ℝ) := by linarith only [h1, hn_bins_width]
        have h3 : (k_b : ℝ) ≤ (n_bins : ℝ) := le_of_mul_le_mul_left h2 he_pos
        exact_mod_cast h3
      exact ⟨(i_b, k_b), hi1, hi2, hk_le, ha1, halo, hnext_b⟩
    let pick : FreeRow → ℕ × ℕ := fun u => Classical.choose (hbin_ex u)
    have hpick : ∀ u : FreeRow,
        1 ≤ (pick u).1 ∧ (pick u).1 ≤ n_bins ∧ (pick u).2 ≤ n_bins ∧
        51 / 100 + D_dual.e * ((pick u).2 : ℝ) ≤ 1 ∧
        51 / 100 + D_dual.e * ((pick u).2 : ℝ) ≤ detectorMaximum (fam u) (3 * ((pick u).1 : ℝ) * T_dual) ∧
        detectorMaximum (fam u) (3 * ((pick u).1 + 1 : ℕ) * T_dual) <
          (51 / 100 + D_dual.e * ((pick u).2 : ℝ)) + 2 * D_dual.e :=
      fun u => Classical.choose_spec (hbin_ex u)
    let grid_set : Finset (ℕ × ℕ) := Finset.Icc 1 n_bins ×ˢ Finset.Iic n_bins
    have hcard_grid : (grid_set.card : ℝ) = N_grid := by
      dsimp only [grid_set, N_grid]
      rw [Finset.card_product, Nat.card_Icc, Nat.card_Iic]
      have : n_bins + 1 - 1 = n_bins := Nat.add_sub_cancel _ _
      rw [this]
    have hmaps_grid : ∀ u ∈ S_high, pick u ∈ grid_set := by
      intro u _
      obtain ⟨hi1, hi2, hk, _⟩ := hpick u
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hi1, hi2⟩, Finset.mem_Iic.mpr hk⟩
    have hC23_pos : 0 < C_c2 + C_c3 := by linarith only [hC_c2, hC_c3]
    -- Bound each `(i_bin, k_bin) ∈ grid_set` fiber by `(C_c2 + C_c3) * U ^ (...) * (1 + |s|)^(2 * J_sf)`.
    have hcell_bound : ∀ ik ∈ grid_set,
        let rows_ik := S_high.filter (fun u => pick u = ik)
        (∑ u ∈ rows_ik,
          ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
              (childLogTest wFresh s) X' 0 0 *
            ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) ≤
        (C_c2 + C_c3) * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_sf) := by
      intro ik hik rows_ik
      by_cases hne_ik : rows_ik.Nonempty
      · obtain ⟨u₀, hu₀⟩ := hne_ik
        have hu₀_eq : pick u₀ = ik := (Finset.mem_filter.mp hu₀).2
        obtain ⟨hi1, hi2, _, ha1, _, _⟩ := hpick u₀
        rw [hu₀_eq] at hi1 hi2 ha1
        let a_ik : ℝ := 51 / 100 + D_dual.e * (ik.2 : ℝ)
        have ha_lo_ik : 51 / 100 ≤ a_ik := by
          have hnn := mul_nonneg he_pos.le (Nat.cast_nonneg ik.2)
          dsimp only [a_ik]; linarith only [hnn]
        -- `detectorMaximum_le_seven_eighths` gives `a_ik ≤ 7/8`, hence `2 * a_ik - 1 ≤ 3/4`!
        have ha_78 : a_ik ≤ 7 / 8 := by
          have hlo0 := (hpick u₀).2.2.2.2.1
          rw [hu₀_eq] at hlo0
          exact hlo0.trans (detectorMaximum_le_seven_eighths (fam u₀) _)
        have hν_34 : 2 * a_ik - 1 ≤ 3 / 4 := by linarith only [ha_78]
        have hrows_ik_norm : ∀ u ∈ rows_ik, Z_dual ^ (1 / 100 : ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U ^ H_free := by
          intro u hu
          have hu_hi := (Finset.mem_filter.mp hu).1
          exact ⟨(Finset.mem_filter.mp hu_hi).2, hmaxH ▸ hS_norm u (Finset.mem_filter.mp hu_hi).1⟩
        have hrows_ik_next : ∀ u ∈ rows_ik,
            detectorMaximum (fam u) (3 * (ik.1 + 1 : ℕ) * T_dual) < a_ik + 2 * D_dual.e := by
          intro u hu
          have hp_eq : pick u = ik := (Finset.mem_filter.mp hu).2
          have hn := (hpick u).2.2.2.2.2
          rwa [hp_eq] at hn
        have hrows_ik_curr : ∀ u ∈ rows_ik,
            a_ik ≤ detectorMaximum (fam u) ((3 * ik.1 : ℕ) * T_dual) := by
          intro u hu
          have hp_eq : pick u = ik := (Finset.mem_filter.mp hu).2
          have hc := (hpick u).2.2.2.2.1
          rw [hp_eq] at hc
          have hcast : 3 * (ik.1 : ℝ) * T_dual = ((3 * ik.1 : ℕ) : ℝ) * T_dual := by push_cast; ring
          rwa [hcast] at hc
        by_cases hc2_cond : 2 * a_ik - 1 ≤ 11 / 25 ∨
            θ * (25 / 3) * (stage1Line r - (1 - r) / 2) ≤ z_J' + z_coll
        · have hcase_ik : 2 * a_ik - 1 ≤ 11 / 25 ∨
              (2 * a_ik - 1 ≤ 3 / 4 ∧ θ * (25 / 3) * (stage1Line r - (1 - r) / 2) ≤ z_J' + z_coll) :=
            hc2_cond.imp id (fun h => ⟨hν_34, h⟩)
          have hb2 := hc2 U (((le_max_right _ _).trans (le_max_left _ _)).trans hU)
            hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hx6 hV0 hzJ'0 hzc0
            hHf_gt hHf_hi hX' hX'_le T'
            (show (∑ j ∈ T', D.ell j / d_outer) ≤ z_rem_th - z_Jv - z_J' - z_coll from hzT'_eq.symm.le)
            hi1 hi2 ha_lo_ik ha1 hcase_ik
            rows_ik hrows_ik_norm hrows_ik_next ζ hζ_re hζ_im s
          exact hb2.trans (mul_le_mul
            (mul_le_mul_of_nonneg_right (by linarith only [hC_c3]) (Real.rpow_nonneg hU_pos.le _))
            h1s_c2 (by positivity) (mul_nonneg hC23_pos.le (Real.rpow_nonneg hU_pos.le _)))
        · have hc2_not := not_or.mp hc2_cond
          have hν_gt : 11 / 25 < 2 * a_ik - 1 := not_le.mp hc2_not.1
          have hzJ_lt : z_J' + z_coll < θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := not_le.mp hc2_not.2
          have hb3 := hc3 U (((le_max_left _ _).trans (le_max_right _ _)).trans hU)
            hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hx6 hV0 hzJ'0 hzc0
            hHf_lo3 hHf_hi hrunm1 hX' hX'_le hzJ_lt.le T'
            (show (1 - θ) * ((1 - r) / 2) + θ * stage1RemWidth r - z_Jv - z_J' - z_coll =
              ∑ j ∈ T', D.ell j / d_outer from hzT'_eq)
            hi1 hi2
            hν_gt.le hν_34 rows_ik hrows_ik_norm hrows_ik_next hrows_ik_curr ζ hζ_re hζ_im s
          have hexp_up : 1 - 3 * ell - 5 * u_sel - x6 ≤ 1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t := by
            linarith only [ht_pos]
          exact hb3.trans (mul_le_mul
            (mul_le_mul (by linarith only [hC_c2]) (Real.rpow_le_rpow_of_exponent_le hU1.le hexp_up)
              (Real.rpow_nonneg hU_pos.le _) hC23_pos.le)
            h1s_c3 (by positivity) (mul_nonneg hC23_pos.le (Real.rpow_nonneg hU_pos.le _)))
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne_ik, Finset.sum_empty]
        exact mul_nonneg (mul_nonneg hC23_pos.le (Real.rpow_nonneg hU_pos.le _)) (by positivity)
    have hhigh_sum :
        (∑ u ∈ S_high,
          ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
              (childLogTest wFresh s) X' 0 0 *
            ∏ j ∈ T', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (U ^ (D.ell j / d_outer)) ζ‖ ^ 2) ≤
        N_grid * (C_c2 + C_c3) * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) *
          (1 + |s|) ^ (2 * J_sf) := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps_grid]
      calc _ ≤ ∑ _ik ∈ grid_set,
              ((C_c2 + C_c3) * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_sf)) :=
            Finset.sum_le_sum hcell_bound
        _ = (grid_set.card : ℝ) *
              ((C_c2 + C_c3) * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_sf)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = _ := by rw [hcard_grid]; ring
    rw [hsplit_S]
    calc _ ≤ C_ns * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_sf) +
            N_grid * (C_c2 + C_c3) * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) *
              (1 + |s|) ^ (2 * J_sf) := add_le_add hlow_bound hhigh_sum
      _ = (C_ns + N_grid * (C_c2 + C_c3)) *
            U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_sf) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp only [C_sf]; linarith only []) (Real.rpow_nonneg hU_pos.le _))
          (by positivity)

end Stage1ParentPoissonEnergy

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
