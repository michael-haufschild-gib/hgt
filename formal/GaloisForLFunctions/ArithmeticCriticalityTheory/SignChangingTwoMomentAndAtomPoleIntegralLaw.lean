import GaloisForLFunctions.ArithmeticCriticalityTheory.ExtraJumpVisibilityThresholdAtInfinity
import GaloisForLFunctions.ArithmeticCriticalityTheory.SignedSuperpositionInfinityFailure
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateTwoSidedRepresentation
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeAtomVersusPoleClassification
import GaloisForLFunctions.BiScaleUncertainty.PowerNodeRemovalLaw

/-!
# Sign-Changing Two-Moment Positivity, Harmonic Radical Collar Law, and Integrated Atom-vs-Pole Separation

This module connects `ArithmeticCriticalityTheory`, `ArithmeticIncidencePositivity`, and
`BiScaleUncertainty` to establish four unconditional families of arithmetic positivity, moment
cancellation, and collar-integral dominance theorems:

1. **Quadratic Folded Potential Density & Two-Moment Sign-Reversal Positivity
   (`quadraticFoldedPotential_profileGauge_eq_neg_mul_poleFreeWeilOperator`,
   `tendsto_quadraticFoldedPotential_profileGauge_div_nhdsGT_zero`,
   `exists_both_ends_quadraticFoldedPotential_pos_of_opposite_moments`):**
   In `OddSupersolutionCriterion`, the Doob-folded ground-state representation
   `markovEnergy(Φ(ω u)) = groundRemainder ω u + 2 ∫_{x>0} u(x)^2 quadraticFoldedPotential ω x dx`
   holds for **every** odd `C²` gauge `ω` without any sign condition. For `ω = M / Φ`, every
   nonnegative profile `M ≥ 0` on `(0, ∞)` has `deriv M 0 ≥ 0`, `jumpMeasureMoment M > 0`, and
   `∫_{r>0} M(r) cosh(r/2) dr > 0`, forcing the quadratic folded potential density to be negative
   at both ends of the half-line. Dropping positivity of `M` decouples the local sign of `M` from
   its global jump-measure and cosh moments:
   - Near `0⁺`, `quadraticFoldedPotential (M / Φ) x / x → -2 * deriv M 0 * jumpMeasureMoment M`,
     so opposite signs between the origin slope `deriv M 0` and `jumpMeasureMoment M` make
     `quadraticFoldedPotential (M / Φ) x > 0` on an origin window `(0, δ)`.
   - Near `+∞`, opposite signs between the asymptotic sign of `M` on `[X₀, ∞)` and the global
     cosh moment `∫_{r>0} M(r) cosh(r/2) dr` make `quadraticFoldedPotential (M / Φ) x > 0` on a
     half-line `[X, ∞)`.

2. **Exact Origin Moment Identity `jumpMeasureMoment (shiftDifference a) = shiftedCollarMass a 0`,
   Two-Shift Moment Cancellation, and the Harmonic Radical (`σ = 0`) Folded Collar Law
   (`jumpMeasureMoment_shiftDifference_eq_shiftedCollarMass_zero`,
   `jumpMeasureMoment_originBalancedProfile_eq_zero`,
   `quadraticFoldedPotential_spanGroundState_of_poleFree`):**
   For every shift `a > 0`, the origin value of the reflected collar mass `shiftedCollarMass a 0`
   equals `jumpMeasureMoment (shiftDifference a) > 0`. On the span `spanGroundState s c a`,
   restricted to the harmonic radical `spanSourceCoefficient s c a = 0` (where the two-sided
   Schrödinger defect vanishes identically), the unbounded pole term in the folded defect cancels
   and the quadratic folded potential density reduces to
   `-2 * spanShiftDifference s c a x * ∑ j ∈ s, c j * shiftedCollarMass (a j) x`.
   Furthermore, the explicit sign-changing two-shift profile
   `originBalancedProfile a b y = shiftedCollarMass b 0 * shiftDifference a y - shiftedCollarMass a 0 * shiftDifference b y`
   has `jumpMeasureMoment (originBalancedProfile a b) = 0`, annihilating the `O(Φ(x))` origin
   obstruction identically.

3. **Integrated Atom-Versus-Pole Dominance Along Shifted Ground-State Collars
   (`collarPolarMass_lt_collarAtomMass_of_mem_atomDominatedModuli`,
   `reflectedDifferencePolarMass_le_atomMass_of_mem_atomDominatedModuli`,
   `collarAtomMass_eq_zero_and_collarPolarMass_pos_of_not_isPrimePow`):**
   Integrating the anti-diagonal classification of `PrimeAtomVersusPoleClassification` against the
   shifted ground-state collar kernel `shiftDifference a x * shiftDifference a (log n - x)` proves
   that for every shift `a > 0` and every `n ∈ atomDominatedModuli = {2, 3, 4, 5, 7}`, the
   integrated prime atom strictly dominates the integrated polar weight with an explicit positive
   surplus lower bound, while for every composite non-prime-power `n ≥ 2` (such as `n = 6`), the
   integrated prime atom vanishes and the integrated polar weight is strictly positive.

4. **Unconditional Separation Between Anti-Diagonal Atom Dominance and Bi-Scale Bathtub Gain at
   `n = 4` and `n = 6` (`four_atomDominated_and_dyadic_ternary_slack_law`,
   `six_polarDominated_and_biscale_incidenceGain_pos`):**
   Combining the anti-diagonal classification with `IncidenceGainOfTheSingleIntegerBathtub` and
   `PowerNodeRemovalLaw` exhibits a sharp arithmetic reversal between `n = 4 = 2²` and
   `n = 6 = 2 · 3`:
   - `n = 4` is the unique composite prime power whose explicit-formula atom dominates the polar
     weight on the entire anti-diagonal (`4 ∈ atomDominatedModuli`), yet `4 ∈ powerNodes 2` yields
     zero incidence gain over the dyadic bathtub (`powerNodes 2`) while yielding positive gain
     `0 < incidenceGain 3 4` over the ternary bathtub (`powerNodes 3`).
   - `n = 6` carries zero von Mangoldt atom (`¬ IsPrimePow 6`), yet `6 ∉ powerNodes 2` and
     `6 ∉ powerNodes 3`, so adjoining blindness at the composite node `6` strictly improves **both**
     the dyadic bathtub (`0 < incidenceGain 2 6`) and the ternary bathtub (`0 < incidenceGain 3 6`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.BiScaleUncertainty

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

variable {ι : Type*}

/-! ## 1. Quadratic Folded Potential Density and Two-Moment Sign-Reversal Positivity -/

/-- The quadratic folded potential density `ω(x) (𝓛_N ω(x) − Φ(x) cosh(x/2) ω(x))` appearing in
`markovEnergy_phiDoob_eq_groundRemainder_add_potential` for an arbitrary (possibly sign-changing)
odd gauge `ω`. -/
def quadraticFoldedPotential (ω : ℝ → ℝ) (x : ℝ) : ℝ :=
  ω x * (foldedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x)

/-- Exact representation of `markovEnergy (Φ(ω u))` in terms of `groundRemainder` and
`quadraticFoldedPotential` for any odd `C²` gauge `ω` (with no sign condition on `ω`). -/
theorem markovEnergy_phiDoob_eq_groundRemainder_add_quadraticFoldedPotential {ω u : ℝ → ℝ}
    (hω : ContDiff ℝ 2 ω) (hodd : ∀ x, ω (-x) = -ω x)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    (hadm : FoldedAdmissible ω u) :
    markovEnergy (fun x => (phiDoobTest (fun y => ω y * u y) x : ℂ)) =
      groundRemainder ω u +
        2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * quadraticFoldedPotential ω x := by
  rw [markovEnergy_phiDoob_eq_groundRemainder_add_potential hω hodd hu huc heven hadm]
  unfold quadraticFoldedPotential
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring

/-- For a profile gauge `ω = M / Φ` with `|M|, |M'| ≤ C e^{−8|y|}`, the quadratic folded potential
density on `[0, ∞)` is `-M(x) * poleFreeWeilOperator (M ∘ abs) x`. -/
theorem quadraticFoldedPotential_profileGauge_eq_neg_mul_poleFreeWeilOperator {M : ℝ → ℝ} {C : ℝ}
    (hM : Differentiable ℝ M) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) {x : ℝ} (hx : 0 ≤ x) :
    quadraticFoldedPotential (fun y => M y / riemannKernelReal y) x =
      -(M x * poleFreeWeilOperator (fun y => M (|y|)) x) := by
  unfold quadraticFoldedPotential
  rw [foldedGenerator_profileGauge_sub_potential_of_decay hM hdec hdec' hx]
  have hΦ := (riemannKernelReal_pos x).ne'
  field_simp

/-- **Exact Quadratic Origin Slope-Moment Law.**
For any `M ∈ C¹` with `M(0) = 0` and `|M|, |M'| ≤ C e^{−8|y|}`, the quadratic folded potential
density divided by `x` converges as `x → 0⁺` to `-2 * deriv M 0 * jumpMeasureMoment M`. -/
theorem tendsto_quadraticFoldedPotential_profileGauge_div_nhdsGT_zero {M : ℝ → ℝ} {C : ℝ}
    (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0)
    (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) :
    Tendsto (fun x => quadraticFoldedPotential (fun y => M y / riemannKernelReal y) x / x)
      (𝓝[>] 0) (𝓝 (-(2 * deriv M 0 * jumpMeasureMoment M))) := by
  have hd : HasDerivAt M (deriv M 0) 0 := (hM.differentiable one_ne_zero 0).hasDerivAt
  have hslope : Tendsto (fun x => M x / x) (𝓝[>] 0) (𝓝 (deriv M 0)) := by
    have h1 := hd.tendsto_slope_zero_right
    refine h1.congr' (Eventually.of_forall fun x => ?_)
    simp [hM0, smul_eq_mul, div_eq_inv_mul]
  have hsrc := tendsto_foldedSource_div_nhdsGT_zero hM hM0 hdec hdec'
  have hmul := hslope.mul hsrc
  have hlim : deriv M 0 * -(2 * jumpMeasureMoment M) = -(2 * deriv M 0 * jumpMeasureMoment M) := by
    ring
  rw [hlim] at hmul
  refine hmul.congr' (Eventually.of_forall fun x => ?_)
  simp only [quadraticFoldedPotential]
  have hΦ := (riemannKernelReal_pos x).ne'
  field_simp

/-- **Origin Positivity via Opposite-Sign Jump Moment.**
If `M ∈ C¹` satisfies `M(0) = 0`, `|M|, |M'| ≤ C e^{−8|y|}`, and its origin slope `deriv M 0`
has strictly opposite sign to `jumpMeasureMoment M` (`deriv M 0 * jumpMeasureMoment M < 0`), then
`quadraticFoldedPotential (M / Φ)` is strictly positive on an origin window `(0, δ)`. -/
theorem exists_origin_window_quadraticFoldedPotential_pos_of_deriv_mul_jumpMeasureMoment_neg
    {M : ℝ → ℝ} {C : ℝ} (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0)
    (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|)))
    (hopp : deriv M 0 * jumpMeasureMoment M < 0) :
    ∃ δ > 0, ∀ x ∈ Ioo 0 δ,
      0 < quadraticFoldedPotential (fun y => M y / riemannKernelReal y) x := by
  have hlim : 0 < -(2 * deriv M 0 * jumpMeasureMoment M) := by linarith
  have hev := (tendsto_quadraticFoldedPotential_profileGauge_div_nhdsGT_zero hM hM0 hdec
    hdec').eventually (lt_mem_nhds hlim)
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have h := hsub hx
  simp only [mem_setOf_eq] at h
  exact (div_pos_iff_of_pos_right hx.1).mp h

/-- **Necessary Origin Moment Sign Law.**
If `quadraticFoldedPotential (M / Φ) ≥ 0` on `(0, δ)` for some `δ > 0`, then
`deriv M 0 * jumpMeasureMoment M ≤ 0`. -/
theorem deriv_mul_jumpMeasureMoment_nonpos_of_quadraticFoldedPotential_nonneg_near_zero
    {M : ℝ → ℝ} {C : ℝ} (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0)
    (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) {δ : ℝ} (hδ : 0 < δ)
    (hnn : ∀ x ∈ Ioo 0 δ,
      0 ≤ quadraticFoldedPotential (fun y => M y / riemannKernelReal y) x) :
    deriv M 0 * jumpMeasureMoment M ≤ 0 := by
  have h := tendsto_quadraticFoldedPotential_profileGauge_div_nhdsGT_zero hM hM0 hdec hdec'
  have hge : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      0 ≤ quadraticFoldedPotential (fun y => M y / riemannKernelReal y) x / x := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    exact div_nonneg (hnn x hx) hx.1.le
  have hlim := ge_of_tendsto h hge
  linarith

/-- **Infinity Positivity via Opposite-Sign Cosh Moment.**
If `M ∈ C¹` with `M(0) = 0` and `|M|, |M'| ≤ C e^{−8|y|}` has sign `ε` on `[X₀, ∞)`
(`∀ x ≥ X₀, 0 < ε * M x`) and its half-line cosh moment has strictly opposite sign to `ε`
(`ε * ∫_{r>0} M(r) cosh(r/2) dr < 0`), then `quadraticFoldedPotential (M / Φ)` is strictly positive
on a half-line `[X, ∞)`. -/
theorem exists_atTop_quadraticFoldedPotential_pos_of_sign_mul_coshMoment_neg
    {M : ℝ → ℝ} {C ε X₀ : ℝ} (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0)
    (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|)))
    (hsign : ∀ x, X₀ ≤ x → 0 < ε * M x)
    (hopp : ε * (∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2)) < 0) :
    ∃ X : ℝ, X₀ ≤ X ∧ ∀ x, X ≤ x →
      0 < quadraticFoldedPotential (fun y => M y / riemannKernelReal y) x := by
  have hlim : 0 < ε * -(2 * ∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2)) := by linarith
  have ht := (tendsto_foldedSource_div hM hM0 hdec hdec').const_mul ε
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (ht.eventually (lt_mem_nhds hlim))
  refine ⟨max X₀ X₁, le_max_left _ _, fun x hx => ?_⟩
  have hx₀ : X₀ ≤ x := (le_max_left _ _).trans hx
  have hx₁ : X₁ ≤ x := (le_max_right _ _).trans hx
  have h1 : 0 < ε * ((foldedGenerator (fun y => M y / riemannKernelReal y) x -
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) /
        (riemannKernelReal x * Real.exp (x / 2))) := hX₁ x hx₁
  have h2 : 0 < ε * M x := hsign x hx₀
  have hε2 : 0 < ε ^ 2 := by
    have hε0 : ε ≠ 0 := fun h0 => by simp [h0] at h2
    exact sq_pos_of_ne_zero hε0
  have hprod : 0 < (ε * M x) * (ε * ((foldedGenerator (fun y => M y / riemannKernelReal y) x -
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) /
        (riemannKernelReal x * Real.exp (x / 2)))) * Real.exp (x / 2) :=
    mul_pos (mul_pos h2 h1) (Real.exp_pos _)
  have heq : (ε * M x) * (ε * ((foldedGenerator (fun y => M y / riemannKernelReal y) x -
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) /
        (riemannKernelReal x * Real.exp (x / 2)))) * Real.exp (x / 2) =
      ε ^ 2 * quadraticFoldedPotential (fun y => M y / riemannKernelReal y) x := by
    unfold quadraticFoldedPotential
    have hΦ := (riemannKernelReal_pos x).ne'
    have hexp := (Real.exp_pos (x / 2)).ne'
    field_simp
  rw [heq] at hprod
  exact pos_of_mul_pos_right hprod hε2.le

/-- **Simultaneous Two-End Positivity of the Quadratic Folded Potential for Sign-Changing Gauges.**
Whenever a sign-changing profile `M ∈ C¹` (`M(0) = 0`, `|M|, |M'| ≤ C e^{−8|y|}`) has origin slope
`deriv M 0` of opposite sign to `jumpMeasureMoment M` and tail sign `ε` on `[X₀, ∞)` of opposite
sign to `∫_{r>0} M(r) cosh(r/2) dr`, its quadratic folded potential density is strictly positive on
both an origin window `(0, δ)` and a half-line `[X, ∞)`. -/
theorem exists_both_ends_quadraticFoldedPotential_pos_of_opposite_moments
    {M : ℝ → ℝ} {C ε X₀ : ℝ} (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0)
    (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|)))
    (hopp0 : deriv M 0 * jumpMeasureMoment M < 0)
    (hsign : ∀ x, X₀ ≤ x → 0 < ε * M x)
    (hopp_inf : ε * (∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2)) < 0) :
    (∃ δ > 0, ∀ x ∈ Ioo 0 δ,
      0 < quadraticFoldedPotential (fun y => M y / riemannKernelReal y) x) ∧
    (∃ X : ℝ, X₀ ≤ X ∧ ∀ x, X ≤ x →
      0 < quadraticFoldedPotential (fun y => M y / riemannKernelReal y) x) :=
  ⟨exists_origin_window_quadraticFoldedPotential_pos_of_deriv_mul_jumpMeasureMoment_neg
      hM hM0 hdec hdec' hopp0,
    exists_atTop_quadraticFoldedPotential_pos_of_sign_mul_coshMoment_neg
      hM hM0 hdec hdec' hsign hopp_inf⟩

/-! ## 2. Exact Origin Moment Identity for Shifted Ground States, Two-Shift Moment Cancellation, and the Harmonic Radical Collar Law -/

/-- **Exact Origin Moment Identity for Shifted Ground States.**
For every shift `a > 0`, the jump-measure moment `jumpMeasureMoment (shiftDifference a)` is equal
to the origin value of the reflected collar mass `shiftedCollarMass a 0`. -/
theorem jumpMeasureMoment_shiftDifference_eq_shiftedCollarMass_zero {a : ℝ} (ha : 0 < a) :
    jumpMeasureMoment (shiftDifference a) = shiftedCollarMass a 0 := by
  unfold jumpMeasureMoment shiftedCollarMass
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [sub_zero, max_eq_left (shiftDifference_pos ha ht).le]
  · refine tsum_congr fun n => ?_
    rw [sub_zero, max_eq_left (shiftDifference_nonneg_of_nonneg ha.le (Real.log_natCast_nonneg n))]

/-- For every shift `a > 0`, the origin reflected collar mass `shiftedCollarMass a 0` is strictly
positive. -/
theorem shiftedCollarMass_zero_pos {a : ℝ} (ha : 0 < a) :
    0 < shiftedCollarMass a 0 := by
  rw [← jumpMeasureMoment_shiftDifference_eq_shiftedCollarMass_zero ha]
  obtain ⟨C, hdec, hdec'⟩ := exists_shiftDifference_decay_eight a
  exact jumpMeasureMoment_pos ((contDiff_shiftDifference_two a).of_le (by norm_num))
    (odd_apply_zero (shiftDifference_neg a)) hdec'
    (fun y hy => shiftDifference_nonneg_of_nonneg ha.le hy)
    (Real.log_pos one_lt_two) (shiftDifference_pos ha (Real.log_pos one_lt_two))

/-- Arch-Levy integrability of `shiftDifference a` on `(0, ∞)` for every `a : ℝ`. -/
theorem integrableOn_archLevy_shiftDifference (a : ℝ) :
    IntegrableOn (fun t => archLevyDensity t * shiftDifference a t) (Ioi 0) := by
  obtain ⟨C, -, hdec'⟩ := exists_shiftDifference_decay_eight a
  have hM : ContDiff ℝ 1 (shiftDifference a) := (contDiff_shiftDifference_two a).of_le (by norm_num)
  have hM0 : shiftDifference a 0 = 0 := odd_apply_zero (shiftDifference_neg a)
  have hlin : ∀ t, |shiftDifference a t| ≤ C * |t| := fun t => by
    simpa [hM0] using abs_sub_le_of_decay hM hdec' t 0
  refine (integrableOn_archLevyDensity_mul_id.const_mul C).mono'
    (measurable_archLevyDensity.mul (continuous_shiftDifference a).measurable).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht0 : 0 < t := mem_Ioi.mp ht
  have hω := archLevyDensity_pos ht0
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hω]
  have h1 := hlin t
  rw [abs_of_pos ht0] at h1
  nlinarith

/-- Prime-atom summability of `shiftDifference a` at `log n` for every `a > 0`. -/
theorem summable_atom_shiftDifference_log {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => vonMangoldtAtom n * shiftDifference a (Real.log n) := by
  refine (summable_atom_max_shiftDifference a 0).congr fun n => ?_
  rw [sub_zero, max_eq_left (shiftDifference_nonneg_of_nonneg ha.le (Real.log_natCast_nonneg n))]

/-- **Linearity of `jumpMeasureMoment` on `spanShiftDifference`.**
For any finite superposition `spanShiftDifference s c a` with positive shifts `a j > 0`, its
jump-measure moment is `∑ j ∈ s, c j * shiftedCollarMass (a j) 0`. -/
theorem jumpMeasureMoment_spanShiftDifference_eq_sum_shiftedCollarMass_zero
    {s : Finset ι} {c a : ι → ℝ} (ha : ∀ j ∈ s, 0 < a j) :
    jumpMeasureMoment (spanShiftDifference s c a) =
      ∑ j ∈ s, c j * shiftedCollarMass (a j) 0 := by
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t * spanShiftDifference s c a t) =
      ∑ j ∈ s, c j * ∫ t in Ioi (0 : ℝ), archLevyDensity t * shiftDifference (a j) t := by
    have e : (fun t => archLevyDensity t * spanShiftDifference s c a t) =
        fun t => ∑ j ∈ s, c j * (archLevyDensity t * shiftDifference (a j) t) := by
      funext t
      unfold spanShiftDifference
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum s fun j _ =>
      (integrableOn_archLevy_shiftDifference (a j)).const_mul (c j)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hprime : (∑' n : ℕ, vonMangoldtAtom n * spanShiftDifference s c a (Real.log n)) =
      ∑ j ∈ s, c j * ∑' n : ℕ, vonMangoldtAtom n * shiftDifference (a j) (Real.log n) := by
    have e : (fun n : ℕ => vonMangoldtAtom n * spanShiftDifference s c a (Real.log n)) =
        fun n => ∑ j ∈ s, c j * (vonMangoldtAtom n * shiftDifference (a j) (Real.log n)) := by
      funext n
      unfold spanShiftDifference
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, Summable.tsum_finsetSum fun j hj =>
      (summable_atom_shiftDifference_log (ha j hj)).mul_left (c j)]
    exact Finset.sum_congr rfl fun j _ => tsum_mul_left
  unfold jumpMeasureMoment
  rw [harch, hprime, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_add, ← jumpMeasureMoment,
    jumpMeasureMoment_shiftDifference_eq_shiftedCollarMass_zero (ha j hj)]

/-- The explicit sign-changing two-shift profile `C_b(0) m_a − C_a(0) m_b` balanced at the origin. -/
def originBalancedProfile (a b y : ℝ) : ℝ :=
  shiftedCollarMass b 0 * shiftDifference a y - shiftedCollarMass a 0 * shiftDifference b y

/-- **Exact Two-Shift Origin Moment Cancellation.**
For any two positive shifts `a, b > 0`, the sign-changing combination `originBalancedProfile a b`
has identically zero jump-measure moment (`jumpMeasureMoment (originBalancedProfile a b) = 0`),
eliminating the `O(Φ(x))` origin obstruction that forces every nonnegative combination to fail. -/
theorem jumpMeasureMoment_originBalancedProfile_eq_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    jumpMeasureMoment (originBalancedProfile a b) = 0 := by
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t * originBalancedProfile a b t) =
      shiftedCollarMass b 0 * (∫ t in Ioi (0 : ℝ), archLevyDensity t * shiftDifference a t) -
        shiftedCollarMass a 0 * (∫ t in Ioi (0 : ℝ), archLevyDensity t * shiftDifference b t) := by
    have e : (fun t => archLevyDensity t * originBalancedProfile a b t) =
        fun t => shiftedCollarMass b 0 * (archLevyDensity t * shiftDifference a t) -
          shiftedCollarMass a 0 * (archLevyDensity t * shiftDifference b t) := by
      funext t; unfold originBalancedProfile; ring
    rw [e, integral_sub ((integrableOn_archLevy_shiftDifference a).const_mul _)
      ((integrableOn_archLevy_shiftDifference b).const_mul _),
      integral_const_mul, integral_const_mul]
  have hprime : (∑' n : ℕ, vonMangoldtAtom n * originBalancedProfile a b (Real.log n)) =
      shiftedCollarMass b 0 * (∑' n : ℕ, vonMangoldtAtom n * shiftDifference a (Real.log n)) -
        shiftedCollarMass a 0 * (∑' n : ℕ, vonMangoldtAtom n * shiftDifference b (Real.log n)) := by
    have e : (fun n : ℕ => vonMangoldtAtom n * originBalancedProfile a b (Real.log n)) =
        fun n => shiftedCollarMass b 0 * (vonMangoldtAtom n * shiftDifference a (Real.log n)) -
          shiftedCollarMass a 0 * (vonMangoldtAtom n * shiftDifference b (Real.log n)) := by
      funext n; unfold originBalancedProfile; ring
    rw [e, ((summable_atom_shiftDifference_log ha).mul_left _).tsum_sub
      ((summable_atom_shiftDifference_log hb).mul_left _), tsum_mul_left, tsum_mul_left]
  have hJa := jumpMeasureMoment_shiftDifference_eq_shiftedCollarMass_zero ha
  have hJb := jumpMeasureMoment_shiftDifference_eq_shiftedCollarMass_zero hb
  unfold jumpMeasureMoment at hJa hJb ⊢
  rw [harch, hprime]
  linear_combination shiftedCollarMass b 0 * hJa - shiftedCollarMass a 0 * hJb

/-- **Quadratic Folded Potential of a Finite Superposition of Shifted Ground States.**
For any finite superposition `spanGroundState s c a` with `a j > 0` and any `x > 0`,
`quadraticFoldedPotential (spanGroundState s c a) x` is twice the product of the test coordinate
`spanShiftDifference s c a x` and `σ sinh(x/2) − ∑ j ∈ s, c j * shiftedCollarMass (a j) x`. -/
theorem quadraticFoldedPotential_spanGroundState_eq {s : Finset ι} {c a : ι → ℝ}
    (ha : ∀ j ∈ s, 0 < a j) {x : ℝ} (hx : 0 < x) :
    quadraticFoldedPotential (spanGroundState s c a) x =
      2 * spanShiftDifference s c a x *
        (spanSourceCoefficient s c a * Real.sinh (x / 2) -
          ∑ j ∈ s, c j * shiftedCollarMass (a j) x) := by
  unfold quadraticFoldedPotential
  rw [foldedDefect_spanGroundState ha hx]
  have hmul := riemannKernelReal_mul_spanGroundState s c a x
  linear_combination 2 * (spanSourceCoefficient s c a * Real.sinh (x / 2) -
    ∑ j ∈ s, c j * shiftedCollarMass (a j) x) * hmul

/-- **Harmonic Radical (`σ = 0`) Folded Collar Law.**
When `spanSourceCoefficient s c a = 0` (so `spanGroundState s c a` lies in the harmonic radical of
the two-sided generator), the unbounded `sinh(x/2)` pole term in `quadraticFoldedPotential`
vanishes identically on `(0, ∞)`, leaving purely the signed collar pairing
`-2 * spanShiftDifference s c a x * ∑ j ∈ s, c j * shiftedCollarMass (a j) x`. -/
theorem quadraticFoldedPotential_spanGroundState_of_poleFree {s : Finset ι} {c a : ι → ℝ}
    (ha : ∀ j ∈ s, 0 < a j) (hσ : spanSourceCoefficient s c a = 0) {x : ℝ} (hx : 0 < x) :
    quadraticFoldedPotential (spanGroundState s c a) x =
      -(2 * spanShiftDifference s c a x * ∑ j ∈ s, c j * shiftedCollarMass (a j) x) := by
  rw [quadraticFoldedPotential_spanGroundState_eq ha hx, hσ, zero_mul, zero_sub, mul_neg]

/-! ## 3. Integrated Atom-Versus-Pole Dominance Along Shifted Ground-State Collars -/

/-- The integrated prime-power atom mass along the collar `(0, log n)` of a profile `M`. -/
def collarAtomMass (M : ℝ → ℝ) (n : ℕ) : ℝ :=
  vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n), M x * M (Real.log n - x)

/-- The integrated polar weight mass along the collar `(0, log n)` of a profile `M`. -/
def collarPolarMass (M : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) (Real.log n),
    M x * M (Real.log n - x) * crossingPolarWeight (Real.log n) x

/-- The profile-weighted reflected difference atom mass at modulus `n` (the `n`-th prime-power
summand of `reflectedDifferenceEnergy (shiftedGroundState a) u` when `M = shiftDifference a`). -/
def reflectedDifferenceAtomMass (M u : ℝ → ℝ) (n : ℕ) : ℝ :=
  vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
    M x * M (Real.log n - x) * (u x - u (Real.log n - x)) ^ 2

/-- The profile-weighted reflected difference polar mass at modulus `n`. -/
def reflectedDifferencePolarMass (M u : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) (Real.log n),
    M x * M (Real.log n - x) * crossingPolarWeight (Real.log n) x *
      (u x - u (Real.log n - x)) ^ 2

/-- Universal midpoint upper bound for `collarPolarMass` for any continuous nonnegative profile `M`
on `(0, ∞)`. -/
theorem collarPolarMass_le_midpoint_mul_integral {M : ℝ → ℝ} (hM : Continuous M)
    (hnn : ∀ x, 0 < x → 0 ≤ M x) (n : ℕ) :
    collarPolarMass M n ≤
      2 * Real.sinh (Real.log n / 4) ^ 2 *
        ∫ x in Ioo (0 : ℝ) (Real.log n), M x * M (Real.log n - x) := by
  unfold collarPolarMass
  have hMr : Continuous fun x => M (Real.log n - x) :=
    hM.comp (continuous_const.sub continuous_id)
  have hint1 : IntegrableOn (fun x => M x * M (Real.log n - x) *
      crossingPolarWeight (Real.log n) x) (Ioo (0 : ℝ) (Real.log n)) :=
    ((hM.mul hMr).mul (continuous_crossingPolarWeight _)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun x => 2 * Real.sinh (Real.log n / 4) ^ 2 *
      (M x * M (Real.log n - x))) (Ioo (0 : ℝ) (Real.log n)) :=
    (continuous_const.mul (hM.mul hMr)).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← integral_const_mul]
  refine setIntegral_mono_on hint1 hint2 measurableSet_Ioo fun x hx => ?_
  have hMx : 0 ≤ M x * M (Real.log n - x) :=
    mul_nonneg (hnn x hx.1) (hnn (Real.log n - x) (sub_pos.mpr hx.2))
  calc M x * M (Real.log n - x) * crossingPolarWeight (Real.log n) x
      ≤ M x * M (Real.log n - x) * (2 * Real.sinh (Real.log n / 4) ^ 2) :=
        mul_le_mul_of_nonneg_left (crossingPolarWeight_le_midpoint (Real.log n) x) hMx
    _ = 2 * Real.sinh (Real.log n / 4) ^ 2 * (M x * M (Real.log n - x)) := by ring

/-- Strict positivity of the collar autocorrelation integral of `shiftDifference a` for every
`a > 0` and `n ≥ 2`. -/
theorem integral_shiftDifference_collar_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 2 ≤ n) :
    0 < ∫ x in Ioo (0 : ℝ) (Real.log n),
      shiftDifference a x * shiftDifference a (Real.log n - x) := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hm := continuous_shiftDifference a
  have hmr : Continuous fun x => shiftDifference a (Real.log n - x) :=
    hm.comp (continuous_const.sub continuous_id)
  have hcont : Continuous fun x => shiftDifference a x * shiftDifference a (Real.log n - x) :=
    hm.mul hmr
  have hint : IntegrableOn (fun x => shiftDifference a x * shiftDifference a (Real.log n - x))
      (Ioo (0 : ℝ) (Real.log n)) :=
    hcont.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx =>
      mul_nonneg (shiftDifference_pos ha hx.1).le
        (shiftDifference_pos ha (sub_pos.mpr hx.2)).le) hint]
  have hsub : Ioo (0 : ℝ) (Real.log n) ⊆
      Function.support (fun x => shiftDifference a x * shiftDifference a (Real.log n - x)) ∩
        Ioo (0 : ℝ) (Real.log n) := fun x hx =>
    ⟨(mul_pos (shiftDifference_pos ha hx.1) (shiftDifference_pos ha (sub_pos.mpr hx.2))).ne', hx⟩
  calc (0 : ENNReal) < volume (Ioo (0 : ℝ) (Real.log n)) := by
        rw [Real.volume_Ioo, sub_zero]
        exact ENNReal.ofReal_pos.mpr hlog
    _ ≤ _ := measure_mono hsub

/-- **Strict Integrated Atom-Over-Pole Dominance on `{2, 3, 4, 5, 7}`.**
For every modulus `n ∈ atomDominatedModuli = {2, 3, 4, 5, 7}` and every shift `a > 0`, the
integrated prime atom mass along the collar of `ω_a` strictly exceeds the integrated polar weight
mass, with explicit positive lower bound
`(vonMangoldtAtom n - 2 * sinh(log n / 4)^2) * ∫_0^{log n} m_a(x) m_a(log n - x) dx`. -/
theorem collarPolarMass_lt_collarAtomMass_of_mem_atomDominatedModuli {a : ℝ} (ha : 0 < a)
    {n : ℕ} (hn : n ∈ atomDominatedModuli) :
    0 < (vonMangoldtAtom n - 2 * Real.sinh (Real.log n / 4) ^ 2) *
        (∫ x in Ioo (0 : ℝ) (Real.log n),
          shiftDifference a x * shiftDifference a (Real.log n - x)) ∧
      (vonMangoldtAtom n - 2 * Real.sinh (Real.log n / 4) ^ 2) *
        (∫ x in Ioo (0 : ℝ) (Real.log n),
          shiftDifference a x * shiftDifference a (Real.log n - x)) ≤
        collarAtomMass (shiftDifference a) n - collarPolarMass (shiftDifference a) n ∧
      collarPolarMass (shiftDifference a) n < collarAtomMass (shiftDifference a) n := by
  have hn2 := two_le_of_mem_atomDominatedModuli hn
  have hmid := crossingPolarWeight_lt_vonMangoldtAtom hn (Real.log n / 2)
  rw [crossingPolarWeight_midpoint] at hmid
  have hI := integral_shiftDifference_collar_pos ha hn2
  have hpos : 0 < (vonMangoldtAtom n - 2 * Real.sinh (Real.log n / 4) ^ 2) *
      ∫ x in Ioo (0 : ℝ) (Real.log n),
        shiftDifference a x * shiftDifference a (Real.log n - x) :=
    mul_pos (sub_pos.mpr hmid) hI
  have hle := collarPolarMass_le_midpoint_mul_integral (continuous_shiftDifference a)
    (fun x hx => (shiftDifference_pos ha hx).le) n
  unfold collarAtomMass
  exact ⟨hpos, by linarith, by linarith⟩

/-- **Profile-Weighted Reflected Difference Atom Dominance on `{2, 3, 4, 5, 7}`.**
For every `n ∈ atomDominatedModuli`, every shift `a > 0`, and every continuous profile `u`, the
reflected difference polar integral at `n` is bounded above by the reflected difference atom
integral. -/
theorem reflectedDifferencePolarMass_le_atomMass_of_mem_atomDominatedModuli {a : ℝ} (ha : 0 < a)
    {n : ℕ} (hn : n ∈ atomDominatedModuli) {u : ℝ → ℝ} (hu : Continuous u) :
    reflectedDifferencePolarMass (shiftDifference a) u n ≤
      reflectedDifferenceAtomMass (shiftDifference a) u n := by
  unfold reflectedDifferencePolarMass reflectedDifferenceAtomMass
  have hm := continuous_shiftDifference a
  have hmr : Continuous fun x => shiftDifference a (Real.log n - x) :=
    hm.comp (continuous_const.sub continuous_id)
  have hur : Continuous fun x => u (Real.log n - x) :=
    hu.comp (continuous_const.sub continuous_id)
  have hdiff : Continuous fun x => (u x - u (Real.log n - x)) ^ 2 := (hu.sub hur).pow 2
  have hint1 : IntegrableOn (fun x => shiftDifference a x * shiftDifference a (Real.log n - x) *
      crossingPolarWeight (Real.log n) x * (u x - u (Real.log n - x)) ^ 2)
      (Ioo (0 : ℝ) (Real.log n)) :=
    (((hm.mul hmr).mul (continuous_crossingPolarWeight _)).mul
      hdiff).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun x => vonMangoldtAtom n *
      (shiftDifference a x * shiftDifference a (Real.log n - x) * (u x - u (Real.log n - x)) ^ 2))
      (Ioo (0 : ℝ) (Real.log n)) :=
    (continuous_const.mul ((hm.mul hmr).mul hdiff)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  rw [← integral_const_mul]
  refine setIntegral_mono_on hint1 hint2 measurableSet_Ioo fun x hx => ?_
  have hMx : 0 ≤ shiftDifference a x * shiftDifference a (Real.log n - x) *
      (u x - u (Real.log n - x)) ^ 2 :=
    mul_nonneg (mul_nonneg (shiftDifference_pos ha hx.1).le
      (shiftDifference_pos ha (sub_pos.mpr hx.2)).le) (sq_nonneg _)
  have hlt := (crossingPolarWeight_lt_vonMangoldtAtom hn x).le
  calc shiftDifference a x * shiftDifference a (Real.log n - x) *
        crossingPolarWeight (Real.log n) x * (u x - u (Real.log n - x)) ^ 2
      = crossingPolarWeight (Real.log n) x *
          (shiftDifference a x * shiftDifference a (Real.log n - x) *
            (u x - u (Real.log n - x)) ^ 2) := by ring
    _ ≤ vonMangoldtAtom n *
          (shiftDifference a x * shiftDifference a (Real.log n - x) *
            (u x - u (Real.log n - x)) ^ 2) :=
        mul_le_mul_of_nonneg_right hlt hMx

/-- **Composite Non-Prime-Power Polar Dominance.**
For every composite `n ≥ 2` that is not a prime power (`¬ IsPrimePow n`, e.g. `n = 6`) and every
shift `a > 0`, the integrated prime atom vanishes while the integrated polar weight along the
collar `(0, log n)` is strictly positive. -/
theorem collarAtomMass_eq_zero_and_collarPolarMass_pos_of_not_isPrimePow {a : ℝ} (ha : 0 < a)
    {n : ℕ} (hn : 2 ≤ n) (hpp : ¬ IsPrimePow n) :
    collarAtomMass (shiftDifference a) n = 0 ∧
      0 < collarPolarMass (shiftDifference a) n := by
  have hvon : vonMangoldtAtom n = 0 := by
    unfold vonMangoldtAtom
    rw [if_pos hn, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  refine ⟨by unfold collarAtomMass; rw [hvon, zero_mul], ?_⟩
  unfold collarPolarMass
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hm := continuous_shiftDifference a
  have hmr : Continuous fun x => shiftDifference a (Real.log n - x) :=
    hm.comp (continuous_const.sub continuous_id)
  have hcont : Continuous fun x =>
      shiftDifference a x * shiftDifference a (Real.log n - x) *
        crossingPolarWeight (Real.log n) x :=
    (hm.mul hmr).mul (continuous_crossingPolarWeight _)
  have hint : IntegrableOn (fun x =>
      shiftDifference a x * shiftDifference a (Real.log n - x) *
        crossingPolarWeight (Real.log n) x) (Ioo (0 : ℝ) (Real.log n)) :=
    hcont.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx =>
      mul_nonneg (mul_nonneg (shiftDifference_pos ha hx.1).le
        (shiftDifference_pos ha (sub_pos.mpr hx.2)).le)
        (crossingPolarWeight_nonneg hx.1.le hx.2.le)) hint]
  have hsub : Ioo (0 : ℝ) (Real.log n) ⊆
      Function.support (fun x =>
        shiftDifference a x * shiftDifference a (Real.log n - x) *
          crossingPolarWeight (Real.log n) x) ∩ Ioo (0 : ℝ) (Real.log n) := fun x hx => by
    have hp1 := shiftDifference_pos ha hx.1
    have hp2 := shiftDifference_pos ha (sub_pos.mpr hx.2)
    have hp3 : 0 < crossingPolarWeight (Real.log n) x := by
      unfold crossingPolarWeight
      exact mul_pos (mul_pos two_pos (Real.sinh_pos_iff.mpr (by linarith [hx.1])))
        (Real.sinh_pos_iff.mpr (by linarith [hx.2]))
    exact ⟨(mul_pos (mul_pos hp1 hp2) hp3).ne', hx⟩
  calc (0 : ENNReal) < volume (Ioo (0 : ℝ) (Real.log n)) := by
        rw [Real.volume_Ioo, sub_zero]
        exact ENNReal.ofReal_pos.mpr hlog
    _ ≤ _ := measure_mono hsub

/-! ## 4. Arithmetic Separation Between Anti-Diagonal Atom Dominance and Bi-Scale Bathtub Gain at `n = 4` and `n = 6` -/

/-- `4` is a power of `2` (`4 ∈ powerNodes 2`). -/
theorem four_mem_powerNodes_two : 4 ∈ powerNodes 2 :=
  ⟨2, by omega, by norm_num⟩

/-- `4` is not a power of `3` (`4 ∉ powerNodes 3`). -/
theorem four_not_mem_powerNodes_three : 4 ∉ powerNodes 3 := by
  rintro ⟨j, hj, h⟩
  rcases j with _ | _ | j
  · omega
  · norm_num at h
  · have : 9 ≤ 3 ^ (j + 2) := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- `6` is not a power of `2` (`6 ∉ powerNodes 2`). -/
theorem six_not_mem_powerNodes_two : 6 ∉ powerNodes 2 := by
  rintro ⟨j, hj, h⟩
  rcases j with _ | _ | _ | j
  · omega
  · norm_num at h
  · norm_num at h
  · have : 8 ≤ 2 ^ (j + 3) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- `6` is not a power of `3` (`6 ∉ powerNodes 3`). -/
theorem six_not_mem_powerNodes_three : 6 ∉ powerNodes 3 := by
  rintro ⟨j, hj, h⟩
  rcases j with _ | _ | j
  · omega
  · norm_num at h
  · have : 9 ≤ 3 ^ (j + 2) := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- `6` is not a prime power (`¬ IsPrimePow 6`). -/
theorem six_not_isPrimePow : ¬ IsPrimePow 6 := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, hk, hpk⟩
  have hp2 := hp.two_le
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · obtain rfl : k = 1 := by omega
    rw [pow_one] at hpk
    subst hpk
    exact absurd hp (by decide)
  · rcases Nat.lt_or_ge p 3 with hp3 | hp3
    · obtain rfl : p = 2 := by omega
      rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · obtain rfl : k = 2 := by omega
        norm_num at hpk
      · have : 8 ≤ 2 ^ k := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
        omega
    · have : 9 ≤ p ^ k := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
          _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
      omega

/-- **The `n = 4` Law (Atom-Dominated Prime Square vs. Dyadic Redundancy and Ternary Gain):**
1. For every shift `a > 0`, `collarPolarMass (shiftDifference a) 4 < collarAtomMass (shiftDifference a) 4`
   (`4 ∈ atomDominatedModuli` is the unique composite prime power whose explicit-formula atom
   dominates the polar weight along the whole collar).
2. Adjoining `4` to the dyadic power grid `powerNodes 2` produces **no** improvement in the
   blind symbol slack (`BlindSymbolSlackOn (insert 4 (powerNodes 2)) M ↔ -symbolPeriodMean 2 ≤ M`),
   whereas removing `4 = 2²` from `powerNodes 2` relaxes the slack by the exact second cosine
   coefficient `|foldedCosineCoefficient 2 2|`.
3. Adjoining `4` to the ternary power grid `powerNodes 3` produces a strictly positive incidence
   gain `0 < incidenceGain 3 4`. -/
theorem four_atomDominated_and_dyadic_ternary_slack_law {a : ℝ} (ha : 0 < a) (M : ℝ) :
    collarPolarMass (shiftDifference a) 4 < collarAtomMass (shiftDifference a) 4 ∧
      (BlindSymbolSlackOn (insert 4 (powerNodes 2)) M ↔
        -symbolPeriodMean 2 ≤ M) ∧
      (BlindSymbolSlackOn (puncturedPowerNodes 2 2) M ↔
        -(symbolPeriodMean 2 - |foldedCosineCoefficient 2 2|) ≤ M) ∧
      0 < incidenceGain 3 4 ∧
      BlindSymbolSlackOn (insert 4 (powerNodes 3))
        (-symbolPeriodMean 3 - incidenceGain 3 4) := by
  have h4mem : (4 : ℕ) ∈ atomDominatedModuli := by
    simp [atomDominatedModuli]
  exact ⟨(collarPolarMass_lt_collarAtomMass_of_mem_atomDominatedModuli ha h4mem).2.2,
    blindSymbolSlackOn_insert_iff_of_mem (q := 2) (n := 4) (by norm_num) four_mem_powerNodes_two M,
    blindSymbolSlackOn_punctured_iff (q := 2) (d := 2) (by norm_num) (by norm_num) M,
    incidenceGain_pos (q := 3) (n := 4) (by norm_num) (by norm_num) four_not_mem_powerNodes_three,
    blindSymbolSlackOn_insert_of_not_mem (q := 3) (n := 4) (by norm_num) (by norm_num)⟩

/-- **The `n = 6` Law (Zero Explicit-Formula Atom vs. Simultaneous Dyadic and Ternary Bathtub Gain):**
1. For every shift `a > 0`, `collarAtomMass (shiftDifference a) 6 = 0` and
   `0 < collarPolarMass (shiftDifference a) 6`: in the explicit formula, `n = 6 = 2 · 3` carries
   zero von Mangoldt atom, so the polar weight strictly dominates the collar.
2. Yet in the bi-scale node-blindness problem, `6` is multiplicatively independent of both `2` and
   `3`, so adjoining blindness at the composite node `6` strictly improves **both** the dyadic
   bathtub (`powerNodes 2`) by `0 < incidenceGain 2 6` and the ternary bathtub (`powerNodes 3`) by
   `0 < incidenceGain 3 6` (including on zero-pole combinations). -/
theorem six_polarDominated_and_biscale_incidenceGain_pos {a : ℝ} (ha : 0 < a) :
    collarAtomMass (shiftDifference a) 6 = 0 ∧
      0 < collarPolarMass (shiftDifference a) 6 ∧
      0 < incidenceGain 2 6 ∧
      0 < incidenceGain 3 6 ∧
      BlindSymbolSlackOn (insert 6 (powerNodes 2))
        (-symbolPeriodMean 2 - incidenceGain 2 6) ∧
      BlindSymbolSlackOn (insert 6 (powerNodes 3))
        (-symbolPeriodMean 3 - incidenceGain 3 6) ∧
      ZeroPoleBlindSymbolSlackOn (insert 6 (powerNodes 2))
        (-symbolPeriodMean 2 - incidenceGain 2 6) ∧
      ZeroPoleBlindSymbolSlackOn (insert 6 (powerNodes 3))
        (-symbolPeriodMean 3 - incidenceGain 3 6) := by
  obtain ⟨h0, hpos⟩ := collarAtomMass_eq_zero_and_collarPolarMass_pos_of_not_isPrimePow
    ha (by norm_num : 2 ≤ 6) six_not_isPrimePow
  exact ⟨h0, hpos,
    incidenceGain_pos (q := 2) (n := 6) (by norm_num) (by norm_num) six_not_mem_powerNodes_two,
    incidenceGain_pos (q := 3) (n := 6) (by norm_num) (by norm_num) six_not_mem_powerNodes_three,
    blindSymbolSlackOn_insert_of_not_mem (q := 2) (n := 6) (by norm_num) (by norm_num),
    blindSymbolSlackOn_insert_of_not_mem (q := 3) (n := 6) (by norm_num) (by norm_num),
    zeroPoleBlindSymbolSlackOn_insert_of_not_mem (q := 2) (n := 6) (by norm_num) (by norm_num),
    zeroPoleBlindSymbolSlackOn_insert_of_not_mem (q := 3) (n := 6) (by norm_num) (by norm_num)⟩

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
