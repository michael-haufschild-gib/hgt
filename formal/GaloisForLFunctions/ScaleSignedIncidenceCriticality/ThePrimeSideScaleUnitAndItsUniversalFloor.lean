import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheScaleUnitInWhichTheApertureLadderConverges
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.FiniteRadiusCertificateReadingsCannotResolveTheWeilCone

/-!
# The prime-side scale unit and its universal floor

The prime-window gate was proved as vacuity: no bounded radius resolves the full Weil cone. It had
no number. This module supplies the number by putting the prime side in the same unit as the zero
side.

A prime weight has a set of **failure apertures**
`weightFailureApertures lam = {a > 0 : the full Weil functional of lam is already negative on some
test of aperture a}`. It is an up-set, and:

* `weightFailureApertures_eq_empty_iff` — it is empty exactly when `lam` lies in the full Weil
  cone. The scale datum is an exact criterion on the prime side too, and for `lam = Λ` that is RH.
* `weightFailureApertures_subset_Ioi_threeTenths` — **the universal floor.** For *every* weight,
  whatever its tail, the failure aperture exceeds `3/10`. The prime side has an unconditional
  quiet zone: no arithmetic weight at all can break Weil positivity inside aperture `3/10`.
  This is the positive floor the prime-window face was missing, and it is independent of the
  certificate radius and of the weight.
* `weightFailureApertures_subset_Ioi_of_radiusReading_eq` — under RH a weight sharing the
  radius-`R` certificate of `Λ` has failure aperture beyond `R`, so the radius-`R` certificate
  certifies exactly the confinement `(max R (3/10), ∞)`
  (`radiusCertificateScaleContent`), and the cone is the intersection of those confinements over
  all radii (`primeLadderConvergesInTheScaleUnit`).

`theTwoWallsShareOneUnit` records that the zero side and the prime side are one unit: on both, the
criterion is emptiness of the failure set, a bounded certificate confines it to the complement of
its own scale, and the content lies in the intersection over all scales. The asymmetry is that the
prime side has a universal floor `3/10` while the zero side has none: an arithmetic weight cannot
fail early, a zero configuration can.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The prime-side scale datum -/

/-- The weight is Weil-positive on every test of aperture `a`. -/
def weightAperturePositivity (a : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re

theorem weightAperturePositivity_mono {a b : ℝ} (hab : a ≤ b) {lam : ℕ → ℝ}
    (h : weightAperturePositivity b lam) : weightAperturePositivity a lam := fun f hf hfs =>
  h f hf (hfs.trans (Icc_subset_Icc (by linarith) hab))

/-- The apertures at which the weight already fails. -/
def weightFailureApertures (lam : ℕ → ℝ) : Set ℝ :=
  {a : ℝ | 0 < a ∧ ¬ weightAperturePositivity a lam}

theorem weightFailureApertures_upSet {lam : ℕ → ℝ} {a b : ℝ}
    (ha : a ∈ weightFailureApertures lam) (hab : a ≤ b) : b ∈ weightFailureApertures lam :=
  ⟨lt_of_lt_of_le ha.1 hab, fun hb => ha.2 (weightAperturePositivity_mono hab hb)⟩

/-- **The prime-side criterion.** The weight lies in the full Weil cone exactly when it has no
failure aperture. -/
theorem weightFailureApertures_eq_empty_iff (lam : ℕ → ℝ) :
    weightFailureApertures lam = ∅ ↔ WeilPositiveFull lam := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h f hf hfc
    obtain ⟨a, ha, hsub⟩ := exists_aperture_of_hasCompactSupport hfc
    by_contra hneg
    exact h a ⟨ha, fun hpos => hneg (hpos f hf hsub)⟩
  · intro hW a hmem
    exact hmem.2 fun f hf hfs => hW f hf
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        ((subset_tsupport f).trans hfs))

/-! ### 2. The universal floor of the prime side -/

/-- **The universal quiet zone.** No prime weight whatsoever fails Weil positivity at an aperture
below `3/10`: the window certificate of that aperture holds for every weight, with a strictly
positive gain. The failure aperture of an arbitrary weight is therefore bounded below by a positive
constant that depends on nothing. -/
theorem weightFailureApertures_subset_Ioi_threeTenths (lam : ℕ → ℝ) :
    weightFailureApertures lam ⊆ Ioi (3 / 10) := by
  intro a ha
  rw [mem_Ioi]
  by_contra h
  refine ha.2 fun f hf hfs => ?_
  have hsub : tsupport f ⊆ Icc (-(3 / 10)) (3 / 10) :=
    hfs.trans (Icc_subset_Icc (by linarith [not_lt.mp h]) (not_lt.mp h))
  have hgain := weilFullFunctional_re_ge_of_support_le_threeTenths lam hf hsub
  have hint : (0 : ℝ) ≤ ∫ x, ‖f x‖ ^ 2 := MeasureTheory.integral_nonneg fun _ => by positivity
  nlinarith

/-- Every weight is Weil-positive at aperture `3/10`. -/
theorem weightAperturePositivity_threeTenths (lam : ℕ → ℝ) :
    weightAperturePositivity (3 / 10) lam := by
  by_contra h
  have := weightFailureApertures_subset_Ioi_threeTenths lam ⟨by norm_num, h⟩
  rw [mem_Ioi] at this
  exact absurd this (lt_irrefl _)

/-! ### 3. The radius ladder in the scale unit -/

/-- Under RH, a weight sharing the radius-`R` certificate of `Λ` cannot fail inside `R`. -/
theorem weightFailureApertures_subset_Ioi_of_radiusReading_eq (hRH : RiemannHypothesis) {R : ℝ}
    {lam : ℕ → ℝ}
    (heq : radiusReading R lam = radiusReading R (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))) :
    weightFailureApertures lam ⊆ Ioi R := by
  have hpos : WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
    WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr ⟨hRH, fun _ _ => rfl⟩
  intro a ha
  rw [mem_Ioi]
  by_contra h
  refine ha.2 fun f hf hfs => ?_
  have hfs' : tsupport f ⊆ Icc (-R) R :=
    hfs.trans (Icc_subset_Icc (by linarith [not_lt.mp h]) (not_lt.mp h))
  have hval : weilFullFunctional lam (EF.weilTest f f) =
      weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (EF.weilTest f f) :=
    congrFun heq ⟨f, hf, hfs'⟩
  rw [hval]
  exact hpos f hf (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport f).trans hfs'))

/-- **The scale content of a radius certificate.** A weight sharing `Λ`'s radius-`R` certificate
has its failure apertures confined beyond `R`, and every weight has them confined beyond `3/10`:
the certificate is worth exactly the larger of the two scales. -/
theorem radiusCertificateScaleContent (hRH : RiemannHypothesis) {R : ℝ} {lam : ℕ → ℝ}
    (heq : radiusReading R lam = radiusReading R (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))) :
    weightFailureApertures lam ⊆ Ioi (max R (3 / 10)) := by
  intro a ha
  rw [mem_Ioi, max_lt_iff]
  exact ⟨weightFailureApertures_subset_Ioi_of_radiusReading_eq hRH heq ha,
    weightFailureApertures_subset_Ioi_threeTenths lam ha⟩

/-- **The prime ladder converges in the scale unit.** Confinement at every scale is membership in
the full Weil cone. -/
theorem primeLadderConvergesInTheScaleUnit (lam : ℕ → ℝ) :
    (∀ R : ℝ, 0 < R → weightFailureApertures lam ⊆ Ioi R) ↔ WeilPositiveFull lam := by
  rw [← weightFailureApertures_eq_empty_iff, Set.eq_empty_iff_forall_notMem]
  refine ⟨fun h b hb => ?_, fun h R _ b hb => absurd (h b hb) not_false⟩
  have := h b hb.1 hb
  rw [mem_Ioi] at this
  exact absurd this (lt_irrefl b)

/-! ### 4. One unit for the two walls -/

/-- **The two walls share one unit.** On the zero side and on the prime side alike, the criterion
is emptiness of the failure set, a bounded certificate confines that set to the complement of its
own scale, and the content is the intersection over all scales. The only asymmetry is the
universal floor `3/10`, which the prime side has and the zero side does not. -/
theorem theTwoWallsShareOneUnit :
    (∀ Z : TemperedZeroConfig, failureApertures Z = ∅ ↔ width Z = 0) ∧
      (∀ lam : ℕ → ℝ, weightFailureApertures lam = ∅ ↔ WeilPositiveFull lam) ∧
      (∀ lam : ℕ → ℝ, weightFailureApertures lam ⊆ Ioi (3 / 10)) ∧
      (∀ (a δ : ℝ), 0 < a → 0 < δ → δ ≤ 1 / 2 → ∃ Z : TemperedZeroConfig,
        failureApertures Z = Ioi a ∧ width Z = δ) :=
  ⟨failureApertures_eq_empty_iff_width_eq_zero, weightFailureApertures_eq_empty_iff,
    weightFailureApertures_subset_Ioi_threeTenths, scaleAndDepthAreIndependent.1⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
