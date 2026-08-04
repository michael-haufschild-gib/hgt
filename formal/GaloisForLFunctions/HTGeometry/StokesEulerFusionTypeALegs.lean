import GaloisForLFunctions.HTGeometry.StokesEulerFusionCapacity
import GaloisForLFunctions.HTGeometry.StokesCartanTypeALegs

/-!
# Euler fusion with arbitrary type-A legs

This module closes the full-marking version of the one-port index law.  A leg state is written in
edge-increment coordinates, so its attached core coordinate is the sum of its increments.  The
full positive form is a sum of coordinate squares and fission-cut squares.  After all local
physical-rank maps are identified, every local root defect and the entire genus/fusion correction
combine into one common-rank square.  Thus arbitrary finite type-A legs cannot create a second
negative direction, even after arbitrary-genus fusion.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes
namespace EulerFusionTypeALegs

/-- Increment coordinates of all type-A legs attached to one Stokes core. -/
abbrev LegMode {n : ℕ} (legLength : Fin n → ℕ) :=
  (i : Fin n) → Fin (legLength i + 1) → ℝ

/-- Recover each core coordinate by summing increments along its attached path. -/
noncomputable def coreFromLegs {n : ℕ} (legLength : Fin n → ℕ) :
    LegMode legLength →ₗ[ℝ] (Fin n → ℝ) where
  toFun d i := ∑ k, d i k
  map_add' := by
    intro d e
    funext i
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' := by
    intro c d
    funext i
    change (∑ k, c * d i k) = c * ∑ k, d i k
    rw [Finset.mul_sum]

theorem coreFromLegs_sum {n : ℕ} (legLength : Fin n → ℕ)
    (d : LegMode legLength) (i : Fin n) :
    ∑ k, d i k = coreFromLegs legLength d i := rfl

/-- One leg-increment coordinate as a linear functional. -/
def coordinateLinear {n : ℕ} (legLength : Fin n → ℕ)
    (i : Fin n) (k : Fin (legLength i + 1)) : LegMode legLength →ₗ[ℝ] ℝ :=
  (LinearMap.proj k : (Fin (legLength i + 1) → ℝ) →ₗ[ℝ] ℝ).comp
    (LinearMap.proj i : LegMode legLength →ₗ[ℝ] (Fin (legLength i + 1) → ℝ))

@[simp] theorem coordinateLinear_apply {n : ℕ} (legLength : Fin n → ℕ)
    (i : Fin n) (k : Fin (legLength i + 1)) (d : LegMode legLength) :
    coordinateLinear legLength i k d = d i k := rfl

/-- Fission-cut current after the leg increments are summed into core coordinates. -/
noncomputable def cutLinear {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (e : Fin (Fintype.card datum.rooted.tree.tree)) :
    LegMode legLength →ₗ[ℝ] ℝ where
  toFun d := ∑ i, coreFromLegs legLength d i * datum.cutVector e i
  map_add' := by
    intro d f
    simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c d
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    change (∑ i, (c * coreFromLegs legLength d i) * datum.cutVector e i) =
      c * ∑ i, coreFromLegs legLength d i * datum.cutVector e i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem cutLinear_apply {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (e : Fin (Fintype.card datum.rooted.tree.tree))
    (d : LegMode legLength) :
    cutLinear datum legLength e d =
      ∑ i, coreFromLegs legLength d i * datum.cutVector e i := rfl

/-- Full physical rank after recovering core coordinates from leg increments. -/
noncomputable def fullRankLinear {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) : LegMode legLength →ₗ[ℝ] ℝ :=
  datum.massLinear.comp (coreFromLegs legLength)

/-- Positive full-leg form: every path increment and every fission cut is a positive square. -/
noncomputable def fullPositiveForm {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) : QuadraticForm ℝ (LegMode legLength) :=
  (∑ i, ∑ k, QuadraticMap.sq.comp (coordinateLinear legLength i k)) +
    ∑ e, datum.rooted.tree.canonicalCuts.length e •
      (QuadraticMap.sq.comp (cutLinear datum legLength e))

/-- Full local Cartan form including arbitrary finite type-A legs. -/
noncomputable def fullCartanForm {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) : QuadraticForm ℝ (LegMode legLength) :=
  fullPositiveForm datum legLength - datum.rootDefect •
    (QuadraticMap.sq.comp (fullRankLinear datum legLength))

theorem fullPositiveForm_apply {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (d : LegMode legLength) :
    fullPositiveForm datum legLength d =
      datum.fullPositiveQuadratic legLength (coreFromLegs legLength d) d := by
  rw [fullPositiveForm, QuadraticMap.add_apply, QuadraticMap.sum_apply,
    QuadraticMap.sum_apply]
  simp_rw [QuadraticMap.sum_apply]
  simp only [QuadraticMap.comp_apply, QuadraticMap.sq_apply,
    coordinateLinear_apply, QuadraticMap.smul_apply, smul_eq_mul, cutLinear_apply,
    CertifiedFissionDatum.fullPositiveQuadratic, pow_two]

theorem fullCartanForm_apply {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (d : LegMode legLength) :
    fullCartanForm datum legLength d =
      datum.fullCartanQuadratic legLength (coreFromLegs legLength d) d := by
  rw [fullCartanForm, QuadraticMap.sub_apply, QuadraticMap.smul_apply,
    QuadraticMap.comp_apply, QuadraticMap.sq_apply, fullPositiveForm_apply]
  simp only [smul_eq_mul, fullRankLinear, LinearMap.coe_comp, Function.comp_apply,
    CertifiedFissionDatum.fullCartanQuadratic,
    CertifiedFissionDatum.massLinear_apply]
  ring

theorem fullPositiveForm_pos {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (d : LegMode legLength) (hd : d ≠ 0) :
    0 < fullPositiveForm datum legLength d := by
  rw [fullPositiveForm_apply]
  exact datum.fullPositiveQuadratic_pos legLength (coreFromLegs legLength d) d
    (coreFromLegs_sum legLength d) (Or.inr hd)

theorem fullPositiveForm_nonneg {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (d : LegMode legLength) :
    0 ≤ fullPositiveForm datum legLength d := by
  by_cases hd : d = 0
  · subst d
    simp [fullPositiveForm_apply, CertifiedFissionDatum.fullPositiveQuadratic]
  · exact (fullPositiveForm_pos datum legLength d hd).le

/-- Family of full local marking spaces. -/
abbrev FullGlobalMode {m : ℕ} {n : Fin (m + 1) → ℕ}
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ) :=
  (a : Fin (m + 1)) → LegMode (legLength a)

/-- Full marked modes with one common physical rank at all punctures. -/
noncomputable def compatibleFullModes {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ) :
    Submodule ℝ (FullGlobalMode legLength) where
  carrier := {d | ∀ a,
    fullRankLinear (datum a) (legLength a) (d a) =
      fullRankLinear (datum 0) (legLength 0) (d 0)}
  zero_mem' := by
    intro a
    simp
  add_mem' := by
    intro d f hd hf a
    change fullRankLinear (datum a) (legLength a) (d a + f a) =
      fullRankLinear (datum 0) (legLength 0) (d 0 + f 0)
    rw [map_add, map_add]
    rw [hd a, hf a]
  smul_mem' := by
    intro c d hd a
    change fullRankLinear (datum a) (legLength a) (c • d a) =
      fullRankLinear (datum 0) (legLength 0) (c • d 0)
    rw [map_smul, map_smul]
    rw [hd a]

/-- Projection of a compatible full marking to one puncture. -/
noncomputable def fullLocalProjection {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ)
    (a : Fin (m + 1)) :
    compatibleFullModes datum legLength →ₗ[ℝ] LegMode (legLength a) :=
  (LinearMap.proj a).comp (compatibleFullModes datum legLength).subtype

@[simp] theorem fullLocalProjection_apply {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ)
    (a : Fin (m + 1)) (d : compatibleFullModes datum legLength) :
    fullLocalProjection datum legLength a d = d.1 a := rfl

/-- Common rank on the full marked fibre product. -/
noncomputable def fullCommonRank {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ) :
    compatibleFullModes datum legLength →ₗ[ℝ] ℝ :=
  (fullRankLinear (datum 0) (legLength 0)).comp
    (fullLocalProjection datum legLength 0)

@[simp] theorem fullCommonRank_apply {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ)
    (d : compatibleFullModes datum legLength) :
    fullCommonRank datum legLength d =
      fullRankLinear (datum 0) (legLength 0) (d.1 0) := rfl

theorem compatible_fullRank {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ)
    (d : compatibleFullModes datum legLength) (a : Fin (m + 1)) :
    fullRankLinear (datum a) (legLength a) (d.1 a) =
      fullCommonRank datum legLength d := by
  exact d.2 a

/-- Positive spatial energy of all punctures, including every type-A leg coordinate. -/
noncomputable def globalFullPositiveForm {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ) :
    QuadraticForm ℝ (compatibleFullModes datum legLength) :=
  ∑ a, (fullPositiveForm (datum a) (legLength a)).comp
    (fullLocalProjection datum legLength a)

/-- Arbitrary-genus fusion form with every local type-A leg retained. -/
noncomputable def fullFusionForm {m : ℕ} {n : Fin (m + 1) → ℕ} (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ) :
    QuadraticForm ℝ (compatibleFullModes datum legLength) :=
  (∑ a, (fullCartanForm (datum a) (legLength a)).comp
    (fullLocalProjection datum legLength a)) +
  (2 * (1 - (genus : ℝ) - ((m + 1 : ℕ) : ℝ))) •
    (QuadraticMap.sq.comp (fullCommonRank datum legLength))

/-- The sole full-marking rank coefficient before capacity completion. -/
noncomputable def fullRankCoefficient {m : ℕ} {n : Fin (m + 1) → ℕ} (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a)) : ℝ :=
  2 * (1 - (genus : ℝ) - ((m + 1 : ℕ) : ℝ)) -
    ∑ a, (datum a).rootDefect

theorem fullFusionForm_eq_positive_add_rank {m : ℕ}
    {n : Fin (m + 1) → ℕ} (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ)
    (d : compatibleFullModes datum legLength) :
    fullFusionForm genus datum legLength d =
      globalFullPositiveForm datum legLength d +
        fullRankCoefficient genus datum * fullCommonRank datum legLength d ^ 2 := by
  rw [fullFusionForm, QuadraticMap.add_apply, QuadraticMap.sum_apply,
    QuadraticMap.smul_apply, QuadraticMap.comp_apply, QuadraticMap.sq_apply]
  rw [globalFullPositiveForm, QuadraticMap.sum_apply]
  simp only [fullCartanForm, QuadraticMap.comp_apply, QuadraticMap.sub_apply,
    QuadraticMap.smul_apply, smul_eq_mul, QuadraticMap.sq_apply,
    fullRankCoefficient, fullLocalProjection_apply]
  have hrank : ∀ a,
      fullRankLinear (datum a) (legLength a) (d.1 a) =
        fullCommonRank datum legLength d := compatible_fullRank datum legLength d
  simp_rw [hrank]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem globalFullPositiveForm_nonneg {m : ℕ}
    {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ)
    (d : compatibleFullModes datum legLength) :
    0 ≤ globalFullPositiveForm datum legLength d := by
  rw [globalFullPositiveForm, QuadraticMap.sum_apply]
  apply Finset.sum_nonneg
  intro a _
  exact fullPositiveForm_nonneg (datum a) (legLength a) (d.1 a)

/-- **Full marked Euler--fusion index theorem.** Arbitrary finite type-A legs and arbitrary genus
still leave at most one negative direction on the physical-rank fibre product. -/
theorem fullFusionForm_sigNeg_le_one {m : ℕ} {n : Fin (m + 1) → ℕ} (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (legLength : (a : Fin (m + 1)) → Fin (n a) → ℕ) :
    sigNeg (fullFusionForm genus datum legLength) ≤ 1 := by
  let coeff : ℝ := fullRankCoefficient genus datum
  let ell : compatibleFullModes datum legLength →ₗ[ℝ] ℝ :=
    (LinearMap.lsmul ℝ ℝ (Real.sqrt (max 0 (-coeff)))).comp
      (fullCommonRank datum legLength)
  apply sigNeg_le_one_of_add_sq_nonneg (fullFusionForm genus datum legLength) ell
  intro d
  rw [fullFusionForm_eq_positive_add_rank]
  change 0 ≤ globalFullPositiveForm datum legLength d +
    coeff * fullCommonRank datum legLength d ^ 2 +
    (Real.sqrt (max 0 (-coeff)) * fullCommonRank datum legLength d) ^ 2
  rw [mul_pow, Real.sq_sqrt (le_max_left 0 (-coeff))]
  by_cases hcoeff : 0 ≤ coeff
  · rw [max_eq_left (neg_nonpos.mpr hcoeff)]
    nlinarith [globalFullPositiveForm_nonneg datum legLength d,
      mul_nonneg hcoeff (sq_nonneg (fullCommonRank datum legLength d))]
  · rw [max_eq_right (neg_nonneg.mpr (le_of_not_ge hcoeff))]
    nlinarith [globalFullPositiveForm_nonneg datum legLength d]

end EulerFusionTypeALegs
end IrregularStokes
end GaloisForLFunctions
