import GaloisForLFunctions.HTGeometry.StokesUniversalContactLaw
import GaloisForLFunctions.HTGeometry.KreinLangerInertia
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Stokes--Cartan Lorentz-capacity law

For every certified finite type-A fission datum, the rescaled Stokes core Cartan form is an
identity-plus-cut Gram form minus one ramification square.  Consequently its negative inertia is
at most one.  The inverse positive Gram matrix supplies an exact scalar capacity whose sign gives
the positive/affine/Lorentz trichotomy, the affine null line, the Lorentz negative vector, and the
determinant wall.

All claims are finite and unconditional.  Root-height assumptions occur explicitly where the
geometric nonnegative rank-one subtraction is needed.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

lemma sigNeg_pos_of_exists_negativeVector {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) {x : M}
    (hx : x ≠ 0) (hneg : Q x < 0) : 0 < sigNeg Q := by
  let V : Submodule ℝ M := ℝ ∙ x
  have hV : ((-Q).restrict V).PosDef := by
    intro y hy
    obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton.mp y.property)
    have hycoe : (y : M) = a • x := ha.symm
    have ha0 : a ≠ 0 := by
      intro haZero
      apply hy
      apply Subtype.ext
      rw [hycoe, haZero]
      simp
    rw [QuadraticMap.restrict_apply, QuadraticMap.neg_apply, hycoe,
      QuadraticMap.map_smul]
    simp only [smul_eq_mul]
    nlinarith [sq_pos_of_ne_zero ha0]
  have hle := le_sigNeg_of_negDef Q hV
  rw [show Module.finrank ℝ V = 1 by
    exact finrank_span_singleton hx] at hle
  omega

namespace FiniteQuadratic

def qform {n : ℕ} (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * x j * A i j

lemma qform_congr {n : ℕ} {A B : Fin n → Fin n → ℝ}
    (h : ∀ i j, A i j = B i j) (x : Fin n → ℝ) : qform A x = qform B x := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [h]

lemma qform_add {n : ℕ} (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    qform (fun i j => A i j + B i j) x = qform A x + qform B x := by
  simp only [qform, mul_add, Finset.sum_add_distrib]

lemma qform_sub {n : ℕ} (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    qform (fun i j => A i j - B i j) x = qform A x - qform B x := by
  simp only [qform, mul_sub, Finset.sum_sub_distrib]

lemma qform_smul {n : ℕ} (a : ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    qform (fun i j => a * A i j) x = a * qform A x := by
  simp only [qform]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sum_mul_sum {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i) * (∑ j, b j) = ∑ i, ∑ j, a i * b j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

lemma qform_delta {n : ℕ} (x : Fin n → ℝ) :
    qform (fun i j => if i = j then 1 else 0) x = ∑ i, x i ^ 2 := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

lemma qform_outer {n : ℕ} (u x : Fin n → ℝ) :
    qform (fun i j => u i * u j) x = (∑ i, x i * u i) ^ 2 := by
  rw [pow_two, sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma sum_comm_three {n m : ℕ}
    (f : Fin n → Fin n → Fin m → ℝ) :
    (∑ i, ∑ j, ∑ e, f i j e) = ∑ e, ∑ i, ∑ j, f i j e := by
  calc
    (∑ i, ∑ j, ∑ e, f i j e) = ∑ i, ∑ e, ∑ j, f i j e := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ e, ∑ i, ∑ j, f i j e := by rw [Finset.sum_comm]

lemma qform_weightedGram {n m : ℕ} (weight : Fin m → ℝ)
    (u : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    qform (fun i j => ∑ e, weight e * (u e i * u e j)) x =
      ∑ e, weight e * (∑ i, x i * u e i) ^ 2 := by
  classical
  calc
    qform (fun i j => ∑ e, weight e * (u e i * u e j)) x =
        ∑ i, ∑ j, ∑ e, x i * x j * (weight e * (u e i * u e j)) := by
      simp only [qform, Finset.mul_sum]
    _ = ∑ e, ∑ i, ∑ j, x i * x j * (weight e * (u e i * u e j)) :=
      sum_comm_three _
    _ = ∑ e, weight e * (∑ i, x i * u e i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro e _
      rw [pow_two, sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

end FiniteQuadratic

namespace DecoratedStokesCore

def realRamification {n : ℕ} (g : DecoratedStokesCore n) (i : Fin n) : ℝ :=
  g.ramification i

def realB {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) : ℝ :=
  g.B i j

def cartanEntry {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) : ℝ :=
  (if i = j then 2 else 0) - g.realB i j

lemma rationalB_eq_contact {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) :
    (g.B i j : ℚ) = (if i = j then 1 else 0) +
      (g.ramification i : ℚ) * (g.ramification j : ℚ) * (g.contactMatrix i j - 1) := by
  by_cases hij : i = j
  · subst j
    have hr : (g.ramification i : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (g.ramification_pos i))
    simp only [if_pos, contactMatrix_self, diagonalContact]
    field_simp
    push_cast
    ring
  · simp only [if_neg hij, g.contactMatrix_of_ne hij, pairContact]
    have hri : (g.ramification i : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (g.ramification_pos i))
    have hrj : (g.ramification j : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (g.ramification_pos j))
    field_simp
    ring

theorem realB_eq_contact {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) :
    g.realB i j = (if i = j then 1 else 0) +
      g.realRamification i * g.realRamification j * (g.realContactMatrix i j - 1) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (g.rationalB_eq_contact i j)
  push_cast at h
  by_cases hij : i = j
  · simpa [realB, realRamification, realContactMatrix, hij] using h
  · simpa [realB, realRamification, realContactMatrix, hij] using h

end DecoratedStokesCore

namespace CertifiedFissionDatum

def ramificationVector {n : ℕ} (datum : CertifiedFissionDatum n) (i : Fin n) : ℝ :=
  datum.core.realRamification i

noncomputable def cutVector {n : ℕ} (datum : CertifiedFissionDatum n)
    (e : Fin (Fintype.card datum.rooted.tree.tree)) (i : Fin n) : ℝ :=
  datum.ramificationVector i * datum.rooted.tree.canonicalCuts.side e i

noncomputable def rootDefect {n : ℕ} (datum : CertifiedFissionDatum n) : ℝ :=
  datum.rooted.tree.canonicalCuts.root - 1

theorem cartanEntry_eq_oneDefect {n : ℕ} (datum : CertifiedFissionDatum n)
    (i j : Fin n) :
    datum.core.cartanEntry i j =
      (if i = j then 1 else 0) +
        (∑ e, datum.rooted.tree.canonicalCuts.length e *
          (datum.cutVector e i * datum.cutVector e j)) -
        datum.rootDefect * (datum.ramificationVector i * datum.ramificationVector j) := by
  classical
  have hcontact : datum.core.realContactMatrix i j =
      datum.rooted.tree.canonicalCuts.root -
        ∑ e, datum.rooted.tree.canonicalCuts.length e *
          (datum.rooted.tree.canonicalCuts.side e i *
            datum.rooted.tree.canonicalCuts.side e j) := by
    rw [← datum.rooted.contact_eq i j, ← datum.rooted.tree.canonicalCuts_contact_eq i j]
    rfl
  rw [DecoratedStokesCore.cartanEntry, datum.core.realB_eq_contact, hcontact]
  have hsum :
      datum.ramificationVector i * datum.ramificationVector j *
          (∑ e, datum.rooted.tree.canonicalCuts.length e *
            (datum.rooted.tree.canonicalCuts.side e i *
              datum.rooted.tree.canonicalCuts.side e j)) =
        ∑ e, datum.rooted.tree.canonicalCuts.length e *
          (datum.cutVector e i * datum.cutVector e j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [cutVector, ramificationVector]
    ring
  rw [← hsum]
  simp only [rootDefect, ramificationVector]
  by_cases hij : i = j <;> simp [hij] <;> ring

noncomputable def positiveKernel {n : ℕ} (datum : CertifiedFissionDatum n)
    (i j : Fin n) : ℝ :=
  (if i = j then 1 else 0) +
    ∑ e, datum.rooted.tree.canonicalCuts.length e *
      (datum.cutVector e i * datum.cutVector e j)

def cartanQuadratic {n : ℕ} (datum : CertifiedFissionDatum n)
    (x : Fin n → ℝ) : ℝ :=
  FiniteQuadratic.qform datum.core.cartanEntry x

noncomputable def positiveQuadratic {n : ℕ} (datum : CertifiedFissionDatum n)
    (x : Fin n → ℝ) : ℝ :=
  FiniteQuadratic.qform datum.positiveKernel x

def totalRamification {n : ℕ} (datum : CertifiedFissionDatum n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i * datum.ramificationVector i

theorem positiveQuadratic_eq_squares {n : ℕ} (datum : CertifiedFissionDatum n)
    (x : Fin n → ℝ) :
    datum.positiveQuadratic x =
      (∑ i, x i ^ 2) +
        ∑ e, datum.rooted.tree.canonicalCuts.length e *
          (∑ i, x i * datum.cutVector e i) ^ 2 := by
  classical
  rw [positiveQuadratic]
  calc
    FiniteQuadratic.qform datum.positiveKernel x =
        FiniteQuadratic.qform (fun i j =>
          (if i = j then 1 else 0) +
            ∑ e, datum.rooted.tree.canonicalCuts.length e *
              (datum.cutVector e i * datum.cutVector e j)) x := by
      apply FiniteQuadratic.qform_congr
      intro i j
      rfl
    _ = (∑ i, x i ^ 2) +
        ∑ e, datum.rooted.tree.canonicalCuts.length e *
          (∑ i, x i * datum.cutVector e i) ^ 2 := by
      rw [FiniteQuadratic.qform_add, FiniteQuadratic.qform_delta,
        FiniteQuadratic.qform_weightedGram]

theorem cartanQuadratic_eq_oneDefect {n : ℕ} (datum : CertifiedFissionDatum n)
    (x : Fin n → ℝ) :
    datum.cartanQuadratic x = datum.positiveQuadratic x -
      datum.rootDefect * datum.totalRamification x ^ 2 := by
  classical
  rw [cartanQuadratic, positiveQuadratic]
  calc
    FiniteQuadratic.qform datum.core.cartanEntry x =
        FiniteQuadratic.qform
          (fun i j => datum.positiveKernel i j -
            datum.rootDefect *
              (datum.ramificationVector i * datum.ramificationVector j)) x := by
      apply FiniteQuadratic.qform_congr
      intro i j
      rw [datum.cartanEntry_eq_oneDefect]
      rfl
    _ = FiniteQuadratic.qform datum.positiveKernel x -
        FiniteQuadratic.qform
          (fun i j => datum.rootDefect *
            (datum.ramificationVector i * datum.ramificationVector j)) x := by
      rw [FiniteQuadratic.qform_sub]
    _ = FiniteQuadratic.qform datum.positiveKernel x - datum.rootDefect *
        FiniteQuadratic.qform
          (fun i j => datum.ramificationVector i * datum.ramificationVector j) x := by
      rw [FiniteQuadratic.qform_smul]
    _ = FiniteQuadratic.qform datum.positiveKernel x -
        datum.rootDefect * datum.totalRamification x ^ 2 := by
      rw [FiniteQuadratic.qform_outer]
      rfl

theorem positiveQuadratic_pos {n : ℕ} (datum : CertifiedFissionDatum n)
    {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < datum.positiveQuadratic x := by
  rw [datum.positiveQuadratic_eq_squares]
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hbase : 0 < ∑ i, x i ^ 2 := by
    apply Finset.sum_pos'
    · intro j _
      exact sq_nonneg (x j)
    · exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hcuts : 0 ≤ ∑ e, datum.rooted.tree.canonicalCuts.length e *
      (∑ i, x i * datum.cutVector e i) ^ 2 := by
    apply Finset.sum_nonneg
    intro e _
    exact mul_nonneg (datum.rooted.tree.canonicalCuts.length_pos e).le (sq_nonneg _)
  exact add_pos_of_pos_of_nonneg hbase hcuts

theorem positiveQuadratic_nonneg {n : ℕ} (datum : CertifiedFissionDatum n)
    (x : Fin n → ℝ) : 0 ≤ datum.positiveQuadratic x := by
  by_cases hx : x = 0
  · subst x
    simp [positiveQuadratic, FiniteQuadratic.qform]
  · exact (datum.positiveQuadratic_pos hx).le

/-- The Cartan quadratic form is strictly positive on the codimension-one ramification-zero
hyperplane. This is the exact, basis-free content of the universal one-defect law. -/
theorem cartanQuadratic_pos_of_totalRamification_eq_zero {n : ℕ}
    (datum : CertifiedFissionDatum n) {x : Fin n → ℝ}
    (hmass : datum.totalRamification x = 0) (hx : x ≠ 0) :
    0 < datum.cartanQuadratic x := by
  rw [datum.cartanQuadratic_eq_oneDefect, hmass]
  norm_num
  exact datum.positiveQuadratic_pos hx

noncomputable def positiveMatrix {n : ℕ} (datum : CertifiedFissionDatum n) :
    Matrix (Fin n) (Fin n) ℝ := datum.positiveKernel

def cartanMatrix {n : ℕ} (datum : CertifiedFissionDatum n) :
    Matrix (Fin n) (Fin n) ℝ := datum.core.cartanEntry

theorem cartanMatrix_eq_positiveMatrix_sub_outer {n : ℕ}
    (datum : CertifiedFissionDatum n) :
    datum.cartanMatrix = datum.positiveMatrix -
      datum.rootDefect • Matrix.vecMulVec datum.ramificationVector
        datum.ramificationVector := by
  classical
  ext i j
  simp only [cartanMatrix, positiveMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  rw [datum.cartanEntry_eq_oneDefect]
  rfl

theorem positiveMatrix_posDef {n : ℕ} (datum : CertifiedFissionDatum n) :
    datum.positiveMatrix.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [positiveMatrix, positiveKernel, eq_comm, mul_comm]
  · intro x hx
    simpa [positiveMatrix, positiveQuadratic, FiniteQuadratic.qform,
      dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      using datum.positiveQuadratic_pos hx

noncomputable def cartanForm {n : ℕ} (datum : CertifiedFissionDatum n) :
    QuadraticForm ℝ (Fin n → ℝ) := datum.cartanMatrix.toQuadraticForm'

theorem cartanForm_apply {n : ℕ} (datum : CertifiedFissionDatum n)
    (x : Fin n → ℝ) : datum.cartanForm x = datum.cartanQuadratic x := by
  simp [cartanForm, cartanMatrix, cartanQuadratic, Matrix.toQuadraticForm',
    Matrix.toLinearMap₂'_apply', FiniteQuadratic.qform, dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_assoc, mul_comm]

noncomputable def massLinear {n : ℕ} (datum : CertifiedFissionDatum n) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun := datum.totalRamification
  map_add' := by
    intro x y
    simp [totalRamification, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    simp [totalRamification, Finset.mul_sum]
    ring

theorem massLinear_apply {n : ℕ} (datum : CertifiedFissionDatum n)
    (x : Fin n → ℝ) : datum.massLinear x = datum.totalRamification x := rfl

/-- The exact Cartan form has at most one negative square whenever root height is at least one. -/
theorem cartanForm_sigNeg_le_one {n : ℕ} (datum : CertifiedFissionDatum n)
    (hroot : 0 ≤ datum.rootDefect) : sigNeg datum.cartanForm ≤ 1 := by
  let ell : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.lsmul ℝ ℝ (Real.sqrt datum.rootDefect)).comp datum.massLinear
  apply sigNeg_le_one_of_add_sq_nonneg datum.cartanForm ell
  intro x
  have hsqrt : (Real.sqrt datum.rootDefect) ^ 2 = datum.rootDefect :=
    Real.sq_sqrt hroot
  rw [datum.cartanForm_apply, datum.cartanQuadratic_eq_oneDefect]
  change 0 ≤ datum.positiveQuadratic x - datum.rootDefect * datum.totalRamification x ^ 2 +
    (Real.sqrt datum.rootDefect * datum.totalRamification x) ^ 2
  rw [mul_pow, hsqrt]
  ring_nf
  exact datum.positiveQuadratic_nonneg x

theorem ramificationVector_ne_zero {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) : datum.ramificationVector ≠ 0 := by
  classical
  let i : Fin n := Classical.choice inferInstance
  intro hzero
  have hi := congrFun hzero i
  have hpos : 0 < datum.ramificationVector i := by
    simp only [ramificationVector, DecoratedStokesCore.realRamification]
    exact_mod_cast datum.core.ramification_pos i
  simp at hi
  linarith

noncomputable def capacityVector {n : ℕ} (datum : CertifiedFissionDatum n) :
    Fin n → ℝ := Matrix.mulVec datum.positiveMatrix⁻¹ datum.ramificationVector

noncomputable def capacity {n : ℕ} (datum : CertifiedFissionDatum n) : ℝ :=
  dotProduct datum.ramificationVector datum.capacityVector

noncomputable def capacityGap {n : ℕ} (datum : CertifiedFissionDatum n) : ℝ :=
  datum.capacity⁻¹ - datum.rootDefect

theorem positiveMatrix_mulVec_capacityVector {n : ℕ}
    (datum : CertifiedFissionDatum n) :
    Matrix.mulVec datum.positiveMatrix datum.capacityVector = datum.ramificationVector := by
  letI := datum.positiveMatrix_posDef.isUnit.invertible
  rw [capacityVector, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec]

theorem capacity_pos {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) : 0 < datum.capacity := by
  have h := datum.positiveMatrix_posDef.inv.dotProduct_mulVec_pos
    datum.ramificationVector_ne_zero
  simpa [capacity, capacityVector] using h

theorem cartanMatrix_det_eq_capacity {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) :
    datum.cartanMatrix.det = datum.positiveMatrix.det * datum.capacity *
      datum.capacityGap := by
  classical
  let u : Fin n → ℝ := fun i => -datum.rootDefect * datum.ramificationVector i
  let v : Fin n → ℝ := datum.ramificationVector
  have houter : Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) v =
      -datum.rootDefect • Matrix.vecMulVec datum.ramificationVector
        datum.ramificationVector := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, u, v, smul_eq_mul]
    ring
  have hcartan : datum.cartanMatrix = datum.positiveMatrix +
      Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) v := by
    rw [datum.cartanMatrix_eq_positiveMatrix_sub_outer, houter]
    simp [sub_eq_add_neg, neg_smul]
  have hdetUnit : IsUnit datum.positiveMatrix.det :=
    (Matrix.isUnit_iff_isUnit_det datum.positiveMatrix).mp
      datum.positiveMatrix_posDef.isUnit
  have hinvSymm : ∀ i j,
      datum.positiveMatrix⁻¹ i j = datum.positiveMatrix⁻¹ j i := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i)
      datum.positiveMatrix_posDef.inv.isHermitian
    simpa [Matrix.conjTranspose_apply] using h
  have hinner :
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
        Matrix.replicateRow (Fin 1) v * datum.positiveMatrix⁻¹ *
        Matrix.replicateCol (Fin 1) u) (0 : Fin 1) 0 =
        1 - datum.rootDefect * datum.capacity := by
    simp [Matrix.mul_apply, u, v, capacity, capacityVector, dotProduct,
      Finset.mul_sum]
    simp_rw [hinvSymm]
    simp only [Matrix.mulVec, dotProduct]
    apply congrArg (fun s : ℝ => 1 - s)
    apply Finset.sum_congr rfl
    intro i _
    have hrow : (∑ j, datum.ramificationVector j * datum.positiveMatrix⁻¹ i j) =
        ∑ j, datum.positiveMatrix⁻¹ i j * datum.ramificationVector j := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hrow]
    ring
  have hc : datum.capacity ≠ 0 := ne_of_gt datum.capacity_pos
  rw [hcartan]
  calc
    (datum.positiveMatrix + Matrix.replicateCol (Fin 1) u *
        Matrix.replicateRow (Fin 1) v).det =
        datum.positiveMatrix.det *
          (1 + Matrix.replicateRow (Fin 1) v * datum.positiveMatrix⁻¹ *
            Matrix.replicateCol (Fin 1) u).det :=
      Matrix.det_add_replicateCol_mul_replicateRow hdetUnit u v
    _ = datum.positiveMatrix.det * (1 - datum.rootDefect * datum.capacity) := by
      rw [Matrix.det_fin_one, hinner]
    _ = datum.positiveMatrix.det * datum.capacity * datum.capacityGap := by
      simp only [capacityGap]
      field_simp

noncomputable def positiveBilinear {n : ℕ} (datum : CertifiedFissionDatum n)
    (x y : Fin n → ℝ) : ℝ :=
  dotProduct x (Matrix.mulVec datum.positiveMatrix y)

theorem positiveKernel_symm {n : ℕ} (datum : CertifiedFissionDatum n)
    (i j : Fin n) : datum.positiveKernel i j = datum.positiveKernel j i := by
  classical
  simp [positiveKernel, eq_comm, mul_comm]

theorem positiveBilinear_symm {n : ℕ} (datum : CertifiedFissionDatum n)
    (x y : Fin n → ℝ) : datum.positiveBilinear x y = datum.positiveBilinear y x := by
  classical
  simp only [positiveBilinear, positiveMatrix, dotProduct, Matrix.mulVec]
  calc
    (∑ i, x i * ∑ j, datum.positiveKernel i j * y j) =
        ∑ i, ∑ j, x i * (datum.positiveKernel i j * y j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ j, ∑ i, x i * (datum.positiveKernel i j * y j) := by
      rw [Finset.sum_comm]
    _ = ∑ j, y j * ∑ i, datum.positiveKernel j i * x i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [datum.positiveKernel_symm]
      ring

theorem positiveQuadratic_eq_bilinear {n : ℕ} (datum : CertifiedFissionDatum n)
    (x : Fin n → ℝ) : datum.positiveQuadratic x = datum.positiveBilinear x x := by
  simp [positiveQuadratic, positiveBilinear, positiveMatrix, FiniteQuadratic.qform,
    dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_comm]

theorem positiveBilinear_add_left {n : ℕ} (datum : CertifiedFissionDatum n)
    (x y z : Fin n → ℝ) :
    datum.positiveBilinear (x + y) z =
      datum.positiveBilinear x z + datum.positiveBilinear y z := by
  simp [positiveBilinear, add_dotProduct]

theorem positiveBilinear_add_right {n : ℕ} (datum : CertifiedFissionDatum n)
    (x y z : Fin n → ℝ) :
    datum.positiveBilinear x (y + z) =
      datum.positiveBilinear x y + datum.positiveBilinear x z := by
  simp [positiveBilinear, Matrix.mulVec_add, dotProduct_add]

theorem positiveBilinear_smul_left {n : ℕ} (datum : CertifiedFissionDatum n)
    (a : ℝ) (x y : Fin n → ℝ) :
    datum.positiveBilinear (a • x) y = a * datum.positiveBilinear x y := by
  simp [positiveBilinear, smul_dotProduct]

theorem positiveBilinear_smul_right {n : ℕ} (datum : CertifiedFissionDatum n)
    (a : ℝ) (x y : Fin n → ℝ) :
    datum.positiveBilinear x (a • y) = a * datum.positiveBilinear x y := by
  simp [positiveBilinear, Matrix.mulVec_smul, dotProduct_smul]

theorem positiveBilinear_capacityVector {n : ℕ}
    (datum : CertifiedFissionDatum n) (x : Fin n → ℝ) :
    datum.positiveBilinear x datum.capacityVector = datum.totalRamification x := by
  rw [positiveBilinear, datum.positiveMatrix_mulVec_capacityVector]
  simp [totalRamification, dotProduct]

theorem totalRamification_capacityVector {n : ℕ}
    (datum : CertifiedFissionDatum n) :
    datum.totalRamification datum.capacityVector = datum.capacity := by
  simp [totalRamification, capacity, dotProduct, mul_comm]

theorem positiveQuadratic_add_capacityVector {n : ℕ}
    (datum : CertifiedFissionDatum n) (z : Fin n → ℝ) (a : ℝ) :
    datum.positiveQuadratic (z + a • datum.capacityVector) =
      datum.positiveQuadratic z + 2 * a * datum.totalRamification z +
        a ^ 2 * datum.capacity := by
  rw [datum.positiveQuadratic_eq_bilinear,
    datum.positiveBilinear_add_left, datum.positiveBilinear_add_right,
    datum.positiveBilinear_smul_right, datum.positiveBilinear_smul_left,
    datum.positiveBilinear_add_right, datum.positiveBilinear_smul_right,
    ← datum.positiveQuadratic_eq_bilinear,
    datum.positiveBilinear_capacityVector,
    datum.positiveBilinear_symm datum.capacityVector z,
    datum.positiveBilinear_capacityVector,
    datum.positiveBilinear_capacityVector,
    datum.totalRamification_capacityVector]
  ring

noncomputable def centeredVector {n : ℕ} (datum : CertifiedFissionDatum n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  x - (datum.totalRamification x / datum.capacity) • datum.capacityVector

theorem totalRamification_centeredVector {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) (x : Fin n → ℝ) :
    datum.totalRamification (datum.centeredVector x) = 0 := by
  have hc : datum.capacity ≠ 0 := ne_of_gt datum.capacity_pos
  change datum.massLinear (datum.centeredVector x) = 0
  rw [centeredVector, LinearMap.map_sub, LinearMap.map_smul,
    datum.massLinear_apply, datum.massLinear_apply,
    datum.totalRamification_capacityVector]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem centeredVector_decomposition {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) (x : Fin n → ℝ) :
    x = datum.centeredVector x +
      (datum.totalRamification x / datum.capacity) • datum.capacityVector := by
  simp [centeredVector]

/-- Sharp capacity completion: the Cartan form is a positive centered square plus the scalar
capacity gap times total ramification squared. -/
theorem cartanQuadratic_eq_centered_capacity {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) (x : Fin n → ℝ) :
    datum.cartanQuadratic x =
      datum.positiveQuadratic (datum.centeredVector x) +
        datum.totalRamification x ^ 2 * datum.capacityGap := by
  have hc : datum.capacity ≠ 0 := ne_of_gt datum.capacity_pos
  rw [datum.cartanQuadratic_eq_oneDefect]
  conv_lhs =>
    enter [1]
    rw [datum.centeredVector_decomposition x,
      datum.positiveQuadratic_add_capacityVector,
      datum.totalRamification_centeredVector]
  simp only [mul_zero, add_zero]
  simp only [capacityGap]
  field_simp
  ring

theorem cartanQuadratic_pos_of_capacityGap_pos {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) (hgap : 0 < datum.capacityGap)
    {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < datum.cartanQuadratic x := by
  rw [datum.cartanQuadratic_eq_centered_capacity]
  by_cases hz : datum.centeredVector x = 0
  · have hmass : datum.totalRamification x ≠ 0 := by
      intro hm
      apply hx
      rw [datum.centeredVector_decomposition x, hz, hm]
      simp
    have hpositive : 0 < datum.totalRamification x ^ 2 * datum.capacityGap :=
      mul_pos (sq_pos_of_ne_zero hmass) hgap
    simpa [hz, positiveQuadratic, FiniteQuadratic.qform] using hpositive
  · exact add_pos_of_pos_of_nonneg (datum.positiveQuadratic_pos hz)
      (mul_nonneg (sq_nonneg _) hgap.le)

theorem cartanQuadratic_nonneg_of_capacityGap_eq_zero {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) (hgap : datum.capacityGap = 0)
    (x : Fin n → ℝ) : 0 ≤ datum.cartanQuadratic x := by
  rw [datum.cartanQuadratic_eq_centered_capacity, hgap]
  simp only [mul_zero, add_zero]
  exact datum.positiveQuadratic_nonneg _

theorem cartanQuadratic_eq_zero_of_capacityGap_eq_zero_iff_centered {n : ℕ}
    [Nonempty (Fin n)] (datum : CertifiedFissionDatum n)
    (hgap : datum.capacityGap = 0) (x : Fin n → ℝ) :
    datum.cartanQuadratic x = 0 ↔ datum.centeredVector x = 0 := by
  rw [datum.cartanQuadratic_eq_centered_capacity, hgap]
  simp only [mul_zero, add_zero]
  constructor
  · intro hzero
    by_contra hz
    have := datum.positiveQuadratic_pos hz
    linarith
  · intro hz
    rw [hz]
    simp [positiveQuadratic, FiniteQuadratic.qform]

theorem centeredVector_eq_zero_iff_mem_capacityLine {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) (x : Fin n → ℝ) :
    datum.centeredVector x = 0 ↔ ∃ a : ℝ, x = a • datum.capacityVector := by
  constructor
  · intro hz
    refine ⟨datum.totalRamification x / datum.capacity, ?_⟩
    calc
      x = datum.centeredVector x +
          (datum.totalRamification x / datum.capacity) • datum.capacityVector :=
        datum.centeredVector_decomposition x
      _ = (datum.totalRamification x / datum.capacity) • datum.capacityVector := by
        rw [hz]
        simp
  · rintro ⟨a, rfl⟩
    have hc : datum.capacity ≠ 0 := ne_of_gt datum.capacity_pos
    have hmass : datum.totalRamification (a • datum.capacityVector) =
        a * datum.capacity := by
      change datum.massLinear (a • datum.capacityVector) = a * datum.capacity
      rw [LinearMap.map_smul, datum.massLinear_apply,
        datum.totalRamification_capacityVector]
      simp [smul_eq_mul]
    simp only [centeredVector, hmass]
    field_simp
    simp

theorem cartanQuadratic_eq_zero_of_capacityGap_eq_zero_iff_capacityLine {n : ℕ}
    [Nonempty (Fin n)] (datum : CertifiedFissionDatum n)
    (hgap : datum.capacityGap = 0) (x : Fin n → ℝ) :
    datum.cartanQuadratic x = 0 ↔ ∃ a : ℝ, x = a • datum.capacityVector := by
  rw [datum.cartanQuadratic_eq_zero_of_capacityGap_eq_zero_iff_centered hgap,
    datum.centeredVector_eq_zero_iff_mem_capacityLine]

theorem centeredVector_capacityVector {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) :
    datum.centeredVector datum.capacityVector = 0 := by
  apply (datum.centeredVector_eq_zero_iff_mem_capacityLine _).2
  exact ⟨1, by simp⟩

theorem capacityVector_ne_zero {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) : datum.capacityVector ≠ 0 := by
  intro hzero
  have hmul := datum.positiveMatrix_mulVec_capacityVector
  rw [hzero, Matrix.mulVec_zero] at hmul
  exact datum.ramificationVector_ne_zero hmul.symm

theorem cartanQuadratic_capacityVector {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) :
    datum.cartanQuadratic datum.capacityVector =
      datum.capacity ^ 2 * datum.capacityGap := by
  rw [datum.cartanQuadratic_eq_centered_capacity,
    datum.centeredVector_capacityVector,
    datum.totalRamification_capacityVector]
  simp [positiveQuadratic, FiniteQuadratic.qform]

theorem cartanQuadratic_capacityVector_neg_of_capacityGap_neg {n : ℕ}
    [Nonempty (Fin n)] (datum : CertifiedFissionDatum n)
    (hgap : datum.capacityGap < 0) :
    datum.cartanQuadratic datum.capacityVector < 0 := by
  rw [datum.cartanQuadratic_capacityVector]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos datum.capacity_pos) hgap

/-- Below the capacity wall, the universal form has exactly one negative square. -/
theorem cartanForm_sigNeg_eq_one_of_capacityGap_neg {n : ℕ} [Nonempty (Fin n)]
    (datum : CertifiedFissionDatum n) (hgap : datum.capacityGap < 0) :
    sigNeg datum.cartanForm = 1 := by
  have hinvpos : 0 < datum.capacity⁻¹ := inv_pos.mpr datum.capacity_pos
  have hroot : 0 ≤ datum.rootDefect := by
    have hlt : datum.capacity⁻¹ < datum.rootDefect := by
      simpa [capacityGap] using hgap
    linarith
  have hupper := datum.cartanForm_sigNeg_le_one hroot
  have hnegative : datum.cartanForm datum.capacityVector < 0 := by
    rw [datum.cartanForm_apply]
    exact datum.cartanQuadratic_capacityVector_neg_of_capacityGap_neg hgap
  have hlower := sigNeg_pos_of_exists_negativeVector datum.cartanForm
    datum.capacityVector_ne_zero hnegative
  omega

end CertifiedFissionDatum

end IrregularStokes
end GaloisForLFunctions
