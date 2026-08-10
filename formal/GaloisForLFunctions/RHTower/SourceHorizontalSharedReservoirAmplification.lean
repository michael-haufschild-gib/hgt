import GaloisForLFunctions.RHTower.SourceHorizontalMomentNeutralAmplification
import GaloisForLFunctions.HTGeometry.KreinLangerInertia
import GaloisForLFunctions.HTGeometry.StokesCartanLorentzCapacity
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Source-horizontal shared-reservoir amplification

A same-sign source packet is polarized by `diag(w) - sqrt(w) sqrt(w)ᵀ`.  One shared
negative reservoir produces exact inertia `(m - 1, 1, 0)`; source reflection negates
the form and reverses the two nonzero indices.  Off-diagonal triples recover every
original prime coefficient, while sufficiently far prime labels make Frobenius square
arbitrarily small.  All statements are unconditional.  This module isolates the exact
positive survivor of the independent-block rank–trace obstruction; it does not assert RH.
-/

open scoped BigOperators
open Matrix

namespace RHTower

noncomputable section

def reservoirSumLinear (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

def reservoirBaseForm (m : ℕ) : QuadraticForm ℝ (Fin m → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin m => (1 : ℝ)) -
    QuadraticMap.sq.comp (reservoirSumLinear m)

theorem reservoirBaseForm_apply (m : ℕ) (x : Fin m → ℝ) :
    reservoirBaseForm m x = (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 := by
  simp [reservoirBaseForm, reservoirSumLinear,
    QuadraticMap.weightedSumSquares_apply, QuadraticMap.sq_apply,
    QuadraticMap.comp_apply, pow_two]

theorem reservoirBaseForm_sigNeg_le_one (m : ℕ) :
    sigNeg (reservoirBaseForm m) ≤ 1 := by
  apply GaloisForLFunctions.sigNeg_le_one_of_add_sq_nonneg
    (reservoirBaseForm m) (reservoirSumLinear m)
  intro x
  rw [reservoirBaseForm_apply]
  change 0 ≤ (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 + (∑ i, x i) ^ 2
  have hsquares : 0 ≤ ∑ i : Fin m, x i ^ 2 :=
    Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (x i))
  linarith

def reservoirOne (m : ℕ) : Fin m → ℝ := fun _ => 1

theorem reservoirBaseForm_one (m : ℕ) :
    reservoirBaseForm m (reservoirOne m) = (m : ℝ) - (m : ℝ) ^ 2 := by
  rw [reservoirBaseForm_apply]
  simp [reservoirOne]

theorem reservoirOne_ne_zero {m : ℕ} (hm : 0 < m) : reservoirOne m ≠ 0 := by
  intro h
  have hi := congrFun h ⟨0, hm⟩
  norm_num [reservoirOne] at hi

theorem reservoirBaseForm_sigNeg {m : ℕ} (hm : 2 ≤ m) :
    sigNeg (reservoirBaseForm m) = 1 := by
  have hupper := reservoirBaseForm_sigNeg_le_one m
  have hneg : reservoirBaseForm m (reservoirOne m) < 0 := by
    rw [reservoirBaseForm_one]
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hlower := GaloisForLFunctions.IrregularStokes.sigNeg_pos_of_exists_negativeVector
    (reservoirBaseForm m) (reservoirOne_ne_zero (by omega)) hneg
  omega

theorem reservoirSumLinear_surjective {m : ℕ} (hm : 0 < m) :
    Function.Surjective (reservoirSumLinear m) := by
  intro r
  refine ⟨Pi.single (⟨0, hm⟩ : Fin m) r, ?_⟩
  simp [reservoirSumLinear]

theorem finrank_reservoirSumLinear_ker {m : ℕ} (hm : 0 < m) :
    Module.finrank ℝ (reservoirSumLinear m).ker = m - 1 := by
  have hrange : (reservoirSumLinear m).range = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ (reservoirSumLinear_surjective hm)
  have hdim := LinearMap.finrank_range_add_finrank_ker (reservoirSumLinear m)
  rw [hrange] at hdim
  have htop : Module.finrank ℝ (⊤ : Submodule ℝ ℝ) = 1 := by simp
  rw [htop, Module.finrank_fin_fun ℝ] at hdim
  omega

theorem reservoirBaseForm_restrict_ker_posDef {m : ℕ} :
    ((reservoirBaseForm m).restrict (reservoirSumLinear m).ker).PosDef := by
  intro x hx
  rw [QuadraticMap.restrict_apply, reservoirBaseForm_apply]
  have hsum : ∑ i, (x.1 i) = 0 := x.2
  rw [hsum, zero_pow (by norm_num), sub_zero]
  have hex : ∃ i : Fin m, x.1 i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hx
    apply Subtype.ext
    funext i
    exact h i
  apply Finset.sum_pos'
  · intro i _
    exact sq_nonneg _
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

theorem reservoirBaseForm_sigPos {m : ℕ} (hm : 2 ≤ m) :
    sigPos (reservoirBaseForm m) = m - 1 := by
  have hlower : m - 1 ≤ sigPos (reservoirBaseForm m) := by
    rw [← finrank_reservoirSumLinear_ker (by omega : 0 < m)]
    exact le_sigPos_of_posDef (reservoirBaseForm m)
      reservoirBaseForm_restrict_ker_posDef
  have hsignature := (reservoirBaseForm m).sigPos_add_sigNeg_add_radical
  rw [reservoirBaseForm_sigNeg hm, Module.finrank_fin_fun ℝ] at hsignature
  omega

theorem reservoirBaseForm_radical_finrank {m : ℕ} (hm : 2 ≤ m) :
    Module.finrank ℝ (reservoirBaseForm m).radical = 0 := by
  have hsignature := (reservoirBaseForm m).sigPos_add_sigNeg_add_radical
  rw [reservoirBaseForm_sigPos hm, reservoirBaseForm_sigNeg hm,
    Module.finrank_fin_fun ℝ] at hsignature
  omega

def reservoirScaleLinear {m : ℕ} (w : Fin m → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun x i := Real.sqrt (w i) * x i
  map_add' x y := by funext i; simp [mul_add]
  map_smul' c x := by funext i; simp [mul_left_comm]

def reservoirWeightedForm {m : ℕ} (w : Fin m → ℝ) :
    QuadraticForm ℝ (Fin m → ℝ) :=
  (reservoirBaseForm m).comp (reservoirScaleLinear w)

def reservoirScaleEquiv {m : ℕ} (w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) where
  toFun x i := Real.sqrt (w i) * x i
  invFun x i := x i / Real.sqrt (w i)
  left_inv x := by
    funext i
    field_simp [ne_of_gt (Real.sqrt_pos.2 (hw i))]
  right_inv x := by
    funext i
    field_simp [ne_of_gt (Real.sqrt_pos.2 (hw i))]
  map_add' x y := by funext i; simp [mul_add]
  map_smul' c x := by funext i; simp [mul_left_comm]

theorem reservoirWeightedForm_equivalent_base {m : ℕ} (w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) :
    QuadraticMap.Equivalent (reservoirWeightedForm w) (reservoirBaseForm m) := by
  let e := reservoirScaleEquiv w hw
  refine ⟨{ toLinearEquiv := e
            map_app' := ?_ }⟩
  intro x
  rfl

theorem reservoirWeightedForm_sigPos {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 < w i) (hm : 2 ≤ m) :
    sigPos (reservoirWeightedForm w) = m - 1 := by
  rw [(reservoirWeightedForm_equivalent_base w hw).sigPos_eq,
    reservoirBaseForm_sigPos hm]

theorem reservoirWeightedForm_sigNeg {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 < w i) (hm : 2 ≤ m) :
    sigNeg (reservoirWeightedForm w) = 1 := by
  rw [(reservoirWeightedForm_equivalent_base w hw).sigNeg_eq,
    reservoirBaseForm_sigNeg hm]

theorem reservoirWeightedForm_radical_finrank {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 < w i) (hm : 2 ≤ m) :
    Module.finrank ℝ (reservoirWeightedForm w).radical = 0 := by
  rw [(reservoirWeightedForm_equivalent_base w hw).rank_radical_eq,
    reservoirBaseForm_radical_finrank hm]

def sourceSharedReservoirMatrix {m : ℕ} (w : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal w - Matrix.vecMulVec (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i))

theorem sourceSharedReservoirMatrix_apply {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 ≤ w i) (i j : Fin m) :
    sourceSharedReservoirMatrix w i j =
      if i = j then 0 else -(Real.sqrt (w i) * Real.sqrt (w j)) := by
  by_cases hij : i = j
  · subst j
    simp only [sourceSharedReservoirMatrix, Matrix.sub_apply,
      Matrix.diagonal_apply_eq, Matrix.vecMulVec_apply, if_pos]
    rw [← pow_two, Real.sq_sqrt (hw i)]
    ring
  · simp [sourceSharedReservoirMatrix,
      Matrix.vecMulVec, hij]

theorem sourceSharedReservoirMatrix_trace {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    (sourceSharedReservoirMatrix w).trace = 0 := by
  rw [sourceSharedReservoirMatrix, Matrix.trace_sub,
    Matrix.trace_diagonal, Matrix.trace_vecMulVec]
  simp [dotProduct, hw]

theorem sourceSharedReservoirMatrix_toQuadraticForm {m : ℕ}
    {w : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i) :
    (sourceSharedReservoirMatrix w).toQuadraticForm' =
      reservoirWeightedForm w := by
  ext x
  rw [reservoirWeightedForm, QuadraticMap.comp_apply,
    reservoirBaseForm_apply]
  simp only [reservoirScaleLinear]
  simp [sourceSharedReservoirMatrix, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply',
    Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Matrix.vecMulVec,
    Finset.mul_sum, Finset.sum_mul, pow_two]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hsqrt : Real.sqrt (w i) ^ 2 = w i := Real.sq_sqrt (hw i)
    calc
      x i * (w i * x i) = w i * x i ^ 2 := by ring
      _ = Real.sqrt (w i) ^ 2 * x i ^ 2 := by rw [hsqrt]
      _ = Real.sqrt (w i) * x i * (Real.sqrt (w i) * x i) := by ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

def sourceSharedReservoirFrobSq {m : ℕ} (w : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, (sourceSharedReservoirMatrix w i j) ^ 2

theorem sourceSharedReservoirMatrix_entry_sq {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 ≤ w i) (i j : Fin m) :
    (sourceSharedReservoirMatrix w i j) ^ 2 =
      w i * w j - if i = j then w i ^ 2 else 0 := by
  rw [sourceSharedReservoirMatrix_apply hw]
  by_cases hij : i = j
  · subst j
    simp [pow_two]
  · rw [if_neg hij, if_neg hij, sub_zero, neg_sq]
    rw [mul_pow, Real.sq_sqrt (hw i), Real.sq_sqrt (hw j)]

theorem sourceSharedReservoirFrobSq_eq {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    sourceSharedReservoirFrobSq w =
      (∑ i, w i) ^ 2 - ∑ i, w i ^ 2 := by
  rw [sourceSharedReservoirFrobSq]
  simp_rw [sourceSharedReservoirMatrix_entry_sq hw,
    Finset.sum_sub_distrib]
  have hprod : (∑ i, w i) ^ 2 = ∑ i, ∑ j, w i * w j := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hdiag : (∑ i, ∑ j, if i = j then w i ^ 2 else 0) =
      ∑ i, w i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  rw [← hprod, hdiag]

def orientedSourceSharedReservoirMatrix {m : ℕ} (s : ℝ) (w : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  s • sourceSharedReservoirMatrix w

theorem orientedSourceSharedReservoirMatrix_apply {m : ℕ} {s : ℝ}
    {w : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i) (i j : Fin m) :
    orientedSourceSharedReservoirMatrix s w i j =
      if i = j then 0 else -s * (Real.sqrt (w i) * Real.sqrt (w j)) := by
  rw [orientedSourceSharedReservoirMatrix, Matrix.smul_apply,
    sourceSharedReservoirMatrix_apply hw]
  split_ifs <;> ring

theorem orientedSourceSharedReservoirMatrix_trace {m : ℕ} {s : ℝ}
    {w : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i) :
    (orientedSourceSharedReservoirMatrix s w).trace = 0 := by
  rw [orientedSourceSharedReservoirMatrix, Matrix.trace_smul,
    sourceSharedReservoirMatrix_trace hw, smul_zero]

theorem orientedSourceSharedReservoirMatrix_toQuadraticForm_one {m : ℕ}
    {w : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i) :
    (orientedSourceSharedReservoirMatrix 1 w).toQuadraticForm' =
      reservoirWeightedForm w := by
  simpa [orientedSourceSharedReservoirMatrix] using
    sourceSharedReservoirMatrix_toQuadraticForm hw

theorem orientedSourceSharedReservoirMatrix_toQuadraticForm_neg_one {m : ℕ}
    {w : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i) :
    (orientedSourceSharedReservoirMatrix (-1) w).toQuadraticForm' =
      -(reservoirWeightedForm w) := by
  ext x
  rw [orientedSourceSharedReservoirMatrix]
  simp only [neg_smul, one_smul, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply',
    Matrix.mulVec, dotProduct, QuadraticMap.neg_apply]
  rw [← sourceSharedReservoirMatrix_toQuadraticForm hw]
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct]
  simp [Finset.sum_neg_distrib]

theorem orientedSourceSharedReservoirFrobSq_eq {m : ℕ} {s : ℝ}
    {w : Fin m → ℝ} (hs : s ^ 2 = 1) :
    (∑ i, ∑ j, (orientedSourceSharedReservoirMatrix s w i j) ^ 2) =
      sourceSharedReservoirFrobSq w := by
  simp [orientedSourceSharedReservoirMatrix, sourceSharedReservoirFrobSq,
    mul_pow, hs]

theorem orientedSourceSharedReservoir_reconstruct {m : ℕ} {s : ℝ}
    {w : Fin m → ℝ} (hs : s ^ 2 = 1) (hw : ∀ i, 0 < w i)
    {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    -(orientedSourceSharedReservoirMatrix s w i j *
          orientedSourceSharedReservoirMatrix s w i k /
        orientedSourceSharedReservoirMatrix s w j k) = s * w i := by
  rw [orientedSourceSharedReservoirMatrix_apply (fun i => (hw i).le) i j,
    orientedSourceSharedReservoirMatrix_apply (fun i => (hw i).le) i k,
    orientedSourceSharedReservoirMatrix_apply (fun i => (hw i).le) j k,
    if_neg hij, if_neg hik, if_neg hjk]
  have hsi : Real.sqrt (w i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hw i))
  have hsj : Real.sqrt (w j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hw j))
  have hsk : Real.sqrt (w k) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hw k))
  have hs0 : s ≠ 0 := by nlinarith
  have hi : Real.sqrt (w i) ^ 2 = w i := Real.sq_sqrt (hw i).le
  field_simp
  nlinarith [hi]

def sourceZeroHorizontalOrientation (q : XiZeroCopy) : ℝ :=
  Real.sign (sourceZeroHorizontalTailLog q)

def sourceZeroHorizontalSharedWeights {m : ℕ}
    (q : XiZeroCopy) (p : Fin m → Nat.Primes) : Fin m → ℝ :=
  fun i => |sourceZeroHorizontalPrimeCarrier q (p i)|

def sourceZeroHorizontalSharedReservoirMatrix {m : ℕ}
    (q : XiZeroCopy) (p : Fin m → Nat.Primes) : Matrix (Fin m) (Fin m) ℝ :=
  orientedSourceSharedReservoirMatrix (sourceZeroHorizontalOrientation q)
    (sourceZeroHorizontalSharedWeights q p)

theorem sourceZeroHorizontalTailLog_pos_of_left
    (q : XiZeroCopy) (hleft : (q.1 : ℂ).re < 1 / 2) :
    0 < sourceZeroHorizontalTailLog q := by
  rw [(completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog 0 q).2]
  exact mul_pos (by linarith) (Real.log_pos (by norm_num))

theorem sourceZeroHorizontalTailLog_neg_of_right
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re) :
    sourceZeroHorizontalTailLog q < 0 := by
  rw [(completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog 0 q).2]
  exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num))

theorem sourceZeroHorizontalOrientation_eq_one_of_left
    (q : XiZeroCopy) (hleft : (q.1 : ℂ).re < 1 / 2) :
    sourceZeroHorizontalOrientation q = 1 := by
  rw [sourceZeroHorizontalOrientation,
    Real.sign_of_pos (sourceZeroHorizontalTailLog_pos_of_left q hleft)]

theorem sourceZeroHorizontalOrientation_eq_neg_one_of_right
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re) :
    sourceZeroHorizontalOrientation q = -1 := by
  rw [sourceZeroHorizontalOrientation,
    Real.sign_of_neg (sourceZeroHorizontalTailLog_neg_of_right q hright)]

theorem sourceZeroHorizontalOrientation_sq_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    sourceZeroHorizontalOrientation q ^ 2 = 1 := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · rw [sourceZeroHorizontalOrientation_eq_one_of_left q hleft]
    norm_num
  · rw [sourceZeroHorizontalOrientation_eq_neg_one_of_right q hright]
    norm_num

theorem sourceZeroHorizontalOrientation_mul_abs_carrier
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) (p : Nat.Primes) :
    sourceZeroHorizontalOrientation q *
        |sourceZeroHorizontalPrimeCarrier q p| =
      sourceZeroHorizontalPrimeCarrier q p := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · rw [sourceZeroHorizontalOrientation_eq_one_of_left q hleft,
      abs_of_pos (sourceZeroHorizontalPrimeCarrier_pos_of_leftHalf q hleft p)]
    ring
  · rw [sourceZeroHorizontalOrientation_eq_neg_one_of_right q hright,
      abs_of_neg (sourceZeroHorizontalPrimeCarrier_neg_of_rightHalf q hright p)]
    ring

theorem sourceZeroHorizontalSharedWeights_pos {m : ℕ}
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (p : Fin m → Nat.Primes) (i : Fin m) :
    0 < sourceZeroHorizontalSharedWeights q p i := by
  rw [sourceZeroHorizontalSharedWeights, abs_pos]
  intro hzero
  exact hoff ((sourceZeroHorizontalPrimeCarrier_eq_zero_iff q (p i)).1 hzero)

@[simp] theorem sourceZeroHorizontalOrientation_reflection (q : XiZeroCopy) :
    sourceZeroHorizontalOrientation (xiZeroCopyLineConjEquiv q) =
      -sourceZeroHorizontalOrientation q := by
  rw [sourceZeroHorizontalOrientation, sourceZeroHorizontalOrientation,
    sourceZeroHorizontalTailLog_reflection 0, Real.sign_neg]

@[simp] theorem sourceZeroHorizontalSharedWeights_reflection {m : ℕ}
    (q : XiZeroCopy) (p : Fin m → Nat.Primes) :
    sourceZeroHorizontalSharedWeights (xiZeroCopyLineConjEquiv q) p =
      sourceZeroHorizontalSharedWeights q p := by
  funext i
  rw [sourceZeroHorizontalSharedWeights, sourceZeroHorizontalSharedWeights,
    sourceZeroHorizontalPrimeCarrier_reflection, abs_neg]

@[simp] theorem sourceZeroHorizontalSharedReservoirMatrix_reflection {m : ℕ}
    (q : XiZeroCopy) (p : Fin m → Nat.Primes) :
    sourceZeroHorizontalSharedReservoirMatrix (xiZeroCopyLineConjEquiv q) p =
      -sourceZeroHorizontalSharedReservoirMatrix q p := by
  rw [sourceZeroHorizontalSharedReservoirMatrix,
    sourceZeroHorizontalSharedReservoirMatrix,
    sourceZeroHorizontalOrientation_reflection,
    sourceZeroHorizontalSharedWeights_reflection]
  ext i j
  simp [orientedSourceSharedReservoirMatrix]

theorem sourceZeroHorizontalSharedReservoirMatrix_trace {m : ℕ}
    (q : XiZeroCopy) (p : Fin m → Nat.Primes) :
    (sourceZeroHorizontalSharedReservoirMatrix q p).trace = 0 := by
  apply orientedSourceSharedReservoirMatrix_trace
  intro i
  exact abs_nonneg _

theorem sourceZeroHorizontalSharedReservoirMatrix_reconstruct {m : ℕ}
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (p : Fin m → Nat.Primes) {i j k : Fin m}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    -(sourceZeroHorizontalSharedReservoirMatrix q p i j *
          sourceZeroHorizontalSharedReservoirMatrix q p i k /
        sourceZeroHorizontalSharedReservoirMatrix q p j k) =
      sourceZeroHorizontalPrimeCarrier q (p i) := by
  rw [sourceZeroHorizontalSharedReservoirMatrix]
  calc
    -(orientedSourceSharedReservoirMatrix (sourceZeroHorizontalOrientation q)
          (sourceZeroHorizontalSharedWeights q p) i j *
        orientedSourceSharedReservoirMatrix (sourceZeroHorizontalOrientation q)
          (sourceZeroHorizontalSharedWeights q p) i k /
        orientedSourceSharedReservoirMatrix (sourceZeroHorizontalOrientation q)
          (sourceZeroHorizontalSharedWeights q p) j k) =
        sourceZeroHorizontalOrientation q *
          sourceZeroHorizontalSharedWeights q p i :=
      orientedSourceSharedReservoir_reconstruct
        (sourceZeroHorizontalOrientation_sq_of_offLine q hoff)
        (sourceZeroHorizontalSharedWeights_pos q hoff p) hij hik hjk
    _ = sourceZeroHorizontalPrimeCarrier q (p i) :=
      sourceZeroHorizontalOrientation_mul_abs_carrier q hoff (p i)

theorem sourceZeroHorizontalSharedReservoirMatrix_inertia_of_left {m : ℕ}
    (q : XiZeroCopy) (hleft : (q.1 : ℂ).re < 1 / 2)
    (p : Fin m → Nat.Primes) (hm : 2 ≤ m) :
    sigPos (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' = m - 1 ∧
      sigNeg (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' = 1 ∧
      Module.finrank ℝ
        (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm'.radical = 0 := by
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := ne_of_lt hleft
  have hw : ∀ i, 0 < sourceZeroHorizontalSharedWeights q p i :=
    sourceZeroHorizontalSharedWeights_pos q hoff p
  have hform :
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' =
        reservoirWeightedForm (sourceZeroHorizontalSharedWeights q p) := by
    rw [sourceZeroHorizontalSharedReservoirMatrix,
      sourceZeroHorizontalOrientation_eq_one_of_left q hleft]
    exact orientedSourceSharedReservoirMatrix_toQuadraticForm_one (fun i => (hw i).le)
  rw [hform]
  exact ⟨reservoirWeightedForm_sigPos hw hm,
    reservoirWeightedForm_sigNeg hw hm,
    reservoirWeightedForm_radical_finrank hw hm⟩

theorem sourceZeroHorizontalSharedReservoirMatrix_inertia_of_right {m : ℕ}
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re)
    (p : Fin m → Nat.Primes) (hm : 2 ≤ m) :
    sigPos (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' = 1 ∧
      sigNeg (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' = m - 1 ∧
      Module.finrank ℝ
        (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm'.radical = 0 := by
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := ne_of_gt hright
  have hw : ∀ i, 0 < sourceZeroHorizontalSharedWeights q p i :=
    sourceZeroHorizontalSharedWeights_pos q hoff p
  have hform :
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' =
        -(reservoirWeightedForm (sourceZeroHorizontalSharedWeights q p)) := by
    rw [sourceZeroHorizontalSharedReservoirMatrix,
      sourceZeroHorizontalOrientation_eq_neg_one_of_right q hright]
    exact orientedSourceSharedReservoirMatrix_toQuadraticForm_neg_one (fun i => (hw i).le)
  rw [hform]
  refine ⟨?_, ?_, ?_⟩
  · rw [sigPos_neg]
    exact reservoirWeightedForm_sigNeg hw hm
  · rw [sigNeg_neg]
    exact reservoirWeightedForm_sigPos hw hm
  · have hsignature := (-(reservoirWeightedForm
        (sourceZeroHorizontalSharedWeights q p))).sigPos_add_sigNeg_add_radical
    rw [sigPos_neg, sigNeg_neg, reservoirWeightedForm_sigNeg hw hm,
      reservoirWeightedForm_sigPos hw hm, Module.finrank_fin_fun ℝ] at hsignature
    omega

theorem exists_sourceZeroHorizontalSharedReservoirPacket
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (m : ℕ) (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Fin m → Nat.Primes,
      Function.Injective p ∧
      (∀ i,
        sourceZeroHorizontalPrimeCarrier q (p i) ≠ 0 ∧
        sourceZeroHorizontalSharedWeights q p i < ε / (m : ℝ)) ∧
      sourceSharedReservoirFrobSq (sourceZeroHorizontalSharedWeights q p) < ε ^ 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hδ : 0 < ε / (m : ℝ) := div_pos hε hmR
  obtain ⟨K, hKcard, hKsmall, -⟩ :=
    exists_sourceZeroHorizontalMomentNeutralPacket q hoff m hδ
  let e : Fin m ≃ ↥K := (K.equivFinOfCardEq hKcard).symm
  let p : Fin m → Nat.Primes := fun i => (e i).1
  have hpInjective : Function.Injective p := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  have hsmall : ∀ i,
      sourceZeroHorizontalPrimeCarrier q (p i) ≠ 0 ∧
        sourceZeroHorizontalSharedWeights q p i < ε / (m : ℝ) := by
    intro i
    have hi := hKsmall (p i) (e i).2
    exact ⟨hi.1, hi.2⟩
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hsum : (∑ i, sourceZeroHorizontalSharedWeights q p i) < ε := by
    calc
      (∑ i, sourceZeroHorizontalSharedWeights q p i) <
          ∑ _i : Fin m, ε / (m : ℝ) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun i _ => (hsmall i).2)
      _ = ε := by
        simp [div_eq_mul_inv]
        field_simp
  have hsum0 : 0 ≤ ∑ i, sourceZeroHorizontalSharedWeights q p i :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsumSq : (∑ i, sourceZeroHorizontalSharedWeights q p i) ^ 2 < ε ^ 2 :=
    (sq_lt_sq₀ hsum0 hε.le).2 hsum
  have hw0 : ∀ i, 0 ≤ sourceZeroHorizontalSharedWeights q p i :=
    fun i => abs_nonneg _
  refine ⟨p, hpInjective, hsmall, ?_⟩
  rw [sourceSharedReservoirFrobSq_eq hw0]
  calc
    (∑ i, sourceZeroHorizontalSharedWeights q p i) ^ 2 -
        ∑ i, sourceZeroHorizontalSharedWeights q p i ^ 2 ≤
      (∑ i, sourceZeroHorizontalSharedWeights q p i) ^ 2 :=
        sub_le_self _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
    _ < ε ^ 2 := hsumSq

theorem sourceZeroHorizontalSharedReservoirFrobSq {m : ℕ}
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (p : Fin m → Nat.Primes) :
    (∑ i, ∑ j, (sourceZeroHorizontalSharedReservoirMatrix q p i j) ^ 2) =
      sourceSharedReservoirFrobSq (sourceZeroHorizontalSharedWeights q p) := by
  rw [sourceZeroHorizontalSharedReservoirMatrix]
  exact orientedSourceSharedReservoirFrobSq_eq
    (sourceZeroHorizontalOrientation_sq_of_offLine q hoff)

/-- Actual source-labelled shared-reservoir amplification.  The prime labels are injective, every
coefficient remains nonzero and recoverable, trace is zero, Frobenius square is arbitrarily small,
reflection negates the matrix, and the exact inertia is orientation-sensitive. -/
theorem exists_sourceZeroHorizontalSharedReservoirAmplification
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (m : ℕ) (hm : 2 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Fin m → Nat.Primes,
      Function.Injective p ∧
      (∀ i,
        sourceZeroHorizontalPrimeCarrier q (p i) ≠ 0 ∧
        sourceZeroHorizontalSharedWeights q p i < ε / (m : ℝ)) ∧
      (sourceZeroHorizontalSharedReservoirMatrix q p).trace = 0 ∧
      (∑ i, ∑ j,
        (sourceZeroHorizontalSharedReservoirMatrix q p i j) ^ 2) < ε ^ 2 ∧
      sourceZeroHorizontalSharedReservoirMatrix (xiZeroCopyLineConjEquiv q) p =
        -sourceZeroHorizontalSharedReservoirMatrix q p ∧
      ((q.1 : ℂ).re < 1 / 2 ∧
          sigPos (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' = m - 1 ∧
          sigNeg (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' = 1 ∧
          Module.finrank ℝ
            (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm'.radical = 0 ∨
        1 / 2 < (q.1 : ℂ).re ∧
          sigPos (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' = 1 ∧
          sigNeg (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' = m - 1 ∧
          Module.finrank ℝ
            (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm'.radical = 0) := by
  obtain ⟨p, hp, hsmall, henergy⟩ :=
    exists_sourceZeroHorizontalSharedReservoirPacket q hoff m (by omega) hε
  refine ⟨p, hp, hsmall, sourceZeroHorizontalSharedReservoirMatrix_trace q p, ?_,
    sourceZeroHorizontalSharedReservoirMatrix_reflection q p, ?_⟩
  · rw [sourceZeroHorizontalSharedReservoirFrobSq q hoff p]
    exact henergy
  · rcases lt_or_gt_of_ne hoff with hleft | hright
    · exact Or.inl ⟨hleft,
        sourceZeroHorizontalSharedReservoirMatrix_inertia_of_left q hleft p hm⟩
    · exact Or.inr ⟨hright,
        sourceZeroHorizontalSharedReservoirMatrix_inertia_of_right q hright p hm⟩

end

end RHTower
