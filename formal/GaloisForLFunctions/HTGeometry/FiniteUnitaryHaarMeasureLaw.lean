import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Normalized Haar probability on finite unitary groups

Mathlib defines the algebraic finite unitary group and general Haar measure,
but does not currently package the compact topological-group instances for
finite complex matrices.  This module supplies those instances, normalizes
Haar measure on the whole unitary group, and constructs the permutation and
two-coordinate Hadamard unitaries needed for the exact Haar second-moment
calculation.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

instance finiteUnitaryIsTopologicalGroup
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsTopologicalGroup (Matrix.unitaryGroup ι ℂ) where
  continuous_mul := continuous_mul
  continuous_inv := by
    apply continuous_induced_rng.2
    change Continuous (fun U : Matrix.unitaryGroup ι ℂ =>
      star (U.1 : Matrix ι ι ℂ))
    fun_prop

noncomputable instance finiteUnitaryCompactSpace
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    CompactSpace (Matrix.unitaryGroup ι ℂ) := by
  refine isCompact_iff_compactSpace.mp ?_
  have hclosed : IsClosed
      {A : Matrix ι ι ℂ | A * star A = 1} :=
    isClosed_eq
      (by fun_prop :
        Continuous (fun A : Matrix ι ι ℂ =>
          A * star A))
      continuous_const
  have hK : IsCompact
      ((Metric.closedBall (0 : ℂ) 1).matrix :
        Set (Matrix ι ι ℂ)) :=
    (isCompact_closedBall (0 : ℂ) 1).matrix
  have hcarrier :
      (↑(Matrix.unitaryGroup ι ℂ) :
        Set (Matrix ι ι ℂ)) =
        {A | A * star A = 1} := by
    ext A
    exact Matrix.mem_unitaryGroup_iff
  rw [hcarrier]
  apply hK.of_isClosed_subset hclosed
  intro A hA
  rw [Set.mem_matrix]
  intro i j
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entry_norm_bound_of_unitary
    (Matrix.mem_unitaryGroup_iff.mpr hA) i j

noncomputable instance finiteUnitaryMeasurableSpace
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MeasurableSpace (Matrix.unitaryGroup ι ℂ) :=
  borel _

instance finiteUnitaryBorelSpace
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    BorelSpace (Matrix.unitaryGroup ι ℂ) :=
  ⟨rfl⟩

/-- Haar measure normalized on the entire finite unitary group. -/
def finiteUnitaryHaar
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Measure (Matrix.unitaryGroup ι ℂ) :=
  haarMeasure
    (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ :
      PositiveCompacts (Matrix.unitaryGroup ι ℂ))

/-- The normalized finite-unitary Haar measure is a probability measure. -/
theorem finiteUnitaryHaar_apply_univ
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    finiteUnitaryHaar ι Set.univ = 1 := by
  exact haarMeasure_self

/-- Left multiplication preserves every Haar integral. -/
theorem integral_finiteUnitaryHaar_mul_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Matrix.unitaryGroup ι ℂ → ℝ)
    (V : Matrix.unitaryGroup ι ℂ) :
    (∫ U, f (V * U) ∂finiteUnitaryHaar ι) =
      ∫ U, f U ∂finiteUnitaryHaar ι := by
  unfold finiteUnitaryHaar
  exact integral_mul_left_eq_self f V

/-- Squared modulus of one entry of a finite unitary. -/
def finiteUnitaryEntryWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ)
    (i j : ι) : ℝ :=
  Complex.normSq (U i j)

/-- Every unitary column has total squared modulus one. -/
theorem sum_finiteUnitaryEntryWeight_column
    {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (j : Fin d) :
    ∑ i, finiteUnitaryEntryWeight U i j = 1 := by
  have h := congrArg
    (fun M : Matrix (Fin d) (Fin d) ℂ => M j j)
    (Matrix.UnitaryGroup.star_mul_self U)
  simp only [Matrix.mul_apply, Matrix.star_apply,
    Matrix.one_apply, if_pos] at h
  have hr := congrArg Complex.re h
  simpa [finiteUnitaryEntryWeight,
    ← Complex.normSq_eq_conj_mul_self] using hr

/-- Unitary permutation matrix associated to a finite coordinate
permutation. -/
def finiteUnitaryPermutation {d : ℕ}
    (e : Fin d ≃ Fin d) :
    Matrix.unitaryGroup (Fin d) ℂ := by
  let U : Matrix (Fin d) (Fin d) ℂ :=
    fun i j => if i = e j then 1 else 0
  refine ⟨U, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  ext i j
  have heq (a x : Fin d) :
      a = e x ↔ e.symm a = x := by
    constructor
    · intro h
      simp [h]
    · intro h
      simp [← h]
  simp [U, Matrix.mul_apply, Matrix.one_apply,
    Matrix.star_apply, heq]

/-- Left multiplication by a permutation unitary permutes row weights. -/
theorem finiteUnitaryEntryWeight_permutation_mul
    {d : ℕ} (e : Fin d ≃ Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) :
    finiteUnitaryEntryWeight
        (finiteUnitaryPermutation e * U) (e i) j =
      finiteUnitaryEntryWeight U i j := by
  have heq (x : Fin d) :
      e i = e x ↔ i = x := e.injective.eq_iff
  simp [finiteUnitaryEntryWeight, finiteUnitaryPermutation,
    Matrix.mul_apply, heq]

/-- Haar fourth moments of individual entries are invariant under row
permutations. -/
theorem integral_finiteUnitaryEntryWeight_sq_equiv
    {d : ℕ} (e : Fin d ≃ Fin d) (i j : Fin d) :
    (∫ U, (finiteUnitaryEntryWeight U (e i) j) ^ 2
        ∂finiteUnitaryHaar (Fin d)) =
      ∫ U, (finiteUnitaryEntryWeight U i j) ^ 2
        ∂finiteUnitaryHaar (Fin d) := by
  have h := integral_finiteUnitaryHaar_mul_left
    (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      (finiteUnitaryEntryWeight U (e i) j) ^ 2)
    (finiteUnitaryPermutation e)
  simpa only [finiteUnitaryEntryWeight_permutation_mul] using h.symm

/-- Hadamard rotation on a distinguished two-coordinate summand, extended by
the identity on all remaining coordinates. -/
def finiteUnitaryExtendedHadamard (d : ℕ) :
    Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ := by
  let r : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  let H : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ
    | Sum.inl i, Sum.inl j =>
        if i = 1 ∧ j = 1 then -r else r
    | Sum.inr i, Sum.inr j => if i = j then 1 else 0
    | _, _ => 0
  refine ⟨H, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;>
      norm_num [H, r, Matrix.mul_apply, Matrix.one_apply,
        Matrix.star_apply, Fintype.sum_sum_type,
        Fin.sum_univ_succ] <;>
      field_simp <;>
      norm_num [Complex.ext_iff, pow_two,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · simp [H, Matrix.mul_apply,
      Matrix.star_apply, Fintype.sum_sum_type]
  · simp [H, Matrix.mul_apply,
      Matrix.star_apply, Fintype.sum_sum_type]
  · simp [H, Matrix.mul_apply, Matrix.one_apply,
      Matrix.star_apply, Fintype.sum_sum_type]

/-- Diagonal unitary multiplying the second distinguished coordinate by a
unit-modulus complex phase. -/
def finiteUnitaryDistinguishedPhase
    (d : ℕ) (z : ℂ) (hz : Complex.normSq z = 1) :
    Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ := by
  let phase : (Fin 2 ⊕ Fin d) → ℂ :=
    fun i => if i = Sum.inl 1 then z else 1
  refine ⟨Matrix.diagonal phase,
    Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  have hzstar : z * star z = 1 := by
    calc
      z * star z = (Complex.normSq z : ℂ) := by
        rw [mul_comm]
        exact Complex.normSq_eq_conj_mul_self.symm
      _ = 1 := by exact_mod_cast hz
  have hphase (i : Fin 2 ⊕ Fin d) :
      phase i * star (phase i) = 1 := by
    by_cases hi : i = Sum.inl 1
    · change (if i = Sum.inl 1 then z else 1) *
          star (if i = Sum.inl 1 then z else 1) = 1
      rw [if_pos hi, hzstar]
    · change (if i = Sum.inl 1 then z else 1) *
          star (if i = Sum.inl 1 then z else 1) = 1
      rw [if_neg hi, star_one, mul_one]
  have hphaseEnd (i : Fin 2 ⊕ Fin d) :
      phase i * starRingEnd ℂ (phase i) = 1 := by
    change phase i * star (phase i) = 1
    exact hphase i
  rw [Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    change (if i = i then
        phase i * starRingEnd ℂ (phase i) else 0) =
      (if i = i then 1 else 0)
    simp only [if_pos]
    exact hphaseEnd i
  · simp [hij]

/-- Four quarter-turn phases cancel every interference term in the fourth
power of a two-coordinate superposition. -/
theorem complex_normSq_four_phase_sum (x y : ℂ) :
    Complex.normSq (x + y) ^ 2 +
      Complex.normSq (x - y) ^ 2 +
      Complex.normSq (x + Complex.I * y) ^ 2 +
      Complex.normSq (x - Complex.I * y) ^ 2 =
    4 * (Complex.normSq x ^ 2 + Complex.normSq y ^ 2 +
      4 * Complex.normSq x * Complex.normSq y) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

/-- The distinguished output coordinate after a Hadamard preceded by a phase
rotation is the normalized superposition `x + z y`. -/
theorem finiteUnitaryEntryWeight_hadamard_phase_mul
    (d : ℕ) (z : ℂ) (hz : Complex.normSq z = 1)
    (U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ)
    (j : Fin 2 ⊕ Fin d) :
    finiteUnitaryEntryWeight
        ((finiteUnitaryExtendedHadamard d *
          finiteUnitaryDistinguishedPhase d z hz) * U)
        (Sum.inl 0) j =
      Complex.normSq
        (U (Sum.inl 0) j + z * U (Sum.inl 1) j) / 2 := by
  simp only [finiteUnitaryEntryWeight]
  change Complex.normSq
      ((((finiteUnitaryExtendedHadamard d :
          Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
            Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) *
        (finiteUnitaryDistinguishedPhase d z hz :
          Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) *
        (U : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ))
          (Sum.inl 0) j) =
      Complex.normSq
        (U (Sum.inl 0) j + z * U (Sum.inl 1) j) / 2
  simp [finiteUnitaryExtendedHadamard,
    finiteUnitaryDistinguishedPhase, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_succ,
    div_eq_mul_inv]
  field_simp
  norm_num [Complex.ext_iff, pow_two,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Haar fourth moment of one distinguished entry. -/
def finiteUnitaryHaarFourthMoment
    (d : ℕ) (j : Fin 2 ⊕ Fin d) : ℝ :=
  ∫ U, (finiteUnitaryEntryWeight U (Sum.inl 0) j) ^ 2
    ∂finiteUnitaryHaar (Fin 2 ⊕ Fin d)

/-- Haar mixed second moment of the two distinguished entry weights. -/
def finiteUnitaryHaarCrossMoment
    (d : ℕ) (j : Fin 2 ⊕ Fin d) : ℝ :=
  ∫ U, finiteUnitaryEntryWeight U (Sum.inl 0) j *
      finiteUnitaryEntryWeight U (Sum.inl 1) j
    ∂finiteUnitaryHaar (Fin 2 ⊕ Fin d)

/-- Fourth power of one normalized phased superposition of the two
distinguished column entries. -/
def finiteUnitaryMixedFourth
    (z : ℂ) {d : ℕ}
    (U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ)
    (j : Fin 2 ⊕ Fin d) : ℝ :=
  (Complex.normSq
      (U (Sum.inl 0) j + z * U (Sum.inl 1) j) / 2) ^ 2

/-- Haar invariance makes every unit-phase mixed fourth moment equal to the
unmixed fourth moment. -/
theorem integral_finiteUnitaryMixedFourth_eq
    (d : ℕ) (z : ℂ) (hz : Complex.normSq z = 1)
    (j : Fin 2 ⊕ Fin d) :
    (∫ U, finiteUnitaryMixedFourth z U j
        ∂finiteUnitaryHaar (Fin 2 ⊕ Fin d)) =
      finiteUnitaryHaarFourthMoment d j := by
  have h := integral_finiteUnitaryHaar_mul_left
    (f := fun U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ =>
      (finiteUnitaryEntryWeight U (Sum.inl 0) j) ^ 2)
    ((finiteUnitaryExtendedHadamard d *
      finiteUnitaryDistinguishedPhase d z hz))
  simpa only [finiteUnitaryMixedFourth,
    finiteUnitaryEntryWeight_hadamard_phase_mul,
    finiteUnitaryHaarFourthMoment] using h

end

end GaloisForLFunctions.HTGeometry
