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
open scoped Matrix.Norms.L2Operator

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

/-- Normalized Haar measure on a finite unitary group is a probability
measure. -/
noncomputable instance finiteUnitaryHaarIsProbabilityMeasure
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsProbabilityMeasure (finiteUnitaryHaar ι) where
  measure_univ := finiteUnitaryHaar_apply_univ ι

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

/-- Evaluation of a fixed matrix entry is continuous on the finite unitary
group. -/
theorem continuous_finiteUnitaryEntry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    Continuous
      (fun U : Matrix.unitaryGroup ι ℂ => U i j) :=
  (continuous_apply j).comp
    ((continuous_apply i).comp continuous_subtype_val)

/-- A fixed squared-modulus entry weight is continuous. -/
theorem continuous_finiteUnitaryEntryWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    Continuous
      (fun U : Matrix.unitaryGroup ι ℂ =>
        finiteUnitaryEntryWeight U i j) := by
  exact Complex.continuous_normSq.comp
    (continuous_finiteUnitaryEntry i j)

/-- Every unitary column has total squared modulus one. -/
theorem sum_finiteUnitaryEntryWeight_column
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ)
    (j : ι) :
  ∑ i, finiteUnitaryEntryWeight U i j = 1 := by
  have h := congrArg
    (fun M : Matrix ι ι ℂ => M j j)
    (Matrix.UnitaryGroup.star_mul_self U)
  simp only [Matrix.mul_apply, Matrix.star_apply,
    Matrix.one_apply, if_pos] at h
  have hr := congrArg Complex.re h
  simpa [finiteUnitaryEntryWeight,
    ← Complex.normSq_eq_conj_mul_self] using hr

/-- Unitary permutation matrix associated to a finite coordinate
permutation. -/
def finiteUnitaryPermutation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) :
    Matrix.unitaryGroup ι ℂ := by
  let U : Matrix ι ι ℂ :=
    fun i j => if i = e j then 1 else 0
  refine ⟨U, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  ext i j
  have heq (a x : ι) :
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
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι)
    (U : Matrix.unitaryGroup ι ℂ)
    (i j : ι) :
    finiteUnitaryEntryWeight
        (finiteUnitaryPermutation e * U) (e i) j =
      finiteUnitaryEntryWeight U i j := by
  have heq (x : ι) :
      e i = e x ↔ i = x := e.injective.eq_iff
  simp [finiteUnitaryEntryWeight, finiteUnitaryPermutation,
    Matrix.mul_apply, heq]

/-- Haar fourth moments of individual entries are invariant under row
permutations. -/
theorem integral_finiteUnitaryEntryWeight_sq_equiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (i j : ι) :
    (∫ U, (finiteUnitaryEntryWeight U (e i) j) ^ 2
        ∂finiteUnitaryHaar ι) =
      ∫ U, (finiteUnitaryEntryWeight U i j) ^ 2
        ∂finiteUnitaryHaar ι := by
  have h := integral_finiteUnitaryHaar_mul_left
    (fun U : Matrix.unitaryGroup ι ℂ =>
      (finiteUnitaryEntryWeight U (e i) j) ^ 2)
    (finiteUnitaryPermutation e)
  simpa only [finiteUnitaryEntryWeight_permutation_mul] using h.symm

/-- Haar first moments of individual entries are invariant under row
permutations. -/
theorem integral_finiteUnitaryEntryWeight_equiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (i j : ι) :
    (∫ U, finiteUnitaryEntryWeight U (e i) j
        ∂finiteUnitaryHaar ι) =
      ∫ U, finiteUnitaryEntryWeight U i j
        ∂finiteUnitaryHaar ι := by
  have h := integral_finiteUnitaryHaar_mul_left
    (fun U : Matrix.unitaryGroup ι ℂ =>
      finiteUnitaryEntryWeight U (e i) j)
    (finiteUnitaryPermutation e)
  simpa only [finiteUnitaryEntryWeight_permutation_mul] using h.symm

/-- Haar mixed entry moments are invariant under simultaneous row
permutations. -/
theorem integral_finiteUnitaryEntryWeight_mul_equiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (i₀ i₁ j : ι) :
    (∫ U, finiteUnitaryEntryWeight U (e i₀) j *
        finiteUnitaryEntryWeight U (e i₁) j
        ∂finiteUnitaryHaar ι) =
      ∫ U, finiteUnitaryEntryWeight U i₀ j *
        finiteUnitaryEntryWeight U i₁ j
        ∂finiteUnitaryHaar ι := by
  have h := integral_finiteUnitaryHaar_mul_left
    (fun U : Matrix.unitaryGroup ι ℂ =>
      finiteUnitaryEntryWeight U (e i₀) j *
        finiteUnitaryEntryWeight U (e i₁) j)
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

/-- Every continuous real observable is integrable against normalized Haar
measure on a finite unitary group. -/
theorem integrable_finiteUnitaryHaar_of_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Matrix.unitaryGroup ι ℂ → ℝ)
    (hf : Continuous f) :
    Integrable f (finiteUnitaryHaar ι) :=
  hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace f)

/-- Entry weights are Haar-integrable. -/
theorem integrable_finiteUnitaryEntryWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    Integrable
      (fun U : Matrix.unitaryGroup ι ℂ =>
        finiteUnitaryEntryWeight U i j)
      (finiteUnitaryHaar ι) := by
  apply integrable_finiteUnitaryHaar_of_continuous
  exact continuous_finiteUnitaryEntryWeight i j

/-- Squared entry weights are Haar-integrable. -/
theorem integrable_finiteUnitaryEntryWeight_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    Integrable
      (fun U : Matrix.unitaryGroup ι ℂ =>
        (finiteUnitaryEntryWeight U i j) ^ 2)
      (finiteUnitaryHaar ι) := by
  apply integrable_finiteUnitaryHaar_of_continuous
  exact (continuous_finiteUnitaryEntryWeight i j).pow 2

/-- Products of two entry weights are Haar-integrable. -/
theorem integrable_finiteUnitaryEntryWeight_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ i₁ j : ι) :
    Integrable
      (fun U : Matrix.unitaryGroup ι ℂ =>
        finiteUnitaryEntryWeight U i₀ j *
          finiteUnitaryEntryWeight U i₁ j)
      (finiteUnitaryHaar ι) := by
  apply integrable_finiteUnitaryHaar_of_continuous
  exact (continuous_finiteUnitaryEntryWeight i₀ j).mul
    (continuous_finiteUnitaryEntryWeight i₁ j)

/-- Every entry of a Haar unitary has mean squared modulus equal to the
reciprocal matrix dimension. -/
theorem integral_finiteUnitaryEntryWeight_eq_card_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    (∫ U, finiteUnitaryEntryWeight U i j
        ∂finiteUnitaryHaar ι) =
      (Fintype.card ι : ℝ)⁻¹ := by
  letI : Nonempty ι := ⟨i⟩
  let μ := finiteUnitaryHaar ι
  let moment := fun k : ι =>
    ∫ U, finiteUnitaryEntryWeight U k j ∂μ
  have hall (k : ι) : moment k = moment i := by
    have h := integral_finiteUnitaryEntryWeight_equiv
      (Equiv.swap i k) i j
    simpa [μ, moment] using h
  have hsum :
      (∫ U, ∑ k, finiteUnitaryEntryWeight U k j ∂μ) =
        ∑ k, moment k := by
    simpa [moment] using
      (integral_finsetSum Finset.univ
        (fun k _ => integrable_finiteUnitaryEntryWeight k j))
  have hnormalized :
      (∫ U, ∑ k, finiteUnitaryEntryWeight U k j ∂μ) = 1 := by
    calc
      _ = ∫ _U, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with U
        exact sum_finiteUnitaryEntryWeight_column U j
      _ = 1 := by simp [μ]
  have hcard :
      (Fintype.card ι : ℝ) * moment i = 1 := by
    rw [hnormalized] at hsum
    have hsame : (∑ k, moment k) =
        (Fintype.card ι : ℝ) * moment i := by
      simp_rw [hall]
      simp
    linarith [hsum, hsame]
  have hcardne : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change moment i = (Fintype.card ι : ℝ)⁻¹
  rw [inv_eq_one_div, eq_div_iff hcardne]
  nlinarith [hcard]

/-- Every phased mixed fourth moment is Haar-integrable. -/
theorem integrable_finiteUnitaryMixedFourth
    (d : ℕ) (z : ℂ) (j : Fin 2 ⊕ Fin d) :
    Integrable
      (fun U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ =>
        finiteUnitaryMixedFourth z U j)
      (finiteUnitaryHaar (Fin 2 ⊕ Fin d)) := by
  apply integrable_finiteUnitaryHaar_of_continuous
  apply Continuous.pow
  apply Continuous.div_const
  apply Complex.continuous_normSq.comp
  exact (continuous_finiteUnitaryEntry (Sum.inl 0) j).add
    (continuous_const.mul
      (continuous_finiteUnitaryEntry (Sum.inl 1) j))

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

/-- The four unit phases resolve the mixed fourth moment into the two pure
fourth powers and their cross term. -/
theorem finiteUnitaryMixedFourth_four_phase_sum
    (d : ℕ) (U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ)
    (j : Fin 2 ⊕ Fin d) :
    finiteUnitaryMixedFourth 1 U j +
        finiteUnitaryMixedFourth (-1) U j +
        finiteUnitaryMixedFourth Complex.I U j +
        finiteUnitaryMixedFourth (-Complex.I) U j =
      (finiteUnitaryEntryWeight U (Sum.inl 0) j) ^ 2 +
        (finiteUnitaryEntryWeight U (Sum.inl 1) j) ^ 2 +
        4 * finiteUnitaryEntryWeight U (Sum.inl 0) j *
          finiteUnitaryEntryWeight U (Sum.inl 1) j := by
  have h := complex_normSq_four_phase_sum
    (U (Sum.inl 0) j) (U (Sum.inl 1) j)
  simp only [finiteUnitaryMixedFourth, finiteUnitaryEntryWeight]
  simp only [one_mul, neg_mul, sub_eq_add_neg] at h ⊢
  norm_num [div_pow] at *
  linarith

/-- Unitary invariance forces the pure fourth moment of an entry to be twice
the mixed moment of two distinct entries in the same column. -/
theorem finiteUnitaryHaarFourthMoment_eq_two_mul_cross
    (d : ℕ) (j : Fin 2 ⊕ Fin d) :
    finiteUnitaryHaarFourthMoment d j =
      2 * finiteUnitaryHaarCrossMoment d j := by
  let μ := finiteUnitaryHaar (Fin 2 ⊕ Fin d)
  let w₀ := fun U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ =>
    finiteUnitaryEntryWeight U (Sum.inl 0) j
  let w₁ := fun U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ =>
    finiteUnitaryEntryWeight U (Sum.inl 1) j
  let m := fun z U =>
    finiteUnitaryMixedFourth z U j
  have hm (z : ℂ) : Integrable (m z) μ := by
    exact integrable_finiteUnitaryMixedFourth d z j
  have hw₀ : Integrable (fun U => (w₀ U) ^ 2) μ := by
    exact integrable_finiteUnitaryEntryWeight_sq (Sum.inl 0) j
  have hw₁ : Integrable (fun U => (w₁ U) ^ 2) μ := by
    exact integrable_finiteUnitaryEntryWeight_sq (Sum.inl 1) j
  have hcross : Integrable (fun U => w₀ U * w₁ U) μ := by
    exact integrable_finiteUnitaryEntryWeight_mul
      (Sum.inl 0) (Sum.inl 1) j
  have hpoint :
      (∫ U, m 1 U + m (-1) U + m Complex.I U +
          m (-Complex.I) U ∂μ) =
        ∫ U, (w₀ U) ^ 2 + (w₁ U) ^ 2 +
          4 * w₀ U * w₁ U ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with U
    exact finiteUnitaryMixedFourth_four_phase_sum d U j
  have hleft :
      (∫ U, m 1 U + m (-1) U + m Complex.I U +
          m (-Complex.I) U ∂μ) =
        ((∫ U, m 1 U ∂μ) + ∫ U, m (-1) U ∂μ) +
          (∫ U, m Complex.I U ∂μ) +
            ∫ U, m (-Complex.I) U ∂μ := by
    calc
      _ = (∫ U, m 1 U + m (-1) U + m Complex.I U ∂μ) +
          ∫ U, m (-Complex.I) U ∂μ := by
        simpa only [Pi.add_apply] using
          integral_add (((hm 1).add (hm (-1))).add (hm Complex.I))
            (hm (-Complex.I))
      _ = ((∫ U, m 1 U + m (-1) U ∂μ) +
          ∫ U, m Complex.I U ∂μ) +
            ∫ U, m (-Complex.I) U ∂μ := by
        rw [show (∫ U, m 1 U + m (-1) U + m Complex.I U ∂μ) =
            (∫ U, m 1 U + m (-1) U ∂μ) +
              ∫ U, m Complex.I U ∂μ by
          simpa only [Pi.add_apply] using
            integral_add ((hm 1).add (hm (-1))) (hm Complex.I)]
      _ = _ := by
        rw [show (∫ U, m 1 U + m (-1) U ∂μ) =
            (∫ U, m 1 U ∂μ) + ∫ U, m (-1) U ∂μ by
          simpa only [Pi.add_apply] using
            integral_add (hm 1) (hm (-1))]
  have hscaled :
      Integrable (fun U => 4 * w₀ U * w₁ U) μ := by
    convert hcross.const_mul 4 using 1
    funext U
    ring
  have hright :
      (∫ U, (w₀ U) ^ 2 + (w₁ U) ^ 2 +
          4 * w₀ U * w₁ U ∂μ) =
        ((∫ U, (w₀ U) ^ 2 ∂μ) +
          ∫ U, (w₁ U) ^ 2 ∂μ) +
            ∫ U, 4 * w₀ U * w₁ U ∂μ := by
    calc
      _ = (∫ U, (w₀ U) ^ 2 + (w₁ U) ^ 2 ∂μ) +
          ∫ U, 4 * w₀ U * w₁ U ∂μ := by
        simpa only [Pi.add_apply] using
          integral_add (hw₀.add hw₁) hscaled
      _ = _ := by
        rw [show (∫ U, (w₀ U) ^ 2 + (w₁ U) ^ 2 ∂μ) =
            (∫ U, (w₀ U) ^ 2 ∂μ) +
              ∫ U, (w₁ U) ^ 2 ∂μ by
          simpa only [Pi.add_apply] using integral_add hw₀ hw₁]
  rw [hleft, hright] at hpoint
  have hm1 :
      (∫ U, m 1 U ∂μ) =
        finiteUnitaryHaarFourthMoment d j := by
    exact integral_finiteUnitaryMixedFourth_eq d 1
      (by norm_num [Complex.normSq_apply]) j
  have hmneg1 :
      (∫ U, m (-1) U ∂μ) =
        finiteUnitaryHaarFourthMoment d j := by
    exact integral_finiteUnitaryMixedFourth_eq d (-1)
      (by norm_num [Complex.normSq_apply]) j
  have hmI :
      (∫ U, m Complex.I U ∂μ) =
        finiteUnitaryHaarFourthMoment d j := by
    exact integral_finiteUnitaryMixedFourth_eq d Complex.I
      (by norm_num [Complex.normSq_apply]) j
  have hmnegI :
      (∫ U, m (-Complex.I) U ∂μ) =
        finiteUnitaryHaarFourthMoment d j := by
    exact integral_finiteUnitaryMixedFourth_eq d (-Complex.I)
      (by norm_num [Complex.normSq_apply]) j
  have hrow :
      (∫ U, (w₁ U) ^ 2 ∂μ) =
        finiteUnitaryHaarFourthMoment d j := by
    have h := integral_finiteUnitaryEntryWeight_sq_equiv
      (e := Equiv.swap
        (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
      (i := Sum.inl (0 : Fin 2)) (j := j)
    simpa [μ, w₁, finiteUnitaryHaarFourthMoment] using h
  have hscale :
      (∫ U, 4 * w₀ U * w₁ U ∂μ) =
        4 * finiteUnitaryHaarCrossMoment d j := by
    calc
      (∫ U, 4 * w₀ U * w₁ U ∂μ) =
          ∫ U, 4 * (w₀ U * w₁ U) ∂μ := by
            congr 1
            funext U
            ring
      _ = 4 * ∫ U, w₀ U * w₁ U ∂μ := by
        rw [integral_const_mul]
      _ = 4 * finiteUnitaryHaarCrossMoment d j := by
        rfl
  have hw₀value :
      (∫ U, (w₀ U) ^ 2 ∂μ) =
        finiteUnitaryHaarFourthMoment d j := by
    rfl
  rw [hm1, hmneg1, hmI, hmnegI, hw₀value, hrow, hscale] at hpoint
  linarith

/-- Column normalization supplies the second independent relation between the
pure and mixed fourth moments. -/
theorem finiteUnitaryHaarFourthMoment_add_cross_eq_first
    (d : ℕ) (j : Fin 2 ⊕ Fin d) :
    finiteUnitaryHaarFourthMoment d j +
        (d + 1 : ℝ) * finiteUnitaryHaarCrossMoment d j =
      (d + 2 : ℝ)⁻¹ := by
  let ι := Fin 2 ⊕ Fin d
  let μ := finiteUnitaryHaar ι
  let a : ι := Sum.inl 0
  let b : ι := Sum.inl 1
  let w := fun (k : ι)
      (U : Matrix.unitaryGroup ι ℂ) =>
    finiteUnitaryEntryWeight U k j
  let cross := fun k : ι =>
    ∫ U, w a U * w k U ∂μ
  have hsplit :
      (∫ U, ∑ k, w a U * w k U ∂μ) =
        ∑ k, cross k := by
    simpa [cross] using
      (integral_finsetSum Finset.univ
        (fun k _ =>
          integrable_finiteUnitaryEntryWeight_mul a k j))
  have hpoint :
      (∫ U, ∑ k, w a U * w k U ∂μ) =
        ∫ U, w a U ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with U
    calc
      (∑ k, w a U * w k U) =
          w a U * ∑ k, w k U := by
            rw [Finset.mul_sum]
      _ = w a U := by
        rw [sum_finiteUnitaryEntryWeight_column U j, mul_one]
  have hfirst :
      (∫ U, w a U ∂μ) = (d + 2 : ℝ)⁻¹ := by
    simpa [ι, μ, a, w, Fintype.card_sum, add_comm] using
      integral_finiteUnitaryEntryWeight_eq_card_inv a j
  have hdiag :
      cross a = finiteUnitaryHaarFourthMoment d j := by
    dsimp [cross, w, a, μ, ι]
    simp [finiteUnitaryHaarFourthMoment,
      pow_two]
  have hcross (k : ι) (hk : k ≠ a) :
      cross k = finiteUnitaryHaarCrossMoment d j := by
    let e : ι ≃ ι := Equiv.swap b k
    have hab : a ≠ b := by
      intro h
      injection h with h'
      omega
    have hak : a ≠ k := hk.symm
    have hfix : e a = a := by
      exact Equiv.swap_apply_of_ne_of_ne hab hak
    have hmove : e b = k := by
      exact Equiv.swap_apply_left b k
    have h := integral_finiteUnitaryEntryWeight_mul_equiv
      e a b j
    simpa [ι, μ, a, b, w, cross, hfix, hmove,
      finiteUnitaryHaarCrossMoment] using h
  have herase :
      (∑ k ∈ (Finset.univ.erase a), cross k) =
        ((Finset.univ.erase a).card : ℝ) *
          finiteUnitaryHaarCrossMoment d j := by
    calc
      _ = ∑ _k ∈ (Finset.univ.erase a),
          finiteUnitaryHaarCrossMoment d j := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hcross k (Finset.ne_of_mem_erase hk)]
      _ = ((Finset.univ.erase a).card : ℝ) *
          finiteUnitaryHaarCrossMoment d j := by
        simp
  have hsum :
      (∑ k, cross k) =
        finiteUnitaryHaarFourthMoment d j +
          (d + 1 : ℝ) *
            finiteUnitaryHaarCrossMoment d j := by
    have heraseAdd := Finset.sum_erase_add Finset.univ cross
      (Finset.mem_univ a)
    have hcard :
        (Finset.univ.erase a).card = d + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ]
      simp [ι, Fintype.card_sum]
      omega
    rw [← heraseAdd, herase, hdiag, hcard]
    push_cast
    ring
  calc
    finiteUnitaryHaarFourthMoment d j +
        (d + 1 : ℝ) * finiteUnitaryHaarCrossMoment d j =
      ∑ k, cross k := hsum.symm
    _ = ∫ U, ∑ k, w a U * w k U ∂μ := hsplit.symm
    _ = ∫ U, w a U ∂μ := hpoint
    _ = (d + 2 : ℝ)⁻¹ := hfirst

/-- Exact mixed fourth moment of two distinct entries in one Haar-unitary
column. -/
theorem finiteUnitaryHaarCrossMoment_eq
    (d : ℕ) (j : Fin 2 ⊕ Fin d) :
    finiteUnitaryHaarCrossMoment d j =
      (((d + 2 : ℕ) : ℝ) * ((d + 3 : ℕ) : ℝ))⁻¹ := by
  have hratio :=
    finiteUnitaryHaarFourthMoment_eq_two_mul_cross d j
  have hnormal :=
    finiteUnitaryHaarFourthMoment_add_cross_eq_first d j
  have hd2 : (((d + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hd3 : (((d + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [inv_eq_one_div] at hnormal ⊢
  field_simp [hd2, hd3] at hnormal ⊢
  norm_num at hnormal ⊢
  nlinarith

/-- Exact fourth moment of one entry in a Haar-unitary column. -/
theorem finiteUnitaryHaarFourthMoment_eq
    (d : ℕ) (j : Fin 2 ⊕ Fin d) :
    finiteUnitaryHaarFourthMoment d j =
      2 * (((d + 2 : ℕ) : ℝ) *
        ((d + 3 : ℕ) : ℝ))⁻¹ := by
  rw [finiteUnitaryHaarFourthMoment_eq_two_mul_cross,
    finiteUnitaryHaarCrossMoment_eq]

/-- Any ordered pair of distinct points can be sent to any other ordered
pair of distinct points by a permutation. -/
theorem exists_equiv_map_ordered_pair
    {α : Type*} [DecidableEq α]
    {a b i k : α} (hab : a ≠ b) (hik : i ≠ k) :
    ∃ e : α ≃ α, e a = i ∧ e b = k := by
  let e₁ : α ≃ α := Equiv.swap a i
  have he₁a : e₁ a = i := Equiv.swap_apply_left a i
  have hb_ne_i : e₁ b ≠ i := by
    rw [← he₁a]
    intro h
    exact hab (e₁.injective h).symm
  let e₂ : α ≃ α := Equiv.swap (e₁ b) k
  have he₂i : e₂ i = i := by
    exact Equiv.swap_apply_of_ne_of_ne hb_ne_i.symm hik
  refine ⟨e₁.trans e₂, ?_, ?_⟩
  · change e₂ (e₁ a) = i
    rw [he₁a, he₂i]
  · change e₂ (e₁ b) = k
    exact Equiv.swap_apply_left (e₁ b) k

/-- Every same-row product has the pure fourth moment; every distinct-row
product has the cross moment. -/
theorem integral_finiteUnitaryEntryWeight_mul_eq_ite
    (d : ℕ) (i k j : Fin 2 ⊕ Fin d) :
    (∫ U, finiteUnitaryEntryWeight U i j *
        finiteUnitaryEntryWeight U k j
        ∂finiteUnitaryHaar (Fin 2 ⊕ Fin d)) =
      if i = k then
        finiteUnitaryHaarFourthMoment d j
      else finiteUnitaryHaarCrossMoment d j := by
  by_cases hik : i = k
  · subst k
    have h := integral_finiteUnitaryEntryWeight_sq_equiv
      (Equiv.swap
        (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin d) i)
      (Sum.inl (0 : Fin 2)) j
    simpa [Equiv.swap_apply_left, finiteUnitaryHaarFourthMoment,
      pow_two] using h
  · have hab :
        (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin d) ≠
          Sum.inl (1 : Fin 2) := by
      intro h
      injection h with h'
      omega
    obtain ⟨e, he₀, he₁⟩ :=
      exists_equiv_map_ordered_pair hab hik
    have h := integral_finiteUnitaryEntryWeight_mul_equiv
      e (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) j
    simpa [hik, he₀, he₁, finiteUnitaryHaarCrossMoment] using h

/-- Haar mean square of a diagonal probe evaluated in one random unitary
column. -/
def finiteUnitaryDiagonalProbeHaarSignal
    (d : ℕ) (s : (Fin 2 ⊕ Fin d) → ℝ)
    (j : Fin 2 ⊕ Fin d) : ℝ :=
  ∫ U, (∑ i, s i * finiteUnitaryEntryWeight U i j) ^ 2
    ∂finiteUnitaryHaar (Fin 2 ⊕ Fin d)

/-- Exact moment expansion for a diagonal probe. -/
theorem finiteUnitaryDiagonalProbeHaarSignal_eq_sum
    (d : ℕ) (s : (Fin 2 ⊕ Fin d) → ℝ)
    (j : Fin 2 ⊕ Fin d) :
    finiteUnitaryDiagonalProbeHaarSignal d s j =
      ∑ i, ∑ k, s i * s k *
        (if i = k then finiteUnitaryHaarFourthMoment d j
          else finiteUnitaryHaarCrossMoment d j) := by
  let ι := Fin 2 ⊕ Fin d
  let μ := finiteUnitaryHaar ι
  let term := fun (i k : ι)
      (U : Matrix.unitaryGroup ι ℂ) =>
    (s i * s k) *
      (finiteUnitaryEntryWeight U i j *
        finiteUnitaryEntryWeight U k j)
  have hterm (i k : ι) : Integrable (term i k) μ := by
    exact (integrable_finiteUnitaryEntryWeight_mul i k j).const_mul
      (s i * s k)
  have hexpand (U : Matrix.unitaryGroup ι ℂ) :
      (∑ i, s i * finiteUnitaryEntryWeight U i j) ^ 2 =
        ∑ i, ∑ k, term i k U := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro k _hk
    simp [term]
    ring
  rw [finiteUnitaryDiagonalProbeHaarSignal]
  calc
    (∫ U, (∑ i, s i * finiteUnitaryEntryWeight U i j) ^ 2
        ∂finiteUnitaryHaar (Fin 2 ⊕ Fin d)) =
      ∫ U, ∑ i, ∑ k, term i k U ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with U
        exact hexpand U
    _ = ∑ i, ∫ U, ∑ k, term i k U ∂μ := by
      exact integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum Finset.univ
          (fun k _ => hterm i k))
    _ = ∑ i, ∑ k, ∫ U, term i k U ∂μ := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact integral_finsetSum Finset.univ (fun k _ => hterm i k)
    _ = ∑ i, ∑ k, s i * s k *
        (if i = k then finiteUnitaryHaarFourthMoment d j
          else finiteUnitaryHaarCrossMoment d j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro k _hk
      rw [show (∫ U, term i k U ∂μ) =
          (s i * s k) *
            ∫ U, finiteUnitaryEntryWeight U i j *
              finiteUnitaryEntryWeight U k j ∂μ by
        simp only [term, integral_const_mul]]
      rw [integral_finiteUnitaryEntryWeight_mul_eq_ite]

/-- A balanced unit-modulus sign vector collapses a two-level exchangeable
moment tensor to `cardinality × (diagonal − off-diagonal)`. -/
theorem balanced_exchangeable_second_moment_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (A B : ℝ)
    (hsum : ∑ i, s i = 0)
    (hsq : ∀ i, (s i) ^ 2 = 1) :
    (∑ i, ∑ k, s i * s k * (if i = k then A else B)) =
      (Fintype.card ι : ℝ) * (A - B) := by
  let diag := fun i k : ι =>
    if i = k then s i * s k else 0
  have hterm (i k : ι) :
      s i * s k * (if i = k then A else B) =
        B * s i * s k + (A - B) * diag i k := by
    by_cases hik : i = k <;> simp [diag, hik] <;> ring
  have hsplit :
      (∑ i, ∑ k,
          (B * s i * s k + (A - B) * diag i k)) =
        (∑ i, ∑ k, B * s i * s k) +
          ∑ i, ∑ k, (A - B) * diag i k := by
    calc
      _ = ∑ i, ((∑ k, B * s i * s k) +
          ∑ k, (A - B) * diag i k) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact Finset.sum_add_distrib
      _ = _ := Finset.sum_add_distrib
  have htotal :
      (∑ i, ∑ k, B * s i * s k) =
        B * (∑ i, s i) ^ 2 := by
    calc
      _ = B * ∑ i, ∑ k, s i * s k := by
        symm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = B * (∑ i, s i) ^ 2 := by
        rw [pow_two, Finset.sum_mul_sum]
  have hdiag :
      (∑ i, ∑ k, diag i k) = ∑ i, (s i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_eq_single i]
    · simp [diag, pow_two]
    · intro k _hk hki
      simp [diag, hki.symm]
    · simp
  have hscaled :
      (∑ i, ∑ k, (A - B) * diag i k) =
        (A - B) * ∑ i, ∑ k, diag i k := by
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
  calc
    (∑ i, ∑ k, s i * s k *
        (if i = k then A else B)) =
      ∑ i, ∑ k,
        (B * s i * s k + (A - B) * diag i k) := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro k _hk
          exact hterm i k
    _ = (∑ i, ∑ k, B * s i * s k) +
        ∑ i, ∑ k, (A - B) * diag i k := hsplit
    _ = B * (∑ i, s i) ^ 2 +
        (A - B) * ∑ i, ∑ k, diag i k := by
          rw [htotal, hscaled]
    _ = (Fintype.card ι : ℝ) * (A - B) := by
      rw [hsum, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
        zero_add, hdiag]
      simp_rw [hsq]
      simp
      ring

/-- A balanced operator-norm-one diagonal probe has exact Haar mean-square
signal `1 / (D + 1)`, where `D` is Hilbert-space dimension. -/
theorem finiteUnitaryDiagonalProbeHaarSignal_eq_dimension_succ_inv
    (d : ℕ) (s : (Fin 2 ⊕ Fin d) → ℝ)
    (j : Fin 2 ⊕ Fin d)
    (hsum : ∑ i, s i = 0)
    (hsq : ∀ i, (s i) ^ 2 = 1) :
    finiteUnitaryDiagonalProbeHaarSignal d s j =
      (d + 3 : ℝ)⁻¹ := by
  rw [finiteUnitaryDiagonalProbeHaarSignal_eq_sum,
    balanced_exchangeable_second_moment_sum s
      (finiteUnitaryHaarFourthMoment d j)
      (finiteUnitaryHaarCrossMoment d j) hsum hsq,
    finiteUnitaryHaarFourthMoment_eq_two_mul_cross,
    finiteUnitaryHaarCrossMoment_eq]
  norm_num [Fintype.card_sum]
  have hd2 : (0 : ℝ) < d + 2 := by positivity
  have hd3 : (0 : ℝ) < d + 3 := by positivity
  field_simp
  ring

/-- Explicit balanced operator-norm-one diagonal probe in every even
dimension `2(n+1)`. -/
def finiteUnitaryBalancedDiagonalSign
    (n : ℕ) : (Fin 2 ⊕ Fin (n + n)) → ℝ
  | Sum.inl i => if i = 0 then 1 else -1
  | Sum.inr i =>
      Sum.elim (fun _ : Fin n => 1) (fun _ : Fin n => -1)
        (finSumFinEquiv.symm i)

/-- Every entry of the explicit balanced probe is a sign. -/
theorem finiteUnitaryBalancedDiagonalSign_sq
    (n : ℕ) (i : Fin 2 ⊕ Fin (n + n)) :
    (finiteUnitaryBalancedDiagonalSign n i) ^ 2 = 1 := by
  rcases i with i | i
  · fin_cases i <;>
      norm_num [finiteUnitaryBalancedDiagonalSign]
  · cases h : finSumFinEquiv.symm i with
    | inl k =>
        simp [finiteUnitaryBalancedDiagonalSign, h]
    | inr k =>
        simp [finiteUnitaryBalancedDiagonalSign, h]

/-- The explicit even-dimensional probe is traceless. -/
theorem sum_finiteUnitaryBalancedDiagonalSign_eq_zero
    (n : ℕ) :
    ∑ i, finiteUnitaryBalancedDiagonalSign n i = 0 := by
  rw [Fintype.sum_sum_type]
  have htail :
      (∑ i : Fin (n + n),
        finiteUnitaryBalancedDiagonalSign n (Sum.inr i)) = 0 := by
    have htransport := Fintype.sum_equiv finSumFinEquiv
      (fun x : Fin n ⊕ Fin n =>
        Sum.elim (fun _ : Fin n => (1 : ℝ))
          (fun _ : Fin n => -1) x)
      (fun i : Fin (n + n) =>
        finiteUnitaryBalancedDiagonalSign n (Sum.inr i))
      (by
        intro x
        rcases x with x | x
        · change (1 : ℝ) =
            Sum.elim (fun _ : Fin n => (1 : ℝ))
              (fun _ : Fin n => -1)
              (finSumFinEquiv.symm
                (finSumFinEquiv (Sum.inl x)))
          rw [Equiv.symm_apply_apply]
          simp
        · change (-1 : ℝ) =
            Sum.elim (fun _ : Fin n => (1 : ℝ))
              (fun _ : Fin n => -1)
              (finSumFinEquiv.symm
                (finSumFinEquiv (Sum.inr x)))
          rw [Equiv.symm_apply_apply]
          simp)
    rw [Fintype.sum_sum_type] at htransport
    simp at htransport
    linarith
  rw [htail, add_zero]
  norm_num [finiteUnitaryBalancedDiagonalSign,
    Fin.sum_univ_succ]

/-- Diagonal unitary realizing the explicit balanced sign probe. -/
def finiteUnitaryBalancedDiagonalProbe (n : ℕ) :
    Matrix.unitaryGroup (Fin 2 ⊕ Fin (n + n)) ℂ := by
  let s := finiteUnitaryBalancedDiagonalSign n
  refine ⟨Matrix.diagonal (fun i => (s i : ℂ)),
    Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  rw [Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply, if_pos]
    have hs := finiteUnitaryBalancedDiagonalSign_sq n i
    change (s i : ℂ) * starRingEnd ℂ (s i : ℂ) = 1
    norm_num [s, Complex.ext_iff, pow_two] at hs ⊢
    nlinarith
  · simp [hij]

/-- The explicit balanced probe is normalized in operator norm, not
Hilbert--Schmidt norm. -/
theorem norm_finiteUnitaryBalancedDiagonalProbe_eq_one
    (n : ℕ) :
    ‖(finiteUnitaryBalancedDiagonalProbe n :
      Matrix (Fin 2 ⊕ Fin (n + n))
        (Fin 2 ⊕ Fin (n + n)) ℂ)‖ = 1 :=
  CStarRing.norm_coe_unitary
    (finiteUnitaryBalancedDiagonalProbe n)

/-- Exact Haar benchmark for the explicit balanced probe in every even
dimension. -/
theorem finiteUnitaryBalancedDiagonalProbeHaarSignal_eq
    (n : ℕ) (j : Fin 2 ⊕ Fin (n + n)) :
    finiteUnitaryDiagonalProbeHaarSignal
        (n + n) (finiteUnitaryBalancedDiagonalSign n) j =
      (n + n + 3 : ℝ)⁻¹ := by
  simpa [Nat.cast_add] using
    finiteUnitaryDiagonalProbeHaarSignal_eq_dimension_succ_inv
    (n + n) (finiteUnitaryBalancedDiagonalSign n) j
    (sum_finiteUnitaryBalancedDiagonalSign_eq_zero n)
    (finiteUnitaryBalancedDiagonalSign_sq n)

end

end GaloisForLFunctions.HTGeometry
