import GaloisForLFunctions.ArithmeticIndexDescent.TranslatedDetailsAreUniformlySmallInGammaEnergy
import GaloisForLFunctions.HTGeometry.FiniteApproxTotallyBounded

/-!
# Compactness of actual details under the original Gamma bound

The reciprocal-width charge bounds the whole detail norm and makes its high
tail vanish uniformly. Every low head belongs to a fixed finite-dimensional
span of the original Haar atoms. Thus the details of all unit-Gamma complete
profiles have compact closure in the actual half-line L² space, even while
their coarse coefficients and their horizons vary freely.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- The actual detail vector has exactly the balanced coefficient square mass. -/
theorem norm_haarSection_sq (d : ℕ → ℝ) (X : ℕ) :
    ‖haarSection d X‖ ^ 2 = ∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2 := by
  have hn : (inner ℂ (haarSection d X) (haarSection d X)).re = ‖haarSection d X‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  exact hn.symm.trans (re_inner_haarSection_self d X)

/-- The original Gamma profile pays the square mass of every actual high-detail projection. -/
theorem cellGammaWeight_mul_haar_tail_mass_le_gamma (q d : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (X : ℕ) :
    cellGammaWeight A *
        (∑ a ∈ Finset.Icc 1 X, haarMass a * (if A ≤ a then d a else 0) ^ 2) ≤
      levyEnergy (completePairProfile q d X) := by
  have hd : (∑ a ∈ Finset.Icc 1 X, cellGammaWeight a * haarMass a * d a ^ 2) ≤
      levyEnergy (completePairProfile q d X) := by
    apply le_trans ?_ (sum_cellGammaWeight_variance_le_gamma
      (completePairProfile_bv q d X) (completePairProfile_compact q d X) X)
    apply Finset.sum_le_sum
    intro a ha
    rw [intervalVariance_completePairProfile q d (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2]
    exact le_of_eq (mul_assoc _ _ _)
  apply le_trans ?_ hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hmass := (haarMass_pos (Finset.mem_Icc.mp ha).1).le
  by_cases hAa : A ≤ a
  · rw [if_pos hAa, mul_assoc]
    exact mul_le_mul_of_nonneg_right (cellGammaWeight_mono hA hAa)
      (mul_nonneg hmass (sq_nonneg _))
  · rw [if_neg hAa, zero_pow (by norm_num : 2 ≠ 0), mul_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (cellGammaWeight_pos (Finset.mem_Icc.mp ha).1).le hmass) (sq_nonneg _)

/-- Removing the actual finite detail head leaves the high-detail vector itself. -/
theorem haarSection_sub_head (d : ℕ → ℝ) (A X : ℕ) :
    haarSection d X - haarSection (fun a => if a < A then d a else 0) X =
      haarSection (fun a => if A ≤ a then d a else 0) X := by
  unfold haarSection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases h : a < A
  · simp only [if_pos h, if_neg (by omega : ¬A ≤ a), sub_self, Complex.ofReal_zero, zero_smul]
  · simp only [if_neg h, if_pos (by omega : A ≤ a), Complex.ofReal_zero, zero_smul, sub_zero]

/-- Exact Gamma payment of the norm error of a finite detail head. -/
theorem cellGammaWeight_mul_norm_haar_head_error_sq_le_gamma (q d : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (X : ℕ) :
    cellGammaWeight A *
      ‖haarSection d X - haarSection (fun a => if a < A then d a else 0) X‖ ^ 2 ≤
        levyEnergy (completePairProfile q d X) := by
  rw [haarSection_sub_head, norm_haarSection_sq]
  exact cellGammaWeight_mul_haar_tail_mass_le_gamma q d hA X

private theorem haarSection_head_one (d : ℕ → ℝ) (X : ℕ) :
    haarSection (fun a => if a < 1 then d a else 0) X = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  simp only [if_neg (by have := (Finset.mem_Icc.mp ha).1; omega : ¬a < 1), Complex.ofReal_zero, zero_smul]

/-- The first pair already supplies a uniform bound for the entire detail vector. -/
theorem cellGammaWeight_one_mul_norm_haarSection_sq_le_gamma (q d : ℕ → ℝ) (X : ℕ) :
    cellGammaWeight 1 * ‖haarSection d X‖ ^ 2 ≤ levyEnergy (completePairProfile q d X) := by
  simpa only [haarSection_head_one, sub_zero] using
    cellGammaWeight_mul_norm_haar_head_error_sq_le_gamma q d (le_refl 1) X

/-- Actual detail vectors of all complete profiles with original Gamma energy at most one. -/
def gammaUnitDetails : Set (Lp ℂ 2 halfLineMeasure) :=
  {f | ∃ (q d : ℕ → ℝ) (X : ℕ), f = haarSection d X ∧ levyEnergy (completePairProfile q d X) ≤ 1}

private theorem haarSection_head_mem_span (d : ℕ → ℝ) (A X : ℕ) :
    haarSection (fun a => if a < A then d a else 0) X ∈
      Submodule.span ℝ (haarAtom '' (Finset.range A : Set ℕ)) := by
  apply Submodule.sum_mem
  intro a _ha
  by_cases h : a < A
  · simp only [if_pos h, Complex.coe_smul]
    have hm : haarAtom a ∈ Submodule.span ℝ (haarAtom '' (Finset.range A : Set ℕ)) :=
      Submodule.subset_span ⟨a, Finset.mem_range.mpr h, rfl⟩
    exact Submodule.smul_mem _ (d a) hm
  · simp only [if_neg h, Complex.ofReal_zero, zero_smul]
    exact Submodule.zero_mem _

/-- Original Gamma control makes the actual detail family totally bounded in half-line L². -/
theorem totallyBounded_gammaUnitDetails : TotallyBounded gammaUnitDetails := by
  apply totallyBounded_of_finiteDimensional_approx (M := Real.sqrt (1 / cellGammaWeight 1))
  · rintro f ⟨q, d, X, rfl, hE⟩
    have h := (cellGammaWeight_one_mul_norm_haarSection_sq_le_gamma q d X).trans hE
    have hs : ‖haarSection d X‖ ^ 2 ≤ 1 / cellGammaWeight 1 := by
      apply (le_div_iff₀ (cellGammaWeight_pos (le_refl 1))).mpr
      simpa only [mul_comm] using h
    exact (Real.le_sqrt (norm_nonneg _) (div_nonneg zero_le_one (cellGammaWeight_pos (le_refl 1)).le)).mpr hs
  · intro ε hε
    obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (1 / ε ^ 2))
    have hA1 : 1 ≤ A := by
      have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
      exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
    have hlog : 1 / ε ^ 2 < Real.log (A : ℝ) := by
      have h := Real.log_lt_log (Real.exp_pos _) hA
      rwa [Real.log_exp] at h
    have hcap : 1 ≤ cellGammaWeight A * ε ^ 2 := by
      exact (div_le_iff₀ (sq_pos_of_pos hε)).mp
        (hlog.le.trans (log_le_cellGammaWeight hA1))
    refine ⟨Submodule.span ℝ (haarAtom '' (Finset.range A : Set ℕ)),
      FiniteDimensional.span_of_finite ℝ ((Finset.finite_toSet _).image haarAtom), ?_⟩
    rintro f ⟨q, d, X, rfl, hE⟩
    refine ⟨haarSection (fun a => if a < A then d a else 0) X,
      haarSection_head_mem_span d A X, ?_⟩
    have h := (cellGammaWeight_mul_norm_haar_head_error_sq_le_gamma q d hA1 X).trans (hE.trans hcap)
    have hs := (mul_le_mul_left (cellGammaWeight_pos hA1)).mp h
    nlinarith only [hs, norm_nonneg (haarSection d X - haarSection (fun a => if a < A then d a else 0) X), hε]

/-- A genuine compact set in the original L² space contains every unit-Gamma complete-profile detail. -/
theorem isCompact_closure_gammaUnitDetails : IsCompact (closure gammaUnitDetails) :=
  totallyBounded_gammaUnitDetails.closure.isCompact_of_isClosed isClosed_closure

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.cellGammaWeight_mul_haar_tail_mass_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.cellGammaWeight_mul_norm_haar_head_error_sq_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.cellGammaWeight_one_mul_norm_haarSection_sq_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.totallyBounded_gammaUnitDetails
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.isCompact_closure_gammaUnitDetails
