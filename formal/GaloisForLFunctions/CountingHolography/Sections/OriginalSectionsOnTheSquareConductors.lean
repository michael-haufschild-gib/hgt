import GaloisForLFunctions.CountingHolography.Sections.OrdinaryPrimeSavingsOnSignedDivisors
import GaloisForLFunctions.CountingHolography.Sections.ANegativePrimeWindowAtEveryMultiplicity

/-!
# Original-radius sections on successive square conductors

The negative ordinary-prime window pays both the remaining prime powers and
the regularized jets on the original mesh for every sufficiently large
conductor and every multiplicity in the square-root range.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology

/-- On all sufficiently late successive square conductors the rational generator
has at least n²/48 logarithmic room at the original radius throughout the
square-root multiplicity range. The original lattice contains exponentially many sections. -/
theorem original_sections_on_successor_squares : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
    ∀ {m : ℕ}, 0 < m → K*(m : ℝ)^2 ≤ n →
      let a := m • successorSquareTriple n
      Real.log (generator a : ℝ) + (n : ℝ)^2/48 ≤ radius a ∧
        (1 : ℤ) ∈ smallSections (generator a : ℝ) (radius a) ∧
        2*⌊Real.exp ((n:ℝ)^2/48)⌋₊+1 ≤ (smallSections (generator a : ℝ) (radius a)).card := by
  obtain ⟨K,hK,hwin⟩ := small_multiplicity_exponential_decay
  obtain ⟨C,hC,h⟩ := pole_balanced_ordinary_section_bound
  refine ⟨max K 1,hK.trans_le (le_max_left _ _),?_⟩
  filter_upwards [hwin,eventually_ge_atTop ⌈768*C⌉₊,eventually_ge_atTop 1] with n hn hnC hn1
  intro m hm hmn
  let a := m • successorSquareTriple n
  have hs : positivePoleDegree a = 0 := by
    change (∑ i : Fin ((2*n+1)^2+1), Real.sqrt ((i : ℝ)+1)*
      (((m • successorSquareTriple n) i : ℤ) : ℝ)) = 0
    simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]
    simp_rw [mul_left_comm _ (m : ℝ)]
    rw [← mul_sum,show (∑ i : Fin ((2*n+1)^2+1), Real.sqrt ((i : ℝ)+1)*(successorSquareTriple n i : ℝ)) =
      0 from positivePoleDegree_successorSquareTriple hn1,mul_zero]
  have hv : (resolution (successorSquareTriple n) : ℝ) ≤ 4 := by
    rw [← coefficientVariation_eq_resolution]
    exact successorSquareTriple_mass n
  have hr : (resolution a : ℝ)^2 ≤ 16*(m : ℝ)^2 := by
    have hr' : (resolution a : ℝ) ≤ (m : ℝ)*4 := by
      rw [show a = m • successorSquareTriple n from rfl,resolution_smul,Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _)
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hr' 2).trans_eq (by ring)
  have hneg := hn hm ((mul_le_mul_of_nonneg_right (le_max_left K 1) (sq_nonneg (m : ℝ))).trans hmn)
  have hm' : (m : ℝ)^2 ≤ n := by simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right (le_max_right K 1) (sq_nonneg (m : ℝ))).trans hmn
  have hC' : 768*C ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnC)
  have hfit : Real.log (generator a : ℝ)+(n : ℝ)^2/48 ≤ radius a := by
    linarith only [h _ a hs,hneg,mul_le_mul_of_nonneg_left hr hC,
      mul_le_mul_of_nonneg_left hm' hC,mul_le_mul_of_nonneg_right hC' (Nat.cast_nonneg (α := ℝ) n)]
  have hpos : 0 < (generator a : ℝ) := by exact_mod_cast contactGenerator_pos _ _ _
  refine ⟨hfit,(mem_smallSections hpos 1).mpr ?_,?_⟩
  · rw [Int.cast_one,mul_one,abs_of_pos hpos]
    exact (Real.log_le_iff_le_exp hpos).mp (by linarith only [hfit,sq_nonneg (n : ℝ)])
  · have hratio := Real.exp_le_exp.mpr (show (n:ℝ)^2/48 ≤ radius a-Real.log (generator a : ℝ) by
        linarith only [hfit])
    rw [Real.exp_sub,Real.exp_log hpos] at hratio
    rw [card_smallSections]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.floor_mono hratio)) 1

#print axioms original_sections_on_successor_squares

end GaloisForLFunctions.CountingHolography.Sections
