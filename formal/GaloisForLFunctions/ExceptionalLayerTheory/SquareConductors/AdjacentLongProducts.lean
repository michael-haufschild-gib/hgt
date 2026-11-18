import GaloisForLFunctions.ExceptionalLayerTheory.AdjacentVaughanOctavesRecoverTheOrdinaryPrimeCount
import GaloisForLFunctions.ExceptionalLayerTheory.RemovingSmallOrdinaryPrimesAtBothWidths

/-!
# The ordinary prime count in the adjacent long-product rows

The difference of the two short cofactors is a single atom on every
input function. It therefore isolates the same divided horizon before
and after the long-product approximation. The unit cofactor gives the
error there without any loss depending on the isolating prime.
-/

noncomputable section
open Finset ArithmeticFunction RHTower.Sieve
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The surviving coprime products, with both cutoffs set at the divided horizon. -/
def longPrimeRow (N : ℕ) : ℝ :=
  let D := ⌊1+Real.log N⌋₊
  remainingPrimeProducts D D N

/-- The contribution of the truncated first-octave coefficients at their
individual divided horizons. -/
def octaveRow (t : ℕ) (f : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 M, firstOctaveCofactor t d*f (M/d)

/-- Cofinal adjacent octaves isolate every signed row simultaneously, even
when its internal cutoffs depend on the divided argument. -/
theorem cofinal_octaves_isolate_rows (B : ℕ) :
    ∃ t > B, (2*t+1).Prime ∧ ∀ (f : ℕ → ℝ) (N : ℕ), 0 < N →
      octaveRow (t+1) f ((2*t+1)*N)-octaveRow t f ((2*t+1)*N) = -f N := by
  obtain ⟨p,hpB,hp,hclass⟩ := Nat.forall_exists_prime_gt_and_modEq (2*B+2)
    (q := 8) (a := 7) (by decide) (by decide)
  change p % 8 = 7 % 8 at hclass
  let t := p/2
  have hpt : 2*t+1=p := by dsimp [t]; omega
  have h4 : 4 ∣ t+1 := by dsimp [t]; omega
  refine ⟨t,by dsimp [t]; omega,hpt.symm ▸ hp,fun f N hN => ?_⟩
  have hm : 2*t+1 ∈ Icc 1 ((2*t+1)*N) :=
    mem_Icc.mpr ⟨by omega,Nat.le_mul_of_pos_right _ hN⟩
  rw [octaveRow,octaveRow,←sum_sub_distrib]
  simp_rw [←sub_mul,adjacent_octave_difference (hpt.symm ▸ hp) h4,ite_mul,zero_mul]
  rw [sum_ite_eq',if_pos hm,Nat.mul_div_cancel_left _ (by omega : 0<2*t+1),neg_one_mul]

private theorem unit_cofactor : typeIIShort 0 = 1 := by
  have h : truncAF (moebius : ArithmeticFunction ℝ) 0 = 0 := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp only [truncAF_apply,if_neg (not_le.mpr hn),ArithmeticFunction.zero_apply]
  simp only [typeIIShort,h,mul_zero,sub_zero]

/-- At every positive integer the long product approximates the ordinary
theta error to square-root precision times six logarithms. -/
theorem theta_longPrimeRow_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |(Chebyshev.theta N-N)-longPrimeRow N| ≤ C*(1+Real.log N)^6*Real.sqrt N := by
  obtain ⟨K,hK,h⟩ := long_first_prime_cofactors
  obtain ⟨P,hP⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨K+|P|,by positivity,fun N hN => ?_⟩
  have hp := h 0 1 N
  rw [cofactorCountError_eq] at hp
  simp only [unit_cofactor,min_eq_right hN,Icc_self,sum_singleton,one_one,one_mul,
    Nat.div_one,abs_one] at hp
  change |(Chebyshev.psi N-N)-longPrimeRow N| ≤ K*(1+Real.log N)^6*Real.sqrt N at hp
  have h₁ : 1 ≤ (1+Real.log (N:ℝ))^6 :=
    one_le_pow₀ (le_add_of_nonneg_right (Real.log_natCast_nonneg N))
  have h₂ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (abs_nonneg P) h₁)
    (Real.sqrt_nonneg (N:ℝ))
  have h₃ := (hP N).trans (mul_le_mul_of_nonneg_right (le_abs_self P) (Real.sqrt_nonneg _))
  rw [abs_le] at hp ⊢
  constructor <;> linarith only [hp.1,hp.2,h₂,h₃,Chebyshev.theta_le_psi (N:ℝ)]

#print axioms cofinal_octaves_isolate_rows
#print axioms theta_longPrimeRow_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
