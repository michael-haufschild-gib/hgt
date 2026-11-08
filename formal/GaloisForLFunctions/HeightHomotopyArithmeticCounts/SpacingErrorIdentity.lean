import GaloisForLFunctions.HeightHomotopyArithmeticCounts.PrimitiveTorsionDivisorFormula
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheSpacingRegulatorRemovesTheAnomaly

/-!
# Exact normalization of the full spacing error

The actual gcd-twisted energy, scalar diagonal counterterm and known limiting
kernel combine into a normalized double Möbius remainder. Off-diagonal
normalization follows from uniqueness of the known limits; diagonal
normalization uses torsion adjunction and the arithmetic spacing radius.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- Off the diagonal, the normalized orbit intersection is the actual Weil prime kernel. -/
theorem twisted_orbitIntersection_of_ne (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m≠n) :
    gcdTwist m n*orbitIntersection m n/Real.sqrt ((m:ℝ)*n) = weilPrimeKernel m n := by
  have hT := (tendsto_torsionEnergy_of_ne hmn).const_mul
    (gcdTwist m n/Real.sqrt ((m:ℝ)*n))
  have hf : (fun r : ℝ => gcdTwist m n/Real.sqrt ((m:ℝ)*n)*torsionEnergy r m n) =
      fun r => twistedEnergy r m n := by
    funext r
    rw [twistedEnergy]
    ring
  rw [hf] at hT
  have h := tendsto_nhds_unique hT (tendsto_twistedEnergy_of_ne hm hn hmn)
  linear_combination -h

/-- The actual scalar-renormalized spacing entry minus its known limiting entry. -/
def spacingKernelError (ε : ℝ) (m n : ℕ) : ℝ :=
  twistedEnergy (spacingRadius ε m n) m n + weilPrimeKernel m n +
    if m=n then Real.log (2*ε)-tameDifferent n else 0

/-- The full spacing error is precisely the normalized finite divisor remainder. -/
theorem spacingKernelError_eq (ε : ℝ) (hε : 0 < ε)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    spacingKernelError ε m n = gcdTwist m n*
      torsionExponentialDefect (ε*((m:ℝ)⁻¹+(n:ℝ)⁻¹)) m n/Real.sqrt ((m:ℝ)*n) := by
  let t := ε*((m:ℝ)⁻¹+(n:ℝ)⁻¹)
  have hm0 : (0:ℝ)< m := by exact_mod_cast hm
  have hn0 : (0:ℝ)< n := by exact_mod_cast hn
  have ht : 0 < t := mul_pos hε (add_pos (inv_pos.mpr hm0) (inv_pos.mpr hn0))
  have hr : spacingRadius ε m n=Real.exp (-t) := by
    unfold spacingRadius
    congr 1
    dsimp only [t]
    ring
  have hT := torsionEnergy_exponential_decomposition t ht m n hm hn
  rw [← hr] at hT
  change spacingKernelError ε m n =
    gcdTwist m n*torsionExponentialDefect t m n/Real.sqrt ((m:ℝ)*n)
  by_cases hmn : m=n
  · subst n
    have hφ : (0:ℝ)<Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm
    have hdiag (z : ℝ) : gcdTwist m m*z/Real.sqrt ((m:ℝ)*m)=z/(Nat.totient m:ℝ) := by
      rw [gcdTwist_eq, Nat.gcd_self, Real.sqrt_mul_self hm0.le]
      field_simp [hm0.ne', hφ.ne']
    have hI : orbitIntersection m m/(Nat.totient m:ℝ)=Real.log m-tameDifferent m := by
      simpa only [selfIntersection] using selfIntersection_eq hm
    have htval : t=2*ε/(m:ℝ) := by dsimp only [t]; rw [div_eq_mul_inv]; ring
    have hlogt : Real.log t=Real.log (2*ε)-Real.log m := by
      rw [htval, Real.log_div (mul_pos (by norm_num) hε).ne' hm0.ne']
    rw [if_pos rfl] at hT
    have hTD := congrArg (fun z : ℝ => z/(Nat.totient m:ℝ)) hT
    have hcancel : (Nat.totient m:ℝ)*Real.log t/(Nat.totient m:ℝ)=Real.log t := by
      field_simp [hφ.ne']
    rw [add_div, add_div, hcancel, hI, hlogt] at hTD
    rw [spacingKernelError, if_pos rfl,
      show weilPrimeKernel m m=0 by simp [weilPrimeKernel], add_zero, twistedEnergy, hdiag, hdiag]
    linear_combination hTD
  · rw [if_neg hmn, zero_mul, add_zero] at hT
    have hI := twisted_orbitIntersection_of_ne m n hm hn hmn
    rw [spacingKernelError, if_neg hmn, add_zero, twistedEnergy, ← hI]
    linear_combination (gcdTwist m n/Real.sqrt ((m:ℝ)*n))*hT

/-- The finite spacing-form error is the quadratic form of the actual error entries. -/
theorem spacingForm_error_eq (ε : ℝ) (S : Finset ℕ) (x : ℕ → ℝ) :
    spacingForm ε S x + Real.log (2*ε)*∑ n ∈ S, (x n)^2 - spacingLimit S x =
      ∑ m ∈ S, ∑ n ∈ S, x m*x n*spacingKernelError ε m n := by
  classical
  have hd : (∑ m ∈ S, ∑ n ∈ S, x m*x n*
      (if m=n then Real.log (2*ε)-tameDifferent n else 0)) =
      ∑ m ∈ S, (x m)^2*(Real.log (2*ε)-tameDifferent m) := by
    apply sum_congr rfl
    intro m hm
    rw [sum_eq_single m]
    · rw [if_pos rfl, pow_two]
    · intro n _hn hnm
      rw [if_neg hnm.symm, mul_zero]
    · exact fun h => (h hm).elim
  simp only [spacingKernelError, mul_add, sum_add_distrib]
  rw [hd]
  unfold spacingForm spacingLimit primeForm
  simp only [mul_sub, sum_sub_distrib, mul_sum]
  ring

#print axioms twisted_orbitIntersection_of_ne
#print axioms spacingKernelError_eq
#print axioms spacingForm_error_eq
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
