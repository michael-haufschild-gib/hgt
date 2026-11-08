import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedGcdForm
import GaloisForLFunctions.ArithmeticElectrostatics.TheWeilPrimeFormOnAtomsIsLogarithmic
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAdjunctionEnergySeparatesValuations
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheSpacingRegulatorRemovesTheAnomaly

/-!
# Weighted bounds for the torsion limit

The prime kernel is bounded by the normalized gcd kernel times `log(mn)`.
Every positive conductor power absorbs this logarithm and the tame diagonal.
The resulting absolute bound is uniform over all finite positive supports.
-/

noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

private theorem primeKernel_mul_sqrt_le_of_dvd (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hdvd : m ∣ n) (hmn : m ≠ n) :
    weilPrimeKernel m n*Real.sqrt ((m:ℝ)*n) ≤
      (Nat.gcd m n:ℝ)*Real.log ((m:ℝ)*n) := by
  obtain ⟨t, rfl⟩ := hdvd
  have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have htmm : (t:ℝ) ≤ (m:ℝ)*(m*t) := by
    have h1 : (t:ℝ) ≤ (m:ℝ)*t := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1 ht0.le
    have h2 : (m:ℝ)*t ≤ (m:ℝ)*(m*t) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1 (mul_nonneg hm0.le ht0.le)
    exact h1.trans h2
  have hΛ : (Λ t:ℝ) ≤ Real.log t := ArithmeticFunction.vonMangoldt_le_log
  have hlog := Real.log_le_log ht0 htmm
  rw [weilPrimeKernel, if_pos ⟨dvd_mul_right m t, hmn⟩,
    Nat.mul_div_cancel_left t hm, sqrt_mul_mul_eq,
    Nat.gcd_eq_left (dvd_mul_right m t), Nat.cast_mul]
  calc (Λ t/Real.sqrt t)*((m:ℝ)*Real.sqrt t) = (m:ℝ)*Λ t := by
        field_simp [hs.ne']
       _ ≤ (m:ℝ)*Real.log ((m:ℝ)*(m*t)) :=
        mul_le_mul_of_nonneg_left (hΛ.trans hlog) hm0.le

/-- The prime kernel has a logarithmic normalized-gcd envelope. -/
theorem weilPrimeKernel_mul_sqrt_le_gcd_log (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    weilPrimeKernel m n*Real.sqrt ((m:ℝ)*n) ≤
      (Nat.gcd m n:ℝ)*Real.log ((m:ℝ)*n) := by
  by_cases hmn : m∣n ∧ m≠n
  · exact primeKernel_mul_sqrt_le_of_dvd m n hm hn hmn.1 hmn.2
  by_cases hnm : n∣m ∧ n≠m
  · have h := primeKernel_mul_sqrt_le_of_dvd n m hn hm hnm.1 hnm.2
    simpa only [ArithmeticElectrostatics.weilPrimeKernel_comm n m,
      Nat.gcd_comm n m, mul_comm (n:ℝ) (m:ℝ)] using h
  · have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hprod : (1:ℝ) ≤ (m:ℝ)*n := by
      simpa only [one_mul] using mul_le_mul hm1 hn1 zero_le_one (Nat.cast_nonneg m)
    rw [weilPrimeKernel, if_neg hmn, if_neg hnm, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hprod)

/-- Every positive conductor power absorbs the logarithm in the prime kernel. -/
theorem weilPrimeKernel_le_gcd_power (κ : ℝ) (hκ : 0 < κ)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    weilPrimeKernel m n ≤ (1/κ)*(Nat.gcd m n:ℝ)*((m:ℝ)*n)^κ/Real.sqrt ((m:ℝ)*n) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt ((m:ℝ)*n) := Real.sqrt_pos.mpr (mul_pos hm0 hn0)
  apply (le_div_iff₀ hs).mpr
  calc weilPrimeKernel m n*Real.sqrt ((m:ℝ)*n) ≤
        (Nat.gcd m n:ℝ)*Real.log ((m:ℝ)*n) := weilPrimeKernel_mul_sqrt_le_gcd_log m n hm hn
       _ ≤ (Nat.gcd m n:ℝ)*(((m:ℝ)*n)^κ/κ) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div (mul_nonneg hm0.le hn0.le) hκ) (Nat.cast_nonneg _)
       _ = _ := by ring

/-- The actual finite-spacing limit kernel, including torsion adjunction on the diagonal. -/
def spacingLimitKernel (m n : ℕ) : ℝ :=
  -weilPrimeKernel m n + if m=n then tameDifferent n else 0

/-- The absolute limit separates exactly into the prime pairing and tame diagonal. -/
theorem spacingLimitKernel_abs (m n : ℕ) :
    |spacingLimitKernel m n| = weilPrimeKernel m n + if m=n then tameDifferent n else 0 := by
  by_cases hmn : m=n
  · subst n
    simp only [spacingLimitKernel, ArithmeticElectrostatics.weilPrimeKernel_self,
      if_true, neg_zero, zero_add,
      abs_of_nonneg (RenormalizedArithmeticPotentialTheory.tameDifferent_nonneg m)]
  · simp only [spacingLimitKernel, if_neg hmn, add_zero, abs_neg,
      abs_of_nonneg (ArithmeticElectrostatics.weilPrimeKernel_nonneg m n)]


/-- The prime part is absolutely bounded on every positively weighted finite probe space. -/
theorem weilPrimeKernel_weighted_absolute_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (x : ℕ → ℝ), (∀ n ∈ S, 0 < n) →
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*weilPrimeKernel m n|) ≤
        C*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  let κ := δ/4
  let β := δ/2
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hβ : 0 < β := half_pos hδ
  obtain ⟨D, hD, hgcd⟩ := normalized_gcd_form_finite_bound β hβ
  refine ⟨(1/κ)*D, by positivity, ?_⟩
  intro S x hS
  let y : ℕ → ℝ := fun n => |x n| *(n:ℝ)^κ
  have hpoint (m : ℕ) (hm : m∈S) (n : ℕ) (hn : n∈S) :
      |x m*x n*weilPrimeKernel m n| ≤
        (1/κ)*((Nat.gcd m n:ℝ)*(y m/Real.sqrt m*(y n/Real.sqrt n))) := by
    have hm0 : (0:ℝ) < m := by exact_mod_cast hS m hm
    have hn0 : (0:ℝ) < n := by exact_mod_cast hS n hn
    rw [abs_mul, abs_mul, abs_of_nonneg (ArithmeticElectrostatics.weilPrimeKernel_nonneg m n)]
    calc |x m| *|x n| *weilPrimeKernel m n ≤
          |x m| *|x n| *((1/κ)*(Nat.gcd m n:ℝ)*((m:ℝ)*n)^κ/Real.sqrt ((m:ℝ)*n)) :=
          mul_le_mul_of_nonneg_left (weilPrimeKernel_le_gcd_power κ hκ m n (hS m hm) (hS n hn))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
         _ = _ := by
          rw [Real.mul_rpow hm0.le hn0.le, Real.sqrt_mul hm0.le]
          dsimp only [y]
          ring
  have hnorm : (∑ n ∈ S, (n:ℝ)^β*(y n)^2) =
      ∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
    apply sum_congr rfl
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hS n hn
    calc (n:ℝ)^β*(y n)^2 = ((n:ℝ)^β*((n:ℝ)^κ*(n:ℝ)^κ))*(x n)^2 := by
          dsimp only [y]
          rw [mul_pow, sq_abs]
          ring
         _ = (n:ℝ)^(β+(κ+κ))*(x n)^2 := by rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
         _ = (n:ℝ)^δ*(x n)^2 := by
          have hexp : β+(κ+κ)=δ := by dsimp only [β, κ]; ring
          rw [hexp]
  calc (∑ m ∈ S, ∑ n ∈ S, |x m*x n*weilPrimeKernel m n|) ≤
        ∑ m ∈ S, ∑ n ∈ S, (1/κ)*((Nat.gcd m n:ℝ)*(y m/Real.sqrt m*(y n/Real.sqrt n))) :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => hpoint m hm n hn
       _ = (1/κ)*∑ m ∈ S, ∑ n ∈ S, (Nat.gcd m n:ℝ)*(y m/Real.sqrt m*(y n/Real.sqrt n)) := by
        simp only [mul_sum]
       _ ≤ (1/κ)*(D*∑ n ∈ S, (n:ℝ)^β*(y n)^2) :=
        mul_le_mul_of_nonneg_left (hgcd S y hS) (by positivity)
       _ = _ := by rw [hnorm]; ring

/-- The limiting kernel is symmetric. -/
theorem spacingLimitKernel_comm (m n : ℕ) : spacingLimitKernel m n=spacingLimitKernel n m := by
  rw [spacingLimitKernel, spacingLimitKernel, ArithmeticElectrostatics.weilPrimeKernel_comm m n]
  by_cases h : m=n
  · subst n; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- The kernel represents the existing finite spacing limit exactly. -/
theorem spacingLimit_eq_kernel (S : Finset ℕ) (x : ℕ → ℝ) :
    spacingLimit S x = ∑ m ∈ S, ∑ n ∈ S, x m*x n*spacingLimitKernel m n := by
  classical
  have hd : (∑ m ∈ S, ∑ n ∈ S, x m*x n*(if m=n then tameDifferent n else 0)) =
      ∑ m ∈ S, (x m)^2*tameDifferent m := by
    apply sum_congr rfl
    intro m hm
    rw [sum_eq_single m]
    · rw [if_pos rfl, pow_two]
    · intro n _hn hnm
      rw [if_neg hnm.symm, mul_zero]
    · exact fun h => (h hm).elim
  simp only [spacingLimitKernel, mul_add, mul_neg, sum_add_distrib, sum_neg_distrib]
  rw [hd]
  rfl

/-- Every positive conductor weight bounds the full absolute limiting pairing. -/
theorem spacingLimitKernel_weighted_absolute_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (x : ℕ → ℝ), (∀ n ∈ S, 0 < n) →
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*spacingLimitKernel m n|) ≤
        C*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  classical
  obtain ⟨A, hA, hprime⟩ := weilPrimeKernel_weighted_absolute_bound δ hδ
  refine ⟨A+1/δ, by positivity, ?_⟩
  intro S x hS
  have hd : (∑ m ∈ S, ∑ n ∈ S, |x m| *|x n| *(if m=n then tameDifferent n else 0)) =
      ∑ m ∈ S, (x m)^2*tameDifferent m := by
    apply sum_congr rfl
    intro m hm
    rw [sum_eq_single m]
    · rw [if_pos rfl, ← pow_two, sq_abs]
    · intro n _hn hnm
      rw [if_neg hnm.symm, mul_zero]
    · exact fun h => (h hm).elim
  have hsplit : (∑ m ∈ S, ∑ n ∈ S, |x m*x n*spacingLimitKernel m n|) =
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*weilPrimeKernel m n|)+
        ∑ n ∈ S, (x n)^2*tameDifferent n := by
    have hP (m n : ℕ) : |weilPrimeKernel m n|=weilPrimeKernel m n :=
      abs_of_nonneg (ArithmeticElectrostatics.weilPrimeKernel_nonneg m n)
    simp only [abs_mul, spacingLimitKernel_abs, mul_add, sum_add_distrib, hP]
    rw [hd]
  have hdiag : (∑ n ∈ S, (x n)^2*tameDifferent n) ≤
      (1/δ)*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hS n hn
    calc (x n)^2*tameDifferent n ≤ (x n)^2*((n:ℝ)^δ/δ) :=
          mul_le_mul_of_nonneg_left
            ((RenormalizedArithmeticPotentialTheory.tameDifferent_le_log (hS n hn)).trans
              (Real.log_le_rpow_div hn0.le hδ)) (sq_nonneg _)
         _ = _ := by ring
  rw [hsplit]
  calc _ ≤ A*(∑ n ∈ S, (n:ℝ)^δ*(x n)^2)+(1/δ)*(∑ n ∈ S, (n:ℝ)^δ*(x n)^2) :=
        add_le_add (hprime S x hS) hdiag
       _ = _ := by ring

#print axioms weilPrimeKernel_mul_sqrt_le_gcd_log
#print axioms weilPrimeKernel_le_gcd_power
#print axioms weilPrimeKernel_weighted_absolute_bound
#print axioms spacingLimitKernel_comm
#print axioms spacingLimitKernel_abs
#print axioms spacingLimit_eq_kernel
#print axioms spacingLimitKernel_weighted_absolute_bound
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
