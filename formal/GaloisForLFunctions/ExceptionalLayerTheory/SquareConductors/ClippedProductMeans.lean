import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.HorizonCancellation
import GaloisForLFunctions.ExceptionalLayerTheory.TransposingTheComplementaryFactorTail

/-!
# Horizon means on clipped coprime product windows

The first prime and its coprime complement may have their own sharp
horizon endpoints. Summing in the horizon before the prime and the
complement bounds the primitive by the square of the product cutoff.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Log-weighted coprime products up to U. Each pair is present on
its own half-open interval of integer horizons. -/
def clippedPrimeProducts (D R F U : ℕ) (lo hi : ℕ → ℕ → ℕ) (k : ℕ) : ℝ :=
  ordinaryFactorTail F U fun p =>
    ∑ v ∈ (Icc 1 (U/p)).filter (p.Coprime ·), innerJump D v *
      (if lo p v ≤ k ∧ k < hi p v then centeredPrimeWeight R (k/(p*v)) else 0)

private theorem sum_clipped {R q : ℕ} (hR : 1 ≤ R) (hq : 0 < q) (a b L H : ℕ) :
    |∑ k ∈ Ico L H, (if a ≤ k ∧ k < b then centeredPrimeWeight R (k/q) else 0)| ≤
      125*(1+mass R)*(128*(128*(R:ℝ)^2+1))*q := by
  have hs : (Ico L H).filter (fun k => a ≤ k ∧ k < b) = Ico (max L a) (min H b) := by
    ext k; simp only [mem_filter,mem_Ico,max_le_iff,lt_min_iff]; tauto
  rw [←sum_filter,hs]
  exact centeredPrimeWeight_horizon_interval hR hq _ _

/-- Discrepancy on every horizon interval, including both clipped ends.
The bound is independent of the number of first primes and applies
with the same constant at the original and dilated horizons. -/
theorem clippedPrimeProducts_interval {R U : ℕ} (hR : 1 ≤ R) (hU : 1 ≤ U)
    (D F : ℕ) (lo hi : ℕ → ℕ → ℕ) (L H : ℕ) :
    |∑ k ∈ Ico L H, clippedPrimeProducts D R F U lo hi k| ≤
      (2*(1+mass (D+1)))*(125*(1+mass R)*(128*(128*(R:ℝ)^2+1)))*
        (U:ℝ)^2*((Real.log 4+4)*(1+Real.log U)) := by
  let A := 2*(1+mass (D+1))
  let B := 125*(1+mass R)*(128*(128*(R:ℝ)^2+1))
  have hA : 0 ≤ A := (abs_nonneg _).trans (innerJump_pointwise_bound D 0)
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let S (p : ℕ) := (Icc 1 (U/p)).filter (p.Coprime ·)
  let w (p v k : ℕ) := if lo p v ≤ k ∧ k < hi p v then centeredPrimeWeight R (k/(p*v)) else 0
  let row (p : ℕ) := ∑ v ∈ S p, innerJump D v*(∑ k ∈ Ico L H, w p v k)
  have swap : (∑ k ∈ Ico L H, clippedPrimeProducts D R F U lo hi k) = ordinaryFactorTail F U row := by
    unfold clippedPrimeProducts ordinaryFactorTail
    rw [sum_comm]
    apply sum_congr rfl; intro p _
    rw [←mul_sum]
    congr 1
    rw [sum_comm]
    exact sum_congr rfl fun v _ => (mul_sum _ _ _).symm
  rw [swap]
  apply ordinaryFactorTail_reciprocal hU (mul_nonneg (mul_nonneg hA hB) (sq_nonneg _))
  intro p hp
  have hp₀ := (mem_filter.mp hp).2.pos
  have hp' : (0:ℝ)<p := by exact_mod_cast hp₀
  have hrow (v : ℕ) (hv : v ∈ S p) :
      |innerJump D v*(∑ k ∈ Ico L H, w p v k)| ≤ A*B*U := by
    obtain ⟨hv₀,hvU⟩ := mem_Icc.mp (mem_filter.mp hv).1
    have hprod : p*v ≤ U := by simpa only [Nat.mul_comm v p] using (Nat.le_div_iff_mul_le hp₀).mp hvU
    have hcell := sum_clipped hR (Nat.mul_pos hp₀ hv₀) (lo p v) (hi p v) L H
    rw [abs_mul]
    exact (mul_le_mul (innerJump_pointwise_bound D v) hcell (abs_nonneg _) hA).trans
      (by change A*(B*((p*v:ℕ):ℝ)) ≤ A*B*U
          rw [←mul_assoc]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hprod) (mul_nonneg hA hB))
  have hcard : (S p).card ≤ U/p := by
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card (filter_subset (p.Coprime ·) (Icc 1 (U/p)))
  have hbound : ((S p).card:ℝ)*p ≤ U := by
    exact_mod_cast (Nat.mul_le_mul_right p hcard).trans (Nat.div_mul_le_self U p)
  change |∑ v ∈ S p, _| ≤ _
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hrow).trans _)
  rw [sum_const,nsmul_eq_mul]
  apply (le_div_iff₀ hp').mpr
  have h := mul_le_mul_of_nonneg_left hbound (mul_nonneg (mul_nonneg hA hB) (Nat.cast_nonneg U))
  linarith only [h]

#print axioms clippedPrimeProducts_interval
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
