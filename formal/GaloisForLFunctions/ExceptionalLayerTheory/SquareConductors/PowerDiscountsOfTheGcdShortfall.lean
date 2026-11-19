import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CumulativeQuadratureOfTheGcdDeficit
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdDeficitAtTheEighthPowerEndpoints

/-!
# The critical power discount for accumulated gcd shortfall

The power-integral alternative in Fino and Majdoub (arXiv:2611.24340,
Lemma 2.1) applies in cumulative shortfall coordinates. Discounting each
charge by (1+D) to the power p yields a finite total exactly when p>1
or the entire grid already has finite shortfall. At the eighth powers
the second possibility is excluded by the arithmetic half-step law.
-/

noncomputable section
open Finset Filter Set
open scoped Topology
open GaloisForLFunctions.CumulativeQuadrature

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Charge at the next endpoint, discounted at that endpoint. -/
def gcdPowerCharge (r : ℕ) (p : ℝ) (i : ℕ) : ℝ :=
  (powerGridGcdDeficit r (i+1)-powerGridGcdDeficit r i)*(1+powerGridGcdDeficit r (i+1))^(-p)

private theorem mass_nonneg (r i : ℕ) : 0 ≤ powerGridGcdDeficit r i :=
  sum_nonneg fun _ _ => le_max_right _ _

private theorem charge_nonneg (r : ℕ) (p : ℝ) (i : ℕ) : 0 ≤ gcdPowerCharge r p i :=
  mul_nonneg (gcd_deficit_increment_bounds r i).1
    (Real.rpow_nonneg (add_nonneg zero_le_one (mass_nonneg r _)) _)

private theorem supercritical_prefix (r K n : ℕ) {p : ℝ} (hp : 1 < p) :
    ∑ i ∈ range n, gcdPowerCharge r p (K+i) ≤ (1+powerGridGcdDeficit r K)^(1-p)/(p-1) := by
  let x := fun i => 1+powerGridGcdDeficit r (K+i)
  have hx : Monotone x := fun i j hij =>
    add_le_add (le_refl 1) (monotone_gcd_deficit r (Nat.add_le_add_left hij K))
  have hpos (i : ℕ) : 0 < x i := add_pos_of_pos_of_nonneg zero_lt_one (mass_nonneg r _)
  have ha : AntitoneOn (fun v : ℝ => v^(-p)) (Icc (x 0) (x n)) := fun _ hv _ _ hvw =>
    Real.rpow_le_rpow_of_nonpos ((hpos 0).trans_le hv.1) hvw (by linarith only [hp])
  have heq (i : ℕ) : x (i+1)-x i = powerGridGcdDeficit r ((K+i)+1)-powerGridGcdDeficit r (K+i) := by
    dsimp only [x]; rw [Nat.add_assoc]; ring
  have hmesh (i : ℕ) (_ : i < n) : x (i+1)-x i ≤ Real.log 2 := by
    rw [heq]; exact (gcd_deficit_increment_bounds r (K+i)).2
  have h := (defect_bounds n hx ha hmesh).1
  have hf : rightSum x (fun v : ℝ => v^(-p)) n = ∑ i ∈ range n, gcdPowerCharge r p (K+i) := by
    apply sum_congr rfl
    intro i _
    rw [heq,gcdPowerCharge]
    simp only [x,Nat.add_assoc]
  have hzero : (0:ℝ) ∉ uIcc (x 0) (x n) := by
    rw [uIcc_of_le (hx (Nat.zero_le n))]
    exact fun h => (hpos 0).not_ge h.1
  rw [defect,hf,integral_rpow (Or.inr ⟨by linarith only [hp],hzero⟩)] at h
  have hden := sub_pos.mpr hp
  have he : ((x n)^(-p+1)-(x 0)^(-p+1))/(-p+1) =
      ((x 0)^(1-p)-(x n)^(1-p))/(p-1) := by
    rw [show -p+1 = 1-p by ring]
    field_simp [hden.ne',(sub_neg.mpr hp).ne] <;> ring
  rw [he] at h
  have hupper := (sub_nonneg.mp h).trans (div_le_div_of_nonneg_right
    (sub_le_self _ (Real.rpow_nonneg (hpos n).le _)) hden.le)
  simpa only [x,Nat.add_zero] using hupper

/-- The complete supercritical tail is bounded by the remaining power
integral even when some steps vanish. -/
theorem supercritical_gcd_tail (r K : ℕ) {p : ℝ} (hp : 1 < p) :
    Summable (fun i => gcdPowerCharge r p (K+i)) ∧
      (∑' i, gcdPowerCharge r p (K+i)) ≤ (1+powerGridGcdDeficit r K)^(1-p)/(p-1) :=
  ⟨summable_of_sum_range_le (fun i => charge_nonneg r p (K+i)) (fun n => supercritical_prefix r K n hp),
    Real.tsum_le_of_sum_range_le (fun i => charge_nonneg r p (K+i)) (fun n => supercritical_prefix r K n hp)⟩

/-- The critical integrability alternative, including growing weights p<0. -/
theorem gcd_power_discount_summable_iff (r : ℕ) (p : ℝ) :
    Summable (gcdPowerCharge r p) ↔ 1 < p ∨ BddAbove (range (powerGridGcdDeficit r) : Set ℝ) := by
  constructor
  · intro hs
    by_cases hp : 1 < p
    · exact Or.inl hp
    right
    let B := ∑' i, gcdPowerCharge r p i
    have hread (n : ℕ) : gcdDeficitLogSum r n ≤ B := by
      apply le_trans _ (hs.sum_le_tsum (Finset.range n) (fun i _ => charge_nonneg r p i))
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (gcd_deficit_increment_bounds r i).1
      rw [←Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le
        (le_add_of_nonneg_right (mass_nonneg r _)) (by linarith only [le_of_not_gt hp])
    refine ⟨Real.exp (B+Real.log 2),?_⟩
    rintro _ ⟨k,rfl⟩
    have hd := (gcd_log_sum_error r k).2
    have ht := mul_le_mul_of_nonneg_left
      (sub_le_self 1 (inv_nonneg.mpr (add_nonneg zero_le_one (mass_nonneg r k))))
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    have hl : Real.log (1+powerGridGcdDeficit r k) ≤ B+Real.log 2 := by
      linarith only [hd,ht,hread k]
    have he := Real.exp_le_exp.mpr hl
    rw [Real.exp_log (add_pos_of_pos_of_nonneg zero_lt_one (mass_nonneg r k))] at he
    linarith only [he]
  · rintro (hp|⟨B,hB⟩)
    · simpa only [Nat.zero_add] using (supercritical_gcd_tail r 0 hp).1
    let A := (1+B)^|p|
    have hmax (k : ℕ) := hB (mem_range_self k)
    have hB₀ := (mass_nonneg r 0).trans (hmax 0)
    have hA : 0 ≤ A := Real.rpow_nonneg (add_nonneg zero_le_one hB₀) _
    apply summable_of_sum_range_le (charge_nonneg r p) (c := B*A)
    intro n
    have hh (i : ℕ) : (1+powerGridGcdDeficit r (i+1))^(-p) ≤ A :=
      (Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (mass_nonneg r _)) (neg_le_abs p)).trans
        (Real.rpow_le_rpow (add_nonneg zero_le_one (mass_nonneg r _))
          (add_le_add (le_refl 1) (hmax _)) (abs_nonneg p))
    have h := sum_le_sum (s := Finset.range n) fun i _ =>
      mul_le_mul_of_nonneg_left (hh i) (gcd_deficit_increment_bounds r i).1
    rw [←sum_mul,sum_range_sub,show powerGridGcdDeficit r 0 = 0 by simp [powerGridGcdDeficit],sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hmax n) hA)

/-- The eighth-power arithmetic series converges precisely above the critical
discount. At equality the reciprocal logarithmic divergence persists. -/
theorem eighth_power_discount_summable_iff (p : ℝ) :
    Summable (gcdPowerCharge 8 p) ↔ 1 < p := by
  rw [gcd_power_discount_summable_iff]
  apply or_iff_left_of_imp
  rintro ⟨B,hB⟩
  obtain ⟨c,hc⟩ := eighth_gcd_deficit_centered_converges
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨k,h₁,h₂⟩ := ((hc.eventually_const_lt (sub_one_lt c)).and
    (hlog.eventually_gt_atTop (2*(B-c+1)))).exists
  exfalso
  linarith only [h₁,h₂,hB (mem_range_self k)]

#print axioms supercritical_gcd_tail
#print axioms gcd_power_discount_summable_iff
#print axioms eighth_power_discount_summable_iff

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
