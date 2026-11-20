import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TheSharpHardyConstantOnAGeometricMesh
import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.ExponentialMomentsOfUnitStepRadiation

/-!
# Square costs of modular radiation in unit time

At every positive exponent the weighted sampled tail energy and its local
releases have equivalent square summability, including the exponent itself.
The geometric Hardy inequality gives the exact sequence-space constant.
Only the releases on individual unit intervals enter the resulting RH test.
-/

noncomputable section
open Filter Finset
open scoped Topology
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Square of the exponentially weighted remaining energy at integer time. -/
def sampledTailSquare (h : CompactPulse) (b : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (b*n)*tailEnergy h n)^2

/-- Square of the weighted energy escaping during a single unit interval. -/
def unitRadiationSquare (h : CompactPulse) (b : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (b*n)*stepDecrement h n 1)^2

private theorem release_eq_difference (h : CompactPulse) (n : ℕ) :
    stepDecrement h n 1=tailEnergy h n-tailEnergy h (n+1:ℕ) := by
  rw [←tailEnergy_sub_step h _ zero_le_one,Nat.cast_succ]

private theorem release_square_le_tail (h : CompactPulse) (b : ℝ) (n : ℕ) :
    unitRadiationSquare h b n ≤ sampledTailSquare h b n := by
  apply pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (stepDecrement_nonneg h n 1))
  exact mul_le_mul_of_nonneg_left ((release_eq_difference h n).le.trans (sub_le_self _ (tailEnergy_nonneg _ _)))
    (Real.exp_pos _).le

private theorem reciprocal_radiation_scale (b : ℝ) (i : ℕ) :
    ((Real.exp (-b))⁻¹)^i=Real.exp (b*i) := by
  rw [Real.exp_neg,inv_inv,←Real.exp_nat_mul]
  congr 1
  ring

/-- A uniform bound on the squared releases controls every finite sample of the
tail at the same exponent and retains the geometric Hardy coefficient. -/
theorem sampled_tail_square_of_release_budget (h : CompactPulse) {b : ℝ} (hb : 0<b) {C : ℝ}
    (budget : ∀ m : ℕ, (∑ i ∈ range m,unitRadiationSquare h b i)≤C) (L : ℕ) :
    (1-Real.exp (-b))^2*(∑ i ∈ range L,sampledTailSquare h b i)≤C := by
  let q := Real.exp (-b)
  have small : q<1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb)
  have scale := reciprocal_radiation_scale b
  have vanish : Tendsto (fun i : ℕ => tailEnergy h i) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_tailEnergy_atTop h).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have total (m : ℕ) : (∑ i ∈ range m,((q⁻¹)^i*(tailEnergy h i-tailEnergy h (i+1:ℕ)))^2)≤C := by
    dsimp only [q]
    simp_rw [scale,←release_eq_difference]
    exact budget m
  have bound := ArithmeticHarmonicAnalysis.geometric_hardy_tail_control (Real.exp_pos _) small
    (fun i : ℕ => tailEnergy h i) vanish total L
  simpa only [scale,sampledTailSquare,q] using bound

/-- Critical-exponent equivalence for one actual pulse. No loss in the
exponential rate is needed to pass from squared local losses to squared tails. -/
theorem radiation_square_summable_iff_tail_square (h : CompactPulse) {b : ℝ} (hb : 0<b) :
    Summable (unitRadiationSquare h b) ↔ Summable (sampledTailSquare h b) := by
  constructor
  · intro paid
    have factor := sq_pos_of_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb)))
    apply summable_of_sum_range_le (fun i => sq_nonneg _)
      (c:=(∑' i,unitRadiationSquare h b i)/(1-Real.exp (-b))^2)
    intro m
    apply (le_div_iff₀ factor).mpr
    rw [mul_comm]
    exact sampled_tail_square_of_release_budget h hb (fun j => paid.sum_le_tsum (range j)
      (fun i _ => sq_nonneg _)) m
  · intro tails
    exact tails.of_nonneg_of_le (fun i => sq_nonneg _) (release_square_le_tail h b)

/-- A tail of size E at time m imposes an absolute future square cost.
If the tail stays fixed for k further unit intervals, moving m forward by k
multiplies this floor by exp(2 b k). -/
theorem remaining_radiation_square_cost (h : CompactPulse) (b : ℝ) (m : ℕ) {C : ℝ}
    (budget : ∀ N : ℕ, (∑ i ∈ range N,unitRadiationSquare h b (m+i))≤C) :
    (1-Real.exp (-b)^2)*(Real.exp (b*m)*tailEnergy h m)^2≤C := by
  let v (i : ℕ) := Real.exp (b*m)*tailEnergy h (m+i:ℕ)
  have grow : Tendsto (fun i : ℕ => (m:ℝ)+(i:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ (m:ℝ) tendsto_natCast_atTop_atTop
  have vanish : Tendsto v atTop (𝓝 0) := by
    simpa only [v,Function.comp_apply,Nat.cast_add,mul_zero] using
      ((tendsto_tailEnergy_atTop h).comp grow).const_mul (Real.exp (b*m))
  have loss (N : ℕ) : (∑ i ∈ range N,(((Real.exp (-b))⁻¹)^i*(v i-v (i+1)))^2)≤C := by
    apply le_trans ?_ (budget N)
    apply sum_le_sum
    intro i _
    have price : Real.exp (b*i)*Real.exp (b*m)=Real.exp (b*(m+i:ℕ)) := by
      rw [←Real.exp_add,Nat.cast_add]
      congr 1
      ring
    rw [reciprocal_radiation_scale,unitRadiationSquare,release_eq_difference]
    dsimp only [v]
    rw [←mul_sub,←mul_assoc,price,Nat.add_assoc]
  have bound := ArithmeticHarmonicAnalysis.geometric_hardy_endpoint_cost (Real.exp_pos (-b)) v vanish loss
  simpa only [v,add_zero] using bound

/-- A stalled interval increases the lower bound on the eventual radiation
cost by the exact exponential factor attached to its length. -/
theorem stalled_radiation_square_cost (h : CompactPulse) (b : ℝ) (m k : ℕ)
    (stall : tailEnergy h (m+k:ℕ)=tailEnergy h m) {C : ℝ}
    (budget : ∀ N : ℕ, (∑ i ∈ range N,unitRadiationSquare h b (m+k+i))≤C) :
    (Real.exp (b*k))^2*((1-Real.exp (-b)^2)*(Real.exp (b*m)*tailEnergy h m)^2)≤C := by
  have bound := remaining_radiation_square_cost h b (m+k) budget
  rw [stall,Nat.cast_add,mul_add,Real.exp_add] at bound
  exact (show (Real.exp (b*k))^2*((1-Real.exp (-b)^2)*(Real.exp (b*m)*tailEnergy h m)^2)=
    (1-Real.exp (-b)^2)*(Real.exp (b*m)*Real.exp (b*k)*tailEnergy h m)^2 by ring).le.trans bound

/-- A sequence of weighted local releases can be tested by square moments
through every exponent below one half. -/
theorem rh_iff_squared_unit_radiation :
    RiemannHypothesis ↔ ∀ h : CompactPulse, ∀ b : ℝ, b<1/2 → Summable (unitRadiationSquare h b) := by
  rw [rh_iff_unit_radiation_moments]
  constructor
  · intro moments h b hb
    let f (i : ℕ) := Real.exp (b*i)*stepDecrement h i 1
    have pos (i : ℕ) : 0≤f i := mul_nonneg (Real.exp_pos _).le (stepDecrement_nonneg h i 1)
    have paid : Summable f := moments h b hb
    apply (paid.mul_left (∑' i,f i)).of_nonneg_of_le (fun _ => sq_nonneg _)
    intro i
    have bound := paid.sum_le_tsum {i} (fun j _ => pos j)
    rw [sum_singleton] at bound
    exact (show f i^2=f i*f i from pow_two _).le.trans (mul_le_mul_of_nonneg_right bound (pos i))
  · intro square h b hb
    obtain ⟨c,bc,half⟩ := exists_between hb
    have paid := square h c half
    let C := (∑' i,unitRadiationSquare h c i)+1
    apply summable_weighted_decrements_of_envelope h bc
    refine ⟨C,fun i => ?_⟩
    let x := Real.exp (c*i)*stepDecrement h i 1
    have bound := paid.sum_le_tsum {i} (fun j _ => sq_nonneg _)
    rw [sum_singleton] at bound
    change x^2≤∑' j,unitRadiationSquare h c j at bound
    have lx : x≤C := (show x≤x^2+1 by nlinarith only [sq_nonneg (x-1/2)]).trans
      (add_le_add bound (le_refl 1))
    have positive := Real.exp_pos (-c*(i:ℝ))
    have undo : x*Real.exp (-c*(i:ℝ))=stepDecrement h i 1 := by
      dsimp only [x]
      rw [mul_right_comm,←Real.exp_add,show c*(i:ℝ)+ -c*i=0 by ring,Real.exp_zero,one_mul]
    exact undo ▸ mul_le_mul_of_nonneg_right lx positive.le

end GaloisForLFunctions.BlackHoleRingdown
