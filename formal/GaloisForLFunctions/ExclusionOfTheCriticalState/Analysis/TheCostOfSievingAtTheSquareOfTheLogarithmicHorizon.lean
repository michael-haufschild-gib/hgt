import GaloisForLFunctions.RHTower.ThetaChronologicalPacketResolution

/-!
# The local absolute cost of a growing prime sieve

Up to the square of the logarithmic observation time, the product of the
inverse half-power local factors has subexponential growth. The prime
number estimate enters through the half-power sum with one logarithmic saving.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

private theorem local_cost_bound (p : Nat.Primes) :
    (1-(Real.sqrt (p:ℕ))⁻¹)⁻¹ ≤ Real.exp (4*(Real.sqrt (p:ℕ))⁻¹) := by
  let a := (Real.sqrt (p:ℕ))⁻¹
  have h2 : (2:ℝ) ≤ (p:ℕ) := by exact_mod_cast p.2.two_le
  have hs : 0 < Real.sqrt (p:ℕ) := Real.sqrt_pos.2 (by linarith)
  have hroot : (4/3:ℝ) ≤ Real.sqrt (p:ℕ) := (Real.le_sqrt (by norm_num) (by positivity)).2 (by linarith)
  have ha : 0 ≤ a := inv_nonneg.2 hs.le
  have hq : a ≤ 3/4 := by
    dsimp only [a]
    rw [← one_div,div_le_iff₀ hs]; linarith only [hroot]
  have hd : 0 < 1-a := by linarith only [hq]
  change (1-a)⁻¹ ≤ _
  calc _ ≤ 4*a+1 := by
         rw [← one_div,div_le_iff₀ hd]
         nlinarith only [mul_nonneg ha (sub_nonneg.2 hq)]
    _ ≤ _ := Real.add_one_le_exp _

/-- Uniform in the subset of primes, including the entire initial segment. -/
theorem sieve_half_cost_le (P : Finset Nat.Primes) {T : ℝ} (hT : 3 ≤ T)
    (hP : ∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) :
    (∏ p ∈ P, (1-(Real.sqrt (p:ℕ))⁻¹)⁻¹) ≤ Real.exp (8*Real.sqrt T+64*T/Real.log T) := by
  let N := ⌊T^2⌋₊
  have hTN : T ≤ (N:ℝ) := by
    have h : T^2 < (N:ℝ)+1 := Nat.lt_floor_add_one _
    nlinarith only [h,hT,sq_nonneg (T-2)]
  have hN : 2 ≤ N := by exact_mod_cast (show 2 ≤ (N:ℝ) by linarith)
  have hT0 : 0 < T := by linarith
  have hlog := Real.log_pos (show 1 < T by linarith)
  have hsN : Real.sqrt N ≤ T := (Real.sqrt_le_sqrt (Nat.floor_le (sq_nonneg T))).trans_eq (Real.sqrt_sq hT0.le)
  let e : Nat.Primes ↪ ℕ := ⟨Subtype.val,Subtype.coe_injective⟩
  have hsub : P.map e ⊆ Nat.primesLE N := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := mem_map.1 hn
    exact Nat.mem_primesLE.2 ⟨Nat.le_floor (hP p hp),p.2⟩
  have hob : (∑ p ∈ P, (Real.sqrt (p:ℕ))⁻¹) ≤ ∑ n ∈ Nat.primesLE N, (n:ℝ)^(-(1/2:ℝ)) := by
    calc _ = ∑ n ∈ P.map e, (n:ℝ)^(-(1/2:ℝ)) := by
                simp only [sum_map,_root_.RHTower.natCast_rpow_neg_half_eq,Function.Embedding.coeFn_mk,e]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hl := Real.log_le_log hT0 hTN
  have hd : Real.sqrt N/Real.log N ≤ T/Real.log T := div_le_div₀ (by positivity) hsN hlog hl
  have hsum := hob.trans (_root_.RHTower.sum_primesLE_rpow_neg_half_le hN)
  calc _ ≤ ∏ p ∈ P, Real.exp (4*(Real.sqrt (p:ℕ))⁻¹) := by
           apply prod_le_prod (fun p _ => ?_) (fun p _ => local_cost_bound p)
           have hh := Real.sqrt_le_sqrt (by exact_mod_cast p.2.one_le : (1:ℝ) ≤ (p:ℕ))
           rw [Real.sqrt_one] at hh
           exact inv_nonneg.2 (sub_nonneg.2 (inv_le_one_of_one_le₀ hh))
    _ = Real.exp (4*∑ p ∈ P, (Real.sqrt (p:ℕ))⁻¹) := by rw [mul_sum,Real.exp_sum]
    _ ≤ _ := by
           apply Real.exp_le_exp.2
           rw [mul_div_assoc 16] at hsum
           rw [mul_div_assoc 64]
           linarith only [hsum,hd,Real.sqrt_le_sqrt hsN]

/-- Even after multiplication by the observation length the cost is smaller
than every fixed positive exponential rate. -/
theorem eventually_quadratic_sieve_cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, T*Real.exp (8*Real.sqrt T+64*T/Real.log T) ≤ Real.exp (ε*T) := by
  have hl : Tendsto (fun T : ℝ => Real.log T/T) atTop (𝓝 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hs : Tendsto (fun T : ℝ => (Real.sqrt T)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hL : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have h := (hl.add (hs.const_mul 8)).add (hL.const_mul 64)
  simp only [mul_zero,add_zero] at h
  filter_upwards [h.eventually_lt_const hε,eventually_gt_atTop (1:ℝ)] with T ht hT
  have hT0 := zero_lt_one.trans hT
  have hr := Real.sq_sqrt hT0.le
  have hpos := Real.sqrt_pos.2 hT0
  have he : (Real.log T/T+8*(Real.sqrt T)⁻¹+64*(Real.log T)⁻¹)*T =
      Real.log T+(8*Real.sqrt T+64*T/Real.log T) := by
    have hroot : (Real.sqrt T)⁻¹*T=Real.sqrt T := by
      calc _ = (Real.sqrt T)⁻¹*((Real.sqrt T)^2) := congrArg (fun v => (Real.sqrt T)⁻¹*v) hr.symm
        _ = _ := by field_simp
    rw [add_mul,add_mul,div_mul_cancel₀ _ hT0.ne',mul_assoc 8,hroot]; ring
  calc _ = Real.exp (Real.log T+(8*Real.sqrt T+64*T/Real.log T)) := by
           rw [Real.exp_add (Real.log T),Real.exp_log hT0]
    _ ≤ _ := Real.exp_le_exp.2 (he.symm.le.trans (mul_le_mul_of_nonneg_right ht.le hT0.le))

#print axioms eventually_quadratic_sieve_cost_le_exp
#print axioms sieve_half_cost_le

end GaloisForLFunctions.ExclusionOfTheCriticalState
