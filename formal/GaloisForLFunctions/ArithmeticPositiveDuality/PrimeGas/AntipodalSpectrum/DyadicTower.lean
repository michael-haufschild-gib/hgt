import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.HalvingPartition

/-!
# Occupation and trace limits of repeated clock halving

All positive windings on the common primitive ray eventually enter.
The omitted thermal weight is a geometric tail with exponent equal to
the current winding order.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks DyadicAperture.Binary Filter
open scoped Topology

def refined (t : ExceptionalTime) : ℕ → ExceptionalTime
  | 0 => t
  | j+1 => halfClock (refined t j)

theorem refined_parameters (t : ExceptionalTime) (j : ℕ) :
    leastWords (refined t j) = leastWords t ∧ block (refined t j) = block t ∧
      windingOrder (refined t j) = 2^j*windingOrder t := by
  induction j with
  | zero => exact ⟨rfl,rfl,by simp [refined]⟩
  | succ j ih =>
    exact ⟨(half_leastWords _).trans ih.1,(half_block _).trans ih.2.1,
      by rw [refined,half_windingOrder,ih.2.2,pow_succ',Nat.mul_assoc]⟩

private theorem order_grows (t : ExceptionalTime) : Tendsto (fun j : ℕ => 2^j*windingOrder t) atTop atTop := by
  apply tendsto_atTop_mono (fun _ => Nat.le_mul_of_pos_right _ (Nat.zero_lt_one.trans (order_nontrivial t)))
  exact tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ))

/-- Exactly the positive windings occur in the union over all refinement levels. -/
theorem refined_union (t : ExceptionalTime) (x : leastWords t) (y : Word) :
    (∃ j, rejected (refined t j).val y) ↔
      ∃ (r : Bool) (k : ℕ+) (n : ℕ+), y = ray (x.val false) (x.val true) r k.val n := by
  have hx (j : ℕ) : x.val ∈ leastWords (refined t j) := (refined_parameters t j).1.symm ▸ x.property
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨r,k,n,he⟩ := (least_support _ ⟨_,hx j⟩ y).mp hj
    have hn : k.val ≠ 0 := fun hz => k.property (hz ▸ dvd_zero _)
    exact ⟨r,⟨k.val,Nat.pos_of_ne_zero hn⟩,n,he⟩
  · rintro ⟨r,k,n,rfl⟩
    obtain ⟨j,hj⟩ := ((order_grows t).eventually_gt_atTop k.val).exists
    refine ⟨j,(least_ray_rejected _ ⟨_,hx j⟩ r k.val n).mpr ?_⟩
    rw [(refined_parameters t j).2.2]
    exact fun hd => hj.not_ge (Nat.le_of_dvd k.property hd)

def saturatedResponse (t : ExceptionalTime) (s : ℂ) :=
  riemannZeta (2*s)*(2*heat s (block t)/(1-heat s (block t)))

theorem response_deficit (t : ExceptionalTime) (s : {z : ℂ // 0 < z.re}) :
    saturatedResponse t s.val-response t s.val =
      riemannZeta (2*s.val)*(2*(heat s.val (block t))^(windingOrder t)/
        (1-(heat s.val (block t))^(windingOrder t))) := by
  unfold saturatedResponse response
  rw [← mul_sub,factor_deficit (heat_contraction _ (block_nontrivial t) _ s.property) (order_nontrivial t)]

theorem refined_deficit (t : ExceptionalTime) (s : {z : ℂ // 0 < z.re}) (j : ℕ) :
    saturatedResponse t s.val-response (refined t j) s.val =
      riemannZeta (2*s.val)*(2*(heat s.val (block t))^(2^j*windingOrder t)/
        (1-(heat s.val (block t))^(2^j*windingOrder t))) := by
  obtain ⟨_,hb,hm⟩ := refined_parameters t j
  simpa only [saturatedResponse,hb,hm] using response_deficit (refined t j) s

private theorem geometric_tail {q : ℂ} (hq : ‖q‖ < 1) (Z : ℂ) {M : ℕ → ℕ} (hM : Tendsto M atTop atTop) :
    Tendsto (fun j => Z*(2*q^(M j)/(1-q^(M j)))) atTop (𝓝 0) := by
  have hu := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp hM
  simpa only [Function.comp_apply,mul_zero,sub_zero,zero_div] using
    (tendsto_const_nhds (x := Z)).mul
      (((tendsto_const_nhds (x := (2:ℂ))).mul hu).div ((tendsto_const_nhds (x := (1:ℂ))).sub hu) (by simp))

/-- Increasing order at a fixed lowest product has the same thermal limit along every sequence. -/
theorem fixed_block_limit (v : ℕ → ExceptionalTime) (H : ℕ+) (hH : ∀ j, block (v j) = H)
    (hM : Tendsto (fun j => windingOrder (v j)) atTop atTop) (s : {z : ℂ // 0 < z.re}) :
    Tendsto (fun j => response (v j) s.val) atTop
      (𝓝 (riemannZeta (2*s.val)*(2*heat s.val H/(1-heat s.val H)))) := by
  have hg : 1 < H.val := hH 0 ▸ block_nontrivial (v 0)
  let L := riemannZeta (2*s.val)*(2*heat s.val H/(1-heat s.val H))
  have h := (tendsto_const_nhds (x := L)).sub
    (geometric_tail (heat_contraction _ hg _ s.property) (riemannZeta (2*s.val)) hM)
  simp only [sub_zero] at h
  apply h.congr
  intro j
  have hd := response_deficit (v j) s
  simp only [saturatedResponse,hH] at hd
  dsimp only [L]
  linear_combination hd

theorem refined_limit (t : ExceptionalTime) (s : {z : ℂ // 0 < z.re}) :
    Tendsto (fun j => response (refined t j) s.val) atTop (𝓝 (saturatedResponse t s.val)) := by
  apply fixed_block_limit (refined t) (block t) (fun j => (refined_parameters t j).2.1) _ s
  exact (order_grows t).congr fun j => (refined_parameters t j).2.2.symm

#print axioms refined_parameters
#print axioms refined_union
#print axioms refined_deficit
#print axioms fixed_block_limit
#print axioms refined_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
