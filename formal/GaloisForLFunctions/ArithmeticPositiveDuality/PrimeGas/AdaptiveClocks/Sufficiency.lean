import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.BlockCodes

/-!
# Summability above the two adaptive exponents

The integer endpoint in a row contributes the smaller-bin count, at most
exp(S/2) up to calibration. The width of the row contributes exp((1−α)S).
After multiplying by the heat weight both terms are geometric.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Clock

open scoped Classical
variable (M : Clock)

private theorem geometric {q : ℝ} (hq : q < 0) :
    Summable fun j : ℕ => Real.exp ((j : ℝ)*q) := by
  simpa only [Real.exp_nat_mul] using summable_geometric_of_lt_one (Real.exp_pos q).le (Real.exp_lt_one_iff.mpr hq)

private theorem block_geometric {q : ℝ} (hq : q < 0) :
    Summable fun k : ℕ × ℕ => Real.exp (q*M.total k) := by
  have h₁ := geometric (mul_neg_of_neg_of_pos hq (mul_pos (by norm_num : (0:ℝ)<2) M.step_pos))
  have h₂ := geometric (mul_neg_of_neg_of_pos hq M.step_pos)
  refine (h₁.mul_of_nonneg h₂ (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)).congr fun k => ?_
  rw [← Real.exp_add,total,base,base,Nat.cast_add]
  congr 1
  ring

/-- The endpoint term retains the smaller energy, which controls the contribution of sparse rows. -/
theorem slot_bound (k : ℕ × ℕ) (σ : ℝ) :
    (M.lowSlots k : ℝ)*(M.highSlots k : ℝ)*Real.exp (-σ*M.total k) ≤
      Real.exp M.step*Real.exp (M.base k.1-σ*M.total k) +
        (M.spread*Real.exp M.step)*Real.exp ((1-(M.exponent : ℝ)-σ)*M.total k) := by
  let L := M.base k.1
  let H := M.base (k.1+k.2)
  let S := M.total k
  have hS : S = L+H := rfl
  have hlo : (M.lowSlots k : ℝ) ≤ Real.exp (L+M.step) := Nat.floor_le (Real.exp_pos _).le
  have hroom : 0 ≤ M.room k := mul_nonneg M.spread_nonneg (Real.exp_pos _).le
  have hhi : (M.highSlots k : ℝ) ≤ M.room k+1 := by
    simpa only [highSlots,Nat.cast_add,Nat.cast_one] using add_le_add (Nat.floor_le hroom) (le_refl (1:ℝ))
  refine (mul_le_mul_of_nonneg_right (mul_le_mul hlo hhi (Nat.cast_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le).trans ?_
  rw [mul_add,mul_one,add_mul,add_comm (Real.exp _ * M.room k * _)]
  apply add_le_add
  · rw [← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
    change L+M.step + -σ*S ≤ M.step+(L-σ*S)
    linarith
  · change Real.exp (L+M.step) * (M.spread*Real.exp (H-(M.exponent:ℝ)*S)) * Real.exp (-σ*S) ≤ _
    apply le_of_eq
    calc
      _ = M.spread*(Real.exp (L+M.step)*Real.exp (H-(M.exponent:ℝ)*S)*Real.exp (-σ*S)) := by ring
      _ = M.spread*(Real.exp M.step*Real.exp ((1-(M.exponent:ℝ)-σ)*S)) := by
        rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
        congr 2
        rw [hS]
        ring
      _ = _ := (mul_assoc _ _ _).symm

private theorem code_summable {σ : ℝ} (hd : 1/2 < σ) (ha : 1-(M.exponent : ℝ) < σ) :
    Summable (fun z : M.Code => Real.exp (-σ*M.total z.1)) := by
  apply (summable_sigma_of_nonneg (fun z : M.Code => (Real.exp_pos (-σ*M.total z.1)).le)).mpr
  refine ⟨fun _ => Summable.of_finite,?_⟩
  have h := ((M.block_geometric (sub_neg.mpr hd)).mul_left (Real.exp M.step)).add
    ((M.block_geometric (sub_neg.mpr ha)).mul_left (M.spread*Real.exp M.step))
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_mul]
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ h
  intro k
  apply (M.slot_bound k σ).trans
  refine add_le_add ?_ le_rfl
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  have hL : M.base k.1 ≤ M.base (k.1+k.2) := mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (Nat.le_add_right k.1 k.2)) M.step_pos.le
  unfold total
  nlinarith only [hL]

private def orient (p : M.Word) : Bool × M.Ordered :=
  if h : p.val.2 ≤ p.val.1 then (false,⟨p,h⟩)
  else (true,⟨⟨p.val.swap,(M.passes_swap p.val).mpr p.property⟩,(le_of_not_ge h)⟩)

private theorem orient_injective : Function.Injective M.orient := by
  let recover (z : Bool × M.Ordered) : Pair := cond z.1 z.2.val.val.swap z.2.val.val
  have h (p : M.Word) : recover (M.orient p) = p.val := by
    unfold orient
    split <;> rfl
  intro p q he
  exact Subtype.ext ((h p).symm.trans ((congrArg recover he).trans (h q)))

private theorem orient_weight (σ : ℝ) (p : M.Word) :
    weight σ (M.orient p).2.val.val = weight σ p.val := by
  unfold orient
  split
  · rfl
  · change Real.exp (-σ*(energy p.val.2+energy p.val.1)) = _
    rw [add_comm]
    rfl

theorem heat_sum_of_bounds (ht : M.time ≠ 0) {σ : ℝ}
    (hd : 1/2 < σ) (ha : 1-(M.exponent : ℝ) < σ) : M.HeatSum σ := by
  have hσ : 0 ≤ σ := by linarith only [hd]
  have hs : Summable fun p : M.Ordered => weight σ p.val.val :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (M.block_weight hσ)
      ((M.code_summable hd ha).comp_injective (i := M.encode ht) (M.encode_injective ht))
  have hh : Summable fun p : Bool × M.Ordered => weight σ p.2.val.val :=
    (summable_prod_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr ⟨fun _ => hs,Summable.of_finite⟩
  exact (hh.comp_injective (i := M.orient) M.orient_injective).congr (M.orient_weight σ)

#print axioms heat_sum_of_bounds
#print axioms slot_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Clock
