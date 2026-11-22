import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Binary

/-!
# Two lower bounds on the adaptive heat boundary

The diagonal supplies a copy of the gas at twice the inverse temperature.
An integer strip about it contains more than a constant times n^(1−2α)
offsets on row n. Summing that strip gives the second necessary exponent.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Clock

variable (M : Clock)

theorem diagonal_bound {σ : ℝ} (h : M.HeatSum σ) : 1/2 < σ := by
  let d (n : ℕ+) : M.Word := ⟨(n,n),M.passes_diag n⟩
  have hi : Function.Injective d := fun _ _ he => congrArg (fun x : M.Word => x.val.1) he
  have hs : Summable fun n : ℕ+ => Real.exp (-(2*σ)*energy n) := by
    refine (h.comp_injective (i := d) hi).congr fun n => ?_
    change Real.exp (-σ*(energy n+energy n)) = _
    congr 1
    ring
  linarith only [(single_summable_iff (2*σ)).mp hs]

private def fraction : ℝ := min 1 (M.scale.val*Real.exp (-(M.exponent : ℝ))/(|M.time| +1))

private theorem fraction_pos : 0 < M.fraction :=
  lt_min zero_lt_one (div_pos (mul_pos M.scale.property (Real.exp_pos _)) (by positivity))

private theorem fraction_le : M.fraction ≤ 1 := min_le_left _ _

private theorem fraction_time : |M.time| *M.fraction < M.scale.val*Real.exp (-(M.exponent : ℝ)) := by
  have h := (le_div_iff₀ (by positivity : 0 < |M.time| +1)).mp (min_le_right 1
    (M.scale.val*Real.exp (-(M.exponent : ℝ))/(|M.time| +1)))
  change M.fraction*(|M.time| +1) ≤ _ at h
  nlinarith only [h,M.fraction_pos]

private def width (n : ℕ+) := M.fraction * Real.exp ((1-2*(M.exponent : ℝ))*energy n)

private def count (n : ℕ+) := ⌊M.width n⌋₊ + 1

def offset (n : ℕ+) (d : ℕ) : ℕ+ := ⟨n.val+d,Nat.add_pos_left n.pos d⟩

theorem log_offset (n : ℕ+) (d : ℕ) :
    energy (offset n d) - energy n ≤ (d : ℝ)/(n : ℕ) := by
  have hn : (0:ℝ) < (n : ℕ) := Nat.cast_pos.mpr n.pos
  have hd : (0:ℝ) < (n : ℕ)+(d : ℝ) := by positivity
  have hh := Real.log_le_sub_one_of_pos (div_pos hd hn)
  rw [Real.log_div hd.ne' hn.ne'] at hh
  change Real.log ((n.val+d : ℕ) : ℝ) - Real.log (n.val : ℝ) ≤ _
  rw [Nat.cast_add]
  exact hh.trans_eq (by field_simp; ring)

private theorem gap_bound (n : ℕ+) (d : Fin (M.count n)) :
    energy (offset n d.val) - energy n ≤ M.fraction * Real.exp (-2*(M.exponent : ℝ)*energy n) := by
  apply (log_offset n d.val).trans
  rw [div_le_iff₀ (Nat.cast_pos.mpr n.pos : (0:ℝ)<(n:ℕ)),← exp_energy n,mul_assoc,← Real.exp_add]
  have h : (d.val : ℝ) ≤ M.width n :=
    (Nat.cast_le.mpr (Nat.le_of_lt_succ d.isLt)).trans (Nat.floor_le (mul_nonneg M.fraction_pos.le (Real.exp_pos _).le))
  apply h.trans_eq
  unfold width
  congr 2
  ring

private theorem gap_le_one (n : ℕ+) (d : Fin (M.count n)) :
    energy (offset n d.val) - energy n ≤ 1 := by
  apply (M.gap_bound n d).trans
  have he : Real.exp (-2*(M.exponent : ℝ)*energy n) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) M.exponent.property) (energy_nonneg n))
  exact (mul_le_mul_of_nonneg_left he M.fraction_pos.le).trans (by simpa using M.fraction_le)

private theorem offset_weight (q : ℝ) (hq : 0 ≤ q) (n : ℕ+) (d : Fin (M.count n)) :
    Real.exp (-q) * Real.exp (-2*q*energy n) ≤ weight q (offset n d.val,n) := by
  rw [← Real.exp_add,weight,Real.exp_le_exp]
  have h := mul_le_mul_of_nonneg_left (M.gap_le_one n d) hq
  nlinarith only [h]

private theorem offset_passes (n : ℕ+) (d : Fin (M.count n)) : M.Passes (offset n d.val,n) := by
  let w := Real.exp (-2*(M.exponent : ℝ)*energy n)
  have hne : n ≤ offset n d.val := Nat.le_add_right n.val d.val
  have hc := chord_le M.time (offset n d.val) n
  rw [abs_of_nonneg (sub_nonneg.mpr (energy_mono hne))] at hc
  refine (hc.trans (mul_le_mul_of_nonneg_left (M.gap_bound n d) (abs_nonneg _))).trans_lt ?_
  change |M.time| *(M.fraction*w) < _
  rw [← mul_assoc]
  refine (mul_lt_mul_of_pos_right M.fraction_time (Real.exp_pos _)).trans_le ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (M.offset_weight M.exponent M.exponent.property n d) M.scale.property.le

private def strip (x : Σ n, Fin (M.count n)) : M.Word := ⟨(offset x.1 x.2.val,x.1),M.offset_passes x.1 x.2⟩

private theorem strip_injective : Function.Injective M.strip := by
  rintro ⟨n,d⟩ ⟨m,e⟩ he
  have hnm : n = m := congrArg (fun x : M.Word => x.val.2) he
  subst m
  have h : n.val+d.val = n.val+e.val := congrArg (fun x : M.Word => x.val.1.val) he
  exact congrArg (Sigma.mk n) (Fin.ext (Nat.add_left_cancel h))

theorem strip_bound {σ : ℝ} (h : M.HeatSum σ) : 1-(M.exponent : ℝ) < σ := by
  have hσ : 0 ≤ σ := by linarith only [M.diagonal_bound h]
  let w (n : ℕ+) := Real.exp (-σ)*Real.exp (-2*σ*energy n)
  have hw (n : ℕ+) : 0 < w n := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hs : Summable (fun x : Σ n, Fin (M.count n) => w x.1) :=
    Summable.of_nonneg_of_le (fun x => (hw x.1).le) (fun x => M.offset_weight σ hσ x.1 x.2)
      (h.comp_injective (i := M.strip) M.strip_injective)
  have hr := ((summable_sigma_of_nonneg (fun x : Σ n, Fin (M.count n) => (hw x.1).le)).mp hs).2
  have hc : Summable fun n : ℕ+ => (M.count n : ℝ)*w n := by
    simpa only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hr
  let ρ := 2*σ+2*(M.exponent : ℝ)-1
  let C := M.fraction*Real.exp (-σ)
  have hC : 0 < C := mul_pos M.fraction_pos (Real.exp_pos _)
  have hj : Summable fun n : ℕ+ => C*Real.exp (-ρ*energy n) := by
    apply Summable.of_nonneg_of_le (fun _ => mul_nonneg hC.le (Real.exp_pos _).le) _ hc
    intro n
    have hh : M.width n ≤ (M.count n : ℝ) := by
      simpa only [count,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (M.width n)).le
    apply le_trans _ (mul_le_mul_of_nonneg_right hh (hw n).le)
    apply le_of_eq
    have hρ : -ρ*energy n = (1-2*(M.exponent:ℝ))*energy n + -2*σ*energy n := by dsimp [ρ]; ring
    rw [hρ,Real.exp_add]
    dsimp [C,w,width]
    ring
  have hh : Summable fun n : ℕ+ => Real.exp (-ρ*energy n) := by
    simpa only [← mul_assoc,inv_mul_cancel₀ hC.ne',one_mul] using hj.mul_left C⁻¹
  have he := (single_summable_iff ρ).mp hh
  dsimp [ρ] at he
  linarith only [he]

#print axioms diagonal_bound
#print axioms strip_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Clock
