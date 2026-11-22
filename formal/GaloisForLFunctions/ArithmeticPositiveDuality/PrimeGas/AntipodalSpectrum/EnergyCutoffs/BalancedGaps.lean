import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedBands
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedHeat

/-!
# Empty intervals between balanced occupation cutoffs

At each scale the last balanced cutoff has an explicit digit expansion.
This confines all positive balanced labels to a fixed fraction of each radix band.
-/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

/-- The exact last balanced cutoff below a radix power and the next balanced label. -/
theorem balanced_cutoff_gap (t : ExceptionalTime) (j k : ℕ) :
    let C := (tailRadix t j).val
    let B := C^2
    let P := fun X => Nat.card (countingStates t j X) = (C+1)*Nat.card (countingStates t (j+1) X)
    IsGreatest {X : ℕ | X < B^k ∧ P X} ((B^k-1)/(C+1)) ∧ P (B^k) := by
  let C : {c : ℕ // 1 < c} := ⟨(tailRadix t j).val,radix_gt_one t j⟩
  let B := C.val^2
  let L := lastBalancedWord C.val k
  have hs : (C.val+1)*L+1 = B^k := last_balanced_scale C k
  have hL : (B^k-1)/(C.val+1) = L := by
    rw [← hs,Nat.add_sub_cancel,Nat.mul_div_cancel_left _ (Nat.succ_pos _)]
  change IsGreatest {X : ℕ | X < B^k ∧ _} ((B^k-1)/(C.val+1)) ∧ _
  rw [hL]
  obtain ⟨h₁,h₂⟩ := balanced_gap_endpoints C k
  refine ⟨⟨⟨?_,(adjacent_count_equality t j L).mpr h₁⟩,?_⟩,(adjacent_count_equality t j (B^k)).mpr h₂⟩
  · rw [← hs]
    exact Nat.lt_succ_of_le (Nat.le_mul_of_pos_left L (Nat.succ_pos _))
  · intro X hx
    have h := stretched_band_cap C k ⟨X,hx.1,(adjacent_count_equality t j X).mp hx.2⟩
    change (C.val+1)*X+1 ≤ B^k at h
    rw [← hs] at h
    exact Nat.le_of_mul_le_mul_left (Nat.le_of_succ_le_succ h) (Nat.succ_pos _)

/-- Each positive balanced label lies in the lower fraction 1/(C+1) of the next cutoff power. -/
theorem balanced_label_band (t : ExceptionalTime) (j : ℕ) (x : PositiveBalancedCutoff t j) :
    let C := (tailRadix t j).val
    let B := C^2
    ∃ k : ℕ, B^k ≤ x.val.val ∧ (C+1)*x.val.val < B*B^k := by
  let C : {c : ℕ // 1 < c} := ⟨(tailRadix t j).val,radix_gt_one t j⟩
  let B := C.val^2
  let n := x.val.val
  let k := Nat.log B n
  have hb : 1 < B := one_lt_pow₀ C.property (by norm_num : (2:ℕ) ≠ 0)
  refine ⟨k,Nat.pow_log_le_self B x.property.ne',?_⟩
  have h := stretched_band_cap C (k+1) ⟨n,Nat.lt_pow_succ_log_self hb n,(adjacent_count_equality t j n).mp x.val.property⟩
  change (C.val+1)*n+1 ≤ B^(k+1) at h
  rw [pow_succ'] at h
  exact h

/-- At the first radix frequency every balanced label lies in one arc strictly shorter than π. -/
theorem balanced_clock_arc (t : ExceptionalTime) (j : ℕ) :
    let τ := Real.pi / energy (tailRadix t j)
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < Real.pi ∧ ∀ x : PositiveBalancedCutoff t j, ∃ k : ℕ,
      0 ≤ τ*Real.log (x.val.val:ℝ)-(k:ℝ)*(2*Real.pi) ∧
      τ*Real.log (x.val.val:ℝ)-(k:ℝ)*(2*Real.pi) ≤ θ := by
  let C := (tailRadix t j).val
  let c : ℝ := C
  let l := Real.log c
  let τ := Real.pi/l
  let g := 2*l-Real.log (c+1)
  have h₂ : 2 ≤ C := radix_gt_one t j
  have hc : (2:ℝ) ≤ c := show ((2:ℕ):ℝ) ≤ (C:ℝ) from Nat.cast_le.mpr h₂
  have hc₀ : 0 < c := by linarith only [hc]
  have hc₁ : 0 < c+1 := by linarith only [hc]
  have hl : 0 < l := Real.log_pos (by linarith only [hc])
  have hτ : 0 < τ := div_pos Real.pi_pos hl
  have hg₀ : 0 ≤ g := by
    have h := Real.log_le_log hc₁ (show c+1 ≤ c^2 by nlinarith only [hc,sq_nonneg (c-2)])
    rw [Real.log_pow] at h
    change 0 ≤ 2*Real.log c-Real.log (c+1)
    exact sub_nonneg.mpr h
  have hg : g < l := by
    have h := Real.log_lt_log hc₀ (show c < c+1 by linarith)
    change 2*Real.log c-Real.log (c+1) < Real.log c
    linarith only [h]
  have hπ : τ*l = Real.pi := div_mul_cancel₀ _ hl.ne'
  refine ⟨τ*g,mul_nonneg hτ.le hg₀,(mul_lt_mul_of_pos_left hg hτ).trans_eq hπ,?_⟩
  intro x
  obtain ⟨k,hk,hcap⟩ := balanced_label_band t j x
  let n := x.val.val
  have hn : (0:ℝ) < n := by exact_mod_cast x.property
  have hpow : 0 < (c^2)^k := pow_pos (sq_pos_of_pos hc₀) _
  have hr₁ : (c^2)^k ≤ (n:ℝ) := by
    have h : (((C^2)^k:ℕ):ℝ) ≤ (n:ℝ) := Nat.cast_le.mpr hk
    simpa only [Nat.cast_pow] using h
  have hr₂ : (c+1)*(n:ℝ) < c^2*(c^2)^k := by
    have h : (((C+1)*n:ℕ):ℝ) < ((C^2*(C^2)^k:ℕ):ℝ) := Nat.cast_lt.mpr hcap
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using h
  have hlow := Real.log_le_log hpow hr₁
  have hupp := Real.log_lt_log (mul_pos hc₁ hn) hr₂
  rw [Real.log_mul hc₁.ne' hn.ne',Real.log_mul (sq_pos_of_pos hc₀).ne' hpow.ne'] at hupp
  simp only [Real.log_pow,Nat.cast_ofNat] at hlow hupp
  change (k:ℝ)*(2*l) ≤ Real.log n at hlow
  change Real.log (c+1)+Real.log n < 2*l+(k:ℝ)*(2*l) at hupp
  have ha := mul_le_mul_of_nonneg_left hlow hτ.le
  have hb := mul_le_mul_of_nonneg_left (show Real.log n ≤ (k:ℝ)*(2*l)+g by
    dsimp only [g]; linarith only [hupp]) hτ.le
  refine ⟨k,?_,?_⟩
  · change 0 ≤ τ*Real.log n-k*(2*Real.pi)
    rw [← hπ]
    linarith only [ha]
  · change τ*Real.log n-k*(2*Real.pi) ≤ τ*g
    rw [← hπ]
    linarith only [hb]

#print axioms balanced_clock_arc
#print axioms balanced_cutoff_gap
#print axioms balanced_label_band

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
