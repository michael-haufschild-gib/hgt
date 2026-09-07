import GaloisForLFunctions.RHTower.DivisorHyperbolaSharpBlocks
import GaloisForLFunctions.RHTower.DivisorHyperbolaSmallPrefixes
import GaloisForLFunctions.RHTower.DivisorHyperbolaPositivePrefix

/-!
# All-cutoff orientation of the literal divisor source

Sharp smooth square-block mass exactly covers the complete centered-prefix
allowance. The analytic initial interval closes every ordinary prefix; floor
repetition and decreasing half-order Abel summation then orient every unsigned
dilation channel. No signed aggregate cancellation is assumed or concluded.
-/

noncomputable section
open Finset
namespace RHTower

private theorem smooth_square_prefix_sharp {s : ℕ} (hs : 5 ≤ s) :
    ((s:ℝ)*(s+1)-2)/8 ≤ ∑ k ∈ Ico 1 (s*s), divisorHyperbolaSmoothRemainder k := by
  induction s,hs using Nat.le_induction with
  | base =>
    rw [show (5:ℕ)*5=24+1 by norm_num,Ico_add_one_right_eq_Icc]
    norm_num only [Nat.cast_ofNat]
    exact sum_divisorHyperbolaSmoothRemainder_twentyFour_ge
  | succ s hs ih =>
    have hblock := sum_divisorHyperbolaSmoothRemainder_square_block_ge_sharp hs
    rw [← sum_Ico_consecutive (show 1 ≤ s*s by nlinarith)
      (show s*s ≤ (s+1)*(s+1) by nlinarith) (f := divisorHyperbolaSmoothRemainder)]
    push_cast
    nlinarith only [ih,hblock]

/-- Sharp smooth-prefix allowance, including every terminal partial square block. -/
theorem sum_divisorHyperbolaSmoothRemainder_ge_sharp {N : ℕ} (hN : 25 ≤ N) :
    ((Nat.sqrt N:ℝ)*(Nat.sqrt N+1)-2)/8 ≤
      ∑ k ∈ Icc 1 N, divisorHyperbolaSmoothRemainder k := by
  let s := Nat.sqrt N
  have hs : 5 ≤ s := Nat.le_sqrt.mpr hN
  have hsN : s*s ≤ N := Nat.sqrt_le N
  have hpref := smooth_square_prefix_sharp hs
  have htail : 0 ≤ ∑ k ∈ Ico (s*s) (N+1), divisorHyperbolaSmoothRemainder k := by
    apply sum_nonneg
    intro k hk
    have hk' := (mem_Ico.mp hk).1
    exact divisorHyperbolaSmoothRemainder_nonneg_of_twentyFive (by nlinarith)
  rw [← Ico_add_one_right_eq_Icc,← sum_Ico_consecutive (show 1 ≤ s*s by nlinarith)
    (show s*s ≤ N+1 by omega) (f := divisorHyperbolaSmoothRemainder)]
  exact hpref.trans (le_add_of_nonneg_right htail)

/-- Removing the identically zero modulus-one channel sharpens the centered-prefix floor. -/
theorem sum_centeredDivisorHyperbola_ge_sharp {N : ℕ} (hN : 1 ≤ N) :
    -((Nat.sqrt N:ℝ)*(Nat.sqrt N+1)-2)/16 ≤
      ∑ k ∈ Icc 1 N, centeredDivisorHyperbola k := by
  rw [sum_centeredDivisorHyperbola_eq_primitives]
  have hbound (s : ℕ) (hs : 1 ≤ s) :
      -((s:ℝ)*(s+1)-2)/16 ≤ ∑ d ∈ Icc 1 s, HTGeometry.centeredModularPrimitive d (N+1) := by
    induction s,hs using Nat.le_induction with
    | base => norm_num [HTGeometry.centeredModularPrimitive,Nat.mod_one]
    | succ s hs ih =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ s+1)]
      have h := (HTGeometry.centeredModularPrimitive_bounds (s+1) (N+1)).1
      push_cast at h ⊢
      nlinarith only [ih,h]
  exact hbound _ (Nat.le_sqrt.mpr (by simpa using hN))

/-- Every ordinary prefix of the literal divisor defect is nonnegative, unconditionally. -/
theorem sum_primeFreeDivisorDefect_nonneg (N : ℕ) :
    0 ≤ ∑ k ∈ Icc 1 N, primeFreeDivisorDefect k := by
  by_cases hN : N ≤ 24
  · exact sum_primeFreeDivisorDefect_nonneg_of_le_twentyFour hN
  have hR := sum_divisorHyperbolaSmoothRemainder_ge_sharp (by omega : 25 ≤ N)
  have hE := sum_centeredDivisorHyperbola_ge_sharp (by omega : 1 ≤ N)
  have hsplit : (∑ k ∈ Icc 1 N, primeFreeDivisorDefect k) =
      (∑ k ∈ Icc 1 N, divisorHyperbolaSmoothRemainder k)+
        2*∑ k ∈ Icc 1 N, centeredDivisorHyperbola k := by
    rw [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    simpa only [primeFreeDivisorDefect,mul_comm] using (divisorHyperbolaSmooth_add_centered k).symm
  rw [hsplit]
  linarith only [hR,hE]

private theorem sum_range_integer_blocks_orientation (d q : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ range (d*q), f k) = ∑ j ∈ range q, ∑ i ∈ range d, f (d*j+i) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ,sum_range_add,ih,Finset.sum_range_succ]

private theorem sum_range_floor_nonneg (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ ∑ k ∈ range n, f k)
    {d : ℕ} (hd : 0 < d) (N : ℕ) :
    0 ≤ ∑ k ∈ range N, f (k/d) := by
  let q := N/d
  let r := N%d
  have hr : r < d := Nat.mod_lt N hd
  have hN : N=d*q+r := (Nat.div_add_mod N d).symm
  have hwhole : (∑ k ∈ range (d*q), f (k/d)) = (d:ℝ)*∑ j ∈ range q, f j := by
    rw [sum_range_integer_blocks_orientation]
    have hblock (j : ℕ) : (∑ i ∈ range d, f ((d*j+i)/d)) = (d:ℝ)*f j := by
      have hdiv (i : ℕ) (hi : i ∈ range d) : (d*j+i)/d=j := by
        rw [Nat.mul_add_div hd,Nat.div_eq_of_lt (mem_range.mp hi),Nat.add_zero]
      calc
        _ = ∑ i ∈ range d, f j := sum_congr rfl (fun i hi => by rw [hdiv i hi])
        _ = _ := by simp
    simp_rw [hblock]
    rw [mul_sum]
  have hpartial : (∑ i ∈ range r, f ((d*q+i)/d))=(r:ℝ)*f q := by
    have hdiv (i : ℕ) (hi : i ∈ range r) : (d*q+i)/d=q := by
      rw [Nat.mul_add_div hd,Nat.div_eq_of_lt ((mem_range.mp hi).trans hr),Nat.add_zero]
    calc
      _ = ∑ i ∈ range r, f q := sum_congr rfl (fun i hi => by rw [hdiv i hi])
      _ = _ := by simp
  have hid : (∑ k ∈ range N, f (k/d)) =
      ((d-r:ℕ):ℝ)*(∑ j ∈ range q, f j)+(r:ℝ)*(∑ j ∈ range (q+1), f j) := by
    conv_lhs => rw [hN,sum_range_add]
    rw [hwhole,hpartial,Finset.sum_range_succ,Nat.cast_sub hr.le]
    ring
  rw [hid]
  exact add_nonneg (mul_nonneg (by positivity) (hf q)) (mul_nonneg (by positivity) (hf (q+1)))

/-- Floor repetition preserves all nonnegative ordinary prefixes of the literal source. -/
theorem sum_primeFreeDivisorDefect_floor_nonneg (N d : ℕ) :
    0 ≤ ∑ k ∈ Icc 1 N, primeFreeDivisorDefect (k/d) := by
  have hD0 : primeFreeDivisorDefect 0=0 := by simp [primeFreeDivisorDefect]
  by_cases hd : d=0
  · simp [hd,hD0]
  have hpref (n : ℕ) : 0 ≤ ∑ k ∈ range n, primeFreeDivisorDefect k := by
    cases n with
    | zero => simp
    | succ n =>
      have heq : (∑ k ∈ range (n+1), primeFreeDivisorDefect k) =
          ∑ k ∈ Icc 1 n, primeFreeDivisorDefect k := by
        rw [← Ico_add_one_right_eq_Icc,sum_Ico_eq_sub _ (by omega : 1 ≤ n+1)]
        simp [hD0]
      rw [heq]
      exact sum_primeFreeDivisorDefect_nonneg n
  rw [← Ico_add_one_right_eq_Icc,sum_Ico_eq_sub _ (by omega : 1 ≤ N+1)]
  simp only [sum_range_one,Nat.zero_div,hD0,sub_zero]
  exact sum_range_floor_nonneg _ hpref (by omega : 0<d) (N+1)

/-- Every literal unsigned half-order dilation channel is nonnegative at every cutoff. -/
theorem divisorUnsignedDilationChannel_nonneg (M d : ℕ) :
    0 ≤ divisorUnsignedDilationChannel M d := by
  have hD0 : primeFreeDivisorDefect 0=0 := by simp [primeFreeDivisorDefect]
  by_cases hd : d=0
  · simp [divisorUnsignedDilationChannel,hd,hD0]
  by_cases hM : M ≤ 1
  · simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : M-1 < d)]
  let w := HTGeometry.halfOrderAbelStep 0
  have hpos : 0 ≤ ∑ k ∈ Icc 1 (M-1), primeFreeDivisorDefect (k/d)*w k := by
    rw [HTGeometry.sum_mul_eq_partial_mul_diff_ring]
    apply add_nonneg
    · apply sum_nonneg
      intro k hk
      exact mul_nonneg (sum_primeFreeDivisorDefect_floor_nonneg k d)
        (sub_nonneg.mpr (HTGeometry.halfOrderAbelStep_antitone 0 (show k ≤ k+1 by omega)))
    · exact mul_nonneg (sum_primeFreeDivisorDefect_floor_nonneg (M-1) d)
        (HTGeometry.halfOrderAbelStep_nonneg 0 (M-1+1))
  have heq : (∑ k ∈ Icc 1 (M-1), primeFreeDivisorDefect (k/d)*w k)=divisorUnsignedDilationChannel M d := by
    unfold divisorUnsignedDilationChannel
    have hsub : Icc d (M-1) ⊆ Icc 1 (M-1) := by
      intro k hk
      exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hk).1; omega,(mem_Icc.mp hk).2⟩
    symm
    calc
      _ = ∑ k ∈ Icc d (M-1), primeFreeDivisorDefect (k/d)*w k := by
        apply sum_congr rfl
        intro k _
        simp only [w,HTGeometry.halfOrderAbelStep,Nat.zero_add]
        ring
      _ = _ := sum_subset hsub (by
        intro k hk hkd
        have hlt : k<d := by have := mem_Icc.mp hk; simp only [mem_Icc] at hkd; omega
        rw [Nat.div_eq_of_lt hlt,hD0,zero_mul])
  rwa [heq] at hpos

end RHTower
