import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper

/-!
# Complete-source obstruction to monotone-weight diagonal dominance

The literal prime-free divisor source does not supply diagonal dominance for arbitrary
nonnegative decreasing time weights. At endpoint seven, flat weights give a strictly
positive source-square-minus-diagonal gap. Continuity preserves that failure for some
positive strictly decreasing geometric weights.

The proof evaluates the finite arithmetic source symbolically and uses analytic bounds
for logarithms and Euler's constant. No experimental result is a proof input. The exact
prefix-mixture identity survives the failed inequality, and the half-order instance is
identified with the existing Möbius dilation channel. Neither the half-order sign nor RH
is asserted.
-/

noncomputable section
open Finset
namespace RHTower

def mobiusDivisorTimeChannel (M : ℕ) (w : ℕ → ℝ) (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    ∑ k ∈ Icc 1 (M-1), w k * primeFreeDivisorDefect (k/d)

private theorem defect_zero : primeFreeDivisorDefect 0 = 0 := by
  simp [primeFreeDivisorDefect]

private theorem defect_small :
    primeFreeDivisorDefect 1 = 2*Real.eulerMascheroniConstant-1 ∧
    primeFreeDivisorDefect 2 = Real.log 2-3+4*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 3 = Real.log 2+Real.log 3-5+6*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 4 = 3*Real.log 2+Real.log 3-8+8*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 5 = 3*Real.log 2+Real.log 3+Real.log 5-10+10*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 6 = 4*Real.log 2+2*Real.log 3+Real.log 5-14+12*Real.eulerMascheroniConstant := by
  have h4 : Real.log 4 = 2*Real.log 2 := Real.log_four_eq
  have h6 : Real.log 6 = Real.log 2+Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    norm_num
  norm_num [primeFreeDivisorDefect, Finset.sum_Icc_succ_top, h4,h6]
  all_goals ring_nf
  all_goals trivial


/-- Exact prefix-mixture representation for every arithmetic time-weighted channel. -/
theorem mobiusDivisorTimeChannel_eq_prefix_mixture (M d : ℕ) (w : ℕ → ℝ) :
    mobiusDivisorTimeChannel M w d =
      (∑ t ∈ Icc 1 (M-1), mobiusDivisorTimeChannel (t+1) (fun _ => 1) d *
        (w t-w (t+1))) + mobiusDivisorTimeChannel M (fun _ => 1) d * w M := by
  have h := HTGeometry.sum_mul_eq_partial_mul_diff_ring
    (fun k => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (k/d)) w (M-1)
  by_cases hM : M=0
  · subst M; simp [mobiusDivisorTimeChannel]
  · have hp : M-1+1=M := by omega
    simpa only [mobiusDivisorTimeChannel, Nat.add_sub_cancel, one_mul,
      Finset.mul_sum, hp, mul_comm, mul_left_comm, mul_assoc] using h

private theorem flat_six_channels :
    mobiusDivisorTimeChannel 7 (fun _ => 1) 1 =
      12*Real.log 2+5*Real.log 3+2*Real.log 5-41+42*Real.eulerMascheroniConstant ∧
    mobiusDivisorTimeChannel 7 (fun _ => 1) 2 =
      13-18*Real.eulerMascheroniConstant-3*Real.log 2-Real.log 3 ∧
    mobiusDivisorTimeChannel 7 (fun _ => 1) 3 =
      6-10*Real.eulerMascheroniConstant-Real.log 2 ∧
    mobiusDivisorTimeChannel 7 (fun _ => 1) 4 = 0 ∧
    mobiusDivisorTimeChannel 7 (fun _ => 1) 5 = 2-4*Real.eulerMascheroniConstant ∧
    mobiusDivisorTimeChannel 7 (fun _ => 1) 6 = 2*Real.eulerMascheroniConstant-1 ∧
    mobiusDivisorTimeChannel 7 (fun _ => 1) 7 = 0 := by
  have h2 := ArithmeticFunction.moebius_apply_prime (Nat.prime_two)
  have h3 := ArithmeticFunction.moebius_apply_prime (Nat.prime_three)
  have h5 := ArithmeticFunction.moebius_apply_prime (Nat.prime_five)
  have h4 : ArithmeticFunction.moebius 4 = 0 := by
    simpa using (ArithmeticFunction.moebius_apply_prime_pow (Nat.prime_two)
      (show (2:ℕ) ≠ 0 by norm_num))
  have h6 : ArithmeticFunction.moebius 6 = 1 := by
    simpa [h2,h3] using ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (show Nat.gcd 2 3 = 1 by rfl)
  obtain ⟨hd1,hd2,hd3,hd4,hd5,hd6⟩ := defect_small
  norm_num [mobiusDivisorTimeChannel,Finset.sum_Icc_succ_top,defect_zero,
    hd1,hd2,hd3,hd4,hd5,hd6,h2,h3,h4,h5,h6]
  all_goals ring_nf
  all_goals trivial

private theorem gamma_lower : (0.545 : ℝ) < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 15
  unfold Real.eulerMascheroniSeq at h
  have hh : ((harmonic 15 : ℚ) : ℝ) = 1195757 / 360360 := by
    norm_num [harmonic_succ, harmonic_zero]
  have hl : Real.log ((15 : ℕ) + 1 : ℝ) = 4 * Real.log 2 := by
    rw [show ((15 : ℕ) + 1 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [hh,hl] at h
  linarith [Real.log_two_lt_d9]

private def sixGap (g a b c : ℝ) : ℝ :=
  (8*a+4*b+2*c-21+12*g)^(2 : ℕ) - (12*a+5*b+2*c-41+42*g)^(2 : ℕ) -
    (13-18*g-3*a-b)^(2 : ℕ) - (6-10*g-a)^(2 : ℕ) - (2-4*g)^(2 : ℕ) - (2*g-1)^(2 : ℕ)

private theorem sixGap_center_lower {g : ℝ} (hlo : 545/1000 ≤ g)
    (hhi : g ≤ 577216/1000000) :
    1/10 < sixGap g (693147/1000000) (1098612/1000000) (1609438/1000000) := by
  have hprod := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  unfold sixGap
  nlinarith

private theorem square_error_bound {x y : ℝ} (hxy : |x-y| ≤ 1/10000) (hy : |y| ≤ 2) :
    |x^(2 : ℕ)-y^(2 : ℕ)| ≤ 1/1000 := by
  have hxb := (abs_le.mp hxy)
  have hyb := (abs_le.mp hy)
  have hsum : |x+y| ≤ 5 := by apply abs_le.mpr; constructor <;> linarith
  calc
    _ = |x-y| * |x+y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (1/10000 : ℝ) * 5 := mul_le_mul hxy hsum (abs_nonneg _) (by norm_num)
    _ ≤ _ := by norm_num

private theorem sixGap_actual_pos :
    0 < sixGap Real.eulerMascheroniConstant (Real.log 2) (Real.log 3) (Real.log 5) := by
  let g := Real.eulerMascheroniConstant
  let a := Real.log 2
  let b := Real.log 3
  let c := Real.log 5
  have hglo : 545/1000 ≤ g := by dsimp [g]; linarith [gamma_lower]
  have hghi : g ≤ 577216/1000000 :=
    eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion.le
  have ha : 693146/1000000 ≤ a ∧ a ≤ 693148/1000000 := by
    dsimp [a]; constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have hb : 1098611/1000000 ≤ b ∧ b ≤ 1098613/1000000 := by
    dsimp [b]; constructor <;> linarith [Real.log_three_gt_d9, Real.log_three_lt_d9]
  have hc : 1609437/1000000 ≤ c ∧ c ≤ 1609439/1000000 := by
    dsimp [c]; constructor <;> linarith [Real.log_five_gt_d9, Real.log_five_lt_d9]
  have hS := square_error_bound
    (x := 8*a+4*b+2*c-21+12*g)
    (y := 8*(693147/1000000)+4*(1098612/1000000)+2*(1609438/1000000)-21+12*g)
    (by apply abs_le.mpr; constructor <;> linarith [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2])
    (by apply abs_le.mpr; constructor <;> linarith)
  have hA := square_error_bound
    (x := 12*a+5*b+2*c-41+42*g)
    (y := 12*(693147/1000000)+5*(1098612/1000000)+2*(1609438/1000000)-41+42*g)
    (by apply abs_le.mpr; constructor <;> linarith [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2])
    (by apply abs_le.mpr; constructor <;> linarith)
  have hB := square_error_bound
    (x := 13-18*g-3*a-b)
    (y := 13-18*g-3*(693147/1000000)-(1098612/1000000))
    (by apply abs_le.mpr; constructor <;> linarith [ha.1,ha.2,hb.1,hb.2])
    (by apply abs_le.mpr; constructor <;> linarith)
  have hC := square_error_bound
    (x := 6-10*g-a) (y := 6-10*g-(693147/1000000))
    (by apply abs_le.mpr; constructor <;> linarith [ha.1,ha.2])
    (by apply abs_le.mpr; constructor <;> linarith)
  have hbase := sixGap_center_lower hglo hghi
  change 0 < sixGap g a b c
  unfold sixGap at hbase ⊢
  linarith [(abs_le.mp hS).1,(abs_le.mp hA).2,(abs_le.mp hB).2,(abs_le.mp hC).2]

/-- The half-order instance is the existing literal floor-dilation channel. -/
theorem mobiusDivisorTimeChannel_sqrt (M d : ℕ) :
    mobiusDivisorTimeChannel M
      (fun k => Real.sqrt (k+1 : ℕ)-Real.sqrt k) d = mobiusDivisorDilationChannel M d := by
  by_cases hd : d=0
  · subst d
    simp [mobiusDivisorTimeChannel,mobiusDivisorDilationChannel]
  · unfold mobiusDivisorTimeChannel mobiusDivisorDilationChannel
    congr 1
    symm
    apply Finset.sum_subset
    · intro k hk
      exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hk).1; omega, (mem_Icc.mp hk).2⟩
    · intro k hk hnot
      have hkd : k < d := by
        have := (mem_Icc.mp hk).2
        simp only [mem_Icc,not_and] at hnot
        omega
      rw [Nat.div_eq_of_lt hkd,defect_zero,mul_zero]

/-- Source square minus diagonal energy, with the complete finite arithmetic channels. -/
def mobiusDivisorTimeGap (M : ℕ) (w : ℕ → ℝ) : ℝ :=
  (∑ d ∈ Icc 1 M, mobiusDivisorTimeChannel M w d)^(2 : ℕ) -
    ∑ d ∈ Icc 1 M, (mobiusDivisorTimeChannel M w d)^(2 : ℕ)

/-- Ordinary nonnegative decreasing time weights do not produce diagonal dominance. -/
theorem mobiusDivisorTimeGap_flat_seven_pos :
    0 < mobiusDivisorTimeGap 7 (fun _ => 1) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := flat_six_channels
  have heq : mobiusDivisorTimeGap 7 (fun _ => 1) =
      sixGap Real.eulerMascheroniConstant (Real.log 2) (Real.log 3) (Real.log 5) := by
    norm_num [mobiusDivisorTimeGap, Finset.sum_Icc_succ_top,h1,h2,h3,h4,h5,h6,h7,sixGap]
    ring
  rw [heq]
  exact sixGap_actual_pos

/-- Failure persists for some positive strictly decreasing geometric kernel. -/
theorem mobiusDivisorTimeGap_geometric_counterexample :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ StrictAnti (fun k : ℕ => q^k) ∧
      (∀ k : ℕ, 0 < q^k) ∧ 0 < mobiusDivisorTimeGap 7 (fun k => q^k) := by
  have hcont : Continuous (fun q : ℝ => mobiusDivisorTimeGap 7 (fun k => q^k)) := by
    unfold mobiusDivisorTimeGap mobiusDivisorTimeChannel
    fun_prop
  have hopen := isOpen_lt (f := fun _ : ℝ => 0) continuous_const hcont
  have hmem : (1:ℝ) ∈ {q | 0 < mobiusDivisorTimeGap 7 (fun k => q^k)} := by
    simpa using mobiusDivisorTimeGap_flat_seven_pos
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen 1 hmem
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  let q : ℝ := 1-δ/2
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  refine ⟨q,hq0,hq1,pow_right_strictAnti₀ hq0 hq1,fun k => pow_pos hq0 k,?_⟩
  apply hball
  rw [Metric.mem_ball,Real.dist_eq]
  apply abs_lt.mpr
  dsimp [q]
  constructor <;> linarith
end RHTower
