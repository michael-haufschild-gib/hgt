import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWeightsPreserveHarmonicGapRows

/-!
# The full nonpolar center retains its arithmetic receiving charge

Terminal Lipschitz weights preserve cancellation in each harmonic gap
row. The center kernels therefore vanish after horizon normalization;
the harmonic pole product retains the von Mangoldt charge.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence
open ArithmeticFunction (vonMangoldt)

/-- Independent shifts of a terminal weight and a mean-zero periodic sequence cost one
bounded-variation constant, uniformly over all subhorizons. -/
theorem abs_terminal_shifted_periodic_zero_mean_le
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    (hz : periodicMean p q = 0) {B : ℝ} (hB : ∀ n, |p n| ≤ B)
    {J N : ℕ} (hN : 1 ≤ N) (hJN : J ≤ N) (s t : ℕ) :
    |∑ n ∈ Icc 1 J, F (((n + s : ℕ) : ℝ) / N) * p (n + t)| ≤
      2 * q * B * (BF + LF) := by
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp only [Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty, abs_zero]
    positivity
  have hpt : ∀ n, p (n + q + t) = p (n + t) := fun n => by
    rw [show n + q + t = n + t + q by omega, hp]
  have hzt : periodicMean (fun n => p (n + t)) q = 0 := by
    have hs : (∑ n ∈ range q, p (n + t)) = ∑ n ∈ range q, p n := by
      rw [show (∑ n ∈ range q, p (n + t)) = ∑ n ∈ range q, p (t + n) by
        exact sum_congr rfl fun n _ => by rw [Nat.add_comm n t]]
      exact sum_range_shift_of_periodic hp t
    rw [periodicMean, hs]
    exact hz
  have hshift : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F (x + s / N) - F (y + s / N)| ≤ LF * |x - y| := by
    intro x _ y _
    simpa only [add_sub_add_right_eq_sub] using hFL (x + s / N) (y + s / N)
  have hb := abs_sum_range_terminal_weight_sub_mean_le
    (F := fun x => F (x + s / N)) (p := fun n => p (n + t))
    (fun x => hF _) hLF hshift hq hpt (fun n => hB _)
    (a := 1) (M := J - 1) hN (by omega)
  rw [hzt, zero_mul, sub_zero, Nat.sub_add_cancel hJ] at hb
  have heq : (∑ i ∈ range J, F (((1 + i : ℕ) : ℝ) / N + s / N) * p (1 + i + t)) =
      ∑ n ∈ Icc 1 J, F (((n + s : ℕ) : ℝ) / N) * p (n + t) := by
    rw [← sum_range_succ_eq_sum_Icc (fun n => F (((n + s : ℕ) : ℝ) / N) * p (n + t))]
    apply sum_congr rfl
    intro i _
    rw [Nat.add_comm 1 i, ← add_div, ← Nat.cast_add]
  rwa [heq] at hb

/-- The full difference kernel against a terminal weight and a nonpolar periodic sequence
has only harmonic growth. -/
theorem abs_terminal_diffPairSum_le
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    (hz : periodicMean p q = 0) {B : ℝ} (hB : ∀ n, |p n| ≤ B)
    {N : ℕ} (hN : 1 ≤ N) :
    |diffPairSum (fun n => F ((n : ℝ) / N)) p N| ≤
      (4 * q * B * (BF + LF)) * harmonic N := by
  rw [diffPairSum_eq, harmonic_eq_sum_Icc_real, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro j hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  have h₁ := abs_terminal_shifted_periodic_zero_mean_le hF hLF hFL hq hp hz hB
    hN (Nat.sub_le N j) 0 j
  have h₂ := abs_terminal_shifted_periodic_zero_mean_le hF hLF hFL hq hp hz hB
    hN (Nat.sub_le N j) j 0
  simp only [Nat.add_zero] at h₁ h₂
  rw [sum_add_distrib, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / j)]
  have hb := (abs_add_le _ _).trans (add_le_add h₁ h₂)
  exact (mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 1 / j)).trans_eq (by ring)

/-- Both full harmonic center kernels vanish against a terminal weight and a fixed
nonpolar Ramanujan conductor. -/
theorem tendsto_terminal_nonpolar_center_kernels
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|) {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun N : ℕ => diffPairSum (fun n => F ((n : ℝ) / N))
      (ramanujanLagCoefficient m) N / N) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => sumPairSum (fun n => F ((n : ℝ) / N))
      (ramanujanLagCoefficient m) N / N) atTop (𝓝 0) := by
  let B : ℝ := ∑ d ∈ m.divisors, (d : ℝ)
  have hp : ∀ n, ramanujanLagCoefficient m (n + m) = ramanujanLagCoefficient m n :=
    fun n => by simpa only [mul_one] using ramanujanLagCoefficient_add_mul m n 1
  have hz : periodicMean (ramanujanLagCoefficient m) m = 0 := by
    rw [periodicMean, sum_range_ramanujanLagCoefficient (by omega), if_neg (by omega), zero_div]
  constructor
  · have hlim := tendsto_harmonic_div_self.const_mul (4 * m * B * (BF + LF))
    simp only [mul_zero] at hlim
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact (div_le_div_of_nonneg_right
      (abs_terminal_diffPairSum_le hF hLF hFL (by omega : 0 < m) hp hz
        (abs_ramanujanLagCoefficient_le m) hN) (Nat.cast_nonneg N)).trans_eq (by ring)
  · have hlim := tendsto_harmonic_div_self.const_mul (BF * ((2 * m + 1) * B + B))
    simp only [mul_zero] at hlim
    apply squeeze_zero_norm
      (fun N => ?_) hlim
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact (div_le_div_of_nonneg_right
      (abs_sumPairSum_le (fun n => F ((n : ℝ) / N)) (ramanujanLagCoefficient m)
        (abs_lagSum_one_add_le hm) (fun n => hF _) (abs_ramanujanLagCoefficient_le m) N)
      (Nat.cast_nonneg N)).trans_eq (by ring)

private theorem sum_terminal_centerKernel_eq (F : ℝ → ℝ) (m N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      F ((n : ℝ) / N) * ramanujanLagCoefficient m j * centerKernel n j) =
    (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n) * lagSum m N +
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N)) * lagHarmonic m N -
      1 / 2 * diffPairSum (fun n => F ((n : ℝ) / N)) (ramanujanLagCoefficient m) N -
      1 / 2 * sumPairSum (fun n => F ((n : ℝ) / N)) (ramanujanLagCoefficient m) N := by
  unfold lagHarmonic lagSum diffPairSum sumPairSum
  rw [sum_mul_sum, sum_mul_sum, mul_sum, mul_sum,
    ← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  unfold centerKernel
  split_ifs <;> ring

/-- The full nonpolar center retains precisely the harmonic von Mangoldt receiving charge. -/
theorem tendsto_terminal_nonpolar_centerKernel_mean
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|) {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      F ((n : ℝ) / N) * ramanujanLagCoefficient m j * centerKernel n j) / N)
      atTop (𝓝 (-vonMangoldt m * ∫ x in (0 : ℝ)..1, F x)) := by
  let B : ℝ := (2 * m + 1) * ∑ d ∈ m.divisors, (d : ℝ)
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hsmall : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n) * lagSum m N / N) atTop (𝓝 0) := by
    have hlim := tendsto_harmonic_div_self.const_mul (BF * B)
    simp only [mul_zero] at hlim
    apply squeeze_zero_norm (fun N => ?_) hlim
    have hs : |∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n| ≤ BF * harmonic N := by
      rw [harmonic_eq_sum_Icc_real, mul_sum]
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro n hn
      rw [abs_div, Nat.abs_cast]
      exact (div_le_div_of_nonneg_right (hF _) (Nat.cast_nonneg n)).trans_eq (by ring)
    rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul hs (abs_lagSum_le hm N) (abs_nonneg _) ((abs_nonneg _).trans hs))
      (Nat.cast_nonneg N)).trans_eq (by dsimp only [B]; ring)
  have hmean := tendsto_weighted_riemannSum (w := fun _ : ℕ => (1 : ℝ))
    (M := 1) (W := 1) (by norm_num) (by intros; rfl) (by intros; norm_num)
    (fun x _ y _ => hFL x y) (fun x _ => hF x) 0
  simp only [Nat.sub_zero, one_mul, sum_range_one, Nat.cast_one, div_one] at hmean
  obtain ⟨hdiff, hsum⟩ := tendsto_terminal_nonpolar_center_kernels hF hLF hFL hm
  have ht := ((hsmall.add (hmean.mul (tendsto_lagHarmonic hm))).sub
    (hdiff.const_mul (1 / 2))).sub (hsum.const_mul (1 / 2))
  simp only [zero_add, mul_zero, sub_zero] at ht
  rw [mul_comm (∫ x in (0 : ℝ)..1, F x)] at ht
  apply ht.congr
  intro N
  rw [sum_terminal_centerKernel_eq]
  ring

/-- The literal pole and archimedean center pairing has the same nonpolar receiving charge. -/
theorem tendsto_terminal_fullNonpolarCenter_pair
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|) {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n *
      ∑ j ∈ Icc 1 N,
        (arithmeticPoleKernel n j - archimedeanCenterKernel n j) *
          (ramanujanLagCoefficient m j / Real.sqrt j)) / N)
      atTop (𝓝 (-vonMangoldt m * ∫ x in (0 : ℝ)..1, F x)) := by
  apply (tendsto_terminal_nonpolar_centerKernel_mean hF hLF hFL hm).congr
  intro N
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [← centerKernel_eq (mem_Icc.mp hn).1 (mem_Icc.mp hj).1]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_nonpolar_center_kernels
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_fullNonpolarCenter_pair
