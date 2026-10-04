import GaloisForLFunctions.RHTower.CCMPrimeDeficitCompletePole
import GaloisForLFunctions.RHTower.CCMPrimeDeficitCoefficientAction
import GaloisForLFunctions.RHTower.CCMPrimeDeficitDilationUniformBound

/-!
# Diffuse harmonic-neutral reconstruction of the actual prime deficit

The literal Möbius head through N is extended on N<n<=2N by
`-(n/N) * sum_(k<=N) mu(k)/k`. Its full harmonic moment is zero, with
no concentrated tail coefficient. At the square-root cutoff its actual
stationary action remains the original prime-deficit primitive.

Complete pole subtraction gives `D = linearWork - quadraticWork` with
all negative-time and mixed-label terms retained. The entire linear
channel and absolute diagonal have unconditional critical-scale
polynomial budgets. No bound for the full signed quadratic work is
claimed; its unequal-label correlations remain the arithmetic gap.
-/

noncomputable section
open scoped BigOperators
namespace RHTower

private def headHarmonic (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, moebiusCoeff n / n

/-- The literal Möbius head, completed by a diffuse harmonic correction
on the next block. Every tail coefficient is at most twice the head's
harmonic mass in absolute value. -/
def ccmPrimeDeficitNeutralCoefficient (N n : ℕ) : ℝ :=
  logarithmicMobiusHeadExtension N
    (fun n => if n ≤ 2 * N then -(n : ℝ) / N * headHarmonic N else 0) n

private theorem neutral_head {N n : ℕ} (hn : n ≤ N) :
    ccmPrimeDeficitNeutralCoefficient N n = moebiusCoeff n := by
  simp only [ccmPrimeDeficitNeutralCoefficient, logarithmicMobiusHeadExtension, if_pos hn]
  rfl

private theorem neutral_tail {N n : ℕ} (hn : N < n) (hn2 : n ≤ 2 * N) :
    ccmPrimeDeficitNeutralCoefficient N n = -(n : ℝ) / N * headHarmonic N := by
  simp [ccmPrimeDeficitNeutralCoefficient, logarithmicMobiusHeadExtension, not_le.mpr hn, hn2]

private theorem neutral_support {N n : ℕ} (hn : 2 * N < n) :
    ccmPrimeDeficitNeutralCoefficient N n = 0 := by
  simp [ccmPrimeDeficitNeutralCoefficient, logarithmicMobiusHeadExtension,
    show ¬ n ≤ N by omega, not_le.mpr hn]

private theorem split_prefix (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (2 * N), f n) =
      (∑ n ∈ Finset.Icc 1 N, f n) + ∑ n ∈ Finset.Icc (N + 1) (2 * N), f n := by
  have hs : Finset.Icc 1 (2 * N) = Finset.Icc 1 N ∪ Finset.Icc (N + 1) (2 * N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) (2 * N)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have := Finset.mem_Icc.mp hn
    have := Finset.mem_Icc.mp hm
    omega
  rw [hs, Finset.sum_union hd]

/-- The full harmonic moment vanishes exactly, with the original head
unchanged and no concentrated tail coefficient. -/
theorem ccmPrimeDeficitNeutralCoefficient_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (2 * N), ccmPrimeDeficitNeutralCoefficient N n / n) = 0 := by
  by_cases hN : N = 0
  · subst N; simp
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [split_prefix]
  have hh : (∑ n ∈ Finset.Icc 1 N, ccmPrimeDeficitNeutralCoefficient N n / n) =
      headHarmonic N := by
    unfold headHarmonic
    apply Finset.sum_congr rfl
    intro n hn
    rw [neutral_head (Finset.mem_Icc.mp hn).2]
  have ht : (∑ n ∈ Finset.Icc (N + 1) (2 * N), ccmPrimeDeficitNeutralCoefficient N n / n) =
      -headHarmonic N := by
    have hp (n : ℕ) (hn : n ∈ Finset.Icc (N + 1) (2 * N)) :
        ccmPrimeDeficitNeutralCoefficient N n / n = -headHarmonic N / N := by
      have hnN : N < n := (Finset.mem_Icc.mp hn).1
      have hnR : (n : ℝ) ≠ 0 := by
        have hnpos : 0 < n := by omega
        exact_mod_cast hnpos.ne'
      rw [neutral_tail hnN (Finset.mem_Icc.mp hn).2]
      field_simp
    rw [Finset.sum_congr rfl hp, Finset.sum_const]
    have hcard : (Finset.Icc (N + 1) (2 * N)).card = N := by rw [Nat.card_Icc]; omega
    rw [hcard]
    simp only [nsmul_eq_mul]
    field_simp
  rw [hh, ht, add_neg_cancel]

private theorem neutral_exp_moment (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (2 * N), ccmPrimeDeficitNeutralCoefficient N n *
      Real.exp (-Real.log n)) = 0 := by
  convert ccmPrimeDeficitNeutralCoefficient_harmonic N using 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [Real.exp_neg, Real.exp_log hnpos, div_eq_mul_inv]

private theorem headHarmonic_bound (N : ℕ) :
    |headHarmonic N| ≤ 1 + Real.log N := by
  have hs : (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) = (harmonic N : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  unfold headHarmonic
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, |moebiusCoeff n / n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [abs_div, abs_of_pos hnpos]
      simpa only [one_div] using div_le_div_of_nonneg_right (abs_moebiusCoeff_le_one n) hnpos.le
    _ ≤ _ := by rw [hs]; exact harmonic_le_one_add_log N

private theorem coefficient_bound {N n : ℕ} (hN : 1 ≤ N) (hn : n ∈ Finset.Icc 1 (2 * N)) :
    |ccmPrimeDeficitNeutralCoefficient N n| ≤ 2 * (1 + Real.log N) + 1 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  by_cases hnN : n ≤ N
  · rw [neutral_head hnN]
    exact (abs_moebiusCoeff_le_one n).trans (by linarith only [hlog])
  · rw [neutral_tail (Nat.lt_of_not_ge hnN) (Finset.mem_Icc.mp hn).2,
      abs_mul, abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hNR]
    have hr : (n : ℝ) / N ≤ 2 := by
      rw [div_le_iff₀ hNR]
      exact_mod_cast (Finset.mem_Icc.mp hn).2
    exact (mul_le_mul hr (headHarmonic_bound N) (abs_nonneg _) (by positivity)).trans
      (by linarith)

private theorem source_causal {t : ℝ} (ht : t < 0) : ccmPrimeDeficitDilationSource t = 0 := by
  have hf : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr ht)
  simp [ccmPrimeDeficitDilationSource, hf]

private theorem weighted_causal (a : ℕ → ℝ) (f : ℝ → ℝ) {t : ℝ} (ht : t < 0) :
    logarithmicWeightedDilation a f t = 0 := by
  have hf : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr ht)
  simp [logarithmicWeightedDilation, hf]

private theorem finite_dilation (a : ℕ → ℝ) (U : ℕ)
    (ha : ∀ n, U < n → a n = 0) (f : ℝ → ℝ) (hf : ∀ t, t < 0 → f t = 0) (T : ℝ) :
    logarithmicWeightedDilation a f T = ∑ n ∈ Finset.Icc 1 U, a n * f (T - Real.log n) := by
  unfold logarithmicWeightedDilation
  rcases le_total U ⌊Real.exp T⌋₊ with hU | hU
  · symm
    apply Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hU⟩)
    intro n hn hnU
    have hUn : U < n := by
      have hn1 := (Finset.mem_Icc.mp hn).1
      simp only [Finset.mem_Icc, hn1, true_and] at hnU
      omega
    rw [ha n hUn, zero_mul]
  · apply Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hU⟩)
    intro n hn hnT
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hneg : T - Real.log n < 0 := by
      by_contra h
      have hlog : Real.log n ≤ T := by linarith only [h]
      have hnf : n ≤ ⌊Real.exp T⌋₊ := (Nat.le_floor_iff (Real.exp_pos T).le).mpr
        ((Real.log_le_iff_le_exp hnpos).mp hlog)
      exact hnT (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, hnf⟩)
    rw [hf _ hneg, mul_zero]

private theorem neutral_dilation (N : ℕ) (f : ℝ → ℝ)
    (hf : ∀ t, t < 0 → f t = 0) (T : ℝ) :
    logarithmicWeightedDilation (ccmPrimeDeficitNeutralCoefficient N) f T =
      ∑ n ∈ Finset.Icc 1 (2 * N), ccmPrimeDeficitNeutralCoefficient N n * f (T - Real.log n) :=
  finite_dilation _ _ (fun _ => neutral_support) f hf T

private theorem neutral_double_dilation (N : ℕ) (T : ℝ) :
    logarithmicWeightedDilation (ccmPrimeDeficitNeutralCoefficient N)
      (logarithmicWeightedDilation (ccmPrimeDeficitNeutralCoefficient N)
        ccmPrimeDeficitDivisorSource) T =
      ∑ m ∈ Finset.Icc 1 (2 * N), ∑ n ∈ Finset.Icc 1 (2 * N),
        ccmPrimeDeficitNeutralCoefficient N m * ccmPrimeDeficitNeutralCoefficient N n *
          ccmPrimeDeficitDivisorSource (T - Real.log m - Real.log n) := by
  rw [neutral_dilation _ _ (fun _ => weighted_causal _ _)]
  apply Finset.sum_congr rfl
  intro m _
  rw [neutral_dilation _ _ (fun _ ht => ccmPrimeDeficitDivisorSource_of_nonpos ht.le), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- This coefficient vector is a literal head extension, so its action
is the original deficit, including every causal endpoint. -/
private theorem ccmPrimeDeficitNeutralCoefficient_action {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCoefficientAction T
      (ccmPrimeDeficitNeutralCoefficient ⌊Real.exp (T / 2)⌋₊) =
        ccmLogChebyshevDeficitPrimitive T :=
  ccmPrimeDeficitCoefficientAction_headExtension _ hT

def ccmPrimeDeficitDilationPoleRemainder (t : ℝ) : ℝ :=
  ccmPrimeDeficitDilationSource t - (Real.eulerMascheroniConstant + 1) * Real.exp t

def ccmPrimeDeficitNeutralLinearWork (T : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 (2 * ⌊Real.exp (T / 2)⌋₊),
    ccmPrimeDeficitNeutralCoefficient ⌊Real.exp (T / 2)⌋₊ n *
      ccmPrimeDeficitDilationPoleRemainder (T - Real.log n)

def ccmPrimeDeficitNeutralQuadraticWork (T : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (2 * ⌊Real.exp (T / 2)⌋₊),
    ∑ n ∈ Finset.Icc 1 (2 * ⌊Real.exp (T / 2)⌋₊),
      ccmPrimeDeficitNeutralCoefficient ⌊Real.exp (T / 2)⌋₊ m *
        ccmPrimeDeficitNeutralCoefficient ⌊Real.exp (T / 2)⌋₊ n *
          ccmPrimeDeficitDivisorPoleRemainder (T - Real.log m - Real.log n)

private theorem neutral_linear_subtraction (N : ℕ) (T : ℝ) :
    (∑ n ∈ Finset.Icc 1 (2 * N), ccmPrimeDeficitNeutralCoefficient N n *
      ccmPrimeDeficitDilationSource (T - Real.log n)) =
        ∑ n ∈ Finset.Icc 1 (2 * N), ccmPrimeDeficitNeutralCoefficient N n *
          ccmPrimeDeficitDilationPoleRemainder (T - Real.log n) := by
  have hp (n : ℕ) : ccmPrimeDeficitNeutralCoefficient N n *
      ccmPrimeDeficitDilationPoleRemainder (T - Real.log n) =
        ccmPrimeDeficitNeutralCoefficient N n * ccmPrimeDeficitDilationSource (T - Real.log n) -
          ((Real.eulerMascheroniConstant + 1) * Real.exp T) *
            (ccmPrimeDeficitNeutralCoefficient N n * Real.exp (-Real.log n)) := by
    unfold ccmPrimeDeficitDilationPoleRemainder
    rw [show Real.exp (T - Real.log n) = Real.exp T * Real.exp (-Real.log n) by
      rw [← Real.exp_add]; congr 1]
    ring
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, neutral_exp_moment, mul_zero, sub_zero]

/-- Exact source-level pole removal for the actual moving Möbius head.
The quadratic remainder retains the prescribed tail and all mixed pairs. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_neutral_work {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T =
      ccmPrimeDeficitNeutralLinearWork T - ccmPrimeDeficitNeutralQuadraticWork T := by
  rw [← ccmPrimeDeficitNeutralCoefficient_action hT]
  unfold ccmPrimeDeficitCoefficientAction logarithmicReconstructionAction
  have hH : logarithmicDilationSum ccmPrimeDeficitDilationSource = ccmPrimeDeficitDivisorSource :=
    funext logarithmicDilationSum_dilationSource_eq_divisorSource
  rw [hH, neutral_dilation _ _ (fun _ => source_causal), neutral_double_dilation,
    neutral_linear_subtraction, ccmPrimeDeficitDivisorSource_finite_pair_eq_complete_pole,
    neutral_exp_moment]
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, sub_zero, zero_add,
    ccmPrimeDeficitNeutralLinearWork, ccmPrimeDeficitNeutralQuadraticWork]

private theorem linear_source_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |ccmPrimeDeficitDilationPoleRemainder t| ≤ C * (max t 0 + 1) := by
  let c := Real.eulerMascheroniConstant + 1
  let k := Real.log (2 * Real.pi) / 2
  let C := 4 + |c| + |k|
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht]
    have heq : ccmPrimeDeficitDilationPoleRemainder t =
        ccmPrimeDeficitDilationRemainder t - c - k * t := by
      dsimp only [ccmPrimeDeficitDilationPoleRemainder, ccmPrimeDeficitDilationRemainder, c, k]
      ring
    rw [heq]
    have h : |ccmPrimeDeficitDilationRemainder t - c - k * t| ≤ 7 / 2 + |c| + |k * t| :=
      ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
      (add_le_add (add_le_add (abs_ccmPrimeDeficitDilationRemainder_le_uniform ht) le_rfl) le_rfl)
    rw [abs_mul, abs_of_nonneg ht] at h
    dsimp only [C]
    have hc := mul_nonneg (abs_nonneg c) ht
    nlinarith only [h, hc, ht, abs_nonneg k]
  · rw [max_eq_right ht.le, ccmPrimeDeficitDilationPoleRemainder, source_causal ht,
      zero_sub, abs_neg, abs_mul, abs_of_pos (Real.exp_pos t)]
    have he : Real.exp t ≤ 1 := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ht.le
    calc
      _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg c)
      _ ≤ _ := by dsimp only [C]; simp only [zero_add, mul_one]; linarith only [abs_nonneg k]

private theorem half_coefficient_budgets {T : ℝ} (hT : 0 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (2 * ⌊Real.exp (T / 2)⌋₊),
      |ccmPrimeDeficitNeutralCoefficient ⌊Real.exp (T / 2)⌋₊ n|) ≤
        6 * Real.exp (T / 2) * (T + 1) ∧
    (∑ n ∈ Finset.Icc 1 (2 * ⌊Real.exp (T / 2)⌋₊),
      ccmPrimeDeficitNeutralCoefficient ⌊Real.exp (T / 2)⌋₊ n ^ 2) ≤
        18 * Real.exp (T / 2) * (T + 1) ^ 2 := by
  let N := ⌊Real.exp (T / 2)⌋₊
  have hN : 1 ≤ N := (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    (by simpa using Real.one_le_exp_iff.mpr (by linarith only [hT] : 0 ≤ T / 2))
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNX : (N : ℝ) ≤ Real.exp (T / 2) := Nat.floor_le (Real.exp_pos _).le
  have hlog : Real.log N ≤ T / 2 := (Real.log_le_iff_le_exp hNR).mpr hNX
  have hp (n : ℕ) (hn : n ∈ Finset.Icc 1 (2 * N)) :
      |ccmPrimeDeficitNeutralCoefficient N n| ≤ 3 * (T + 1) :=
    (coefficient_bound hN hn).trans (by linarith only [hlog, hT])
  constructor
  · calc
      _ ≤ ∑ _n ∈ Finset.Icc 1 (2 * N), (3 * (T + 1)) :=
        Finset.sum_le_sum (fun n hn => hp n hn)
      _ = 6 * (N : ℝ) * (T + 1) := by simp; ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ ∑ _n ∈ Finset.Icc 1 (2 * N), (3 * (T + 1)) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hs := (sq_le_sq₀ (abs_nonneg (ccmPrimeDeficitNeutralCoefficient N n))
          (by positivity : 0 ≤ 3 * (T + 1))).mpr (hp n hn)
        simpa only [sq_abs] using hs
      _ = 18 * (N : ℝ) * (T + 1) ^ 2 := by simp; ring
      _ ≤ _ := by gcongr

/-- The entire linear channel of the actual neutral completion has a
critical-scale polynomial budget, including the whole diffuse tail. -/
theorem ccmPrimeDeficitNeutralLinearWork_critical_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 0 ≤ T →
      |ccmPrimeDeficitNeutralLinearWork T| ≤ K * Real.exp (T / 2) * (T + 1) ^ 2 := by
  obtain ⟨C, hC, hc⟩ := linear_source_bound
  refine ⟨12 * C, by positivity, fun T hT => ?_⟩
  let N := ⌊Real.exp (T / 2)⌋₊
  have hp (n : ℕ) (hn : n ∈ Finset.Icc 1 (2 * N)) :
      |ccmPrimeDeficitDilationPoleRemainder (T - Real.log n)| ≤ C * (T + 1) := by
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
    have ht : max (T - Real.log n) 0 ≤ T := max_le (by linarith only [hl]) hT
    exact (hc _).trans (mul_le_mul_of_nonneg_left (by linarith only [ht]) hC.le)
  have hs : |∑ n ∈ Finset.Icc 1 (2 * N), ccmPrimeDeficitNeutralCoefficient N n *
      ccmPrimeDeficitDilationPoleRemainder (T - Real.log n)| ≤
        6 * C * Real.exp (T / 2) * (T + 1) ^ 2 := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (2 * N), |ccmPrimeDeficitNeutralCoefficient N n| *
          |ccmPrimeDeficitDilationPoleRemainder (T - Real.log n)| := by
        simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
          (fun n => ccmPrimeDeficitNeutralCoefficient N n *
            ccmPrimeDeficitDilationPoleRemainder (T - Real.log n)) (Finset.Icc 1 (2 * N))
      _ ≤ ∑ n ∈ Finset.Icc 1 (2 * N), |ccmPrimeDeficitNeutralCoefficient N n| * (C * (T + 1)) :=
        Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hp n hn) (abs_nonneg _))
      _ = (∑ n ∈ Finset.Icc 1 (2 * N), |ccmPrimeDeficitNeutralCoefficient N n|) * (C * (T + 1)) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (6 * Real.exp (T / 2) * (T + 1)) * (C * (T + 1)) :=
        mul_le_mul_of_nonneg_right (half_coefficient_budgets hT).1 (by positivity)
      _ = _ := by ring
  rw [ccmPrimeDeficitNeutralLinearWork, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2)]
  exact (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2)).trans_eq (by ring)

/-- Absolute budget of every diagonal in the actual diffuse neutral
packet. Unequal labels remain in the full quadratic work. -/
def ccmPrimeDeficitNeutralDiagonalBudget (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (2 * ⌊Real.exp (T / 2)⌋₊),
    ccmPrimeDeficitNeutralCoefficient ⌊Real.exp (T / 2)⌋₊ n ^ 2 *
      |ccmPrimeDeficitDivisorPoleRemainder (T - Real.log n - Real.log n)|

/-- Diffuse completion pays its full absolute diagonal at critical
scale. No sign or estimate for unequal-label interactions is inferred. -/
theorem ccmPrimeDeficitNeutralDiagonalBudget_critical_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 0 ≤ T →
      ccmPrimeDeficitNeutralDiagonalBudget T ≤ K * Real.exp (T / 2) * (T + 1) ^ 4 := by
  obtain ⟨C, hC, hc⟩ := ccmPrimeDeficitDivisorPoleRemainder_global_bound
  refine ⟨18 * C, by positivity, fun T hT => ?_⟩
  let N := ⌊Real.exp (T / 2)⌋₊
  have hp (n : ℕ) (hn : n ∈ Finset.Icc 1 (2 * N)) :
      |ccmPrimeDeficitDivisorPoleRemainder (T - Real.log n - Real.log n)| ≤ C * (T + 1) ^ 2 := by
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
    have ht : max (T - Real.log n - Real.log n) 0 ≤ T := max_le (by linarith only [hl]) hT
    refine (hc _).trans ?_
    gcongr
  unfold ccmPrimeDeficitNeutralDiagonalBudget
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 * N), ccmPrimeDeficitNeutralCoefficient N n ^ 2 * (C * (T + 1) ^ 2) :=
      Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hp n hn) (sq_nonneg _))
    _ = (∑ n ∈ Finset.Icc 1 (2 * N), ccmPrimeDeficitNeutralCoefficient N n ^ 2) * (C * (T + 1) ^ 2) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (18 * Real.exp (T / 2) * (T + 1) ^ 2) * (C * (T + 1) ^ 2) :=
      mul_le_mul_of_nonneg_right (half_coefficient_budgets hT).2 (by positivity)
    _ = _ := by ring

end RHTower
