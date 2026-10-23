import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheAveragedBudgetIsExactlyAdmission

/-!
# The signed budget is strictly weaker than its positive part

For an energy family with an admitted right endpoint `c`, admission at `a` is *equivalent* to a
horizon-free bound on the signed integral of the relative loss `r_T = −E'_T/(1 + E_T)` over `[a, c]`
(`ArithmeticContinuationAndCriticalEnergy.averagedContinuation_iff_admits`), because that integral
is `log(1 + E_T(a)) − log(1 + E_T(c))`. Paying every local loss separately — a horizon-free bound on
`∫_a^c (r_T)_+` (`PositivePartContinuation`) — is sufficient (`averagedContinuation_of_positivePart`)
but not necessary, even for smooth families that are nondecreasing in the horizon:

the lacunary family `E_T(ε) = Σ_{k=1}^T 2^{−k}(2 + sin(16^k ε))` is nonnegative, nondecreasing in
`T`, bounded by `3` at every damping (so admitted everywhere and averaged-continuable on every
interval), and yet `∫_a^c (r_T)_+ ≥ (8^T(c − a)/2 − 5)/8 → ∞` on every nondegenerate interval
(`exists_admitted_monotone_not_positivePartContinuation`).

The mechanism is lacunary oscillation: testing `−E'_T` against `(1 − cos(16^T ε))/2 ∈ [0, 1]` picks
out the top frequency, `∫_a^c E'_T(ε) cos(16^T ε) dε ≥ 8^T(c − a)/2 − 2`, while all lower
frequencies are almost orthogonal to it. The lesson for the arithmetic source: keep signed recovery;
a continuation estimate must let losses at one damping be repaid at another.
-/

open Filter Topology Finset MeasureTheory intervalIntegral
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

variable {E : ℝ → ℕ → ℝ} {E' : ℕ → ℝ → ℝ} {a c : ℝ}

/-- **A positive-part continuation budget on `[a, c]`**: the relative loss is integrable and its
positive part has a horizon-free integral bound. -/
def PositivePartContinuation (E : ℝ → ℕ → ℝ) (E' : ℕ → ℝ → ℝ) (a c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ T : ℕ, IntervalIntegrable (relativeLoss E E' T) volume a c ∧
    ∫ ε in a..c, max (relativeLoss E E' T ε) 0 ≤ C

/-- The positive part of an interval-integrable function is interval-integrable. -/
theorem intervalIntegrable_max_zero {f : ℝ → ℝ} {a c : ℝ} (h : IntervalIntegrable f volume a c) :
    IntervalIntegrable (fun x => max (f x) 0) volume a c :=
  ⟨h.1.pos_part, h.2.pos_part⟩

/-- Paying every loss separately is an averaged budget. -/
theorem averagedContinuation_of_positivePart (hac : a ≤ c)
    (h : PositivePartContinuation E E' a c) : AveragedContinuation E E' a c := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun T => ⟨(hC T).1, ?_⟩⟩
  have hint := (hC T).1
  have hint' : IntervalIntegrable (fun ε => max (relativeLoss E E' T ε) 0) volume a c :=
    intervalIntegrable_max_zero hint
  exact (intervalIntegral.integral_mono_on hac hint hint' fun ε _ => le_max_left _ _).trans
    (hC T).2

/-! ## Two trigonometric integrals -/

/-- `|∫_a^c cos(n x) cos(m x) dx| ≤ 3/m` when `0 < 16 n ≤ m`. -/
theorem abs_integral_cos_mul_cos_le {m n : ℝ} (hn : 0 < n) (hnm : 16 * n ≤ m) (a c : ℝ) :
    |∫ x in a..c, Real.cos (n * x) * Real.cos (m * x)| ≤ 3 / m := by
  have hm : 0 < m := by linarith
  have h1 : 0 < m - n := by linarith
  have h2 : 0 < m + n := by linarith
  set G : ℝ → ℝ := fun x => Real.sin ((m - n) * x) / (2 * (m - n)) +
    Real.sin ((m + n) * x) / (2 * (m + n))
  have hG : ∀ x, HasDerivAt G (Real.cos (n * x) * Real.cos (m * x)) x := by
    intro x
    have d1 := (((hasDerivAt_id' x).const_mul (m - n)).sin).div_const (2 * (m - n))
    have d2 := (((hasDerivAt_id' x).const_mul (m + n)).sin).div_const (2 * (m + n))
    refine (d1.add d2).congr_deriv ?_
    have hc1 : Real.cos ((m - n) * x) = Real.cos (m * x) * Real.cos (n * x) +
        Real.sin (m * x) * Real.sin (n * x) := by rw [sub_mul, Real.cos_sub]
    have hc2 : Real.cos ((m + n) * x) = Real.cos (m * x) * Real.cos (n * x) -
        Real.sin (m * x) * Real.sin (n * x) := by rw [add_mul, Real.cos_add]
    rw [hc1, hc2]
    field_simp
    ring
  have hcont : Continuous fun x => Real.cos (n * x) * Real.cos (m * x) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x)
    (hcont.intervalIntegrable _ _)]
  have hb : ∀ x, |G x| ≤ 1 / (2 * (m - n)) + 1 / (2 * (m + n)) := by
    intro x
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (m - n))]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (m + n))]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  have hsum : 2 * (1 / (2 * (m - n)) + 1 / (2 * (m + n))) ≤ 3 / m := by
    have e1 : 1 / (2 * (m - n)) ≤ 8 / (15 * m) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have e2 : 1 / (2 * (m + n)) ≤ 1 / (2 * m) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have e3 : 2 * (8 / (15 * m) + 1 / (2 * m)) ≤ 3 / m := by
      rw [show 2 * (8 / (15 * m) + 1 / (2 * m)) = (31 / 15) / m by field_simp; ring]
      exact div_le_div_of_nonneg_right (by norm_num) hm.le
    linarith
  calc |G c - G a| ≤ |G c| + |G a| := abs_sub _ _
    _ ≤ 2 * (1 / (2 * (m - n)) + 1 / (2 * (m + n))) := by linarith [hb c, hb a]
    _ ≤ 3 / m := hsum

/-- `∫_a^c cos²(m x) dx ≥ (c − a)/2 − 1/(2m)` for `m > 0`. -/
theorem integral_cos_mul_cos_self_ge {m : ℝ} (hm : 0 < m) (a c : ℝ) :
    (c - a) / 2 - 1 / (2 * m) ≤ ∫ x in a..c, Real.cos (m * x) * Real.cos (m * x) := by
  set G : ℝ → ℝ := fun x => x / 2 + Real.sin (2 * m * x) / (4 * m)
  have hG : ∀ x, HasDerivAt G (Real.cos (m * x) * Real.cos (m * x)) x := by
    intro x
    have d1 := (hasDerivAt_id' x).div_const 2
    have d2 := (((hasDerivAt_id' x).const_mul (2 * m)).sin).div_const (4 * m)
    refine (d1.add d2).congr_deriv ?_
    have hc : Real.cos (2 * m * x) = 2 * Real.cos (m * x) ^ 2 - 1 := by
      rw [show 2 * m * x = 2 * (m * x) by ring, Real.cos_two_mul]
    rw [hc]
    field_simp
    ring
  have hcont : Continuous fun x => Real.cos (m * x) * Real.cos (m * x) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x)
    (hcont.intervalIntegrable _ _)]
  simp only [G]
  have hs1 := Real.neg_one_le_sin (2 * m * c)
  have hs2 := Real.sin_le_one (2 * m * a)
  have h4 : (0 : ℝ) < 4 * m := by positivity
  have hsdiff : -2 / (4 * m) ≤ Real.sin (2 * m * c) / (4 * m) - Real.sin (2 * m * a) / (4 * m) := by
    rw [← sub_div]; exact div_le_div_of_nonneg_right (by linarith) h4.le
  have : -2 / (4 * m) = -(1 / (2 * m)) := by field_simp; ring
  linarith

/-! ## The lacunary family -/

/-- The lacunary energy family `E_T(ε) = Σ_{k=1}^T 2^{−k}(2 + sin(16^k ε))`. -/
def lacunaryEnergy (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 T, (2 : ℝ)⁻¹ ^ k * (2 + Real.sin (16 ^ k * ε))

/-- Its damping derivative `Σ_{k=1}^T 8^k cos(16^k ε)`. -/
def lacunaryEnergyDeriv (T : ℕ) (ε : ℝ) : ℝ := ∑ k ∈ Icc 1 T, (8 : ℝ) ^ k * Real.cos (16 ^ k * ε)

theorem hasDerivAt_lacunaryEnergy (T : ℕ) (ε : ℝ) :
    HasDerivAt (fun x => lacunaryEnergy x T) (lacunaryEnergyDeriv T ε) ε := by
  unfold lacunaryEnergy lacunaryEnergyDeriv
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := ((((hasDerivAt_id' ε).const_mul ((16 : ℝ) ^ k)).sin).const_add 2).const_mul
    ((2 : ℝ)⁻¹ ^ k)
  refine h.congr_deriv ?_
  rw [show (8 : ℝ) ^ k = (2 : ℝ)⁻¹ ^ k * 16 ^ k by rw [← mul_pow]; norm_num]
  ring

theorem sum_half_pow_le (T : ℕ) : ∑ k ∈ Icc 1 T, (2 : ℝ)⁻¹ ^ k ≤ 1 := by
  have h : ∀ T : ℕ, ∑ k ∈ Icc 1 T, (2 : ℝ)⁻¹ ^ k = 1 - (2 : ℝ)⁻¹ ^ T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
        rw [sum_Icc_succ_top (by omega), ih, pow_succ]; ring
  rw [h]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) T]

theorem lacunaryEnergy_nonneg (ε : ℝ) (T : ℕ) : 0 ≤ lacunaryEnergy ε T :=
  sum_nonneg fun k _ => mul_nonneg (by positivity) (by linarith [Real.neg_one_le_sin (16 ^ k * ε)])

theorem lacunaryEnergy_le (ε : ℝ) (T : ℕ) : lacunaryEnergy ε T ≤ 3 := by
  calc lacunaryEnergy ε T ≤ ∑ k ∈ Icc 1 T, (2 : ℝ)⁻¹ ^ k * 3 :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (by linarith [Real.sin_le_one (16 ^ k * ε)]) (by positivity)
    _ = 3 * ∑ k ∈ Icc 1 T, (2 : ℝ)⁻¹ ^ k := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ ≤ 3 := by linarith [sum_half_pow_le T]

/-- The family is nondecreasing in the horizon. -/
theorem lacunaryEnergy_mono (ε : ℝ) : Monotone (lacunaryEnergy ε) := by
  intro S T hST
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hST) fun k _ _ =>
    mul_nonneg (by positivity) (by linarith [Real.neg_one_le_sin (16 ^ k * ε)])

theorem continuous_lacunaryEnergyDeriv (T : ℕ) : Continuous (lacunaryEnergyDeriv T) := by
  unfold lacunaryEnergyDeriv; fun_prop

theorem continuous_lacunaryEnergy (T : ℕ) : Continuous fun ε => lacunaryEnergy ε T := by
  unfold lacunaryEnergy; fun_prop

theorem intervalIntegrable_relativeLoss_lacunary (T : ℕ) (a c : ℝ) :
    IntervalIntegrable (relativeLoss lacunaryEnergy lacunaryEnergyDeriv T) volume a c := by
  refine Continuous.intervalIntegrable ?_ a c
  unfold relativeLoss
  exact ((continuous_lacunaryEnergyDeriv T).neg).div (continuous_const.add
    (continuous_lacunaryEnergy T)) fun ε => by linarith [lacunaryEnergy_nonneg ε T]

/-- The geometric sum `Σ_{k=1}^{S} 8^k ≤ 8^{S+1}/7`. -/
theorem sum_eight_pow_le (S : ℕ) : ∑ k ∈ Icc 1 S, (8 : ℝ) ^ k ≤ 8 ^ (S + 1) / 7 := by
  induction S with
  | zero => norm_num
  | succ n ih =>
      rw [sum_Icc_succ_top (by omega)]
      have : (8 : ℝ) ^ (n + 1) / 7 + 8 ^ (n + 1) = 8 ^ (n + 1 + 1) / 7 := by ring
      linarith

/-- **The top frequency survives.** `∫_a^c E'_T(ε) cos(16^T ε) dε ≥ 8^T(c − a)/2 − 2` for
`T ≥ 1`. -/
theorem integral_lacunaryEnergyDeriv_mul_cos_ge (S : ℕ) (a c : ℝ) :
    (8 : ℝ) ^ (S + 1) * (c - a) / 2 - 2 ≤
      ∫ x in a..c, lacunaryEnergyDeriv (S + 1) x * Real.cos (16 ^ (S + 1) * x) := by
  set m : ℝ := 16 ^ (S + 1)
  have hm : 0 < m := by positivity
  have hcont : ∀ k : ℕ, Continuous fun x => (8 : ℝ) ^ k * Real.cos (16 ^ k * x) *
      Real.cos (m * x) := fun k => by fun_prop
  have hterm : ∀ k : ℕ, (∫ x in a..c, (8 : ℝ) ^ k * Real.cos (16 ^ k * x) * Real.cos (m * x)) =
      (8 : ℝ) ^ k * ∫ x in a..c, Real.cos (16 ^ k * x) * Real.cos (m * x) := fun k => by
    rw [← intervalIntegral.integral_const_mul]; congr 1; ext x; ring
  have hsplit : (∫ x in a..c, lacunaryEnergyDeriv (S + 1) x * Real.cos (m * x)) =
      (∑ k ∈ Icc 1 S, (8 : ℝ) ^ k * ∫ x in a..c, Real.cos (16 ^ k * x) * Real.cos (m * x)) +
        (8 : ℝ) ^ (S + 1) * ∫ x in a..c, Real.cos (m * x) * Real.cos (m * x) := by
    have hfun : (fun x => lacunaryEnergyDeriv (S + 1) x * Real.cos (m * x)) =
        fun x => ∑ k ∈ Icc 1 (S + 1), (8 : ℝ) ^ k * Real.cos (16 ^ k * x) * Real.cos (m * x) := by
      funext x; simp only [lacunaryEnergyDeriv, sum_mul]
    rw [hfun, intervalIntegral.integral_finsetSum fun k _ => (hcont k).intervalIntegrable _ _,
      sum_Icc_succ_top (by omega)]
    simp only [hterm]
    rfl
  rw [hsplit]
  -- the lower frequencies are almost orthogonal to the top one
  have hlow : |∑ k ∈ Icc 1 S, (8 : ℝ) ^ k * ∫ x in a..c, Real.cos (16 ^ k * x) * Real.cos (m * x)|
      ≤ 1 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ Icc 1 S, |(8 : ℝ) ^ k * ∫ x in a..c, Real.cos (16 ^ k * x) *
        Real.cos (m * x)| ≤ (8 : ℝ) ^ k * (3 / m) := by
      intro k hk
      have hkS : k ≤ S := (mem_Icc.mp hk).2
      rw [abs_mul, abs_of_pos (by positivity)]
      refine mul_le_mul_of_nonneg_left (abs_integral_cos_mul_cos_le (by positivity) ?_ a c)
        (by positivity)
      have : (16 : ℝ) ^ k ≤ 16 ^ S := pow_le_pow_right₀ (by norm_num) hkS
      simp only [m, pow_succ]; linarith
    refine (sum_le_sum hterm).trans ?_
    rw [← sum_mul]
    have h8 := sum_eight_pow_le S
    have h816 : (8 : ℝ) ^ (S + 1) ≤ m := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc (∑ k ∈ Icc 1 S, (8 : ℝ) ^ k) * (3 / m) ≤ 8 ^ (S + 1) / 7 * (3 / m) :=
          mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = 3 / 7 * (8 ^ (S + 1) / m) := by ring
      _ ≤ 3 / 7 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [div_le_one hm]; exact h816
      _ ≤ 1 := by norm_num
  have htop := integral_cos_mul_cos_self_ge hm a c
  have htop' : (8 : ℝ) ^ (S + 1) * ((c - a) / 2 - 1 / (2 * m)) ≤
      (8 : ℝ) ^ (S + 1) * ∫ x in a..c, Real.cos (m * x) * Real.cos (m * x) :=
    mul_le_mul_of_nonneg_left htop (by positivity)
  have hratio : (8 : ℝ) ^ (S + 1) * (1 / (2 * m)) ≤ 1 / 2 := by
    have h816 : (8 : ℝ) ^ (S + 1) ≤ m := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hl := (abs_le.mp hlow).1
  have hexpand : (8 : ℝ) ^ (S + 1) * ((c - a) / 2 - 1 / (2 * m)) =
      (8 : ℝ) ^ (S + 1) * (c - a) / 2 - (8 : ℝ) ^ (S + 1) * (1 / (2 * m)) := by ring
  linarith

/-- The positive part of the relative loss dominates `−E'(1 − cos(16^T ε))/8`. -/
theorem max_relativeLoss_ge (T : ℕ) (ε : ℝ) :
    (-lacunaryEnergyDeriv T ε + lacunaryEnergyDeriv T ε * Real.cos (16 ^ T * ε)) / 8 ≤
      max (relativeLoss lacunaryEnergy lacunaryEnergyDeriv T ε) 0 := by
  have hE0 := lacunaryEnergy_nonneg ε T
  have hE3 := lacunaryEnergy_le ε T
  have hc1 := Real.cos_le_one (16 ^ T * ε)
  have hc2 := Real.neg_one_le_cos (16 ^ T * ε)
  set d := lacunaryEnergyDeriv T ε
  set k := Real.cos (16 ^ T * ε)
  have hlhs : (-d + d * k) / 8 = -d * ((1 - k) / 2) / 4 := by ring
  rw [hlhs, relativeLoss]
  rcases le_or_gt d 0 with hd | hd
  · refine le_trans ?_ (le_max_left _ _)
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    have h1 : -d * ((1 - k) / 2) ≤ -d := by nlinarith
    nlinarith
  · refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ (1 - k) / 2 := by linarith
    have : -d * ((1 - k) / 2) ≤ 0 := by nlinarith
    linarith

/-- **The positive-part budget fails on every nondegenerate interval.** -/
theorem not_positivePartContinuation_lacunary (hac : a < c) :
    ¬ PositivePartContinuation lacunaryEnergy lacunaryEnergyDeriv a c := by
  rintro ⟨C, hC⟩
  -- choose a horizon at which the top frequency outweighs `C`
  have htend : Tendsto (fun S : ℕ => (8 : ℝ) ^ (S + 1) * (c - a) / 2) atTop atTop := by
    have h := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 8)).comp
      (tendsto_add_atTop_nat 1)
    exact (h.atTop_mul_const (by linarith : (0 : ℝ) < c - a)).atTop_div_const (by norm_num)
  obtain ⟨S, hS⟩ := (htend.eventually_gt_atTop (8 * C + 5)).exists
  set T := S + 1
  have hint := (hC T).1
  have hcontD := continuous_lacunaryEnergyDeriv T
  have hlow : IntervalIntegrable (fun ε => (-lacunaryEnergyDeriv T ε +
      lacunaryEnergyDeriv T ε * Real.cos (16 ^ T * ε)) / 8) volume a c :=
    (Continuous.intervalIntegrable (by fun_prop) a c)
  have hmax : IntervalIntegrable
      (fun ε => max (relativeLoss lacunaryEnergy lacunaryEnergyDeriv T ε) 0) volume a c :=
    intervalIntegrable_max_zero hint
  have hmono := intervalIntegral.integral_mono_on hac.le hlow hmax fun ε _ =>
    max_relativeLoss_ge T ε
  -- evaluate the lower integral
  have hFTC : (∫ x in a..c, lacunaryEnergyDeriv T x) = lacunaryEnergy c T - lacunaryEnergy a T :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_lacunaryEnergy T x)
      (hcontD.intervalIntegrable _ _)
  have hlowval : (∫ ε in a..c, (-lacunaryEnergyDeriv T ε +
      lacunaryEnergyDeriv T ε * Real.cos (16 ^ T * ε)) / 8) =
      (-(lacunaryEnergy c T - lacunaryEnergy a T) +
        ∫ x in a..c, lacunaryEnergyDeriv T x * Real.cos (16 ^ T * x)) / 8 := by
    have hi1 : IntervalIntegrable (fun x => -lacunaryEnergyDeriv T x) volume a c :=
      hcontD.neg.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun x => lacunaryEnergyDeriv T x * Real.cos (16 ^ T * x))
        volume a c := (hcontD.mul (by fun_prop)).intervalIntegrable _ _
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_neg, hFTC]
  have htop := integral_lacunaryEnergyDeriv_mul_cos_ge S a c
  have hE := lacunaryEnergy_le c T
  have hE0 := lacunaryEnergy_nonneg a T
  rw [hlowval] at hmono
  have := (hC T).2
  linarith

/-- **Signed admission does not pay every local loss.** There is a smooth family, nonnegative,
nondecreasing in the horizon and bounded by `3`, hence admitted at every parameter and carrying an
averaged budget on every interval, which has no positive-part budget on any nondegenerate
interval. -/
theorem exists_admitted_monotone_not_positivePartContinuation :
    ∃ (F : ℝ → ℕ → ℝ) (F' : ℕ → ℝ → ℝ),
      (∀ ε T, 0 ≤ F ε T) ∧ (∀ ε, Monotone (F ε)) ∧
      (∀ T ε, HasDerivAt (fun x => F x T) (F' T ε) ε) ∧ (∀ ε, Admits F ε) ∧
      (∀ a c, a ≤ c → AveragedContinuation F F' a c) ∧
      (∀ a c, a < c → ¬ PositivePartContinuation F F' a c) := by
  refine ⟨lacunaryEnergy, lacunaryEnergyDeriv, lacunaryEnergy_nonneg, lacunaryEnergy_mono,
    hasDerivAt_lacunaryEnergy, fun ε => ⟨3, fun T => lacunaryEnergy_le ε T⟩,
    fun a c hac => ?_, fun a c hac => not_positivePartContinuation_lacunary hac⟩
  exact (averagedContinuation_iff_admits hac (fun ε _ T => lacunaryEnergy_nonneg ε T)
    (fun T ε _ => hasDerivAt_lacunaryEnergy T ε)
    (fun T => intervalIntegrable_relativeLoss_lacunary T a c)
    ⟨3, fun T => lacunaryEnergy_le c T⟩).mpr ⟨3, fun T => lacunaryEnergy_le a T⟩

end GaloisForLFunctions.ArithmeticCompensationTheory
