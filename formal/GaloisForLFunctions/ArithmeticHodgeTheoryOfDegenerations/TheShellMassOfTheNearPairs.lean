import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNonRatioPrimesOnConductorPackets

/-!
# The shell mass of the near pairs

The near pairs of two conductor packets, weighted by the profile autocorrelation `G` at the
log-distance in units of the width `w = c/N`, carry exactly the shell correction of the completed
conductor energy:

`Σ_{n ≠ j ≤ N} c_b(n) c_a(j) G(log(j/n)/w)/√(nj) = [a = b] ∫φ² φ(a) S_a(c) + O(c²/N)`

for `1 ≤ c ≤ N/8` (`abs_shellMass_sub_le`), `S_a(c) = (2/(∫φ² φ(a))) Σ_{1 ≤ h < c} c_a(h) ∫_{h/c}^1 G(u)/u du`.
Along each gap `h = j − n` the kernel is linearized to `G(h/(wn))/n`, the periodic pair weight is
replaced by its mean `2[a = b] c_a(h)`, and the sum over `n` is the integral
`∫ G(h/(wx)) dx/x = ∫_{h/c}^1 G(t)/t dt`. The error is small enough to survive multiplication by
`log N`, which is what the cancellation of the logarithm in the near block requires.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped Real

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis BezoutValuationIncidence

/-- The shell mass of the near pairs of two conductors. -/
def shellMass (φ : ℝ → ℝ) (c : ℝ) (N a b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
    (if j = n then 0 else shellAutocorr φ ((Real.log j - Real.log n) / (c / N))) *
      ramanujanLagCoefficient b n * ramanujanLagCoefficient a j / (Real.sqrt n * Real.sqrt j)

/-- The pair weight along a gap `h`. -/
def gapPairWeight (a b n h : ℕ) : ℝ :=
  ramanujanLagCoefficient b n * ramanujanLagCoefficient a (n + h) +
    ramanujanLagCoefficient b (n + h) * ramanujanLagCoefficient a n

/-- The exact gap kernel `G(log(1 + h/n)/w)/√(n(n + h))`. -/
def shellGapKernel (φ : ℝ → ℝ) (w : ℝ) (h : ℕ) (x : ℝ) : ℝ :=
  shellAutocorr φ (Real.log (1 + h / x) / w) / Real.sqrt (x * (x + h))

/-- The linearized gap kernel `G(h/(wx))/x`. -/
def linGapKernel (φ : ℝ → ℝ) (w : ℝ) (h : ℕ) (x : ℝ) : ℝ :=
  shellAutocorr φ (h / (w * x)) / x

/-! ### The gap form -/

theorem shellMass_eq_gaps (φ : ℝ → ℝ) (c : ℝ) (N a b : ℕ) :
    shellMass φ c N a b = ∑ h ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N - h),
      gapPairWeight a b n h * shellGapKernel φ (c / N) h n := by
  set T : ℕ → ℕ → ℝ := fun n j =>
    (if j = n then 0 else shellAutocorr φ ((Real.log j - Real.log n) / (c / N))) *
      ramanujanLagCoefficient b n * ramanujanLagCoefficient a j / (Real.sqrt n * Real.sqrt j)
    with hT
  have hsplit : ∀ n j, T n j = (if n < j then T n j else 0) + (if j < n then T n j else 0) :=
    fun n j => by
      rcases lt_trichotomy n j with h | h | h
      · rw [if_pos h, if_neg (by omega), add_zero]
      · subst h; simp [hT]
      · rw [if_neg (by omega), if_pos h, zero_add]
  have hker : ∀ n h : ℕ, 1 ≤ n → shellAutocorr φ ((Real.log ((n + h : ℕ) : ℝ) - Real.log n) /
      (c / N)) = shellAutocorr φ (Real.log (1 + h / (n : ℝ)) / (c / N)) := fun n h hn => by
    rw [log_add_sub_log hn]
  have hker' : ∀ n h : ℕ, 1 ≤ n → shellAutocorr φ ((Real.log n - Real.log ((n + h : ℕ) : ℝ)) /
      (c / N)) = shellAutocorr φ (Real.log (1 + h / (n : ℝ)) / (c / N)) := fun n h hn => by
    rw [← shellAutocorr_neg, ← neg_div, neg_sub, log_add_sub_log hn]
  calc shellMass φ c N a b = ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, T n j := rfl
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (if n < j then T n j else 0) +
        ∑ j ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (if j < n then T n j else 0) := by
        rw [Finset.sum_comm (s := Finset.Icc 1 N) (t := Finset.Icc 1 N)
          (f := fun j n => if j < n then T n j else 0), ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun n _ => by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => hsplit n j
    _ = ∑ h ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N - h), T n (n + h) +
        ∑ h ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N - h), T (n + h) n := by
        rw [sum_sum_ite_lt T N, sum_sum_ite_lt (fun j n => T n j) N]
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun h hh => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn1 := (Finset.mem_Icc.mp hn).1
        have hh1 := (Finset.mem_Icc.mp hh).1
        simp only [hT, if_neg (show n + h ≠ n by omega), if_neg (show n ≠ n + h by omega),
          hker n h hn1, hker' n h hn1, gapPairWeight, shellGapKernel, sqrt_mul_sqrt_add,
          mul_comm (Real.sqrt ((n + h : ℕ) : ℝ)) (Real.sqrt n)]
        ring

/-! ### Elementary bounds -/

/-- `Σ_{m ≤ n ≤ K} 1/n² ≤ 1/(m − 1)` for `m ≥ 2`. -/
theorem sum_Icc_inv_sq_le {m : ℕ} (hm : 2 ≤ m) (K : ℕ) :
    ∑ n ∈ Finset.Icc m K, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((m : ℝ) - 1) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have key : ∀ K : ℕ, ∑ n ∈ Finset.Icc m K, (1 : ℝ) / (n : ℝ) ^ 2 ≤
      1 / ((m : ℝ) - 1) - (if m ≤ K then 1 / (K : ℝ) else 1 / ((m : ℝ) - 1)) := by
    intro K
    induction K with
    | zero => rw [Finset.Icc_eq_empty (by omega), if_neg (by omega)]; simp
    | succ K ih =>
      rcases Nat.lt_or_ge (K + 1) m with h | h
      · rw [Finset.Icc_eq_empty (by omega), if_neg (by omega)]; simp
      · rw [Finset.sum_Icc_succ_top h, if_pos h]
        have hK : (1 : ℝ) ≤ K := by
          have : 1 ≤ K := by omega
          exact_mod_cast this
        rcases Nat.lt_or_ge K m with h' | h'
        · have hKm : K + 1 = m := by omega
          rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, zero_add]
          have : ((K + 1 : ℕ) : ℝ) = m := by exact_mod_cast hKm
          rw [this]
          have hpos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
          rw [div_sub_div _ _ hpos.ne' (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith
        · rw [if_pos h'] at ih
          have hstep : (1 : ℝ) / ((K + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (K : ℝ) - 1 / ((K + 1 : ℕ) : ℝ) := by
            push_cast
            rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
              (by positivity)]
            nlinarith
          linarith
  have h := key K
  split_ifs at h with hmK
  · have : (0 : ℝ) ≤ 1 / (K : ℝ) := by positivity
    linarith
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    positivity

/-- The tail `Σ_{X < n ≤ K} 1/n² ≤ 2/X` for `X ≥ 1`. -/
theorem sum_filter_inv_sq_le (K : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ (Finset.Icc 1 K).filter (fun n : ℕ => X < n), (1 : ℝ) / (n : ℝ) ^ 2 ≤ 2 / X := by
  set m := ⌊X⌋₊ + 1
  have hm : 2 ≤ m := by have := Nat.one_le_floor_iff X |>.mpr hX; omega
  have hsub : (Finset.Icc 1 K).filter (fun n : ℕ => X < n) ⊆ Finset.Icc m K := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨Nat.succ_le_of_lt ((Nat.floor_lt (by linarith)).mpr hn.2), hn.1.2⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
    ((sum_Icc_inv_sq_le hm K).trans ?_)
  have hfl : X / 2 ≤ (⌊X⌋₊ : ℝ) := by
    have h1 := Nat.lt_floor_add_one X
    have h2 : (1 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast Nat.one_le_floor_iff X |>.mpr hX
    linarith
  have hm' : ((m : ℕ) : ℝ) - 1 = ⌊X⌋₊ := by simp [m]
  rw [hm', div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

theorem log_one_add_two_mul_ge {w : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1) : w ≤ Real.log (1 + 2 * w) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.abs_exp_sub_one_le (x := w) (by rw [abs_of_nonneg hw]; exact hw1)
  rw [abs_of_nonneg hw] at h
  linarith [le_abs_self (Real.exp w - 1)]

theorem abs_log_one_add_sub_le_sq {x : ℝ} (hx : 0 ≤ x) : |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have h1 : Real.log (1 + x) ≤ x := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)]
  have h2 : x / (1 + x) ≤ Real.log (1 + x) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / (1 + x))
    rw [one_div, Real.log_inv] at h
    have : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by field_simp; ring
    linarith
  have h3 : x - x ^ 2 ≤ x / (1 + x) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith [sq_nonneg x]
  rw [abs_le]; constructor <;> nlinarith

section Gaps

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- **Linearization of the gap kernel.** -/
theorem abs_gapKernel_sub_lin_le {K : NNReal} (hK : LipschitzWith K (shellAutocorr φ)) {w : ℝ}
    (hw : 0 < w) (hw2 : w ≤ 1 / 2) {h n : ℕ} (hh : 1 ≤ h) (hn : 1 ≤ n) :
    |shellGapKernel φ w h n - linGapKernel φ w h n| ≤
      if (h : ℝ) / (2 * w) < n then 2 * (K + ∫ u, φ u ^ 2) * h / (n : ℝ) ^ 2 else 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  set M := ∫ u, φ u ^ 2
  have hM0 : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  split_ifs with hnx
  · set x : ℝ := h / n with hx
    have hx0 : 0 ≤ x := by positivity
    have hxw : x < 2 * w := by
      rw [hx, div_lt_iff₀ hn0]; rw [div_lt_iff₀ (by positivity)] at hnx; linarith
    have hlin : (h : ℝ) / (w * n) = x / w := by rw [hx]; field_simp
    have hsq : Real.sqrt (n * (n + h)) ≥ n := by
      rw [ge_iff_le, Real.le_sqrt hn0.le (by positivity)]; nlinarith
    rw [shellGapKernel, linGapKernel, hlin]
    have e : shellAutocorr φ (Real.log (1 + x) / w) / Real.sqrt (n * (n + h)) -
        shellAutocorr φ (x / w) / n =
        (shellAutocorr φ (Real.log (1 + x) / w) - shellAutocorr φ (x / w)) /
          Real.sqrt (n * (n + h)) + shellAutocorr φ (x / w) *
            (1 / Real.sqrt (n * (n + 0)) - 1 / Real.sqrt (n * (n + h))) * (-1) := by
      rw [add_zero, Real.sqrt_mul_self hn0.le]; ring
    rw [e]
    have hL := hK.dist_le_mul (Real.log (1 + x) / w) (x / w)
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hw] at hL
    have hlog := abs_log_one_add_sub_le_sq hx0
    have hG := abs_shellAutocorr_le' hφ hsupp (x / w)
    have hs := abs_inv_sqrt_sub_le hn0 (le_refl (0 : ℝ)) (Nat.cast_nonneg h)
    rw [zero_sub, abs_neg, abs_of_pos hh0] at hs
    have h1 : |(shellAutocorr φ (Real.log (1 + x) / w) - shellAutocorr φ (x / w)) /
        Real.sqrt (n * (n + h))| ≤ 2 * K * h / (n : ℝ) ^ 2 := by
      rw [abs_div, abs_of_pos (lt_of_lt_of_le hn0 hsq), div_le_iff₀ (lt_of_lt_of_le hn0 hsq)]
      have hKx : (K : ℝ) * (|Real.log (1 + x) - x| / w) ≤ K * (x * (2 * w) / w) := by
        apply mul_le_mul_of_nonneg_left _ K.2
        apply div_le_div_of_nonneg_right _ hw.le
        calc |Real.log (1 + x) - x| ≤ x ^ 2 := hlog
          _ ≤ x * (2 * w) := by nlinarith
      have hxn : x * (2 * w) / w = 2 * h / n := by rw [hx]; field_simp
      rw [hxn] at hKx
      calc _ ≤ (K : ℝ) * (2 * h / n) := hL.trans hKx
        _ ≤ 2 * K * h / (n : ℝ) ^ 2 * Real.sqrt (n * (n + h)) := by
            rw [show 2 * (K : ℝ) * h / (n : ℝ) ^ 2 * Real.sqrt (n * (n + h)) =
              (K : ℝ) * (2 * h / n) * (Real.sqrt (n * (n + h)) / n) by field_simp]
            refine le_mul_of_one_le_right (by positivity) ?_
            rw [le_div_iff₀ hn0, one_mul]; exact hsq
    have h2 : |shellAutocorr φ (x / w) * (1 / Real.sqrt (n * (n + 0)) -
        1 / Real.sqrt (n * (n + h))) * (-1)| ≤ M * h / (n : ℝ) ^ 2 := by
      rw [abs_mul, abs_neg, abs_one, mul_one, abs_mul]
      calc _ ≤ M * (h / (2 * (n : ℝ) ^ 2)) := mul_le_mul hG hs (abs_nonneg _) hM0
        _ ≤ M * h / (n : ℝ) ^ 2 := by
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hh0.le (by positivity)
              (by nlinarith)) hM0
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 2 * K * h / (n : ℝ) ^ 2 + M * h / (n : ℝ) ^ 2 := add_le_add h1 h2
      _ ≤ 2 * (K + M) * h / (n : ℝ) ^ 2 := by
          rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
          nlinarith [mul_nonneg hM0 hh0.le]
  · push Not at hnx
    have h2w : (h : ℝ) / n ≥ 2 * w := by
      rw [ge_iff_le, le_div_iff₀ hn0]; rw [le_div_iff₀ (by positivity)] at hnx; linarith
    have hz1 : shellAutocorr φ (Real.log (1 + h / n) / w) = 0 := by
      apply shellAutocorr_eq_zero_of_one_le hφ hsupp
      rw [le_div_iff₀ hw, one_mul]
      exact (log_one_add_two_mul_ge hw.le (by linarith)).trans
        (Real.log_le_log (by linarith) (by linarith))
    have hz2 : shellAutocorr φ (h / (w * n)) = 0 := by
      apply shellAutocorr_eq_zero_of_one_le hφ hsupp
      rw [le_div_iff₀ (by positivity), one_mul]
      have : (h : ℝ) ≥ 2 * w * n := by rwa [ge_iff_le, le_div_iff₀ hn0] at h2w
      nlinarith
    rw [shellGapKernel, linGapKernel, hz1, hz2]; simp

/-- The linearized gap kernel vanishes up to `x = h/w`. -/
theorem linGapKernel_eq_zero {w : ℝ} (hw : 0 < w) {h : ℕ} {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ h / w) : linGapKernel φ w h x = 0 := by
  rw [linGapKernel, shellAutocorr_eq_zero_of_one_le hφ hsupp, zero_div]
  rw [le_div_iff₀ (by positivity), one_mul]
  rw [le_div_iff₀ hw] at hx; linarith

theorem abs_linGapKernel_le {w : ℝ} (hw : 0 < w) {h : ℕ} (hh : 1 ≤ h) {x : ℝ} (hx0 : 0 < x) :
    |linGapKernel φ w h x| ≤ (∫ u, φ u ^ 2) * w / h := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  rcases le_or_gt x (h / w) with hx | hx
  · rw [linGapKernel_eq_zero hφ hsupp hw hx0 hx, abs_zero]
    have : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    positivity
  · rw [linGapKernel, abs_div, abs_of_pos hx0]
    have hG := abs_shellAutocorr_le' hφ hsupp ((h : ℝ) / (w * x))
    rw [div_le_iff₀ hx0]
    have : (h : ℝ) / w * w = h := by field_simp
    calc _ ≤ ∫ u, φ u ^ 2 := hG
      _ ≤ (∫ u, φ u ^ 2) * w / h * x := by
          rw [mul_div_assoc, mul_assoc]
          refine le_mul_of_one_le_right (integral_nonneg fun _ => sq_nonneg _) ?_
          rw [div_mul_eq_mul_div, le_div_iff₀ hh0, one_mul]
          rw [div_lt_iff₀ hw] at hx; linarith

/-- **The linearized gap kernel is Lipschitz** with constant `(2K + ∫φ²)·4w²/h²`. -/
theorem abs_linGapKernel_sub_le {K : NNReal} (hK : LipschitzWith K (shellAutocorr φ)) {w : ℝ}
    (hw : 0 < w) {h : ℕ} (hh : 1 ≤ h) {x y : ℝ} (hx0 : 0 < x) (hy0 : 0 < y) :
    |linGapKernel φ w h x - linGapKernel φ w h y| ≤
      (2 * K + ∫ u, φ u ^ 2) * (4 * w ^ 2 / (h : ℝ) ^ 2) * |x - y| := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  set M := ∫ u, φ u ^ 2
  have hM0 : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  set x₁ : ℝ := h / (2 * w) with hx₁
  have hx₁0 : 0 < x₁ := by positivity
  have hx₁w : x₁ ≤ h / w := by rw [hx₁]; exact div_le_div_of_nonneg_left hh0.le hw (by linarith)
  set lam := (2 * (K : ℝ) + M) * (4 * w ^ 2 / (h : ℝ) ^ 2) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hbig : ∀ x y : ℝ, x₁ ≤ x → x₁ ≤ y →
      |linGapKernel φ w h x - linGapKernel φ w h y| ≤ lam * |x - y| := by
    intro x y hx hy
    have hx0' := hx₁0.trans_le hx
    have hy0' := hx₁0.trans_le hy
    have hinv : |1 / x - 1 / y| ≤ |x - y| / x₁ ^ 2 := by
      rw [div_sub_div _ _ hx0'.ne' hy0'.ne', abs_div, abs_of_pos (mul_pos hx0' hy0'), one_mul,
        mul_one, abs_sub_comm y x, div_le_div_iff₀ (mul_pos hx0' hy0') (by positivity)]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
    have hL := hK.dist_le_mul ((h : ℝ) / (w * x)) (h / (w * y))
    rw [Real.dist_eq, Real.dist_eq] at hL
    have harg : (h : ℝ) / (w * x) - h / (w * y) = h / w * (1 / x - 1 / y) := by
      field_simp
    rw [harg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < h / w)] at hL
    have hG := abs_shellAutocorr_le' hφ hsupp ((h : ℝ) / (w * y))
    have e : linGapKernel φ w h x - linGapKernel φ w h y =
        (shellAutocorr φ (h / (w * x)) - shellAutocorr φ (h / (w * y))) * (1 / x) +
          shellAutocorr φ (h / (w * y)) * (1 / x - 1 / y) := by
      simp only [linGapKernel]; ring
    rw [e]
    have hhw : (h : ℝ) / w / x ≤ 2 := by
      rw [div_le_iff₀ hx0']; rw [hx₁, div_le_iff₀ (by positivity)] at hx
      field_simp; linarith
    calc _ ≤ |(shellAutocorr φ (h / (w * x)) - shellAutocorr φ (h / (w * y))) * (1 / x)| +
          |shellAutocorr φ (h / (w * y)) * (1 / x - 1 / y)| := abs_add_le _ _
      _ ≤ K * (h / w * |1 / x - 1 / y|) * (1 / x) + M * |1 / x - 1 / y| := by
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / x)]
          exact add_le_add (mul_le_mul_of_nonneg_right hL (by positivity))
            (mul_le_mul_of_nonneg_right hG (abs_nonneg _))
      _ = (K * (h / w / x) + M) * |1 / x - 1 / y| := by ring
      _ ≤ (2 * K + M) * (|x - y| / x₁ ^ 2) :=
          mul_le_mul (by nlinarith [K.2]) hinv (abs_nonneg _) (by positivity)
      _ = lam * |x - y| := by rw [hlam, hx₁]; field_simp; ring
  have hzero : ∀ z : ℝ, 0 < z → z ≤ x₁ → linGapKernel φ w h z = 0 := fun z hz hzx =>
    linGapKernel_eq_zero hφ hsupp hw hz (hzx.trans hx₁w)
  rcases le_or_gt x₁ x with hx | hx <;> rcases le_or_gt x₁ y with hy | hy
  · exact hbig x y hx hy
  · rw [hzero y hy0 hy.le, ← hzero x₁ hx₁0 le_rfl]
    exact (hbig x x₁ hx le_rfl).trans (mul_le_mul_of_nonneg_left (by
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith) hlam0)
  · rw [hzero x hx0 hx.le, ← hzero x₁ hx₁0 le_rfl]
    exact (hbig x₁ y le_rfl hy).trans (mul_le_mul_of_nonneg_left (by
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith) hlam0)
  · rw [hzero x hx0 hx.le, hzero y hy0 hy.le, sub_self, abs_zero]; positivity

end Gaps

/-! ### One gap -/

theorem abs_gapPairWeight_le (a b n h : ℕ) :
    |gapPairWeight a b n h| ≤ 2 * ((∑ t ∈ a.divisors, (t : ℝ)) * ∑ t ∈ b.divisors, (t : ℝ)) := by
  rw [gapPairWeight]
  have h1 := abs_ramanujanLagCoefficient_le a (n + h)
  have h2 := abs_ramanujanLagCoefficient_le b n
  have h3 := abs_ramanujanLagCoefficient_le a n
  have h4 := abs_ramanujanLagCoefficient_le b (n + h)
  calc _ ≤ |ramanujanLagCoefficient b n * ramanujanLagCoefficient a (n + h)| +
        |ramanujanLagCoefficient b (n + h) * ramanujanLagCoefficient a n| := abs_add_le _ _
    _ ≤ (∑ t ∈ b.divisors, (t : ℝ)) * (∑ t ∈ a.divisors, (t : ℝ)) +
        (∑ t ∈ b.divisors, (t : ℝ)) * (∑ t ∈ a.divisors, (t : ℝ)) := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul h2 h1 (abs_nonneg _) (by positivity))
          (mul_le_mul h4 h3 (abs_nonneg _) (by positivity))
    _ = _ := by ring

theorem gapPairWeight_periodic (a b h n : ℕ) :
    gapPairWeight a b (n + b * a) h = gapPairWeight a b n h := by
  have h1 : ∀ k, ramanujanLagCoefficient b (k + b * a) = ramanujanLagCoefficient b k :=
    fun k => ramanujanLagCoefficient_add_mul b k a
  have h2 : ∀ k, ramanujanLagCoefficient a (k + b * a) = ramanujanLagCoefficient a k :=
    fun k => by rw [mul_comm b a]; exact ramanujanLagCoefficient_add_mul a k b
  simp only [gapPairWeight]
  rw [show n + b * a + h = n + h + b * a by ring, h1 n, h2 (n + h), h1 (n + h), h2 n]

theorem periodicMean_gapPairWeight {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : ℕ) :
    periodicMean (fun n => gapPairWeight a b n h) (b * a) =
      2 * (if a = b then ramanujanLagCoefficient a h else 0) := by
  rw [periodicMean, ← sum_range_gapWeight ha hb h]
  simp only [gapPairWeight]

section GapSums

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- The linearization error along one gap is `O(w)`. -/
theorem abs_sum_gap_sub_lin_le {K : NNReal} (hK : LipschitzWith K (shellAutocorr φ)) {w : ℝ}
    (hw : 0 < w) (hw2 : w ≤ 1 / 2) (a b : ℕ) {h : ℕ} (hh : 1 ≤ h) (R : ℕ) :
    |∑ n ∈ Finset.Icc 1 R, gapPairWeight a b n h * (shellGapKernel φ w h n - linGapKernel φ w h n)| ≤
      2 * ((∑ t ∈ a.divisors, (t : ℝ)) * ∑ t ∈ b.divisors, (t : ℝ)) *
        (2 * (K + ∫ u, φ u ^ 2) * (4 * w)) := by
  set σ := 2 * ((∑ t ∈ a.divisors, (t : ℝ)) * ∑ t ∈ b.divisors, (t : ℝ))
  have hσ : 0 ≤ σ := by positivity
  set M := ∫ u, φ u ^ 2
  have hM0 : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  set X : ℝ := h / (2 * w)
  have hX : 1 ≤ X := by
    rw [le_div_iff₀ (by positivity)]; linarith [(by exact_mod_cast hh : (1 : ℝ) ≤ h)]
  calc _ ≤ ∑ n ∈ Finset.Icc 1 R, σ * (if X < (n : ℝ) then 2 * (K + M) * h / (n : ℝ) ^ 2 else 0) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        rw [abs_mul]
        exact mul_le_mul (abs_gapPairWeight_le a b n h)
          (abs_gapKernel_sub_lin_le hφ hsupp hK hw hw2 hh (Finset.mem_Icc.mp hn).1) (abs_nonneg _) hσ
    _ = ∑ n ∈ (Finset.Icc 1 R).filter (fun n : ℕ => X < n), σ * (2 * (K + M) * h / (n : ℝ) ^ 2) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
    _ = σ * (2 * (K + M) * h) * ∑ n ∈ (Finset.Icc 1 R).filter (fun n : ℕ => X < n),
        (1 : ℝ) / (n : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ σ * (2 * (K + M) * h) * (2 / X) :=
        mul_le_mul_of_nonneg_left (sum_filter_inv_sq_le R hX) (by positivity)
    _ = σ * (2 * (K + M) * (4 * w)) := by simp only [X]; field_simp; ring

/-- The periodic pair weight along one gap is its mean `2[a = b]c_a(h)`, up to the variation of the
linearized kernel. -/
theorem abs_sum_gap_lin_sub_mean_le {K : NNReal} (hK : LipschitzWith K (shellAutocorr φ)) {w : ℝ}
    (hw : 0 < w) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {h : ℕ} (hh : 1 ≤ h) {R : ℕ} (hR : 1 ≤ R) :
    |∑ n ∈ Finset.Icc 1 R, gapPairWeight a b n h * linGapKernel φ w h n -
        2 * (if a = b then ramanujanLagCoefficient a h else 0) *
          ∑ n ∈ Finset.Icc 1 R, linGapKernel φ w h n| ≤
      2 * (b * a : ℕ) * (2 * ((∑ t ∈ a.divisors, (t : ℝ)) * ∑ t ∈ b.divisors, (t : ℝ))) *
        ((∫ u, φ u ^ 2) * w / h +
          (2 * K + ∫ u, φ u ^ 2) * (4 * w ^ 2 / (h : ℝ) ^ 2) * R) := by
  set lam := (2 * (K : ℝ) + ∫ u, φ u ^ 2) * (4 * w ^ 2 / (h : ℝ) ^ 2)
  have hlam0 : 0 ≤ lam := by
    have : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    positivity
  have hq : 0 < b * a := Nat.mul_pos hb ha
  set f : ℕ → ℝ := fun i => linGapKernel φ w h ((i + 1 : ℕ) : ℝ)
  have hconv : ∀ F : ℕ → ℝ, ∑ n ∈ Finset.Icc 1 R, F n = ∑ i ∈ range ((R - 1) + 1), F (i + 1) := by
    intro F; rw [Nat.sub_add_cancel hR, sum_range_succ_eq_sum_Icc]
  have havg := abs_sum_range_mul_shift_sub_mean_le hq (fun n => gapPairWeight_periodic a b h n)
    (fun n => abs_gapPairWeight_le a b n h) 1 f (R - 1)
  rw [periodicMean_gapPairWeight ha hb h] at havg
  have e1 : ∑ n ∈ Finset.Icc 1 R, gapPairWeight a b n h * linGapKernel φ w h n =
      ∑ i ∈ range ((R - 1) + 1), f i * gapPairWeight a b (1 + i) h := by
    rw [hconv]; refine Finset.sum_congr rfl fun i _ => by simp only [f]; rw [add_comm 1 i]; ring
  have e2 : ∑ n ∈ Finset.Icc 1 R, linGapKernel φ w h n = ∑ i ∈ range ((R - 1) + 1), f i := by
    rw [hconv]
  rw [e1, e2]
  refine havg.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hfM : |f (R - 1)| ≤ (∫ u, φ u ^ 2) * w / h :=
    abs_linGapKernel_le hφ hsupp hw hh (by positivity)
  have hvar : ∑ i ∈ range (R - 1), |f (i + 1) - f i| ≤ lam * R := by
    calc _ ≤ ∑ _i ∈ range (R - 1), lam := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := abs_linGapKernel_sub_le hφ hsupp hK hw hh
            (x := ((i + 1 + 1 : ℕ) : ℝ)) (y := ((i + 1 : ℕ) : ℝ)) (by positivity) (by positivity)
          have hd : |((i + 1 + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)| = 1 := by push_cast; norm_num
          rw [hd, mul_one] at this
          exact this
      _ = lam * (R - 1 : ℕ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ lam * R := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le R 1) hlam0
  exact add_le_add hfM hvar

/-- The substitution `t = h/(wx)`: `∫_1^{1+R} G(h/(wx)) dx/x = ∫_{h/(w(1+R))}^{h/w} G(t)/t dt`. -/
theorem integral_linGapKernel_eq {w : ℝ} (hw : 0 < w) {h : ℕ} (hh : 1 ≤ h) (R : ℕ) :
    ∫ x in (1 : ℝ)..(1 + R), linGapKernel φ w h x =
      ∫ t in ((h : ℝ) / (w * (1 + R)))..(h / w), shellAutocorr φ t / t := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hcont := continuous_shellAutocorr hφ hsupp
  set F : ℝ → ℝ := fun x => h / w / x with hF
  have hderiv : ∀ x ∈ uIcc (1 : ℝ) (1 + R), HasDerivAt F (-(h / w) / x ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have := (hasDerivAt_inv hx0).const_mul (h / w)
    simpa only [hF, div_eq_mul_inv, mul_neg, neg_mul] using this
  have hcont' : ContinuousOn (fun x => -(h / w) / x ^ 2) (uIcc (1 : ℝ) (1 + R)) := by
    refine ContinuousOn.div continuousOn_const (continuous_pow 2).continuousOn fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])] at hx
    have : 0 < x := by linarith [hx.1]
    positivity
  have hpos : ∀ t ∈ F '' uIcc (1 : ℝ) (1 + R), 0 < t := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])] at hx
    have : 0 < x := by linarith [hx.1]
    simp only [hF]; positivity
  have hg : ContinuousOn (fun t => shellAutocorr φ t / t) (F '' uIcc (1 : ℝ) (1 + R)) :=
    hcont.continuousOn.div continuousOn_id fun t ht => (hpos t ht).ne'
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hcont' hg
  have hF1 : F 1 = h / w := by simp [hF]
  have hFR : F (1 + R) = h / (w * (1 + R)) := by simp only [hF]; field_simp
  rw [hF1, hFR] at hsub
  rw [intervalIntegral.integral_symm (h / w) (h / (w * (1 + R))), ← hsub,
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])] at hx
  have hx0 : 0 < x := by linarith [hx.1]
  simp only [Function.comp, hF, linGapKernel]
  rw [show (h : ℝ) / w / x = h / (w * x) by field_simp]
  field_simp

theorem abs_integral_div_le {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    |∫ t in t₀..t₁, shellAutocorr φ t / t| ≤ (∫ u, φ u ^ 2) * Real.log (t₁ / t₀) := by
  have hcont := continuous_shellAutocorr hφ hsupp
  have hM0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hpos : ∀ t ∈ Set.uIcc t₀ t₁, 0 < t := fun t ht' => by
    rw [Set.uIcc_of_le ht] at ht'; linarith [ht'.1]
  have hint1 : IntervalIntegrable (fun t => |shellAutocorr φ t / t|) volume t₀ t₁ :=
    ((hcont.continuousOn.div continuousOn_id fun t h' => (hpos t h').ne').abs).intervalIntegrable
  have hint2 : IntervalIntegrable (fun t => (∫ u, φ u ^ 2) * t⁻¹) volume t₀ t₁ :=
    ((continuousOn_const.mul (continuousOn_inv₀.mono fun t h' => (hpos t h').ne'))).intervalIntegrable
  refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
  calc ∫ t in t₀..t₁, |shellAutocorr φ t / t| ≤ ∫ t in t₀..t₁, (∫ u, φ u ^ 2) * t⁻¹ := by
        refine intervalIntegral.integral_mono_on ht hint1 hint2 fun t ht' => ?_
        have ht0 : 0 < t := by linarith [ht'.1]
        rw [abs_div, abs_of_pos ht0, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (abs_shellAutocorr_le' hφ hsupp t) (by positivity)
    _ = (∫ u, φ u ^ 2) * Real.log (t₁ / t₀) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ht₀ (ht₀.trans_le ht)]

/-- **One gap.** Along a gap `h ≤ N/2` with `w = c/N ≤ 1/2`, the pair sum is
`2[a = b] c_a(h) ∫_{h/c}^1 G(t)/t dt` up to `O(w + w²N/h² + h/N)`. -/
theorem abs_gapSum_sub_le {K : NNReal} (hK : LipschitzWith K (shellAutocorr φ)) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) {c : ℝ} {N h : ℕ} (hc : 0 < c) (hN : 1 ≤ N) (hw2 : c / N ≤ 1 / 2)
    (hh : 1 ≤ h) (hhN : 2 * h ≤ N) :
    |∑ n ∈ Finset.Icc 1 (N - h), gapPairWeight a b n h * shellGapKernel φ (c / N) h n -
        2 * (if a = b then ramanujanLagCoefficient a h else 0) *
          ∫ t in ((h : ℝ) / c)..1, shellAutocorr φ t / t| ≤
      2 * ((∑ t ∈ a.divisors, (t : ℝ)) * ∑ t ∈ b.divisors, (t : ℝ)) *
          (2 * (K + ∫ u, φ u ^ 2) * (4 * (c / N))) +
        2 * (b * a : ℕ) * (2 * ((∑ t ∈ a.divisors, (t : ℝ)) * ∑ t ∈ b.divisors, (t : ℝ))) *
          ((∫ u, φ u ^ 2) * (c / N) / h +
            (2 * K + ∫ u, φ u ^ 2) * (4 * (c / N) ^ 2 / (h : ℝ) ^ 2) * N) +
        2 * (∑ t ∈ a.divisors, (t : ℝ)) *
          ((2 * K + ∫ u, φ u ^ 2) * (4 * (c / N) ^ 2 / (h : ℝ) ^ 2) * N +
            (∫ u, φ u ^ 2) * (2 * h / N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  set w := c / N with hwdef
  have hw : 0 < w := div_pos hc hN0
  set R := N - h with hRdef
  have hR1 : 1 ≤ R := by omega
  have hRN : (R : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N h
  have hRcast : (R : ℝ) = N - h := by rw [hRdef, Nat.cast_sub (by omega)]
  set M := ∫ u, φ u ^ 2
  have hM0 : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  set σa := ∑ t ∈ a.divisors, (t : ℝ)
  set σb := ∑ t ∈ b.divisors, (t : ℝ)
  set Pm := 2 * (if a = b then ramanujanLagCoefficient a h else 0)
  have hPm : |Pm| ≤ 2 * σa := by
    simp only [Pm]
    split_ifs
    · rw [abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left (abs_ramanujanLagCoefficient_le a h)
        (by norm_num)
    · simp; positivity
  set lam := (2 * (K : ℝ) + M) * (4 * w ^ 2 / (h : ℝ) ^ 2)
  have hlam0 : 0 ≤ lam := by positivity
  -- the four pieces
  have h1 := abs_sum_gap_sub_lin_le hφ hsupp hK hw hw2 a b hh R
  have h2 := abs_sum_gap_lin_sub_mean_le hφ hsupp hK hw ha hb hh hR1
  have hEM := abs_sum_range_sub_integral_le (f := linGapKernel φ w h) (lam := lam) 1 R
    (fun x hx y hy => abs_linGapKernel_sub_le hφ hsupp hK hw hh (by linarith [hx.1])
      (by linarith [hy.1]))
  have hconv : ∑ i ∈ range R, linGapKernel φ w h (1 + i) =
      ∑ n ∈ Finset.Icc 1 R, linGapKernel φ w h n := by
    rw [← sum_range_succ_eq_sum_Icc]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring_nf
  rw [hconv, integral_linGapKernel_eq hφ hsupp hw hh R] at hEM
  -- the upper limit of the substitution
  have hhw : 1 ≤ (h : ℝ) / w := by
    rw [le_div_iff₀ hw, one_mul]; linarith [(by exact_mod_cast hh : (1 : ℝ) ≤ h)]
  set t₀ := (h : ℝ) / c with ht₀
  set t₁ := (h : ℝ) / (w * (1 + R)) with ht₁
  have hcw : c = w * N := by rw [hwdef]; field_simp
  have ht₀0 : 0 < t₀ := by positivity
  have ht01 : t₀ ≤ t₁ := by
    rw [ht₀, ht₁, hcw]
    exact div_le_div_of_nonneg_left hh0.le (by positivity) (mul_le_mul_of_nonneg_left
      (by rw [hRcast]; linarith [(by exact_mod_cast hh : (1 : ℝ) ≤ h)]) hw.le)
  have hcont := continuous_shellAutocorr hφ hsupp
  have hii : ∀ x y : ℝ, 0 < x → 0 < y →
      IntervalIntegrable (fun t => shellAutocorr φ t / t) volume x y := by
    intro x y hx hy
    refine (hcont.continuousOn.div continuousOn_id fun t ht => ?_).intervalIntegrable
    rcases le_total x y with hxy | hxy
    · rw [Set.uIcc_of_le hxy] at ht; exact (hx.trans_le ht.1).ne'
    · rw [Set.uIcc_of_ge hxy] at ht; exact (hy.trans_le ht.1).ne'
  have hzero : ∫ t in (1 : ℝ)..(h / w), shellAutocorr φ t / t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => by
      rw [Set.uIcc_of_le hhw] at ht
      simp only [shellAutocorr_eq_zero_of_one_le hφ hsupp ht.1, zero_div]]
    simp
  have hsplit : ∫ t in t₁..(h / w), shellAutocorr φ t / t = ∫ t in t₁..1, shellAutocorr φ t / t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii t₁ 1 (ht₀0.trans_le ht01) one_pos)
      (hii 1 (h / w) one_pos (by linarith)), hzero, add_zero]
  have hend : |(∫ t in t₁..1, shellAutocorr φ t / t) - ∫ t in t₀..1, shellAutocorr φ t / t| ≤
      M * (2 * h / N) := by
    have e : (∫ t in t₁..1, shellAutocorr φ t / t) - (∫ t in t₀..1, shellAutocorr φ t / t) =
        -∫ t in t₀..t₁, shellAutocorr φ t / t := by
      have hadd : (∫ t in t₀..t₁, shellAutocorr φ t / t) + (∫ t in t₁..1, shellAutocorr φ t / t) =
          ∫ t in t₀..1, shellAutocorr φ t / t := intervalIntegral.integral_add_adjacent_intervals
        (hii t₀ t₁ ht₀0 (ht₀0.trans_le ht01)) (hii t₁ 1 (ht₀0.trans_le ht01) one_pos)
      rw [eq_neg_iff_add_eq_zero, ← hadd]
      ring
    rw [e, abs_neg]
    refine (abs_integral_div_le hφ hsupp ht₀0 ht01).trans (mul_le_mul_of_nonneg_left ?_ hM0)
    have hq : t₁ / t₀ = N / (N - h + 1) := by
      have h2h : (2 * h : ℝ) ≤ N := by exact_mod_cast hhN
      have hd1 : (1 : ℝ) + (N - h) ≠ 0 := by linarith
      have hd2 : (N : ℝ) - h + 1 ≠ 0 := by linarith
      rw [ht₁, ht₀, hcw, hRcast]
      field_simp [hd1, hd2, hh0.ne', hw.ne', hN0.ne']
      ring
    rw [hq]
    have hden : (N : ℝ) / 2 ≤ N - h + 1 := by
      have : (2 * h : ℝ) ≤ N := by exact_mod_cast hhN
      linarith
    have hden0 : (0 : ℝ) < N - h + 1 := by linarith
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hden0.ne', div_le_div_iff₀ hden0 hN0]
    nlinarith
  -- assemble
  set I₀ := ∫ t in t₀..1, shellAutocorr φ t / t with hI₀
  set I₁ := ∫ t in t₁..1, shellAutocorr φ t / t with hI₁
  set Iw := ∫ t in t₁..(h / w), shellAutocorr φ t / t with hIw
  set S₀ := ∑ n ∈ Finset.Icc 1 R, gapPairWeight a b n h * shellGapKernel φ w h n with hS₀
  set S₁ := ∑ n ∈ Finset.Icc 1 R, gapPairWeight a b n h * linGapKernel φ w h n with hS₁
  set S₂ := ∑ n ∈ Finset.Icc 1 R, linGapKernel φ w h n with hS₂
  set D := ∑ n ∈ Finset.Icc 1 R, gapPairWeight a b n h * (shellGapKernel φ w h n - linGapKernel φ w h n)
    with hDdef
  have hD : D = S₀ - S₁ := by
    rw [hDdef, hS₀, hS₁, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have e : S₀ - Pm * I₀ = D + (S₁ - Pm * S₂) + Pm * (S₂ - Iw) + Pm * (I₁ - I₀) := by
    rw [hD, hsplit]; ring
  rw [e]
  have h3 : |Pm * (S₂ - Iw)| ≤ 2 * σa * (lam * N) := by
    rw [abs_mul]
    refine mul_le_mul hPm (hEM.trans (mul_le_mul_of_nonneg_left hRN hlam0)) (abs_nonneg _)
      (by positivity)
  have hend' : |I₁ - I₀| ≤ M * (2 * h / N) := hend
  have h4 : |Pm * (I₁ - I₀)| ≤ 2 * σa * (M * (2 * h / N)) := by
    rw [abs_mul]; exact mul_le_mul hPm hend' (abs_nonneg _) (by positivity)
  have h2' : |S₁ - Pm * S₂| ≤ 2 * (b * a : ℕ) * (2 * (σa * σb)) * (M * w / h + lam * N) := by
    refine h2.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hRN hlam0)) (by positivity))
  have habs : |D + (S₁ - Pm * S₂) + Pm * (S₂ - Iw) + Pm * (I₁ - I₀)| ≤
      |D| + |S₁ - Pm * S₂| + |Pm * (S₂ - Iw)| + |Pm * (I₁ - I₀)| := by
    have e1 := abs_add_le (D + (S₁ - Pm * S₂) + Pm * (S₂ - Iw)) (Pm * (I₁ - I₀))
    have e2 := abs_add_le (D + (S₁ - Pm * S₂)) (Pm * (S₂ - Iw))
    have e3 := abs_add_le D (S₁ - Pm * S₂)
    linarith
  refine habs.trans ?_
  have hfin : 2 * (σa * σb) * (2 * (K + M) * (4 * w)) +
      2 * (b * a : ℕ) * (2 * (σa * σb)) * (M * w / h + lam * N) +
      2 * σa * (lam * N) + 2 * σa * (M * (2 * h / N)) =
      2 * (σa * σb) * (2 * (K + M) * (4 * (c / N))) +
        2 * (b * a : ℕ) * (2 * (σa * σb)) *
          (M * (c / N) / h + (2 * K + M) * (4 * (c / N) ^ 2 / (h : ℝ) ^ 2) * N) +
        2 * σa * ((2 * K + M) * (4 * (c / N) ^ 2 / (h : ℝ) ^ 2) * N + M * (2 * h / N)) := by
    simp only [lam, hwdef]; ring
  rw [← hfin]
  linarith [h1, h2', h3, h4]

theorem gapKernel_eq_zero_of_le {w : ℝ} (hw : 0 < w) (hw2 : w ≤ 1 / 2) {h n : ℕ} (hn : 1 ≤ n)
    (hhn : 2 * w * n ≤ h) : shellGapKernel φ w h n = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2w : 2 * w ≤ (h : ℝ) / n := by rw [le_div_iff₀ hn0]; linarith
  rw [shellGapKernel, shellAutocorr_eq_zero_of_one_le hφ hsupp, zero_div]
  rw [le_div_iff₀ hw, one_mul]
  exact (log_one_add_two_mul_ge hw.le (by linarith)).trans
    (Real.log_le_log (by linarith) (by linarith))

omit hφ hsupp in
theorem sum_Icc_inv_sq_le_three (H : ℕ) : ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) ^ 2 ≤ 3 := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 H) (fun h : ℕ => (1 : ℝ) < h)]
  have h1 := sum_filter_inv_sq_le H (X := 1) le_rfl
  have h2 : ∑ h ∈ (Finset.Icc 1 H).filter (fun h : ℕ => ¬ (1 : ℝ) < h), (1 : ℝ) / (h : ℝ) ^ 2 ≤ 1 := by
    have hsub : (Finset.Icc 1 H).filter (fun h : ℕ => ¬ (1 : ℝ) < h) ⊆ {1} := by
      intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc, not_lt, Finset.mem_singleton] at hh ⊢
      have : (h : ℝ) ≤ 1 := hh.2
      have : h ≤ 1 := by exact_mod_cast this
      omega
    calc _ ≤ ∑ h ∈ ({1} : Finset ℕ), (1 : ℝ) / (h : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 1 := by simp
  linarith

/-- The shell correction is the gap sum of its targets over `1 ≤ h ≤ 2c`. -/
theorem shellCorrection_eq_gapTargets (hM : 0 < ∫ u, φ u ^ 2) {a : ℕ} (ha : 0 < a) {c : ℝ}
    (hc : 1 ≤ c) :
    (∫ u, φ u ^ 2) * a.totient * shellCorrection φ c a = ∑ h ∈ Finset.Icc 1 ⌊2 * c⌋₊,
      2 * ramanujanLagCoefficient a h * ∫ t in ((h : ℝ) / c)..1, shellAutocorr φ t / t := by
  have htot : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  have hcle : ⌈c⌉₊ ≤ ⌊2 * c⌋₊ := Nat.le_floor ((Nat.ceil_lt_add_one (by linarith)).le.trans
    (by linarith))
  have hsub : Finset.Ico 1 ⌈c⌉₊ ⊆ Finset.Icc 1 ⌊2 * c⌋₊ := by
    intro h hh; simp only [Finset.mem_Ico, Finset.mem_Icc] at hh ⊢; omega
  rw [shellCorrection, ← Finset.sum_subset hsub, Finset.mul_sum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun h _ => ?_
    field_simp
  · intro h hh hnot
    simp only [Finset.mem_Ico, Finset.mem_Icc, not_and, not_lt] at hh hnot
    have hch : c ≤ h := (Nat.le_ceil c).trans (by exact_mod_cast hnot hh.1)
    have h1 : 1 ≤ (h : ℝ) / c := by rw [le_div_iff₀ (by linarith)]; linarith
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_congr
      (g := fun _ => (0 : ℝ)) fun t ht => by
        rw [Set.uIcc_of_le h1] at ht
        simp only [shellAutocorr_eq_zero_of_one_le hφ hsupp ht.1, zero_div]]
    simp

/-- **The shell mass of the near pairs.** For `1 ≤ c ≤ N/8`,
`|Σ_{n ≠ j} c_b(n)c_a(j)G(log(j/n)/w)/√(nj) − [a = b]∫φ² φ(a) S_a(c)| ≤ C c²/N`. -/
theorem abs_shellMass_sub_le (hM : 0 < ∫ u, φ u ^ 2) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (N : ℕ), 1 ≤ c → 8 * c ≤ N →
      |shellMass φ c N a b -
          (if a = b then (∫ u, φ u ^ 2) * a.totient * shellCorrection φ c a else 0)| ≤
        C * c ^ 2 / N := by
  obtain ⟨K, hK⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  set M := ∫ u, φ u ^ 2 with hMdef
  set σa := ∑ t ∈ a.divisors, (t : ℝ) with hσadef
  set σb := ∑ t ∈ b.divisors, (t : ℝ) with hσbdef
  set q : ℝ := ((b * a : ℕ) : ℝ) with hqdef
  have hσa : 0 ≤ σa := by positivity
  have hσb : 0 ≤ σb := by positivity
  have hq0 : 0 ≤ q := by positivity
  set A₁ := 2 * (σa * σb) * (2 * (K + M) * 4) + 2 * q * (2 * (σa * σb)) * M
  set A₂ := (2 * q * (2 * (σa * σb)) + 2 * σa) * ((2 * K + M) * 4)
  set A₃ := 2 * σa * (M * 2)
  refine ⟨2 * A₁ + 3 * A₂ + 4 * A₃, by positivity, fun c N hc hcN => ?_⟩
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  set w := c / N with hwdef
  have hw : 0 < w := div_pos (by linarith) hN0
  have hw2 : w ≤ 1 / 2 := by rw [hwdef, div_le_iff₀ hN0]; linarith
  set H := ⌊2 * c⌋₊ with hH
  have hHc : (H : ℝ) ≤ 2 * c := Nat.floor_le (by linarith)
  have hHN : H ≤ N := by
    have : (H : ℝ) ≤ N := by linarith
    exact_mod_cast this
  -- the gaps beyond `2c` are empty
  have hsplit : Finset.Icc 1 N = Finset.Icc 1 H ∪ Finset.Ioc H N := by
    ext h; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 H) (Finset.Ioc H N) := by
    rw [Finset.disjoint_left]; intro h h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  have hfar : ∀ h ∈ Finset.Ioc H N, ∑ n ∈ Finset.Icc 1 (N - h),
      gapPairWeight a b n h * shellGapKernel φ w h n = 0 := by
    intro h hh
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2.trans (Nat.sub_le N h)
    have h2c : 2 * c < h := by
      have := Nat.lt_floor_add_one (2 * c)
      have h' : H + 1 ≤ h := (Finset.mem_Ioc.mp hh).1
      have : ((H + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast h'
      push_cast at this; linarith
    rw [gapKernel_eq_zero_of_le hφ hsupp hw hw2 hn1 (by
      have : 2 * w * n ≤ 2 * w * N := mul_le_mul_of_nonneg_left hnN (by positivity)
      have e : 2 * w * N = 2 * c := by rw [hwdef]; field_simp
      linarith), mul_zero]
  -- the target as a gap sum
  have htarget : (if a = b then M * a.totient * shellCorrection φ c a else 0) =
      ∑ h ∈ Finset.Icc 1 H, 2 * (if a = b then ramanujanLagCoefficient a h else 0) *
        ∫ t in ((h : ℝ) / c)..1, shellAutocorr φ t / t := by
    split_ifs with hab
    · exact shellCorrection_eq_gapTargets hφ hsupp hM ha hc
    · simp
  rw [shellMass_eq_gaps, hsplit, Finset.sum_union hdisj, Finset.sum_congr rfl hfar,
    Finset.sum_const_zero, add_zero, htarget, ← Finset.sum_sub_distrib]
  -- the gap bound
  have hgap : ∀ h ∈ Finset.Icc 1 H,
      |∑ n ∈ Finset.Icc 1 (N - h), gapPairWeight a b n h * shellGapKernel φ (c / N) h n -
        2 * (if a = b then ramanujanLagCoefficient a h else 0) *
          ∫ t in ((h : ℝ) / c)..1, shellAutocorr φ t / t| ≤
        A₁ * (c / N) + A₂ * (c ^ 2 / N) * (1 / (h : ℝ) ^ 2) + A₃ * (h / N) := by
    intro h hh
    have hh1 := (Finset.mem_Icc.mp hh).1
    have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh1
    have hhN : 2 * h ≤ N := by
      have : (2 * h : ℝ) ≤ N := by
        have := (by exact_mod_cast (Finset.mem_Icc.mp hh).2 : (h : ℝ) ≤ H); linarith
      exact_mod_cast this
    have hbnd := abs_gapSum_sub_le hφ hsupp hK ha hb (by linarith) hN hw2 hh1 hhN
    simp only [← hMdef, ← hσadef, ← hσbdef, ← hqdef] at hbnd
    refine hbnd.trans ?_
    have hwh : M * (c / N) / h ≤ M * (c / N) := by
      have hM0 : 0 ≤ M * (c / N) := by positivity
      exact div_le_self hM0 hh0
    have hh0' : (h : ℝ) ≠ 0 := by positivity
    have hdiff : A₁ * (c / N) + A₂ * (c ^ 2 / N) * (1 / (h : ℝ) ^ 2) + A₃ * (h / N) -
        (2 * (σa * σb) * (2 * (K + M) * (4 * (c / N))) +
          2 * q * (2 * (σa * σb)) *
            (M * (c / N) / h + (2 * K + M) * (4 * (c / N) ^ 2 / (h : ℝ) ^ 2) * N) +
          2 * σa * ((2 * K + M) * (4 * (c / N) ^ 2 / (h : ℝ) ^ 2) * N + M * (2 * h / N))) =
        2 * q * (2 * (σa * σb)) * (M * (c / N) - M * (c / N) / h) := by
      simp only [A₁, A₂, A₃]
      field_simp
      ring
    have hnn : 0 ≤ 2 * q * (2 * (σa * σb)) * (M * (c / N) - M * (c / N) / h) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hwh)
    linarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hgap).trans ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div]
  have hinv := sum_Icc_inv_sq_le_three H
  have hsumh : ∑ h ∈ Finset.Icc 1 H, (h : ℝ) ≤ 4 * c ^ 2 := by
    calc _ ≤ ∑ _h ∈ Finset.Icc 1 H, (H : ℝ) :=
          Finset.sum_le_sum fun h hh => by exact_mod_cast (Finset.mem_Icc.mp hh).2
      _ = (H : ℝ) * H := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ (2 * c) * (2 * c) := mul_le_mul hHc hHc (by positivity) (by linarith)
      _ = 4 * c ^ 2 := by ring
  have hA₁ : 0 ≤ A₁ := by positivity
  have hA₂ : 0 ≤ A₂ := by positivity
  have hA₃ : 0 ≤ A₃ := by positivity
  have t1 : (H : ℝ) * (A₁ * (c / N)) ≤ 2 * A₁ * (c ^ 2 / N) := by
    have hAc : 0 ≤ A₁ * (c / N) := mul_nonneg hA₁ (div_nonneg (by linarith) hN0.le)
    have : (H : ℝ) * (A₁ * (c / N)) ≤ 2 * c * (A₁ * (c / N)) :=
      mul_le_mul_of_nonneg_right hHc hAc
    have e : 2 * c * (A₁ * (c / N)) = 2 * A₁ * (c ^ 2 / N) := by ring
    linarith
  have t2 : A₂ * (c ^ 2 / N) * ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) ^ 2 ≤
      3 * A₂ * (c ^ 2 / N) := by
    have := mul_le_mul_of_nonneg_left hinv
      (mul_nonneg hA₂ (div_nonneg (sq_nonneg c) hN0.le))
    linarith
  have t3 : A₃ * ((∑ h ∈ Finset.Icc 1 H, (h : ℝ)) / N) ≤ 4 * A₃ * (c ^ 2 / N) := by
    have := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsumh hN0.le) hA₃
    have e : A₃ * (4 * c ^ 2 / N) = 4 * A₃ * (c ^ 2 / N) := by ring
    linarith
  have e : (2 * A₁ + 3 * A₂ + 4 * A₃) * c ^ 2 / N =
      2 * A₁ * (c ^ 2 / N) + 3 * A₂ * (c ^ 2 / N) + 4 * A₃ * (c ^ 2 / N) := by ring
  rw [e]
  linarith

end GapSums

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
