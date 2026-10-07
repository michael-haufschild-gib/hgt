import GaloisForLFunctions.RHTower.WeilZetaSquareAveraging
import GaloisForLFunctions.HTGeometry.GcdWeightedSeriesInversion

/-!
# Dilation rigidity of the Weil cone in the presence of a Möbius part

Let `a, f : ℕ → ℝ` with `Σ |a(n)| n^{−1/2+δ} < ∞`, `Σ |f(n)| n^{−1/2+δ} < ∞` for some `δ > 0`,
`f(1) = 0`, and `v` regular with continuation `E` bounded on the critical line.

**Theorem** (`eq_delta_of_weilPositiveFull`). If `lam = Λ ⋆ a + μ ⋆ f + v` is full-cone Weil-positive,
then `a = δ₁`.

**Proof.** For `m ≥ 1`, `c = ±1` and `W = |1 + c m^{it}|²`, the averaged boundary inequality gives
`∫ ω_L W (1 − Re A) |ζ|² ≥ −K L` (`exists_averaged_ge`). Expanding `W (1 − Re A)` into cosines and using
the twisted second moments `∫ ω_L |ζ|² cos((log m₁ − log m₂)t) = gcd(m₁,m₂)(m₁m₂)^{−1/2} W(L) + O(m₁m₂ L)`
(`abs_momentRe_log_sub_le`), the left side is `B(c, m) W(L) + o(L log L)`, where
`B(c, m) = (1 + c²)(1 − A(1)) + c m^{−1/2}(2 − Σ a(n)(1 + gcd(m,n))/n)` (`coeffB`). Since
`W(L) ≥ L log L`, `B(c, m) ≥ 0` (`coeffB_nonneg`). With `A(1) = 1` and `c = ±1` this is
`Σ_n a(n) gcd(m,n)/n = 1` for every `m ≥ 1`, and the gcd inversion
(`eq_zero_of_tsum_gcd_mul_div_eq_zero`) applied to `a − δ₁` gives `a = δ₁`.

No realness at zeros, no zero counting and no discrete moment of `ζ′` is used: the weight `|ζ|²`
annihilates every zero, and only fixed-twist second moments of `ζ` enter.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation

namespace RHTower.WeilZetaSquare

variable {a f v : ℕ → ℝ} {E : ℂ → ℂ} {δ : ℝ}

/-! ## The real part of the dilation series on the line -/

theorem re_term_line (a : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    (LSeries.term (fun n => (a n : ℂ)) (linePt t) n).re =
      a n / Real.sqrt n * Real.cos (Real.log n * t) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hs : linePt t = (1 / 2 : ℂ) + (t : ℂ) * I := by simp [linePt]
  rw [hs, term_add]
  have hhalf : LSeries.term (fun n => (a n : ℂ)) (1 / 2) n = ((a n / Real.sqrt n : ℝ) : ℂ) := by
    rw [LSeries.term_of_ne_zero hn.ne']
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow hn0, Real.sqrt_eq_rpow]
    push_cast; ring
  rw [hhalf, Complex.re_ofReal_mul,
    show -((t : ℂ) * I * (Real.log n : ℂ)) = ((-(Real.log n * t) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem summable_coeff_line (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) :
    Summable fun n => |a n / Real.sqrt n| := by
  have hs : Summable fun n => ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖ :=
    summable_norm_iff.mpr (summable_of_le_re ha (by simp; linarith))
  refine hs.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [LSeries.norm_term_eq, if_neg hn.ne', abs_div, Real.sqrt_eq_rpow, Complex.ofReal_re,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  simp

/-- `Re A(½+it) = Σ a(n) n^{−1/2} cos(t log n)`. -/
theorem re_dilSeries_line (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (t : ℝ) :
    (dilSeries a (linePt t)).re = ∑' n, a n / Real.sqrt n * Real.cos (Real.log n * t) := by
  have hs : LSeriesSummable (fun n => (a n : ℂ)) (linePt t) :=
    summable_of_le_re ha (by rw [linePt_re]; linarith)
  unfold dilSeries LSeries
  rw [Complex.re_tsum hs]
  exact tsum_congr fun n => re_term_line a t n

/-! ## The twisted moments at rational frequencies -/

/-- **Main term at a rational frequency**: for `m₁, m₂ ≥ 1`,
`|M_L(log m₁ − log m₂) − gcd(m₁,m₂)(m₁m₂)^{−1/2} W(L)| ≤ C m₁ m₂ L`. -/
theorem exists_abs_momentRe_log_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ {m₁ m₂ : ℕ}, 0 < m₁ → 0 < m₂ →
      |momentRe L (Real.log m₁ - Real.log m₂) -
          (Nat.gcd m₁ m₂ : ℝ) / Real.sqrt ((m₁ : ℝ) * m₂) * (ZetaNotch.logWindow L).re| ≤
        C * ((m₁ : ℝ) * m₂) * L := by
  obtain ⟨C, hC, hmain⟩ := exists_abs_momentRe_sub_le
  refine ⟨C, hC, fun {L} hL {m₁ m₂} h1 h2 => ?_⟩
  have hg0 : 0 < Nat.gcd m₁ m₂ := Nat.gcd_pos_of_pos_left _ h1
  have hcop : Nat.Coprime (m₁ / Nat.gcd m₁ m₂) (m₂ / Nat.gcd m₁ m₂) :=
    Nat.coprime_div_gcd_div_gcd hg0
  have hm₁ : m₁ = Nat.gcd m₁ m₂ * (m₁ / Nat.gcd m₁ m₂) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hm₂ : m₂ = Nat.gcd m₁ m₂ * (m₂ / Nat.gcd m₁ m₂) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  have hh0 : 0 < m₁ / Nat.gcd m₁ m₂ := Nat.div_pos (Nat.gcd_le_left _ h1) hg0
  have hk0 : 0 < m₂ / Nat.gcd m₁ m₂ := Nat.div_pos (Nat.gcd_le_right _ h2) hg0
  have hE := hmain hL hh0 hk0 hcop
  generalize Nat.gcd m₁ m₂ = g at hg0 hm₁ hm₂ hE hh0 hk0 ⊢
  generalize m₁ / g = h at hm₁ hE hh0
  generalize m₂ / g = k at hm₂ hE hk0
  subst hm₁ hm₂
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hlog : Real.log h - Real.log k = Real.log ((g * h : ℕ) : ℝ) - Real.log ((g * k : ℕ) : ℝ) := by
    push_cast
    rw [Real.log_mul hgR.ne' hhR.ne', Real.log_mul hgR.ne' hkR.ne']
    ring
  have hsq : (Real.sqrt ((h : ℝ) * k))⁻¹ =
      (g : ℝ) / Real.sqrt (((g * h : ℕ) : ℝ) * ((g * k : ℕ) : ℝ)) := by
    push_cast
    rw [show (g : ℝ) * h * (g * k) = (g : ℝ) ^ 2 * (h * k) by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ (g : ℝ) ^ 2 by positivity) ((h : ℝ) * k),
      Real.sqrt_sq hgR.le]
    have : 0 < Real.sqrt ((h : ℝ) * k) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  rw [hlog, hsq] at hE
  refine hE.trans ?_
  have hhm : (h : ℝ) * k ≤ ((g * h : ℕ) : ℝ) * ((g * k : ℕ) : ℝ) := by
    push_cast
    have h1g : (1 : ℝ) ≤ g := by exact_mod_cast hg0
    have hhk : 0 ≤ (h : ℝ) * k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul h1g h1g zero_le_one (by linarith)) hhk]
  have hL0 : 0 ≤ L := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhm hC) hL0

/-! ## The coefficient `B(c, m)` -/

/-- The main-term coefficient of the `n`-th twist. -/
def coeffTerm (c : ℝ) (m n : ℕ) : ℝ :=
  (1 + c ^ 2) / Real.sqrt n + c / Real.sqrt ((m : ℝ) * n) +
    c * (Nat.gcd m n : ℝ) / Real.sqrt ((m : ℝ) * n)

theorem abs_coeffTerm_le {c : ℝ} (hc : |c| ≤ 1) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    |coeffTerm c m n| ≤ 4 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 1 ≤ Real.sqrt n := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hnR
  have hsmn : 1 ≤ Real.sqrt ((m : ℝ) * n) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hg : (Nat.gcd m n : ℝ) ≤ Real.sqrt ((m : ℝ) * n) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have h1 : (Nat.gcd m n : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left m n)
    have h2 : (Nat.gcd m n : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right m n)
    have h0 : (0 : ℝ) ≤ Nat.gcd m n := Nat.cast_nonneg _
    nlinarith
  have hc' := abs_le.mp hc
  have hspn : 0 < Real.sqrt n := by linarith
  have hspmn : 0 < Real.sqrt ((m : ℝ) * n) := by linarith
  have t1 : |(1 + c ^ 2) / Real.sqrt n| ≤ 2 := by
    rw [abs_div, abs_of_pos hspn, abs_of_pos (by positivity : (0 : ℝ) < 1 + c ^ 2),
      div_le_iff₀ hspn]
    nlinarith
  have t2 : |c / Real.sqrt ((m : ℝ) * n)| ≤ 1 := by
    rw [abs_div, abs_of_pos hspmn, div_le_iff₀ hspmn]; linarith
  have t3 : |c * (Nat.gcd m n : ℝ) / Real.sqrt ((m : ℝ) * n)| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos hspmn, Nat.abs_cast, div_le_iff₀ hspmn]
    calc |c| * (Nat.gcd m n : ℝ) ≤ 1 * Real.sqrt ((m : ℝ) * n) :=
          mul_le_mul hc hg (Nat.cast_nonneg _) zero_le_one
      _ = 1 * Real.sqrt ((m : ℝ) * n) := rfl
  unfold coeffTerm
  calc _ ≤ |(1 + c ^ 2) / Real.sqrt n| + |c / Real.sqrt ((m : ℝ) * n)| +
        |c * (Nat.gcd m n : ℝ) / Real.sqrt ((m : ℝ) * n)| := abs_add_three _ _ _
    _ ≤ 4 := by linarith

/-- `B(c, m) = 1 + c² + 2c m^{−1/2} − Σ_n a(n) n^{−1/2} coeffTerm(c, m, n)`. -/
def coeffB (a : ℕ → ℝ) (c : ℝ) (m : ℕ) : ℝ :=
  1 + c ^ 2 + 2 * c / Real.sqrt m - ∑' n, a n / Real.sqrt n * coeffTerm c m n

/-- The truncation of `B`. -/
def coeffBN (a : ℕ → ℝ) (c : ℝ) (m N : ℕ) : ℝ :=
  1 + c ^ 2 + 2 * c / Real.sqrt m - ∑ n ∈ Finset.range N, a n / Real.sqrt n * coeffTerm c m n

/-- The truncated real part `Σ_{n < N} a(n) n^{−1/2} cos(t log n)`. -/
def reAN (a : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, a n / Real.sqrt n * Real.cos (Real.log n * t)

/-- The tail `Σ_{n ≥ N} |a(n)| n^{−1/2}`. -/
def tailN (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑' n, |a (n + N) / Real.sqrt (n + N : ℕ)|

theorem tailN_nonneg (a : ℕ → ℝ) (N : ℕ) : 0 ≤ tailN a N := tsum_nonneg fun _ => abs_nonneg _

theorem tendsto_tailN (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) :
    Tendsto (tailN a) atTop (𝓝 0) := by
  have hs := summable_coeff_line hδ ha
  exact tendsto_sum_nat_add (f := fun n => |a n / Real.sqrt n|)

theorem abs_re_sub_reAN_le (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (N : ℕ) (t : ℝ) :
    |(dilSeries a (linePt t)).re - reAN a N t| ≤ tailN a N := by
  have hs := summable_coeff_line hδ ha
  have hsc : Summable fun n => a n / Real.sqrt n * Real.cos (Real.log n * t) :=
    Summable.of_norm_bounded hs fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [re_dilSeries_line hδ ha, reAN, ← hsc.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hs' : Summable fun n => |a (n + N) / Real.sqrt ((n + N : ℕ) : ℝ)| :=
    (summable_nat_add_iff N).mpr hs
  have hFG : ∀ n, ‖a (n + N) / Real.sqrt ((n + N : ℕ) : ℝ) *
      Real.cos (Real.log ((n + N : ℕ) : ℝ) * t)‖ ≤ |a (n + N) / Real.sqrt ((n + N : ℕ) : ℝ)| := by
    intro n
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hF : Summable fun n => ‖a (n + N) / Real.sqrt ((n + N : ℕ) : ℝ) *
      Real.cos (Real.log ((n + N : ℕ) : ℝ) * t)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hFG hs'
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hF).trans (Summable.tsum_le_tsum hFG hF hs')

theorem abs_coeffB_sub_coeffBN_le (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) {c : ℝ} (hc : |c| ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) (N : ℕ) : |coeffB a c m - coeffBN a c m N| ≤ 4 * tailN a N := by
  have hs := summable_coeff_line hδ ha
  have hbound : ∀ n, |a n / Real.sqrt n * coeffTerm c m n| ≤ 4 * |a n / Real.sqrt n| := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_coeffTerm_le hc hm hn) (abs_nonneg _)
  have hsc : Summable fun n => a n / Real.sqrt n * coeffTerm c m n :=
    Summable.of_norm_bounded (hs.mul_left 4) fun n => by rw [Real.norm_eq_abs]; exact hbound n
  unfold coeffB coeffBN
  rw [← hsc.sum_add_tsum_nat_add N]
  have e : 1 + c ^ 2 + 2 * c / Real.sqrt m - (∑ n ∈ Finset.range N, a n / Real.sqrt n *
      coeffTerm c m n + ∑' n, a (n + N) / Real.sqrt (n + N : ℕ) * coeffTerm c m (n + N)) -
      (1 + c ^ 2 + 2 * c / Real.sqrt m - ∑ n ∈ Finset.range N, a n / Real.sqrt n *
        coeffTerm c m n) = -∑' n, a (n + N) / Real.sqrt (n + N : ℕ) * coeffTerm c m (n + N) := by
    ring
  rw [e, abs_neg, tailN, ← tsum_mul_left]
  have hs' := (summable_nat_add_iff N).mpr hs
  refine (norm_tsum_le_tsum_norm ((summable_nat_add_iff N).mpr hsc).norm).trans ?_
  exact Summable.tsum_le_tsum (fun n => hbound (n + N)) ((summable_nat_add_iff N).mpr hsc).norm
    (hs'.mul_left 4)

/-! ## The cosine expansion -/

theorem div_sqrt_zero (a : ℕ → ℝ) : a 0 / Real.sqrt ((0 : ℕ) : ℝ) = 0 := by simp

/-- `W (1 − A_N) = (1+c²) + 2c cos(t log m) − Σ_{n<N} a(n) n^{−1/2}[(1+c²) cos(t log n)
+ c cos(t log mn) + c cos(t (log m − log n))]`. -/
theorem twoPointWeight_mul_one_sub_reAN (a : ℕ → ℝ) (c : ℝ) {m : ℕ} (hm : 1 ≤ m) (N : ℕ)
    (t : ℝ) :
    twoPointWeight c m t * (1 - reAN a N t) =
      (1 + c ^ 2) * Real.cos ((Real.log (1 : ℕ) - Real.log (1 : ℕ)) * t) +
        2 * c * Real.cos ((Real.log m - Real.log (1 : ℕ)) * t) -
        ∑ n ∈ Finset.range N, a n / Real.sqrt n *
          ((1 + c ^ 2) * Real.cos ((Real.log n - Real.log (1 : ℕ)) * t) +
            c * Real.cos ((Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) * t) +
            c * Real.cos ((Real.log m - Real.log n) * t)) := by
  unfold twoPointWeight reAN
  simp only [Nat.cast_one, Real.log_one, sub_self, zero_mul, Real.cos_zero, mul_one, sub_zero]
  rw [mul_sub, mul_one, Finset.mul_sum]
  have hterm : ∀ n ∈ Finset.range N,
      (1 + c ^ 2 + 2 * c * Real.cos (t * Real.log m)) *
        (a n / Real.sqrt n * Real.cos (Real.log n * t)) =
      a n / Real.sqrt n * ((1 + c ^ 2) * Real.cos (Real.log n * t) +
        c * Real.cos (Real.log ((m * n : ℕ) : ℝ) * t) +
        c * Real.cos ((Real.log m - Real.log n) * t)) := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : Real.log ((m * n : ℕ) : ℝ) = Real.log m + Real.log n := by
      push_cast; exact Real.log_mul hmR.ne' hnR.ne'
    have key : 2 * Real.cos (t * Real.log m) * Real.cos (Real.log n * t) =
        Real.cos ((Real.log m + Real.log n) * t) + Real.cos ((Real.log m - Real.log n) * t) := by
      rw [show (Real.log m + Real.log n) * t = Real.log m * t + Real.log n * t by ring,
        show (Real.log m - Real.log n) * t = Real.log m * t - Real.log n * t by ring,
        Real.cos_add, Real.cos_sub, mul_comm t (Real.log m)]
      ring
    rw [hlog]
    linear_combination (a n / Real.sqrt n * c) * key
  rw [Finset.sum_congr rfl hterm]
  ring_nf

theorem integrable_win_zsq_cos {L : ℝ} (hL : 0 < L) (ξ : ℝ) :
    Integrable fun t => win L t * zsq t * Real.cos (ξ * t) := by
  have h := integrable_win_mul hL (g := fun t => zsq t * Real.cos (ξ * t))
    (continuous_zsq.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only; ring

/-- **The truncated integral as a combination of twisted moments.** -/
theorem integral_truncated_eq (a : ℕ → ℝ) {L : ℝ} (hL : 0 < L) (c : ℝ) {m : ℕ} (hm : 1 ≤ m)
    (N : ℕ) :
    ∫ t, win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t) =
      (1 + c ^ 2) * momentRe L (Real.log (1 : ℕ) - Real.log (1 : ℕ)) +
        2 * c * momentRe L (Real.log m - Real.log (1 : ℕ)) -
        ∑ n ∈ Finset.range N, a n / Real.sqrt n *
          ((1 + c ^ 2) * momentRe L (Real.log n - Real.log (1 : ℕ)) +
            c * momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) +
            c * momentRe L (Real.log m - Real.log n)) := by
  have hI := integrable_win_zsq_cos hL
  set F : ℝ → ℝ → ℝ := fun ξ t => win L t * zsq t * Real.cos (ξ * t) with hF
  have hpt : (fun t => win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t)) =
      fun t => (1 + c ^ 2) * F (Real.log (1 : ℕ) - Real.log (1 : ℕ)) t +
        2 * c * F (Real.log m - Real.log (1 : ℕ)) t -
        ∑ n ∈ Finset.range N, a n / Real.sqrt n *
          ((1 + c ^ 2) * F (Real.log n - Real.log (1 : ℕ)) t +
            c * F (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) t +
            c * F (Real.log m - Real.log n) t) := by
    funext t
    have e0 : win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t) =
        (win L t * zsq t) * (twoPointWeight c m t * (1 - reAN a N t)) := by ring
    rw [e0, twoPointWeight_mul_one_sub_reAN a c hm N t, mul_sub, Finset.mul_sum]
    simp only [hF]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun n _ => by ring
  have hF : ∀ ξ, Integrable (F ξ) := fun ξ => hI ξ
  have hIn : ∀ n, Integrable fun t => a n / Real.sqrt n *
      ((1 + c ^ 2) * F (Real.log n - Real.log (1 : ℕ)) t +
        c * F (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) t +
        c * F (Real.log m - Real.log n) t) := fun n =>
    ((((hF _).const_mul _).add ((hF _).const_mul _)).add ((hF _).const_mul _)).const_mul _
  have h0 : Integrable fun t => (1 + c ^ 2) * F (Real.log (1 : ℕ) - Real.log (1 : ℕ)) t :=
    (hF _).const_mul _
  have h1 : Integrable fun t => 2 * c * F (Real.log m - Real.log (1 : ℕ)) t := (hF _).const_mul _
  have h01 : Integrable fun t => (1 + c ^ 2) * F (Real.log (1 : ℕ) - Real.log (1 : ℕ)) t +
      2 * c * F (Real.log m - Real.log (1 : ℕ)) t := h0.add h1
  have hS : Integrable fun t => ∑ n ∈ Finset.range N, a n / Real.sqrt n *
      ((1 + c ^ 2) * F (Real.log n - Real.log (1 : ℕ)) t +
        c * F (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) t +
        c * F (Real.log m - Real.log n) t) := integrable_finsetSum _ fun n _ => hIn n
  rw [hpt, integral_sub h01 hS, integral_add h0 h1, integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun n _ => hIn n]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have g1 : Integrable fun t => (1 + c ^ 2) * F (Real.log n - Real.log (1 : ℕ)) t :=
    (hF _).const_mul _
  have g2 : Integrable fun t => c * F (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) t :=
    (hF _).const_mul _
  have g3 : Integrable fun t => c * F (Real.log m - Real.log n) t := (hF _).const_mul _
  have g12 : Integrable fun t => (1 + c ^ 2) * F (Real.log n - Real.log (1 : ℕ)) t +
      c * F (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) t := g1.add g2
  rw [integral_const_mul, integral_add g12 g3, integral_add g1 g2, integral_const_mul,
    integral_const_mul, integral_const_mul]
  rfl

theorem abs_add_sub_le (x y z : ℝ) : |x + y - z| ≤ |x| + |y| + |z| := by
  have h1 := abs_sub (x + y) z
  have h2 := abs_add_le x y
  linarith

/-! ## Main term of the truncated integral -/

/-- The error weight `E_N = 2 + 2m + Σ_{n<N} |a(n)| n^{−1/2} · 4mn`. -/
def errN (a : ℕ → ℝ) (m N : ℕ) : ℝ :=
  2 + 2 * m + ∑ n ∈ Finset.range N, |a n / Real.sqrt n| * (4 * m * n)

theorem errN_nonneg (a : ℕ → ℝ) (m N : ℕ) : 0 ≤ errN a m N := by
  unfold errN
  have : 0 ≤ ∑ n ∈ Finset.range N, |a n / Real.sqrt n| * (4 * m * n) :=
    Finset.sum_nonneg fun n _ => by positivity
  positivity

/-- **The truncated integral against its main term**:
`|∫ ω_L W (1 − A_N) Z − B_N(c, m) W(L)| ≤ C L E_N`. -/
theorem exists_abs_integral_truncated_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℝ) {c : ℝ}, |c| ≤ 1 → ∀ {m : ℕ}, 1 ≤ m → ∀ (N : ℕ) {L : ℝ},
      16 ≤ L →
      |(∫ t, win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t)) -
          coeffBN a c m N * (ZetaNotch.logWindow L).re| ≤ C * L * errN a m N := by
  obtain ⟨C, hC, hmain⟩ := exists_abs_momentRe_log_sub_le
  refine ⟨C, hC, fun a {c} hc {m} hm N {L} hL => ?_⟩
  have hL0 : 0 < L := by linarith
  have hc' := abs_le.mp hc
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- the individual twists
  have e11 := hmain hL (m₁ := 1) (m₂ := 1) one_pos one_pos
  have em1 := hmain hL (m₁ := m) (m₂ := 1) (by omega) one_pos
  simp only [Nat.gcd_one_right, Nat.cast_one, mul_one, Real.sqrt_one,
    div_one, one_mul] at e11 em1
  set Wl := (ZetaNotch.logWindow L).re
  rw [integral_truncated_eq a hL0 c hm N]
  have hterm : ∀ n ∈ Finset.range N,
      |a n / Real.sqrt n * ((1 + c ^ 2) * momentRe L (Real.log n - Real.log (1 : ℕ)) +
          c * momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) +
          c * momentRe L (Real.log m - Real.log n)) -
        a n / Real.sqrt n * coeffTerm c m n * Wl| ≤
      C * L * (|a n / Real.sqrt n| * (4 * m * n)) := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have en1 := hmain hL (m₁ := n) (m₂ := 1) hn one_pos
    have emn := hmain hL (m₁ := m * n) (m₂ := 1) (Nat.mul_pos (by omega) hn) one_pos
    have emn' := hmain hL (m₁ := m) (m₂ := n) (by omega) hn
    simp only [Nat.gcd_one_right, Nat.cast_one, mul_one] at en1 emn
    have hsq : Real.sqrt (((m * n : ℕ) : ℝ)) = Real.sqrt ((m : ℝ) * n) := by push_cast; rfl
    rw [hsq] at emn
    have hdiff : a n / Real.sqrt n * ((1 + c ^ 2) * momentRe L (Real.log n - Real.log (1 : ℕ)) +
          c * momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) +
          c * momentRe L (Real.log m - Real.log n)) -
        a n / Real.sqrt n * coeffTerm c m n * Wl =
        a n / Real.sqrt n * ((1 + c ^ 2) * (momentRe L (Real.log n - Real.log (1 : ℕ)) -
            1 / Real.sqrt n * Wl) +
          c * (momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) -
            1 / Real.sqrt ((m : ℝ) * n) * Wl) +
          c * (momentRe L (Real.log m - Real.log n) -
            (Nat.gcd m n : ℝ) / Real.sqrt ((m : ℝ) * n) * Wl)) := by
      unfold coeffTerm; ring
    rw [hdiff, abs_mul]
    have hmnR : ((m * n : ℕ) : ℝ) = (m : ℝ) * n := by push_cast; ring
    rw [hmnR] at emn
    have b1 : |(1 + c ^ 2) * (momentRe L (Real.log n - Real.log (1 : ℕ)) - 1 / Real.sqrt n * Wl)|
        ≤ 2 * (C * (n : ℝ) * L) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + c ^ 2)]
      have : 1 + c ^ 2 ≤ 2 := by nlinarith
      exact mul_le_mul this (by simpa using en1) (abs_nonneg _) (by norm_num)
    have b2 : |c * (momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) -
        1 / Real.sqrt ((m : ℝ) * n) * Wl)| ≤ 1 * (C * ((m : ℝ) * n) * L) := by
      rw [abs_mul]
      exact mul_le_mul hc (by simpa using emn) (abs_nonneg _) zero_le_one
    have b3 : |c * (momentRe L (Real.log m - Real.log n) -
        (Nat.gcd m n : ℝ) / Real.sqrt ((m : ℝ) * n) * Wl)| ≤ 1 * (C * ((m : ℝ) * n) * L) := by
      rw [abs_mul]
      exact mul_le_mul hc emn' (abs_nonneg _) zero_le_one
    have hnm : (n : ℝ) ≤ (m : ℝ) * n := by nlinarith
    have hY : |(1 + c ^ 2) * (momentRe L (Real.log n - Real.log (1 : ℕ)) - 1 / Real.sqrt n * Wl) +
          c * (momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) -
            1 / Real.sqrt ((m : ℝ) * n) * Wl) +
          c * (momentRe L (Real.log m - Real.log n) -
            (Nat.gcd m n : ℝ) / Real.sqrt ((m : ℝ) * n) * Wl)| ≤ C * L * (4 * m * n) := by
      calc _ ≤ |(1 + c ^ 2) * (momentRe L (Real.log n - Real.log (1 : ℕ)) - 1 / Real.sqrt n * Wl)|
            + |c * (momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) -
              1 / Real.sqrt ((m : ℝ) * n) * Wl)| +
            |c * (momentRe L (Real.log m - Real.log n) -
              (Nat.gcd m n : ℝ) / Real.sqrt ((m : ℝ) * n) * Wl)| := abs_add_three _ _ _
        _ ≤ 2 * (C * (n : ℝ) * L) + 1 * (C * ((m : ℝ) * n) * L) + 1 * (C * ((m : ℝ) * n) * L) := by
            linarith
        _ ≤ C * L * (4 * m * n) := by
            have : 0 ≤ C * L := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hnm this]
    calc |a n / Real.sqrt n| * _ ≤ |a n / Real.sqrt n| * (C * L * (4 * m * n)) :=
          mul_le_mul_of_nonneg_left hY (abs_nonneg _)
      _ = C * L * (|a n / Real.sqrt n| * (4 * m * n)) := by ring
  have hsplit : ((1 + c ^ 2) * momentRe L (Real.log (1 : ℕ) - Real.log (1 : ℕ)) +
        2 * c * momentRe L (Real.log m - Real.log (1 : ℕ)) -
        ∑ n ∈ Finset.range N, a n / Real.sqrt n *
          ((1 + c ^ 2) * momentRe L (Real.log n - Real.log (1 : ℕ)) +
            c * momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) +
            c * momentRe L (Real.log m - Real.log n))) - coeffBN a c m N * Wl =
      (1 + c ^ 2) * (momentRe L (Real.log (1 : ℕ) - Real.log (1 : ℕ)) - Wl) +
        2 * c * (momentRe L (Real.log m - Real.log (1 : ℕ)) - 1 / Real.sqrt m * Wl) -
        ∑ n ∈ Finset.range N, (a n / Real.sqrt n *
          ((1 + c ^ 2) * momentRe L (Real.log n - Real.log (1 : ℕ)) +
            c * momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) +
            c * momentRe L (Real.log m - Real.log n)) - a n / Real.sqrt n * coeffTerm c m n * Wl) := by
    unfold coeffBN
    rw [Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
    ring
  rw [hsplit]
  have hs : |∑ n ∈ Finset.range N, (a n / Real.sqrt n *
          ((1 + c ^ 2) * momentRe L (Real.log n - Real.log (1 : ℕ)) +
            c * momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) +
            c * momentRe L (Real.log m - Real.log n)) - a n / Real.sqrt n * coeffTerm c m n * Wl)| ≤
      C * L * ∑ n ∈ Finset.range N, |a n / Real.sqrt n| * (4 * m * n) := by
    rw [Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
  have h1 : |(1 + c ^ 2) * (momentRe L (Real.log (1 : ℕ) - Real.log (1 : ℕ)) - Wl)| ≤ 2 * (C * L) := by
    simp only [Nat.cast_one]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + c ^ 2)]
    have : 1 + c ^ 2 ≤ 2 := by nlinarith
    exact mul_le_mul this (by simpa using e11) (abs_nonneg _) (by norm_num)
  have h2 : |2 * c * (momentRe L (Real.log m - Real.log (1 : ℕ)) - 1 / Real.sqrt m * Wl)| ≤
      2 * (C * m * L) := by
    simp only [Nat.cast_one]
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul hc em1 (abs_nonneg _) zero_le_one
    nlinarith
  unfold errN
  have hCL : 0 ≤ C * L := by positivity
  calc _ ≤ |(1 + c ^ 2) * (momentRe L (Real.log (1 : ℕ) - Real.log (1 : ℕ)) - Wl)| +
        |2 * c * (momentRe L (Real.log m - Real.log (1 : ℕ)) - 1 / Real.sqrt m * Wl)| +
        |∑ n ∈ Finset.range N, (a n / Real.sqrt n *
          ((1 + c ^ 2) * momentRe L (Real.log n - Real.log (1 : ℕ)) +
            c * momentRe L (Real.log ((m * n : ℕ) : ℝ) - Real.log (1 : ℕ)) +
            c * momentRe L (Real.log m - Real.log n)) - a n / Real.sqrt n * coeffTerm c m n * Wl)| :=
        abs_add_sub_le _ _ _
    _ ≤ 2 * (C * L) + 2 * (C * m * L) + C * L * ∑ n ∈ Finset.range N, |a n / Real.sqrt n| * (4 * m * n) :=
        add_le_add (add_le_add h1 h2) hs
    _ = C * L * (2 + 2 * m + ∑ n ∈ Finset.range N, |a n / Real.sqrt n| * (4 * m * n)) := by ring

/-! ## The tail of the dilation series -/

theorem continuous_reAN (a : ℕ → ℝ) (N : ℕ) : Continuous (reAN a N) := by
  unfold reAN
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))

/-- `|∫ ω W (1 − Re A) Z − ∫ ω W (1 − A_N) Z| ≤ 4 τ_N ∫ ω Z`. -/
theorem abs_integral_sub_truncated_le (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) {L : ℝ} (hL : 0 < L)
    {c : ℝ} (hc : |c| ≤ 1) (m N : ℕ) :
    |(∫ t, win L t * (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) * zsq t)) -
        ∫ t, win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t)| ≤
      4 * tailN a N * ∫ t, win L t * zsq t := by
  have cR : Continuous fun t : ℝ => (dilSeries a (linePt t)).re :=
    Complex.continuous_re.comp (continuous_dilSeries_line hδ ha)
  have cW := continuous_twoPointWeight c m
  have i1 : Integrable fun t => win L t *
      (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) * zsq t) :=
    integrable_win_mul hL ((cW.mul (continuous_const.sub cR)).mul continuous_zsq)
  have i2 : Integrable fun t => win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t) :=
    integrable_win_mul hL ((cW.mul (continuous_const.sub (continuous_reAN a N))).mul continuous_zsq)
  have i3 : Integrable fun t => 4 * tailN a N * (win L t * zsq t) :=
    (integrable_win_mul hL continuous_zsq).const_mul _
  rw [← integral_sub i1 i2, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono (i1.sub i2).abs i3 fun t => ?_)
  have hw := blockWindow_nonneg L (2 * L) (L / 2) t
  have hW0 := twoPointWeight_nonneg hc m t
  have hW1 := twoPointWeight_le hc m t
  have hz := zsq_nonneg t
  have hd := abs_re_sub_reAN_le hδ ha N t
  have e : win L t * (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) * zsq t) -
      win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t) =
      win L t * twoPointWeight c m t * zsq t * (reAN a N t - (dilSeries a (linePt t)).re) := by ring
  rw [e, abs_mul, abs_of_nonneg (by positivity), abs_sub_comm]
  have hτ := tailN_nonneg a N
  calc win L t * twoPointWeight c m t * zsq t * |(dilSeries a (linePt t)).re - reAN a N t|
      ≤ win L t * 4 * zsq t * tailN a N := by gcongr
    _ = 4 * tailN a N * (win L t * zsq t) := by ring

/-! ## `B(c, m) ≥ 0` -/

theorem momentRe_zero_eq (L : ℝ) : momentRe L 0 = ∫ t, win L t * zsq t := by
  unfold momentRe; simp

/-- **`B(c, m) ≥ 0`** for `|c| ≤ 1`, `m ≥ 1`. -/
theorem coeffB_nonneg (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v))
    {SE : ℝ} (hEb : ∀ t, ‖E (linePt t)‖ ≤ SE) {c : ℝ} (hc : |c| ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ coeffB a c m := by
  by_contra hneg
  push Not at hneg
  set β := -coeffB a c m with hβdef
  have hβ : 0 < β := by linarith
  obtain ⟨K, hK⟩ := exists_averaged_ge hδ ha hf hf1 hv hW hEb hc hm
  obtain ⟨C, hC, hmainN⟩ := exists_abs_integral_truncated_sub_le
  obtain ⟨K₀, hK₀, hmom⟩ := exists_momentRe_zero_le
  have hτpos : 0 < β / (16 * (4 + K₀)) := by positivity
  obtain ⟨N, hN⟩ := ((tendsto_order.1 (tendsto_tailN hδ ha)).2 _ hτpos).exists
  set τ := tailN a N with hτdef
  have hτ0 : 0 ≤ τ := tailN_nonneg a N
  set E := errN a m N
  have hE0 : 0 ≤ E := errN_nonneg a m N
  -- a large aperture
  obtain ⟨L, hL32, hLlog⟩ : ∃ L : ℝ, 32 ≤ L ∧ (4 * (K + C * E) + 1) / β < Real.log L := by
    obtain ⟨L, hL⟩ := ((Real.tendsto_log_atTop.eventually_gt_atTop ((4 * (K + C * E) + 1) / β)).and
      (eventually_ge_atTop (32 : ℝ))).exists
    exact ⟨L, hL.2, hL.1⟩
  have hL0 : 0 < L := by linarith
  have hL16 : 16 ≤ L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  set Wl := (ZetaNotch.logWindow L).re
  have hWl : L * Real.log L ≤ Wl := WeilFiniteSupport.re_logWindow_ge (by linarith)
  have hI := hK hL32
  have hTr := abs_integral_sub_truncated_le hδ ha hL0 hc m N
  have hMain : |(∫ t, win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t)) -
      coeffBN a c m N * (ZetaNotch.logWindow L).re| ≤ C * L * errN a m N := hmainN a hc hm N hL16
  have hBN := abs_coeffB_sub_coeffBN_le hδ ha hc hm N
  have hM0 : ∫ t, win L t * zsq t ≤ K₀ * L * Real.log L := by
    rw [← momentRe_zero_eq]; exact hmom hL16
  set I := ∫ t, win L t * (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) * zsq t)
  set IN := ∫ t, win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t)
  have h1 : I ≤ IN + 4 * τ * (K₀ * L * Real.log L) := by
    have := (abs_le.mp hTr).2
    have h4 : 4 * τ * ∫ t, win L t * zsq t ≤ 4 * τ * (K₀ * L * Real.log L) :=
      mul_le_mul_of_nonneg_left hM0 (by positivity)
    linarith
  have h2 : IN ≤ coeffBN a c m N * Wl + C * L * E := by
    have := (abs_le.mp hMain).2; linarith
  have h3 : coeffBN a c m N ≤ -β + 4 * τ := by
    have := (abs_le.mp hBN).1; linarith
  have hτ1 : 4 * τ ≤ β / 2 := by
    have : τ ≤ β / (16 * (4 + K₀)) := hN.le
    have h' : β / (16 * (4 + K₀)) ≤ β / 64 := div_le_div_of_nonneg_left hβ.le (by norm_num) (by nlinarith)
    linarith
  have hτ2 : 4 * τ * K₀ ≤ β / 4 := by
    have : τ ≤ β / (16 * (4 + K₀)) := hN.le
    have h' : 4 * τ * K₀ ≤ 4 * (β / (16 * (4 + K₀))) * K₀ := by
      have := mul_le_mul_of_nonneg_right this hK₀; nlinarith
    have h'' : 4 * (β / (16 * (4 + K₀))) * K₀ ≤ β / 4 := by
      rw [show 4 * (β / (16 * (4 + K₀))) * K₀ = β / 4 * (K₀ / (4 + K₀)) by field_simp; ring]
      have : K₀ / (4 + K₀) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      nlinarith
    linarith
  have hWl0 : 0 ≤ Wl := le_trans (by positivity) hWl
  have h4 : coeffBN a c m N * Wl ≤ -(β / 2) * (L * Real.log L) := by
    have : coeffBN a c m N ≤ -(β / 2) := by linarith
    have hb2 : 0 ≤ β / 2 := by positivity
    nlinarith
  have hLL : 0 < L * Real.log L := by positivity
  have hfin : β / 4 * (L * Real.log L) ≤ (K + C * E) * L := by
    have := hI
    have hτK : 4 * τ * (K₀ * L * Real.log L) ≤ β / 4 * (L * Real.log L) := by
      have := mul_le_mul_of_nonneg_right hτ2 hLL.le
      nlinarith
    nlinarith
  have hcontra : β / 4 * Real.log L ≤ K + C * E := by
    have := hfin
    rw [show β / 4 * (L * Real.log L) = (β / 4 * Real.log L) * L by ring] at this
    exact le_of_mul_le_mul_right this hL0
  have hlog' : 4 * (K + C * E) + 1 < β * Real.log L := by
    rw [div_lt_iff₀ hβ] at hLlog; linarith
  linarith

/-! ## The gcd identity and the theorem -/

theorem summable_a_div (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) :
    Summable fun n => |a n| / Real.sqrt n := by
  refine (summable_coeff_line hδ ha).congr fun n => ?_
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem summable_a_gcd_div (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) {m : ℕ} (hm : 0 < m) :
    Summable fun n => a n * (Nat.gcd m n : ℝ) / n := by
  refine Summable.of_norm_bounded ((summable_a_div hδ ha).mul_left (m + 1 : ℝ)) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hg : (Nat.gcd m n : ℝ) ≤ m + 1 := by
    have : Nat.gcd m n ≤ m + 1 := (Nat.gcd_le_left n hm).trans (Nat.le_succ m)
    exact_mod_cast this
  rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast, Nat.abs_cast]
  have hsn : Real.sqrt n ≤ n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  calc |a n| * (Nat.gcd m n : ℝ) / n ≤ |a n| * (m + 1) / Real.sqrt n := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hg (abs_nonneg _)) hsn0 hsn
    _ = (m + 1 : ℝ) * (|a n| / Real.sqrt n) := by ring

theorem summable_a_div_n (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) :
    Summable fun n => a n / n := by
  refine (summable_a_gcd_div hδ ha one_pos).congr fun n => ?_
  simp

/-- `A(1) = Σ a(n)/n = 1`. -/
theorem tsum_a_div_eq_one (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v)) :
    ∑' n, a n / n = 1 := by
  have h := dilSeries_one_eq_one hδ ha hf hf1 hv hW
  have hs : LSeriesSummable (fun n => (a n : ℂ)) 1 := summable_of_le_re ha (by simp; linarith)
  have hre := congrArg Complex.re h
  unfold dilSeries LSeries at hre
  rw [Complex.re_tsum hs, Complex.one_re] at hre
  rw [← hre]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn.ne', Complex.cpow_one, ← Complex.ofReal_natCast,
    ← Complex.ofReal_div, Complex.ofReal_re]

/-- `B(c, m) = (1 + c²)(1 − Σ a(n)/n) + (c/√m)(2 − Σ a(n)/n − Σ a(n) gcd(m,n)/n)`. -/
theorem coeffB_eq (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (c : ℝ) {m : ℕ}
    (hm : 1 ≤ m) :
    coeffB a c m = (1 + c ^ 2) * (1 - ∑' n, a n / n) +
      c / Real.sqrt m * (2 - ∑' n, a n / n - ∑' n, a n * (Nat.gcd m n : ℝ) / n) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  have hpt : ∀ n, a n / Real.sqrt n * coeffTerm c m n =
      (1 + c ^ 2) * (a n / n) + c / Real.sqrt m * (a n / n + a n * (Nat.gcd m n : ℝ) / n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
    have hnn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnR.le
    unfold coeffTerm
    rw [Real.sqrt_mul hmR.le]
    generalize Real.sqrt (n : ℝ) = r at hnn hsn ⊢
    rw [← hnn]
    field_simp
    ring
  have hu := summable_a_div_n hδ ha
  have hg := summable_a_gcd_div hδ ha (by omega : 0 < m)
  unfold coeffB
  rw [tsum_congr hpt, Summable.tsum_add (hu.mul_left _) ((hu.add hg).mul_left _), tsum_mul_left,
    tsum_mul_left, Summable.tsum_add hu hg]
  field_simp
  ring

/-- **`Σ_n a(n) gcd(m, n)/n = 1`** for every `m ≥ 1`. -/
theorem tsum_a_gcd_div_eq_one (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v))
    {SE : ℝ} (hEb : ∀ t, ‖E (linePt t)‖ ≤ SE) {m : ℕ} (hm : 1 ≤ m) :
    ∑' n, a n * (Nat.gcd m n : ℝ) / n = 1 := by
  have hS1 := tsum_a_div_eq_one hδ ha hf hf1 hv hW
  have h1 := coeffB_nonneg hδ ha hf hf1 hv hW hEb (c := 1) (by norm_num) hm
  have h2 := coeffB_nonneg hδ ha hf hf1 hv hW hEb (c := -1) (by norm_num) hm
  rw [coeffB_eq hδ ha _ hm, hS1] at h1 h2
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  set G := ∑' n, a n * (Nat.gcd m n : ℝ) / n
  have h1' : 0 ≤ 1 - G := by
    have : 0 ≤ 1 / Real.sqrt m * (2 - 1 - G) := by linarith
    have := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 1 / Real.sqrt m)).mp this
    linarith
  have h2' : 0 ≤ G - 1 := by
    have : 0 ≤ 1 / Real.sqrt m * (G - 1) := by
      have e : (1 + (-1 : ℝ) ^ 2) * (1 - 1) + -1 / Real.sqrt m * (2 - 1 - G) =
          1 / Real.sqrt m * (G - 1) := by ring
      linarith
    exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 1 / Real.sqrt m)).mp this
  linarith

/-- **Dilation rigidity in the presence of a Möbius part.** If `Λ ⋆ a + μ ⋆ f + v` is full-cone
Weil-positive, with `a`, `f` absolutely convergent past `½` (`f(1) = 0`) and `v` regular with
continuation bounded on the critical line, then `a = δ₁`. -/
theorem eq_delta_of_weilPositiveFull (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v))
    {SE : ℝ} (hEb : ∀ t, ‖E (linePt t)‖ ≤ SE) :
    a 1 = 1 ∧ ∀ n, 2 ≤ n → a n = 0 := by
  classical
  set b : ℕ → ℝ := fun n => a n - if n = 1 then 1 else 0 with hb
  have hbs : Summable fun n => |b n| / Real.sqrt n := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_a_div hδ ha).add (summable_of_ne_finset_zero (s := {1})
        (f := fun n : ℕ => if n = 1 then (1 : ℝ) else 0) fun n hn => by simp at hn; simp [hn]))
    by_cases h1 : n = 1
    · subst h1
      simp only [hb, ite_true, Nat.cast_one, Real.sqrt_one, div_one]
      have := abs_sub (a 1) 1
      rw [abs_one] at this
      linarith
    · simp only [hb, if_neg h1, sub_zero, add_zero, le_refl]
  have hzero : ∀ m, 0 < m → ∑' n, b n * (Nat.gcd m n : ℝ) / n = 0 := by
    intro m hm
    have hG := tsum_a_gcd_div_eq_one hδ ha hf hf1 hv hW hEb (m := m) hm
    have hδs : Summable fun n : ℕ => (if n = 1 then (1 : ℝ) else 0) * (Nat.gcd m n : ℝ) / n :=
      summable_of_ne_finset_zero (s := {1}) fun n hn => by simp at hn; simp [hn]
    have e : (fun n => b n * (Nat.gcd m n : ℝ) / n) = fun n =>
        a n * (Nat.gcd m n : ℝ) / n - (if n = 1 then (1 : ℝ) else 0) * (Nat.gcd m n : ℝ) / n := by
      funext n; simp only [hb]; ring
    rw [e, Summable.tsum_sub (summable_a_gcd_div hδ ha hm) hδs, hG,
      tsum_eq_single 1 (fun n hn => by simp [hn])]
    simp
  have hb0 := eq_zero_of_tsum_gcd_mul_div_eq_zero hbs hzero
  refine ⟨?_, fun n hn => ?_⟩
  · have := hb0 1 one_pos
    simp only [hb, ite_true] at this
    linarith
  · have := hb0 n (by omega)
    simp only [hb, if_neg (show n ≠ 1 by omega), sub_zero] at this
    exact this

/-! ## Full uniqueness with a finite Möbius part -/

theorem finiteTypeSeq_eq_delta_left {a : ℕ → ℝ} (h1 : a 1 = 1) (h2 : ∀ n, 2 ≤ n → a n = 0)
    (f v : ℕ → ℝ) :
    finiteTypeSeq a f v = finiteTypeSeq (fun n => if n = 1 then 1 else 0) f v := by
  funext n
  unfold finiteTypeSeq
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp0 : p.2 ≠ 0 := by
    obtain ⟨hmul, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    intro h
    rw [h, mul_zero] at hmul
    exact hn hmul.symm
  have hq : a p.2 = if p.2 = 1 then 1 else 0 := by
    split_ifs with h
    · rw [h, h1]
    · exact h2 _ (by omega)
  rw [hq]

theorem lSeriesSummable_of_supportedIn {N : ℕ} {f : ℕ → ℝ} (hf : SupportedIn N f) (s : ℂ) :
    LSeriesSummable (fun n => (f n : ℂ)) s :=
  WeilFiniteType.LSeriesSummable_of_supportedIn hf s

/-- **Uniqueness for infinite dilations with a finite Möbius part.** If `Λ ⋆ a + μ ⋆ f + v` is
full-cone Weil-positive, with `a` absolutely convergent past `½`, `f` finitely supported (`f(1) = 0`)
and `v` regular with continuation bounded on the critical line, then `a = δ₁`, `f = 0`, `v = 0`. -/
theorem eq_delta_and_eq_zero_of_weilPositiveFull (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) {N : ℕ}
    (hfN : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {SE : ℝ} (hEb : ∀ t, ‖E (linePt t)‖ ≤ SE) :
    a 1 = 1 ∧ (∀ n, 2 ≤ n → a n = 0) ∧ (∀ n, f n = 0) ∧ ∀ n, v n = 0 := by
  obtain ⟨h1, h2⟩ := eq_delta_of_weilPositiveFull hδ ha
    (lSeriesSummable_of_supportedIn hfN _) hf1 hv hW hEb
  refine ⟨h1, h2, ?_⟩
  rw [finiteTypeSeq_eq_delta_left h1 h2] at hW
  have hN : SupportedIn (max N 1) f :=
    ⟨hfN.1, fun n hn => hfN.2 n (lt_of_le_of_lt (le_max_left N 1) hn)⟩
  have hδ₁ : SupportedIn (max N 1) (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) :=
    ⟨by simp, fun n hn => if_neg (by omega)⟩
  obtain ⟨-, hf0, hv0⟩ := WeilFiniteType.finiteType_uniqueness hδ₁ hN hf1 hv hW
  exact ⟨hf0, hv0⟩

/-- **Within the class, a Weil-positive completion exists iff RH.** The class consists of
`Λ ⋆ a + μ ⋆ f + v` with `a` absolutely convergent past `½`, `f` finitely supported with `f(1) = 0`,
and `v` regular with continuation bounded on the critical line. -/
theorem exists_weilPositive_iff :
    (∃ (a f v : ℕ → ℝ) (E : ℂ → ℂ) (δ SE : ℝ) (N : ℕ), 0 < δ ∧
      LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) ∧ SupportedIn N f ∧ f 1 = 0 ∧
      RegularPart v E ∧ (∀ t, ‖E (linePt t)‖ ≤ SE) ∧ WeilPositiveFull (finiteTypeSeq a f v)) ↔
      RiemannHypothesis := by
  rw [riemannHypothesis_iff_weilPositiveFull_vonMangoldt]
  constructor
  · rintro ⟨a, f, v, E, δ, SE, N, hδ, ha, hfN, hf1, hv, hEb, hW⟩
    obtain ⟨h1, h2, hf0, hv0⟩ := eq_delta_and_eq_zero_of_weilPositiveFull hδ ha hfN hf1 hv hW hEb
    have hf' : f = fun _ => 0 := funext hf0
    have hv' : v = fun _ => 0 := funext hv0
    rw [finiteTypeSeq_eq_delta_left h1 h2, hf', hv', WeilFiniteType.finiteTypeSeq_delta_zero_zero]
      at hW
    exact hW
  · intro hW
    refine ⟨fun n => if n = 1 then 1 else 0, fun _ => 0, fun _ => 0, fun _ => 0, 1, 0, 1, one_pos,
      ?_, ⟨rfl, fun _ _ => rfl⟩, rfl, WeilFiniteType.regularPart_zero, fun t => by simp, ?_⟩
    · refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
      have : n ≠ 1 := by simpa using hn
      simp [LSeries.term, this]
    · rw [WeilFiniteType.finiteTypeSeq_delta_zero_zero]
      exact hW

end RHTower.WeilZetaSquare
