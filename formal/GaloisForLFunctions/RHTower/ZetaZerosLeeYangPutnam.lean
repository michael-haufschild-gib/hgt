import GaloisForLFunctions.RHTower.ZetaZerosLeeYangDirichletSeries
import GaloisForLFunctions.HTGeometry.HamburgerFunctionalEquation
import GaloisForLFunctions.HTGeometry.RectangleMaxModulus
import GaloisForLFunctions.HTGeometry.EntireBezout
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay
import GaloisForLFunctions.RHTower.SelbergThetaHorizontalBoundary

/-!
# A multi-prime Putnam theorem: the zeros of `ζ` do not contain a Lee–Yang zero set

For real `|a| < 1` let `Y_a(s) = cosh((s − ½) log 6) + a cosh((s − ½) log(3/2))`.  Every zero of
`Y_a` lies on the critical line (`RHTower.LeeYang.re_eq_half_of_leeYang_eq_zero`), where
`Y_a(½ + it) = cos(t log 6) + a cos(t log(3/2))`.  For `a ≠ 0` this zero set is not a finite
union of arithmetic progressions.

**Theorem** (`exists_analyticOrderAt_xi_lt_leeYang`).  Some zero `ρ` of `Y_a` is a zero of `ξ` of
strictly smaller order.  For `|a| ≤ 4/5` all zeros of `Y_a` are simple, so some real `t` has
`cos(t log 6) + a cos(t log(3/2)) = 0` and `ζ(½ + it) ≠ 0`
(`exists_cos_add_cos_eq_zero_riemannZeta_ne_zero`).

*Proof.*  Suppose the orders of `Y_a` are dominated by those of `ξ`.  Then `q = ξ/Y_a` is entire.
On the vertical lines `Re s = 3/2, −½` and on the heights `Im s = 2πk/log 6` the function `Y_a` is
bounded below, so the maximum modulus principle on the rectangles between consecutive heights
transfers the decay `ξ ≪ |t|^N e^{−π|t|/4}` to `q` on the strip `−½ ≤ Re s ≤ 3/2`.  The Dirichlet
series `G(s) = ζ(s)/(2√6 Y_a(s)) = Σ_{m} c(m) m^{−s}` has `c(1) = 0`, and
`Γ_ℝ(s) G(s) = 2q(s)/(2√6 s(s−1))` satisfies the functional equation of `ζ` with the polar
part `α Γ_ℝ(s) + β Γ_ℝ(s − 1)`, `α = −q(0)/(2√6)`.  Hamburger's theorem gives `c(n) = −2α` for every
`n ≥ 1`; at `n = 1` this forces `q(0) = 0`, contradicting `q(0) Y_a(0) = ξ(0) = ½`.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry (coeffDirichlet verticalStrip)

noncomputable section

namespace RHTower.LeeYang

/-! ## Preliminary bounds -/

/-- The height step `T₁ = 2π / log 6`. -/
def T₁ : ℝ := 2 * Real.pi / L₁

theorem L₁_lt_three : L₁ < 3 := by
  rw [L₁, Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.quadratic_le_exp_of_nonneg (x := 3) (by norm_num)
  linarith

theorem two_le_T₁ : 2 ≤ T₁ := by
  rw [T₁, le_div_iff₀ L₁_pos]
  nlinarith [Real.pi_gt_three, L₁_lt_three, L₁_pos]

theorem T₁_pos : 0 < T₁ := by linarith [two_le_T₁]

/-- `ξ` decays like `|t|^N e^{−π|t|/4}` on the strip `−½ ≤ Re s ≤ 3/2`. -/
theorem exists_xi_bound_strip : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 →
    2 ≤ |z.im| → ‖xi z‖ ≤ C * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 4)) := by
  obtain ⟨C, N, hC, h⟩ := RHTower.SelbergThetaHorizontalBoundary.xi_strip_decay
  refine ⟨C, N, hC, fun z h1 h2 ht => ?_⟩
  rcases le_or_gt (1 / 2) z.re with hz | hz
  · exact h z hz (by linarith) ht
  · have hz' : xi z = xi (1 - z) := (xi_one_sub z).symm
    have him : |(1 - z).im| = |z.im| := by simp [abs_neg]
    rw [hz', ← him]
    exact h (1 - z) (by simp; linarith) (by simp; linarith) (by rw [him]; exact ht)

/-- `x^N e^{−πx/4} ≤ C/(1 + x²)` for `x ≥ 1`. -/
theorem exists_pow_mul_exp_le (N : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
    x ^ N * Real.exp (-(Real.pi * x / 4)) ≤ B / (1 + x ^ 2) := by
  set c : ℝ := Real.pi / 4
  have hc : 0 < c := by positivity
  refine ⟨2 * ((N + 2).factorial : ℝ) / c ^ (N + 2), by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hexp := Real.pow_div_factorial_le_exp (c * x) (by positivity) (N + 2)
  have hfac : (0 : ℝ) < (N + 2).factorial := by exact_mod_cast Nat.factorial_pos _
  have hmain : x ^ (N + 2) * Real.exp (-(c * x)) ≤ ((N + 2).factorial : ℝ) / c ^ (N + 2) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    rw [div_le_iff₀ hfac, mul_pow] at hexp
    nlinarith [Real.exp_pos (c * x), pow_pos hc (N + 2), pow_pos hx0 (N + 2)]
  have hpi : Real.pi * x / 4 = c * x := by ring
  rw [hpi]
  have h1x : 0 < 1 + x ^ 2 := by positivity
  rw [le_div_iff₀ h1x]
  have hx2 : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
  calc x ^ N * Real.exp (-(c * x)) * (1 + x ^ 2)
      ≤ x ^ N * Real.exp (-(c * x)) * (2 * x ^ 2) :=
        mul_le_mul_of_nonneg_left hx2 (by positivity)
    _ = 2 * (x ^ (N + 2) * Real.exp (-(c * x))) := by ring
    _ ≤ 2 * (((N + 2).factorial : ℝ) / c ^ (N + 2)) := by gcongr
    _ = _ := by ring

/-- The Gamma factor decays like `|t|^N e^{−π|t|/4}` on the strip, together with its shift. -/
theorem exists_Gammaℝ_bound_strip : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ z : ℂ, -1 / 2 ≤ z.re →
    z.re ≤ 3 / 2 → 2 ≤ |z.im| →
      ‖Gammaℝ z‖ ≤ C * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 4)) ∧
      ‖Gammaℝ (z - 1)‖ ≤ C * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 4)) := by
  obtain ⟨C, N, hC, h⟩ := GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
    (a := 1 / 4) (by norm_num) 2
  -- `Γ(w) = Γ(w + 1)/w` for `w = s/2` with `|Im w| ≥ 1`
  have key : ∀ w : ℂ, 1 / 4 ≤ w.re + 1 → w.re + 1 ≤ 2 → 1 ≤ |w.im| →
      ‖Complex.Gamma w‖ ≤ C * |w.im| ^ N * Real.exp (-(Real.pi * |w.im| / 2)) := by
    intro w h1 h2 h3
    have hw0 : w ≠ 0 := fun hw => by simp [hw] at h3; linarith
    have hrec : Complex.Gamma w = Complex.Gamma (w + 1) / w := by
      rw [Complex.Gamma_add_one w hw0]; field_simp
    have hw1 : w + 1 = ((w.re + 1 : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have hG := h (w.re + 1) w.im h1 h2 h3
    rw [← hw1] at hG
    have hwn : 1 ≤ ‖w‖ := h3.trans (Complex.abs_im_le_norm w)
    rw [hrec, norm_div]
    calc ‖Complex.Gamma (w + 1)‖ / ‖w‖ ≤ ‖Complex.Gamma (w + 1)‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) one_pos hwn
      _ ≤ _ := by rw [div_one]; exact hG
  refine ⟨Real.pi * C, N, by positivity, fun z h1 h2 ht => ?_⟩
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpow : ∀ x : ℝ, -1 / 2 - 1 ≤ x → x ≤ 3 / 2 →
      ‖(Real.pi : ℂ) ^ (-(x : ℂ) / 2 + -(z.im : ℂ) / 2 * I)‖ ≤ Real.pi := by
    intro x hx1 hx2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    have hre : (-(x : ℂ) / 2 + -(z.im : ℂ) / 2 * I).re = -x / 2 := by simp
    rw [hre]
    calc Real.pi ^ (-x / 2) ≤ Real.pi ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = Real.pi := Real.rpow_one _
  have him2 : |(z / 2).im| = |z.im| / 2 := by simp [abs_div]
  have hexp : Real.exp (-(Real.pi * (|z.im| / 2) / 2)) = Real.exp (-(Real.pi * |z.im| / 4)) := by
    congr 1; ring
  have hmono : (|z.im| / 2) ^ N ≤ |z.im| ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg z.im]) N
  constructor
  · rw [Complex.Gammaℝ_def]
    have hz : -z / 2 = -(z.re : ℂ) / 2 + -(z.im : ℂ) / 2 * I := by
      conv_lhs => rw [← Complex.re_add_im z]
      ring
    have hG := key (z / 2) (by simp; linarith) (by simp; linarith) (by rw [him2]; linarith)
    rw [him2, hexp] at hG
    rw [norm_mul, hz]
    calc ‖(Real.pi : ℂ) ^ (-(z.re : ℂ) / 2 + -(z.im : ℂ) / 2 * I)‖ * ‖Complex.Gamma (z / 2)‖
        ≤ Real.pi * (C * (|z.im| / 2) ^ N * Real.exp (-(Real.pi * |z.im| / 4))) :=
          mul_le_mul (hpow z.re (by linarith) h2) hG (norm_nonneg _) hpos.le
      _ ≤ Real.pi * (C * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 4))) := by gcongr
      _ = _ := by ring
  · rw [Complex.Gammaℝ_def]
    have hz : -(z - 1) / 2 = -((z.re - 1 : ℝ) : ℂ) / 2 + -(z.im : ℂ) / 2 * I := by
      conv_lhs => rw [← Complex.re_add_im z]
      push_cast; ring
    have him3 : |((z - 1) / 2).im| = |z.im| / 2 := by simp [abs_div]
    have hG := key ((z - 1) / 2) (by simp; linarith) (by simp; linarith) (by rw [him3]; linarith)
    rw [him3, hexp] at hG
    rw [norm_mul, hz]
    calc ‖(Real.pi : ℂ) ^ (-((z.re - 1 : ℝ) : ℂ) / 2 + -(z.im : ℂ) / 2 * I)‖
          * ‖Complex.Gamma ((z - 1) / 2)‖
        ≤ Real.pi * (C * (|z.im| / 2) ^ N * Real.exp (-(Real.pi * |z.im| / 4))) :=
          mul_le_mul (hpow (z.re - 1) (by linarith) (by linarith)) hG (norm_nonneg _) hpos.le
      _ ≤ Real.pi * (C * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 4))) := by gcongr
      _ = _ := by ring

/-! ## The quotient `ξ / Y_a` on the strip -/

/-- `Y_a` is bounded below by `1 − |a|` on the edges of the rectangles between the heights
`2πk/log 6`. -/
theorem norm_leeYang_ge_on_edge {a : ℝ} (ha : |a| < 1) {k : ℤ} {w : ℂ}
    (hedge : w.re = -1 / 2 ∨ w.re = 3 / 2 ∨ w.im = T₁ * k ∨ w.im = T₁ * (k + 1)) :
    1 - |a| ≤ ‖leeYang a w‖ := by
  rcases hedge with h | h | h | h
  · have := norm_leeYang_ge_of_re ha.le (s := w) (Or.inr h)
    linarith [abs_nonneg a]
  · have := norm_leeYang_ge_of_re ha.le (s := w) (Or.inl h)
    linarith [abs_nonneg a]
  · exact norm_leeYang_ge_of_im (a := a) k (by rw [h, T₁]; ring)
  · exact norm_leeYang_ge_of_im (a := a) (k + 1) (by rw [h, T₁]; push_cast; ring)

/-- **One band.**  On the rectangle `[−½, 3/2] × [T₁k, T₁(k+1)]`, away from the real axis, the
quotient obeys the decay of `ξ` up to a shift of one band. -/
theorem norm_quotient_le_band {a : ℝ} (ha : |a| < 1) {q : ℂ → ℂ} (hq : Differentiable ℂ q)
    (hxq : ∀ z, xi z = q z * leeYang a z) {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hxi : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → 2 ≤ |z.im| →
      ‖xi z‖ ≤ C * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 4)))
    {k : ℤ} (hk : 1 ≤ k ∨ k ≤ -2) {z : ℂ} (h1 : -1 / 2 ≤ z.re) (h2 : z.re ≤ 3 / 2)
    (h3 : T₁ * k ≤ z.im) (h4 : z.im ≤ T₁ * (k + 1)) :
    ‖q z‖ ≤ C / (1 - |a|) * (|z.im| + T₁) ^ N * Real.exp (-(Real.pi * (|z.im| - T₁) / 4)) := by
  have hT := T₁_pos
  have h2T := two_le_T₁
  have ha1 : 0 < 1 - |a| := by linarith
  set mid : ℝ := T₁ * k + T₁ / 2 with hmid
  set f : ℂ → ℂ := fun w => q (w + (mid : ℂ) * I)
  have hf : Differentiable ℂ f := hq.comp (differentiable_id.add_const _)
  have hshift : ∀ w : ℂ, (w + (mid : ℂ) * I).re = w.re ∧ (w + (mid : ℂ) * I).im = w.im + mid := by
    intro w; constructor <;> simp
  -- every height in the band is at least `2` in absolute value
  have hfar : ∀ t : ℝ, T₁ * k ≤ t → t ≤ T₁ * (k + 1) → 2 ≤ |t| := by
    intro t ht1 ht2
    rcases hk with hk | hk
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [abs_of_pos (by nlinarith)]
      nlinarith
    · have : (k : ℝ) ≤ -2 := by exact_mod_cast hk
      rw [abs_of_neg (by nlinarith)]
      nlinarith
  have hbound := GaloisForLFunctions.HTGeometry.norm_le_of_mem_rectangle (f := f) hf
    (A := -1 / 2) (B := 3 / 2) (T := T₁ / 2)
    (C := C / (1 - |a|) * (|z.im| + T₁) ^ N * Real.exp (-(Real.pi * (|z.im| - T₁) / 4)))
    (by norm_num) (by linarith) ?_ (z := z - (mid : ℂ) * I) (by simp; linarith) (by simp; linarith)
    (by simp; linarith [hmid]) (by simp; linarith [hmid])
  · simpa [f] using hbound
  intro w hw1 hw2 hw3 hw4 hedge
  obtain ⟨hre, him⟩ := hshift w
  set v := w + (mid : ℂ) * I
  have hv1 : T₁ * k ≤ v.im := by rw [him]; linarith [hmid]
  have hv2 : v.im ≤ T₁ * (k + 1) := by rw [him]; linarith [hmid]
  have hedge' : v.re = -1 / 2 ∨ v.re = 3 / 2 ∨ v.im = T₁ * k ∨ v.im = T₁ * (k + 1) := by
    rcases hedge with h | h | h | h
    · exact Or.inl (by rw [hre, h])
    · exact Or.inr (Or.inl (by rw [hre, h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [him, h]; ring)))
    · exact Or.inr (Or.inr (Or.inr (by rw [him, h]; ring)))
  have hY := norm_leeYang_ge_on_edge ha hedge'
  have hYpos : 0 < ‖leeYang a v‖ := lt_of_lt_of_le ha1 hY
  have hqv : ‖q v‖ = ‖xi v‖ / ‖leeYang a v‖ := by
    rw [hxq v, norm_mul, mul_div_cancel_right₀ _ hYpos.ne']
  have hvfar := hfar v.im hv1 hv2
  have hxv := hxi v (by rw [hre]; linarith) (by rw [hre]; linarith) hvfar
  -- the heights of `v` and `z` differ by at most one band
  have hdist : |v.im - z.im| ≤ T₁ := by
    rw [abs_le]; constructor <;> linarith
  have hup : |v.im| ≤ |z.im| + T₁ := by
    have := abs_sub_abs_le_abs_sub v.im z.im
    linarith
  have hlow : |z.im| - T₁ ≤ |v.im| := by
    have := abs_sub_abs_le_abs_sub z.im v.im
    rw [abs_sub_comm] at this
    linarith
  show ‖f w‖ ≤ _
  change ‖q v‖ ≤ _
  rw [hqv, div_le_iff₀ hYpos]
  calc ‖xi v‖ ≤ C * |v.im| ^ N * Real.exp (-(Real.pi * |v.im| / 4)) := hxv
    _ ≤ C * (|z.im| + T₁) ^ N * Real.exp (-(Real.pi * (|z.im| - T₁) / 4)) := by
        gcongr
    _ = C / (1 - |a|) * (|z.im| + T₁) ^ N * Real.exp (-(Real.pi * (|z.im| - T₁) / 4)) *
          (1 - |a|) := by field_simp
    _ ≤ _ := by gcongr

/-- **Decay of the quotient on the strip.** -/
theorem exists_quotient_bound_strip {a : ℝ} (ha : |a| < 1) {q : ℂ → ℂ} (hq : Differentiable ℂ q)
    (hxq : ∀ z, xi z = q z * leeYang a z) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → T₁ ≤ |z.im| →
      ‖q z‖ ≤ C * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 4)) := by
  obtain ⟨C, N, hC, hxi⟩ := exists_xi_bound_strip
  have hT := T₁_pos
  have ha1 : 0 < 1 - |a| := by linarith
  refine ⟨C / (1 - |a|) * 2 ^ N * Real.exp (Real.pi * T₁ / 4), N, by positivity,
    fun z h1 h2 ht => ?_⟩
  have hband : ‖q z‖ ≤ C / (1 - |a|) * (|z.im| + T₁) ^ N *
      Real.exp (-(Real.pi * (|z.im| - T₁) / 4)) := by
    rcases le_or_gt 0 z.im with hpos | hneg
    · rw [abs_of_nonneg hpos] at ht
      set k : ℤ := ⌊z.im / T₁⌋
      have hk1 : 1 ≤ k := by
        rw [Int.le_floor]; push_cast; rw [le_div_iff₀ hT]; linarith
      have hfl := Int.floor_le (z.im / T₁)
      have hfl2 := Int.lt_floor_add_one (z.im / T₁)
      refine norm_quotient_le_band ha hq hxq hC hxi (k := k) (Or.inl hk1) h1 h2 ?_ ?_
      · have := mul_le_mul_of_nonneg_left hfl hT.le
        rw [mul_div_cancel₀ _ hT.ne'] at this
        exact this
      · have := mul_le_mul_of_nonneg_left hfl2.le hT.le
        rw [mul_div_cancel₀ _ hT.ne'] at this
        exact this
    · rw [abs_of_neg hneg] at ht
      set k : ℤ := ⌈z.im / T₁⌉ - 1
      have hc : ⌈z.im / T₁⌉ ≤ -1 := by
        rw [Int.ceil_le]; push_cast; rw [div_le_iff₀ hT]; linarith
      have hk : k ≤ -2 := by simp only [k]; omega
      have hce := Int.le_ceil (z.im / T₁)
      have hce2 := Int.ceil_lt_add_one (z.im / T₁)
      refine norm_quotient_le_band ha hq hxq hC hxi (k := k) (Or.inr hk) h1 h2 ?_ ?_
      · simp only [k]; push_cast
        have := mul_le_mul_of_nonneg_left hce2.le hT.le
        rw [mul_add, mul_div_cancel₀ _ hT.ne'] at this
        linarith
      · simp only [k]; push_cast
        have := mul_le_mul_of_nonneg_left hce hT.le
        rw [mul_div_cancel₀ _ hT.ne'] at this
        linarith
  refine hband.trans (le_of_eq_of_le rfl ?_)
  have hTt : T₁ ≤ |z.im| := ht
  have hpow : (|z.im| + T₁) ^ N ≤ 2 ^ N * |z.im| ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) N
  have hexp : Real.exp (-(Real.pi * (|z.im| - T₁) / 4)) =
      Real.exp (Real.pi * T₁ / 4) * Real.exp (-(Real.pi * |z.im| / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc C / (1 - |a|) * (|z.im| + T₁) ^ N *
        (Real.exp (Real.pi * T₁ / 4) * Real.exp (-(Real.pi * |z.im| / 4)))
      ≤ C / (1 - |a|) * (2 ^ N * |z.im| ^ N) *
        (Real.exp (Real.pi * T₁ / 4) * Real.exp (-(Real.pi * |z.im| / 4))) := by gcongr
    _ = _ := by ring

/-! ## The completed quotient and its polar part -/

/-- `2√6 = 2 e^{(log 6)/2}`. -/
def kLY : ℂ := 2 * Complex.exp ((L₁ : ℂ) / 2)

theorem kLY_ne_zero : kLY ≠ 0 := mul_ne_zero two_ne_zero (Complex.exp_ne_zero _)

/-- `Γ_ℝ(s) ζ(s)/(2√6 Y_a(s)) = 2q(s)/(2√6 s(s−1))`. -/
def Fq (q : ℂ → ℂ) (s : ℂ) : ℂ := 2 * q s / (kLY * (s * (s - 1)))

/-- The polar coefficients `α = −q(0)/(2√6)` and `β = q(1)/(2√6)`. -/
def αq (q : ℂ → ℂ) : ℂ := -q 0 / kLY

def βq (q : ℂ → ℂ) : ℂ := q 1 / kLY

/-- The numerator at `s = 0`. -/
def N0 (q : ℂ → ℂ) (s : ℂ) : ℂ :=
  2 * q s / (kLY * (s - 1)) - 2 * αq q * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1)

/-- The numerator at `s = 1`. -/
def N1 (q : ℂ → ℂ) (s : ℂ) : ℂ :=
  2 * q s / (kLY * s) - 2 * βq q * (Real.pi : ℂ) ^ (-(s - 1) / 2) * Complex.Gamma ((s - 1) / 2 + 1)

/-- The completed quotient minus its polar part, with the removable singularities filled. -/
def strippedQuotient (q : ℂ → ℂ) (s : ℂ) : ℂ :=
  if s = 0 then dslope (N0 q) 0 0 - βq q * Gammaℝ (0 - 1)
  else if s = 1 then dslope (N1 q) 1 1 - αq q * Gammaℝ 1
  else Fq q s - αq q * Gammaℝ s - βq q * Gammaℝ (s - 1)

theorem Gammaℝ_eq_two_mul {s : ℂ} (hs : s ≠ 0) :
    Gammaℝ s = 2 * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) / s := by
  rw [Complex.Gammaℝ_def, Complex.Gamma_add_one (s / 2) (by simpa using hs)]
  field_simp

theorem N0_zero (q : ℂ → ℂ) : N0 q 0 = 0 := by
  have hK := kLY_ne_zero
  simp [N0, αq]
  field_simp
  ring

theorem N1_one (q : ℂ → ℂ) : N1 q 1 = 0 := by
  have hK := kLY_ne_zero
  simp [N1, βq]
  field_simp
  ring

theorem dslope_N0 (q : ℂ → ℂ) {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    dslope (N0 q) 0 s = Fq q s - αq q * Gammaℝ s := by
  rw [dslope_of_ne _ hs, slope_def_field, N0_zero, Gammaℝ_eq_two_mul hs, N0, Fq]
  have hK := kLY_ne_zero
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

theorem dslope_N1 (q : ℂ → ℂ) {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    dslope (N1 q) 1 s = Fq q s - βq q * Gammaℝ (s - 1) := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [dslope_of_ne _ hs1, slope_def_field, N1_one, Gammaℝ_eq_two_mul h1, N1, Fq]
  have hK := kLY_ne_zero
  field_simp
  ring

theorem strippedQuotient_eq (q : ℂ → ℂ) {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    strippedQuotient q s = Fq q s - αq q * Gammaℝ s - βq q * Gammaℝ (s - 1) := by
  rw [strippedQuotient, if_neg hs, if_neg hs1]

theorem differentiableAt_Gammaℝ_of {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(2 * m)) :
    DifferentiableAt ℂ Gammaℝ s := by
  have hfun : Gammaℝ = fun s => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; exact Complex.Gammaℝ_def s
  rw [hfun]
  refine DifferentiableAt.mul ?_ ?_
  · exact (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => -s / 2) s).const_cpow
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  · refine (Complex.differentiableAt_Gamma (s / 2) fun m h => hs m ?_).comp s (by fun_prop)
    linear_combination 2 * h

theorem differentiableAt_Gammaℝ_of_re {s : ℂ} (hre : -1 < s.re) (hs : s ≠ 0) :
    DifferentiableAt ℂ Gammaℝ s := by
  refine differentiableAt_Gammaℝ_of fun m h => ?_
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp at h; exact hs h
  · have := congrArg Complex.re h
    simp at this
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith

theorem differentiableAt_strippedQuotient {q : ℂ → ℂ} (hq : Differentiable ℂ q) {z : ℂ} (h1 : -1 < z.re)
    (h2 : z.re < 2) : DifferentiableAt ℂ (strippedQuotient q) z := by
  have hK := kLY_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases hz0 : z = 0
  · subst hz0
    -- near `0` the function is `dslope N0 0 − β Γ_ℝ(· − 1)`
    have hball : Metric.ball (0 : ℂ) (1 / 2) ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
    have hN0 : DifferentiableOn ℂ (N0 q) (Metric.ball 0 (1 / 2)) := by
      intro w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      have hw1 : w - 1 ≠ 0 := by
        intro h
        have : w = 1 := by linear_combination h
        rw [this] at hw; norm_num at hw
      have hG : DifferentiableAt ℂ Complex.Gamma (w / 2 + 1) := by
        refine Complex.differentiableAt_Gamma _ fun m h => ?_
        have := congrArg Complex.re h
        simp at this
        have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        rw [abs_le] at hre
        linarith
      refine DifferentiableAt.differentiableWithinAt ?_
      unfold N0
      refine ((hq w).const_mul 2 |>.div ((differentiableAt_id.sub_const 1).const_mul kLY)
        (mul_ne_zero hK hw1)).sub ?_
      refine ((differentiableAt_const _).mul ?_).mul (hG.comp w (by fun_prop))
      exact (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => -s / 2) w).const_cpow (Or.inl hpi)
    have hds : DifferentiableAt ℂ (dslope (N0 q) 0) 0 :=
      ((differentiableOn_dslope hball).mpr hN0).differentiableAt hball
    have hG1 : DifferentiableAt ℂ (fun s => Gammaℝ (s - 1)) 0 := by
      refine (differentiableAt_Gammaℝ_of fun m h => ?_).comp 0 (by fun_prop)
      have := congrArg Complex.re h
      simp at this
      have : (m : ℝ) = 1 / 2 := by linarith
      have hm : (2 : ℝ) * m = 1 := by linarith
      have : (2 * m : ℕ) = 1 := by exact_mod_cast hm
      omega
    have heq : (fun s => dslope (N0 q) 0 s - βq q * Gammaℝ (s - 1)) =ᶠ[𝓝 0] strippedQuotient q := by
      filter_upwards [hball] with w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      by_cases hw0 : w = 0
      · subst hw0; simp [strippedQuotient]
      · have hw1 : w ≠ 1 := fun h => by rw [h] at hw; norm_num at hw
        rw [strippedQuotient_eq q hw0 hw1, dslope_N0 q hw0 hw1]
    exact (heq.differentiableAt_iff).mp (hds.sub (hG1.const_mul _))
  by_cases hz1 : z = 1
  · subst hz1
    have hball : Metric.ball (1 : ℂ) (1 / 2) ∈ 𝓝 (1 : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
    have hN1 : DifferentiableOn ℂ (N1 q) (Metric.ball 1 (1 / 2)) := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have hw0 : w ≠ 0 := by
        intro h; rw [h] at hw; norm_num at hw
      have hG : DifferentiableAt ℂ Complex.Gamma ((w - 1) / 2 + 1) := by
        refine Complex.differentiableAt_Gamma _ fun m h => ?_
        have := congrArg Complex.re h
        simp at this
        have hre : |(w - 1).re| ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
        simp only [Complex.sub_re, Complex.one_re] at hre
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        rw [abs_le] at hre
        linarith
      refine DifferentiableAt.differentiableWithinAt ?_
      unfold N1
      refine ((hq w).const_mul 2 |>.div (differentiableAt_id.const_mul kLY)
        (mul_ne_zero hK hw0)).sub ?_
      refine ((differentiableAt_const _).mul ?_).mul (hG.comp w (by fun_prop))
      exact (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => -(s - 1) / 2) w).const_cpow (Or.inl hpi)
    have hds : DifferentiableAt ℂ (dslope (N1 q) 1) 1 :=
      ((differentiableOn_dslope hball).mpr hN1).differentiableAt hball
    have hG0 : DifferentiableAt ℂ Gammaℝ 1 :=
      differentiableAt_Gammaℝ_of_re (by norm_num) one_ne_zero
    have heq : (fun s => dslope (N1 q) 1 s - αq q * Gammaℝ s) =ᶠ[𝓝 1] strippedQuotient q := by
      filter_upwards [hball] with w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      by_cases hw1 : w = 1
      · subst hw1; simp [strippedQuotient]
      · have hw0 : w ≠ 0 := fun h => by rw [h] at hw; norm_num at hw
        rw [strippedQuotient_eq q hw0 hw1, dslope_N1 q hw0 hw1]
        ring
    exact (heq.differentiableAt_iff).mp (hds.sub (hG0.const_mul _))
  -- away from `0` and `1`
  have hopen : {w : ℂ | w ≠ 0 ∧ w ≠ 1} ∈ 𝓝 z :=
    (isOpen_ne.inter isOpen_ne).mem_nhds ⟨hz0, hz1⟩
  have heq : (fun s => Fq q s - αq q * Gammaℝ s - βq q * Gammaℝ (s - 1)) =ᶠ[𝓝 z] strippedQuotient q := by
    filter_upwards [hopen] with w hw
    rw [strippedQuotient_eq q hw.1 hw.2]
  refine (heq.differentiableAt_iff).mp ?_
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hF : DifferentiableAt ℂ (Fq q) z := by
    unfold Fq
    exact ((hq z).const_mul 2).div ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).const_mul
      kLY) (mul_ne_zero hK (mul_ne_zero hz0 hz1'))
  have hG : DifferentiableAt ℂ Gammaℝ z := differentiableAt_Gammaℝ_of_re h1 hz0
  have hG1 : DifferentiableAt ℂ (fun s => Gammaℝ (s - 1)) z := by
    refine (differentiableAt_Gammaℝ_of fun m h => ?_).comp z (by fun_prop)
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp at h; exact hz1' h
    · have := congrArg Complex.re h
      simp at this
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
  exact (hF.sub (hG.const_mul _)).sub (hG1.const_mul _)

/-! ## Decay of `E` and the functional equation -/

theorem exists_strippedQuotient_bound {a : ℝ} (ha : |a| < 1) {q : ℂ → ℂ} (hq : Differentiable ℂ q)
    (hxq : ∀ z, xi z = q z * leeYang a z) :
    ∃ C : ℝ, ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖strippedQuotient q s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨Cq, Nq, hCq, hqb⟩ := exists_quotient_bound_strip ha hq hxq
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := exists_Gammaℝ_bound_strip
  obtain ⟨B, hB, hBb⟩ := exists_pow_mul_exp_le (Nq + NΓ)
  have hK := kLY_ne_zero
  have hKn : 0 < ‖kLY‖ := norm_pos_iff.mpr hK
  have hT := T₁_pos
  have h2T := two_le_T₁
  set D : ℝ := 2 / ‖kLY‖ * Cq + (‖αq q‖ + ‖βq q‖) * CΓ with hD
  have hD0 : 0 ≤ D := by positivity
  -- the compact middle part
  set R : Set ℂ := Set.Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-T₁) T₁
  have hRc : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (strippedQuotient q) R := by
    intro z hz
    rw [Complex.mem_reProdIm, Set.mem_Icc, Set.mem_Icc] at hz
    exact (differentiableAt_strippedQuotient hq (by linarith [hz.1.1]) (by linarith [hz.1.2])).continuousAt
      |>.continuousWithinAt
  obtain ⟨M, hM⟩ := hRc.exists_bound_of_continuousOn hcont
  refine ⟨D * B + max M 0 * (1 + T₁ ^ 2), fun s hs => ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
  have h1t : 0 < 1 + s.im ^ 2 := by positivity
  rcases le_or_gt T₁ |s.im| with hfar | hnear
  · -- far from the real axis
    have hsim : 2 ≤ |s.im| := h2T.trans hfar
    have ht1 : 1 ≤ |s.im| := by linarith
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsim; simp at hsim; linarith
    have hs1' : s ≠ 1 := fun h => by rw [h] at hsim; simp at hsim; linarith
    rw [strippedQuotient_eq q hs0 hs1']
    have hFq : ‖Fq q s‖ ≤ 2 / ‖kLY‖ * ‖q s‖ := by
      have hn1 : 1 ≤ ‖s‖ * ‖s - 1‖ := by
        have a1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
        have a2 : |s.im| ≤ ‖s - 1‖ := by
          have := Complex.abs_im_le_norm (s - 1); simpa using this
        nlinarith
      rw [Fq, norm_div, norm_mul, norm_mul, norm_mul]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_left (by positivity) hKn ?_
      calc ‖kLY‖ = ‖kLY‖ * 1 := (mul_one _).symm
        _ ≤ ‖kLY‖ * (‖s‖ * ‖s - 1‖) := by gcongr
    have hqs := hqb s hs1 hs2 hfar
    obtain ⟨hΓ1, hΓ2⟩ := hΓ s hs1 hs2 hsim
    set e := Real.exp (-(Real.pi * |s.im| / 4))
    have he : 0 ≤ e := (Real.exp_pos _).le
    have hpq : |s.im| ^ Nq ≤ |s.im| ^ (Nq + NΓ) := pow_le_pow_right₀ ht1 (by omega)
    have hpΓ : |s.im| ^ NΓ ≤ |s.im| ^ (Nq + NΓ) := pow_le_pow_right₀ ht1 (by omega)
    have hmain : ‖Fq q s - αq q * Gammaℝ s - βq q * Gammaℝ (s - 1)‖ ≤
        D * (|s.im| ^ (Nq + NΓ) * e) := by
      calc ‖Fq q s - αq q * Gammaℝ s - βq q * Gammaℝ (s - 1)‖
          ≤ ‖Fq q s - αq q * Gammaℝ s‖ + ‖βq q * Gammaℝ (s - 1)‖ := norm_sub_le _ _
        _ ≤ (‖Fq q s‖ + ‖αq q * Gammaℝ s‖) + ‖βq q * Gammaℝ (s - 1)‖ := by
            gcongr; exact norm_sub_le _ _
        _ = ‖Fq q s‖ + ‖αq q‖ * ‖Gammaℝ s‖ + ‖βq q‖ * ‖Gammaℝ (s - 1)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ 2 / ‖kLY‖ * (Cq * |s.im| ^ Nq * e) + ‖αq q‖ * (CΓ * |s.im| ^ NΓ * e)
            + ‖βq q‖ * (CΓ * |s.im| ^ NΓ * e) := by
            gcongr
            exact hFq.trans (by gcongr)
        _ ≤ 2 / ‖kLY‖ * (Cq * |s.im| ^ (Nq + NΓ) * e) + ‖αq q‖ * (CΓ * |s.im| ^ (Nq + NΓ) * e)
            + ‖βq q‖ * (CΓ * |s.im| ^ (Nq + NΓ) * e) := by gcongr
        _ = D * (|s.im| ^ (Nq + NΓ) * e) := by rw [hD]; ring
    have hBs := hBb |s.im| ht1
    rw [sq_abs] at hBs
    calc ‖Fq q s - αq q * Gammaℝ s - βq q * Gammaℝ (s - 1)‖ ≤ D * (|s.im| ^ (Nq + NΓ) * e) :=
          hmain
      _ ≤ D * (B / (1 + s.im ^ 2)) := by gcongr
      _ = D * B / (1 + s.im ^ 2) := by ring
      _ ≤ (D * B + max M 0 * (1 + T₁ ^ 2)) / (1 + s.im ^ 2) := by
          gcongr
          have : 0 ≤ max M 0 * (1 + T₁ ^ 2) := by positivity
          linarith
  · -- the compact middle part
    have hsR : s ∈ R := by
      rw [Complex.mem_reProdIm, Set.mem_Icc, Set.mem_Icc]
      rw [abs_lt] at hnear
      exact ⟨⟨hs1, hs2⟩, ⟨hnear.1.le, hnear.2.le⟩⟩
    have hEs := hM s hsR
    have hsq : s.im ^ 2 ≤ T₁ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hnear.le 2
    rw [le_div_iff₀ h1t]
    have hM0 : M ≤ max M 0 := le_max_left _ _
    have hM1 : 0 ≤ max M 0 := le_max_right _ _
    have hDB : 0 ≤ D * B := by positivity
    calc ‖strippedQuotient q s‖ * (1 + s.im ^ 2) ≤ max M 0 * (1 + T₁ ^ 2) := by
          gcongr
          exact hEs.trans hM0
      _ ≤ D * B + max M 0 * (1 + T₁ ^ 2) := by linarith

theorem leeYang_one_sub (a : ℝ) (s : ℂ) : leeYang a (1 - s) = leeYang a s := by
  unfold leeYang
  rw [show (1 - s - 1 / 2) = -(s - 1 / 2) by ring, neg_mul, neg_mul, Complex.cosh_neg,
    Complex.cosh_neg]

theorem leeYang_ne_zero_of_re {a : ℝ} (ha : |a| < 1) {s : ℂ} (hs : s.re = 3 / 2 ∨ s.re = -1 / 2) :
    leeYang a s ≠ 0 := by
  intro h
  have := norm_leeYang_ge_of_re ha.le hs
  rw [h, norm_zero] at this
  norm_num at this

/-- On `Re w = 3/2` the completed Dirichlet series is the completed quotient. -/
theorem Gammaℝ_mul_coeffDirichlet {a : ℝ} (ha : |a| < 1) {q : ℂ → ℂ}
    (hxq : ∀ z, xi z = q z * leeYang a z) {c : ℕ → ℂ}
    (hc : ∀ s : ℂ, 1 < s.re → coeffDirichlet c s =
      riemannZeta s / (2 * Complex.exp ((L₁ : ℂ) / 2) * leeYang a s))
    {w : ℂ} (hw : w.re = 3 / 2) : Gammaℝ w * coeffDirichlet c w = Fq q w := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; norm_num at hw
  have hw1 : w ≠ 1 := fun h => by rw [h] at hw; norm_num at hw
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hY := leeYang_ne_zero_of_re ha (Or.inl hw)
  have hΓ : Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hw]; norm_num)
  have hK := kLY_ne_zero
  rw [hc w (by rw [hw]; norm_num), riemannZeta_def_of_ne_zero hw0]
  have hΛ : completedRiemannZeta w = 2 * xi w / (w * (w - 1)) := by
    rw [xi_eq_half_mul hw0 hw1]; field_simp
  rw [hΛ, hxq w, Fq, kLY]
  field_simp

theorem quotient_one_sub {a : ℝ} {q : ℂ → ℂ} (hxq : ∀ z, xi z = q z * leeYang a z) {s : ℂ}
    (hY : leeYang a s ≠ 0) : q (1 - s) = q s := by
  have h := hxq (1 - s)
  rw [xi_one_sub, hxq s, leeYang_one_sub] at h
  exact (mul_right_cancel₀ hY h).symm

/-! ## The contradiction -/

theorem xi_zero : xi 0 = 1 / 2 := by simp [xi]

theorem leeYang_zero_ne_zero {a : ℝ} (ha : |a| < 1) : leeYang a 0 ≠ 0 := by
  intro h
  have := norm_leeYang_ge_of_im (a := a) (s := 0) 0 (by simp)
  rw [h, norm_zero] at this
  linarith

/-- **No domination of orders.**  The zeros of `Y_a` cannot all be zeros of `ξ` of at least the
same order. -/
theorem false_of_analyticOrderAt_le {a : ℝ} (ha : |a| < 1)
    (H : ∀ z, analyticOrderAt (leeYang a) z ≤ analyticOrderAt xi z) : False := by
  obtain ⟨q, hq, hxq⟩ := GaloisForLFunctions.HTGeometry.exists_entire_quotient xi_differentiable
    (differentiable_leeYang a) ⟨0, leeYang_zero_ne_zero ha⟩ H
  obtain ⟨c, hc1, hcs, hcD⟩ := exists_coeff_dirichlet_zeta_div_leeYang ha
  obtain ⟨C, hC⟩ := exists_strippedQuotient_bound ha hq hxq
  have hE : DifferentiableOn ℂ (strippedQuotient q) (verticalStrip (-1 / 2) (3 / 2)) := fun z hz =>
    (differentiableAt_strippedQuotient hq (by linarith [hz.1]) (by linarith [hz.2])).differentiableWithinAt
  have hR : ∀ s : ℂ, s.re = 3 / 2 → Gammaℝ s * coeffDirichlet c s =
      strippedQuotient q s + (αq q * Gammaℝ s + βq q * Gammaℝ (s - 1)) := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    rw [Gammaℝ_mul_coeffDirichlet ha hxq hcD hs, strippedQuotient_eq q hs0 hs1]
    ring
  have hL : ∀ s : ℂ, s.re = -1 / 2 → (1 : ℂ) * (Gammaℝ (1 - s) * coeffDirichlet c (1 - s)) =
      strippedQuotient q s + (αq q * Gammaℝ s + βq q * Gammaℝ (s - 1)) := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    have hre : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
    have hY := leeYang_ne_zero_of_re ha (Or.inr hs)
    rw [one_mul, Gammaℝ_mul_coeffDirichlet ha hxq hcD hre, strippedQuotient_eq q hs0 hs1, Fq, Fq,
      quotient_one_sub hxq hY, show (1 - s) * (1 - s - 1) = s * (s - 1) by ring]
    ring
  have h := GaloisForLFunctions.HTGeometry.coeff_eq_of_completed_functional_equation
    (a := c) (b := c) (E := strippedQuotient q) (α := αq q) (β := βq q) (ε := 1) (C := C)
    hcs hcs hE hC hR hL 0
  rw [zero_add, hc1] at h
  have hα : αq q = 0 := by linear_combination h / 2
  have hq0 : q 0 = 0 := by
    have hK := kLY_ne_zero
    rw [αq, neg_div, neg_eq_zero, div_eq_zero_iff] at hα
    exact hα.resolve_right hK
  have hx := hxq 0
  rw [hq0, zero_mul, xi_zero] at hx
  norm_num at hx

/-- **Multi-prime Putnam theorem.**  For real `|a| < 1`, some zero `ρ` of
`Y_a(s) = cosh((s − ½) log 6) + a cosh((s − ½) log(3/2))` lies on the critical line and is a zero of
`ξ` of strictly smaller order (possibly not a zero of `ξ` at all). -/
theorem exists_analyticOrderAt_xi_lt_leeYang {a : ℝ} (ha : |a| < 1) :
    ∃ ρ : ℂ, leeYang a ρ = 0 ∧ ρ.re = 1 / 2 ∧ analyticOrderAt xi ρ < analyticOrderAt (leeYang a) ρ := by
  by_contra hcon
  push Not at hcon
  refine false_of_analyticOrderAt_le ha fun z => ?_
  by_cases hz : leeYang a z = 0
  · exact hcon z hz (re_eq_half_of_leeYang_eq_zero ha hz)
  · rw [((differentiable_leeYang a).analyticAt z).analyticOrderAt_eq_zero.mpr hz]
    exact zero_le

/-! ## Simple zeros and the explicit form -/

theorem hasDerivAt_leeYang (a : ℝ) (s : ℂ) :
    HasDerivAt (leeYang a)
      (Complex.sinh ((s - 1 / 2) * L₁) * L₁ + a * (Complex.sinh ((s - 1 / 2) * L₂) * L₂)) s := by
  have h1 : HasDerivAt (fun s : ℂ => (s - 1 / 2) * (L₁ : ℂ)) (L₁ : ℂ) s := by
    simpa using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const (L₁ : ℂ)
  have h2 : HasDerivAt (fun s : ℂ => (s - 1 / 2) * (L₂ : ℂ)) (L₂ : ℂ) s := by
    simpa using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const (L₂ : ℂ)
  exact h1.ccosh.add (h2.ccosh.const_mul (a : ℂ))

theorem leeYang_half_add (a t : ℝ) :
    leeYang a (1 / 2 + t * I) = ((Real.cos (t * L₁) + a * Real.cos (t * L₂) : ℝ) : ℂ) := by
  unfold leeYang
  rw [show (1 / 2 + (t : ℂ) * I - 1 / 2) * L₁ = ((t * L₁ : ℝ) : ℂ) * I by push_cast; ring,
    show (1 / 2 + (t : ℂ) * I - 1 / 2) * L₂ = ((t * L₂ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.cosh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cos]
  push_cast; ring

theorem deriv_leeYang_half_add (a t : ℝ) :
    deriv (leeYang a) (1 / 2 + t * I) =
      ((L₁ * Real.sin (t * L₁) + a * L₂ * Real.sin (t * L₂) : ℝ) : ℂ) * I := by
  rw [(hasDerivAt_leeYang a _).deriv,
    show (1 / 2 + (t : ℂ) * I - 1 / 2) * L₁ = ((t * L₁ : ℝ) : ℂ) * I by push_cast; ring,
    show (1 / 2 + (t : ℂ) * I - 1 / 2) * L₂ = ((t * L₂ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.sinh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_sin]
  push_cast; ring

theorem one_le_L₁ : 1 ≤ L₁ := by
  rw [L₁, Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem L₂_le_half : L₂ ≤ 1 / 2 := by
  rw [L₂, Real.log_le_iff_le_exp (by norm_num)]
  have := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
  linarith

/-- For `|a| ≤ 4/5` every zero of `Y_a` is simple. -/
theorem deriv_leeYang_ne_zero {a : ℝ} (ha : |a| ≤ 4 / 5) {ρ : ℂ} (hρ : leeYang a ρ = 0)
    (hre : ρ.re = 1 / 2) : deriv (leeYang a) ρ ≠ 0 := by
  have hρ' : ρ = 1 / 2 + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  set t := ρ.im
  rw [hρ'] at hρ ⊢
  rw [leeYang_half_add, Complex.ofReal_eq_zero] at hρ
  rw [deriv_leeYang_half_add]
  refine mul_ne_zero ?_ Complex.I_ne_zero
  rw [Complex.ofReal_ne_zero]
  intro h
  have hc1 := Real.sin_sq_add_cos_sq (t * L₁)
  have hc2 := Real.sin_sq_add_cos_sq (t * L₂)
  have hcos : Real.cos (t * L₁) = -(a * Real.cos (t * L₂)) := by linarith
  have ha2 : a ^ 2 ≤ 16 / 25 := by
    have := sq_abs a
    nlinarith [abs_nonneg a]
  have hL1 := one_le_L₁
  have hL2 := L₂_le_half
  have hL2p := L₂_pos
  have hsin1 : 9 / 25 ≤ Real.sin (t * L₁) ^ 2 := by
    rw [hcos] at hc1
    nlinarith [sq_nonneg (Real.cos (t * L₂)), sq_nonneg (Real.sin (t * L₂))]
  have hsq : (L₁ * Real.sin (t * L₁)) ^ 2 = (a * L₂ * Real.sin (t * L₂)) ^ 2 := by
    have : L₁ * Real.sin (t * L₁) = -(a * L₂ * Real.sin (t * L₂)) := by linarith
    rw [this]; ring
  have hlhs : 9 / 25 ≤ (L₁ * Real.sin (t * L₁)) ^ 2 := by
    rw [mul_pow]; nlinarith
  have hrhs : (a * L₂ * Real.sin (t * L₂)) ^ 2 ≤ 4 / 25 := by
    rw [mul_pow, mul_pow]
    have hs2 : Real.sin (t * L₂) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.cos (t * L₂))]
    have hl2 : L₂ ^ 2 ≤ 1 / 4 := by nlinarith
    calc a ^ 2 * L₂ ^ 2 * Real.sin (t * L₂) ^ 2 ≤ (16 / 25) * (1 / 4) * 1 := by
          gcongr
      _ = 4 / 25 := by norm_num
  linarith

/-- **Multi-prime Putnam theorem, explicit form.**  For real `|a| ≤ 4/5` there is a real `t` with
`cos(t log 6) + a cos(t log(3/2)) = 0` and `ζ(½ + it) ≠ 0`.  For `a = 0` this is Putnam's
non-periodicity on the progression `t = (2k + 1)π/(2 log 6)`. -/
theorem exists_cos_add_cos_eq_zero_riemannZeta_ne_zero {a : ℝ} (ha : |a| ≤ 4 / 5) :
    ∃ t : ℝ, Real.cos (t * Real.log 6) + a * Real.cos (t * Real.log (3 / 2)) = 0 ∧
      riemannZeta (1 / 2 + t * I) ≠ 0 := by
  have ha1 : |a| < 1 := lt_of_le_of_lt ha (by norm_num)
  obtain ⟨ρ, hρ, hre, hord⟩ := exists_analyticOrderAt_xi_lt_leeYang ha1
  have hY1 : analyticOrderAt (leeYang a) ρ = 1 :=
    ((differentiable_leeYang a).analyticAt ρ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ
      (deriv_leeYang_ne_zero ha hρ hre)
  rw [hY1] at hord
  have hxi0 : analyticOrderAt xi ρ = 0 := Order.lt_one_iff.mp hord
  have hxi : xi ρ ≠ 0 := (xi_differentiable.analyticAt ρ).analyticOrderAt_eq_zero.mp hxi0
  have hρ' : ρ = 1 / 2 + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  refine ⟨ρ.im, ?_, ?_⟩
  · have h := hρ
    rw [hρ', leeYang_half_add, Complex.ofReal_eq_zero] at h
    exact h
  · rw [← hρ']
    intro hz
    refine hxi (xi_eq_zero_of_zeta_eq_zero hz ?_ ?_)
    · rintro ⟨n, hn⟩
      have := congrArg Complex.re hn
      simp [hre] at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro h; rw [h] at hre; norm_num at hre

end RHTower.LeeYang
