import GaloisForLFunctions.RHTower.HorizontalIsolationCrossPairOverlap

/-!
# Decay of the cross-pair overlaps in the ordinate gap

For two off-line zeros `p = ½ + ε_p + iγ_p`, `q = ½ + ε_q + iγ_q`, with `Δ = γ_q − γ_p`, the full-grid
overlap of the even vector of `p` with the odd vector of `q` is
`L ∫ φ² cosh(ε_p u) sinh(ε_q u) sin(Δu) du / c` (`hasSum_re_mul_im_cross_grid`).

* **Integration by parts** (`abs_integral_mul_sin_le`). For `F` vanishing at both ends,
  `|∫ F(u) sin(Δu)| ≤ ∫|F'|/|Δ|`.
* **Cross window** (`abs_integral_cross_window_le`). With `F = φ² cosh(ε_p u) sinh(ε_q u)`,
  `|∫ φ² cosh(ε_p u) sinh(ε_q u) sin(Δu)| ≤ (2 A₁ + |ε_p| A₂ + |ε_q| A₃)/|Δ|`, where
  - `A₁ = √(∫ φ'² cosh²(ε_p u)) √(∫ φ² sinh²(ε_q u))`;
  - `A₂ = √(∫ φ² sinh²(ε_p u)) √(∫ φ² sinh²(ε_q u))`;
  - `A₃ = √(∫ φ² cosh²(ε_p u)) √(∫ φ² cosh²(ε_q u))`.

  Divided by the norms `√(∫φ²cosh²(ε_p u)) √(∫φ²sinh²(ε_q u))`, each term is scale-free. The
  normalised angle between the even vector of `p` and the odd vector of `q` is therefore
  `O((‖φ'cosh‖/‖φcosh‖ + ε_p + ε_q·‖φcosh(ε_q·)‖/‖φsinh(ε_q·)‖)/|Δ|)`, with no exponential factor.
* **Truncation** (`abs_sub_sum_le_of_hasSum`). If `Σ_j a_j b_j = A`, `Σ a_j² = P_a` and
  `Σ b_j² = P_b`, then any finite partial sum over `S` satisfies
  `|A − Σ_S a b| ≤ √(P_a − Σ_S a²) √(P_b − Σ_S b²)`. The truncated block overlap thus differs from
  the full-grid value by at most the geometric mean of the two leakages.
* **Block form** (`abs_inner_blockImVec_blockReVec_le`). The truncated block overlap
  `⟪h_q, g_p⟫` is at most `(L |∫ φ² cosh sinh sin| + √(ℓ_p ℓ_q))/c`, with the leakages
  `ℓ_p = L∫φ²cosh²(ε_p u) − Σ_{k<d} (Re φ̂_p)²` and `ℓ_q = Σ_j (Im φ̂_q)² − Σ_{k<d} (Im φ̂_q)²`.
-/

open Complex MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace RHTower

/-! ## Integration by parts -/

/-- `|∫_a^b F(u) sin(Δu) du| ≤ (∫_a^b |F'|)/|Δ|` for `F` vanishing at both ends. -/
theorem abs_integral_mul_sin_le {a b Δ : ℝ} (hab : a ≤ b) (hΔ : Δ ≠ 0) {F F' : ℝ → ℝ}
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (F' x) x) (hF'c : ContinuousOn F' (uIcc a b))
    (ha : F a = 0) (hb : F b = 0) :
    |∫ x in a..b, F x * Real.sin (Δ * x)| ≤ (∫ x in a..b, |F' x|) / |Δ| := by
  have hv : ∀ x ∈ uIcc a b, HasDerivAt (fun x => -Real.cos (Δ * x) / Δ)
      (Real.sin (Δ * x)) x := by
    intro x _
    have h := ((((hasDerivAt_id' x).const_mul Δ).cos).neg).div_const Δ
    refine h.congr_deriv ?_
    field_simp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hF hv
    (hF'c.intervalIntegrable) (by apply Continuous.intervalIntegrable; fun_prop)
  rw [hibp, ha, hb, zero_mul, zero_mul, sub_zero, zero_sub, abs_neg]
  have hrw : (∫ x in a..b, F' x * (-Real.cos (Δ * x) / Δ)) =
      -(∫ x in a..b, F' x * Real.cos (Δ * x)) / Δ := by
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [hrw, abs_div, abs_neg]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg Δ)
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
  refine intervalIntegral.integral_mono_on hab ?_ ?_ fun x _ => ?_
  · exact (hF'c.mul (by fun_prop : Continuous fun x => Real.cos (Δ * x)).continuousOn).abs
      |>.intervalIntegrable
  · exact hF'c.abs.intervalIntegrable
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-! ## Cauchy–Schwarz on an interval -/

/-- `(∫_a^b f g)² ≤ (∫_a^b f²)(∫_a^b g²)` for continuous `f, g` and `a ≤ b`. -/
theorem sq_intervalIntegral_mul_le {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * ∫ x in a..b, g x ^ 2 := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x in a..b, g x ^ 2) * (t * t) +
      (-2 * ∫ x in a..b, f x * g x) * t + ∫ x in a..b, f x ^ 2 := by
    intro t
    have hnn : 0 ≤ ∫ x in a..b, (f x - t * g x) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have hexp : (∫ x in a..b, (f x - t * g x) ^ 2) =
        (∫ x in a..b, f x ^ 2) - 2 * t * (∫ x in a..b, f x * g x) +
          t ^ 2 * ∫ x in a..b, g x ^ 2 := by
      have e : (fun x => (f x - t * g x) ^ 2) =
          fun x => (f x ^ 2 - (2 * t) * (f x * g x)) + t ^ 2 * g x ^ 2 := by
        funext x; ring
      have i1 : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
        (hf.pow 2).intervalIntegrable a b
      have i2 : IntervalIntegrable (fun x => (2 * t) * (f x * g x)) volume a b :=
        ((hf.mul hg).const_mul (2 * t)).intervalIntegrable a b
      have i3 : IntervalIntegrable (fun x => t ^ 2 * g x ^ 2) volume a b :=
        ((hg.pow 2).const_mul (t ^ 2)).intervalIntegrable a b
      have i12 : IntervalIntegrable (fun x => f x ^ 2 - (2 * t) * (f x * g x)) volume a b :=
        i1.sub i2
      rw [e, intervalIntegral.integral_add i12 i3, intervalIntegral.integral_sub i1 i2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [hexp] at hnn
    nlinarith
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith

/-- `∫_a^b |f g| ≤ √(∫ f²) √(∫ g²)` for continuous `f, g` and `a ≤ b`. -/
theorem integral_abs_mul_le_sqrt {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    ∫ x in a..b, |f x| * |g x| ≤
      Real.sqrt (∫ x in a..b, f x ^ 2) * Real.sqrt (∫ x in a..b, g x ^ 2) := by
  have h := sq_intervalIntegral_mul_le hab hf.abs hg.abs
  simp only [sq_abs] at h
  have h0 : 0 ≤ ∫ x in a..b, |f x| * |g x| :=
    intervalIntegral.integral_nonneg hab fun x _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [← Real.sqrt_mul (intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le h

/-! ## The cross window -/

/-- **Cross-window integration by parts.** For `φ` with derivative `φ'` on `[−L/2, L/2]`,
vanishing at `±L/2`:
`|∫ φ² cosh(ε_p u) sinh(ε_q u) sin(Δu)|
≤ (∫ 2|φ||φ'| cosh(ε_p u)|sinh(ε_q u)| + |ε_p| φ²|sinh(ε_p u)||sinh(ε_q u)|
    + |ε_q| φ² cosh(ε_p u) cosh(ε_q u)) / |Δ|`. -/
theorem abs_integral_cross_window_le_pointwise {L Δ εp εq : ℝ} (hL : 0 < L) (hΔ : Δ ≠ 0)
    {φ φ' : ℝ → ℝ} (hφ : ∀ u, HasDerivAt φ (φ' u) u) (hφ'c : Continuous φ')
    (h0 : φ (-(L / 2)) = 0) (h1 : φ (L / 2) = 0) :
    |∫ u in (-(L / 2))..(L / 2),
        φ u ^ 2 * Real.cosh (εp * u) * Real.sinh (εq * u) * Real.sin (Δ * u)| ≤
      (∫ u in (-(L / 2))..(L / 2),
        (2 * |φ u| * |φ' u| * Real.cosh (εp * u) * |Real.sinh (εq * u)| +
          |εp| * φ u ^ 2 * |Real.sinh (εp * u)| * |Real.sinh (εq * u)| +
          |εq| * φ u ^ 2 * Real.cosh (εp * u) * Real.cosh (εq * u))) / |Δ| := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun u => (hφ u).continuousAt
  set F : ℝ → ℝ := fun u => φ u * φ u * Real.cosh (εp * u) * Real.sinh (εq * u) with hF
  set F' : ℝ → ℝ := fun u => 2 * φ u * φ' u * Real.cosh (εp * u) * Real.sinh (εq * u) +
    φ u ^ 2 * (εp * Real.sinh (εp * u) * Real.sinh (εq * u) +
      εq * Real.cosh (εp * u) * Real.cosh (εq * u)) with hF'
  have hFd : ∀ u, HasDerivAt F (F' u) u := by
    intro u
    have hcp := ((hasDerivAt_id' u).const_mul εp).cosh
    have hsq := ((hasDerivAt_id' u).const_mul εq).sinh
    have h2 := (((hφ u).fun_mul (hφ u)).fun_mul hcp).fun_mul hsq
    refine h2.congr_deriv ?_
    simp only [hF']
    ring
  have hF'c : Continuous F' := by simp only [hF']; fun_prop
  have hab : -(L / 2) ≤ L / 2 := by linarith
  have hmain := abs_integral_mul_sin_le hab hΔ (fun u _ => hFd u) hF'c.continuousOn
    (by simp [hF, h0]) (by simp [hF, h1])
  have hint : (∫ u in (-(L / 2))..(L / 2),
      φ u ^ 2 * Real.cosh (εp * u) * Real.sinh (εq * u) * Real.sin (Δ * u)) =
      ∫ u in (-(L / 2))..(L / 2), F u * Real.sin (Δ * u) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hF]
    ring
  rw [hint]
  refine hmain.trans (div_le_div_of_nonneg_right ?_ (abs_nonneg _))
  refine intervalIntegral.integral_mono_on hab (hF'c.abs.intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; fun_prop) fun u _ => ?_
  simp only [hF']
  have hc1 := Real.cosh_pos (εp * u)
  have hc2 := Real.cosh_pos (εq * u)
  calc |2 * φ u * φ' u * Real.cosh (εp * u) * Real.sinh (εq * u) +
        φ u ^ 2 * (εp * Real.sinh (εp * u) * Real.sinh (εq * u) +
          εq * Real.cosh (εp * u) * Real.cosh (εq * u))|
      ≤ |2 * φ u * φ' u * Real.cosh (εp * u) * Real.sinh (εq * u)| +
        |φ u ^ 2 * (εp * Real.sinh (εp * u) * Real.sinh (εq * u))| +
        |φ u ^ 2 * (εq * Real.cosh (εp * u) * Real.cosh (εq * u))| := by
        rw [mul_add, ← add_assoc]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = 2 * |φ u| * |φ' u| * Real.cosh (εp * u) * |Real.sinh (εq * u)| +
          |εp| * φ u ^ 2 * |Real.sinh (εp * u)| * |Real.sinh (εq * u)| +
          |εq| * φ u ^ 2 * Real.cosh (εp * u) * Real.cosh (εq * u) := by
        simp only [abs_mul, abs_pow, sq_abs, abs_of_pos hc1, abs_of_pos hc2,
          abs_two]
        ring

/-- **Cross-window bound in Cauchy–Schwarz form.**
`|∫ φ² cosh(ε_p u) sinh(ε_q u) sin(Δu)| ≤ (2 A₁ + |ε_p| A₂ + |ε_q| A₃)/|Δ|`. -/
theorem abs_integral_cross_window_le {L Δ εp εq : ℝ} (hL : 0 < L) (hΔ : Δ ≠ 0)
    {φ φ' : ℝ → ℝ} (hφ : ∀ u, HasDerivAt φ (φ' u) u) (hφ'c : Continuous φ')
    (h0 : φ (-(L / 2)) = 0) (h1 : φ (L / 2) = 0) :
    |∫ u in (-(L / 2))..(L / 2),
        φ u ^ 2 * Real.cosh (εp * u) * Real.sinh (εq * u) * Real.sin (Δ * u)| ≤
      (2 * (Real.sqrt (∫ u in (-(L / 2))..(L / 2), (φ' u * Real.cosh (εp * u)) ^ 2) *
            Real.sqrt (∫ u in (-(L / 2))..(L / 2), (φ u * Real.sinh (εq * u)) ^ 2)) +
        |εp| * (Real.sqrt (∫ u in (-(L / 2))..(L / 2), (φ u * Real.sinh (εp * u)) ^ 2) *
            Real.sqrt (∫ u in (-(L / 2))..(L / 2), (φ u * Real.sinh (εq * u)) ^ 2)) +
        |εq| * (Real.sqrt (∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (εp * u)) ^ 2) *
            Real.sqrt (∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (εq * u)) ^ 2))) /
        |Δ| := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun u => (hφ u).continuousAt
  have hab : -(L / 2) ≤ L / 2 := by linarith
  refine (abs_integral_cross_window_le_pointwise hL hΔ hφ hφ'c h0 h1).trans
    (div_le_div_of_nonneg_right ?_ (abs_nonneg _))
  have i1 := integral_abs_mul_le_sqrt (f := fun u => φ' u * Real.cosh (εp * u))
    (g := fun u => φ u * Real.sinh (εq * u)) hab (by fun_prop) (by fun_prop)
  have i2 := integral_abs_mul_le_sqrt (f := fun u => φ u * Real.sinh (εp * u))
    (g := fun u => φ u * Real.sinh (εq * u)) hab (by fun_prop) (by fun_prop)
  have i3 := integral_abs_mul_le_sqrt (f := fun u => φ u * Real.cosh (εp * u))
    (g := fun u => φ u * Real.cosh (εq * u)) hab (by fun_prop) (by fun_prop)
  have e : (fun u => 2 * |φ u| * |φ' u| * Real.cosh (εp * u) * |Real.sinh (εq * u)| +
        |εp| * φ u ^ 2 * |Real.sinh (εp * u)| * |Real.sinh (εq * u)| +
        |εq| * φ u ^ 2 * Real.cosh (εp * u) * Real.cosh (εq * u)) =
      fun u => (2 * (|φ' u * Real.cosh (εp * u)| * |φ u * Real.sinh (εq * u)|) +
        |εp| * (|φ u * Real.sinh (εp * u)| * |φ u * Real.sinh (εq * u)|)) +
        |εq| * (|φ u * Real.cosh (εp * u)| * |φ u * Real.cosh (εq * u)|) := by
    funext u
    have hc1 := Real.cosh_pos (εp * u)
    have hc2 := Real.cosh_pos (εq * u)
    simp only [abs_mul, abs_of_pos hc1, abs_of_pos hc2]
    rw [show φ u ^ 2 = |φ u| * |φ u| by rw [← abs_mul, ← sq, abs_sq]]
    ring
  rw [e, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  · have := abs_nonneg εp
    have := abs_nonneg εq
    nlinarith [mul_le_mul_of_nonneg_left i2 (abs_nonneg εp),
      mul_le_mul_of_nonneg_left i3 (abs_nonneg εq)]
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-! ## Truncation -/

/-- **Truncation by Cauchy–Schwarz.** If `Σ_j a_j b_j = A`, `Σ a_j² = P_a`, `Σ b_j² = P_b`, then for
every finite `S`: `|A − Σ_S a b| ≤ √(P_a − Σ_S a²) √(P_b − Σ_S b²)`. -/
theorem abs_sub_sum_le_of_hasSum {ι : Type*} {a b : ι → ℝ} {A Pa Pb : ℝ}
    (hab : HasSum (fun j => a j * b j) A) (ha : HasSum (fun j => a j ^ 2) Pa)
    (hb : HasSum (fun j => b j ^ 2) Pb) (S : Finset ι) :
    |A - ∑ j ∈ S, a j * b j| ≤
      Real.sqrt (Pa - ∑ j ∈ S, a j ^ 2) * Real.sqrt (Pb - ∑ j ∈ S, b j ^ 2) := by
  classical
  -- the complementary series
  have hsplit : ∀ (f : ι → ℝ) (F : ℝ), HasSum f F →
      HasSum (fun j => if j ∈ S then 0 else f j) (F - ∑ j ∈ S, f j) := by
    intro f F hf
    have hS : HasSum (fun j => if j ∈ S then f j else 0) (∑ j ∈ S, f j) := by
      have h1 : HasSum (fun j => if j ∈ S then f j else 0)
          (∑ j ∈ S, (if j ∈ S then f j else 0)) :=
        hasSum_sum_of_ne_finset_zero fun j hj => if_neg hj
      rwa [Finset.sum_ite_mem, Finset.inter_self] at h1
    have e : (fun j => if j ∈ S then 0 else f j) =
        fun j => f j - (if j ∈ S then f j else 0) := by
      funext j; split_ifs <;> simp
    rw [e]
    exact hf.sub hS
  set a' : ι → ℝ := fun j => if j ∈ S then 0 else a j with ha'
  set b' : ι → ℝ := fun j => if j ∈ S then 0 else b j with hb'
  have hab' : HasSum (fun j => a' j * b' j) (A - ∑ j ∈ S, a j * b j) := by
    have e : (fun j => a' j * b' j) = fun j => if j ∈ S then 0 else a j * b j := by
      funext j; simp only [ha', hb']; split_ifs <;> simp
    rw [e]; exact hsplit _ _ hab
  have ha'' : HasSum (fun j => a' j ^ 2) (Pa - ∑ j ∈ S, a j ^ 2) := by
    have e : (fun j => a' j ^ 2) = fun j => if j ∈ S then 0 else a j ^ 2 := by
      funext j; simp only [ha']; split_ifs <;> simp
    rw [e]; exact hsplit _ _ ha
  have hb'' : HasSum (fun j => b' j ^ 2) (Pb - ∑ j ∈ S, b j ^ 2) := by
    have e : (fun j => b' j ^ 2) = fun j => if j ∈ S then 0 else b j ^ 2 := by
      funext j; simp only [hb']; split_ifs <;> simp
    rw [e]; exact hsplit _ _ hb
  set A' := A - ∑ j ∈ S, a j * b j
  set Pa' := Pa - ∑ j ∈ S, a j ^ 2
  set Pb' := Pb - ∑ j ∈ S, b j ^ 2
  have hPa0 : 0 ≤ Pa' := ha''.nonneg fun j => sq_nonneg _
  -- the discriminant of `t ↦ Σ (a' − t b')² ≥ 0`
  have key : ∀ t : ℝ, 0 ≤ Pb' * (t * t) + (-2 * A') * t + Pa' := by
    intro t
    have hq : HasSum (fun j => (a' j - t * b' j) ^ 2) (Pa' - 2 * t * A' + t ^ 2 * Pb') := by
      have e : (fun j => (a' j - t * b' j) ^ 2) =
          fun j => (a' j ^ 2 - (2 * t) * (a' j * b' j)) + t ^ 2 * b' j ^ 2 := by
        funext j; ring
      rw [e]
      have := (ha''.sub (hab'.mul_left (2 * t))).add (hb''.mul_left (t ^ 2))
      convert this using 2
    have := hq.nonneg fun j => sq_nonneg _
    nlinarith
  have hd := discrim_le_zero key
  unfold discrim at hd
  have hlim : A' ^ 2 ≤ Pa' * Pb' := by nlinarith
  rw [← Real.sqrt_mul hPa0]
  exact Real.abs_le_sqrt hlim

/-- **Truncation against a dominating series.** If `b_j² ≤ c_j` with `Σ c = P_c`, then
`|A − Σ_S a b| ≤ √(P_a − Σ_S a²) √(P_c − Σ_S c)`. -/
theorem abs_sub_sum_le_of_hasSum_le {ι : Type*} {a b c : ι → ℝ} {A Pa Pc : ℝ}
    (hab : HasSum (fun j => a j * b j) A) (ha : HasSum (fun j => a j ^ 2) Pa)
    (hc : HasSum c Pc) (hbc : ∀ j, b j ^ 2 ≤ c j) (S : Finset ι) :
    |A - ∑ j ∈ S, a j * b j| ≤
      Real.sqrt (Pa - ∑ j ∈ S, a j ^ 2) * Real.sqrt (Pc - ∑ j ∈ S, c j) := by
  classical
  have hbs : Summable fun j => b j ^ 2 :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) hbc hc.summable
  have hb := hbs.hasSum
  refine (abs_sub_sum_le_of_hasSum hab ha hb S).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  -- compare the two tails
  have htail : ∀ (f : ι → ℝ) (F : ℝ), HasSum f F →
      HasSum (fun j => if j ∈ S then 0 else f j) (F - ∑ j ∈ S, f j) := by
    intro f F hf
    have hS : HasSum (fun j => if j ∈ S then f j else 0) (∑ j ∈ S, f j) := by
      have h1 : HasSum (fun j => if j ∈ S then f j else 0)
          (∑ j ∈ S, (if j ∈ S then f j else 0)) :=
        hasSum_sum_of_ne_finset_zero fun j hj => if_neg hj
      rwa [Finset.sum_ite_mem, Finset.inter_self] at h1
    have e : (fun j => if j ∈ S then 0 else f j) =
        fun j => f j - (if j ∈ S then f j else 0) := by
      funext j; split_ifs <;> simp
    rw [e]
    exact hf.sub hS
  exact hasSum_le (fun j => by split_ifs <;> simp [hbc j]) (htail _ _ hb) (htail _ _ hc)

/-! ## The block overlap -/

section Block

open Zeta23 Zeta23.ZeroSide

variable {Z : ZeroConfig} {T : ℝ} {P : Params}

/-- The window of `φ̂(w + Δ − iε)`: `paperFT(φ e^{ε·} e^{iΔ·})(w) = φ̂(w + Δ − iε)`. -/
theorem paperFT_shifted_window (P : Params) (T w Δ ε : ℝ) :
    paperFT (fun u => ((P.phi T u : ℝ) : ℂ) * cexp ((ε : ℂ) * u) * cexp (I * Δ * u)) (w : ℂ) =
      P.phiHat T (((w + Δ : ℝ) : ℂ) - (ε : ℂ) * I) := by
  simp only [Params.phiHat, paperFT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Truncated block overlap.** The block overlap `⟪h_q, g_p⟫` differs from its full-grid value
`L ∫ φ² cosh(ε_p u) sinh(ε_q u) sin(Δu)/c` by at most `√(ℓ_p ℓ_q)/c`, where `ℓ_p` and `ℓ_q` are the
leakages of the full-grid series `Σ (Re φ̂_p)²` and `Σ |φ̂_q|²` off the block indices. -/
theorem abs_inner_blockImVec_blockReVec_sub_le (hconj : PhiHatConj T P) {c : ℝ} (hc : 0 < c)
    (hL : 0 < P.L T) (hφc : Continuous (P.phi T))
    (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0) (p q : ZI Z T) :
    |⟪blockImVec (blockData Z T P hconj) c q, blockReVec (blockData Z T P hconj) c p⟫ -
        P.L T * (∫ u in (-(P.L T / 2))..(P.L T / 2),
          P.phi T u ^ 2 * Real.cosh (((p : ℂ).re - 1 / 2) * u) *
            Real.sinh (((q : ℂ).re - 1 / 2) * u) * Real.sin (((q : ℂ).im - (p : ℂ).im) * u)) / c| ≤
      Real.sqrt (P.L T * (∫ u in (-(P.L T / 2))..(P.L T / 2),
            P.phi T u ^ 2 * Real.cosh (((p : ℂ).re - 1 / 2) * u) *
              Real.cosh (((p : ℂ).re - 1 / 2) * u) * Real.cos (0 * u)) -
          ∑ k : Fin (P.d T), (P.phiHat T (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) *
            (2 * Real.pi / P.L T))) : ℝ) : ℂ) - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I)).re ^ 2) *
        Real.sqrt (P.L T * (∫ u in (-(P.L T / 2))..(P.L T / 2),
            ‖((P.phi T u : ℝ) : ℂ) * cexp ((((q : ℂ).re - 1 / 2 : ℝ) : ℂ) * u) *
              cexp (I * (((q : ℂ).im - (p : ℂ).im : ℝ) : ℂ) * u)‖ ^ 2) -
          ∑ k : Fin (P.d T), ‖P.phiHat T (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) *
            (2 * Real.pi / P.L T)) + ((q : ℂ).im - (p : ℂ).im)) : ℝ) : ℂ) -
              (((q : ℂ).re - 1 / 2 : ℝ) : ℂ) * I)‖ ^ 2) / c := by
  classical
  set γ := (p : ℂ).im with hγ
  set εp := (p : ℂ).re - 1 / 2 with hεp
  set εq := (q : ℂ).re - 1 / 2 with hεq
  set Δ := (q : ℂ).im - (p : ℂ).im with hΔ
  set L := P.L T with hLdef
  set w : ℤ → ℝ := fun j => γ - (T + j * (2 * Real.pi / L)) with hw
  set a : ℤ → ℝ := fun j => (P.phiHat T (((w j : ℝ) : ℂ) - (εp : ℂ) * I)).re with ha
  set b : ℤ → ℝ := fun j => (P.phiHat T ((((w j + Δ) : ℝ) : ℂ) - (εq : ℂ) * I)).im with hb
  set cc : ℤ → ℝ := fun j => ‖P.phiHat T ((((w j + Δ) : ℝ) : ℂ) - (εq : ℂ) * I)‖ ^ 2 with hcc
  -- the three full-grid series
  have hab := hasSum_re_mul_im_cross_grid P T hL hφc hsupp hconj γ Δ εp εq
  have haa := hasSum_re_mul_re_cross_grid P T hL hφc hsupp hconj γ 0 εp εp
  simp only [add_zero] at haa
  have hcc' : HasSum cc (L * ∫ u in (-(L / 2))..(L / 2),
      ‖((P.phi T u : ℝ) : ℂ) * cexp ((εq : ℂ) * u) * cexp (I * (Δ : ℂ) * u)‖ ^ 2) := by
    have h := hasSum_norm_sq_paperFT_grid hL
      (ψ := fun u => ((P.phi T u : ℝ) : ℂ) * cexp ((εq : ℂ) * u) * cexp (I * (Δ : ℂ) * u))
      (by fun_prop) (fun u hu => by simp [hsupp u hu]) γ T
    refine h.congr_fun fun j => ?_
    simp only [hcc, hw]
    rw [paperFT_shifted_window]
  have hbc : ∀ j, b j ^ 2 ≤ cc j := fun j => by
    simp only [hb, hcc]
    rw [← Complex.sq_norm_sub_sq_re]
    nlinarith [sq_nonneg (P.phiHat T ((((w j + Δ) : ℝ) : ℂ) - (εq : ℂ) * I)).re]
  have haa' : HasSum (fun j => a j ^ 2) (L * ∫ u in (-(L / 2))..(L / 2),
      P.phi T u ^ 2 * Real.cosh (εp * u) * Real.cosh (εp * u) * Real.cos (0 * u)) := by
    refine haa.congr_fun fun j => ?_
    simp only [ha, sq]
    rfl
  -- the block indices
  set S : Finset ℤ := Finset.univ.image fun k : Fin (P.d T) => ((k : ℕ) : ℤ) with hS
  have hinj : Set.InjOn (fun k : Fin (P.d T) => ((k : ℕ) : ℤ))
      ((Finset.univ : Finset (Fin (P.d T))) : Set (Fin (P.d T))) := by
    intro x _ y _ h
    simp only [Nat.cast_inj] at h
    exact Fin.ext h
  have hsumS : ∀ f : ℤ → ℝ, ∑ j ∈ S, f j = ∑ k : Fin (P.d T), f ((k : ℕ) : ℤ) := fun f =>
    Finset.sum_image hinj
  have htrunc := abs_sub_sum_le_of_hasSum_le hab haa' hcc' hbc S
  rw [hsumS, hsumS, hsumS] at htrunc
  rw [inner_blockImVec_blockReVec_eq_grid hconj hc p q]
  have hc' : |c| = c := abs_of_pos hc
  rw [← sub_div, abs_div, hc']
  refine div_le_div_of_nonneg_right ?_ hc.le
  rw [abs_sub_comm]
  convert htrunc using 3

end Block

end RHTower
