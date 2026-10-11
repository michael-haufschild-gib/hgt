import GaloisForLFunctions.RHTower.XiExceptionalPointDiscrete

/-!
# The fold law at an exceptional point

Let `s* = ½ + h* + ix*` be an exceptional point: `Re ξ(s*) = 0`, `Im ξ'(s*) = 0`. Call it
*nondegenerate* if `ξ'(s*) ≠ 0` (so `ξ'(s*)` is real and nonzero) and `Re ξ''(s*) ≠ 0`. Put
`F(h, x) = Re ξ(½ + h + ix) = cos(hD)Ξ(x)`. Then `∂ₓF = −Im ξ'`, `∂ₓ²F = −Re ξ''`,
`∂ₕF = Re ξ'`.

**Theorem** (`fold_law`). At a nondegenerate exceptional point there are `r, ε > 0` such that for
`0 < |h − h*| < ε`:
* if `ξ'(s*)·Re ξ''(s*)·(h − h*) > 0`, then `cos(hD)Ξ` has two distinct real zeros in
  `(x* − r, x* + r)`;
* if `ξ'(s*)·Re ξ''(s*)·(h − h*) < 0`, then `cos(hD)Ξ` has no real zero in `[x* − r, x* + r]`.

So a nondegenerate exceptional point is a square-root fold. Two real zeros of the producer collide
at `x*` and leave the real axis on the side of `h*` fixed by the sign of `ξ'(s*)·Re ξ''(s*)`. The
fold closes (defects for `h < h*`, real zeros for `h > h*`) iff `ξ'(s*)·Re ξ''(s*) > 0`.

**Proof.**
* `F(h, x*) = ξ'(s*)(h − h*) + o(h − h*)`.
* `F(h*, x* ± r) ≈ −½ Re ξ''(s*) r²`.
* On the side where these signs differ, the intermediate value theorem gives a real zero on each
  side of `x*`.
* On the other side, `|∂ₓ²F| ≥ m > 0` near `(h*, x*)` gives
  `F(h, x) ≥ F(h, x*) − (∂ₓF(h, x*))²/(2m)` (after normalising the sign).
  `∂ₓF(h, x*) = −Im ξ'(½ + h + ix*) = O(h − h*)`, so the right side has the sign of
  `F(h, x*) ≍ |h − h*|`.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- `F(h, x) = Re ξ(½ + h + ix)`. -/
def foldF (h x : ℝ) : ℝ := (xi (((1 / 2 + h : ℝ) : ℂ) + x * I)).re

/-- `∂ₓF = −Im ξ'`. -/
def foldFx (h x : ℝ) : ℝ := -(deriv xi (((1 / 2 + h : ℝ) : ℂ) + x * I)).im

/-- `∂ₓ²F = −Re ξ''`. -/
def foldFxx (h x : ℝ) : ℝ := -(deriv (deriv xi) (((1 / 2 + h : ℝ) : ℂ) + x * I)).re

theorem hasDerivAt_xi_vertical (c x : ℝ) :
    HasDerivAt (fun y : ℝ => xi ((c : ℂ) + y * I)) (deriv xi ((c : ℂ) + x * I) * I) x := by
  have hp : HasDerivAt (fun y : ℝ => (c : ℂ) + y * I) I x := by
    simpa using ((hasDerivAt_id x).ofReal_comp.mul_const I).const_add (c : ℂ)
  exact (xi_differentiable _).hasDerivAt.comp x hp

theorem hasDerivAt_xi'_vertical (c x : ℝ) :
    HasDerivAt (fun y : ℝ => deriv xi ((c : ℂ) + y * I))
      (deriv (deriv xi) ((c : ℂ) + x * I) * I) x := by
  have hp : HasDerivAt (fun y : ℝ => (c : ℂ) + y * I) I x := by
    simpa using ((hasDerivAt_id x).ofReal_comp.mul_const I).const_add (c : ℂ)
  exact ((xi_analyticAt _).deriv.differentiableAt.hasDerivAt).comp x hp

theorem hasDerivAt_foldF_x (h x : ℝ) : HasDerivAt (foldF h) (foldFx h x) x := by
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_xi_vertical (1 / 2 + h) x)
  have e : Complex.reCLM (deriv xi (((1 / 2 + h : ℝ) : ℂ) + x * I) * I) = foldFx h x := by
    simp [foldFx, Complex.mul_re]
  rw [e] at this
  exact this

theorem hasDerivAt_foldFx_x (h x : ℝ) : HasDerivAt (foldFx h) (foldFxx h x) x := by
  have := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_xi'_vertical (1 / 2 + h) x)).neg
  have e : -Complex.imCLM (deriv (deriv xi) (((1 / 2 + h : ℝ) : ℂ) + x * I) * I) = foldFxx h x := by
    simp [foldFxx, Complex.mul_im]
  rw [e] at this
  exact this

theorem hasDerivAt_foldF_h (h x : ℝ) :
    HasDerivAt (fun h => foldF h x) (deriv xi (((1 / 2 + h : ℝ) : ℂ) + x * I)).re h := by
  have hp : HasDerivAt (fun h : ℝ => (((1 / 2 + h : ℝ) : ℂ) + x * I)) 1 h := by
    have := ((hasDerivAt_id h).const_add (1 / 2 : ℝ)).ofReal_comp.add_const ((x : ℂ) * I)
    simpa using this
  have h1 : HasDerivAt (fun h => foldF h x)
      (Complex.reCLM (deriv xi (((1 / 2 + h : ℝ) : ℂ) + x * I) * 1)) h :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt h ((xi_differentiable _).hasDerivAt.comp h hp)
  rw [mul_one, Complex.reCLM_apply] at h1
  exact h1

theorem cosProducer_eq_foldF (h x : ℝ) : cosProducer h x = (foldF h x : ℂ) := by
  rw [cosProducer_ofReal, foldF]
  congr 3; push_cast; ring

theorem continuous_foldF_uncurry : Continuous fun p : ℝ × ℝ => foldF p.1 p.2 := by
  unfold foldF
  exact Complex.continuous_re.comp (xi_differentiable.continuous.comp (by fun_prop))

theorem continuous_foldFx_uncurry : Continuous fun p : ℝ × ℝ => foldFx p.1 p.2 := by
  unfold foldFx
  have hd : Continuous (deriv xi) := by
    rw [← continuousOn_univ]
    exact (xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ).deriv.continuousOn
  exact (Complex.continuous_im.comp (hd.comp (by fun_prop))).neg

theorem continuous_foldFxx_uncurry : Continuous fun p : ℝ × ℝ => foldFxx p.1 p.2 := by
  unfold foldFxx
  have hd : Continuous (deriv (deriv xi)) := by
    rw [← continuousOn_univ]
    exact (xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ).deriv.deriv.continuousOn
  exact (Complex.continuous_re.comp (hd.comp (by fun_prop))).neg

/-! ## A quadratic lower bound from a second-derivative bound -/

/-- If `f'' ≥ m` on `[a − r, a + r]`, then `f(x) ≥ f(a) + f'(a)(x − a) + (m/2)(x − a)²` there. -/
theorem quadratic_lower_bound {f f' f'' : ℝ → ℝ} {a r m : ℝ}
    (hf : ∀ x ∈ Icc (a - r) (a + r), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (a - r) (a + r), HasDerivAt f' (f'' x) x)
    (hm : ∀ x ∈ Icc (a - r) (a + r), m ≤ f'' x) :
    ∀ x ∈ Icc (a - r) (a + r), f a + f' a * (x - a) + m / 2 * (x - a) ^ 2 ≤ f x := by
  intro x hx
  have hr : 0 ≤ r := by linarith [hx.1, hx.2]
  set φ : ℝ → ℝ := fun t => f t - f a - f' a * (t - a) - m / 2 * (t - a) ^ 2 with hφ
  set φ' : ℝ → ℝ := fun t => f' t - f' a - m * (t - a) with hφ'
  have hφd : ∀ t ∈ Icc (a - r) (a + r), HasDerivAt φ (φ' t) t := by
    intro t ht
    have h1 := ((hf t ht).sub_const (f a)).sub (((hasDerivAt_id t).sub_const a).const_mul (f' a))
    have h2 := (((hasDerivAt_id t).sub_const a).pow 2).const_mul (m / 2)
    exact (h1.sub h2).congr_deriv (by norm_num [hφ']; ring)
  have hφ'd : ∀ t ∈ Icc (a - r) (a + r), HasDerivAt φ' (f'' t - m) t := by
    intro t ht
    have h := ((hf' t ht).sub_const (f' a)).sub (((hasDerivAt_id t).sub_const a).const_mul m)
    exact h.congr_deriv (by ring)
  have hmono' : MonotoneOn φ' (Icc (a - r) (a + r)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t ht => (hφ'd t ht).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Icc]; intro t ht
      exact (hφ'd t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      rw [(hφ'd t (Ioo_subset_Icc_self ht)).deriv]
      linarith [hm t (Ioo_subset_Icc_self ht)]
  have ha : a ∈ Icc (a - r) (a + r) := ⟨by linarith, by linarith⟩
  have hφa : φ a = 0 := by simp [hφ]
  have hφ'a : φ' a = 0 := by simp [hφ']
  suffices 0 ≤ φ x by simp only [hφ] at this; linarith
  rcases le_total a x with hax | hxa
  · have hsub : Icc a (a + r) ⊆ Icc (a - r) (a + r) := Icc_subset_Icc (by linarith) le_rfl
    have hmono : MonotoneOn φ (Icc a (a + r)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun t ht => (hφd t (hsub ht)).continuousAt.continuousWithinAt) ?_ ?_
      · rw [interior_Icc]; intro t ht
        exact (hφd t (hsub (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]; intro t ht
        have htI := hsub (Ioo_subset_Icc_self ht)
        rw [(hφd t htI).deriv, ← hφ'a]
        exact hmono' ha htI ht.1.le
    have := hmono ⟨le_rfl, by linarith⟩ ⟨hax, hx.2⟩ hax
    rwa [hφa] at this
  · have hsub : Icc (a - r) a ⊆ Icc (a - r) (a + r) := Icc_subset_Icc le_rfl (by linarith)
    have hanti : AntitoneOn φ (Icc (a - r) a) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        (fun t ht => (hφd t (hsub ht)).continuousAt.continuousWithinAt) ?_ ?_
      · rw [interior_Icc]; intro t ht
        exact (hφd t (hsub (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]; intro t ht
        have htI := hsub (Ioo_subset_Icc_self ht)
        rw [(hφd t htI).deriv, ← hφ'a]
        exact hmono' htI ha ht.2.le
    have := hanti ⟨hx.1, hxa⟩ ⟨by linarith, le_rfl⟩ hxa
    rwa [hφa] at this

/-! ## The abstract concave fold -/

/-- **Concave fold.** Let `F(h, ·)` have `x`-derivatives `Fx`, `Fxx`, with `Fxx` jointly
continuous. Suppose `F(h₀, x₀) = 0`, `∂ₓF(h₀, x₀) = 0`, `∂ₓ²F(h₀, x₀) < 0`, and
`h ↦ F(h, x₀)`, `h ↦ ∂ₓF(h, x₀)` are differentiable at `h₀`, the first with nonzero derivative `c`.
Then for `h` near `h₀`, `F(h, ·)` has a zero on each side of `x₀` when `c(h − h₀) > 0`, and is
negative on `[x₀ − r, x₀ + r]` when `c(h − h₀) < 0`. -/
theorem concave_fold {F Fx Fxx : ℝ → ℝ → ℝ} {h₀ x₀ c d : ℝ}
    (hF : ∀ h x, HasDerivAt (F h) (Fx h x) x)
    (hFx : ∀ h x, HasDerivAt (Fx h) (Fxx h x) x)
    (hcFxx : Continuous fun p : ℝ × ℝ => Fxx p.1 p.2)
    (hFh : HasDerivAt (fun h => F h x₀) c h₀)
    (hFxh : HasDerivAt (fun h => Fx h x₀) d h₀)
    (h0 : F h₀ x₀ = 0) (h1 : Fx h₀ x₀ = 0) (h2 : Fxx h₀ x₀ < 0) (hc : c ≠ 0) :
    ∃ r > 0, ∃ ε > 0, ∀ h, 0 < |h - h₀| → |h - h₀| < ε →
      (0 < c * (h - h₀) →
        ∃ x₁ ∈ Ioo (x₀ - r) x₀, ∃ x₂ ∈ Ioo x₀ (x₀ + r), F h x₁ = 0 ∧ F h x₂ = 0) ∧
      (c * (h - h₀) < 0 → ∀ x ∈ Icc (x₀ - r) (x₀ + r), F h x < 0) := by
  -- uniform concavity
  set m : ℝ := -Fxx h₀ x₀ / 2 with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (h₀, x₀), Fxx p.1 p.2 < -m :=
    hcFxx.continuousAt.eventually_lt continuousAt_const (by simp only; linarith)
  obtain ⟨ρ, hρ, hρall⟩ := Metric.eventually_nhds_iff.mp hev
  set r : ℝ := ρ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hconc : ∀ h, |h - h₀| < ρ → ∀ x ∈ Icc (x₀ - r) (x₀ + r), Fxx h x ≤ -m := by
    intro h hh x hx
    refine (hρall (y := (h, x)) ?_).le
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    refine ⟨hh, ?_⟩
    rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
  -- the quadratic upper bound
  have hquad : ∀ h, |h - h₀| < ρ → ∀ x ∈ Icc (x₀ - r) (x₀ + r),
      F h x ≤ F h x₀ + Fx h x₀ * (x - x₀) - m / 2 * (x - x₀) ^ 2 := by
    intro h hh x hx
    have := quadratic_lower_bound (f := fun x => -F h x) (f' := fun x => -Fx h x)
      (f'' := fun x => -Fxx h x) (m := m) (fun x _ => (hF h x).neg) (fun x _ => (hFx h x).neg)
      (fun x hx => by linarith [hconc h hh x hx]) x hx
    linarith
  -- first-order control in `h`
  obtain ⟨A, hA⟩ : ∃ A, A = |c| := ⟨_, rfl⟩
  have hApos : 0 < A := hA ▸ abs_pos.mpr hc
  obtain ⟨B, hB⟩ : ∃ B, B = |d| + 1 := ⟨_, rfl⟩
  have hBpos : 0 < B := by rw [hB]; positivity
  obtain ⟨ε₁, hε₁, hall₁⟩ := Metric.eventually_nhds_iff.mp
    ((hasDerivAt_iff_isLittleO.mp hFh).def (half_pos hApos))
  obtain ⟨ε₂, hε₂, hall₂⟩ := Metric.eventually_nhds_iff.mp
    ((hasDerivAt_iff_isLittleO.mp hFxh).def one_pos)
  have hFbd : ∀ h, |h - h₀| < ε₁ → |F h x₀ - c * (h - h₀)| ≤ A / 2 * |h - h₀| := by
    intro h hh
    have := hall₁ (y := h) (by rwa [Real.dist_eq])
    simpa [h0, Real.norm_eq_abs, smul_eq_mul, mul_comm] using this
  have hFxbd : ∀ h, |h - h₀| < ε₂ → |Fx h x₀| ≤ B * |h - h₀| := by
    intro h hh
    have := hall₂ (y := h) (by rwa [Real.dist_eq])
    simp only [h1, sub_zero, Real.norm_eq_abs, smul_eq_mul, one_mul] at this
    have h3 : |(h - h₀) * d| = |d| * |h - h₀| := by rw [abs_mul, mul_comm]
    calc |Fx h x₀| = |(Fx h x₀ - (h - h₀) * d) + (h - h₀) * d| := by ring_nf
      _ ≤ |Fx h x₀ - (h - h₀) * d| + |(h - h₀) * d| := abs_add_le _ _
      _ ≤ |h - h₀| + |d| * |h - h₀| := by rw [h3]; linarith
      _ = B * |h - h₀| := by rw [hB]; ring
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * A + B * r := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min (min ε₁ ε₂) (min ρ (min (m * r ^ 2 / (4 * K)) (m * A / B ^ 2))) :=
    ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεle : ε ≤ ε₁ ∧ ε ≤ ε₂ ∧ ε ≤ ρ ∧ ε ≤ m * r ^ 2 / (4 * K) ∧ ε ≤ m * A / B ^ 2 := by
    rw [hε]
    exact ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  refine ⟨r, hrpos, ε, hεpos, fun h hδ hδε => ?_⟩
  have hFh' := hFbd h (hδε.trans_le hεle.1)
  have hFx' := hFxbd h (hδε.trans_le hεle.2.1)
  have hδρ : |h - h₀| < ρ := hδε.trans_le hεle.2.2.1
  have hδK : |h - h₀| * (4 * K) < m * r ^ 2 :=
    (lt_div_iff₀ (by positivity)).mp (hδε.trans_le hεle.2.2.2.1)
  have hδB : |h - h₀| * B ^ 2 < m * A :=
    (lt_div_iff₀ (by positivity)).mp (hδε.trans_le hεle.2.2.2.2)
  have hcδ : |c * (h - h₀)| = A * |h - h₀| := by rw [abs_mul, hA]
  have hAδ : 0 < A * |h - h₀| := mul_pos hApos hδ
  have hKexp : |h - h₀| * (4 * K) = 8 * (A * |h - h₀|) + 4 * (B * |h - h₀| * r) := by
    rw [hK]; ring
  have hb := abs_le.mp hFh'
  refine ⟨fun hpos => ?_, fun hneg => ?_⟩
  · -- two zeros
    have hcpos : c * (h - h₀) = A * |h - h₀| := by rw [← hcδ, abs_of_pos hpos]
    have hmid : 0 < F h x₀ := by linarith [hb.1]
    have hFle : F h x₀ ≤ 3 / 2 * (A * |h - h₀|) := by linarith [hb.2]
    have hFxr : |Fx h x₀ * r| ≤ B * |h - h₀| * r := by
      rw [abs_mul, abs_of_pos hrpos]; exact mul_le_mul_of_nonneg_right hFx' hrpos.le
    have hFxr' := abs_le.mp hFxr
    have hmr : 0 < m * r ^ 2 := by positivity
    have hendL : F h (x₀ - r) < 0 := by
      have hq := hquad h hδρ (x₀ - r) ⟨le_rfl, by linarith⟩
      have e1 : Fx h x₀ * (x₀ - r - x₀) = -(Fx h x₀ * r) := by ring
      have e2 : (x₀ - r - x₀) ^ 2 = r ^ 2 := by ring
      rw [e1, e2] at hq
      linarith [hFxr'.1]
    have hendR : F h (x₀ + r) < 0 := by
      have hq := hquad h hδρ (x₀ + r) ⟨by linarith, le_rfl⟩
      have e1 : Fx h x₀ * (x₀ + r - x₀) = Fx h x₀ * r := by ring
      have e2 : (x₀ + r - x₀) ^ 2 = r ^ 2 := by ring
      rw [e1, e2] at hq
      linarith [hFxr'.2]
    have hcont : Continuous (F h) :=
      continuous_iff_continuousAt.mpr fun x => (hF h x).continuousAt
    obtain ⟨x₁, hx₁, hx₁0⟩ := intermediate_value_Ioo (by linarith : x₀ - r ≤ x₀)
      hcont.continuousOn ⟨hendL, hmid⟩
    obtain ⟨x₂, hx₂, hx₂0⟩ := intermediate_value_Ioo' (by linarith : x₀ ≤ x₀ + r)
      hcont.continuousOn ⟨hendR, hmid⟩
    exact ⟨x₁, hx₁, x₂, hx₂, hx₁0, hx₂0⟩
  · -- no zeros
    have hcneg : c * (h - h₀) = -(A * |h - h₀|) := by rw [← hcδ, abs_of_neg hneg]; ring
    have hmid : F h x₀ ≤ -(A / 2 * |h - h₀|) := by linarith [hb.2]
    have hFxsq : Fx h x₀ ^ 2 ≤ (B * |h - h₀|) ^ 2 := by
      have := abs_le.mp hFx'
      exact sq_le_sq' this.1 this.2
    have hB2 : B ^ 2 * |h - h₀| ^ 2 < m * A * |h - h₀| := by
      have := mul_lt_mul_of_pos_right hδB hδ
      linarith
    have hfin : Fx h x₀ ^ 2 / (2 * m) < A / 2 * |h - h₀| := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    intro x hx
    have hq := hquad h hδρ x hx
    have hsq : Fx h x₀ * (x - x₀) - m / 2 * (x - x₀) ^ 2 ≤ Fx h x₀ ^ 2 / (2 * m) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [sq_nonneg (m * (x - x₀) - Fx h x₀)]
    linarith

theorem hasDerivAt_foldFx_h (h x : ℝ) :
    HasDerivAt (fun h => foldFx h x) (-(deriv (deriv xi) (((1 / 2 + h : ℝ) : ℂ) + x * I)).im) h := by
  have hp : HasDerivAt (fun h : ℝ => (((1 / 2 + h : ℝ) : ℂ) + x * I)) 1 h := by
    have := ((hasDerivAt_id h).const_add (1 / 2 : ℝ)).ofReal_comp.add_const ((x : ℂ) * I)
    simpa using this
  have h1 : HasDerivAt (fun h => (deriv xi (((1 / 2 + h : ℝ) : ℂ) + x * I)).im)
      (Complex.imCLM (deriv (deriv xi) (((1 / 2 + h : ℝ) : ℂ) + x * I) * 1)) h :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt h
      (((xi_analyticAt _).deriv.differentiableAt.hasDerivAt).comp h hp)
  rw [mul_one, Complex.imCLM_apply] at h1
  exact h1.neg

/-! ## The fold law -/

/-- **The fold law at a nondegenerate exceptional point.** Let `s* = ½ + h* + ix*` be exceptional
(`Re ξ(s*) = 0`, `Im ξ'(s*) = 0`) with `ξ'(s*) ≠ 0` and `Re ξ''(s*) ≠ 0`, and put
`κ = Re ξ'(s*) · Re ξ''(s*)`. There are `r, ε > 0` such that for `0 < |h − h*| < ε`:
* if `κ(h − h*) > 0`, `cos(hD)Ξ` has a real zero in `(x* − r, x*)` and one in `(x*, x* + r)`;
* if `κ(h − h*) < 0`, `cos(hD)Ξ` has no real zero in `[x* − r, x* + r]`.

So two real zeros of the producer collide at `x*` and leave the real axis as a conjugate pair on
the side `κ(h − h*) < 0`. -/
theorem fold_law {h₀ x₀ : ℝ} (hex : IsXiExceptional (((1 / 2 + h₀ : ℝ) : ℂ) + x₀ * I))
    (hc : deriv xi (((1 / 2 + h₀ : ℝ) : ℂ) + x₀ * I) ≠ 0)
    (hq : (deriv (deriv xi) (((1 / 2 + h₀ : ℝ) : ℂ) + x₀ * I)).re ≠ 0) :
    ∃ r > 0, ∃ ε > 0, ∀ h : ℝ, 0 < |h - h₀| → |h - h₀| < ε →
      (0 < (deriv xi (((1 / 2 + h₀ : ℝ) : ℂ) + x₀ * I)).re *
          (deriv (deriv xi) (((1 / 2 + h₀ : ℝ) : ℂ) + x₀ * I)).re * (h - h₀) →
        ∃ x₁ ∈ Ioo (x₀ - r) x₀, ∃ x₂ ∈ Ioo x₀ (x₀ + r),
          cosProducer h x₁ = 0 ∧ cosProducer h x₂ = 0) ∧
      ((deriv xi (((1 / 2 + h₀ : ℝ) : ℂ) + x₀ * I)).re *
          (deriv (deriv xi) (((1 / 2 + h₀ : ℝ) : ℂ) + x₀ * I)).re * (h - h₀) < 0 →
        ∀ x ∈ Icc (x₀ - r) (x₀ + r), cosProducer h x ≠ 0) := by
  set s : ℂ := ((1 / 2 + h₀ : ℝ) : ℂ) + x₀ * I with hs
  set c : ℝ := (deriv xi s).re with hcdef
  set q : ℝ := (deriv (deriv xi) s).re with hqdef
  have hcne : c ≠ 0 := by
    intro h0; apply hc
    exact Complex.ext (by rw [Complex.zero_re]; exact h0) (by rw [Complex.zero_im]; exact hex.2)
  have hF0 : foldF h₀ x₀ = 0 := hex.1
  have hFx0 : foldFx h₀ x₀ = 0 := by
    show -(deriv xi s).im = 0
    rw [hex.2, neg_zero]
  have hzero : ∀ h x : ℝ, cosProducer h x = 0 ↔ foldF h x = 0 := fun h x => by
    rw [cosProducer_eq_foldF, Complex.ofReal_eq_zero]
  rcases lt_or_gt_of_ne hq with hqneg | hqpos
  · -- `Re ξ'' < 0`: apply the concave fold to `−F`
    obtain ⟨r, hr, ε, hε, hall⟩ := concave_fold (F := fun h x => -foldF h x)
      (Fx := fun h x => -foldFx h x) (Fxx := fun h x => -foldFxx h x) (c := -c)
      (d := (deriv (deriv xi) s).im) (h₀ := h₀) (x₀ := x₀)
      (fun h x => (hasDerivAt_foldF_x h x).neg) (fun h x => (hasDerivAt_foldFx_x h x).neg)
      continuous_foldFxx_uncurry.neg (hasDerivAt_foldF_h h₀ x₀).neg
      (by have := (hasDerivAt_foldFx_h h₀ x₀).neg; rw [neg_neg] at this; exact this)
      (by simp only [hF0, neg_zero]) (by simp only [hFx0, neg_zero])
      (by show -(-(deriv (deriv xi) s).re) < 0; rw [neg_neg]; exact hqneg) (neg_ne_zero.mpr hcne)
    refine ⟨r, hr, ε, hε, fun h h1 h2 => ⟨fun hpos => ?_, fun hneg => ?_⟩⟩
    · have : 0 < -c * (h - h₀) := by nlinarith
      obtain ⟨x₁, hx₁, x₂, hx₂, h₁, h₂⟩ := (hall h h1 h2).1 this
      exact ⟨x₁, hx₁, x₂, hx₂, (hzero h x₁).mpr (neg_eq_zero.mp h₁),
        (hzero h x₂).mpr (neg_eq_zero.mp h₂)⟩
    · have : -c * (h - h₀) < 0 := by nlinarith
      intro x hx h0
      have h3 : -foldF h x < 0 := (hall h h1 h2).2 this x hx
      rw [(hzero h x).mp h0, neg_zero] at h3
      exact lt_irrefl _ h3
  · -- `Re ξ'' > 0`: apply the concave fold to `F`
    obtain ⟨r, hr, ε, hε, hall⟩ := concave_fold (F := foldF) (Fx := foldFx) (Fxx := foldFxx)
      (c := c) (d := -(deriv (deriv xi) s).im) (h₀ := h₀) (x₀ := x₀)
      hasDerivAt_foldF_x hasDerivAt_foldFx_x continuous_foldFxx_uncurry
      (hasDerivAt_foldF_h h₀ x₀) (hasDerivAt_foldFx_h h₀ x₀) hF0 hFx0
      (by show -(deriv (deriv xi) s).re < 0; exact neg_neg_of_pos hqpos) hcne
    refine ⟨r, hr, ε, hε, fun h h1 h2 => ⟨fun hpos => ?_, fun hneg => ?_⟩⟩
    · have : 0 < c * (h - h₀) := by nlinarith
      obtain ⟨x₁, hx₁, x₂, hx₂, h₁, h₂⟩ := (hall h h1 h2).1 this
      exact ⟨x₁, hx₁, x₂, hx₂, (hzero h x₁).mpr h₁, (hzero h x₂).mpr h₂⟩
    · have : c * (h - h₀) < 0 := by nlinarith
      intro x hx h0
      have := (hall h h1 h2).2 this x hx
      rw [(hzero h x).mp h0] at this; exact lt_irrefl _ this

end

end RHTower
