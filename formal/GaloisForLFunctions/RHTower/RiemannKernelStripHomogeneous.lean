import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel

/-!
# The second-order Ξ-equation and its bounded solution

Let `a₁, a₂` be nonzero reals and `m(z) = 1/((1 − iz/a₁)(1 − iz/a₂))`.  The transform

  `ψ_m(x) = ∫ Φ(u) m(u) e^{ixu} du`

solves `ψ − (1/a₁ + 1/a₂)ψ′ + ψ″/(a₁a₂) = Ξ` (`kernelPsi_ode`).  Differentiating under the integral
multiplies `Φm` by `iu`, and `(1 − iu/a₁)(1 − iu/a₂)` cancels `m`.  The transform is bounded by
`∫|Φ|` (`norm_kernelPsi_le`).

Any other real solution `ψ` differs from `ψ_m` by a homogeneous solution `d` of
`(D − a₁)(D − a₂)d = 0`.  So `d = Ae^{a₁x} + Be^{a₂x}`, or `d = (A + Bx)e^{ax}` when `a₁ = a₂ = a`.
At every zero of `ψ`, `|d| = |ψ_m| ≤ ∫|Φ|`.  A nonzero exponential sum with nonzero real exponents
is unbounded towards at least one end, along every sequence going to that end.  Hence, if `ψ` has
zeros arbitrarily far out at both ends, then `d = 0` and `ψ = ψ_m`
(`ofReal_eq_kernelPsi_of_ode`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower.KernelStrip

noncomputable section

/-! ## Unbounded exponential sums -/

/-- A function that eventually exceeds `δe^{γx}` (`γ, δ > 0`) is not bounded along any sequence
tending to `+∞`. -/
theorem false_of_growth {f : ℝ → ℝ} {K γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hev : ∀ᶠ x in atTop, δ * Real.exp (γ * x) ≤ f x) (hz : ∀ T, ∃ x > T, f x ≤ K) : False := by
  have ht : Tendsto (fun x : ℝ => δ * Real.exp (γ * x)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hγ)).const_mul_atTop hδ
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((ht.eventually_gt_atTop K).and hev)
  obtain ⟨x, hx, hfx⟩ := hz T
  have := hT x hx.le
  linarith [this.1, this.2]

/-- Dominance of the larger exponent at `+∞`: if `q < p`, `0 < p` and `P ≠ 0`, then eventually
`|P|/2·e^{px} ≤ |Pe^{px} + Qe^{qx}|`. -/
theorem eventually_dominant {p q : ℝ} (hqp : q < p) {P Q : ℂ} (hP : P ≠ 0) :
    ∀ᶠ x in atTop, ‖P‖ / 2 * Real.exp (p * x) ≤
      ‖P * (Real.exp (p * x) : ℂ) + Q * (Real.exp (q * x) : ℂ)‖ := by
  have hP0 : 0 < ‖P‖ := norm_pos_iff.mpr hP
  have ht : Tendsto (fun x : ℝ => ‖Q‖ * Real.exp ((q - p) * x)) atTop (𝓝 (‖Q‖ * 0)) :=
    (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))).const_mul _
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const (by linarith : (0 : ℝ) < ‖P‖ / 2)] with x hx
  have h1 : ‖P * (Real.exp (p * x) : ℂ)‖ = ‖P‖ * Real.exp (p * x) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h2 : ‖Q * (Real.exp (q * x) : ℂ)‖ = ‖Q‖ * Real.exp ((q - p) * x) * Real.exp (p * x) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_assoc,
      ← Real.exp_add]
    ring_nf
  have h3 := norm_sub_norm_le (P * (Real.exp (p * x) : ℂ)) (-(Q * (Real.exp (q * x) : ℂ)))
  rw [sub_neg_eq_add, norm_neg, h1, h2] at h3
  have h4 : ‖Q‖ * Real.exp ((q - p) * x) * Real.exp (p * x) ≤ ‖P‖ / 2 * Real.exp (p * x) :=
    mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
  linarith

/-- Reflection: zeros arbitrarily far towards `−∞` become zeros arbitrarily far towards `+∞`. -/
theorem neg_cofinal {f : ℝ → ℂ} {K : ℝ} (h : ∀ T, ∃ x < -T, ‖f x‖ ≤ K) :
    ∀ T, ∃ y > T, ‖f (-y)‖ ≤ K := by
  intro T
  obtain ⟨x, hx, hfx⟩ := h T
  exact ⟨-x, by linarith, by simpa using hfx⟩

/-- Two distinct nonzero exponents with `β < α`: an exponential sum bounded along sequences going to
both ends vanishes. -/
theorem expPair_eq_zero_of_lt {α β K : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (hβα : β < α) {A B : ℂ}
    (hp : ∀ T, ∃ x > T, ‖A * (Real.exp (α * x) : ℂ) + B * (Real.exp (β * x) : ℂ)‖ ≤ K)
    (hn : ∀ T, ∃ x < -T, ‖A * (Real.exp (α * x) : ℂ) + B * (Real.exp (β * x) : ℂ)‖ ≤ K) :
    A = 0 ∧ B = 0 := by
  -- the reflected sum
  have hn' : ∀ T, ∃ y > T, ‖B * (Real.exp (-β * y) : ℂ) + A * (Real.exp (-α * y) : ℂ)‖ ≤ K := by
    intro T
    obtain ⟨y, hy, hfy⟩ := neg_cofinal (f := fun x : ℝ =>
      A * (Real.exp (α * x) : ℂ) + B * (Real.exp (β * x) : ℂ)) hn T
    refine ⟨y, hy, ?_⟩
    simp only [mul_neg, neg_mul] at hfy ⊢
    rwa [add_comm]
  have hpos : ∀ (P Q : ℂ) (p q : ℝ), q < p → 0 < p → P ≠ 0 →
      (∀ T, ∃ x > T, ‖P * (Real.exp (p * x) : ℂ) + Q * (Real.exp (q * x) : ℂ)‖ ≤ K) → False := by
    intro P Q p q hqp hp0 hP hz
    exact false_of_growth hp0 (by positivity : 0 < ‖P‖ / 2) (eventually_dominant hqp hP) hz
  by_contra hne
  rcases lt_or_gt_of_ne hα with hα0 | hα0
  · -- `α < 0`, so `β < 0` and the reflected exponents `−β > −α > 0`
    have hβ0 : β < 0 := by linarith
    by_cases hB : B = 0
    · have hA : A ≠ 0 := fun hA => hne ⟨hA, hB⟩
      refine hpos A 0 (-α) (-α - 1) (by linarith) (by linarith) hA fun T => ?_
      obtain ⟨y, hy, hfy⟩ := hn' T
      refine ⟨y, hy, ?_⟩
      simpa [hB] using hfy
    · exact hpos B A (-β) (-α) (by linarith) (by linarith) hB hn'
  · -- `α > 0`
    by_cases hA : A = 0
    · have hB : B ≠ 0 := fun hB => hne ⟨hA, hB⟩
      rcases lt_or_gt_of_ne hβ with hβ0 | hβ0
      · refine hpos B 0 (-β) (-β - 1) (by linarith) (by linarith) hB fun T => ?_
        obtain ⟨y, hy, hfy⟩ := hn' T
        refine ⟨y, hy, ?_⟩
        simpa [hA] using hfy
      · refine hpos B 0 β (β - 1) (by linarith) hβ0 hB fun T => ?_
        obtain ⟨x, hx, hfx⟩ := hp T
        refine ⟨x, hx, ?_⟩
        simpa [hA] using hfx
    · exact hpos A B α β hβα hα0 hA hp

/-- Two distinct nonzero exponents: an exponential sum bounded along sequences going to both ends
vanishes. -/
theorem expPair_eq_zero {α β K : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α ≠ β) {A B : ℂ}
    (hp : ∀ T, ∃ x > T, ‖A * (Real.exp (α * x) : ℂ) + B * (Real.exp (β * x) : ℂ)‖ ≤ K)
    (hn : ∀ T, ∃ x < -T, ‖A * (Real.exp (α * x) : ℂ) + B * (Real.exp (β * x) : ℂ)‖ ≤ K) :
    A = 0 ∧ B = 0 := by
  rcases lt_or_gt_of_ne hαβ with h | h
  · have hp' : ∀ T, ∃ x > T, ‖B * (Real.exp (β * x) : ℂ) + A * (Real.exp (α * x) : ℂ)‖ ≤ K :=
      fun T => by obtain ⟨x, hx, h⟩ := hp T; exact ⟨x, hx, by rwa [add_comm]⟩
    have hn' : ∀ T, ∃ x < -T, ‖B * (Real.exp (β * x) : ℂ) + A * (Real.exp (α * x) : ℂ)‖ ≤ K :=
      fun T => by obtain ⟨x, hx, h⟩ := hn T; exact ⟨x, hx, by rwa [add_comm]⟩
    exact (expPair_eq_zero_of_lt hβ hα h hp' hn').symm
  · exact expPair_eq_zero_of_lt hα hβ h hp hn

/-- A repeated nonzero exponent: `(A + Bx)e^{ax}` bounded along sequences going to both ends
vanishes. -/
theorem expLin_eq_zero {a K : ℝ} (ha : a ≠ 0) {A B : ℂ}
    (hp : ∀ T, ∃ x > T, ‖(A + B * x) * (Real.exp (a * x) : ℂ)‖ ≤ K)
    (hn : ∀ T, ∃ x < -T, ‖(A + B * x) * (Real.exp (a * x) : ℂ)‖ ≤ K) :
    A = 0 ∧ B = 0 := by
  -- growth at `+∞` for a positive exponent
  have hgrow : ∀ (P Q : ℂ) (b : ℝ), 0 < b → (P ≠ 0 ∨ Q ≠ 0) →
      (∀ T, ∃ x > T, ‖(P + Q * x) * (Real.exp (b * x) : ℂ)‖ ≤ K) → False := by
    intro P Q b hb hPQ hz
    have hnorm : ∀ x : ℝ, ‖(P + Q * x) * (Real.exp (b * x) : ℂ)‖ =
        ‖P + Q * x‖ * Real.exp (b * x) := by
      intro x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    by_cases hQ : Q = 0
    · have hP : P ≠ 0 := hPQ.resolve_right (not_not.mpr hQ)
      refine false_of_growth hb (norm_pos_iff.mpr hP) (Eventually.of_forall fun x => ?_) hz
      rw [hnorm, hQ, zero_mul, add_zero]
    · have hQ0 : 0 < ‖Q‖ := norm_pos_iff.mpr hQ
      refine false_of_growth hb one_pos ?_ hz
      filter_upwards [eventually_ge_atTop ((1 + ‖P‖) / ‖Q‖), eventually_ge_atTop 0] with x hx hx0
      rw [hnorm]
      have h1 : 1 ≤ ‖P + Q * x‖ := by
        have h2 : ‖Q * (x : ℂ)‖ = ‖Q‖ * x := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
        have h3 := norm_sub_norm_le (Q * (x : ℂ)) (-P)
        rw [sub_neg_eq_add, norm_neg, h2, add_comm] at h3
        rw [div_le_iff₀ hQ0] at hx
        linarith
      calc 1 * Real.exp (b * x) ≤ ‖P + Q * x‖ * Real.exp (b * x) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = ‖P + Q * x‖ * Real.exp (b * x) := rfl
  by_contra hne
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_contra h; push Not at h; exact hne h
  rcases lt_or_gt_of_ne ha with ha0 | ha0
  · refine hgrow A (-B) (-a) (by linarith) (hAB.imp id (fun h => neg_ne_zero.mpr h)) fun T => ?_
    obtain ⟨x, hx, hfx⟩ := hn T
    refine ⟨-x, by linarith, ?_⟩
    have e : (A + -B * ((-x : ℝ) : ℂ)) * (Real.exp (-a * -x) : ℂ) =
        (A + B * x) * (Real.exp (a * x) : ℂ) := by
      push_cast; ring_nf
    rw [e]; exact hfx
  · exact hgrow A B a ha0 hAB hp

/-! ## The homogeneous equation -/

/-- **Homogeneous solutions bounded along both ends vanish.**  If `d − (1/a₁ + 1/a₂)d′ + d″/(a₁a₂) = 0`
with nonzero real `a_j`, and `|d| ≤ K` along sequences going to `+∞` and to `−∞`, then `d = 0`. -/
theorem eq_zero_of_homogeneous {a₁ a₂ K : ℝ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) {d d' d'' : ℝ → ℂ}
    (hd : ∀ x, HasDerivAt d (d' x) x) (hd' : ∀ x, HasDerivAt d' (d'' x) x)
    (hode : ∀ x, d x - ((1 / a₁ + 1 / a₂ : ℝ) : ℂ) * d' x + ((1 / (a₁ * a₂) : ℝ) : ℂ) * d'' x = 0)
    (hp : ∀ T, ∃ x > T, ‖d x‖ ≤ K) (hn : ∀ T, ∃ x < -T, ‖d x‖ ≤ K) : ∀ x, d x = 0 := by
  have hc₁ : (a₁ : ℂ) ≠ 0 := by exact_mod_cast ha₁
  have hc₂ : (a₂ : ℂ) ≠ 0 := by exact_mod_cast ha₂
  -- `d″ = (a₁ + a₂)d′ − a₁a₂ d`
  have hdd : ∀ x, d'' x = (a₁ + a₂) * d' x - a₁ * a₂ * d x := by
    intro x
    have h := hode x
    push_cast at h
    field_simp at h
    linear_combination h
  -- `e = d′ − a₂ d` satisfies `e′ = a₁ e`
  set e : ℝ → ℂ := fun x => d' x - a₂ * d x with he
  have hed : ∀ x, HasDerivAt e (a₁ * e x) x := by
    intro x
    have h := (hd' x).sub ((hd x).const_mul (a₂ : ℂ))
    refine h.congr_deriv ?_
    simp only [he]
    rw [hdd x]; ring
  -- `e(x) = e(0)e^{a₁x}`
  have hexp : ∀ (b : ℝ) (x : ℝ), HasDerivAt (fun x : ℝ => (Real.exp (b * x) : ℂ))
      (b * (Real.exp (b * x) : ℂ)) x := by
    intro b x
    have h := ((Real.hasDerivAt_exp (b * x)).comp x ((hasDerivAt_id x).const_mul b)).ofReal_comp
    refine h.congr_deriv ?_
    push_cast; ring
  have hconst : ∀ {F : ℝ → ℂ}, (∀ x, HasDerivAt F 0 x) → ∀ x, F x = F 0 := by
    intro F hF x
    exact is_const_of_deriv_eq_zero (fun y => (hF y).differentiableAt)
      (fun y => (hF y).deriv) x 0
  have he_eq : ∀ x, e x = e 0 * (Real.exp (a₁ * x) : ℂ) := by
    have h := hconst (F := fun x => e x * (Real.exp (-a₁ * x) : ℂ)) fun x => by
      have := (hed x).mul (hexp (-a₁) x)
      refine this.congr_deriv ?_
      push_cast; ring
    intro x
    have h1 := h x
    simp only [mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one] at h1
    have h2 : (Real.exp (-a₁ * x) : ℂ) * (Real.exp (a₁ * x) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
    calc e x = e x * ((Real.exp (-a₁ * x) : ℂ) * (Real.exp (a₁ * x) : ℂ)) := by rw [h2, mul_one]
      _ = e 0 * (Real.exp (a₁ * x) : ℂ) := by rw [← mul_assoc, h1]
  -- `F = d e^{−a₂x}` has `F′ = e(0)e^{(a₁−a₂)x}`
  have hF : ∀ x, HasDerivAt (fun x => d x * (Real.exp (-a₂ * x) : ℂ))
      (e 0 * (Real.exp ((a₁ - a₂) * x) : ℂ)) x := by
    intro x
    have h := (hd x).mul (hexp (-a₂) x)
    refine h.congr_deriv ?_
    have h1 : d' x - (a₂ : ℂ) * d x = e 0 * (Real.exp (a₁ * x) : ℂ) := he_eq x
    have h2 : (Real.exp ((a₁ - a₂) * x) : ℂ) =
        (Real.exp (a₁ * x) : ℂ) * (Real.exp (-a₂ * x) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; ring_nf
    rw [h2]
    simp only [Complex.ofReal_neg]
    linear_combination (Real.exp (-a₂ * x) : ℂ) * h1
  have hback : ∀ x, d x = (d x * (Real.exp (-a₂ * x) : ℂ)) * (Real.exp (a₂ * x) : ℂ) := by
    intro x
    rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  rcases eq_or_ne a₁ a₂ with h12 | h12
  · -- repeated exponent: `d = (d(0) + e(0)x)e^{a₂x}`
    have hG := hconst (F := fun x => d x * (Real.exp (-a₂ * x) : ℂ) - e 0 * x) fun x => by
      have := (hF x).sub ((hasDerivAt_id x).ofReal_comp.const_mul (e 0))
      refine this.congr_deriv ?_
      rw [h12, sub_self, zero_mul, Real.exp_zero]; simp
    have hform : ∀ x, d x = (d 0 + e 0 * x) * (Real.exp (a₂ * x) : ℂ) := by
      intro x
      have := hG x
      simp only [Complex.ofReal_zero, mul_zero, sub_zero, Real.exp_zero, Complex.ofReal_one,
        mul_one] at this
      rw [hback x]
      linear_combination (Real.exp (a₂ * x) : ℂ) * this
    obtain ⟨h0, h1⟩ := expLin_eq_zero ha₂ (A := d 0) (B := e 0)
      (fun T => by obtain ⟨x, hx, h⟩ := hp T; exact ⟨x, hx, by rwa [← hform x]⟩)
      (fun T => by obtain ⟨x, hx, h⟩ := hn T; exact ⟨x, hx, by rwa [← hform x]⟩)
    intro x
    rw [hform x, h0, h1]; simp
  · -- distinct exponents: `d = Ae^{a₁x} + Be^{a₂x}`
    have hsub : (a₁ - a₂ : ℝ) ≠ 0 := sub_ne_zero.mpr h12
    have hsubc : ((a₁ - a₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsub
    have hG := hconst (F := fun x => d x * (Real.exp (-a₂ * x) : ℂ) -
        e 0 / ((a₁ - a₂ : ℝ) : ℂ) * (Real.exp ((a₁ - a₂) * x) : ℂ)) fun x => by
      have := (hF x).sub ((hexp (a₁ - a₂) x).const_mul (e 0 / ((a₁ - a₂ : ℝ) : ℂ)))
      refine this.congr_deriv ?_
      field_simp
      ring
    set A : ℂ := e 0 / ((a₁ - a₂ : ℝ) : ℂ)
    set B : ℂ := d 0 - A
    have hform : ∀ x, d x = A * (Real.exp (a₁ * x) : ℂ) + B * (Real.exp (a₂ * x) : ℂ) := by
      intro x
      have := hG x
      simp only [mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one] at this
      have h2 : (Real.exp ((a₁ - a₂) * x) : ℂ) * (Real.exp (a₂ * x) : ℂ) =
          (Real.exp (a₁ * x) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]; ring_nf
      rw [hback x]
      linear_combination (Real.exp (a₂ * x) : ℂ) * this + A * h2
    obtain ⟨h0, h1⟩ := expPair_eq_zero ha₁ ha₂ h12 (A := A) (B := B)
      (fun T => by obtain ⟨x, hx, h⟩ := hp T; exact ⟨x, hx, by rwa [← hform x]⟩)
      (fun T => by obtain ⟨x, hx, h⟩ := hn T; exact ⟨x, hx, by rwa [← hform x]⟩)
    intro x
    rw [hform x, h0, h1]; simp

/-! ## The transform `ψ_m` -/

/-- `m(z) = 1/((1 − iz/a₁)(1 − iz/a₂))`. -/
def lorentzPair (a₁ a₂ : ℝ) (z : ℂ) : ℂ := 1 / ((1 - I * z / a₁) * (1 - I * z / a₂))

theorem one_sub_I_mul_div_eq (a u : ℝ) : 1 - I * (u : ℂ) / a = 1 - ((u / a : ℝ) : ℂ) * I := by
  push_cast; ring

theorem one_le_norm_one_sub_I_mul_div (a u : ℝ) : 1 ≤ ‖1 - I * (u : ℂ) / a‖ := by
  rw [one_sub_I_mul_div_eq]
  have h := Complex.abs_re_le_norm (1 - ((u / a : ℝ) : ℂ) * I)
  have hre : (1 - ((u / a : ℝ) : ℂ) * I).re = 1 := by simp
  rw [hre, abs_one] at h
  exact h

theorem one_sub_I_mul_div_ne_zero (a u : ℝ) : 1 - I * (u : ℂ) / a ≠ 0 := by
  intro h
  have := one_le_norm_one_sub_I_mul_div a u
  rw [h, norm_zero] at this
  linarith

theorem norm_lorentzPair_le (a₁ a₂ u : ℝ) : ‖lorentzPair a₁ a₂ u‖ ≤ 1 := by
  rw [lorentzPair, norm_div, norm_one, norm_mul]
  have h1 := one_le_norm_one_sub_I_mul_div a₁ u
  have h2 := one_le_norm_one_sub_I_mul_div a₂ u
  rw [div_le_one (by positivity)]
  nlinarith

theorem continuous_lorentzPair (a₁ a₂ : ℝ) : Continuous fun u : ℝ => lorentzPair a₁ a₂ u := by
  unfold lorentzPair
  refine continuous_const.div (by fun_prop) fun u => ?_
  exact mul_ne_zero (one_sub_I_mul_div_ne_zero a₁ u) (one_sub_I_mul_div_ne_zero a₂ u)

/-- `(1 − iu/a₁)(1 − iu/a₂)·m(u) = 1`. -/
theorem lorentzPair_mul (a₁ a₂ u : ℝ) :
    lorentzPair a₁ a₂ u * ((1 - I * (u : ℂ) / a₁) * (1 - I * (u : ℂ) / a₂)) = 1 := by
  rw [lorentzPair, one_div, inv_mul_cancel₀]
  exact mul_ne_zero (one_sub_I_mul_div_ne_zero a₁ u) (one_sub_I_mul_div_ne_zero a₂ u)

theorem continuous_riemannPhiKernel : Continuous riemannPhiKernel := by
  rw [← riemannKernelDeriv_zero]; exact continuous_riemannKernelDeriv 0

/-- `|Φ(u)| ≤ C e^{−3|u|}` on the real line. -/
theorem exists_norm_riemannPhiKernel_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖riemannPhiKernel u‖ ≤ C * Real.exp (-(3 * |u|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_kernelC_le (c := 0) (by positivity) 3
  refine ⟨C, hC0, fun u => ?_⟩
  have h := hC (u : ℂ) (by simp)
  rwa [kernelC_ofReal, Complex.ofReal_re] at h

/-- A continuous function with `|F(u)| ≤ C e^{−|u|}` is integrable. -/
theorem integrable_of_norm_le_exp {F : ℝ → ℂ} (hF : Continuous F) {C : ℝ}
    (hb : ∀ u, ‖F u‖ ≤ C * Real.exp (-(1 * |u|))) : Integrable F :=
  ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C).mono'
    hF.aestronglyMeasurable (Eventually.of_forall hb)

theorem integrable_mul_cexp_I_mul {h : ℝ → ℂ} (hh : Integrable h) (x : ℝ) :
    Integrable (fun u : ℝ => h u * cexp (I * x * u)) := by
  refine hh.norm.mono' (hh.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable
    (by fun_prop))) (Eventually.of_forall fun u => ?_)
  rw [norm_mul, show I * (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The three profiles `h = Φm`, `h₁ = iuh`, `h₂ = iuh₁` and their integrability. -/
theorem lorentz_profiles_integrable (a₁ a₂ : ℝ) :
    Integrable (fun u : ℝ => riemannPhiKernel u * lorentzPair a₁ a₂ u) ∧
      Integrable (fun u : ℝ => (u : ℂ) * (riemannPhiKernel u * lorentzPair a₁ a₂ u)) ∧
      Integrable (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u)) ∧
      Integrable (fun u : ℝ => (u : ℂ) * (I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u))) ∧
      Integrable (fun u : ℝ => I * u * (I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le
  have hc : Continuous fun u : ℝ => riemannPhiKernel u * lorentzPair a₁ a₂ u :=
    continuous_riemannPhiKernel.mul (continuous_lorentzPair a₁ a₂)
  -- `|u|^k |h(u)| ≤ 2C e^{−|u|}` for `k ≤ 2`
  have hk : ∀ k : ℕ, k ≤ 2 → ∀ u : ℝ,
      |u| ^ k * ‖riemannPhiKernel u * lorentzPair a₁ a₂ u‖ ≤ 2 * C * Real.exp (-(1 * |u|)) := by
    intro k hk u
    have hu := abs_nonneg u
    have hh : ‖riemannPhiKernel u * lorentzPair a₁ a₂ u‖ ≤ C * Real.exp (-(3 * |u|)) := by
      rw [norm_mul]
      calc ‖riemannPhiKernel u‖ * ‖lorentzPair a₁ a₂ u‖ ≤ (C * Real.exp (-(3 * |u|))) * 1 :=
            mul_le_mul (hC u) (norm_lorentzPair_le a₁ a₂ u) (norm_nonneg _) (by positivity)
        _ = C * Real.exp (-(3 * |u|)) := mul_one _
    have hpow : |u| ^ k ≤ 2 * Real.exp (2 * |u|) := by
      have h2 := Real.pow_div_factorial_le_exp (2 * |u|) (by positivity) k
      have hf : (k.factorial : ℝ) ≤ 2 := by
        interval_cases k <;> norm_num [Nat.factorial]
      have hpk : |u| ^ k ≤ (2 * |u|) ^ k := pow_le_pow_left₀ hu (by linarith) k
      have hfpos : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
      rw [div_le_iff₀ hfpos] at h2
      nlinarith [Real.exp_pos (2 * |u|), pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * |u|) k]
    calc |u| ^ k * ‖riemannPhiKernel u * lorentzPair a₁ a₂ u‖
        ≤ (2 * Real.exp (2 * |u|)) * (C * Real.exp (-(3 * |u|))) :=
          mul_le_mul hpow hh (norm_nonneg _) (by positivity)
      _ = 2 * C * Real.exp (-(1 * |u|)) := by
          rw [show 2 * Real.exp (2 * |u|) * (C * Real.exp (-(3 * |u|))) =
            2 * C * (Real.exp (2 * |u|) * Real.exp (-(3 * |u|))) by ring, ← Real.exp_add]
          ring_nf
  have hnorm : ∀ u : ℝ, ‖(u : ℂ)‖ = |u| := fun u => by rw [Complex.norm_real, Real.norm_eq_abs]
  refine ⟨integrable_of_norm_le_exp hc (C := 2 * C) fun u => ?_,
    integrable_of_norm_le_exp (by fun_prop) (C := 2 * C) fun u => ?_,
    integrable_of_norm_le_exp (by fun_prop) (C := 2 * C) fun u => ?_,
    integrable_of_norm_le_exp (by fun_prop) (C := 2 * C) fun u => ?_,
    integrable_of_norm_le_exp (by fun_prop) (C := 2 * C) fun u => ?_⟩
  · simpa using hk 0 (by norm_num) u
  · rw [norm_mul, hnorm]; simpa using hk 1 (by norm_num) u
  · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, hnorm]; simpa using hk 1 (by norm_num) u
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, hnorm, ← mul_assoc, ← sq]
    simpa using hk 2 le_rfl u
  · rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul, hnorm,
      ← mul_assoc, ← sq]
    simpa using hk 2 le_rfl u

/-- **`ψ_m` solves the Ξ-equation**, with its two derivatives given by the transforms of `iuh` and
`(iu)²h`. -/
theorem kernelPsi_ode (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    (∀ x : ℝ, HasDerivAt (fun x : ℝ => kernelPsi (lorentzPair a₁ a₂) x)
        (paperFT (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u)) x) x) ∧
      (∀ x : ℝ, HasDerivAt
        (fun x : ℝ => paperFT (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u)) x)
        (paperFT (fun u : ℝ => I * u * (I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u))) x) x) ∧
      ∀ x : ℝ, kernelPsi (lorentzPair a₁ a₂) x -
          ((1 / a₁ + 1 / a₂ : ℝ) : ℂ) *
            paperFT (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u)) x +
          ((1 / (a₁ * a₂) : ℝ) : ℂ) *
            paperFT (fun u : ℝ => I * u * (I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u))) x =
        paperFT riemannPhiKernel x := by
  obtain ⟨i0, i1, i2, i3, i4⟩ := lorentz_profiles_integrable a₁ a₂
  set h : ℝ → ℂ := fun u => riemannPhiKernel u * lorentzPair a₁ a₂ u with hh
  have hk : (fun x : ℝ => kernelPsi (lorentzPair a₁ a₂) x) = fun x : ℝ => paperFT h x := rfl
  refine ⟨fun x => ?_, fun x => hasDerivAt_paperFT i2 i3 x, fun x => ?_⟩
  · rw [hk]; exact hasDerivAt_paperFT i0 i1 x
  · have e0 : kernelPsi (lorentzPair a₁ a₂) x = paperFT h x := rfl
    set s₁ : ℂ := ((1 / a₁ + 1 / a₂ : ℝ) : ℂ)
    set p₁ : ℂ := ((1 / (a₁ * a₂) : ℝ) : ℂ)
    have I0 : Integrable (fun u : ℝ => h u * cexp (I * x * u)) := integrable_mul_cexp_I_mul i0 x
    have I2 : Integrable (fun u : ℝ => s₁ * (I * u * h u * cexp (I * x * u))) :=
      (integrable_mul_cexp_I_mul i2 x).const_mul s₁
    have I4 : Integrable (fun u : ℝ => p₁ * (I * u * (I * u * h u) * cexp (I * x * u))) :=
      (integrable_mul_cexp_I_mul i4 x).const_mul p₁
    have I02 : Integrable (fun u : ℝ => h u * cexp (I * x * u) -
        s₁ * (I * u * h u * cexp (I * x * u))) := I0.sub I2
    have hsplit : paperFT h x - s₁ * paperFT (fun u : ℝ => I * u * h u) x +
        p₁ * paperFT (fun u : ℝ => I * u * (I * u * h u)) x =
        ∫ u : ℝ, (h u * cexp (I * x * u) - s₁ * (I * u * h u * cexp (I * x * u)) +
          p₁ * (I * u * (I * u * h u) * cexp (I * x * u))) := by
      rw [integral_add I02 I4, integral_sub I0 I2, integral_const_mul, integral_const_mul]
      rfl
    rw [e0, hsplit]
    show _ = ∫ u : ℝ, riemannPhiKernel u * cexp (I * x * u)
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have hm := lorentzPair_mul a₁ a₂ u
    have hc₁ : (a₁ : ℂ) ≠ 0 := by exact_mod_cast ha₁
    have hc₂ : (a₂ : ℂ) ≠ 0 := by exact_mod_cast ha₂
    have key : h u - s₁ * (I * u * h u) + p₁ * (I * u * (I * u * h u)) =
        riemannPhiKernel u * (lorentzPair a₁ a₂ u *
          ((1 - I * (u : ℂ) / a₁) * (1 - I * (u : ℂ) / a₂))) := by
      simp only [hh, s₁, p₁]
      push_cast
      field_simp
      ring
    rw [hm, mul_one] at key
    simp only
    linear_combination cexp (I * x * u) * key

/-- `|ψ_m(x)| ≤ ∫|Φm|`. -/
theorem norm_kernelPsi_le (a₁ a₂ x : ℝ) :
    ‖kernelPsi (lorentzPair a₁ a₂) x‖ ≤ ∫ u : ℝ, ‖riemannPhiKernel u * lorentzPair a₁ a₂ u‖ := by
  unfold kernelPsi
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (Eventually.of_forall fun u => ?_)))
  simp only
  rw [norm_mul, show I * (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-! ## Identification -/

/-- **The Ξ-equation with zeros at both ends.**  Let `a₁, a₂ ≠ 0` and let a real `ψ` satisfy
`ψ − (1/a₁ + 1/a₂)ψ′ + ψ″/(a₁a₂) = Ξ`, with `Ξ(x) = ∫ Φ(u) e^{ixu} du`.  If `ψ` has zeros arbitrarily
far towards `+∞` and towards `−∞`, then `ψ(x) = ∫ Φ(u) m(u) e^{ixu} du` with
`m(u) = 1/((1 − iu/a₁)(1 − iu/a₂))`. -/
theorem ofReal_eq_kernelPsi_of_ode {a₁ a₂ : ℝ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) {ψ ψ' ψ'' : ℝ → ℝ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (hψ' : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (hode : ∀ x, ((ψ x - (1 / a₁ + 1 / a₂) * ψ' x + ψ'' x / (a₁ * a₂) : ℝ) : ℂ) =
      paperFT riemannPhiKernel x)
    (hzp : ∀ T, ∃ x > T, ψ x = 0) (hzn : ∀ T, ∃ x < -T, ψ x = 0) :
    ∀ x, (ψ x : ℂ) = kernelPsi (lorentzPair a₁ a₂) x := by
  obtain ⟨hk1, hk2, hkode⟩ := kernelPsi_ode a₁ a₂ ha₁ ha₂
  set K := ∫ u : ℝ, ‖riemannPhiKernel u * lorentzPair a₁ a₂ u‖
  set d : ℝ → ℂ := fun x => (ψ x : ℂ) - kernelPsi (lorentzPair a₁ a₂) x with hd
  have hdd : ∀ x, HasDerivAt d ((ψ' x : ℂ) -
      paperFT (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u)) x) x :=
    fun x => (hψ x).ofReal_comp.sub (hk1 x)
  have hdd' : ∀ x, HasDerivAt (fun x => (ψ' x : ℂ) -
      paperFT (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u)) x)
      ((ψ'' x : ℂ) - paperFT (fun u : ℝ =>
        I * u * (I * u * (riemannPhiKernel u * lorentzPair a₁ a₂ u))) x) x :=
    fun x => (hψ' x).ofReal_comp.sub (hk2 x)
  have hzero := eq_zero_of_homogeneous (K := K) ha₁ ha₂ hdd hdd' (fun x => ?_)
    (fun T => ?_) (fun T => ?_)
  · intro x
    have := hzero x
    simp only [hd] at this
    exact sub_eq_zero.mp this
  · have h1 := hode x
    have h2 := hkode x
    push_cast at h1 h2 ⊢
    simp only [hd]
    linear_combination h1 - h2
  · obtain ⟨x, hx, hψx⟩ := hzp T
    refine ⟨x, hx, ?_⟩
    simp only [hd, hψx, Complex.ofReal_zero, zero_sub, norm_neg]
    exact norm_kernelPsi_le a₁ a₂ x
  · obtain ⟨x, hx, hψx⟩ := hzn T
    refine ⟨x, hx, ?_⟩
    simp only [hd, hψx, Complex.ofReal_zero, zero_sub, norm_neg]
    exact norm_kernelPsi_le a₁ a₂ x

end

end RHTower.KernelStrip
