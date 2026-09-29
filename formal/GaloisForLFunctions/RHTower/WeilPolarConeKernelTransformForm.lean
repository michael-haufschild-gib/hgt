import GaloisForLFunctions.RHTower.WeilPolarConeFirstVariation

/-!
# Two-sided polar positivity confines the Riemann-kernel transform to a plane

Let `w` be real weights with `Σ |w(n)| n^{−σ} < ∞` for every `σ > 1`, and suppose that `Λ + w` and
`Λ − w` are both Weil-positive on polar tests. Write `G = G_w` (`weightKernelTransform`),
`e₊(y) = e^{y/2}`, `e₋(y) = e^{−y/2}`, and `S` for the weighted cusp series of `a = 1 ⋆ w'`
(`w' = w · 1_{n ≥ 2}`) against `e^{y/2} e^{−πk²e^{2y}}`.

**Theorem** (`exists_weightKernelTransform_form`). There are reals `ν, A, C₊, C₋` with
* `G(y) = ν y (e₊ − e₋) + A (e₊ + e₋)`;
* `S(y) + S(−y) = (ν/2) y² (e₊ + e₋) + (A − ν) y (e₊ − e₋) + C₊ e₊ + C₋ e₋`.

The first variation `∫ H · L_c G = 0` holds for all polar `H`
(`integral_mul_polarShift_weightKernelTransform_eq_zero`). The polar tests are the common kernel of
the two moments against `e₊` and `e₋`. So `L_c G ∈ span{e₊, e₋}`
(`exists_eq_exp_of_forall_polar_integral_eq_zero`), and evenness gives `L_c G = λ_c (e₊ + e₋)`.

Multiplying by `2 cosh(c/2)/c²` and letting `c → 0` (`tendsto_secondDifference`) gives
`G'' − G/4 = ν (e₊ + e₋)`. Since `G = F'' − F/4` with `F(y) = S(y) + S(−y)`, two second-order linear
equations then give both stated forms.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## Polar moments of real tests -/

theorem paperFT_ofReal_I_half (H : ℝ → ℝ) :
    paperFT (fun u => (H u : ℂ)) (I / 2) = ((∫ u, H u * Real.exp (-(u / 2)) : ℝ) : ℂ) := by
  unfold paperFT
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : I * (I / 2) * (u : ℂ) = ((-(u / 2) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  simp only [e, ← Complex.ofReal_exp]; push_cast; ring

theorem paperFT_ofReal_neg_I_half (H : ℝ → ℝ) :
    paperFT (fun u => (H u : ℂ)) (-(I / 2)) = ((∫ u, H u * Real.exp (u / 2) : ℝ) : ℂ) := by
  unfold paperFT
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : I * (-(I / 2)) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  simp only [e, ← Complex.ofReal_exp]; push_cast; ring

/-! ## The annihilator of the polar tests -/

theorem integrable_mul_of_hasCompactSupport {H g : ℝ → ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) (hg : Continuous g) : Integrable fun u => H u * g u :=
  (hH.mul hg).integrable_of_hasCompactSupport hHc.mul_right

/-- `∫ (H − c₁φ₁ − c₂φ₂) g = ∫ H g − c₁ ∫ φ₁ g − c₂ ∫ φ₂ g`. -/
theorem integral_sub_two_smul_mul {H φ₁ φ₂ g : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    (h₁ : Continuous φ₁) (h₁c : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (h₂c : HasCompactSupport φ₂) (hg : Continuous g) (c₁ c₂ : ℝ) :
    ∫ u, (H u - c₁ * φ₁ u - c₂ * φ₂ u) * g u =
      (∫ u, H u * g u) - c₁ * (∫ u, φ₁ u * g u) - c₂ * ∫ u, φ₂ u * g u := by
  have i0 := integrable_mul_of_hasCompactSupport hH hHc hg
  have i1 := (integrable_mul_of_hasCompactSupport h₁ h₁c hg).const_mul c₁
  have i2 := (integrable_mul_of_hasCompactSupport h₂ h₂c hg).const_mul c₂
  have i01 : Integrable fun u => H u * g u - c₁ * (φ₁ u * g u) := i0.sub i1
  have e : (fun u => (H u - c₁ * φ₁ u - c₂ * φ₂ u) * g u) =
      fun u => H u * g u - c₁ * (φ₁ u * g u) - c₂ * (φ₂ u * g u) := by
    funext u; ring
  rw [e, integral_sub i01 i2, integral_sub i0 i1, integral_const_mul, integral_const_mul]

/-- **Annihilator of the polar tests.** A continuous `f` orthogonal to every real `C²` compactly
supported test with vanishing moments against `e^{±u/2}` is a combination of `e^{u/2}` and
`e^{−u/2}`. -/
theorem exists_eq_exp_of_forall_polar_integral_eq_zero {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ H : ℝ → ℝ, ContDiff ℝ 2 H → HasCompactSupport H →
      ∫ u, H u * Real.exp (-(u / 2)) = 0 → ∫ u, H u * Real.exp (u / 2) = 0 →
      ∫ u, H u * f u = 0) :
    ∃ α β : ℝ, ∀ y, f y = α * Real.exp (y / 2) + β * Real.exp (-(y / 2)) := by
  set b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  set φ₁ : ℝ → ℝ := fun u => b u with hφ₁
  set φ₂ : ℝ → ℝ := fun u => b (u - 1) with hφ₂
  have h₁d : ContDiff ℝ 2 φ₁ := b.contDiff
  have h₂d : ContDiff ℝ 2 φ₂ := b.contDiff.comp (contDiff_id.sub contDiff_const)
  have h₁c : HasCompactSupport φ₁ := b.hasCompactSupport
  have h₂c : HasCompactSupport φ₂ := b.hasCompactSupport.comp_homeomorph (Homeomorph.subRight 1)
  have hem : Continuous fun u : ℝ => Real.exp (-(u / 2)) := by fun_prop
  have hep : Continuous fun u : ℝ => Real.exp (u / 2) := by fun_prop
  -- the two moments of the bump are positive
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  have hpos : ∀ g : ℝ → ℝ, Continuous g → (∀ u, 0 < g u) → 0 < ∫ u, φ₁ u * g u := by
    intro g hg hg0
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (h₁d.continuous.mul hg) h₁c.mul_right (fun u => mul_nonneg b.nonneg (hg0 u).le) ?_
    simp only [φ₁, hb0, one_mul]; exact (hg0 0).ne'
  set p := ∫ u, φ₁ u * Real.exp (-(u / 2)) with hp
  set q := ∫ u, φ₁ u * Real.exp (u / 2) with hq
  have hp0 : 0 < p := hpos _ hem fun u => Real.exp_pos _
  have hq0 : 0 < q := hpos _ hep fun u => Real.exp_pos _
  have hp2 : ∫ u, φ₂ u * Real.exp (-(u / 2)) = Real.exp (-(1 / 2)) * p := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun v => φ₁ v * Real.exp (-((v + 1) / 2))) 1
    simp only [sub_add_cancel] at h
    rw [h, hp, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [show -((v + 1) / 2) = -(1 / 2) + -(v / 2) by ring, Real.exp_add]; ring
  have hq2 : ∫ u, φ₂ u * Real.exp (u / 2) = Real.exp (1 / 2) * q := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun v => φ₁ v * Real.exp ((v + 1) / 2)) 1
    simp only [sub_add_cancel] at h
    rw [h, hq, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [show (v + 1) / 2 = 1 / 2 + v / 2 by ring, Real.exp_add]; ring
  set d := Real.exp (1 / 2) - Real.exp (-(1 / 2)) with hd
  have hd0 : 0 < d := by
    rw [hd, sub_pos]; exact Real.exp_lt_exp.mpr (by norm_num)
  set X₁ := ∫ u, φ₁ u * f u
  set X₂ := ∫ u, φ₂ u * f u
  set Z := X₂ - Real.exp (-(1 / 2)) * X₁
  refine ⟨Z / (q * d), X₁ / p - Z / (p * d), fun y => ?_⟩
  -- every test pairs with `f` through its two moments
  have hmain : ∀ H : ℝ → ℝ, ContDiff ℝ 2 H → HasCompactSupport H →
      ∫ u, H u * f u = (X₁ / p - Z / (p * d)) * (∫ u, H u * Real.exp (-(u / 2))) +
        Z / (q * d) * ∫ u, H u * Real.exp (u / 2) := by
    intro H hH hHc
    set x := ∫ u, H u * Real.exp (-(u / 2))
    set z := ∫ u, H u * Real.exp (u / 2)
    set c₂ := (z / q - x / p) / d
    set c₁ := x / p - c₂ * Real.exp (-(1 / 2))
    have hHt : ContDiff ℝ 2 fun u => H u - c₁ * φ₁ u - c₂ * φ₂ u :=
      (hH.sub (contDiff_const.mul h₁d)).sub (contDiff_const.mul h₂d)
    have hHtc : HasCompactSupport fun u => H u - c₁ * φ₁ u - c₂ * φ₂ u :=
      (hHc.sub (h₁c.mul_left)).sub h₂c.mul_left
    have hm := integral_sub_two_smul_mul hH.continuous hHc h₁d.continuous h₁c h₂d.continuous h₂c
      hem c₁ c₂
    have hpl := integral_sub_two_smul_mul hH.continuous hHc h₁d.continuous h₁c h₂d.continuous h₂c
      hep c₁ c₂
    have hf' := integral_sub_two_smul_mul hH.continuous hHc h₁d.continuous h₁c h₂d.continuous h₂c
      hf c₁ c₂
    rw [hp2] at hm
    rw [hq2] at hpl
    have hE : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; simp
    have hm0 : x - c₁ * p - c₂ * (Real.exp (-(1 / 2)) * p) = 0 := by
      simp only [c₁]; field_simp; ring
    have hpl0 : z - c₁ * q - c₂ * (Real.exp (1 / 2) * q) = 0 := by
      simp only [c₁, c₂]; field_simp; ring
    have hzero := h _ hHt hHtc (by rw [hm]; exact hm0) (by rw [hpl]; exact hpl0)
    rw [hf'] at hzero
    have : ∫ u, H u * f u = c₁ * X₁ + c₂ * X₂ := by linarith
    rw [this]
    have hp' : p ≠ 0 := hp0.ne'
    have hq' : q ≠ 0 := hq0.ne'
    have hd' : d ≠ 0 := hd0.ne'
    simp only [c₁, c₂, Z]
    field_simp
    ring
  have hcont : Continuous fun u => f u - (Z / (q * d) * Real.exp (u / 2) +
      (X₁ / p - Z / (p * d)) * Real.exp (-(u / 2))) := by fun_prop
  have hae : ∀ᵐ u ∂(volume : Measure ℝ), f u - (Z / (q * d) * Real.exp (u / 2) +
      (X₁ / p - Z / (p * d)) * Real.exp (-(u / 2))) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable fun g hg hgc => ?_
    have hg2 : ContDiff ℝ 2 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
    have hsplit : ∫ u, g u • (f u - (Z / (q * d) * Real.exp (u / 2) +
        (X₁ / p - Z / (p * d)) * Real.exp (-(u / 2)))) =
        (∫ u, g u * f u) - (X₁ / p - Z / (p * d)) * (∫ u, g u * Real.exp (-(u / 2))) -
          Z / (q * d) * ∫ u, g u * Real.exp (u / 2) := by
      have i0 := integrable_mul_of_hasCompactSupport hg.continuous hgc hf
      have i1 := (integrable_mul_of_hasCompactSupport hg.continuous hgc hem).const_mul
        (X₁ / p - Z / (p * d))
      have i2 := (integrable_mul_of_hasCompactSupport hg.continuous hgc hep).const_mul (Z / (q * d))
      have i01 : Integrable fun u => g u * f u -
          (X₁ / p - Z / (p * d)) * (g u * Real.exp (-(u / 2))) := i0.sub i1
      rw [← integral_const_mul, ← integral_const_mul, ← integral_sub i0 i1, ← integral_sub i01 i2]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [smul_eq_mul]; ring
    rw [hsplit, hmain g hg2 hgc]; ring
  have := (hcont.ae_eq_iff_eq volume continuous_const).mp hae
  have hy := congrFun this y
  linarith

/-! ## The symmetric second difference -/

/-- **Second-difference limit.** If `f'' ` exists everywhere and is continuous at `y`, then
`(f(y + c) + f(y − c) − 2 f(y))/c² → f''(y)` as `c → 0⁺`. -/
theorem tendsto_secondDifference {f f₁ f₂ : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f₁ x) x)
    (h2 : ∀ x, HasDerivAt f₁ (f₂ x) x) {y : ℝ} (hc : ContinuousAt f₂ y) :
    Tendsto (fun c => (f (y + c) + f (y - c) - 2 * f y) / c ^ 2) (𝓝[>] 0) (𝓝 (f₂ y)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hc (ε / 4) (by positivity)
  refine ⟨δ, hδ, fun c hc0 hcδ => ?_⟩
  have hcpos : 0 < c := hc0
  have hcδ' : c < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hcpos] at hcδ; exact hcδ
  set g₂ : ℝ → ℝ := fun t => f₂ (y + t) + f₂ (y - t) - 2 * f₂ y with hg₂
  set g₁ : ℝ → ℝ := fun t => f₁ (y + t) - f₁ (y - t) - 2 * f₂ y * t with hg₁
  set g : ℝ → ℝ := fun t => f (y + t) + f (y - t) - 2 * f y - f₂ y * t ^ 2 with hg
  have hd1 : ∀ t, HasDerivAt g₁ (g₂ t) t := by
    intro t
    have ha := (h2 (y + t)).comp t ((hasDerivAt_id t).const_add y)
    have hb := (h2 (y - t)).comp t ((hasDerivAt_id t).const_sub y)
    have hc' := (hasDerivAt_id t).const_mul (2 * f₂ y)
    have := (ha.sub hb).sub hc'
    refine this.congr_deriv ?_
    simp only [hg₂]; ring
  have hd0 : ∀ t, HasDerivAt g (g₁ t) t := by
    intro t
    have ha := (h1 (y + t)).comp t ((hasDerivAt_id t).const_add y)
    have hb := (h1 (y - t)).comp t ((hasDerivAt_id t).const_sub y)
    have hc' := (hasDerivAt_pow 2 t).const_mul (f₂ y)
    have := ((ha.add hb).sub_const (2 * f y)).sub hc'
    refine this.congr_deriv ?_
    simp only [hg₁]; push_cast; ring
  have hb2 : ∀ t ∈ Ico 0 c, ‖g₂ t‖ ≤ ε / 2 := by
    intro t ht
    have ht' : |t| < δ := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
    have e1 := hδf (x := y + t) (by rw [Real.dist_eq]; simpa using ht')
    have e2 := hδf (x := y - t) (by rw [Real.dist_eq]; simpa [abs_neg] using ht')
    rw [Real.dist_eq] at e1 e2
    rw [Real.norm_eq_abs]
    show |f₂ (y + t) + f₂ (y - t) - 2 * f₂ y| ≤ ε / 2
    have : f₂ (y + t) + f₂ (y - t) - 2 * f₂ y = (f₂ (y + t) - f₂ y) + (f₂ (y - t) - f₂ y) := by ring
    rw [this]
    calc |(f₂ (y + t) - f₂ y) + (f₂ (y - t) - f₂ y)| ≤ |f₂ (y + t) - f₂ y| + |f₂ (y - t) - f₂ y| :=
          abs_add_le _ _
      _ ≤ ε / 2 := by linarith
  have hg₁0 : g₁ 0 = 0 := by simp only [hg₁, add_zero, sub_zero, sub_self, mul_zero]
  have hb1 : ∀ t ∈ Ico 0 c, ‖g₁ t‖ ≤ ε / 2 * c := by
    intro t ht
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := g₁) (a := 0) (b := c)
      (fun x _ => (hd1 x).hasDerivWithinAt) hb2 t (Ico_subset_Icc_self ht)
    rw [hg₁0, sub_zero, sub_zero] at h
    calc ‖g₁ t‖ ≤ ε / 2 * t := h
      _ ≤ ε / 2 * c := by gcongr; exact ht.2.le
  have hg0 : g 0 = 0 := by
    simp only [hg, add_zero, sub_zero]; ring
  have h0 := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (a := 0) (b := c)
    (fun x _ => (hd0 x).hasDerivWithinAt) hb1 c ⟨hcpos.le, le_rfl⟩
  rw [hg0, sub_zero, sub_zero, Real.norm_eq_abs] at h0
  have hc2 : 0 < c ^ 2 := by positivity
  rw [Real.dist_eq]
  have e : (f (y + c) + f (y - c) - 2 * f y) / c ^ 2 - f₂ y = g c / c ^ 2 := by
    simp only [hg]; field_simp
  rw [e, abs_div, abs_of_pos hc2, div_lt_iff₀ hc2]
  calc |g c| ≤ ε / 2 * c * c := h0
    _ < ε * c ^ 2 := by nlinarith

/-! ## Second-order equations with exponential forcing -/

/-- Solutions of `f'' − f/4 = p'' − p/4` are `p + A e^{y/2} + B e^{−y/2}`. -/
theorem exists_eq_add_exp_of_second_deriv {f f₁ f₂ p p₁ p₂ : ℝ → ℝ}
    (hf1 : ∀ y, HasDerivAt f (f₁ y) y) (hf2 : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (hp1 : ∀ y, HasDerivAt p (p₁ y) y) (hp2 : ∀ y, HasDerivAt p₁ (p₂ y) y)
    (h : ∀ y, f₂ y - f y / 4 = p₂ y - p y / 4) :
    ∃ A B : ℝ, ∀ y, f y = p y + A * Real.exp (y / 2) + B * Real.exp (-(y / 2)) := by
  obtain ⟨A, B, hAB⟩ := exists_eq_exp_of_second_deriv (f := fun y => f y - p y)
    (f₁ := fun y => f₁ y - p₁ y) (f₂ := fun y => f₂ y - p₂ y)
    (fun y => (hf1 y).sub (hp1 y)) (fun y => (hf2 y).sub (hp2 y))
    (fun y => by have := h y; linarith)
  exact ⟨A, B, fun y => by have := hAB y; linarith⟩

theorem hasDerivAt_exp_div_two' (y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (y / 2) / 2) y :=
  (((hasDerivAt_id' y).div_const 2).exp).congr_deriv (by ring_nf)

theorem hasDerivAt_exp_neg_div_two' (y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y / 2))) (-(Real.exp (-(y / 2)) / 2)) y :=
  (((hasDerivAt_id' y).div_const 2).neg.exp).congr_deriv (by simp only [Pi.neg_apply]; ring_nf)

/-- `(y (e₊ − e₋))' = (e₊ − e₋) + y (e₊ + e₋)/2`. -/
theorem hasDerivAt_mul_expDiff (y : ℝ) :
    HasDerivAt (fun y : ℝ => y * (Real.exp (y / 2) - Real.exp (-(y / 2))))
      ((Real.exp (y / 2) - Real.exp (-(y / 2))) +
        y * (Real.exp (y / 2) + Real.exp (-(y / 2))) / 2) y :=
  ((hasDerivAt_id' y).mul ((hasDerivAt_exp_div_two' y).sub (hasDerivAt_exp_neg_div_two' y))).congr_deriv
    (by simp only [Pi.add_apply, Pi.sub_apply]; ring)

/-- `((e₊ − e₋) + y (e₊ + e₋)/2)' = (e₊ + e₋) + y (e₊ − e₋)/4`. -/
theorem hasDerivAt_mul_expDiff_deriv (y : ℝ) :
    HasDerivAt (fun y : ℝ => (Real.exp (y / 2) - Real.exp (-(y / 2))) +
        y * (Real.exp (y / 2) + Real.exp (-(y / 2))) / 2)
      ((Real.exp (y / 2) + Real.exp (-(y / 2))) +
        y * (Real.exp (y / 2) - Real.exp (-(y / 2))) / 4) y :=
  (((hasDerivAt_exp_div_two' y).sub (hasDerivAt_exp_neg_div_two' y)).add
    (((hasDerivAt_id' y).mul ((hasDerivAt_exp_div_two' y).add
      (hasDerivAt_exp_neg_div_two' y))).div_const 2)).congr_deriv
    (by simp only [Pi.add_apply, Pi.sub_apply]; ring)

/-- `(y² (e₊ + e₋))' = 2y (e₊ + e₋) + y² (e₊ − e₋)/2`. -/
theorem hasDerivAt_sq_mul_expSum (y : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 * (Real.exp (y / 2) + Real.exp (-(y / 2))))
      (2 * y * (Real.exp (y / 2) + Real.exp (-(y / 2))) +
        y ^ 2 * (Real.exp (y / 2) - Real.exp (-(y / 2))) / 2) y :=
  ((hasDerivAt_pow 2 y).mul ((hasDerivAt_exp_div_two' y).add
    (hasDerivAt_exp_neg_div_two' y))).congr_deriv
    (by simp only [Pi.add_apply, Pi.sub_apply]; push_cast; ring)

/-- `(2y (e₊ + e₋) + y² (e₊ − e₋)/2)' = 2 (e₊ + e₋) + 2y (e₊ − e₋) + y² (e₊ + e₋)/4`. -/
theorem hasDerivAt_sq_mul_expSum_deriv (y : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * y * (Real.exp (y / 2) + Real.exp (-(y / 2))) +
        y ^ 2 * (Real.exp (y / 2) - Real.exp (-(y / 2))) / 2)
      (2 * (Real.exp (y / 2) + Real.exp (-(y / 2))) +
        2 * y * (Real.exp (y / 2) - Real.exp (-(y / 2))) +
        y ^ 2 * (Real.exp (y / 2) + Real.exp (-(y / 2))) / 4) y :=
  ((((hasDerivAt_id' y).const_mul 2).mul ((hasDerivAt_exp_div_two' y).add
    (hasDerivAt_exp_neg_div_two' y))).add
    (((hasDerivAt_pow 2 y).mul ((hasDerivAt_exp_div_two' y).sub
      (hasDerivAt_exp_neg_div_two' y))).div_const 2)).congr_deriv
    (by simp only [Pi.add_apply, Pi.sub_apply]; push_cast; ring)

end

end RHTower
