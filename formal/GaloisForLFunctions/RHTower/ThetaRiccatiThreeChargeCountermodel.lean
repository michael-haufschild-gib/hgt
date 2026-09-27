import GaloisForLFunctions.RHTower.ThetaRiccatiGaussianCountermodel

/-!
# Three-charge Riccati countermodel

The Gaussian Riccati family `g_ε = exp(-ε(cosh(x/σ)-1)) · e^{-x²/(2σ²)}(1+2a cosh(x/σ))` can be
fitted to any prescribed ordinary mass `M > 0` and reflected half-density charges
`∫ e^{±x/2} g = Q > M`, while keeping positivity, evenness, analyticity, rapid derivative decay,
strict log-concavity, all four reflected action inequalities and a Fourier zero at arbitrarily
small positive height.  With `M = ∫ k` and `Q = 1/2` for the completed theta source `k`, this
matches all three literal theta budgets.

The ratio `Q/M` at `ε = 0` is `exp(σ²/8)(1+2a cosh(σ/4))/(1+2a)`, strictly increasing in `σ`; an
intermediate-value argument fits the ratio, a scalar fixes the mass, and Hurwitz transports the
`ε = 0` lattice zero at height `2 arcosh(1/(2a))/σ` to the perturbed family.
-/

open MeasureTheory Set Filter Topology Complex

namespace RHTower

/-! ## Mass and critical charge of the Riccati family -/

/-- Ordinary mass `∫ g_ε`. -/
noncomputable def riccatiMass (a σ ε : ℝ) : ℝ := ∫ x, riccatiSource a σ ε x

/-- Critical half-density charge `∫ e^{x/2} g_ε`. -/
noncomputable def riccatiCharge (a σ ε : ℝ) : ℝ := ∫ x, Real.exp (x / 2) * riccatiSource a σ ε x

theorem riccatiFourier_eq_mass (a σ ε : ℝ) : riccatiFourier a σ ε 0 = (riccatiMass a σ ε : ℂ) := by
  unfold riccatiFourier riccatiMass
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp

theorem riccatiFourier_eq_charge (a σ ε : ℝ) :
    riccatiFourier a σ ε (-(I / 2)) = (riccatiCharge a σ ε : ℂ) := by
  unfold riccatiFourier riccatiCharge
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  have : I * -(I / 2) * (x : ℂ) = ((x / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this, ← Complex.ofReal_exp]
  push_cast
  ring

theorem riccatiMass_pos {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    0 < riccatiMass a σ ε := by
  unfold riccatiMass
  have hi : Integrable (riccatiSource a σ ε) :=
    (integrable_riccatiSource_mul_exp_abs ha hσ hε 0).congr (ae_of_all _ fun x => by simp)
  refine integral_pos_iff_support_of_nonneg (fun x => (riccatiSource_nonneg ha x)) hi |>.mpr ?_
  have : Function.support (riccatiSource a σ ε) = univ :=
    Set.eq_univ_of_forall fun x => (riccatiSource_pos ha hσ.ne' ε x).ne'
  rw [this]
  simp

theorem riccatiMass_zero {σ : ℝ} (hσ : 0 < σ) (a : ℝ) :
    riccatiMass a σ 0 = σ * Real.sqrt (2 * Real.pi) * (1 + 2 * a) := by
  have h := riccatiFourier_zero hσ a 0
  rw [riccatiFourier_eq_mass] at h
  have : ((σ * Real.sqrt (2 * Real.pi) * (1 + 2 * a) : ℝ) : ℂ) =
      ((σ * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.exp (-(σ ^ 2 * 0 ^ 2 / 2)) *
        (1 + 2 * a * Complex.cos (σ * 0 / 2)) := by
    simp
  exact_mod_cast h.trans this.symm

theorem riccatiCharge_zero {σ : ℝ} (hσ : 0 < σ) (a : ℝ) :
    riccatiCharge a σ 0 =
      σ * Real.sqrt (2 * Real.pi) * Real.exp (σ ^ 2 / 8) * (1 + 2 * a * Real.cosh (σ / 4)) := by
  have h := riccatiFourier_zero hσ a (-(I / 2))
  rw [riccatiFourier_eq_charge] at h
  have e1 : -((σ : ℂ) ^ 2 * (-(I / 2)) ^ 2 / 2) = ((σ ^ 2 / 8 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have e2 : (σ : ℂ) * -(I / 2) / 2 = -(((σ / 4 : ℝ) : ℂ) * I) := by push_cast; ring
  rw [e1, e2, Complex.cos_neg, Complex.cos_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_exp] at h
  exact_mod_cast h

/-- The undamped charge/mass ratio `R₀(a,σ) = e^{σ²/8}(1 + 2a cosh(σ/4))/(1 + 2a)`. -/
noncomputable def riccatiRatioZero (a σ : ℝ) : ℝ :=
  Real.exp (σ ^ 2 / 8) * (1 + 2 * a * Real.cosh (σ / 4)) / (1 + 2 * a)

theorem riccatiCharge_div_mass_zero {σ : ℝ} (hσ : 0 < σ) {a : ℝ} (ha : 0 ≤ a) :
    riccatiCharge a σ 0 / riccatiMass a σ 0 = riccatiRatioZero a σ := by
  rw [riccatiCharge_zero hσ, riccatiMass_zero hσ]
  unfold riccatiRatioZero
  have : 0 < σ * Real.sqrt (2 * Real.pi) := by positivity
  field_simp

theorem riccatiRatioZero_ge {a σ : ℝ} (ha : 0 ≤ a) : Real.exp (σ ^ 2 / 8) ≤ riccatiRatioZero a σ := by
  unfold riccatiRatioZero
  rw [le_div_iff₀ (by positivity)]
  have hc := Real.one_le_cosh (σ / 4)
  have h1 : 1 + 2 * a ≤ 1 + 2 * a * Real.cosh (σ / 4) := by nlinarith
  exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

theorem riccatiRatioZero_le {a σ : ℝ} (ha : 0 ≤ a) :
    riccatiRatioZero a σ ≤ Real.exp (σ ^ 2 / 8 + |σ| / 4) := by
  unfold riccatiRatioZero
  rw [div_le_iff₀ (by positivity), Real.exp_add]
  have hc : Real.cosh (σ / 4) ≤ Real.exp (|σ| / 4) := by
    rw [Real.cosh_eq]
    rcases abs_cases σ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      have : Real.exp (-(σ / 4)) ≤ Real.exp (σ / 4) := Real.exp_le_exp.mpr (by linarith)
      linarith
    · rw [h, neg_div]
      have : Real.exp (σ / 4) ≤ Real.exp (-(σ / 4)) := Real.exp_le_exp.mpr (by linarith)
      linarith
  have h1 : 1 ≤ Real.exp (|σ| / 4) := Real.one_le_exp (by positivity)
  have h2 : 1 + 2 * a * Real.cosh (σ / 4) ≤ Real.exp (|σ| / 4) * (1 + 2 * a) := by nlinarith
  calc Real.exp (σ ^ 2 / 8) * (1 + 2 * a * Real.cosh (σ / 4))
      ≤ Real.exp (σ ^ 2 / 8) * (Real.exp (|σ| / 4) * (1 + 2 * a)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by ring

theorem riccatiRatioZero_strictMonoOn {a : ℝ} (ha : 0 ≤ a) :
    StrictMonoOn (riccatiRatioZero a) (Ioi 0) := by
  intro σ hσ τ hτ hστ
  have hσ0 : 0 < σ := hσ
  unfold riccatiRatioZero
  refine div_lt_div_of_pos_right ?_ (by positivity)
  have h1 : Real.exp (σ ^ 2 / 8) < Real.exp (τ ^ 2 / 8) := Real.exp_lt_exp.mpr (by nlinarith)
  have h2 : Real.cosh (σ / 4) ≤ Real.cosh (τ / 4) := Real.cosh_le_cosh.mpr (by
    rw [abs_of_pos (by linarith), abs_of_pos (by have : (0 : ℝ) < τ := hτ; linarith)]
    linarith)
  have h3 : 0 < 1 + 2 * a * Real.cosh (σ / 4) := by have := Real.cosh_pos (σ / 4); positivity
  exact mul_lt_mul h1 (by nlinarith) h3 (Real.exp_pos _).le

theorem continuous_riccatiRatioZero (a : ℝ) : Continuous (riccatiRatioZero a) := by
  unfold riccatiRatioZero
  exact (by fun_prop : Continuous fun σ : ℝ => Real.exp (σ ^ 2 / 8) *
    (1 + 2 * a * Real.cosh (σ / 4))).div_const _

/-! ## Continuity of mass and charge in the width -/

theorem continuousOn_riccatiIntegral {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) {σ₁ σ₂ : ℝ}
    (hσ₁ : 0 < σ₁) (c : ℝ) :
    ContinuousOn (fun σ => ∫ x, Real.exp (c * x) * riccatiSource a σ ε x) (Icc σ₁ σ₂) := by
  have hσ₂ : ∀ σ ∈ Icc σ₁ σ₂, 0 < σ := fun σ hσ => lt_of_lt_of_le hσ₁ hσ.1
  refine continuousOn_of_dominated
    (bound := fun x => (1 + 2 * a) * (Real.exp (1 / 8) *
      Real.exp (-(x - 0) ^ 2 / (2 * (2 * max σ₂ σ₁) ^ 2))) * Real.exp (|c| * |x|))
    (fun σ hσ => by
      have : Continuous fun x => Real.exp (c * x) * riccatiSource a σ ε x := by
        unfold riccatiSource riccatiBase riccatiGauss; fun_prop
      exact this.aestronglyMeasurable)
    (fun σ hσ => ae_of_all _ fun x => ?_)
    (integrable_envelope_mul_exp_abs (lt_of_lt_of_le hσ₁ (le_max_right _ _)) _ _)
    (ae_of_all _ fun x => ?_)
  · have hs := riccatiSource_le_envelope (S := max σ₂ σ₁) ha (hσ₂ σ hσ)
      (le_trans hσ.2 (le_max_left _ _)) hε x
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (riccatiSource_nonneg ha x)),
      mul_comm]
    refine mul_le_mul hs (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
    calc c * x ≤ |c * x| := le_abs_self _
      _ = |c| * |x| := abs_mul _ _
  · have hmaps : MapsTo (fun σ : ℝ => (σ, ε)) (Icc σ₁ σ₂) {p : ℝ × ℝ | p.1 ≠ 0} :=
      fun σ hσ => (hσ₂ σ hσ).ne'
    exact continuousOn_const.mul ((continuous_riccatiSource_params a x).comp
      (continuous_id.prodMk continuous_const).continuousOn hmaps)

theorem continuousOn_riccatiMass {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) :
    ContinuousOn (fun σ => riccatiMass a σ ε) (Icc σ₁ σ₂) :=
  (continuousOn_riccatiIntegral (σ₂ := σ₂) ha hε hσ₁ 0).congr fun σ _ => by
    unfold riccatiMass; simp

theorem continuousOn_riccatiCharge {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) {σ₁ σ₂ : ℝ}
    (hσ₁ : 0 < σ₁) : ContinuousOn (fun σ => riccatiCharge a σ ε) (Icc σ₁ σ₂) :=
  (continuousOn_riccatiIntegral (σ₂ := σ₂) ha hε hσ₁ (1 / 2)).congr fun σ _ => by
    unfold riccatiCharge
    exact integral_congr_ae (ae_of_all _ fun x => by simp only; ring_nf)

/-! ## Charge fitting -/

theorem riccatiDepth_of_cosh {t₀ : ℝ} (ht : 0 < t₀) :
    riccatiDepth (1 / (2 * Real.cosh t₀)) = t₀ := by
  unfold riccatiDepth
  have hc := Real.cosh_pos t₀
  rw [show 1 / (2 * (1 / (2 * Real.cosh t₀))) = Real.cosh t₀ by field_simp,
    Real.arcosh_cosh ht.le]

theorem tendsto_riccatiIntegrals {a : ℝ} (ha : 0 ≤ a) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun j : ℕ => riccatiMass a σ (1 / ((j : ℝ) + 1))) atTop (𝓝 (riccatiMass a σ 0)) ∧
    Tendsto (fun j : ℕ => riccatiCharge a σ (1 / ((j : ℝ) + 1))) atTop
      (𝓝 (riccatiCharge a σ 0)) := by
  have hconv := tendstoLocallyUniformly_riccatiFourier ha hσ (σk := fun _ => σ)
    (εk := fun j => 1 / ((j : ℝ) + 1)) (fun _ => hσ) (fun j => by positivity)
    tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
  have hpt : ∀ z, Tendsto (fun j : ℕ => riccatiFourier a σ (1 / ((j : ℝ) + 1)) z) atTop
      (𝓝 (riccatiFourier a σ 0 z)) := fun z =>
    hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  constructor
  · have h := (Complex.continuous_re.tendsto _).comp (hpt 0)
    simpa [Function.comp_def, riccatiFourier_eq_mass] using h
  · have h := (Complex.continuous_re.tendsto _).comp (hpt (-(I / 2)))
    simpa [Function.comp_def, riccatiFourier_eq_charge] using h

theorem riccatiCharge_eq_integral_neg {a σ ε : ℝ} :
    (∫ x, Real.exp (-(x / 2)) * riccatiSource a σ ε x) = riccatiCharge a σ ε := by
  unfold riccatiCharge
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [riccatiSource_neg, neg_div, neg_neg]

/-- **Exact scalar theta charges do not repair global Riccati zero control.**  For every
`0 < M < Q` and `η > 0` there is a positive, even, real-analytic density `g = C g_ε` with ordinary
mass `M`, both half-density charges `Q`, superexponentially decaying derivatives, strictly
concave logarithm, the strict global reflected Riccati law, an entire Fourier transform of order
at most one, and a Fourier zero with `0 < Im z < η`. -/
theorem riccati_three_charge_countermodel {M Q : ℝ} (hM : 0 < M) (hMQ : M < Q) {η : ℝ}
    (hη : 0 < η) :
    ∃ a σ ε C : ℝ, 0 < a ∧ a < 1 / 2 ∧ 0 < σ ∧ 0 < ε ∧ 0 < C ∧
      (∫ x, C * riccatiSource a σ ε x) = M ∧
      (∫ x, Real.exp (x / 2) * (C * riccatiSource a σ ε x)) = Q ∧
      (∫ x, Real.exp (-(x / 2)) * (C * riccatiSource a σ ε x)) = Q ∧
      (∀ x, 0 < C * riccatiSource a σ ε x) ∧
      (∀ x, C * riccatiSource a σ ε (-x) = C * riccatiSource a σ ε x) ∧
      (∀ x, AnalyticAt ℝ (fun y => C * riccatiSource a σ ε y) x) ∧
      (∀ (k : ℕ) (A : ℝ), ∃ D, ∀ x : ℝ,
        |iteratedDeriv k (fun y => C * riccatiSource a σ ε y) x| ≤ D * Real.exp (-(A * |x|))) ∧
      StrictConcaveOn ℝ univ (fun x => Real.log (C * riccatiSource a σ ε x)) ∧
      (∀ u t, riccatiAction a σ ε u t = 2 * Real.log (C * riccatiSource a σ ε u) -
        Real.log (C * riccatiSource a σ ε (u + t)) - Real.log (C * riccatiSource a σ ε (u - t))) ∧
      (∀ u t, 0 < t → 0 < riccatiAction a σ ε u t ∧ 0 < riccatiJetOne a σ ε u t ∧
        0 < riccatiJetTwo a σ ε u t ∧ 0 < riccatiMargin a σ ε u t) ∧
      (∀ z, (∫ x : ℝ, ((C * riccatiSource a σ ε x : ℝ) : ℂ) * Complex.exp (I * z * x)) =
        C * riccatiFourier a σ ε z) ∧
      Differentiable ℂ (riccatiFourier a σ ε) ∧
      (∀ δ : ℝ, 0 < δ → ∃ R₀, ∀ z : ℂ, R₀ ≤ ‖z‖ →
        ‖riccatiFourier a σ ε z‖ ≤ Real.exp (‖z‖ ^ (1 + δ))) ∧
      ∃ z : ℂ, riccatiFourier a σ ε z = 0 ∧ 0 < z.im ∧ z.im < η := by
  set R := Q / M
  have hR : 1 < R := (one_lt_div hM).mpr hMQ
  have hlogR : 0 < Real.log R := Real.log_pos hR
  set m := min 1 (8 * Real.log R / 3)
  have hm : 0 < m := lt_min one_pos (by positivity)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmR : m ≤ 8 * Real.log R / 3 := min_le_right _ _
  set t₀ := η * m / 8
  have ht₀ : 0 < t₀ := by positivity
  set a := 1 / (2 * Real.cosh t₀)
  have hcosh : 1 < Real.cosh t₀ := Real.one_lt_cosh.mpr ht₀.ne'
  have ha : 0 < a := by positivity
  have ha2 : a < 1 / 2 := by
    simp only [a]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hA : riccatiDepth a = t₀ := riccatiDepth_of_cosh ht₀
  -- the undamped root `σ*`
  have hlow : ∀ σ, 0 < σ → σ < m → riccatiRatioZero a σ < R := by
    intro σ hσ hσm
    refine lt_of_le_of_lt (riccatiRatioZero_le ha.le) ?_
    rw [abs_of_pos hσ, ← Real.exp_log (by linarith : (0 : ℝ) < R)]
    refine Real.exp_lt_exp.mpr ?_
    have : σ ^ 2 / 8 ≤ σ / 8 := by nlinarith
    linarith
  set σlo := m / 2
  set σhi := Real.sqrt (8 * Real.log R) + 1
  have hσlo : 0 < σlo := by positivity
  have hlohi : σlo ≤ σhi := by
    have : σlo ≤ 1 / 2 := by simp only [σlo]; linarith
    have := Real.sqrt_nonneg (8 * Real.log R)
    linarith
  have hRlo : riccatiRatioZero a σlo ≤ R := (hlow σlo hσlo (by simp only [σlo]; linarith)).le
  have hRhi : R ≤ riccatiRatioZero a σhi := by
    refine le_trans ?_ (riccatiRatioZero_ge ha.le)
    rw [← Real.exp_log (by linarith : (0 : ℝ) < R)]
    refine Real.exp_le_exp.mpr ?_
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 8 * Real.log R)
    have hs0 := Real.sqrt_nonneg (8 * Real.log R)
    simp only [σhi]
    nlinarith
  obtain ⟨σs, hσs, hσsR⟩ := intermediate_value_Icc hlohi
    (continuous_riccatiRatioZero a).continuousOn ⟨hRlo, hRhi⟩
  have hσs0 : 0 < σs := lt_of_lt_of_le hσlo hσs.1
  have hσsm : m ≤ σs := by
    by_contra h
    push Not at h
    have := hlow σs hσs0 h
    linarith
  -- perturbation widths and damping
  set δ : ℕ → ℝ := fun k => min (σs / 2) 1 / ((k : ℝ) + 1)
  have hδ : ∀ k, 0 < δ k := fun k => by simp only [δ]; positivity
  have hδle : ∀ k, δ k ≤ σs / 2 := fun k => by
    simp only [δ]
    have h1 : min (σs / 2) 1 ≤ σs / 2 := min_le_left _ _
    have h2 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    calc min (σs / 2) 1 / ((k : ℝ) + 1) ≤ min (σs / 2) 1 / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos h2
      _ ≤ σs / 2 := by rw [div_one]; exact h1
  have hsign : ∀ k, ∃ j : ℕ, k ≤ j ∧
      riccatiCharge a (σs - δ k) (1 / ((j : ℝ) + 1)) -
        R * riccatiMass a (σs - δ k) (1 / ((j : ℝ) + 1)) < 0 ∧
      0 < riccatiCharge a (σs + δ k) (1 / ((j : ℝ) + 1)) -
        R * riccatiMass a (σs + δ k) (1 / ((j : ℝ) + 1)) := by
    intro k
    have hpos1 : 0 < σs - δ k := by linarith [hδle k]
    have hpos2 : 0 < σs + δ k := by linarith [hδ k]
    have hlt1 : riccatiRatioZero a (σs - δ k) < R := by
      rw [← hσsR]
      exact riccatiRatioZero_strictMonoOn ha.le hpos1 hσs0 (by linarith [hδ k])
    have hlt2 : R < riccatiRatioZero a (σs + δ k) := by
      rw [← hσsR]
      exact riccatiRatioZero_strictMonoOn ha.le hσs0 hpos2 (by linarith [hδ k])
    have hm1 := riccatiMass_pos ha.le hpos1 (le_refl 0)
    have hm2 := riccatiMass_pos ha.le hpos2 (le_refl 0)
    have hlim1 : riccatiCharge a (σs - δ k) 0 - R * riccatiMass a (σs - δ k) 0 < 0 := by
      have := riccatiCharge_div_mass_zero hpos1 ha.le
      rw [div_eq_iff hm1.ne'] at this
      rw [this]
      nlinarith
    have hlim2 : 0 < riccatiCharge a (σs + δ k) 0 - R * riccatiMass a (σs + δ k) 0 := by
      have := riccatiCharge_div_mass_zero hpos2 ha.le
      rw [div_eq_iff hm2.ne'] at this
      rw [this]
      nlinarith
    obtain ⟨t1, t2⟩ := tendsto_riccatiIntegrals ha.le hpos1
    obtain ⟨u1, u2⟩ := tendsto_riccatiIntegrals ha.le hpos2
    have e1 := (t2.sub (t1.const_mul R)).eventually (gt_mem_nhds hlim1)
    have e2 := (u2.sub (u1.const_mul R)).eventually (lt_mem_nhds hlim2)
    obtain ⟨j, hj⟩ := (e1.and (e2.and (eventually_ge_atTop k))).exists
    exact ⟨j, hj.2.2, hj.1, hj.2.1⟩
  choose jk hjk hneg hposk using hsign
  set ε : ℕ → ℝ := fun k => 1 / ((jk k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k => by simp only [ε]; positivity
  have hfit : ∀ k, ∃ σ ∈ Icc (σs - δ k) (σs + δ k),
      riccatiCharge a σ (ε k) - R * riccatiMass a σ (ε k) = 0 := by
    intro k
    have hpos1 : 0 < σs - δ k := by linarith [hδle k]
    have hcont : ContinuousOn (fun σ => riccatiCharge a σ (ε k) - R * riccatiMass a σ (ε k))
        (Icc (σs - δ k) (σs + δ k)) :=
      (continuousOn_riccatiCharge ha.le (hε k).le hpos1).sub
        (continuousOn_const.mul (continuousOn_riccatiMass ha.le (hε k).le hpos1))
    have hle : σs - δ k ≤ σs + δ k := by linarith [hδ k]
    obtain ⟨σ, hσ, hσ0⟩ := intermediate_value_Icc hle hcont ⟨(hneg k).le, (hposk k).le⟩
    exact ⟨σ, hσ, hσ0⟩
  choose σk hσk hσkfit using hfit
  have hσkpos : ∀ k, 0 < σk k := fun k => by linarith [(hσk k).1, hδle k]
  have hσlim : Tendsto σk atTop (𝓝 σs) := by
    have hδlim : Tendsto δ atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (min (σs / 2) 1)
      rw [mul_zero] at this
      refine this.congr fun k => ?_
      simp only [δ]
      ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => σs) atTop (𝓝 σs)).sub hδlim)
      (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => σs) atTop (𝓝 σs)).add hδlim)
      (fun k => (hσk k).1) (fun k => (hσk k).2)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun k => (hε k).le) (fun k => ?_)
    simp only [ε]
    exact div_le_div_of_nonneg_left zero_le_one (by positivity)
      (by have := hjk k; exact_mod_cast Nat.add_le_add_right this 1)
  have hev := eventually_riccatiZeros ha ha2 hσs0 hσkpos (fun k => (hε k).le) hσlim hεlim
    (fun _ : Unit => (0 : ℤ))
  obtain ⟨k, hk⟩ := hev.exists
  obtain ⟨w, hwball, hwzero⟩ := hk ()
  set σ := σk k
  set e := ε k
  have hσ := hσkpos k
  have he := hε k
  have hmass := riccatiMass_pos ha.le hσ he.le
  have hmne : riccatiMass a σ e ≠ 0 := hmass.ne'
  set C := M / riccatiMass a σ e
  have hC : 0 < C := div_pos hM hmass
  have hfitk : riccatiCharge a σ e = R * riccatiMass a σ e := by linarith [hσkfit k]
  refine ⟨a, σ, e, C, ha, ha2, hσ, he, hC, ?_, ?_, ?_, fun x => ?_, fun x => ?_, fun x => ?_,
    fun k A => ?_, ?_, fun u t => ?_, fun u t ht => riccati_reflected_positivity ha.le hσ he.le u ht,
    fun z => ?_, differentiable_riccatiFourier ha.le hσ he.le,
    fun δ hδ => riccatiFourier_order_le_one ha.le hσ he hδ, w, hwzero, ?_, ?_⟩
  · rw [integral_const_mul]
    change C * riccatiMass a σ e = M
    simp only [C]
    field_simp
  · have : (fun x => Real.exp (x / 2) * (C * riccatiSource a σ e x)) =
        fun x => C * (Real.exp (x / 2) * riccatiSource a σ e x) := funext fun x => by ring
    rw [this, integral_const_mul]
    change C * riccatiCharge a σ e = Q
    rw [hfitk]
    simp only [C, R]
    field_simp
  · have : (fun x => Real.exp (-(x / 2)) * (C * riccatiSource a σ e x)) =
        fun x => C * (Real.exp (-(x / 2)) * riccatiSource a σ e x) := funext fun x => by ring
    rw [this, integral_const_mul, riccatiCharge_eq_integral_neg, hfitk]
    simp only [C, R]
    field_simp
  · exact mul_pos hC (riccatiSource_pos ha.le hσ.ne' e x)
  · rw [riccatiSource_neg]
  · exact analyticAt_const.mul (analyticAt_riccatiSource a σ e x)
  · obtain ⟨D, hD⟩ := iteratedDeriv_riccatiSource_decay ha.le hσ he k A
    refine ⟨C * D, fun x => ?_⟩
    rw [iteratedDeriv_const_mul_field, abs_mul, abs_of_pos hC, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hD x) hC.le
  · have h := strictConcaveOn_log_riccatiSource ha.le hσ he.le
    have e1 : (fun x => Real.log (C * riccatiSource a σ e x)) =
        fun x => Real.log C + Real.log (riccatiSource a σ e x) := funext fun x => by
      rw [Real.log_mul hC.ne' (riccatiSource_pos ha.le hσ.ne' e x).ne']
    rw [e1]
    exact (h.add_const (Real.log C)).congr fun x _ => by simp only [Pi.add_apply]; ring
  · have hlog : ∀ y, Real.log (C * riccatiSource a σ e y) = Real.log C + riccatiLog a σ e y :=
      fun y => by
        rw [Real.log_mul hC.ne' (riccatiSource_pos ha.le hσ.ne' e y).ne',
          riccatiSource_eq_exp ha.le hσ.ne', Real.log_exp]
    rw [hlog, hlog, hlog]
    unfold riccatiAction
    ring
  · unfold riccatiFourier
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    push_cast
    ring
  · have hr := riccatiRadius_pos ha ha2 hσs0
    have hball : ‖w - riccatiZero a σs 0‖ ≤ riccatiRadius a σs := by
      rw [← dist_eq_norm]; exact hwball
    have him := (Complex.abs_im_le_norm (w - riccatiZero a σs 0)).trans hball
    rw [Complex.sub_im, riccatiZero_im, hA, abs_le] at him
    have hrA : riccatiRadius a σs ≤ t₀ / σs := by
      unfold riccatiRadius
      rw [hA]
      exact div_le_div_of_nonneg_right (min_le_right _ _) hσs0.le
    have : 0 < t₀ / σs := by positivity
    have e2 : 2 / σs * t₀ = 2 * (t₀ / σs) := by ring
    linarith
  · have hball : ‖w - riccatiZero a σs 0‖ ≤ riccatiRadius a σs := by
      rw [← dist_eq_norm]; exact hwball
    have him := (Complex.abs_im_le_norm (w - riccatiZero a σs 0)).trans hball
    rw [Complex.sub_im, riccatiZero_im, hA, abs_le] at him
    have hrA : riccatiRadius a σs ≤ t₀ / σs := by
      unfold riccatiRadius
      rw [hA]
      exact div_le_div_of_nonneg_right (min_le_right _ _) hσs0.le
    have h3 : t₀ / σs ≤ t₀ / m := div_le_div_of_nonneg_left ht₀.le hm hσsm
    have h4 : t₀ / m = η / 8 := by simp only [t₀]; field_simp
    have e2 : 2 / σs * t₀ = 2 * (t₀ / σs) := by ring
    linarith

/-! ## The literal theta budgets -/

theorem integral_exp_neg_half_mul_thetaCuspFullSource :
    (∫ x, Real.exp (-(x / 2)) * thetaCuspFullSource x) = 1 / 2 := by
  rw [← integral_exp_half_mul_thetaCuspFullSource_eq_half, ← integral_neg_eq_self]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [thetaCuspFullSource_neg]
  ring_nf

/-- The ordinary theta mass lies strictly between `0` and the critical charge `1/2`. -/
theorem integral_thetaCuspFullSource_mem :
    0 < ∫ x, thetaCuspFullSource x ∧ (∫ x, thetaCuspFullSource x) < 1 / 2 := by
  have hk0 : 0 < ∫ x, thetaCuspFullSource x := by
    simpa using integral_exp_mul_thetaCuspFullSource_pos 0
  refine ⟨hk0, ?_⟩
  have hkint : Integrable thetaCuspFullSource := integrable_thetaCuspFullSource'
  have h1 := integrable_exp_mul_thetaCuspFullSource_real (1 / 2)
  have h2 := integrable_exp_mul_thetaCuspFullSource_real (-(1 / 2))
  have hcosh : (∫ x, Real.cosh (x / 2) * thetaCuspFullSource x) = 1 / 2 := by
    have e : (fun x => Real.cosh (x / 2) * thetaCuspFullSource x) = fun x =>
        (Real.exp (1 / 2 * x) * thetaCuspFullSource x +
          Real.exp (-(1 / 2) * x) * thetaCuspFullSource x) / 2 := by
      funext x; rw [Real.cosh_eq]; ring_nf
    rw [e, integral_div, integral_add h1 h2]
    have a1 := integral_exp_half_mul_thetaCuspFullSource_eq_half
    have a2 := integral_exp_neg_half_mul_thetaCuspFullSource
    rw [show (fun x => Real.exp (-(1 / 2) * x) * thetaCuspFullSource x) =
      fun x => Real.exp (-(x / 2)) * thetaCuspFullSource x from funext fun x => by ring_nf, a1, a2]
    norm_num
  have hdiff : 0 < ∫ x, (Real.cosh (x / 2) - 1) * thetaCuspFullSource x := by
    have hi : Integrable (fun x => (Real.cosh (x / 2) - 1) * thetaCuspFullSource x) := by
      have e : (fun x => (Real.cosh (x / 2) - 1) * thetaCuspFullSource x) = fun x =>
          (Real.exp (1 / 2 * x) * thetaCuspFullSource x +
            Real.exp (-(1 / 2) * x) * thetaCuspFullSource x) / 2 - thetaCuspFullSource x := by
        funext x; rw [Real.cosh_eq]; ring_nf
      rw [e]
      exact ((h1.add h2).div_const 2).sub hkint
    have hnn : ∀ x, 0 ≤ (Real.cosh (x / 2) - 1) * thetaCuspFullSource x := fun x =>
      mul_nonneg (by linarith [Real.one_le_cosh (x / 2)]) (thetaCuspFullSource_pos_all x).le
    refine (integral_pos_iff_support_of_nonneg hnn hi).mpr ?_
    have hsub : Ioi (0 : ℝ) ⊆ Function.support
        (fun x => (Real.cosh (x / 2) - 1) * thetaCuspFullSource x) := by
      intro x hx
      have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
      have := Real.one_lt_cosh.mpr (div_ne_zero hx0 two_ne_zero)
      exact mul_ne_zero (by linarith) (thetaCuspFullSource_pos_all x).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  have e : (∫ x, (Real.cosh (x / 2) - 1) * thetaCuspFullSource x) =
      (∫ x, Real.cosh (x / 2) * thetaCuspFullSource x) - ∫ x, thetaCuspFullSource x := by
    rw [← integral_sub _ hkint]
    · exact integral_congr_ae (ae_of_all _ fun x => by simp only; ring)
    · have e2 : (fun x => Real.cosh (x / 2) * thetaCuspFullSource x) = fun x =>
          (Real.exp (1 / 2 * x) * thetaCuspFullSource x +
            Real.exp (-(1 / 2) * x) * thetaCuspFullSource x) / 2 := by
        funext x; rw [Real.cosh_eq]; ring_nf
      rw [e2]
      exact (h1.add h2).div_const 2
  linarith

/-- **Matching all three literal theta budgets.**  With `M = ∫ k` and `Q = 1/2`, the
charge-fitted Riccati countermodel has the ordinary mass and both reflected half-density charges
of the completed theta source, and still a Fourier zero with `0 < Im z < η`. -/
theorem riccati_three_charge_theta_budgets {η : ℝ} (hη : 0 < η) :
    ∃ a σ ε C : ℝ, 0 < a ∧ a < 1 / 2 ∧ 0 < σ ∧ 0 < ε ∧ 0 < C ∧
      (∫ x, C * riccatiSource a σ ε x) = ∫ x, thetaCuspFullSource x ∧
      (∫ x, Real.exp (x / 2) * (C * riccatiSource a σ ε x)) =
        ∫ x, Real.exp (x / 2) * thetaCuspFullSource x ∧
      (∫ x, Real.exp (-(x / 2)) * (C * riccatiSource a σ ε x)) =
        ∫ x, Real.exp (-(x / 2)) * thetaCuspFullSource x ∧
      (∀ x, 0 < C * riccatiSource a σ ε x) ∧
      (∀ u t, 0 < t → 0 < riccatiAction a σ ε u t ∧ 0 < riccatiJetOne a σ ε u t ∧
        0 < riccatiJetTwo a σ ε u t ∧ 0 < riccatiMargin a σ ε u t) ∧
      ∃ z : ℂ, riccatiFourier a σ ε z = 0 ∧ 0 < z.im ∧ z.im < η := by
  obtain ⟨hM, hMQ⟩ := integral_thetaCuspFullSource_mem
  obtain ⟨a, σ, ε, C, ha, ha2, hσ, hε, hC, h1, h2, h3, h4, -, -, -, -, -, h5, -, -, -, h6⟩ :=
    riccati_three_charge_countermodel hM hMQ hη
  have eh : (∫ x, Real.exp (x / 2) * thetaCuspFullSource x) = 1 / 2 := by
    rw [← integral_exp_half_mul_thetaCuspFullSource_eq_half]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only; ring_nf)
  exact ⟨a, σ, ε, C, ha, ha2, hσ, hε, hC, h1, h2.trans eh.symm,
    h3.trans integral_exp_neg_half_mul_thetaCuspFullSource.symm, h4, h5, h6⟩

end RHTower
