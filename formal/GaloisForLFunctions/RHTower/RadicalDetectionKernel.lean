import GaloisForLFunctions.RHTower.ResolventDivisionDecay

/-!
# The detection kernel of an off-line pair

`Ξ(z) = ξ(1/2 + iz)` is the transform of Riemann's kernel `Φ` (`riemannXiHat`), so it vanishes at
`γ_ρ` for every nontrivial zero `ρ`. At an off-line pair `γ₀ = gammaOf ρ₀`, `γ₁ = conj γ₀`, with
orders `m₀, m₁` and leading factors `u₀, u₁` (`exists_local_factor_riemannXiHat`), the kernel

`h = D_{γ₀}^{m₀} D_{γ₁}^{m₁} Φ`

has transform `Ξ(z)/((z-γ₀)^{m₀}(z-γ₁)^{m₁})` (`OffLinePairData.kernel_mul`). It therefore vanishes
at every other zero (`kernel_eq_zero`) and takes the values `u₀(γ₀)/(γ₀-γ₁)^{m₁}` and
`u₁(γ₁)/(γ₁-γ₀)^{m₀}` at the pair (`kernel_at_γ₀`, `kernel_at_γ₁`). It also keeps the
super-exponential decay of `Φ`, with weighted tails bounded by those of `Φ`
(`expTail_kernel_le`).

The module also provides the smooth plateau `plateau b w` and the shift operators `polarOp`, whose
symbol `cos(sz) - cosh(s/2)` vanishes at `±i/2`, and `nodeOp`, with symbol `c₁ + c₂ e^{isz}`. These
turn the kernel into a Hodge-class test. The calculus of the kernel is `kernel_calculus`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

local notation "Φ" => riemannPhiKernel

/-! ## Riemann's kernel in the super-exponential class -/

theorem superExpDecay_riemannPhiKernel : SuperExpDecay Φ := by
  refine ⟨continuous_riemannPhiKernel, fun c => ?_⟩
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := |c| + 1) (by positivity)
  refine Integrable.mono' (integrable_exp_neg_abs.const_mul C)
    ((continuous_riemannPhiKernel.norm.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖Φ u‖ * Real.exp (c * |u|) ≤ (C * Real.exp (-((|c| + 1) * |u|))) * Real.exp (c * |u|) :=
        mul_le_mul_of_nonneg_right (hC u) (Real.exp_pos _).le
    _ = C * Real.exp (-((|c| + 1) * |u|) + c * |u|) := by rw [Real.exp_add]; ring
    _ ≤ C * Real.exp (-|u|) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
        have : c * |u| ≤ |c| * |u| := mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg u)
        nlinarith [abs_nonneg u]

/-- The transform of Riemann's kernel, `Ξ(z) = ξ(1/2 + iz)`. -/
def riemannXiHat (z : ℂ) : ℂ := paperFT Φ z

theorem riemannXiHat_eq (z : ℂ) : riemannXiHat z = riemannPhiTransform (1 / 2 + I * z) :=
  paperFT_riemannPhiKernel z

theorem differentiable_riemannXiHat : Differentiable ℂ riemannXiHat := by
  have h : riemannXiHat = fun z => riemannPhiTransform (1 / 2 + I * z) :=
    funext riemannXiHat_eq
  rw [h]
  exact differentiable_riemannPhiTransform.comp (by fun_prop)

theorem riemannXiHat_ne_zero : riemannXiHat (-(3 / 2 * I)) ≠ 0 := by
  rw [riemannXiHat_eq]
  have h : (1 / 2 : ℂ) + I * (-(3 / 2 * I)) = 2 := by
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (-(3 / 2 : ℂ)) * hI
  rw [h]; exact riemannPhiTransform_two_ne_zero

theorem gammaOf_reflect' (ρ : ℂ) : gammaOf (Zeta23.reflect ρ) = (starRingEnd ℂ) (gammaOf ρ) := by
  unfold gammaOf Zeta23.reflect
  apply Complex.ext <;> simp
  ring_nf

theorem one_half_add_I_mul_gammaOf (ρ : ℂ) : 1 / 2 + I * gammaOf ρ = ρ := by
  unfold gammaOf; field_simp; ring

/-- `Ξ` vanishes at `gammaOf ρ` for every nontrivial zero `ρ`. -/
theorem riemannXiHat_gammaOf_eq_zero {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    riemannXiHat (gammaOf ρ) = 0 := by
  rw [riemannXiHat_eq, one_half_add_I_mul_gammaOf]
  have h : IsNontrivialZero ρ := hρ
  exact riemannPhiTransform_eq_zero_of_nontrivial h.1 h.2.1 h.2.2

/-- **Local factorisation of `Ξ` at a zero.** Every zero of the entire function `Ξ` has a finite
order `m ≥ 1` and a nonvanishing analytic leading factor. -/
theorem exists_local_factor_riemannXiHat {γ : ℂ} (hγ : riemannXiHat γ = 0) :
    ∃ (m : ℕ) (u : ℂ → ℂ), 1 ≤ m ∧ AnalyticAt ℂ u γ ∧ u γ ≠ 0 ∧
      riemannXiHat =ᶠ[𝓝 γ] fun z => (z - γ) ^ m * u z := by
  have han : AnalyticAt ℂ riemannXiHat γ := differentiable_riemannXiHat.analyticAt γ
  have hnot : ¬∀ᶠ z in 𝓝 γ, riemannXiHat z = 0 := by
    intro hev
    have hon : AnalyticOnNhd ℂ riemannXiHat univ :=
      fun z _ => differentiable_riemannXiHat.analyticAt z
    have hzero := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ γ) hev
    exact riemannXiHat_ne_zero (hzero (mem_univ _))
  obtain ⟨m, u, hu, hu0, hev⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnot
  refine ⟨m, u, ?_, hu, hu0, hev.mono fun z hz => by simpa [smul_eq_mul] using hz⟩
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · exfalso
    have := hev.self_of_nhds
    simp only [h0, pow_zero, one_smul] at this
    exact hu0 (this ▸ hγ)
  · exact hpos

/-! ## The detection kernel for an off-line pair -/

/-- The data attached to an off-line pair `γ₀, γ₁ = conj γ₀` of zeros of `Ξ`: orders and leading
factors. -/
structure OffLinePairData where
  γ₀ : ℂ
  m₀ : ℕ
  m₁ : ℕ
  u₀ : ℂ → ℂ
  u₁ : ℂ → ℂ
  hm₀ : 1 ≤ m₀
  hm₁ : 1 ≤ m₁
  hu₀ : AnalyticAt ℂ u₀ γ₀
  hu₁ : AnalyticAt ℂ u₁ ((starRingEnd ℂ) γ₀)
  hu₀0 : u₀ γ₀ ≠ 0
  hu₁0 : u₁ ((starRingEnd ℂ) γ₀) ≠ 0
  hloc₀ : riemannXiHat =ᶠ[𝓝 γ₀] fun z => (z - γ₀) ^ m₀ * u₀ z
  hloc₁ : riemannXiHat =ᶠ[𝓝 ((starRingEnd ℂ) γ₀)]
    fun z => (z - (starRingEnd ℂ) γ₀) ^ m₁ * u₁ z
  him : γ₀.im ≠ 0
  him2 : |γ₀.im| ≤ 1 / 2

namespace OffLinePairData

variable (D : OffLinePairData)

/-- The second node `γ₁ = conj γ₀`. -/
def γ₁ : ℂ := (starRingEnd ℂ) D.γ₀

theorem γ₁_ne : D.γ₀ ≠ D.γ₁ := by
  intro h
  have := congrArg Complex.im h
  simp only [γ₁, Complex.conj_im] at this
  exact D.him (by linarith)

theorem him₁ : |D.γ₁.im| ≤ 1 / 2 := by
  simp only [γ₁, Complex.conj_im, abs_neg]; exact D.him2

/-- `D_{γ₁}^{m₁} Φ`. -/
def g₁ : ℝ → ℂ := iterResolvent D.γ₁ D.m₁ Φ

/-- The detection kernel `h = D_{γ₀}^{m₀} D_{γ₁}^{m₁} Φ`. -/
def kernel : ℝ → ℂ := iterResolvent D.γ₀ D.m₀ D.g₁

theorem hloc₁' : paperFT Φ =ᶠ[𝓝 D.γ₁] fun z => (z - D.γ₁) ^ D.m₁ * D.u₁ z := D.hloc₁

theorem hloc₀' : paperFT Φ =ᶠ[𝓝 D.γ₀] fun z => (z - D.γ₀) ^ D.m₀ * D.u₀ z := D.hloc₀

theorem spec₁ : SuperExpDecay D.g₁ ∧
    (paperFT D.g₁ =ᶠ[𝓝 D.γ₁] fun z => (z - D.γ₁) ^ (D.m₁ - D.m₁) * D.u₁ z) ∧
    ∀ z, (z - D.γ₁) ^ D.m₁ * paperFT D.g₁ z = paperFT Φ z :=
  iterResolvent_spec superExpDecay_riemannPhiKernel D.him₁ D.hu₁.continuousAt D.hloc₁' D.m₁ le_rfl

theorem superExpDecay_g₁ : SuperExpDecay D.g₁ := D.spec₁.1

/-- At `γ₀`, the transform of `g₁` still vanishes to order `m₀`, with factor `u₀/(z-γ₁)^{m₁}`. -/
theorem loc₀_g₁ : paperFT D.g₁ =ᶠ[𝓝 D.γ₀]
    fun z => (z - D.γ₀) ^ D.m₀ * (D.u₀ z / (z - D.γ₁) ^ D.m₁) :=
  iterResolvent_eventually_ne superExpDecay_riemannPhiKernel D.him₁ D.hu₁.continuousAt D.hloc₁'
    D.γ₁_ne D.hloc₀' D.m₁ le_rfl

theorem contAt_v₀ : ContinuousAt (fun z => D.u₀ z / (z - D.γ₁) ^ D.m₁) D.γ₀ :=
  D.hu₀.continuousAt.div ((continuousAt_id.sub continuousAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr D.γ₁_ne))

theorem spec₀ : SuperExpDecay D.kernel ∧
    (paperFT D.kernel =ᶠ[𝓝 D.γ₀]
      fun z => (z - D.γ₀) ^ (D.m₀ - D.m₀) * (D.u₀ z / (z - D.γ₁) ^ D.m₁)) ∧
    ∀ z, (z - D.γ₀) ^ D.m₀ * paperFT D.kernel z = paperFT D.g₁ z :=
  iterResolvent_spec D.superExpDecay_g₁ D.him2 D.contAt_v₀ D.loc₀_g₁ D.m₀ le_rfl

theorem superExpDecay_kernel : SuperExpDecay D.kernel := D.spec₀.1

/-- The transform of the kernel at `γ₁`: the factor `u₁/(z-γ₀)^{m₀}`. -/
theorem loc₁_kernel : paperFT D.kernel =ᶠ[𝓝 D.γ₁]
    fun z => (z - D.γ₁) ^ 0 * ((D.u₁ z) / (z - D.γ₀) ^ D.m₀) := by
  have h₁ := D.spec₁.2.1
  rw [Nat.sub_self] at h₁
  exact iterResolvent_eventually_ne D.superExpDecay_g₁ D.him2 D.contAt_v₀ D.loc₀_g₁
    D.γ₁_ne.symm h₁ D.m₀ le_rfl

/-- `(z-γ₀)^{m₀}(z-γ₁)^{m₁} ĥ(z) = Ξ(z)`. -/
theorem kernel_mul (z : ℂ) :
    (z - D.γ₀) ^ D.m₀ * (z - D.γ₁) ^ D.m₁ * paperFT D.kernel z = riemannXiHat z := by
  rw [mul_comm ((z - D.γ₀) ^ D.m₀), mul_assoc, D.spec₀.2.2 z, D.spec₁.2.2 z]; rfl

theorem kernel_at_γ₀ : paperFT D.kernel D.γ₀ = D.u₀ D.γ₀ / (D.γ₀ - D.γ₁) ^ D.m₁ := by
  have h := D.spec₀.2.1.eq_of_nhds
  rw [Nat.sub_self, pow_zero, one_mul] at h
  exact h

theorem kernel_at_γ₁ : paperFT D.kernel D.γ₁ = D.u₁ D.γ₁ / (D.γ₁ - D.γ₀) ^ D.m₀ := by
  have h := D.loc₁_kernel.eq_of_nhds
  rw [pow_zero, one_mul] at h
  exact h

/-- At every other zero of `Ξ`, the kernel's transform vanishes. -/
theorem kernel_eq_zero {z : ℂ} (hz : riemannXiHat z = 0) (h0 : z ≠ D.γ₀) (h1 : z ≠ D.γ₁) :
    paperFT D.kernel z = 0 := by
  have h := D.kernel_mul z
  rw [hz] at h
  have hne : (z - D.γ₀) ^ D.m₀ * (z - D.γ₁) ^ D.m₁ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr h0)) (pow_ne_zero _ (sub_ne_zero.mpr h1))
  exact (mul_eq_zero.mp h).resolve_left hne

end OffLinePairData

/-! ## A smooth plateau -/

theorem smoothTransition_eventually_zero {x : ℝ} (hx : x < 0) :
    Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)

theorem smoothTransition_eventually_one {x : ℝ} (hx : 1 < x) :
    Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact Real.smoothTransition.one_of_one_le (le_of_lt hy)

theorem deriv_smoothTransition_eq_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · rw [(smoothTransition_eventually_zero hx).deriv_eq]; simp
  · rw [(smoothTransition_eventually_one hx).deriv_eq]; simp

theorem deriv2_smoothTransition_eq_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have hev : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
    rcases hx with hx | hx
    · filter_upwards [Iio_mem_nhds hx] with y hy
      exact deriv_smoothTransition_eq_zero (Or.inl hy)
    · filter_upwards [Ioi_mem_nhds hx] with y hy
      exact deriv_smoothTransition_eq_zero (Or.inr hy)
  rw [hev.deriv_eq]; simp

theorem contDiff_smoothTransition_three : ContDiff ℝ 3 Real.smoothTransition :=
  Real.smoothTransition.contDiff (n := 3)

theorem contDiff_deriv_smoothTransition : ContDiff ℝ 2 (deriv Real.smoothTransition) :=
  contDiff_smoothTransition_three.deriv'

theorem contDiff_deriv2_smoothTransition : ContDiff ℝ 1 (deriv (deriv Real.smoothTransition)) :=
  contDiff_deriv_smoothTransition.deriv'

/-- The first two derivatives of the smooth transition are bounded. -/
theorem exists_smoothTransition_deriv_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K ∧
      |deriv (deriv Real.smoothTransition) x| ≤ K := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    contDiff_deriv_smoothTransition.continuous.continuousOn
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    contDiff_deriv2_smoothTransition.continuous.continuousOn
  refine ⟨max 1 (max C₁ C₂), le_max_left _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · refine ⟨?_, ?_⟩
    · have := hC₁ x hx; rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
    · have := hC₂ x hx; rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_right _ _).trans (le_max_right _ _))
  · have hx' : x < 0 ∨ 1 < x := by
      simp only [mem_Icc, not_and_or, not_le] at hx; exact hx
    rw [deriv_smoothTransition_eq_zero hx', deriv2_smoothTransition_eq_zero hx', abs_zero]
    exact ⟨by positivity, by positivity⟩

/-- A smooth plateau: `1` on `[-(b-w), b-w]`, `0` off `(-b, b)`. -/
def plateau (b w x : ℝ) : ℝ :=
  Real.smoothTransition ((x + b) / w) * Real.smoothTransition ((b - x) / w)

theorem plateau_nonneg (b w x : ℝ) : 0 ≤ plateau b w x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem plateau_le_one (b w x : ℝ) : plateau b w x ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem plateau_eq_one {b w x : ℝ} (hw : 0 < w) (hx : |x| ≤ b - w) : plateau b w x = 1 := by
  have h1 : 1 ≤ (x + b) / w := by
    rw [le_div_iff₀ hw]; have := neg_abs_le x; linarith
  have h2 : 1 ≤ (b - x) / w := by
    rw [le_div_iff₀ hw]; have := le_abs_self x; linarith
  simp [plateau, Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2]

theorem plateau_eq_zero {b w x : ℝ} (hw : 0 < w) (hx : b ≤ |x|) : plateau b w x = 0 := by
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx
    have : (b - x) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
    simp [plateau, Real.smoothTransition.zero_of_nonpos this]
  · rw [abs_of_neg h0] at hx
    have : (x + b) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
    simp [plateau, Real.smoothTransition.zero_of_nonpos this]

theorem contDiff_plateau (b w : ℝ) : ContDiff ℝ 2 (plateau b w) := by
  have hS : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff (n := 2)
  exact (hS.comp (by fun_prop)).mul (hS.comp (by fun_prop))

/-- The derivative of the plateau. -/
def plateau₁ (b w x : ℝ) : ℝ :=
  deriv Real.smoothTransition ((x + b) / w) / w * Real.smoothTransition ((b - x) / w) -
    Real.smoothTransition ((x + b) / w) * (deriv Real.smoothTransition ((b - x) / w) / w)

/-- The second derivative of the plateau. -/
def plateau₂ (b w x : ℝ) : ℝ :=
  deriv (deriv Real.smoothTransition) ((x + b) / w) / w ^ 2 * Real.smoothTransition ((b - x) / w) -
    2 * (deriv Real.smoothTransition ((x + b) / w) * deriv Real.smoothTransition ((b - x) / w)) /
      w ^ 2 +
    Real.smoothTransition ((x + b) / w) * deriv (deriv Real.smoothTransition) ((b - x) / w) / w ^ 2

theorem hasDerivAt_affine_comp {F : ℝ → ℝ} (hF : Differentiable ℝ F) (k c x : ℝ) :
    HasDerivAt (fun x => F (k * x + c)) (deriv F (k * x + c) * k) x := by
  have hA : HasDerivAt (fun x : ℝ => k * x + c) k x := by
    simpa using ((hasDerivAt_id x).const_mul k).add_const c
  exact (hF (k * x + c)).hasDerivAt.comp x hA

theorem differentiable_smoothTransition : Differentiable ℝ Real.smoothTransition :=
  (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)

theorem differentiable_deriv_smoothTransition : Differentiable ℝ (deriv Real.smoothTransition) :=
  contDiff_deriv_smoothTransition.differentiable (by norm_num)

theorem hasDerivAt_plateau {b w : ℝ} (hw : w ≠ 0) (x : ℝ) :
    HasDerivAt (plateau b w) (plateau₁ b w x) x := by
  have hA := hasDerivAt_affine_comp differentiable_smoothTransition (1 / w) (b / w) x
  have hB := hasDerivAt_affine_comp differentiable_smoothTransition (-(1 / w)) (b / w) x
  have hfA : (fun x : ℝ => Real.smoothTransition (1 / w * x + b / w)) =
      fun x => Real.smoothTransition ((x + b) / w) := by
    funext y; congr 1; field_simp
  have hfB : (fun x : ℝ => Real.smoothTransition (-(1 / w) * x + b / w)) =
      fun x => Real.smoothTransition ((b - x) / w) := by
    funext y; congr 1; field_simp; ring
  rw [hfA] at hA; rw [hfB] at hB
  have h := hA.mul hB
  unfold plateau plateau₁
  refine h.congr_deriv ?_
  have e1 : 1 / w * x + b / w = (x + b) / w := by field_simp
  have e2 : -(1 / w) * x + b / w = (b - x) / w := by field_simp; ring
  rw [e1, e2]; ring

theorem hasDerivAt_plateau₁ {b w : ℝ} (hw : w ≠ 0) (x : ℝ) :
    HasDerivAt (plateau₁ b w) (plateau₂ b w x) x := by
  have hA := hasDerivAt_affine_comp differentiable_smoothTransition (1 / w) (b / w) x
  have hB := hasDerivAt_affine_comp differentiable_smoothTransition (-(1 / w)) (b / w) x
  have hA' := hasDerivAt_affine_comp differentiable_deriv_smoothTransition (1 / w) (b / w) x
  have hB' := hasDerivAt_affine_comp differentiable_deriv_smoothTransition (-(1 / w)) (b / w) x
  have e1 : ∀ y : ℝ, 1 / w * y + b / w = (y + b) / w := fun y => by field_simp
  have e2 : ∀ y : ℝ, -(1 / w) * y + b / w = (b - y) / w := fun y => by field_simp; ring
  simp only [e1, e2] at hA hB hA' hB'
  have h := ((hA'.div_const w).mul hB).sub (hA.mul (hB'.div_const w))
  unfold plateau₁ plateau₂
  refine h.congr_deriv ?_
  field_simp
  ring

theorem abs_plateau₁_le {b w K : ℝ} (hw : 0 < w)
    (hK : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K ∧
      |deriv (deriv Real.smoothTransition) x| ≤ K) (x : ℝ) :
    |plateau₁ b w x| ≤ 2 * K / w := by
  unfold plateau₁
  have hS1 := Real.smoothTransition.le_one ((b - x) / w)
  have hS0 := Real.smoothTransition.nonneg ((b - x) / w)
  have hT1 := Real.smoothTransition.le_one ((x + b) / w)
  have hT0 := Real.smoothTransition.nonneg ((x + b) / w)
  have ha := (hK ((x + b) / w)).1
  have hb := (hK ((b - x) / w)).1
  have hK0 : 0 ≤ K := (abs_nonneg _).trans ha
  calc |deriv Real.smoothTransition ((x + b) / w) / w * Real.smoothTransition ((b - x) / w) -
        Real.smoothTransition ((x + b) / w) * (deriv Real.smoothTransition ((b - x) / w) / w)|
      ≤ |deriv Real.smoothTransition ((x + b) / w) / w * Real.smoothTransition ((b - x) / w)| +
        |Real.smoothTransition ((x + b) / w) * (deriv Real.smoothTransition ((b - x) / w) / w)| :=
        abs_sub _ _
    _ ≤ K / w * 1 + 1 * (K / w) := by
        rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos hw, abs_of_nonneg hS0,
          abs_of_nonneg hT0]
        gcongr
    _ = 2 * K / w := by ring

theorem abs_plateau₂_le {b w K : ℝ} (hw : 0 < w)
    (hK : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K ∧
      |deriv (deriv Real.smoothTransition) x| ≤ K) (x : ℝ) :
    |plateau₂ b w x| ≤ (2 * K + 2 * K ^ 2) / w ^ 2 := by
  unfold plateau₂
  have hS1 := Real.smoothTransition.le_one ((b - x) / w)
  have hS0 := Real.smoothTransition.nonneg ((b - x) / w)
  have hT1 := Real.smoothTransition.le_one ((x + b) / w)
  have hT0 := Real.smoothTransition.nonneg ((x + b) / w)
  have ha := (hK ((x + b) / w)).1
  have hb := (hK ((b - x) / w)).1
  have ha2 := (hK ((x + b) / w)).2
  have hb2 := (hK ((b - x) / w)).2
  have hw2 : 0 < w ^ 2 := by positivity
  set p := deriv Real.smoothTransition ((x + b) / w)
  set q := deriv Real.smoothTransition ((b - x) / w)
  set p2 := deriv (deriv Real.smoothTransition) ((x + b) / w)
  set q2 := deriv (deriv Real.smoothTransition) ((b - x) / w)
  set S1 := Real.smoothTransition ((x + b) / w)
  set S2 := Real.smoothTransition ((b - x) / w)
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  have hinv : 0 < (w ^ 2)⁻¹ := inv_pos.mpr hw2
  have e : p2 * (w ^ 2)⁻¹ * S2 - 2 * (p * q) * (w ^ 2)⁻¹ + S1 * q2 * (w ^ 2)⁻¹ =
      (p2 * S2 - 2 * (p * q) + S1 * q2) * (w ^ 2)⁻¹ := by ring
  rw [e, abs_mul, abs_of_pos hinv]
  apply mul_le_mul_of_nonneg_right _ hinv.le
  have h1 : |p2 * S2| ≤ K := by
    rw [abs_mul, abs_of_nonneg hS0]; nlinarith [abs_nonneg p2]
  have h2 : |2 * (p * q)| ≤ 2 * K ^ 2 := by
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
    nlinarith
  have h3 : |S1 * q2| ≤ K := by
    rw [abs_mul, abs_of_nonneg hT0]; nlinarith [abs_nonneg q2]
  calc |p2 * S2 - 2 * (p * q) + S1 * q2| ≤ |p2 * S2| + |2 * (p * q)| + |S1 * q2| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ K + 2 * K ^ 2 + K := by linarith
    _ = 2 * K + 2 * K ^ 2 := by ring

/-! ## Shift operators with explicit symbols -/

theorem paperFT_comp_sub (g : ℝ → ℂ) (s : ℝ) (z : ℂ) :
    paperFT (fun x => g (x - s)) z = Complex.exp (I * z * s) * paperFT g z := by
  unfold paperFT
  rw [← integral_const_mul]
  have h := integral_sub_right_eq_self (μ := volume)
    (fun y : ℝ => Complex.exp (I * z * s) * (g y * Complex.exp (I * z * y))) s
  rw [← h]
  congr 1; funext x
  have e : Complex.exp (I * z * x) =
      Complex.exp (I * z * s) * Complex.exp (I * z * ((x - s : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]; ring

theorem integrable_comp_sub_mul_cexp {g : ℝ → ℂ} {z : ℂ}
    (hg : Integrable (fun u => g u * Complex.exp (I * z * u))) (s : ℝ) :
    Integrable (fun u => g (u - s) * Complex.exp (I * z * u)) := by
  have h := (hg.comp_sub_right s).const_mul (Complex.exp (I * z * s))
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring

/-- The polar operator `((g(·-s) + g(·+s))/2 - cosh(s/2) g)`, whose symbol vanishes at `±i/2`. -/
def polarOp (s : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (g (x - s) + g (x + s)) / 2 - (Real.cosh (s / 2) : ℂ) * g x

/-- The symbol `cos(sz) - cosh(s/2)` of the polar operator. -/
def polarSymbol (s : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp (I * z * s) + Complex.exp (-(I * z * s))) / 2 - (Real.cosh (s / 2) : ℂ)

theorem paperFT_polarOp {g : ℝ → ℂ} {z : ℂ}
    (hg : Integrable (fun u => g u * Complex.exp (I * z * u))) (s : ℝ) :
    paperFT (polarOp s g) z = polarSymbol s z * paperFT g z := by
  have h1 := integrable_comp_sub_mul_cexp hg s
  have h2 := integrable_comp_sub_mul_cexp hg (-s)
  simp only [sub_neg_eq_add] at h2
  have e1 := paperFT_comp_sub g s z
  have e2 := paperFT_comp_sub g (-s) z
  simp only [sub_neg_eq_add] at e2
  have hsplit : paperFT (polarOp s g) z =
      (paperFT (fun x => g (x - s)) z + paperFT (fun x => g (x + s)) z) / 2 -
        (Real.cosh (s / 2) : ℂ) * paperFT g z := by
    unfold paperFT polarOp
    rw [← integral_add h1 h2, ← integral_div, ← integral_const_mul, ← integral_sub]
    · congr 1; funext x; ring
    · exact (h1.add h2).div_const 2
    · exact hg.const_mul _
  rw [hsplit, e1, e2]
  unfold polarSymbol
  push_cast
  ring_nf

theorem polarSymbol_half_I (s : ℝ) : polarSymbol s (I / 2) = 0 := by
  unfold polarSymbol
  have h1 : I * (I / 2) * (s : ℂ) = ((-(s / 2) : ℝ) : ℂ) := by
    push_cast; linear_combination (s / 2 : ℂ) * Complex.I_mul_I
  have h2 : -(I * (I / 2) * (s : ℂ)) = ((s / 2 : ℝ) : ℂ) := by rw [h1]; push_cast; ring
  rw [h2, h1, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Real.cosh_eq]
  push_cast; ring_nf

theorem polarSymbol_neg_half_I (s : ℝ) : polarSymbol s (-(I / 2)) = 0 := by
  unfold polarSymbol
  have h1 : I * (-(I / 2)) * (s : ℂ) = ((s / 2 : ℝ) : ℂ) := by
    push_cast; linear_combination (-(s / 2) : ℂ) * Complex.I_mul_I
  have h2 : -(I * (-(I / 2)) * (s : ℂ)) = ((-(s / 2) : ℝ) : ℂ) := by rw [h1]; push_cast; ring
  rw [h2, h1, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Real.cosh_eq]
  push_cast; ring_nf

/-- The interpolation operator `c₁ g + c₂ g(· - s)`, with symbol `c₁ + c₂ e^{isz}`. -/
def nodeOp (c₁ c₂ : ℂ) (s : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ := c₁ * g x + c₂ * g (x - s)

def nodeSymbol (c₁ c₂ : ℂ) (s : ℝ) (z : ℂ) : ℂ := c₁ + c₂ * Complex.exp (I * z * s)

theorem paperFT_nodeOp {g : ℝ → ℂ} {z : ℂ}
    (hg : Integrable (fun u => g u * Complex.exp (I * z * u))) (c₁ c₂ : ℂ) (s : ℝ) :
    paperFT (nodeOp c₁ c₂ s g) z = nodeSymbol c₁ c₂ s z * paperFT g z := by
  have h1 := integrable_comp_sub_mul_cexp hg s
  have e1 := paperFT_comp_sub g s z
  have hsplit : paperFT (nodeOp c₁ c₂ s g) z =
      c₁ * paperFT g z + c₂ * paperFT (fun x => g (x - s)) z := by
    unfold paperFT nodeOp
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hg.const_mul _) (h1.const_mul _)]
    congr 1; funext x; ring
  rw [hsplit, e1]; unfold nodeSymbol; ring

/-! ## Calculus of the operators -/

theorem SuperExpDecay.integrable {g : ℝ → ℂ} (hg : SuperExpDecay g) : Integrable g := by
  have h := hg.2 0
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  exact (integrable_norm_iff hg.1.aestronglyMeasurable).mp h

theorem integral_norm_eq_expTail {g : ℝ → ℂ} : ∫ u, ‖g u‖ = expTail g 0 0 := by
  unfold expTail
  congr 1; funext u
  simp [indicator, abs_nonneg]

theorem contDiff_two_of_hasDerivAt {F F₁ F₂ : ℝ → ℂ} (h₁ : ∀ x, HasDerivAt F (F₁ x) x)
    (h₂ : ∀ x, HasDerivAt F₁ (F₂ x) x) (hc : Continuous F₂) : ContDiff ℝ 2 F := by
  have hd1 : deriv F = F₁ := funext fun x => (h₁ x).deriv
  have hd2 : deriv F₁ = F₂ := funext fun x => (h₂ x).deriv
  have hF₁ : ContDiff ℝ 1 F₁ := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiff_succ_iff_deriv]
    exact ⟨fun x => (h₂ x).differentiableAt, by simp, by rw [hd2]; exact contDiff_zero.mpr hc⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨fun x => (h₁ x).differentiableAt, by simp, by rw [hd1]; exact hF₁⟩

theorem hasDerivAt_polarOp {g g' : ℝ → ℂ} (hg : ∀ x, HasDerivAt g (g' x) x) (s x : ℝ) :
    HasDerivAt (polarOp s g) (polarOp s g' x) x := by
  unfold polarOp
  exact (((hg (x - s)).comp_sub_const x s).add ((hg (x + s)).comp_add_const x s)).div_const 2
    |>.sub ((hg x).const_mul _)

theorem hasDerivAt_nodeOp {g g' : ℝ → ℂ} (hg : ∀ x, HasDerivAt g (g' x) x) (c₁ c₂ : ℂ)
    (s x : ℝ) : HasDerivAt (nodeOp c₁ c₂ s g) (nodeOp c₁ c₂ s g' x) x := by
  unfold nodeOp
  exact ((hg x).const_mul c₁).add (((hg (x - s)).comp_sub_const x s).const_mul c₂)

theorem continuous_polarOp {g : ℝ → ℂ} (hg : Continuous g) (s : ℝ) :
    Continuous (polarOp s g) := by
  unfold polarOp; fun_prop

theorem continuous_nodeOp {g : ℝ → ℂ} (hg : Continuous g) (c₁ c₂ : ℂ) (s : ℝ) :
    Continuous (nodeOp c₁ c₂ s g) := by
  unfold nodeOp; fun_prop

theorem polarOp_eq_zero {g : ℝ → ℂ} {b s x : ℝ} (hs : 0 ≤ s)
    (hg : ∀ u, b ≤ |u| → g u = 0) (hx : b + s ≤ |x|) : polarOp s g x = 0 := by
  unfold polarOp
  have h1 : b ≤ |x - s| := by
    have := abs_sub_abs_le_abs_sub x s; rw [abs_of_nonneg hs] at this; linarith
  have h2 : b ≤ |x + s| := by
    have := abs_add' x s
    have h3 : |x| ≤ |x + s| + |s| := by
      calc |x| = |(x + s) + (-s)| := by ring_nf
        _ ≤ |x + s| + |-s| := abs_add_le _ _
        _ = |x + s| + |s| := by rw [abs_neg]
    rw [abs_of_nonneg hs] at h3; linarith
  have h0 : b ≤ |x| := by linarith
  rw [hg _ h1, hg _ h2, hg _ h0]; simp

theorem nodeOp_eq_zero {g : ℝ → ℂ} {b s x : ℝ} (hs : 0 ≤ s) (c₁ c₂ : ℂ)
    (hg : ∀ u, b ≤ |u| → g u = 0) (hx : b + s ≤ |x|) : nodeOp c₁ c₂ s g x = 0 := by
  unfold nodeOp
  have h1 : b ≤ |x - s| := by
    have := abs_sub_abs_le_abs_sub x s; rw [abs_of_nonneg hs] at this; linarith
  have h0 : b ≤ |x| := by linarith
  rw [hg _ h1, hg _ h0]; simp

theorem integral_norm_polarOp_le {g : ℝ → ℂ} (hg : Integrable g) (s : ℝ) :
    ∫ x, ‖polarOp s g x‖ ≤ (1 + Real.cosh (s / 2)) * ∫ x, ‖g x‖ := by
  have hc0 : 0 ≤ Real.cosh (s / 2) := (Real.cosh_pos _).le
  have i1 : Integrable (fun x => ‖g (x - s)‖) := (hg.comp_sub_right s).norm
  have i2 : Integrable (fun x => ‖g (x + s)‖) := (hg.comp_add_right s).norm
  have hmaj : ∀ x, ‖polarOp s g x‖ ≤ (‖g (x - s)‖ + ‖g (x + s)‖) / 2 + Real.cosh (s / 2) * ‖g x‖ := by
    intro x
    unfold polarOp
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0,
      show ‖(2 : ℂ)‖ = 2 by simp]
    gcongr
    exact norm_add_le _ _
  calc ∫ x, ‖polarOp s g x‖
      ≤ ∫ x, ((‖g (x - s)‖ + ‖g (x + s)‖) / 2 + Real.cosh (s / 2) * ‖g x‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ?_
          (Eventually.of_forall hmaj)
        exact ((i1.add i2).div_const 2).add (hg.norm.const_mul _)
    _ = (1 + Real.cosh (s / 2)) * ∫ x, ‖g x‖ := by
        have i12 : Integrable (fun x => (‖g (x - s)‖ + ‖g (x + s)‖) / 2) := (i1.add i2).div_const 2
        have i3 : Integrable (fun x => Real.cosh (s / 2) * ‖g x‖) := hg.norm.const_mul _
        rw [integral_add i12 i3, integral_div, integral_add i1 i2, integral_const_mul,
          integral_sub_right_eq_self (fun x => ‖g x‖) s,
          integral_add_right_eq_self (fun x => ‖g x‖) s]
        ring

theorem integral_norm_nodeOp_le {g : ℝ → ℂ} (hg : Integrable g) (c₁ c₂ : ℂ) (s : ℝ) :
    ∫ x, ‖nodeOp c₁ c₂ s g x‖ ≤ (‖c₁‖ + ‖c₂‖) * ∫ x, ‖g x‖ := by
  have i1 : Integrable (fun x => ‖g (x - s)‖) := (hg.comp_sub_right s).norm
  calc ∫ x, ‖nodeOp c₁ c₂ s g x‖ ≤ ∫ x, (‖c₁‖ * ‖g x‖ + ‖c₂‖ * ‖g (x - s)‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((hg.norm.const_mul _).add (i1.const_mul _)) (Eventually.of_forall fun x => ?_)
        unfold nodeOp
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ = (‖c₁‖ + ‖c₂‖) * ∫ x, ‖g x‖ := by
        rw [integral_add (hg.norm.const_mul _) (i1.const_mul _), integral_const_mul,
          integral_const_mul, integral_sub_right_eq_self (fun x => ‖g x‖) s]
        ring

theorem SuperExpDecay.sub {g h : ℝ → ℂ} (hg : SuperExpDecay g) (hh : SuperExpDecay h) :
    SuperExpDecay (fun u => g u - h u) := by
  have h2 := hg.add (hh.const_mul (-1))
  have e : (g + fun u => -1 * h u) = fun u => g u - h u := by funext u; simp; ring
  rw [e] at h2; exact h2

theorem continuous_plateau₂ (b w : ℝ) : Continuous (plateau₂ b w) := by
  have c1 := contDiff_deriv_smoothTransition.continuous
  have c2 := contDiff_deriv2_smoothTransition.continuous
  have c0 := (Real.smoothTransition.contDiff (n := 0)).continuous
  unfold plateau₂
  have hA : Continuous fun x : ℝ => (x + b) / w := by fun_prop
  have hB : Continuous fun x : ℝ => (b - x) / w := by fun_prop
  exact (((c2.comp hA).div_const _).mul (c0.comp hB)).sub
    (((continuous_const.mul ((c1.comp hA).mul (c1.comp hB))).div_const _)) |>.add
    (((c0.comp hA).mul (c2.comp hB)).div_const _)

theorem continuous_plateau₁ (b w : ℝ) : Continuous (plateau₁ b w) := by
  have c1 := contDiff_deriv_smoothTransition.continuous
  have c0 := (Real.smoothTransition.contDiff (n := 0)).continuous
  unfold plateau₁
  have hA : Continuous fun x : ℝ => (x + b) / w := by fun_prop
  have hB : Continuous fun x : ℝ => (b - x) / w := by fun_prop
  exact (((c1.comp hA).div_const _).mul (c0.comp hB)).sub ((c0.comp hA).mul ((c1.comp hB).div_const _))

theorem continuous_plateau (b w : ℝ) : Continuous (plateau b w) :=
  (contDiff_plateau b w).continuous

namespace OffLinePairData

variable (D : OffLinePairData)

/-- The total order `m₀ + m₁` divided out. -/
def n : ℕ := D.m₀ + D.m₁

theorem expTail_iter₁_le {k : ℕ} (hk : k ≤ D.m₁) {c X : ℝ} (hc : 0 ≤ c) :
    expTail (iterResolvent D.γ₁ k Φ) c X ≤ 2 ^ D.n * expTail Φ (c + 3 / 2 * D.n) X := by
  have h := expTail_iterResolvent_le superExpDecay_riemannPhiKernel D.him₁ D.hu₁.continuousAt
    D.hloc₁' k hk c X hc
  refine h.trans (mul_le_mul ?_ ?_ (expTail_nonneg _ _ _) (by positivity))
  · exact pow_le_pow_right₀ (by norm_num) (by unfold n; omega)
  · apply expTail_mono_weight superExpDecay_riemannPhiKernel
    have : (k : ℝ) ≤ D.n := by unfold n; exact_mod_cast (by omega : k ≤ D.m₀ + D.m₁)
    linarith

theorem expTail_iter₀_le {k : ℕ} (hk : k ≤ D.m₀) {c X : ℝ} (hc : 0 ≤ c) :
    expTail (iterResolvent D.γ₀ k D.g₁) c X ≤ 2 ^ D.n * expTail Φ (c + 3 / 2 * D.n) X := by
  have h1 := expTail_iterResolvent_le D.superExpDecay_g₁ D.him2 D.contAt_v₀ D.loc₀_g₁ k hk c X hc
  have h2 := expTail_iterResolvent_le superExpDecay_riemannPhiKernel D.him₁ D.hu₁.continuousAt
    D.hloc₁' D.m₁ le_rfl (c + 3 / 2 * k) X (by positivity)
  have h2' : expTail D.g₁ (c + 3 / 2 * k) X ≤
      2 ^ D.m₁ * expTail Φ (c + 3 / 2 * k + 3 / 2 * D.m₁) X := h2
  calc expTail (iterResolvent D.γ₀ k D.g₁) c X
      ≤ 2 ^ k * (2 ^ D.m₁ * expTail Φ (c + 3 / 2 * k + 3 / 2 * D.m₁) X) :=
        h1.trans (mul_le_mul_of_nonneg_left h2' (by positivity))
    _ = 2 ^ (k + D.m₁) * expTail Φ (c + 3 / 2 * k + 3 / 2 * D.m₁) X := by rw [pow_add]; ring
    _ ≤ 2 ^ D.n * expTail Φ (c + 3 / 2 * D.n) X := by
        refine mul_le_mul ?_ ?_ (expTail_nonneg _ _ _) (by positivity)
        · exact pow_le_pow_right₀ (by norm_num) (by unfold n; omega)
        · apply expTail_mono_weight superExpDecay_riemannPhiKernel
          have : (k : ℝ) + D.m₁ ≤ D.n := by
            unfold n; push_cast; have : (k : ℝ) ≤ D.m₀ := by exact_mod_cast hk
            linarith
          linarith

theorem superExpDecay_iter₀ {k : ℕ} (hk : k ≤ D.m₀) :
    SuperExpDecay (iterResolvent D.γ₀ k D.g₁) :=
  (iterResolvent_spec D.superExpDecay_g₁ D.him2 D.contAt_v₀ D.loc₀_g₁ k hk).1

theorem superExpDecay_iter₁ {k : ℕ} (hk : k ≤ D.m₁) :
    SuperExpDecay (iterResolvent D.γ₁ k Φ) :=
  (iterResolvent_spec superExpDecay_riemannPhiKernel D.him₁ D.hu₁.continuousAt D.hloc₁' k hk).1

/-- The penultimate iterate `D_{γ₀}^{m₀-1} g₁`. -/
def gp : ℝ → ℂ := iterResolvent D.γ₀ (D.m₀ - 1) D.g₁

theorem superExpDecay_gp : SuperExpDecay D.gp := D.superExpDecay_iter₀ (by omega)

theorem kernel_eq : D.kernel = resolventDiv D.γ₀ D.gp := by
  have h : D.m₀ = (D.m₀ - 1) + 1 := by have := D.hm₀; omega
  unfold kernel gp
  conv_lhs => rw [h]
  rw [iterResolvent_succ]

theorem norm_γ₁ : ‖D.γ₁‖ = ‖D.γ₀‖ := Complex.norm_conj _

/-- The penultimate iterate is itself a resolvent image. -/
theorem exists_gp_resolvent : ∃ (γ' : ℂ) (g₂ : ℝ → ℂ), ‖γ'‖ = ‖D.γ₀‖ ∧ SuperExpDecay g₂ ∧
    D.gp = resolventDiv γ' g₂ ∧
    ∀ c X : ℝ, 0 ≤ c → expTail g₂ c X ≤ 2 ^ D.n * expTail Φ (c + 3 / 2 * D.n) X := by
  rcases Nat.lt_or_ge D.m₀ 2 with h1 | h2
  · have hm : D.m₀ - 1 = 0 := by have := D.hm₀; omega
    have hm₁ : D.m₁ = (D.m₁ - 1) + 1 := by have := D.hm₁; omega
    refine ⟨D.γ₁, iterResolvent D.γ₁ (D.m₁ - 1) Φ, D.norm_γ₁, D.superExpDecay_iter₁ (by omega),
      ?_, fun c X hc => D.expTail_iter₁_le (by omega) hc⟩
    unfold gp g₁
    rw [hm, iterResolvent_zero]
    conv_lhs => rw [hm₁]
    rw [iterResolvent_succ]
  · refine ⟨D.γ₀, iterResolvent D.γ₀ (D.m₀ - 2) D.g₁, rfl, D.superExpDecay_iter₀ (by omega),
      ?_, fun c X hc => D.expTail_iter₀_le (by omega) hc⟩
    unfold gp
    rw [show D.m₀ - 1 = (D.m₀ - 2) + 1 by omega, iterResolvent_succ]

theorem expTail_kernel_le {c X : ℝ} (hc : 0 ≤ c) :
    expTail D.kernel c X ≤ 2 ^ D.n * expTail Φ (c + 3 / 2 * D.n) X :=
  D.expTail_iter₀_le le_rfl hc

theorem expTail_gp_le {c X : ℝ} (hc : 0 ≤ c) :
    expTail D.gp c X ≤ 2 ^ D.n * expTail Φ (c + 3 / 2 * D.n) X :=
  D.expTail_iter₀_le (by omega) hc

/-- **Calculus of the kernel.** `h` is twice differentiable with explicit derivatives whose
`L¹` norms are controlled by the weighted norm of `Φ`. -/
theorem kernel_calculus : ∃ k₁ k₂ : ℝ → ℂ, (∀ x, HasDerivAt D.kernel (k₁ x) x) ∧
    (∀ x, HasDerivAt k₁ (k₂ x) x) ∧ Continuous k₁ ∧ Continuous k₂ ∧ Integrable k₁ ∧
    Integrable k₂ ∧
    (∫ x, ‖k₁ x‖) ≤ (1 + ‖D.γ₀‖) * (2 ^ D.n * expTail Φ (3 / 2 * D.n) 0) ∧
    (∫ x, ‖k₂ x‖) ≤ (1 + ‖D.γ₀‖) ^ 2 * (2 ^ D.n * expTail Φ (3 / 2 * D.n) 0) := by
  obtain ⟨γ', g₂, hγ', hg₂, hgp, hbd₂⟩ := D.exists_gp_resolvent
  set G : ℝ := 2 ^ D.n * expTail Φ (3 / 2 * D.n) 0 with hG
  have hG0 : 0 ≤ G := mul_nonneg (by positivity) (expTail_nonneg _ _ _)
  have hgp' := D.superExpDecay_gp
  have hk := D.superExpDecay_kernel
  set k₁ : ℝ → ℂ := fun x => -I * D.γ₀ * D.kernel x - I * D.gp x with hk₁
  set p₁ : ℝ → ℂ := fun x => -I * γ' * D.gp x - I * g₂ x with hp₁
  set k₂ : ℝ → ℂ := fun x => -I * D.γ₀ * k₁ x - I * p₁ x with hk₂
  have hdk : ∀ x, HasDerivAt D.kernel (k₁ x) x := by
    intro x
    have h := hasDerivAt_resolventDiv hgp' D.γ₀ x
    rw [← D.kernel_eq] at h; exact h
  have hdp : ∀ x, HasDerivAt D.gp (p₁ x) x := by
    intro x
    have h := hasDerivAt_resolventDiv hg₂ γ' x
    rw [← hgp] at h; exact h
  have hdk₁ : ∀ x, HasDerivAt k₁ (k₂ x) x := by
    intro x
    exact ((hdk x).const_mul (-I * D.γ₀)).sub ((hdp x).const_mul I) |>.congr_deriv (by
      simp only [hk₂]; try ring)
  have ck : Continuous D.kernel := hk.1
  have cgp : Continuous D.gp := hgp'.1
  have cg₂ : Continuous g₂ := hg₂.1
  have ck₁ : Continuous k₁ := by simp only [hk₁]; fun_prop
  have cp₁ : Continuous p₁ := by simp only [hp₁]; fun_prop
  have ck₂ : Continuous k₂ := by simp only [hk₂]; fun_prop
  have ik : Integrable D.kernel := hk.integrable
  have igp : Integrable D.gp := hgp'.integrable
  have ig₂ : Integrable g₂ := hg₂.integrable
  have ik₁ : Integrable k₁ := (ik.const_mul _).sub (igp.const_mul _)
  have ip₁ : Integrable p₁ := (igp.const_mul _).sub (ig₂.const_mul _)
  have ik₂ : Integrable k₂ := (ik₁.const_mul _).sub (ip₁.const_mul _)
  have nk : ∫ x, ‖D.kernel x‖ ≤ G := by
    rw [integral_norm_eq_expTail]; have := D.expTail_kernel_le (c := 0) (X := 0) le_rfl
    simpa using this
  have ngp : ∫ x, ‖D.gp x‖ ≤ G := by
    rw [integral_norm_eq_expTail]; have := D.expTail_gp_le (c := 0) (X := 0) le_rfl
    simpa using this
  have ng₂ : ∫ x, ‖g₂ x‖ ≤ G := by
    rw [integral_norm_eq_expTail]; have := hbd₂ 0 0 le_rfl
    simpa using this
  have hnI : ‖I‖ = 1 := Complex.norm_I
  have nk₁ : ∫ x, ‖k₁ x‖ ≤ ‖D.γ₀‖ * (∫ x, ‖D.kernel x‖) + ∫ x, ‖D.gp x‖ := by
    rw [← integral_const_mul, ← integral_add (ik.norm.const_mul _) igp.norm]
    refine integral_mono ik₁.norm ((ik.norm.const_mul _).add igp.norm) fun x => ?_
    simp only [hk₁]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_neg, hnI]; simp
  have np₁ : ∫ x, ‖p₁ x‖ ≤ ‖γ'‖ * (∫ x, ‖D.gp x‖) + ∫ x, ‖g₂ x‖ := by
    rw [← integral_const_mul, ← integral_add (igp.norm.const_mul _) ig₂.norm]
    refine integral_mono ip₁.norm ((igp.norm.const_mul _).add ig₂.norm) fun x => ?_
    simp only [hp₁]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_neg, hnI]; simp
  have nk₂ : ∫ x, ‖k₂ x‖ ≤ ‖D.γ₀‖ * (∫ x, ‖k₁ x‖) + ∫ x, ‖p₁ x‖ := by
    rw [← integral_const_mul, ← integral_add (ik₁.norm.const_mul _) ip₁.norm]
    refine integral_mono ik₂.norm ((ik₁.norm.const_mul _).add ip₁.norm) fun x => ?_
    simp only [hk₂]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_neg, hnI]; simp
  have hγn : 0 ≤ ‖D.γ₀‖ := norm_nonneg _
  have b₁ : ∫ x, ‖k₁ x‖ ≤ (1 + ‖D.γ₀‖) * G := by nlinarith
  refine ⟨k₁, k₂, hdk, hdk₁, ck₁, ck₂, ik₁, ik₂, b₁, ?_⟩
  rw [hγ'] at np₁
  nlinarith

end OffLinePairData

end

end RHTower
