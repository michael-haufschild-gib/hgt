import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Legendre residual transduction

A source potential `A` on an open convex `U ⊆ Θ` (finite-dimensional real) with reporter
`μ = dA`, positive-definite Hessian `H = d²A` and third response `T = d³A`, whose reporter is a
diffeomorphism onto an open convex `M ⊆ Θ*` with continuous inverse `ν`, turns a marked target
`m ∈ M` into the residual `e(θ) = m - μ(θ)`, the promoted intervention `X_m(θ) = H_θ⁻¹ e(θ)` and the
power `P(θ) = e(θ)(X_m(θ)) = H_θ(X, X) ≥ 0`.

* **Theorem 4.1.**  `θ(t) = ν(m + e^{-t}(μ(θ₀) - m))` is the unique solution of `θ' = X_m(θ)`,
  `θ(0) = θ₀`; its reporter contracts on a straight line, `e(θ(t)) = e^{-t} e(θ₀)`, and
  `θ(t) → θ_* = ν(m)`.
* **Theorem 5.1.**  The dual Bregman work `W(η) = A*(m) - A*(η) - dA*_η(m - η)` obeys
  `dW/dt = -P`, `W(μ(θ₀)) - W(μ(θ(T))) = ∫₀ᵀ P` and `W(μ(θ₀)) = ∫₀^∞ P`.
* **Corollary 5.2.**  `θ_*` is the unique stationary point, the unique zero-work state and the
  global limit.
* **Theorem 7.1.**  `P' = -2P - T(v, v, v)` along the flow, `v = X_m(θ)`.
* **Theorem 9.1.**  Compact dual-work sublevels give compact bounded-work sets and trajectories.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ResidualTransduction

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ]

/-- A Legendre source chart: the data and hypotheses of `(LRT.8)`–`(LRT.10)`. -/
structure LegendreChart (Θ : Type*) [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] where
  /-- the open convex source domain -/
  U : Set Θ
  isOpen_U : IsOpen U
  convex_U : Convex ℝ U
  /-- the formation potential -/
  A : Θ → ℝ
  /-- the reporter `μ = dA` -/
  μ : Θ → Θ →L[ℝ] ℝ
  /-- the Hessian `H = d²A` -/
  H : Θ → Θ →L[ℝ] Θ →L[ℝ] ℝ
  /-- the third response `T = d³A` -/
  T : Θ → Θ →L[ℝ] Θ →L[ℝ] Θ →L[ℝ] ℝ
  hasFDerivAt_A : ∀ θ ∈ U, HasFDerivAt A (μ θ) θ
  hasFDerivAt_μ : ∀ θ ∈ U, HasFDerivAt μ (H θ) θ
  hasFDerivAt_H : ∀ θ ∈ U, HasFDerivAt H (T θ) θ
  posDef : ∀ θ ∈ U, ∀ v, v ≠ 0 → 0 < H θ v v
  /-- the reporter image -/
  M : Set (Θ →L[ℝ] ℝ)
  image_eq : μ '' U = M
  isOpen_M : IsOpen M
  convex_M : Convex ℝ M
  /-- the inverse reporter `ν = μ⁻¹ : M → U` -/
  inv : (Θ →L[ℝ] ℝ) → Θ
  mapsTo_inv : MapsTo inv M U
  μ_inv : ∀ η ∈ M, μ (inv η) = η
  inv_μ : ∀ θ ∈ U, inv (μ θ) = θ
  continuousOn_inv : ContinuousOn inv M

namespace LegendreChart

variable (C : LegendreChart Θ)

omit [FiniteDimensional ℝ Θ] in
theorem μ_mem {θ : Θ} (hθ : θ ∈ C.U) : C.μ θ ∈ C.M := C.image_eq ▸ mem_image_of_mem _ hθ

omit [FiniteDimensional ℝ Θ] in
/-- The Hessian is symmetric (second derivative symmetry). -/
theorem H_symm {θ : Θ} (hθ : θ ∈ C.U) (v w : Θ) : C.H θ v w = C.H θ w v :=
  second_derivative_symmetric_of_eventually
    (Filter.mem_of_superset (C.isOpen_U.mem_nhds hθ) fun y hy => C.hasFDerivAt_A y hy)
    (C.hasFDerivAt_μ θ hθ) v w

theorem finrank_dual : Module.finrank ℝ (Θ →L[ℝ] ℝ) = Module.finrank ℝ Θ := by
  rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Θ)
    (F' := ℝ)), Subspace.dual_finrank_eq]

/-- The positive-definite Hessian, as an isomorphism `Θ ≃ Θ*`. -/
def hessianEquiv {θ : Θ} (hθ : θ ∈ C.U) : Θ ≃L[ℝ] (Θ →L[ℝ] ℝ) :=
  have hinj : Function.Injective (C.H θ : Θ →ₗ[ℝ] Θ →L[ℝ] ℝ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra h
    have := C.posDef θ hθ v h
    have hv' : C.H θ v = 0 := hv
    rw [hv', zero_apply] at this
    exact lt_irrefl 0 this
  (LinearEquiv.ofBijective (C.H θ : Θ →ₗ[ℝ] Θ →L[ℝ] ℝ)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_dual (Θ := Θ)).symm).1 hinj⟩).toContinuousLinearEquiv

theorem hessianEquiv_coe {θ : Θ} (hθ : θ ∈ C.U) :
    (C.hessianEquiv hθ : Θ →L[ℝ] Θ →L[ℝ] ℝ) = C.H θ := by
  ext v
  rfl

theorem H_isInvertible {θ : Θ} (hθ : θ ∈ C.U) : (C.H θ).IsInvertible :=
  ⟨C.hessianEquiv hθ, C.hessianEquiv_coe hθ⟩

theorem H_inverse_apply {θ : Θ} (hθ : θ ∈ C.U) (y : Θ →L[ℝ] ℝ) :
    C.H θ ((C.H θ).inverse y) = y :=
  (C.H_isInvertible hθ).self_apply_inverse y

/-- **`(LRT.11)`, second half**: the inverse reporter has derivative `H⁻¹` at `η ∈ M`. -/
theorem hasFDerivAt_inv {η : Θ →L[ℝ] ℝ} (hη : η ∈ C.M) :
    HasFDerivAt C.inv (C.H (C.inv η)).inverse η := by
  have hθ := C.mapsTo_inv hη
  have h := HasFDerivAt.of_local_left_inverse (f' := C.hessianEquiv hθ)
    (C.continuousOn_inv.continuousAt (C.isOpen_M.mem_nhds hη))
    (by rw [hessianEquiv_coe]; exact C.hasFDerivAt_μ _ hθ)
    (Filter.mem_of_superset (C.isOpen_M.mem_nhds hη) fun y hy => C.μ_inv y hy)
  rwa [← ContinuousLinearMap.inverse_equiv, hessianEquiv_coe] at h

/-! ### Residual, promoted intervention, power -/

/-- `(LRT.12)` the residual `e(θ) = m - μ(θ)`. -/
def residual (m : Θ →L[ℝ] ℝ) (θ : Θ) : Θ →L[ℝ] ℝ := m - C.μ θ

/-- `(LRT.12)` the promoted intervention `X_m(θ) = H_θ⁻¹ e(θ)`. -/
def promote (m : Θ →L[ℝ] ℝ) (θ : Θ) : Θ := (C.H θ).inverse (C.residual m θ)

/-- `(LRT.12)` the power `P(θ) = e(θ)(X_m(θ))`. -/
def power (m : Θ →L[ℝ] ℝ) (θ : Θ) : ℝ := C.residual m θ (C.promote m θ)

theorem H_promote (m : Θ →L[ℝ] ℝ) {θ : Θ} (hθ : θ ∈ C.U) :
    C.H θ (C.promote m θ) = C.residual m θ :=
  C.H_inverse_apply hθ _

/-- `(LRT.13)`: `P = H(X, X) ≥ 0`. -/
theorem power_eq (m : Θ →L[ℝ] ℝ) {θ : Θ} (hθ : θ ∈ C.U) :
    C.power m θ = C.H θ (C.promote m θ) (C.promote m θ) := by
  rw [power, ← C.H_promote m hθ]

/-- The target state `θ_* = ν(m)`. -/
def target (m : Θ →L[ℝ] ℝ) : Θ := C.inv m

theorem promote_eq_zero_iff (m : Θ →L[ℝ] ℝ) (hm : m ∈ C.M) {θ : Θ} (hθ : θ ∈ C.U) :
    C.promote m θ = 0 ↔ θ = C.target m := by
  constructor
  · intro h
    have h1 := C.H_promote m hθ
    rw [h, map_zero, residual, eq_comm, sub_eq_zero] at h1
    rw [target, h1, C.inv_μ θ hθ]
  · intro h
    rw [promote, residual, h, target, C.μ_inv m hm, sub_self, map_zero]

/-- `(LRT.13)`: `P ≥ 0`, with equality exactly at `θ_*`. -/
theorem power_nonneg_and_eq_zero_iff (m : Θ →L[ℝ] ℝ) (hm : m ∈ C.M) {θ : Θ} (hθ : θ ∈ C.U) :
    0 ≤ C.power m θ ∧ (C.power m θ = 0 ↔ θ = C.target m) := by
  rw [C.power_eq m hθ]
  by_cases h : C.promote m θ = 0
  · rw [h, map_zero]
    exact ⟨le_rfl, ⟨fun _ => (C.promote_eq_zero_iff m hm hθ).1 h, fun _ => rfl⟩⟩
  · have hpos := C.posDef θ hθ _ h
    refine ⟨hpos.le, ⟨fun h0 => absurd h0 hpos.ne', fun ht => absurd ((C.promote_eq_zero_iff m hm
      hθ).2 ht) h⟩⟩

/-! ### Theorem 4.1: the exact residual-transduction flow -/

/-- `(LRT.14)` the straight mean-coordinate contraction `η(t) = m + e^{-t}(μ(θ₀) - m)`. -/
def flowMean (m : Θ →L[ℝ] ℝ) (θ₀ : Θ) (t : ℝ) : Θ →L[ℝ] ℝ :=
  m + Real.exp (-t) • (C.μ θ₀ - m)

/-- `(LRT.15)` the source flow `θ(t) = ν(η(t))`. -/
def flow (m : Θ →L[ℝ] ℝ) (θ₀ : Θ) (t : ℝ) : Θ := C.inv (C.flowMean m θ₀ t)

variable {m : Θ →L[ℝ] ℝ} (hm : m ∈ C.M) {θ₀ : Θ} (hθ₀ : θ₀ ∈ C.U)
include hm hθ₀

omit [FiniteDimensional ℝ Θ] in
theorem flowMean_mem {t : ℝ} (ht : 0 ≤ t) : C.flowMean m θ₀ t ∈ C.M := by
  have h := C.convex_M hm (C.μ_mem hθ₀)
    (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)) : 0 ≤ 1 - Real.exp (-t))
    (Real.exp_pos (-t)).le (by ring)
  convert h using 1
  rw [flowMean]
  module

omit [FiniteDimensional ℝ Θ] in
theorem flow_mem {t : ℝ} (ht : 0 ≤ t) : C.flow m θ₀ t ∈ C.U :=
  C.mapsTo_inv (C.flowMean_mem hm hθ₀ ht)

omit [FiniteDimensional ℝ Θ] in
/-- **`(LRT.17)`**: the reporter moves on the straight contraction. -/
theorem μ_flow {t : ℝ} (ht : 0 ≤ t) : C.μ (C.flow m θ₀ t) = C.flowMean m θ₀ t :=
  C.μ_inv _ (C.flowMean_mem hm hθ₀ ht)

omit [FiniteDimensional ℝ Θ] in
/-- **`(LRT.17)`**: `e(θ(t)) = e^{-t} e(θ₀)`. -/
theorem residual_flow {t : ℝ} (ht : 0 ≤ t) :
    C.residual m (C.flow m θ₀ t) = Real.exp (-t) • C.residual m θ₀ := by
  rw [residual, C.μ_flow hm hθ₀ ht, flowMean, residual, smul_sub, smul_sub]
  abel

omit [FiniteDimensional ℝ Θ] hm hθ₀ in
theorem hasDerivAt_flowMean (t : ℝ) :
    HasDerivAt (C.flowMean m θ₀) (m - C.flowMean m θ₀ t) t := by
  have h := (((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).smul_const
    (C.μ θ₀ - m)).const_add m
  have heq : m - C.flowMean m θ₀ t = (Real.exp (-t) * -1) • (C.μ θ₀ - m) := by
    rw [flowMean]
    module
  rw [heq]
  exact h

/-- **Theorem 4.1, `(LRT.16)`, `(LRT.18)`**: `θ' = X_m(θ)` along the flow. -/
theorem hasDerivAt_flow {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (C.flow m θ₀) (C.promote m (C.flow m θ₀ t)) t := by
  have h := (C.hasFDerivAt_inv (C.flowMean_mem hm hθ₀ ht)).comp_hasDerivAt t
    (C.hasDerivAt_flowMean (m := m) (θ₀ := θ₀) t)
  have heq : C.promote m (C.flow m θ₀ t) =
      (C.H (C.inv (C.flowMean m θ₀ t))).inverse (m - C.flowMean m θ₀ t) := by
    rw [promote, residual, C.μ_flow hm hθ₀ ht]
    rfl
  rw [heq]
  exact h

omit hm hθ₀ in
/-- **Theorem 4.1, uniqueness, `(LRT.19)`**: every solution of `θ' = X_m(θ)`, `θ(0) = θ₀`, staying
in `U` agrees with the flow on `[0, ∞)`. -/
theorem flow_unique (γ : ℝ → Θ) (hγ0 : γ 0 = θ₀) (hγU : ∀ t, 0 ≤ t → γ t ∈ C.U)
    (hγ : ∀ t, 0 ≤ t → HasDerivAt γ (C.promote m (γ t)) t) :
    ∀ t, 0 ≤ t → γ t = C.flow m θ₀ t := by
  -- `f(t) = e^t (μ(γ t) - m)` is constant
  set f : ℝ → Θ →L[ℝ] ℝ := fun t => Real.exp t • (C.μ (γ t) - m) with hf
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt f 0 t := fun t ht => by
    have hμγ : HasDerivAt (fun s => C.μ (γ s)) (C.H (γ t) (C.promote m (γ t))) t :=
      (C.hasFDerivAt_μ _ (hγU t ht)).comp_hasDerivAt t (hγ t ht)
    rw [C.H_promote m (hγU t ht), residual] at hμγ
    have h := (Real.hasDerivAt_exp t).smul (hμγ.sub_const m)
    rw [show Real.exp t • (m - C.μ (γ t)) + Real.exp t • (C.μ (γ t) - m) = 0 by
      rw [← smul_add, sub_add_sub_cancel, sub_self, smul_zero]] at h
    exact h
  have hconst : ∀ t, 0 ≤ t → f t = f 0 := fun t ht => by
    have hcont : ContinuousOn f (Icc 0 t) := fun s hs =>
      (hderiv s hs.1).continuousAt.continuousWithinAt
    exact constant_of_has_deriv_right_zero hcont
      (fun s hs => (hderiv s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  intro t ht
  have h := hconst t ht
  simp only [hf, Real.exp_zero, one_smul, hγ0] at h
  have hμ : C.μ (γ t) = C.flowMean m θ₀ t := by
    have h' := congrArg (fun z => Real.exp (-t) • z) h
    simp only [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul] at h'
    rw [flowMean, ← h']
    abel
  rw [flow, ← hμ, C.inv_μ _ (hγU t ht)]

omit [FiniteDimensional ℝ Θ] hθ₀ in
/-- **Theorem 4.1**: `θ(t) → θ_*`. -/
theorem tendsto_flow : Tendsto (C.flow m θ₀) atTop (𝓝 (C.target m)) := by
  have hmean : Tendsto (C.flowMean m θ₀) atTop (𝓝 m) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.smul_const (C.μ θ₀ - m)).const_add m
    rw [zero_smul, add_zero] at h
    exact h
  have hcont := C.continuousOn_inv.continuousAt (C.isOpen_M.mem_nhds hm)
  exact hcont.tendsto.comp hmean

/-! ### Theorem 5.1: work conservation -/

/-- The Legendre dual `A*(η) = η(ν η) - A(ν η)` on `M`. -/
def dualPotential (η : Θ →L[ℝ] ℝ) : ℝ := η (C.inv η) - C.A (C.inv η)

omit hm hθ₀ in
/-- **`(LRT.11)`**: `dA*_η = ν(η)`, i.e. `ζ ↦ ζ(ν η)`. -/
theorem hasFDerivAt_dualPotential {η : Θ →L[ℝ] ℝ} (hη : η ∈ C.M) :
    HasFDerivAt C.dualPotential (ContinuousLinearMap.apply ℝ ℝ (C.inv η)) η := by
  have hinv := C.hasFDerivAt_inv hη
  have hθ := C.mapsTo_inv hη
  have h1 := (hasFDerivAt_id (𝕜 := ℝ) η).clm_apply hinv
  have h2 := (C.hasFDerivAt_A _ hθ).comp η hinv
  have h := h1.sub h2
  rw [C.μ_inv η hη] at h
  have heq : (id η : Θ →L[ℝ] ℝ) ∘L (C.H (C.inv η)).inverse +
      (ContinuousLinearMap.id ℝ (Θ →L[ℝ] ℝ)).flip (C.inv η) -
      η ∘L (C.H (C.inv η)).inverse = ContinuousLinearMap.apply ℝ ℝ (C.inv η) := by
    ext ζ
    simp
  rw [heq] at h
  exact h

/-- **`(LRT.20)`** the dual Bregman work `W(η) = A*(m) - A*(η) - dA*_η(m - η)`. -/
def work (m η : Θ →L[ℝ] ℝ) : ℝ := C.dualPotential m - C.dualPotential η - (m - η) (C.inv η)

omit hm hθ₀ [FiniteDimensional ℝ Θ] in
theorem work_self (m : Θ →L[ℝ] ℝ) : C.work m m = 0 := by
  simp [work]

omit hm hθ₀ in
/-- **`(LRT.24)`**: `dW_η(z) = -d²A*_η(z, m - η) = -z(H⁻¹(m - η))`, `H = H_{ν η}`. -/
theorem hasFDerivAt_work {η : Θ →L[ℝ] ℝ} (hη : η ∈ C.M) :
    HasFDerivAt (C.work m)
      (-ContinuousLinearMap.apply ℝ ℝ ((C.H (C.inv η)).inverse (m - η))) η := by
  have hθ := C.mapsTo_inv hη
  have hpair := ((hasFDerivAt_id (𝕜 := ℝ) η).const_sub m).clm_apply (C.hasFDerivAt_inv hη)
  have h := ((C.hasFDerivAt_dualPotential hη).const_sub (C.dualPotential m)).sub hpair
  have hsymm : ∀ z : Θ →L[ℝ] ℝ,
      (m - η) ((C.H (C.inv η)).inverse z) = z ((C.H (C.inv η)).inverse (m - η)) := fun z => by
    conv_lhs => rw [← C.H_inverse_apply hθ (m - η)]
    conv_rhs => rw [← C.H_inverse_apply hθ z]
    exact C.H_symm hθ _ _
  refine h.congr_fderiv (ContinuousLinearMap.ext fun z => ?_)
  have hz := hsymm z
  simp only [map_sub, sub_apply] at hz
  simp
  linarith

/-- **Theorem 5.1, `(LRT.21)`**: `dW/dt = -P` along the flow. -/
theorem hasDerivAt_work_flow {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => C.work m (C.flowMean m θ₀ s)) (-C.power m (C.flow m θ₀ t)) t := by
  have hη := C.hasDerivAt_flowMean (m := m) (θ₀ := θ₀) t
  have hA := (C.hasFDerivAt_dualPotential (C.flowMean_mem hm hθ₀ ht)).comp_hasDerivAt t hη
  have hθ := C.hasDerivAt_flow hm hθ₀ ht
  have hpair := (hη.const_sub m).clm_apply hθ
  have h := (hA.const_sub (C.dualPotential m)).sub hpair
  have hres : C.residual m (C.flow m θ₀ t) = m - C.flowMean m θ₀ t := by
    rw [residual, C.μ_flow hm hθ₀ ht]
  have heq : -(ContinuousLinearMap.apply ℝ ℝ (C.inv (C.flowMean m θ₀ t))
        (m - C.flowMean m θ₀ t)) -
      ((-(m - C.flowMean m θ₀ t)) (C.flow m θ₀ t) +
        (m - C.flowMean m θ₀ t) (C.promote m (C.flow m θ₀ t))) =
      -C.power m (C.flow m θ₀ t) := by
    rw [power, hres, ContinuousLinearMap.apply_apply, neg_apply]
    change -((m - C.flowMean m θ₀ t) (C.flow m θ₀ t)) -
      (-((m - C.flowMean m θ₀ t) (C.flow m θ₀ t)) +
        (m - C.flowMean m θ₀ t) (C.promote m (C.flow m θ₀ t))) = _
    ring
  rw [heq] at h
  exact h

/-- The promoted intervention is continuous along the flow. -/
theorem continuousAt_promote_flow {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun s => C.promote m (C.flow m θ₀ s)) t := by
  have hθU := C.flow_mem hm hθ₀ ht
  have hflow := (C.hasDerivAt_flow hm hθ₀ ht).continuousAt
  have hH : ContinuousAt (fun s => C.H (C.flow m θ₀ s)) t :=
    (C.hasFDerivAt_H _ hθU).continuousAt.comp hflow
  have hinv : ContinuousAt (fun s => (C.H (C.flow m θ₀ s)).inverse) t :=
    ContinuousAt.comp (f := fun s => C.H (C.flow m θ₀ s))
      ((C.H_isInvertible hθU).contDiffAt_map_inverse (n := 0)).continuousAt hH
  have hres : ContinuousAt (fun s => C.residual m (C.flow m θ₀ s)) t :=
    continuousAt_const.sub ((C.hasFDerivAt_μ _ hθU).continuousAt.comp hflow)
  exact hinv.clm_apply hres

theorem continuousAt_power_flow {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun s => C.power m (C.flow m θ₀ s)) t := by
  have hθU := C.flow_mem hm hθ₀ ht
  have hflow := (C.hasDerivAt_flow hm hθ₀ ht).continuousAt
  have hres : ContinuousAt (fun s => C.residual m (C.flow m θ₀ s)) t :=
    continuousAt_const.sub ((C.hasFDerivAt_μ _ hθU).continuousAt.comp hflow)
  exact hres.clm_apply (C.continuousAt_promote_flow hm hθ₀ ht)

/-- **Theorem 5.1, `(LRT.22)`**: `W(μ(θ₀)) - W(μ(θ(T))) = ∫₀ᵀ P`. -/
theorem work_sub_eq_integral {T : ℝ} (hT : 0 ≤ T) :
    C.work m (C.μ θ₀) - C.work m (C.μ (C.flow m θ₀ T)) =
      ∫ t in (0 : ℝ)..T, C.power m (C.flow m θ₀ t) := by
  have hderiv : ∀ x ∈ uIcc 0 T, HasDerivAt (fun s => -C.work m (C.flowMean m θ₀ s))
      (C.power m (C.flow m θ₀ x)) x := fun x hx => by
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le hT] at hx
      exact hx.1
    have := (C.hasDerivAt_work_flow hm hθ₀ hx0).neg
    rwa [neg_neg] at this
  have hint : IntervalIntegrable (fun t => C.power m (C.flow m θ₀ t)) volume 0 T := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le hT] at hx
      exact hx.1
    exact (C.continuousAt_power_flow hm hθ₀ hx0).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, C.μ_flow hm hθ₀ hT]
  simp only [flowMean, neg_zero, Real.exp_zero, one_smul, add_sub_cancel]
  ring

omit hθ₀ in
theorem tendsto_work_flow :
    Tendsto (fun t => C.work m (C.flowMean m θ₀ t)) atTop (𝓝 0) := by
  have hmean : Tendsto (C.flowMean m θ₀) atTop (𝓝 m) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.smul_const (C.μ θ₀ - m)).const_add m
    rw [zero_smul, add_zero] at h
    exact h
  have hcont : ContinuousAt (C.work m) m := by
    have hinv := C.continuousOn_inv.continuousAt (C.isOpen_M.mem_nhds hm)
    have hA := (C.hasFDerivAt_dualPotential hm).continuousAt
    exact (continuousAt_const.sub hA).sub ((continuousAt_const.sub continuousAt_id).clm_apply hinv)
  have h := hcont.tendsto.comp hmean
  rwa [C.work_self] at h

/-- **Theorem 5.1, `(LRT.23)`**: `W(μ(θ₀)) = ∫₀^∞ P`. -/
theorem work_eq_integral_Ioi :
    C.work m (C.μ θ₀) = ∫ t in Ioi (0 : ℝ), C.power m (C.flow m θ₀ t) := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun s => -C.work m (C.flowMean m θ₀ s))
      (C.power m (C.flow m θ₀ x)) x := fun x hx => by
    have := (C.hasDerivAt_work_flow hm hθ₀ (le_of_lt hx)).neg
    rwa [neg_neg] at this
  have hcont : ContinuousWithinAt (fun s => -C.work m (C.flowMean m θ₀ s)) (Ici 0) 0 := by
    have := (C.hasDerivAt_work_flow hm hθ₀ le_rfl).continuousAt.neg
    exact this.continuousWithinAt
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ C.power m (C.flow m θ₀ x) := fun x hx =>
    (C.power_nonneg_and_eq_zero_iff m hm (C.flow_mem hm hθ₀ (le_of_lt hx))).1
  have hlim : Tendsto (fun s => -C.work m (C.flowMean m θ₀ s)) atTop (𝓝 0) := by
    have := (C.tendsto_work_flow (θ₀ := θ₀) hm).neg
    rwa [neg_zero] at this
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]
  simp only [flowMean, neg_zero, Real.exp_zero, one_smul, add_sub_cancel, zero_sub, neg_neg]

/-- **Corollary 5.2**: `θ_*` is the unique zero-work state. -/
theorem work_eq_zero_iff : C.work m (C.μ θ₀) = 0 ↔ θ₀ = C.target m := by
  constructor
  · intro h0
    by_contra hne
    have hres0 : C.residual m θ₀ ≠ 0 := fun h => hne (by
      rw [residual, sub_eq_zero] at h
      rw [target, h, C.inv_μ θ₀ hθ₀])
    have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < C.power m (C.flow m θ₀ t) := fun t ht => by
      have hU := C.flow_mem hm hθ₀ (le_of_lt ht)
      obtain ⟨hnn, hiff⟩ := C.power_nonneg_and_eq_zero_iff m hm hU
      refine lt_of_le_of_ne hnn fun h => ?_
      have hst := hiff.1 h.symm
      have hres := C.residual_flow hm hθ₀ (le_of_lt ht)
      rw [hst, residual, target, C.μ_inv m hm, sub_self] at hres
      exact hres0 ((smul_eq_zero.1 hres.symm).resolve_left (Real.exp_pos _).ne')
    have hint : IntegrableOn (fun t => C.power m (C.flow m θ₀ t)) (Ioi 0) := by
      refine integrableOn_Ioi_deriv_of_nonneg
        (g := fun s => -C.work m (C.flowMean m θ₀ s)) ?_ (fun x hx => ?_) (fun x hx =>
    (hpos x hx).le)
        (by have := (C.tendsto_work_flow (θ₀ := θ₀) hm).neg; rwa [neg_zero] at this)
      · exact (C.hasDerivAt_work_flow hm hθ₀ le_rfl).continuousAt.neg.continuousWithinAt
      · have := (C.hasDerivAt_work_flow hm hθ₀ (le_of_lt hx)).neg
        rwa [neg_neg] at this
    have hgt : 0 < ∫ t in Ioi (0 : ℝ), C.power m (C.flow m θ₀ t) := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => (hpos x hx).le))
        hint]
      have hsub : Ioi (0 : ℝ) ⊆ Function.support fun t => C.power m (C.flow m θ₀ t) :=
        fun t ht => (hpos t ht).ne'
      calc (0 : ENNReal) < volume (Ioi (0 : ℝ)) := by simp
        _ = volume (Function.support (fun t => C.power m (C.flow m θ₀ t)) ∩ Ioi 0) := by
            rw [inter_eq_right.2 hsub]
    rw [← C.work_eq_integral_Ioi hm hθ₀, h0] at hgt
    exact lt_irrefl 0 hgt
  · intro h
    rw [h, target, C.μ_inv m hm, C.work_self]

/-- **Corollary 5.2**: `θ_*` is the unique stationary point and the global limit of every
trajectory. -/
theorem unique_selection :
    (C.promote m θ₀ = 0 ↔ θ₀ = C.target m) ∧ (C.work m (C.μ θ₀) = 0 ↔ θ₀ = C.target m) ∧
      Tendsto (C.flow m θ₀) atTop (𝓝 (C.target m)) :=
  ⟨C.promote_eq_zero_iff m hm hθ₀, C.work_eq_zero_iff hm hθ₀, C.tendsto_flow (θ₀ := θ₀) hm⟩

/-! ### Theorem 7.1: the cubic response controls the power decay -/

omit [FiniteDimensional ℝ Θ] in
theorem eventually_flowMean_mem {t : ℝ} (ht : 0 ≤ t) : ∀ᶠ s in 𝓝 t, C.flowMean m θ₀ s ∈ C.M :=
  (C.hasDerivAt_flowMean (m := m) (θ₀ := θ₀) t).continuousAt.preimage_mem_nhds
    (C.isOpen_M.mem_nhds (C.flowMean_mem hm hθ₀ ht))

omit [FiniteDimensional ℝ Θ] hm in
theorem flow_zero : C.flow m θ₀ 0 = θ₀ := by
  rw [flow, flowMean, neg_zero, Real.exp_zero, one_smul, add_sub_cancel, C.inv_μ θ₀ hθ₀]

/-- **Theorem 7.1, `(LRT.39)`, `(LRT.41)`–`(LRT.43)`**: `P' = -2P - T(v, v, v)` along the flow. -/
theorem hasDerivAt_power_flow {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => C.power m (C.flow m θ₀ s))
      (-2 * C.power m (C.flow m θ₀ t) -
        C.T (C.flow m θ₀ t) (C.promote m (C.flow m θ₀ t)) (C.promote m (C.flow m θ₀ t))
          (C.promote m (C.flow m θ₀ t))) t := by
  have hθU := C.flow_mem hm hθ₀ ht
  have hflow := C.hasDerivAt_flow hm hθ₀ ht
  have hH := HasFDerivAt.comp_hasDerivAt (l := C.H) (l' := C.T (C.flow m θ₀ t)) t
    (C.hasFDerivAt_H _ hθU) hflow
  have hres : HasDerivAt (fun s => C.residual m (C.flow m θ₀ s))
      (-C.residual m (C.flow m θ₀ t)) t := by
    have h := ((C.hasFDerivAt_μ _ hθU).comp_hasDerivAt t hflow).const_sub m
    rw [C.H_promote m hθU] at h
    exact h
  have hinv : HasDerivAt (fun s => (C.H (C.flow m θ₀ s)).inverse)
      (deriv (fun s => (C.H (C.flow m θ₀ s)).inverse) t) t := by
    have hdi := (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (𝕜 := ℝ) (n := 1)
      (C.H_isInvertible hθU)).differentiableAt one_ne_zero
    have hdiff := hdi.comp t hH.differentiableAt
    exact hdiff.hasDerivAt
  have hv : HasDerivAt (fun s => C.promote m (C.flow m θ₀ s))
      (deriv (fun s => C.promote m (C.flow m θ₀ s)) t) t :=
    (hinv.clm_apply hres).differentiableAt.hasDerivAt
  have hident : (fun s => C.H (C.flow m θ₀ s) (C.promote m (C.flow m θ₀ s))) =ᶠ[𝓝 t]
      fun s => C.residual m (C.flow m θ₀ s) := by
    filter_upwards [C.eventually_flowMean_mem hm hθ₀ ht] with s hs
    exact C.H_promote m (C.mapsTo_inv hs)
  have hLHS := hH.clm_apply hv
  have hderivEq : C.T (C.flow m θ₀ t) (C.promote m (C.flow m θ₀ t))
      (C.promote m (C.flow m θ₀ t)) +
      C.H (C.flow m θ₀ t) (deriv (fun s => C.promote m (C.flow m θ₀ s)) t) =
      -C.residual m (C.flow m θ₀ t) :=
    hLHS.unique (hres.congr_of_eventuallyEq hident)
  have hP := hres.clm_apply hv
  have hkey : C.residual m (C.flow m θ₀ t) (deriv (fun s => C.promote m (C.flow m θ₀ s)) t) =
      -C.residual m (C.flow m θ₀ t) (C.promote m (C.flow m θ₀ t)) - C.T (C.flow m θ₀ t) (C.promote m
    (C.flow m θ₀ t)) (C.promote m (C.flow m θ₀ t)) (C.promote m (C.flow m θ₀ t)) := by
    rw [← C.H_promote m hθU, C.H_symm hθU]
    have h1 := congrArg (fun φ : Θ →L[ℝ] ℝ => φ (C.promote m (C.flow m θ₀ t))) hderivEq
    simp only [add_apply, neg_apply] at h1
    rw [← C.H_promote m hθU] at h1
    linarith
  have heq : (-C.residual m (C.flow m θ₀ t)) (C.promote m (C.flow m θ₀ t)) +
      C.residual m (C.flow m θ₀ t) (deriv (fun s => C.promote m (C.flow m θ₀ s)) t) =
      -2 * C.power m (C.flow m θ₀ t) - C.T (C.flow m θ₀ t) (C.promote m (C.flow m θ₀ t))
        (C.promote m (C.flow m θ₀ t)) (C.promote m (C.flow m θ₀ t)) := by
    rw [hkey, neg_apply, power]
    ring
  rw [heq] at hP
  exact hP

/-- **Theorem 7.1, `(LRT.40)`**: `(e^{2t} P)' = -e^{2t} T(v, v, v)`. -/
theorem hasDerivAt_scaled_power {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => Real.exp (2 * s) * C.power m (C.flow m θ₀ s))
      (-(Real.exp (2 * t) *
        C.T (C.flow m θ₀ t) (C.promote m (C.flow m θ₀ t)) (C.promote m (C.flow m θ₀ t))
          (C.promote m (C.flow m θ₀ t)))) t := by
  have hexp : HasDerivAt (fun s => Real.exp (2 * s)) (Real.exp (2 * t) * 2) t := by
    have h := ((hasDerivAt_id t).const_mul (2 : ℝ)).exp
    simp only [id, mul_one] at h
    exact h
  have h := hexp.mul (C.hasDerivAt_power_flow hm hθ₀ ht)
  have heq : Real.exp (2 * t) * 2 * C.power m (C.flow m θ₀ t) + Real.exp (2 * t) *
      (-2 * C.power m (C.flow m θ₀ t) - C.T (C.flow m θ₀ t) (C.promote m (C.flow m θ₀ t))
        (C.promote m (C.flow m θ₀ t)) (C.promote m (C.flow m θ₀ t))) =
      -(Real.exp (2 * t) * C.T (C.flow m θ₀ t) (C.promote m (C.flow m θ₀ t))
        (C.promote m (C.flow m θ₀ t)) (C.promote m (C.flow m θ₀ t))) := by ring
  rw [heq] at h
  exact h

/-- **Theorem 7.1, consequence 1**: for a quadratic potential (`T = 0`), `P(t) = e^{-2t} P(0)`. -/
theorem power_flow_of_T_eq_zero (hT : ∀ θ ∈ C.U, C.T θ = 0) {t : ℝ} (ht : 0 ≤ t) :
    C.power m (C.flow m θ₀ t) = Real.exp (-2 * t) * C.power m θ₀ := by
  set g : ℝ → ℝ := fun s => Real.exp (2 * s) * C.power m (C.flow m θ₀ s)
  have hderiv : ∀ s, 0 ≤ s → HasDerivAt g 0 s := fun s hs => by
    have h := C.hasDerivAt_scaled_power hm hθ₀ hs
    rw [hT _ (C.flow_mem hm hθ₀ hs)] at h
    simpa using h
  have hconst := constant_of_has_deriv_right_zero (f := g) (a := 0) (b := t)
    (fun s hs => (hderiv s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hderiv s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  simp only [g, mul_zero, Real.exp_zero, one_mul, C.flow_zero (m := m) hθ₀] at hconst
  rw [← hconst, ← mul_assoc, ← Real.exp_add, show -2 * t + 2 * t = 0 by ring, Real.exp_zero,
    one_mul]

/-- **Theorem 7.1, consequences 2–3**: a signed cubic response makes `e^{2t} P` monotone. -/
theorem scaled_power_monotone :
    ((∀ t, 0 ≤ t → 0 ≤ C.T (C.flow m θ₀ t) (C.promote m (C.flow m θ₀ t))
        (C.promote m (C.flow m θ₀ t)) (C.promote m (C.flow m θ₀ t))) →
      AntitoneOn (fun s => Real.exp (2 * s) * C.power m (C.flow m θ₀ s)) (Ici 0)) ∧
    ((∀ t, 0 ≤ t → C.T (C.flow m θ₀ t) (C.promote m (C.flow m θ₀ t))
        (C.promote m (C.flow m θ₀ t)) (C.promote m (C.flow m θ₀ t)) ≤ 0) →
      MonotoneOn (fun s => Real.exp (2 * s) * C.power m (C.flow m θ₀ s)) (Ici 0)) := by
  have hcont : ContinuousOn (fun s => Real.exp (2 * s) * C.power m (C.flow m θ₀ s)) (Ici 0) :=
    fun s hs => (C.hasDerivAt_scaled_power hm hθ₀ hs).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => Real.exp (2 * s) * C.power m (C.flow m θ₀ s))
      (interior (Ici 0)) := fun s hs => by
    rw [interior_Ici] at hs
    exact (C.hasDerivAt_scaled_power hm hθ₀ (le_of_lt hs)).differentiableAt.differentiableWithinAt
  refine ⟨fun hpos => antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont hdiff fun s hs => ?_,
    fun hneg => monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff fun s hs => ?_⟩
  · rw [interior_Ici] at hs
    rw [(C.hasDerivAt_scaled_power hm hθ₀ (le_of_lt hs)).deriv]
    have := hpos s (le_of_lt hs)
    have := Real.exp_pos (2 * s)
    nlinarith
  · rw [interior_Ici] at hs
    rw [(C.hasDerivAt_scaled_power hm hθ₀ (le_of_lt hs)).deriv]
    have := hneg s (le_of_lt hs)
    have := Real.exp_pos (2 * s)
    nlinarith

/-! ### Theorem 9.1: finite Legendre properness -/

omit hθ₀ hm [FiniteDimensional ℝ Θ] in
/-- **Theorem 9.1**: compact dual-work sublevels in `M` give compact bounded-work sets in `U`. -/
theorem isCompact_work_sublevel (hW : ∀ R : ℝ, IsCompact {η | η ∈ C.M ∧ C.work m η ≤ R})
    (R : ℝ) : IsCompact {θ | θ ∈ C.U ∧ C.work m (C.μ θ) ≤ R} := by
  have himage : {θ | θ ∈ C.U ∧ C.work m (C.μ θ) ≤ R} =
      C.inv '' {η | η ∈ C.M ∧ C.work m η ≤ R} := by
    ext θ
    constructor
    · rintro ⟨hθ, hR⟩
      exact ⟨C.μ θ, ⟨C.μ_mem hθ, hR⟩, C.inv_μ θ hθ⟩
    · rintro ⟨η, ⟨hη, hR⟩, rfl⟩
      exact ⟨C.mapsTo_inv hη, by rwa [C.μ_inv η hη]⟩
  rw [himage]
  exact (hW R).image_of_continuousOn (C.continuousOn_inv.mono fun η hη => hη.1)

/-- **Theorem 9.1**: work is nonincreasing, so every trajectory stays in one compact bounded-work
set, and `θ_*` is the unique attainable zero-work state. -/
theorem trajectory_compact (hW : ∀ R : ℝ, IsCompact {η | η ∈ C.M ∧ C.work m η ≤ R}) :
    IsCompact {θ | θ ∈ C.U ∧ C.work m (C.μ θ) ≤ C.work m (C.μ θ₀)} ∧
      (∀ t, 0 ≤ t → C.flow m θ₀ t ∈ {θ | θ ∈ C.U ∧ C.work m (C.μ θ) ≤ C.work m (C.μ θ₀)}) ∧
      ∀ θ ∈ C.U, C.work m (C.μ θ) = 0 → θ = C.target m := by
  refine ⟨C.isCompact_work_sublevel hW _, fun t ht => ⟨C.flow_mem hm hθ₀ ht, ?_⟩,
    fun θ hθ h0 => (C.work_eq_zero_iff hm hθ).1 h0⟩
  have h := C.work_sub_eq_integral hm hθ₀ ht
  have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, C.power m (C.flow m θ₀ s) :=
    intervalIntegral.integral_nonneg ht fun s hs =>
      (C.power_nonneg_and_eq_zero_iff m hm (C.flow_mem hm hθ₀ hs.1)).1
  linarith

end LegendreChart

end GaloisForLFunctions.HTGeometry.ResidualTransduction
