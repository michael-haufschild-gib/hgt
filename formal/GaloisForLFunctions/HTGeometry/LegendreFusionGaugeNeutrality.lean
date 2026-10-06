import GaloisForLFunctions.HTGeometry.LegendreResidualTransduction

/-!
# Shared-channel fusion, gauge neutrality and the cofinal boundary

* **Theorem 6.1.**  For channels `A_i` with positive-semidefinite Hessians `H_i` whose sum `H` is
  positive definite, along the fused flow `θ' = v = H⁻¹ e`, `e = Σ_i e_i`, `e_i = m_i - μ_i`, the
  local residuals obey `e_i' = -j_i` with currents `j_i = H_i v`, `Σ_i j_i = e`, `e' = -e`, and the
  power splits without cancellation, `e(v) = Σ_i H_i(v, v)` with every term nonnegative; the fused
  intervention is not the sum of local interventions.
* **Theorem 8.1.**  A linear reparametrization `g : W ≃ Θ` pulls the chart back to a chart on `W`
  with `μ̃ = g*μ g`, `H̃ = g* H g`, `ẽ = g* e`, `X̃ = g⁻¹ X`; trajectories correspond and residuals,
  power and work are preserved.  An affine gauge `A + ℓ + c` with target `m + ℓ` changes none of
  `H, e, X, P, W`.  **Corollary 8.2**: a reparametrization followed by an affine gauge is
  information- and work-neutral.
* **§9, cofinal warning.**  For `A_N(x) = x²/(2N)`, `m = 1`, `θ₀ = 0`, every reporter trajectory is
  `1 - e^{-t}`, yet the initial intervention is `N` and the source endpoint `θ_*^{(N)} = N` escapes.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ResidualTransduction

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ]

/-- A positive-definite bilinear form `Θ → Θ*` is invertible. -/
theorem isInvertible_of_posDef (B : Θ →L[ℝ] Θ →L[ℝ] ℝ) (hB : ∀ v, v ≠ 0 → 0 < B v v) :
    B.IsInvertible := by
  have hinj : Function.Injective (B : Θ →ₗ[ℝ] Θ →L[ℝ] ℝ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra h
    have := hB v h
    have hv' : B v = 0 := hv
    rw [hv', zero_apply] at this
    exact lt_irrefl 0 this
  let e := (LinearEquiv.ofBijective (B : Θ →ₗ[ℝ] Θ →L[ℝ] ℝ)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (LegendreChart.finrank_dual (Θ := Θ)).symm).1 hinj⟩).toContinuousLinearEquiv
  exact ⟨e, by ext v; rfl⟩

/-! ### Theorem 6.1: shared-channel fusion -/

/-- A family of source channels with positive-semidefinite Hessians summing to a positive-definite
total Hessian. -/
structure ChannelFamily (I Θ : Type*) [Fintype I] [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] where
  /-- the open source domain -/
  U : Set Θ
  isOpen_U : IsOpen U
  /-- the channel potentials -/
  A : I → Θ → ℝ
  /-- the channel reporters -/
  μ : I → Θ → Θ →L[ℝ] ℝ
  /-- the channel Hessians -/
  H : I → Θ → Θ →L[ℝ] Θ →L[ℝ] ℝ
  hasFDerivAt_A : ∀ i, ∀ θ ∈ U, HasFDerivAt (A i) (μ i θ) θ
  hasFDerivAt_μ : ∀ i, ∀ θ ∈ U, HasFDerivAt (μ i) (H i θ) θ
  psd : ∀ i, ∀ θ ∈ U, ∀ v, 0 ≤ H i θ v v
  posDef_sum : ∀ θ ∈ U, ∀ v, v ≠ 0 → 0 < ∑ i, H i θ v v

namespace ChannelFamily

variable {I : Type*} [Fintype I] (F : ChannelFamily I Θ) (m : I → Θ →L[ℝ] ℝ)

/-- `(LRT.27)` the total Hessian `H = Σ_i H_i`. -/
def totalH (θ : Θ) : Θ →L[ℝ] Θ →L[ℝ] ℝ := ∑ i, F.H i θ

/-- `(LRT.29)` the local residuals `e_i = m_i - μ_i`. -/
def localResidual (i : I) (θ : Θ) : Θ →L[ℝ] ℝ := m i - F.μ i θ

/-- `(LRT.29)` the fused residual `e = Σ_i e_i`. -/
def fusedResidual (θ : Θ) : Θ →L[ℝ] ℝ := ∑ i, F.localResidual m i θ

/-- `(LRT.29)` the fused intervention `v = H⁻¹ e`. -/
def fusedIntervention (θ : Θ) : Θ := (F.totalH θ).inverse (F.fusedResidual m θ)

/-- `(LRT.29)` the channel currents `j_i = H_i v`. -/
def current (i : I) (θ : Θ) : Θ →L[ℝ] ℝ := F.H i θ (F.fusedIntervention m θ)

theorem totalH_isInvertible {θ : Θ} (hθ : θ ∈ F.U) : (F.totalH θ).IsInvertible :=
  isInvertible_of_posDef _ fun v hv => by
    simpa [totalH] using F.posDef_sum θ hθ v hv

/-- **`(LRT.30)`, `(LRT.34)`**: the currents sum to the fused residual, `Σ_i j_i = e`. -/
theorem sum_current {θ : Θ} (hθ : θ ∈ F.U) : ∑ i, F.current m i θ = F.fusedResidual m θ := by
  have h := (F.totalH_isInvertible hθ).self_apply_inverse (F.fusedResidual m θ)
  rw [← h]
  simp [current, fusedIntervention, totalH]

/-- **`(LRT.31)`, `(LRT.35)`**: the power splits without cancellation,
`e(v) = H(v, v) = Σ_i H_i(v, v)` with every term nonnegative. -/
theorem power_split {θ : Θ} (hθ : θ ∈ F.U) :
    F.fusedResidual m θ (F.fusedIntervention m θ) =
        F.totalH θ (F.fusedIntervention m θ) (F.fusedIntervention m θ) ∧
      F.totalH θ (F.fusedIntervention m θ) (F.fusedIntervention m θ) =
        ∑ i, F.H i θ (F.fusedIntervention m θ) (F.fusedIntervention m θ) ∧
      ∀ i, 0 ≤ F.H i θ (F.fusedIntervention m θ) (F.fusedIntervention m θ) := by
  refine ⟨?_, by simp [totalH], fun i => F.psd i θ hθ _⟩
  rw [fusedIntervention, (F.totalH_isInvertible hθ).self_apply_inverse]

/-- **Theorem 6.1, `(LRT.30)`, `(LRT.33)`**: along any fused flow `θ' = v`, the local residuals
obey `e_i' = -j_i` and the fused residual obeys `e' = -e`. -/
theorem fused_flow_currents (γ : ℝ → Θ) {t : ℝ} (hγU : γ t ∈ F.U)
    (hγ : HasDerivAt γ (F.fusedIntervention m (γ t)) t) :
    (∀ i, HasDerivAt (fun s => F.localResidual m i (γ s)) (-F.current m i (γ t)) t) ∧
      HasDerivAt (fun s => F.fusedResidual m (γ s)) (-F.fusedResidual m (γ t)) t := by
  have hloc : ∀ i, HasDerivAt (fun s => F.localResidual m i (γ s)) (-F.current m i (γ t)) t :=
    fun i => by
      have h := ((F.hasFDerivAt_μ i _ hγU).comp_hasDerivAt t hγ).const_sub (m i)
      exact h
  refine ⟨hloc, ?_⟩
  have h := HasDerivAt.sum (u := Finset.univ) fun i _ => hloc i
  rw [Finset.sum_neg_distrib, F.sum_current m hγU] at h
  have hfun : (fun s => F.fusedResidual m (γ s)) = ∑ i, fun s => F.localResidual m i (γ s) := by
    funext s
    simp [fusedResidual, Finset.sum_apply]
  rw [hfun]
  exact h

/-- **`(LRT.32)`**: the fused intervention is not the sum of local interventions: two scalar
channels with `H₁ = H₂ = 1` and `e₁ = e₂ = 1` give `H⁻¹(e₁ + e₂) = 1 ≠ 2 = H₁⁻¹e₁ + H₂⁻¹e₂`. -/
theorem fusion_nonproduct :
    (ContinuousLinearMap.mul ℝ ℝ + ContinuousLinearMap.mul ℝ ℝ).inverse
        (ContinuousLinearMap.id ℝ ℝ + ContinuousLinearMap.id ℝ ℝ) ≠
      (ContinuousLinearMap.mul ℝ ℝ).inverse (ContinuousLinearMap.id ℝ ℝ) +
        (ContinuousLinearMap.mul ℝ ℝ).inverse (ContinuousLinearMap.id ℝ ℝ) := by
  have h1 : (ContinuousLinearMap.mul ℝ ℝ).IsInvertible :=
    isInvertible_of_posDef _ fun v hv => by simpa [mul_self_pos] using hv
  have h2 : (ContinuousLinearMap.mul ℝ ℝ + ContinuousLinearMap.mul ℝ ℝ).IsInvertible :=
    isInvertible_of_posDef _ fun v hv => by
      simp only [add_apply, ContinuousLinearMap.mul_apply']
      have := mul_self_pos.2 hv
      linarith
  have hone : (ContinuousLinearMap.mul ℝ ℝ).inverse (ContinuousLinearMap.id ℝ ℝ) = 1 :=
    (h1.inverse_apply_eq).2 (by ext; simp)
  have hfused : (ContinuousLinearMap.mul ℝ ℝ + ContinuousLinearMap.mul ℝ ℝ).inverse
      (ContinuousLinearMap.id ℝ ℝ + ContinuousLinearMap.id ℝ ℝ) = 1 :=
    (h2.inverse_apply_eq).2 (by ext; simp)
  rw [hone, hfused]
  norm_num

/-- **Corollary 6.2**: for three channels, the current triangle `j₁ + j₂ + j₃ = e` and the positive
power identity `e(v) = H₁(v,v) + H₂(v,v) + H₃(v,v)` hold exactly. -/
theorem three_channel (F : ChannelFamily (Fin 3) Θ) (m : Fin 3 → Θ →L[ℝ] ℝ) {θ : Θ}
    (hθ : θ ∈ F.U) :
    F.current m 0 θ + F.current m 1 θ + F.current m 2 θ = F.fusedResidual m θ ∧
      F.fusedResidual m θ (F.fusedIntervention m θ) =
        F.H 0 θ (F.fusedIntervention m θ) (F.fusedIntervention m θ) +
          F.H 1 θ (F.fusedIntervention m θ) (F.fusedIntervention m θ) +
          F.H 2 θ (F.fusedIntervention m θ) (F.fusedIntervention m θ) := by
  obtain ⟨h1, h2, -⟩ := F.power_split m hθ
  refine ⟨by rw [← F.sum_current m hθ, Fin.sum_univ_three], ?_⟩
  rw [h1, h2, Fin.sum_univ_three]

end ChannelFamily

/-- The fused flow of a channel family is the residual-transduction flow of the summed chart: if a
Legendre chart has reporter `Σ_i μ_i` and Hessian `Σ_i H_i`, its flow toward `Σ_i m_i` satisfies
`θ' = v`, so Theorem 6.1 applies to it. -/
theorem fusedFlow_of_chart {I : Type*} [Fintype I] (F : ChannelFamily I Θ)
    (C : LegendreChart Θ) (hμ : ∀ θ, C.μ θ = ∑ i, F.μ i θ)
    (hH : ∀ θ, C.H θ = F.totalH θ) (m : I → Θ →L[ℝ] ℝ) (hm : ∑ i, m i ∈ C.M) {θ₀ : Θ}
    (hθ₀ : θ₀ ∈ C.U) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (C.flow (∑ i, m i) θ₀) (F.fusedIntervention m (C.flow (∑ i, m i) θ₀ t)) t := by
  have h := C.hasDerivAt_flow hm hθ₀ ht
  have heq : C.promote (∑ i, m i) (C.flow (∑ i, m i) θ₀ t) =
      F.fusedIntervention m (C.flow (∑ i, m i) θ₀ t) := by
    simp only [LegendreChart.promote, LegendreChart.residual, ChannelFamily.fusedIntervention,
      ChannelFamily.fusedResidual, ChannelFamily.localResidual, hH, hμ, Finset.sum_sub_distrib]
  rw [heq] at h
  exact h

/-! ### Theorem 8.1: coordinate neutrality -/

section Pullback

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Pullback of covectors `φ ↦ φ ∘ g` (`g*`). -/
def covectorPullback (g : W ≃L[ℝ] Θ) : (Θ →L[ℝ] ℝ) ≃L[ℝ] (W →L[ℝ] ℝ) :=
  g.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

omit [FiniteDimensional ℝ Θ] in
theorem covectorPullback_apply (g : W ≃L[ℝ] Θ) (φ : Θ →L[ℝ] ℝ) (w : W) :
    covectorPullback g φ w = φ (g w) := by
  simp [covectorPullback, ContinuousLinearEquiv.arrowCongr_apply]

/-- Pullback of bilinear forms `B ↦ g* B g`. -/
def bilinearPullback (g : W ≃L[ℝ] Θ) : (Θ →L[ℝ] Θ →L[ℝ] ℝ) ≃L[ℝ] (W →L[ℝ] W →L[ℝ] ℝ) :=
  g.symm.arrowCongr (covectorPullback g)

omit [FiniteDimensional ℝ Θ] in
theorem bilinearPullback_apply (g : W ≃L[ℝ] Θ) (B : Θ →L[ℝ] Θ →L[ℝ] ℝ) (a b : W) :
    bilinearPullback g B a b = B (g a) (g b) := by
  simp [bilinearPullback, ContinuousLinearEquiv.arrowCongr_apply, covectorPullback_apply]

namespace LegendreChart

variable (C : LegendreChart Θ)

/-- **`(LRT.44)`–`(LRT.45)`** the chart pulled back by a linear isomorphism `g : W ≃ Θ`:
`Ã = A ∘ g`, `μ̃ = g* μ g`, `H̃ = g* H g`, `ν̃ = g⁻¹ ν (g*)⁻¹`. -/
def pullback (g : W ≃L[ℝ] Θ) : LegendreChart W where
  U := g ⁻¹' C.U
  isOpen_U := C.isOpen_U.preimage g.continuous
  convex_U := C.convex_U.linear_preimage (g : W →L[ℝ] Θ).toLinearMap
  A w := C.A (g w)
  μ w := covectorPullback g (C.μ (g w))
  H w := bilinearPullback g (C.H (g w))
  T w := (bilinearPullback g : (Θ →L[ℝ] Θ →L[ℝ] ℝ) →L[ℝ] (W →L[ℝ] W →L[ℝ] ℝ)).comp
    ((C.T (g w)).comp (g : W →L[ℝ] Θ))
  hasFDerivAt_A w hw := by
    have h := (C.hasFDerivAt_A _ hw).comp w g.hasFDerivAt
    refine h.congr_fderiv (ContinuousLinearMap.ext fun a => ?_)
    simp [covectorPullback_apply]
  hasFDerivAt_μ w hw := by
    have h := (covectorPullback g : (Θ →L[ℝ] ℝ) →L[ℝ] (W →L[ℝ] ℝ)).hasFDerivAt.comp w
      ((C.hasFDerivAt_μ _ hw).comp w g.hasFDerivAt)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_)
    simp [bilinearPullback_apply, covectorPullback_apply]
  hasFDerivAt_H w hw := by
    have h1 := HasFDerivAt.comp (𝕜 := ℝ) (F := Θ) (G := Θ →L[ℝ] Θ →L[ℝ] ℝ) (g := C.H)
      (g' := C.T (g w)) (f := g) (f' := (g : W →L[ℝ] Θ)) w (C.hasFDerivAt_H (g w) hw)
      g.hasFDerivAt
    have hL := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Θ →L[ℝ] Θ →L[ℝ] ℝ)
      (F := W →L[ℝ] W →L[ℝ] ℝ)
      (bilinearPullback g : (Θ →L[ℝ] Θ →L[ℝ] ℝ) →L[ℝ] (W →L[ℝ] W →L[ℝ] ℝ)) (x := C.H (g w))
    exact HasFDerivAt.comp (𝕜 := ℝ) (E := W) (F := Θ →L[ℝ] Θ →L[ℝ] ℝ)
      (G := W →L[ℝ] W →L[ℝ] ℝ)
      (g' := (bilinearPullback g : (Θ →L[ℝ] Θ →L[ℝ] ℝ) →L[ℝ] (W →L[ℝ] W →L[ℝ] ℝ)))
      (f := fun w => C.H (g w)) w hL h1
  posDef w hw v hv := by
    rw [bilinearPullback_apply]
    exact C.posDef _ hw _ (by simpa using hv)
  M := covectorPullback g '' C.M
  image_eq := by
    ext ζ
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨C.μ (g w), C.μ_mem hw, rfl⟩
    · rintro ⟨η, hη, rfl⟩
      exact ⟨g.symm (C.inv η), by simpa using C.mapsTo_inv hη, by
        rw [ContinuousLinearEquiv.apply_symm_apply, C.μ_inv η hη]⟩
  isOpen_M := (covectorPullback g).isOpenMap _ C.isOpen_M
  convex_M := by
    have h := C.convex_M.linear_image (covectorPullback g).toLinearEquiv.toLinearMap
    exact h
  inv ζ := g.symm (C.inv ((covectorPullback g).symm ζ))
  mapsTo_inv := by
    rintro _ ⟨η, hη, rfl⟩
    simpa using C.mapsTo_inv hη
  μ_inv := by
    rintro _ ⟨η, hη, rfl⟩
    simp [C.μ_inv η hη]
  inv_μ w hw := by
    simp [C.inv_μ _ hw]
  continuousOn_inv := by
    refine g.symm.continuous.comp_continuousOn (C.continuousOn_inv.comp
      (covectorPullback g).symm.continuous.continuousOn ?_)
    rintro _ ⟨η, hη, rfl⟩
    simpa using hη

variable (g : W ≃L[ℝ] Θ)

omit [FiniteDimensional ℝ Θ] in
/-- **`(LRT.45)`**: `μ̃(w) = g* μ(g w)` and `H̃_w = g* H_{g w} g`. -/
theorem pullback_μ_H (w a b : W) :
    (C.pullback g).μ w a = C.μ (g w) (g a) ∧ (C.pullback g).H w a b = C.H (g w) (g a) (g b) :=
  ⟨covectorPullback_apply g _ a, bilinearPullback_apply g _ a b⟩

omit [FiniteDimensional ℝ Θ] in
/-- **`(LRT.45)`**: `ẽ = g* e`. -/
theorem pullback_residual (m : Θ →L[ℝ] ℝ) (w : W) :
    (C.pullback g).residual (covectorPullback g m) w = covectorPullback g (C.residual m (g w)) := by
  simp [residual, pullback, map_sub]

/-- **`(LRT.45)`, `(LRT.47)`**: `X̃ = g⁻¹ X`. -/
theorem pullback_promote [FiniteDimensional ℝ W] (m : Θ →L[ℝ] ℝ)
    {w : W} (hw : w ∈ (C.pullback g).U) :
    (C.pullback g).promote (covectorPullback g m) w = g.symm (C.promote m (g w)) := by
  have hinv := (C.pullback g).H_isInvertible hw
  rw [promote, hinv.inverse_apply_eq, pullback_residual]
  ext a
  simp only [pullback, bilinearPullback_apply, ContinuousLinearEquiv.apply_symm_apply,
    covectorPullback_apply]
  rw [C.H_promote m hw]

/-- **`(LRT.46)`, `(LRT.48)`**: power is unchanged. -/
theorem pullback_power [FiniteDimensional ℝ W] (m : Θ →L[ℝ] ℝ) {w : W} (hw : w ∈ (C.pullback g).U) :
    (C.pullback g).power (covectorPullback g m) w = C.power m (g w) := by
  rw [power, C.pullback_promote g m hw, C.pullback_residual g m, covectorPullback_apply,
    ContinuousLinearEquiv.apply_symm_apply, power]

omit [FiniteDimensional ℝ Θ] in
/-- **Theorem 8.1**: transformed trajectories correspond, `g w(t) = θ(t)`. -/
theorem pullback_flow (m : Θ →L[ℝ] ℝ) (w₀ : W) (t : ℝ) :
    g ((C.pullback g).flow (covectorPullback g m) w₀ t) = C.flow m (g w₀) t := by
  have hmean : (C.pullback g).flowMean (covectorPullback g m) w₀ t =
      covectorPullback g (C.flowMean m (g w₀) t) := by
    simp [flowMean, pullback, map_add, map_smul, map_sub]
  rw [flow, hmean, flow]
  simp [pullback]

omit [FiniteDimensional ℝ Θ] in
/-- **Theorem 8.1, `(LRT.46)`**: Bregman work is unchanged. -/
theorem pullback_work (m η : Θ →L[ℝ] ℝ) :
    (C.pullback g).work (covectorPullback g m) (covectorPullback g η) = C.work m η := by
  simp [work, dualPotential, pullback, covectorPullback_apply]

/-- **Theorem 8.1, `(LRT.46)`**: along corresponding trajectories `ẽ(t) = g* e(t)`, `W̃(t) = W(t)`,
`P̃(t) = P(t)`. -/
theorem pullback_neutral [FiniteDimensional ℝ W] (m : Θ →L[ℝ] ℝ) (hm : m ∈ C.M)
    (w₀ : W) (hw₀ : g w₀ ∈ C.U) {t : ℝ}
    (ht : 0 ≤ t) :
    (C.pullback g).residual (covectorPullback g m) ((C.pullback g).flow (covectorPullback g m) w₀ t)
        = covectorPullback g (C.residual m (C.flow m (g w₀) t)) ∧
      (C.pullback g).work (covectorPullback g m)
          ((C.pullback g).μ ((C.pullback g).flow (covectorPullback g m) w₀ t)) =
        C.work m (C.μ (C.flow m (g w₀) t)) ∧
      (C.pullback g).power (covectorPullback g m)
          ((C.pullback g).flow (covectorPullback g m) w₀ t) =
        C.power m (C.flow m (g w₀) t) := by
  have hflow := C.pullback_flow g m w₀ t
  have hmem : (C.pullback g).flow (covectorPullback g m) w₀ t ∈ (C.pullback g).U := by
    change g _ ∈ C.U
    rw [hflow]
    exact C.flow_mem hm hw₀ ht
  refine ⟨by rw [pullback_residual, hflow], ?_, by rw [C.pullback_power g m hmem, hflow]⟩
  change (C.pullback g).work (covectorPullback g m)
    (covectorPullback g (C.μ (g ((C.pullback g).flow (covectorPullback g m) w₀ t)))) = _
  rw [pullback_work, hflow]

end LegendreChart

end Pullback

/-! ### Affine gauge neutrality and Corollary 8.2 -/

namespace LegendreChart

variable (C : LegendreChart Θ)

/-- **`(LRT.49)`** the affine gauge `A' = A + ℓ + c`, `μ' = μ + ℓ`, `H' = H`. -/
def gauge (ℓ : Θ →L[ℝ] ℝ) (c : ℝ) : LegendreChart Θ where
  U := C.U
  isOpen_U := C.isOpen_U
  convex_U := C.convex_U
  A θ := C.A θ + ℓ θ + c
  μ θ := C.μ θ + ℓ
  H := C.H
  T := C.T
  hasFDerivAt_A θ hθ := ((C.hasFDerivAt_A θ hθ).add ℓ.hasFDerivAt).add_const c
  hasFDerivAt_μ θ hθ := (C.hasFDerivAt_μ θ hθ).add_const ℓ
  hasFDerivAt_H := C.hasFDerivAt_H
  posDef := C.posDef
  M := (fun η => η - ℓ) ⁻¹' C.M
  image_eq := by
    ext η
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      simpa using C.μ_mem hθ
    · intro hη
      exact ⟨C.inv (η - ℓ), C.mapsTo_inv hη, by rw [C.μ_inv _ hη, sub_add_cancel]⟩
  isOpen_M := C.isOpen_M.preimage (continuous_id.sub continuous_const)
  convex_M := by
    intro x hx y hy a b ha hb hab
    simp only [mem_preimage] at hx hy ⊢
    have h := C.convex_M hx hy ha hb hab
    convert h using 1
    rw [smul_sub, smul_sub]
    nth_rw 1 [← one_smul ℝ ℓ]
    rw [← hab, add_smul]
    abel
  inv η := C.inv (η - ℓ)
  mapsTo_inv _ hη := C.mapsTo_inv hη
  μ_inv η hη := by
    rw [C.μ_inv _ hη, sub_add_cancel]
  inv_μ θ hθ := by
    rw [add_sub_cancel_right, C.inv_μ θ hθ]
  continuousOn_inv := C.continuousOn_inv.comp (continuous_id.sub continuous_const).continuousOn
    fun _ h => h

variable (ℓ : Θ →L[ℝ] ℝ) (c : ℝ) (m : Θ →L[ℝ] ℝ)

omit [FiniteDimensional ℝ Θ] in
/-- **`(LRT.50)`**: `μ' = μ + ℓ`, `H' = H`, `e' = e`, `X' = X`, `P' = P`. -/
theorem gauge_invariants (θ : Θ) :
    (C.gauge ℓ c).μ θ = C.μ θ + ℓ ∧ (C.gauge ℓ c).H θ = C.H θ ∧
      (C.gauge ℓ c).residual (m + ℓ) θ = C.residual m θ ∧
      (C.gauge ℓ c).promote (m + ℓ) θ = C.promote m θ ∧
      (C.gauge ℓ c).power (m + ℓ) θ = C.power m θ := by
  have hres : (C.gauge ℓ c).residual (m + ℓ) θ = C.residual m θ := by
    simp only [residual, gauge]
    abel
  refine ⟨rfl, rfl, hres, ?_, ?_⟩
  · simp only [promote, hres]
    rfl
  · simp only [power, promote, hres]
    rfl

omit [FiniteDimensional ℝ Θ] in
/-- **`(LRT.50)`**: `W' = W` (the target moves with the reporter). -/
theorem gauge_work (η : Θ →L[ℝ] ℝ) :
    (C.gauge ℓ c).work (m + ℓ) (η + ℓ) = C.work m η := by
  simp only [work, dualPotential, gauge, add_sub_cancel_right, add_sub_add_right_eq_sub, add_apply]
  ring

omit [FiniteDimensional ℝ Θ] in
/-- **`(LRT.50)`**: the gauged flow is the original flow. -/
theorem gauge_flow (θ₀ : Θ) (t : ℝ) : (C.gauge ℓ c).flow (m + ℓ) θ₀ t = C.flow m θ₀ t := by
  simp only [flow, flowMean, gauge]
  congr 1
  rw [show C.μ θ₀ + ℓ - (m + ℓ) = C.μ θ₀ - m by abel]
  abel

/-- **Corollary 8.2**: a reparametrization followed by an affine gauge (the action of a functional
equation on the formation potential) preserves power and work and transports trajectories. -/
theorem functional_equation_neutral {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (g : W ≃L[ℝ] Θ) (ℓ' : W →L[ℝ] ℝ) (c : ℝ) (m : Θ →L[ℝ] ℝ)
    (hm : m ∈ C.M) (w₀ : W) (hw₀ : g w₀ ∈ C.U) {t : ℝ} (ht : 0 ≤ t) :
    g (((C.pullback g).gauge ℓ' c).flow (covectorPullback g m + ℓ') w₀ t) = C.flow m (g w₀) t ∧
      ((C.pullback g).gauge ℓ' c).power (covectorPullback g m + ℓ')
          (((C.pullback g).gauge ℓ' c).flow (covectorPullback g m + ℓ') w₀ t) =
        C.power m (C.flow m (g w₀) t) ∧
      ∀ η : Θ →L[ℝ] ℝ, ((C.pullback g).gauge ℓ' c).work (covectorPullback g m + ℓ')
          (covectorPullback g η + ℓ') = C.work m η := by
  refine ⟨?_, ?_, fun η => ?_⟩
  · rw [gauge_flow, pullback_flow]
  · rw [gauge_flow, ((C.pullback g).gauge_invariants ℓ' c _ _).2.2.2.2]
    exact ((C.pullback_neutral g m hm w₀ hw₀ ht).2.2)
  · rw [gauge_work, pullback_work]

end LegendreChart

/-! ### §9: the cofinal escape countermodel -/

/-- The quadratic chart `A_N(x) = x²/(2N)` on `ℝ`, with `μ_N(x) = x/N`, `H_N = 1/N`, `T = 0`. -/
def quadraticChart (N : ℝ) (hN : 0 < N) : LegendreChart ℝ where
  U := univ
  isOpen_U := isOpen_univ
  convex_U := convex_univ
  A x := x ^ 2 / (2 * N)
  μ x := (N⁻¹ • ContinuousLinearMap.mul ℝ ℝ) x
  H _ := N⁻¹ • ContinuousLinearMap.mul ℝ ℝ
  T _ := 0
  hasFDerivAt_A x _ := by
    have h := ((hasDerivAt_pow 2 x).div_const (2 * N)).hasFDerivAt
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, smul_apply,
      ContinuousLinearMap.mul_apply']
    field_simp
    ring
  hasFDerivAt_μ x _ := (N⁻¹ • ContinuousLinearMap.mul ℝ ℝ).hasFDerivAt
  hasFDerivAt_H x _ := hasFDerivAt_const _ x
  posDef x _ v hv := by
    simp only [smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
    have := mul_self_pos.2 hv
    positivity
  M := univ
  image_eq := by
    rw [image_univ, eq_univ_iff_forall]
    intro η
    refine ⟨N * η 1, ?_⟩
    ext
    simp only [smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
    field_simp
  isOpen_M := isOpen_univ
  convex_M := convex_univ
  inv η := N * η 1
  mapsTo_inv _ _ := mem_univ _
  μ_inv η _ := by
    ext
    simp only [smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
    field_simp
  inv_μ x _ := by
    simp only [smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
    field_simp
  continuousOn_inv := (continuous_const.mul
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).continuous).continuousOn

/-- **§9, `(LRT.52)`–`(LRT.53)`**: for `A_N`, target `m = 1` and `θ₀ = 0`: the Hessian is `1/N`, the
initial intervention is `N`, the reporter trajectory `1 - e^{-t}` does not depend on `N`, yet the
source endpoint `θ_*^{(N)} = N` escapes to infinity. -/
theorem quadraticChart_cofinal_escape :
    (∀ N (hN : 0 < N) (x v w : ℝ), (quadraticChart N hN).H x v w = v * w / N) ∧
      (∀ N (hN : 0 < N), (quadraticChart N hN).promote (ContinuousLinearMap.id ℝ ℝ) 0 = N) ∧
      (∀ N (hN : 0 < N) (t : ℝ), (quadraticChart N hN).flowMean (ContinuousLinearMap.id ℝ ℝ) 0 t =
        (1 - Real.exp (-t)) • ContinuousLinearMap.id ℝ ℝ) ∧
      (∀ N (hN : 0 < N), (quadraticChart N hN).target (ContinuousLinearMap.id ℝ ℝ) = N) := by
  refine ⟨fun N hN x v w => ?_, fun N hN => ?_, fun N hN t => ?_, fun N hN => ?_⟩
  · simp only [quadraticChart, smul_apply, ContinuousLinearMap.mul_apply',
      smul_eq_mul]
    field_simp
  · have hinv := (quadraticChart N hN).H_isInvertible (mem_univ (0 : ℝ))
    rw [LegendreChart.promote, hinv.inverse_apply_eq]
    ext
    simp only [LegendreChart.residual, quadraticChart, smul_apply,
      ContinuousLinearMap.mul_apply', smul_eq_mul, sub_apply]
    field_simp
    simp
  · ext
    simp only [LegendreChart.flowMean, quadraticChart, smul_apply, smul_eq_mul]
    simp
    ring
  · simp [LegendreChart.target, quadraticChart]

theorem tendsto_quadraticChart_target :
    Tendsto (fun N : ℝ => N) atTop atTop ∧
      ∀ N (hN : 0 < N), (quadraticChart N hN).target (ContinuousLinearMap.id ℝ ℝ) = N :=
  ⟨tendsto_id, quadraticChart_cofinal_escape.2.2.2⟩

end GaloisForLFunctions.HTGeometry.ResidualTransduction
