import GaloisForLFunctions.HTGeometry.AffineObserverHolonomy

/-!
# The affine observer field equation

For finitely many based holonomies `Hol e` and source currents `c e` on the root fibre, the
**holonomy defect** `D x = (x − Hol e x)_e` has normal operator `Δ_hol = D* D` and source term
`J_src = D* c`.  Every exact global presentation satisfies `Δ_hol x = J_src`, and conversely a
solution of the normal equation is exact exactly when its residual vanishes.

* `holonomyLaplacian_apply_of_exact` and `exact_iff_energy_eq_zero` : the field equation and the
  separate zero-residual integrability condition;
* `solutionSet_eq` : the exact root values form a coset of `ker Δ_hol`;
* `holonomy_tfae` : the exact/hard/mirage trichotomy of the transverse regime;
* `holonomyDefect_gauge` : unitary frame covariance;
* `nonempty_iInter_iff_bddAbove_infDist_contexts` : cofinal globalization is exactly bounded
  solution capacity.
-/

open Filter
open scoped InnerProductSpace Topology

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {C : Type*} [Fintype C]

/-- The holonomy defect operator `x ↦ (x − Hol e x)_e`. -/
noncomputable def holonomyDefect (Hol : C → (E ≃ₗᵢ[𝕜] E)) :
    E →L[𝕜] PiLp 2 (fun _ : C => E) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : C => E)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi
      (fun e => ContinuousLinearMap.id 𝕜 E - (Hol e).toLinearIsometry.toContinuousLinearMap)

omit [CompleteSpace E] [Fintype C] in
@[simp] theorem holonomyDefect_apply (Hol : C → (E ≃ₗᵢ[𝕜] E)) (x : E) (e : C) :
    holonomyDefect Hol x e = x - Hol e x := rfl

/-- The source current vector of a chord family. -/
noncomputable def currentVector (c : C → E) : PiLp 2 (fun _ : C => E) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : C => E)).symm c

omit [CompleteSpace E] [Fintype C] in
@[simp] theorem currentVector_apply (c : C → E) (e : C) :
    (currentVector (𝕜 := 𝕜) c) e = c e := rfl

/-- The holonomy Laplacian `Δ_hol = D* D`. -/
noncomputable def holonomyLaplacian (Hol : C → (E ≃ₗᵢ[𝕜] E)) : E →L[𝕜] E :=
  ContinuousLinearMap.adjoint (holonomyDefect Hol) ∘L holonomyDefect Hol

/-- The source current `J_src = D* c`. -/
noncomputable def sourceCurrent (Hol : C → (E ≃ₗᵢ[𝕜] E)) (c : C → E) : E :=
  ContinuousLinearMap.adjoint (holonomyDefect Hol) (currentVector (𝕜 := 𝕜) c)

/-- The affine precision energy `E(x) = ‖D x − c‖²`. -/
noncomputable def holonomyEnergy (Hol : C → (E ≃ₗᵢ[𝕜] E)) (c : C → E) (x : E) : ℝ :=
  ‖holonomyDefect Hol x - currentVector (𝕜 := 𝕜) c‖ ^ 2

omit [CompleteSpace E] in
/-- Being exact is having zero residual. -/
theorem exact_iff_energy_eq_zero (Hol : C → (E ≃ₗᵢ[𝕜] E)) (c : C → E) (x : E) :
    (∀ e : C, x - Hol e x = c e) ↔ holonomyEnergy Hol c x = 0 := by
  constructor
  · intro hx
    have hzero : holonomyDefect Hol x - currentVector (𝕜 := 𝕜) c = 0 := by
      ext e
      show holonomyDefect Hol x e - c e = (0 : PiLp 2 (fun _ : C => E)) e
      rw [holonomyDefect_apply, hx e]
      simp
    rw [holonomyEnergy, hzero, norm_zero]
    norm_num
  · intro hE e
    have hzero : holonomyDefect Hol x - currentVector (𝕜 := 𝕜) c = 0 := by
      rw [← norm_eq_zero]
      have := hE
      rw [holonomyEnergy] at this
      nlinarith [norm_nonneg (holonomyDefect Hol x - currentVector (𝕜 := 𝕜) c)]
    have hcoord := congrArg (fun z : PiLp 2 (fun _ : C => E) => z e) hzero
    simp only at hcoord
    have : holonomyDefect Hol x e - c e = 0 := hcoord
    rw [holonomyDefect_apply] at this
    exact sub_eq_zero.mp this

/-- **Theorem 4.1.**  Every exact global presentation satisfies the observer field equation. -/
theorem holonomyLaplacian_apply_of_exact (Hol : C → (E ≃ₗᵢ[𝕜] E)) (c : C → E) {x : E}
    (hx : ∀ e : C, x - Hol e x = c e) :
    holonomyLaplacian Hol x = sourceCurrent Hol c := by
  have hD : holonomyDefect Hol x = currentVector (𝕜 := 𝕜) c := by
    ext e
    show holonomyDefect Hol x e = c e
    rw [holonomyDefect_apply, hx e]
  rw [holonomyLaplacian, sourceCurrent, ContinuousLinearMap.comp_apply, hD]

theorem ker_holonomyLaplacian (Hol : C → (E ≃ₗᵢ[𝕜] E)) :
    LinearMap.ker ((holonomyLaplacian Hol : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = LinearMap.ker ((holonomyDefect Hol : E →L[𝕜] PiLp 2 (fun _ : C => E)) :
          E →ₗ[𝕜] PiLp 2 (fun _ : C => E)) :=
  ContinuousLinearMap.ker_adjoint_comp_self (holonomyDefect Hol)

omit [CompleteSpace E] [Fintype C] in
theorem mem_ker_holonomyDefect_iff (Hol : C → (E ≃ₗᵢ[𝕜] E)) (x : E) :
    x ∈ LinearMap.ker ((holonomyDefect Hol : E →L[𝕜] PiLp 2 (fun _ : C => E)) :
        E →ₗ[𝕜] PiLp 2 (fun _ : C => E)) ↔ ∀ e : C, Hol e x = x := by
  constructor
  · intro hx e
    have h0 : holonomyDefect Hol x = 0 := hx
    have hcoord := congrArg (fun z : PiLp 2 (fun _ : C => E) => z e) h0
    simp only at hcoord
    have : x - Hol e x = 0 := hcoord
    exact (sub_eq_zero.mp this).symm
  · intro hx
    show holonomyDefect Hol x = 0
    ext e
    show x - Hol e x = (0 : PiLp 2 (fun _ : C => E)) e
    rw [hx e, sub_self]
    simp

/-- **Theorem 4.1.**  If an exact global presentation exists, the exact root values are a coset of
the kernel of the holonomy Laplacian. -/
theorem solutionSet_eq (Hol : C → (E ≃ₗᵢ[𝕜] E)) (c : C → E) {x₀ : E}
    (hx₀ : ∀ e : C, x₀ - Hol e x₀ = c e) :
    {x : E | ∀ e : C, x - Hol e x = c e}
      = {x : E | x - x₀ ∈ LinearMap.ker
          ((holonomyLaplacian Hol : E →L[𝕜] E) : E →ₗ[𝕜] E)} := by
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ker_holonomyLaplacian, mem_ker_holonomyDefect_iff]
  constructor
  · intro hx e
    have h1 := hx e
    have h2 := hx₀ e
    have : (x - Hol e x) - (x₀ - Hol e x₀) = 0 := by rw [h1, h2, sub_self]
    have hlin : Hol e (x - x₀) = Hol e x - Hol e x₀ := map_sub _ _ _
    rw [hlin]
    have hgoal : (x - x₀) - (Hol e x - Hol e x₀) = 0 := by
      calc (x - x₀) - (Hol e x - Hol e x₀)
          = (x - Hol e x) - (x₀ - Hol e x₀) := by abel
        _ = 0 := this
    exact (sub_eq_zero.mp hgoal).symm
  · intro hx e
    have hfix := hx e
    have hlin : Hol e (x - x₀) = Hol e x - Hol e x₀ := map_sub _ _ _
    rw [hlin] at hfix
    have h2 := hx₀ e
    have hgoal : x - Hol e x = x₀ - Hol e x₀ := by
      have : (x - x₀) - (Hol e x - Hol e x₀) = 0 := by rw [hfix, sub_self]
      have hcalc : (x - Hol e x) - (x₀ - Hol e x₀) = 0 := by
        calc (x - Hol e x) - (x₀ - Hol e x₀)
            = (x - x₀) - (Hol e x - Hol e x₀) := by abel
          _ = 0 := this
      exact sub_eq_zero.mp hcalc
    rw [hgoal, h2]

/-! ## The transverse regimes -/

/-- **Corollary 5.1.**  Transverse uniformity, closed range of the defect map, and closedness of
the sum of the holonomy defect ranges are equivalent. -/
theorem holonomy_tfae (Hol : C → (E ≃ₗᵢ[𝕜] E)) :
    List.TFAE
      [ ContinuousLinearMap.HasTransverseLowerBound (holonomyDefect Hol),
        IsClosed (Set.range (holonomyDefect Hol)),
        IsClosed (Set.range (ContinuousLinearMap.adjoint (holonomyDefect Hol))) ] := by
  tfae_have 1 ↔ 2 :=
    ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range (holonomyDefect Hol)
  tfae_have 2 ↔ 3 :=
    (ContinuousLinearMap.isClosed_range_adjoint_iff (holonomyDefect Hol)).symm
  tfae_finish

omit [CompleteSpace E] in
/-- **Corollary 5.1(3).**  Without a transverse lower bound there are transverse unit vectors that
are almost invariant under every chord holonomy. -/
theorem exists_almost_invariant_unit_sequence (Hol : C → (E ≃ₗᵢ[𝕜] E))
    (hgap : ¬ ContinuousLinearMap.HasTransverseLowerBound (holonomyDefect Hol)) :
    ∃ u : ℕ → E,
      (∀ n, u n ∈ (LinearMap.ker ((holonomyDefect Hol :
        E →L[𝕜] PiLp 2 (fun _ : C => E)) : E →ₗ[𝕜] PiLp 2 (fun _ : C => E)))ᗮ) ∧
      (∀ n, ‖u n‖ = 1) ∧
      ∀ e : C, Tendsto (fun n => ‖u n - Hol e (u n)‖) atTop (𝓝 0) := by
  classical
  have hstep : ∀ n : ℕ, ∃ x ∈ (LinearMap.ker ((holonomyDefect Hol :
      E →L[𝕜] PiLp 2 (fun _ : C => E)) : E →ₗ[𝕜] PiLp 2 (fun _ : C => E)))ᗮ,
      ‖holonomyDefect Hol x‖ < (1 / (n + 1 : ℝ)) * ‖x‖ := by
    intro n
    by_contra hcon
    push Not at hcon
    exact hgap ⟨1 / (n + 1 : ℝ), by positivity, fun x hx => hcon x hx⟩
  choose x hxmem hxlt using hstep
  have hxne : ∀ n, x n ≠ 0 := by
    intro n hzero
    have := hxlt n
    rw [hzero, norm_zero, map_zero, norm_zero] at this
    simp at this
  refine ⟨fun n => (‖x n‖ : 𝕜)⁻¹ • x n, fun n => Submodule.smul_mem _ _ (hxmem n), fun n => ?_, ?_⟩
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    field_simp [norm_ne_zero_iff.mpr (hxne n)]
  · intro e
    have hbound : ∀ n : ℕ,
        ‖((‖x n‖ : 𝕜)⁻¹ • x n) - Hol e ((‖x n‖ : 𝕜)⁻¹ • x n)‖ ≤ 1 / (n + 1 : ℝ) := by
      intro n
      have hnorm : (0 : ℝ) < ‖x n‖ := norm_pos_iff.mpr (hxne n)
      have hcoord : ((‖x n‖ : 𝕜)⁻¹ • x n) - Hol e ((‖x n‖ : 𝕜)⁻¹ • x n)
          = (‖x n‖ : 𝕜)⁻¹ • (x n - Hol e (x n)) := by
        rw [map_smul, smul_sub]
      rw [hcoord, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      have hle : ‖x n - Hol e (x n)‖ ≤ ‖holonomyDefect Hol (x n)‖ := by
        have hcomp : ‖holonomyDefect Hol (x n)‖ ^ 2
            = ∑ j : C, ‖holonomyDefect Hol (x n) j‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
        have hterm : ‖x n - Hol e (x n)‖ ^ 2 ≤ ‖holonomyDefect Hol (x n)‖ ^ 2 := by
          rw [hcomp]
          refine Finset.single_le_sum (f := fun j : C => ‖holonomyDefect Hol (x n) j‖ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ e)
        nlinarith [norm_nonneg (x n - Hol e (x n)), norm_nonneg (holonomyDefect Hol (x n))]
      have hlt := hxlt n
      rw [inv_mul_le_iff₀ hnorm]
      nlinarith [hle, hlt]
    refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## Unitary frame covariance -/

omit [CompleteSpace E] [Fintype C] in
/-- **Proposition 6.1.**  A unitary change of observer frame conjugates the holonomies, transports
the currents, and bijects the exact root values. -/
theorem exact_gauge_iff {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    (G : E ≃ₗᵢ[𝕜] E') (Hol : C → (E ≃ₗᵢ[𝕜] E)) (c : C → E) (x : E) :
    (∀ e : C, x - Hol e x = c e)
      ↔ ∀ e : C, G x - ((G.symm.trans (Hol e)).trans G) (G x) = G (c e) := by
  refine forall_congr' fun e => ?_
  have hconj : ((G.symm.trans (Hol e)).trans G) (G x) = G (Hol e x) := by
    simp [LinearIsometryEquiv.trans_apply]
  rw [hconj, ← map_sub]
  exact ⟨fun h => by rw [h], fun h => G.injective h⟩

/-- The conjugated holonomy family. -/
noncomputable def gaugeHolonomy {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    (G : E ≃ₗᵢ[𝕜] E') (Hol : C → (E ≃ₗᵢ[𝕜] E)) (e : C) : E' ≃ₗᵢ[𝕜] E' :=
  (G.symm.trans (Hol e)).trans G

omit [CompleteSpace E] [Fintype C] in
theorem gaugeHolonomy_apply {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    (G : E ≃ₗᵢ[𝕜] E') (Hol : C → (E ≃ₗᵢ[𝕜] E)) (e : C) (z : E) :
    gaugeHolonomy G Hol e (G z) = G (Hol e z) := by
  simp [gaugeHolonomy, LinearIsometryEquiv.trans_apply]

omit [CompleteSpace E] in
/-- **Proposition 6.1.**  The affine precision energy is observer-frame invariant. -/
theorem holonomyEnergy_gauge {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    (G : E ≃ₗᵢ[𝕜] E') (Hol : C → (E ≃ₗᵢ[𝕜] E)) (c : C → E) (x : E) :
    holonomyEnergy (gaugeHolonomy G Hol) (fun e => G (c e)) (G x)
      = holonomyEnergy Hol c x := by
  have hcoord : ∀ e : C,
      ‖holonomyDefect (gaugeHolonomy G Hol) (G x) e - G (c e)‖
        = ‖holonomyDefect Hol x e - c e‖ := by
    intro e
    rw [holonomyDefect_apply, holonomyDefect_apply, gaugeHolonomy_apply, ← map_sub, ← map_sub,
      LinearIsometryEquiv.norm_map]
  rw [holonomyEnergy, holonomyEnergy, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hl : (holonomyDefect (gaugeHolonomy G Hol) (G x)
      - currentVector (𝕜 := 𝕜) fun e => G (c e)) e
      = holonomyDefect (gaugeHolonomy G Hol) (G x) e - G (c e) := rfl
  have hr : (holonomyDefect Hol x - currentVector (𝕜 := 𝕜) c) e
      = holonomyDefect Hol x e - c e := rfl
  rw [hl, hr, hcoord e]

omit [CompleteSpace E] [Fintype C] in
/-- **Corollary 5.1(1).**  Nonzero joint holonomy fixed vectors are exactly nonzero linear global
presentations at the root. -/
theorem ker_holonomyDefect_ne_bot_iff (Hol : C → (E ≃ₗᵢ[𝕜] E)) :
    LinearMap.ker ((holonomyDefect Hol : E →L[𝕜] PiLp 2 (fun _ : C => E)) :
        E →ₗ[𝕜] PiLp 2 (fun _ : C => E)) ≠ ⊥
      ↔ ∃ x : E, x ≠ 0 ∧ ∀ e : C, Hol e x = x := by
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, hx, hne⟩
    exact ⟨x, hne, (mem_ker_holonomyDefect_iff Hol x).mp hx⟩
  · rintro ⟨x, hne, hfix⟩
    exact ⟨x, (mem_ker_holonomyDefect_iff Hol x).mpr hfix, hne⟩

/-! ## Cofinal globalization and the capacity horizon -/

section Capacity

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The finite observer contexts of a countable chord family. -/
def observerContext (Hol : ℕ → (F ≃ₗᵢ[ℝ] F)) (c : ℕ → F) (n : ℕ) : Set F :=
  {x : F | ∀ k ≤ n, x - Hol k x = c k}

omit [CompleteSpace F] in
theorem observerContext_antitone (Hol : ℕ → (F ≃ₗᵢ[ℝ] F)) (c : ℕ → F) (n : ℕ) :
    observerContext Hol c (n + 1) ⊆ observerContext Hol c n := by
  intro x hx k hk
  exact hx k (by omega)

omit [CompleteSpace F] in
theorem observerContext_isClosed (Hol : ℕ → (F ≃ₗᵢ[ℝ] F)) (c : ℕ → F) (n : ℕ) :
    IsClosed (observerContext Hol c n) := by
  have hrepr : observerContext Hol c n
      = ⋂ k ∈ Finset.range (n + 1),
        (fun x : F => x - Hol k x) ⁻¹' {c k} := by
    ext x
    simp only [observerContext, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
      Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h k hk => h k (by omega), fun h k hk => h k (by omega)⟩
  rw [hrepr]
  refine isClosed_biInter fun k _ => ?_
  refine IsClosed.preimage ?_ isClosed_singleton
  exact continuous_id.sub (Hol k).continuous

omit [CompleteSpace F] in
theorem observerContext_convex (Hol : ℕ → (F ≃ₗᵢ[ℝ] F)) (c : ℕ → F) (n : ℕ) :
    Convex ℝ (observerContext Hol c n) := by
  intro x hx y hy s t hs ht hst k hk
  have hxk : x - Hol k x = c k := hx k hk
  have hyk : y - Hol k y = c k := hy k hk
  have hlin : Hol k (s • x + t • y) = s • Hol k x + t • Hol k y := by
    rw [map_add, map_smul, map_smul]
  rw [hlin]
  have hcalc : (s • x + t • y) - (s • Hol k x + t • Hol k y)
      = s • (x - Hol k x) + t • (y - Hol k y) := by
    rw [smul_sub, smul_sub]
    abel
  rw [hcalc, hxk, hyk, ← add_smul, hst, one_smul]

/-- **Theorem 8.1.**  A consistent countable observer family globalizes exactly when the finite
contexts have bounded solution capacity. -/
theorem nonempty_iInter_observerContext_iff (Hol : ℕ → (F ≃ₗᵢ[ℝ] F)) (c : ℕ → F)
    (hne : ∀ n, (observerContext Hol c n).Nonempty) :
    (⋂ n, observerContext Hol c n).Nonempty
      ↔ ∃ R : ℝ, ∀ n, Metric.infDist 0 (observerContext Hol c n) ≤ R :=
  nonempty_iInter_iff_bddAbove_infDist _ hne (observerContext_isClosed Hol c)
    (observerContext_convex Hol c) (observerContext_antitone Hol c)

/-- **Corollary 8.2.**  A finite-consistency mirage has exactly one cause: the solution capacity
escapes every bound. -/
theorem tendsto_infDist_observerContext_of_empty (Hol : ℕ → (F ≃ₗᵢ[ℝ] F)) (c : ℕ → F)
    (hne : ∀ n, (observerContext Hol c n).Nonempty)
    (hempty : (⋂ n, observerContext Hol c n) = ∅) :
    Tendsto (fun n => Metric.infDist 0 (observerContext Hol c n)) atTop atTop := by
  have hunb : ¬ ∃ R : ℝ, ∀ n, Metric.infDist 0 (observerContext Hol c n) ≤ R := by
    intro hbdd
    have := (nonempty_iInter_observerContext_iff Hol c hne).mpr hbdd
    rw [hempty] at this
    exact this.ne_empty rfl
  have hmono : Monotone fun n => Metric.infDist 0 (observerContext Hol c n) := by
    intro n m hnm
    refine Metric.infDist_le_infDist_of_subset ?_ (hne m)
    exact antitone_nat_of_succ_le (observerContext_antitone Hol c) hnm
  refine tendsto_atTop_atTop.mpr fun b => ?_
  by_contra hcon
  push Not at hcon
  apply hunb
  refine ⟨b, fun n => ?_⟩
  obtain ⟨m, hm, hlt⟩ := hcon n
  exact le_trans (hmono hm) hlt.le

end Capacity

end GaloisForLFunctions.HTGeometry
