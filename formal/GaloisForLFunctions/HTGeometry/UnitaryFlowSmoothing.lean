import GaloisForLFunctions.HTGeometry.CompactCommutingFlowDecomposition

/-!
# Smoothings of a strongly continuous unitary flow

For a strongly continuous one-parameter unitary group `U` and a compactly supported continuous
weight `φ`, the smoothing

`K_φ x = ∫ φ(t) • U t x dt`

is a bounded operator commuting with the flow.  Commutation needs no change of variables: both
`U s (K_φ x)` and `K_φ (U s x)` equal `∫ φ(t) • U (s + t) x dt`, because a continuous linear map
passes through a Bochner integral and the group law is symmetric in its two arguments.

Together with the eigenspace machinery this is the input of the block decomposition: whenever a
smoothing is compact, its eigenspaces are finite-dimensional and flow-invariant.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A strongly continuous one-parameter unitary group. -/
structure UnitaryFlow (𝕜 : Type*) [RCLike 𝕜] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] where
  /-- The unitary at each time. -/
  op : ℝ → (H ≃ₗᵢ[𝕜] H)
  /-- The group law. -/
  op_add : ∀ s t x, op (s + t) x = op s (op t x)
  /-- Strong continuity. -/
  continuous_orbit : ∀ x, Continuous fun t => op t x

variable [NormedSpace ℝ H] [CompleteSpace H]

/-- The smoothing of a unitary flow against a weight. -/
noncomputable def flowSmoothing (U : UnitaryFlow 𝕜 H) (phi : ℝ → ℝ) (x : H) : H :=
  ∫ t, phi t • U.op t x

omit [CompleteSpace H] in
/-- The smoothing integrand is continuous. -/
theorem continuous_flowSmoothing_integrand (U : UnitaryFlow 𝕜 H) {phi : ℝ → ℝ}
    (hphi : Continuous phi) (x : H) :
    Continuous fun t => phi t • U.op t x :=
  hphi.smul (U.continuous_orbit x)

omit [CompleteSpace H] in
/-- A compactly supported continuous weight gives an integrable smoothing integrand. -/
theorem integrable_flowSmoothing_integrand (U : UnitaryFlow 𝕜 H) {phi : ℝ → ℝ}
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi) (x : H) :
    Integrable fun t => phi t • U.op t x := by
  refine (continuous_flowSmoothing_integrand U hphi x).integrable_of_hasCompactSupport ?_
  exact hsupp.smul_right

/-- **The smoothing commutes with the flow.**  Both sides equal `∫ φ(t) • U (s + t) x dt`. -/
theorem flowSmoothing_comm (U : UnitaryFlow 𝕜 H) {phi : ℝ → ℝ}
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi) (s : ℝ) (x : H) :
    U.op s (flowSmoothing U phi x) = flowSmoothing U phi (U.op s x) := by
  have hint := integrable_flowSmoothing_integrand U hphi hsupp x
  have hL :
      (U.op s).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ
          (∫ t, phi t • U.op t x) =
        ∫ t, (U.op s).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ
          (phi t • U.op t x) :=
    (ContinuousLinearMap.integral_comp_comm _ hint).symm
  rw [flowSmoothing, flowSmoothing]
  have hleft : U.op s (∫ t, phi t • U.op t x) = ∫ t, phi t • U.op s (U.op t x) := by
    simpa using hL
  rw [hleft]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show phi t • U.op s (U.op t x) = phi t • U.op t (U.op s x)
  rw [← U.op_add s t, ← U.op_add t s, add_comm s t]

/-! ## Time reversal and symmetry -/

omit [NormedSpace ℝ H] [CompleteSpace H] in
/-- The flow at time zero is the identity. -/
theorem op_zero (U : UnitaryFlow 𝕜 H) (x : H) : U.op 0 x = x := by
  have h := U.op_add 0 0 x
  rw [add_zero] at h
  exact ((U.op 0).injective h.symm)

omit [NormedSpace ℝ H] [CompleteSpace H] in
/-- Time reversal is the inverse unitary. -/
theorem op_neg (U : UnitaryFlow 𝕜 H) (t : ℝ) (x : H) : U.op (-t) x = (U.op t).symm x := by
  refine (U.op t).injective ?_
  rw [(U.op t).apply_symm_apply, ← U.op_add t (-t) x, add_neg_cancel, op_zero]

omit [NormedSpace ℝ H] [CompleteSpace H] in
/-- Unitarity moves the flow to the other side of the inner product as time reversal. -/
theorem inner_op_left (U : UnitaryFlow 𝕜 H) (t : ℝ) (x y : H) :
    inner 𝕜 (U.op t x) y = inner 𝕜 x (U.op (-t) y) := by
  rw [op_neg]
  have h := (U.op t).inner_map_map x ((U.op t).symm y)
  rw [(U.op t).apply_symm_apply] at h
  exact h

/-- **Self-adjointness of the smoothing for a real even weight.**  Time reversal turns the flow
into its inverse, and evenness of the weight absorbs the resulting change of variables. -/
theorem flowSmoothing_inner_symm [IsScalarTower ℝ 𝕜 H] (U : UnitaryFlow 𝕜 H) {phi : ℝ → ℝ}
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi)
    (heven : ∀ t, phi (-t) = phi t) (x y : H) :
    inner 𝕜 (flowSmoothing U phi x) y = inner 𝕜 x (flowSmoothing U phi y) := by
  have hintx := integrable_flowSmoothing_integrand U hphi hsupp x
  have hinty := integrable_flowSmoothing_integrand U hphi hsupp y
  have hright : inner 𝕜 x (flowSmoothing U phi y) = ∫ t, inner 𝕜 x (phi t • U.op t y) :=
    (integral_inner hinty x).symm
  have h1 : inner 𝕜 y (flowSmoothing U phi x) = ∫ t, inner 𝕜 y (phi t • U.op t x) :=
    (integral_inner hintx y).symm
  have hleft : inner 𝕜 (flowSmoothing U phi x) y = ∫ t, inner 𝕜 (phi t • U.op t x) y := by
    calc inner 𝕜 (flowSmoothing U phi x) y
        = (starRingEnd 𝕜) (inner 𝕜 y (flowSmoothing U phi x)) := (inner_conj_symm _ _).symm
      _ = (starRingEnd 𝕜) (∫ t, inner 𝕜 y (phi t • U.op t x)) := by rw [h1]
      _ = ∫ t, (starRingEnd 𝕜) (inner 𝕜 y (phi t • U.op t x)) := integral_conj.symm
      _ = ∫ t, inner 𝕜 (phi t • U.op t x) y :=
          integral_congr_ae (Filter.Eventually.of_forall fun t => inner_conj_symm _ _)
  rw [hleft, hright]
  have hstep : ∀ t : ℝ,
      inner 𝕜 (phi t • U.op t x) y = inner 𝕜 x (phi (-t) • U.op (-t) y) := by
    intro t
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) (phi t) (U.op t x),
      RCLike.real_smul_eq_coe_smul (K := 𝕜) (phi (-t)) (U.op (-t) y),
      inner_smul_real_left, inner_smul_real_right, inner_op_left, heven]
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep)]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (MeasurableEquiv.neg ℝ).measurableEmbedding
    (fun t => inner 𝕜 x (phi t • U.op t y))

/-! ## The smoothing as a bounded operator -/

section Bounded

variable [SMulCommClass ℝ 𝕜 H]

/-- The smoothing is linear. -/
noncomputable def flowSmoothingLinear (U : UnitaryFlow 𝕜 H) (phi : ℝ → ℝ)
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi) : H →ₗ[𝕜] H where
  toFun := flowSmoothing U phi
  map_add' x y := by
    simp only [flowSmoothing]
    rw [← integral_add (integrable_flowSmoothing_integrand U hphi hsupp x)
      (integrable_flowSmoothing_integrand U hphi hsupp y)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show phi t • U.op t (x + y) = phi t • U.op t x + phi t • U.op t y
    rw [map_add, smul_add]
  map_smul' c x := by
    simp only [flowSmoothing, RingHom.id_apply]
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show phi t • U.op t (c • x) = c • (phi t • U.op t x)
    rw [map_smul, smul_comm]

omit [CompleteSpace H] [SMulCommClass ℝ 𝕜 H] in
/-- The smoothing is bounded by the `L¹` norm of the weight. -/
theorem norm_flowSmoothing_le (U : UnitaryFlow 𝕜 H) (phi : ℝ → ℝ) (x : H) :
    ‖flowSmoothing U phi x‖ ≤ (∫ t, |phi t|) * ‖x‖ := by
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  have hpt : ∀ t : ℝ, ‖phi t • U.op t x‖ = |phi t| * ‖x‖ := by
    intro t
    rw [norm_smul, Real.norm_eq_abs, (U.op t).norm_map]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_mul_const]

/-- The smoothing as a continuous linear operator. -/
noncomputable def flowSmoothingCLM (U : UnitaryFlow 𝕜 H) (phi : ℝ → ℝ)
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi) : H →L[𝕜] H :=
  (flowSmoothingLinear U phi hphi hsupp).mkContinuous (∫ t, |phi t|)
    (norm_flowSmoothing_le U phi)

omit [CompleteSpace H] in
@[simp]
theorem flowSmoothingCLM_apply (U : UnitaryFlow 𝕜 H) (phi : ℝ → ℝ)
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi) (x : H) :
    flowSmoothingCLM U phi hphi hsupp x = flowSmoothing U phi x := rfl

/-- For a real even weight the bounded smoothing is symmetric. -/
theorem isSymmetric_flowSmoothingCLM [IsScalarTower ℝ 𝕜 H] (U : UnitaryFlow 𝕜 H) {phi : ℝ → ℝ}
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi) (heven : ∀ t, phi (-t) = phi t) :
    ((flowSmoothingCLM U phi hphi hsupp : H →L[𝕜] H) : H →ₗ[𝕜] H).IsSymmetric := by
  intro x y
  exact flowSmoothing_inner_symm U hphi hsupp heven x y

/-- **The blocks span.**  For a compact symmetric smoothing the eigenspaces have trivial
orthogonal complement, so the finite-dimensional flow-invariant blocks exhaust the space. -/
theorem orthogonalComplement_iSup_eigenspaces_flowSmoothing_eq_bot [IsScalarTower ℝ 𝕜 H]
    (U : UnitaryFlow 𝕜 H) {phi : ℝ → ℝ}
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi) (heven : ∀ t, phi (-t) = phi t)
    (hK : IsCompactOperator (flowSmoothingCLM U phi hphi hsupp)) :
    (⨆ mu, Module.End.eigenspace
        ((flowSmoothingCLM U phi hphi hsupp : H →L[𝕜] H) : H →ₗ[𝕜] H) mu)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hK
    (isSymmetric_flowSmoothingCLM U hphi hsupp heven)

end Bounded

/-! ## Unimodularity on the blocks -/

omit [NormedSpace ℝ H] [CompleteSpace H] in
/-- **Eigenvalues of a unitary are unimodular.** -/
theorem norm_eq_one_of_unitary_eigenvector {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] (V : F ≃ₗᵢ[𝕜] F) {x : F} (hx : x ≠ 0) {mu : 𝕜}
    (heig : V x = mu • x) : ‖mu‖ = 1 := by
  have hnorm : ‖x‖ = ‖mu‖ * ‖x‖ := by
    calc ‖x‖ = ‖V x‖ := (V.norm_map x).symm
      _ = ‖mu • x‖ := by rw [heig]
      _ = ‖mu‖ * ‖x‖ := norm_smul mu x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  nlinarith [hnorm, hxpos]

omit [NormedSpace ℝ H] [CompleteSpace H] in
/-- On a nonzero finite-dimensional complex block a unitary has an eigenvector, and its
eigenvalue lies on the unit circle.  This is the finite-dimensional half of discreteness: each
block contributes one unimodular flow character. -/
theorem exists_unimodular_eigenvector {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [Nontrivial F] (V : F ≃ₗᵢ[ℂ] F) :
    ∃ (x : F) (mu : ℂ), x ≠ 0 ∧ V x = mu • x ∧ ‖mu‖ = 1 := by
  obtain ⟨mu, hmu⟩ := Module.End.exists_eigenvalue (V.toLinearEquiv.toLinearMap : Module.End ℂ F)
  obtain ⟨x, hx⟩ := hmu.exists_hasEigenvector
  have heig : V x = mu • x := Module.End.mem_eigenspace_iff.mp hx.1
  exact ⟨x, mu, hx.2, heig, norm_eq_one_of_unitary_eigenvector V hx.2 heig⟩

/-! ## Block decomposition from a compact commuting smoothing -/

omit [NormedSpace ℝ H] in
/-- **Finite-dimensional flow blocks from a compact smoothing.**  If some operator commuting with
the flow is compact, then each of its eigenspaces for a nonzero eigenvalue is finite dimensional,
is preserved by the whole flow, and carries the restricted flow as a unitary group. -/
theorem flowBlock_finiteDimensional_and_invariant
    (U : UnitaryFlow 𝕜 H) {K : H →L[𝕜] H} (hK : IsCompactOperator K)
    (hcomm : ∀ s x, K (U.op s x) = U.op s (K x)) {mu : 𝕜} (hmu : mu ≠ 0) :
    FiniteDimensional 𝕜 (Module.End.eigenspace K.toLinearMap mu) ∧
      ∀ s : ℝ, ∀ x ∈ Module.End.eigenspace K.toLinearMap mu,
        U.op s x ∈ Module.End.eigenspace K.toLinearMap mu :=
  ⟨finiteDimensional_eigenspace_of_isCompactOperator hK hmu,
    fun s => mapsTo_eigenspace_of_unitary_comm (U.op s) K (hcomm s) mu⟩

/-- The flow restricted to one such block, as a unitary of the block. -/
noncomputable def flowBlockUnitary
    (U : UnitaryFlow 𝕜 H) (K : H →L[𝕜] H)
    (hcomm : ∀ s x, K (U.op s x) = U.op s (K x)) (mu : 𝕜) (s : ℝ) :
    (Module.End.eigenspace K.toLinearMap mu) ≃ₗᵢ[𝕜]
      (Module.End.eigenspace K.toLinearMap mu) :=
  unitaryEigenspaceRestrict (U.op s) K (hcomm s) mu

omit [NormedSpace ℝ H] [CompleteSpace H] in
/-- The restricted flow is again a one-parameter group. -/
theorem flowBlockUnitary_add
    (U : UnitaryFlow 𝕜 H) (K : H →L[𝕜] H)
    (hcomm : ∀ s x, K (U.op s x) = U.op s (K x)) (mu : 𝕜) (s t : ℝ)
    (x : Module.End.eigenspace K.toLinearMap mu) :
    flowBlockUnitary U K hcomm mu (s + t) x =
      flowBlockUnitary U K hcomm mu s (flowBlockUnitary U K hcomm mu t x) := by
  apply Subtype.ext
  simpa [flowBlockUnitary] using U.op_add s t (x : H)

end GaloisForLFunctions.HTGeometry
