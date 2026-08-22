import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The Banach transpose and invertibility

For a bounded operator `L : E → F` between Banach spaces the **transpose**
`Lᵀ : F* → E*` is precomposition with `L`.  The main theorem is that `L` is an isomorphism if
and only if `Lᵀ` is:

* if `L` has a bounded inverse then the transpose of that inverse inverts `Lᵀ`;
* conversely, `Lᵀ` invertible makes the *double* transpose invertible, and since the canonical
  embeddings into the biduals are isometric and intertwine `L` with `Lᵀᵀ`, the operator `L` is
  bounded below — hence injective with closed range — while injectivity of `Lᵀ` forces the range
  to be dense by Hahn–Banach.

Under the trace duality `(S¹(ℋ))* ≅ S(ℋ)` this is the statement that a bounded operator on the
trace class is an isomorphism exactly when its adjoint is an isomorphism on the bounded operators.
-/

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The **Banach transpose** of `L : E →L[𝕜] F`: precomposition with `L` on the strong duals. -/
noncomputable def transposeCLM (L : E →L[𝕜] F) : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E :=
  (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip L

@[simp] lemma transposeCLM_apply (L : E →L[𝕜] F) (f : StrongDual 𝕜 F) (x : E) :
    transposeCLM L f x = f (L x) := rfl

@[simp] lemma transposeCLM_id :
    transposeCLM (ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E) := by
  ext f x
  rfl

lemma transposeCLM_comp (L : E →L[𝕜] F) (M : F →L[𝕜] G) :
    transposeCLM (M.comp L) = (transposeCLM L).comp (transposeCLM M) := by
  ext f x
  rfl

/-- The double transpose extends `L` along the canonical embeddings into the biduals. -/
lemma transposeCLM_transposeCLM_inclusion (L : E →L[𝕜] F) (x : E) :
    transposeCLM (transposeCLM L) (NormedSpace.inclusionInDoubleDual 𝕜 E x)
      = NormedSpace.inclusionInDoubleDual 𝕜 F (L x) := by
  ext f
  rfl

/-! ### Transposing an inverse -/

/-- If `L` has a two-sided bounded inverse then so does its transpose. -/
theorem bijective_transposeCLM_of_inverse {L : E →L[𝕜] F} {M : F →L[𝕜] E}
    (h1 : M.comp L = ContinuousLinearMap.id 𝕜 E)
    (h2 : L.comp M = ContinuousLinearMap.id 𝕜 F) :
    Function.Bijective (transposeCLM L) := by
  have hA : (transposeCLM L).comp (transposeCLM M)
      = ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E) := by
    rw [← transposeCLM_comp, h1, transposeCLM_id]
  have hB : (transposeCLM M).comp (transposeCLM L)
      = ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 F) := by
    rw [← transposeCLM_comp, h2, transposeCLM_id]
  have hBapp : ∀ f : StrongDual 𝕜 F, transposeCLM M (transposeCLM L f) = f := by
    intro f
    have h := congrArg (fun (T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 F) => T f) hB
    simpa using h
  refine ⟨Function.LeftInverse.injective hBapp, fun f => ⟨transposeCLM M f, ?_⟩⟩
  have h := congrArg (fun (T : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E) => T f) hA
  simpa using h

/-- The transpose of a bijective bounded operator between Banach spaces is bijective. -/
theorem bijective_transposeCLM_of_bijective [CompleteSpace E] [CompleteSpace F]
    {L : E →L[𝕜] F} (hL : Function.Bijective L) : Function.Bijective (transposeCLM L) := by
  have hker : LinearMap.ker (L : E →ₗ[𝕜] F) = ⊥ := LinearMap.ker_eq_bot.mpr hL.1
  have hrange : LinearMap.range (L : E →ₗ[𝕜] F) = ⊤ := LinearMap.range_eq_top.mpr hL.2
  set e : E ≃L[𝕜] F := ContinuousLinearEquiv.ofBijective L hker hrange with he
  have heL : ∀ x, e x = L x := fun x => rfl
  refine bijective_transposeCLM_of_inverse (M := (e.symm : F →L[𝕜] E)) ?_ ?_
  · ext x
    show e.symm (L x) = x
    rw [← heL x, e.symm_apply_apply]
  · ext y
    show L (e.symm y) = y
    rw [← heL (e.symm y), e.apply_symm_apply]

/-! ### Hahn–Banach separation from a closed subspace -/

/-- A closed proper subspace of a normed space is annihilated by a nonzero functional. -/
theorem exists_dual_eq_zero_on {p : Submodule 𝕜 F} (hp : IsClosed (p : Set F))
    {x : F} (hx : x ∉ p) :
    ∃ f : StrongDual 𝕜 F, f ≠ 0 ∧ ∀ y ∈ p, f y = 0 := by
  haveI : IsClosed (p : Set F) := hp
  have hne : (Submodule.Quotient.mk x : F ⧸ p) ≠ 0 := fun h =>
    hx ((Submodule.Quotient.mk_eq_zero p).mp h)
  have hmk : ‖(Submodule.Quotient.mk x : F ⧸ p)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  obtain ⟨g, -, hgx⟩ := exists_dual_vector'' 𝕜 (Submodule.Quotient.mk x : F ⧸ p)
  refine ⟨g.comp (p.mkQ.mkContinuous 1
      (fun m => by simpa using Submodule.Quotient.norm_mk_le p m)), ?_, ?_⟩
  · intro hcon
    apply hmk
    have h2 := congrArg (fun (h : StrongDual 𝕜 F) => h x) hcon
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearMap.mkContinuous_apply, Submodule.mkQ_apply, zero_apply] at h2
    rw [h2] at hgx
    exact_mod_cast hgx.symm
  · intro y hy
    simp [(Submodule.Quotient.mk_eq_zero p).mpr hy]

/-! ### The converse -/

/-- **Lemma 3.14 (Kim–Mer–Pálfia), converse half.**  If the transpose of `L` is an isomorphism
then so is `L`.  Surjectivity of the transpose makes `L` bounded below through a norming
functional, and injectivity of the transpose makes the range dense. -/
theorem bijective_of_bijective_transposeCLM [CompleteSpace E] [CompleteSpace F]
    {L : E →L[𝕜] F} (h : Function.Bijective (transposeCLM L)) : Function.Bijective L := by
  have hker : LinearMap.ker ((transposeCLM L : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
      StrongDual 𝕜 F →ₗ[𝕜] StrongDual 𝕜 E) = ⊥ := LinearMap.ker_eq_bot.mpr h.1
  have hrange : LinearMap.range ((transposeCLM L : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
      StrongDual 𝕜 F →ₗ[𝕜] StrongDual 𝕜 E) = ⊤ := LinearMap.range_eq_top.mpr h.2
  set e : StrongDual 𝕜 F ≃L[𝕜] StrongDual 𝕜 E :=
    ContinuousLinearEquiv.ofBijective (transposeCLM L) hker hrange with he
  have heL : ∀ g, e g = transposeCLM L g := fun g => rfl
  set einv : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 F :=
    (e.symm : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 F) with heinv
  -- `L` is bounded below: a norming functional for `x` factors through `L`
  have hbound : ∀ x : E, ‖x‖ ≤ ‖einv‖ * ‖L x‖ := by
    intro x
    obtain ⟨f, hf1, hfx⟩ := exists_dual_vector'' 𝕜 x
    have hfe : transposeCLM L (einv f) = f := by
      rw [heinv, ← heL]
      exact e.apply_symm_apply f
    have hval : f x = einv f (L x) := by
      conv_lhs => rw [← hfe]
      rfl
    have hnf : ‖einv f‖ ≤ ‖einv‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    have h1 : ‖x‖ = ‖f x‖ := by rw [hfx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]
    calc ‖x‖ = ‖f x‖ := h1
      _ = ‖einv f (L x)‖ := by rw [hval]
      _ ≤ ‖einv f‖ * ‖L x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖einv‖ * ‖f‖) * ‖L x‖ := by
          exact mul_le_mul_of_nonneg_right hnf (norm_nonneg _)
      _ ≤ (‖einv‖ * 1) * ‖L x‖ := by gcongr
      _ = ‖einv‖ * ‖L x‖ := by rw [mul_one]
  have hinj : Function.Injective L := by
    intro x y hxy
    have hb := hbound (x - y)
    rw [show L (x - y) = 0 by rw [map_sub, hxy, sub_self], norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  -- the range is closed
  have hanti : AntilipschitzWith ‖einv‖₊ (L : E → F) := by
    refine AddMonoidHomClass.antilipschitz_of_bound L fun x => ?_
    simpa using hbound x
  have hclosed : IsClosed (Set.range (L : E → F)) :=
    hanti.isClosed_range L.uniformContinuous
  -- the range is everything
  have hsurj : Function.Surjective L := by
    by_contra hcon
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : F, ∀ x, L x ≠ y₀ := by
      simpa [Function.Surjective, not_forall] using hcon
    have hy₀' : y₀ ∉ LinearMap.range (L : E →ₗ[𝕜] F) := by
      rintro ⟨x, hxeq⟩
      exact hy₀ x hxeq
    have hpc : IsClosed ((LinearMap.range (L : E →ₗ[𝕜] F) : Submodule 𝕜 F) : Set F) := by
      show IsClosed (Set.range ((L : E →ₗ[𝕜] F) : E → F))
      exact hclosed
    obtain ⟨f, hf0, hfz⟩ := exists_dual_eq_zero_on hpc hy₀'
    apply hf0
    have hzero : transposeCLM L f = 0 := by
      ext x
      exact hfz (L x) ⟨x, rfl⟩
    have hzz : transposeCLM L f = transposeCLM L 0 := by simpa using hzero
    exact h.1 hzz
  exact ⟨hinj, hsurj⟩

/-- **Lemma 3.14 (Kim–Mer–Pálfia).**  A bounded operator between Banach spaces is an isomorphism
if and only if its Banach transpose is an isomorphism of the strong duals. -/
theorem bijective_transposeCLM_iff [CompleteSpace E] [CompleteSpace F] (L : E →L[𝕜] F) :
    Function.Bijective (transposeCLM L) ↔ Function.Bijective L :=
  ⟨bijective_of_bijective_transposeCLM, bijective_transposeCLM_of_bijective⟩

end GaloisForLFunctions.HTGeometry
