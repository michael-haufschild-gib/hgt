import GaloisForLFunctions.HTGeometry.BlockFormationSemiFredholm
import GaloisForLFunctions.HTGeometry.CompactOperatorFiniteSchurReduction

/-!
# Projection lift of an almost-orthogonal projection sum

Let `P`, `Q` be orthogonal projections on a Hilbert space with `PQ` compact.  Then `P + Q` is a
projection modulo compact operators, and it lifts to a genuine orthogonal projection:
there is a projection `Ψ` with `Ψ - (P + Q)` compact.

The construction: a finite-codimensional closed subspace `M` on which `‖PQ x‖ ≤ ½‖x‖` cuts `ran Q`
down to `N' = ran Q ∩ M`, with projection `Q'` and `Q - Q'` of finite rank.  On `N'` the operator
`1 - P` is bounded below by `√3/2`, so `A = (1 - P)Q'` has closed range with projection `R`, and
`Ψ = P + R` is a projection (`PR = RP = 0`).  Writing `A = Q' - PQ'` gives `RQ' - Q' = RPQ' - PQ'`
and `(1 - Q')R = -(1 - Q')PQ'B` for a bounded left inverse `B` of `A`; both are compact, and so is
`R(1 - Q') = ((1 - Q')R)*`.  Hence `R - Q'` and `Ψ - (P + Q)` are compact.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TightFormation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isStarProjection_starProjection (K : Submodule ℂ H) [K.HasOrthogonalProjection] :
    IsStarProjection K.starProjection :=
  ⟨K.isIdempotentElem_starProjection,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 K.starProjection_isSymmetric⟩

/-- An orthogonal projection splits the norm: `‖x‖² = ‖P x‖² + ‖x - P x‖²`. -/
theorem norm_sq_eq_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
  have hidem : P (P x) = P x := congrArg (fun T : H →L[ℂ] H => T x) hP.isIdempotentElem.eq
  have hsym : ∀ a b : H, ⟪P a, b⟫_ℂ = ⟪a, P b⟫_ℂ := hP.isSelfAdjoint.isSymmetric
  have horth : ⟪P x, x - P x⟫_ℂ = 0 := by
    rw [inner_sub_right, hsym x (P x), hidem, hsym x x, sub_self]
  have h := @norm_add_sq ℂ _ _ _ _ (P x) (x - P x)
  rw [horth, map_zero, mul_zero, add_zero, add_sub_cancel] at h
  exact h

/-- **Projection lift.**  If `P`, `Q` are orthogonal projections with `PQ` compact, there is an
orthogonal projection `Ψ` with `Ψ - (P + Q)` compact. -/
theorem exists_isStarProjection_compact_sub_add {P Q : H →L[ℂ] H} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (hPQ : IsCompactOperator (P ∘L Q)) :
    ∃ Ψ : H →L[ℂ] H, IsStarProjection Ψ ∧ IsCompactOperator (Ψ - (P + Q)) := by
  have hPidem : ∀ x, P (P x) = P x := fun x =>
    congrArg (fun T : H →L[ℂ] H => T x) hP.isIdempotentElem.eq
  have hQidem : ∀ x, Q (Q x) = Q x := fun x =>
    congrArg (fun T : H →L[ℂ] H => T x) hQ.isIdempotentElem.eq
  have hPsym : ∀ a b : H, ⟪P a, b⟫_ℂ = ⟪a, P b⟫_ℂ := hP.isSelfAdjoint.isSymmetric
  have hQsym : ∀ a b : H, ⟪Q a, b⟫_ℂ = ⟪a, Q b⟫_ℂ := hQ.isSelfAdjoint.isSymmetric
  obtain ⟨M, hMcl, hMfin, hMcon⟩ :=
    exists_finiteCodimensional_strictContractionKernel_of_isCompactOperator (P ∘L Q) hPQ
  haveI : CompleteSpace M := hMcl.completeSpace_coe
  set N : Submodule ℂ H := LinearMap.range (Q : H →ₗ[ℂ] H) with hN
  have hNcl : IsClosed (N : Set H) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range hQ.isIdempotentElem
  have hQN : ∀ v ∈ N, Q v = v := by
    rintro _ ⟨x, rfl⟩
    exact hQidem x
  set N' : Submodule ℂ H := N ⊓ M with hN'
  have hN'cl : IsClosed (N' : Set H) := hNcl.inter hMcl
  haveI : CompleteSpace N' := hN'cl.completeSpace_coe
  set Q' : H →L[ℂ] H := N'.starProjection with hQ'
  have hQ'proj : IsStarProjection Q' := isStarProjection_starProjection N'
  have hQ'sym : ∀ a b : H, ⟪Q' a, b⟫_ℂ = ⟪a, Q' b⟫_ℂ := hQ'proj.isSelfAdjoint.isSymmetric
  have hQ'mem : ∀ x, Q' x ∈ N' := N'.starProjection_apply_mem
  have hQ'fix : ∀ v ∈ N', Q' v = v := fun v hv => Submodule.starProjection_eq_self_iff.2 hv
  have hQQ' : ∀ x, Q (Q' x) = Q' x := fun x => hQN _ (hQ'mem x).1
  -- `P` is a strict contraction on `N'`
  have hsmall : ∀ x, ‖P (Q' x)‖ ≤ (1 / 2) * ‖Q' x‖ := fun x => by
    rcases eq_or_ne (Q' x) 0 with h | h
    · simp [h]
    · have := hMcon (Q' x) (hQ'mem x).2 h
      rw [ContinuousLinearMap.comp_apply, hQQ'] at this
      exact this.le
  -- `Q - Q'` has finite rank
  have hQcpt : IsCompactOperator (Q - Q') := by
    apply isCompactOperator_of_finiteDimensional_range
    have hW : FiniteDimensional ℂ (N ⊓ N'ᗮ : Submodule ℂ H) := by
      haveI : FiniteDimensional ℂ Mᗮ := hMfin
      let f : (N ⊓ N'ᗮ : Submodule ℂ H) →ₗ[ℂ] Mᗮ :=
        (Mᗮ.orthogonalProjectionOnto : H →L[ℂ] Mᗮ).toLinearMap.comp (Submodule.subtype _)
      refine Module.Finite.of_injective f ?_
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      have hwM : (w : H) ∈ M := by
        have h1 : (w : H) ∈ Mᗮᗮ := Submodule.orthogonalProjectionOnto_eq_zero_iff.1 hw
        rwa [Submodule.orthogonal_orthogonal] at h1
      have hwN' : (w : H) ∈ N' := ⟨w.2.1, hwM⟩
      have h0 : ⟪(w : H), (w : H)⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 w.2.2 _ hwN'
      exact Subtype.ext (inner_self_eq_zero.1 h0)
    refine Submodule.finiteDimensional_of_le (S₂ := N ⊓ N'ᗮ) ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨N.sub_mem (LinearMap.mem_range_self _ x) (hQ'mem x).1, ?_⟩
    show (Q - Q') x ∈ N'ᗮ
    rw [Submodule.mem_orthogonal]
    intro v hv
    change ⟪v, Q x - Q' x⟫_ℂ = 0
    rw [inner_sub_right, ← hQsym, hQN v hv.1, ← hQ'sym, hQ'fix v hv, sub_self]
  -- the operator `A = (1 - P) Q'` and its restriction to `N'`
  set A' : N' →L[ℂ] H := (1 - P) ∘L N'.subtypeL with hA'
  have hA'apply : ∀ v : N', A' v = (v : H) - P v := fun v => rfl
  have hA'bound : ∀ v : N', (1 / 2) * ‖v‖ ≤ ‖A' v‖ := fun v => by
    have hPv : ‖P (v : H)‖ ≤ (1 / 2) * ‖(v : H)‖ := by
      have := hsmall v
      rwa [hQ'fix v v.2] at this
    have hpy := norm_sq_eq_of_isStarProjection hP (v : H)
    rw [hA'apply, Submodule.coe_norm]
    have hsq : ((1 / 2) * ‖(v : H)‖) ^ 2 ≤ ‖(v : H) - P v‖ ^ 2 := by
      nlinarith [norm_nonneg (P (v : H)), norm_nonneg (v : H)]
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq
  have hA'inj : Function.Injective A' := fun v w hvw => by
    have h := hA'bound (v - w)
    rw [map_sub, hvw, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (by linarith [norm_nonneg (v - w)]))
  have hA'cl : IsClosed (Set.range A') := by
    rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range]
    exact ⟨1 / 2, by norm_num, fun x _ => hA'bound x⟩
  set Rg : Submodule ℂ H := LinearMap.range (A' : N' →ₗ[ℂ] H) with hRg
  haveI : CompleteSpace Rg := completeSpace_range hA'cl
  set R : H →L[ℂ] H := Rg.starProjection with hR
  have hRproj : IsStarProjection R := isStarProjection_starProjection Rg
  have hRsym : ∀ a b : H, ⟪R a, b⟫_ℂ = ⟪a, R b⟫_ℂ := hRproj.isSelfAdjoint.isSymmetric
  set L : H →L[ℂ] N' := moorePenrose A' hA'inj hA'cl with hL
  have hAQ' : ∀ x, (1 - P) (Q' x) = A' ⟨Q' x, hQ'mem x⟩ := fun x => rfl
  have hRA : ∀ x, R ((1 - P) (Q' x)) = (1 - P) (Q' x) := fun x =>
    Submodule.starProjection_eq_self_iff.2 (by rw [hAQ']; exact LinearMap.mem_range_self _ _)
  have hAB : ∀ y, (1 - P) (Q' (L (R y))) = R y := fun y => by
    obtain ⟨v, hv⟩ := Rg.starProjection_apply_mem y
    change A' v = R y at hv
    rw [← hv, hL, moorePenrose_apply_self, hQ'fix v v.2]
    rfl
  have hPR : ∀ y, P (R y) = 0 := fun y => by
    obtain ⟨v, hv⟩ := Rg.starProjection_apply_mem y
    change A' v = R y at hv
    rw [← hv, hA'apply, map_sub, hPidem, sub_self]
  have hRP : ∀ y, R (P y) = 0 := fun y => by
    refine ext_inner_right ℂ fun z => ?_
    rw [hRsym, hPsym, hPR, inner_zero_right, inner_zero_left]
  refine ⟨P + R, hP.add hRproj (ContinuousLinearMap.ext fun y => hPR y), ?_⟩
  -- compactness of `Ψ - (P + Q) = (R - Q') + (Q' - Q)`
  have hPQ' : IsCompactOperator (P ∘L Q') := by
    have h : (P ∘L Q' : H → H) = (P ∘L Q) ∘ Q' := funext fun x => by
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hQQ']
    rw [h]
    exact hPQ.comp_clm Q'
  have hRQ' : IsCompactOperator (R ∘L Q' - Q') := by
    have h : R ∘L Q' - Q' = R ∘L (P ∘L Q') - P ∘L Q' := by
      ext1 x
      have hsplit : Q' x = (1 - P) (Q' x) + P (Q' x) := by
        rw [sub_apply, one_apply_eq_self, sub_add_cancel]
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      conv_lhs => rw [hsplit, map_add, hRA]
      rw [sub_apply, one_apply_eq_self]
      abel
    rw [h]
    exact (hPQ'.clm_comp R).sub hPQ'
  have h1R : IsCompactOperator ((1 - Q') ∘L R) := by
    have h : (1 - Q') ∘L R = -((1 - Q') ∘L (P ∘L Q') ∘L N'.subtypeL ∘L L ∘L R) := by
      ext1 y
      set z : H := Q' (L (R y)) with hz
      have hy : z - P z = R y := hAB y
      have hQz : Q' z = z := hQ'fix _ (hQ'mem _)
      show (1 - Q') (R y) = -((1 - Q') (P z))
      rw [← hy]
      simp only [sub_apply, one_apply_eq_self, map_sub, hQz]
      abel
    have hc : IsCompactOperator ((1 - Q') ∘L (P ∘L Q') ∘L N'.subtypeL ∘L L ∘L R) := by
      have := (hPQ'.comp_clm (N'.subtypeL ∘L L ∘L R)).clm_comp (1 - Q')
      convert this using 1 <;> rfl
    rw [h]
    exact hc.neg
  have hR1 : IsCompactOperator (R ∘L (1 - Q')) := by
    have hadj : ContinuousLinearMap.adjoint ((1 - Q') ∘L R) = R ∘L (1 - Q') := by
      rw [ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.isSelfAdjoint_iff'.1 hRproj.isSelfAdjoint,
        ContinuousLinearMap.isSelfAdjoint_iff'.1
          ((IsSelfAdjoint.one _).sub hQ'proj.isSelfAdjoint)]
    rw [← hadj]
    exact RHTower.isCompactOperator_adjoint _ h1R
  have hfinal : P + R - (P + Q) = (R ∘L (1 - Q') + (R ∘L Q' - Q')) - (Q - Q') := by
    ext1 x
    simp only [add_apply, sub_apply,
      ContinuousLinearMap.comp_apply, one_apply_eq_self, map_sub]
    abel
  rw [hfinal]
  exact (hR1.add hRQ').sub hQcpt

end GaloisForLFunctions.HTGeometry.TightFormation
