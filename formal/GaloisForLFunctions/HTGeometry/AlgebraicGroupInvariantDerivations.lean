import GaloisForLFunctions.HTGeometry.AlgebraicGroupDerivationCoordinates
import GaloisForLFunctions.HTGeometry.MaurerCartanJetCoordinates
import GaloisForLFunctions.HTGeometry.SemilinearCircuitDescent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Translation-invariant derivations of the function field of an algebraic group

**Descent.**  A subspace `S ⊆ K^κ` (`κ` finite) stable under a family of field automorphisms acting
coordinatewise is spanned by its fixed vectors: a stable nonzero subspace contains a nonzero fixed
vector (least-support argument), and eliminating one of its nonzero coordinates reduces the
dimension.

**Invariant derivations.**  The tangent coordinates `Θ : Der_C(F) → F^r` of an integral
commutative algebraic group are `F`-linear, injective and equivariant (translations conjugate
derivations and act coordinatewise on `F^r`).  So `Θ(Der_C F)` is spanned by fixed vectors, and
their preimages are translation-invariant derivations spanning `Der_C F`.  Extracting a basis
gives `d = trdeg_C F` invariant derivations `D_i` with `det(D_i t_j) ≠ 0` for any transcendence
basis `t`.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-! ### Descent for coordinatewise stable subspaces -/

section Descent

variable {K κ I : Type*} [Field K] [Fintype κ] (σ : I → K ≃+* K)

/-- **A coordinatewise stable subspace is spanned by its fixed vectors.** -/
theorem le_span_fixed_of_stable (S : Submodule K (κ → K))
    (hS : ∀ i v, v ∈ S → (fun k => σ i (v k)) ∈ S) :
    S ≤ Submodule.span K {v | v ∈ S ∧ ∀ i, (fun k => σ i (v k)) = v} := by
  classical
  induction h : Module.finrank K S using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hS0 : S = ⊥
    · rw [hS0]
      exact bot_le
    -- a nonzero fixed vector
    let e := Finsupp.linearEquivFunOnFinite K K κ
    let W : Submodule K (κ →₀ K) := S.comap e.toLinearMap
    have hWstable : ∀ i v, v ∈ W → GaloisForLFunctions.finsuppMapRangeRingEquiv σ i v ∈ W := by
      intro i v hv
      change e _ ∈ S
      convert hS i (e v) hv using 1
      funext k
      simp [e, GaloisForLFunctions.finsuppMapRangeRingEquiv_apply]
    have hW0 : W ≠ ⊥ := by
      intro hW
      apply hS0
      rw [eq_bot_iff]
      intro v hv
      have : e.symm v ∈ W := by
        change e (e.symm v) ∈ S
        rwa [LinearEquiv.apply_symm_apply]
      rw [hW, Submodule.mem_bot] at this
      rw [Submodule.mem_bot, ← e.apply_symm_apply v, this, map_zero]
    obtain ⟨u, huW, hu0, hufix⟩ :=
      GaloisForLFunctions.stable_finsupp_submodule_exists_nonzero_fixed σ W hWstable hW0
    set v := e u with hv
    have hvS : v ∈ S := huW
    have hvfix : ∀ i, (fun k => σ i (v k)) = v := by
      intro i
      funext k
      have := congrArg (fun w : κ →₀ K => w k) (hufix i)
      simpa [v, e, GaloisForLFunctions.finsuppMapRangeRingEquiv_apply] using this
    have hv0 : v ≠ 0 := by
      intro h0
      apply hu0
      rw [← e.symm_apply_apply u, ← hv, h0, map_zero]
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv0 (funext hall)
    -- eliminate the `j`-th coordinate
    let S' : Submodule K (κ → K) := S ⊓ LinearMap.ker (LinearMap.proj j)
    have hS'stable : ∀ i w, w ∈ S' → (fun k => σ i (w k)) ∈ S' := by
      intro i w hw
      refine ⟨hS i w hw.1, ?_⟩
      have h0 : w j = 0 := hw.2
      change σ i (w j) = 0
      rw [h0, map_zero]
    have hlt : S' < S := by
      refine lt_of_le_of_ne inf_le_left fun heq => hj ?_
      have : v ∈ S' := heq ▸ hvS
      exact this.2
    have hrank : Module.finrank K S' < n := h ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hS'span := ih _ hrank S' hS'stable rfl
    have hmono : Submodule.span K {w | w ∈ S' ∧ ∀ i, (fun k => σ i (w k)) = w} ≤
        Submodule.span K {w | w ∈ S ∧ ∀ i, (fun k => σ i (w k)) = w} :=
      Submodule.span_mono fun w hw => ⟨hw.1.1, hw.2⟩
    intro s hs
    have hdecomp : s = (s - (s j / v j) • v) + (s j / v j) • v := by abel
    rw [hdecomp]
    refine Submodule.add_mem _ (hmono (hS'span ⟨S.sub_mem hs (S.smul_mem _ hvS), ?_⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨hvS, hvfix⟩))
    change s j - (s j / v j) * v j = 0
    rw [div_mul_cancel₀ _ hj, sub_self]

end Descent

/-! ### Invariant derivations -/

variable {C : Type u} [Field C] [CharZero C] (G : Over (Spec (.of C))) [GrpObj G]
  [IsCommMonObj G] [IsIntegral G.left] [LocallyOfFiniteType G.hom]

/-- A derivation commuting with every translation. -/
def IsTranslationInvariant (D : Derivation C G.left.functionField G.left.functionField) : Prop :=
  ∀ (x : 𝟙_ (Over (Spec (.of C))) ⟶ G) (f : G.left.functionField),
    D (translationAlgEquiv G x f) = translationAlgEquiv G x (D f)

omit [CharZero C] [IsCommMonObj G] [LocallyOfFiniteType G.hom] in
theorem isTranslationInvariant_of_conj
    {D : Derivation C G.left.functionField G.left.functionField}
    (h : ∀ x, conjDerivation (translationAlgEquiv G x) D = D) : IsTranslationInvariant G D := by
  intro x f
  have := congrArg (fun E : Derivation C G.left.functionField G.left.functionField =>
    E (translationAlgEquiv G x f)) (h x)
  simp only [conjDerivation_apply, AlgEquiv.symm_apply_apply] at this
  exact this.symm

omit [CharZero C] in
/-- **The translation-invariant derivations span all derivations.** -/
theorem span_translationInvariant_eq_top :
    Submodule.span G.left.functionField {D | IsTranslationInvariant G D} = ⊤ := by
  rw [eq_top_iff]
  intro D _
  let T := tangentCoordsLinear G
  let σ : (𝟙_ (Over (Spec (.of C))) ⟶ G) → G.left.functionField ≃+* G.left.functionField :=
    fun x => (translationAlgEquiv G x).toRingEquiv
  have hTσ : ∀ x E, (fun k => σ x (T E k)) = T (conjDerivation (translationAlgEquiv G x) E) := by
    intro x E
    funext k
    exact (tangentCoords_conjDerivation G x E k).symm
  have hstable : ∀ x v, v ∈ LinearMap.range T → (fun k => σ x (v k)) ∈ LinearMap.range T := by
    rintro x _ ⟨E, rfl⟩
    exact ⟨_, (hTσ x E).symm⟩
  have hspan := le_span_fixed_of_stable σ (LinearMap.range T) hstable ⟨D, rfl⟩
  have hfixed : {v | v ∈ LinearMap.range T ∧ ∀ x, (fun k => σ x (v k)) = v} ⊆
      T '' {D | IsTranslationInvariant G D} := by
    rintro _ ⟨⟨E, rfl⟩, hE⟩
    refine ⟨E, isTranslationInvariant_of_conj G fun x => ?_, rfl⟩
    apply tangentCoordsLinear_injective G
    exact (hTσ x E).symm.trans (hE x)
  have hmem := Submodule.span_mono hfixed hspan
  rw [Submodule.span_image] at hmem
  obtain ⟨E, hE, hTE⟩ := hmem
  rwa [← tangentCoordsLinear_injective G hTE]

/-- **A basis of translation-invariant derivations.**  For every transcendence basis `t` of the
function field there are `d` translation-invariant derivations `D_i` with `det(D_i t_j) ≠ 0`. -/
theorem exists_translationInvariant_derivationMatrix_det_ne_zero {d : ℕ}
    {t : Fin d → G.left.functionField} (ht : IsTranscendenceBasis C t) :
    ∃ D : Fin d → Derivation C G.left.functionField G.left.functionField,
      (∀ i, IsTranslationInvariant G (D i)) ∧ (derivationMatrix D t).det ≠ 0 := by
  classical
  -- values on the transcendence basis
  let E : Derivation C G.left.functionField G.left.functionField →ₗ[G.left.functionField]
      (Fin d → G.left.functionField) :=
    { toFun := fun D j => D (t j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsum : ∀ (f : Fin d → Derivation C G.left.functionField G.left.functionField)
      (a : G.left.functionField), (∑ j, f j) a = ∑ j, f j a := fun f a => by
    rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    rfl
  have hEsurj : Function.Surjective E := by
    intro v
    refine ⟨∑ j, v j • jetPartial ht j, ?_⟩
    funext k
    change (∑ j, v j • jetPartial ht j) (t k) = v k
    rw [hsum]
    simp only [Derivation.smul_apply, jetPartial_apply_basis, smul_eq_mul]
    simp
  have hspanE : Submodule.span G.left.functionField (E '' {D | IsTranslationInvariant G D}) = ⊤ := by
    have h1 := congrArg (Submodule.map E) (span_translationInvariant_eq_top G)
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hEsurj] at h1
    exact h1
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent G.left.functionField
    (E '' {D | IsTranslationInvariant G D})
  rw [hspanE] at hbspan
  let B := Module.Basis.mk hbind (by rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hbspan])
  letI : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = d := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let eb : Fin d ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ i : Fin d, ∃ D, IsTranslationInvariant G D ∧
      E D = (eb i : Fin d → G.left.functionField) := by
    intro i
    obtain ⟨D, hD, hDE⟩ := hbsub (eb i).2
    exact ⟨D, hD, hDE⟩
  choose D hDinv hDE using hpre
  refine ⟨D, hDinv, ?_⟩
  have hrows : LinearIndependent G.left.functionField (fun i => derivationMatrix D t i) := by
    have : (fun i => derivationMatrix D t i) =
        (fun c : b => (c : Fin d → G.left.functionField)) ∘ eb := by
      funext i
      rw [Function.comp_apply, ← hDE i]
      rfl
    rw [this]
    exact hbind.comp eb eb.injective
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
  exact Matrix.linearIndependent_rows_iff_isUnit.mp hrows

end

end GaloisForLFunctions.HTGeometry
