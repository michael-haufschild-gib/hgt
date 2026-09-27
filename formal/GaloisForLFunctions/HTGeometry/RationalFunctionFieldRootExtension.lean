import GaloisForLFunctions.HTGeometry.TwistedDerivationKernel
import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalStateEmbedding
import GaloisForLFunctions.HTGeometry.TranscendentalMobius

/-!
# Extending a field map across a transcendental and an algebraic generator

Let `E = F(X, v)` with `X` transcendental over `F` and `v` a root of `Q(X, W)`, where
`Q ∈ F[V][W]` is irreducible over `F(V)`.  Then `F(X) ≅ F(V)` and the minimal polynomial of `v`
over it is `Q(V, W)` up to a unit, so for every field map `ι : F → T`, every `τ ∈ T` transcendental
over `ι(F)` and every root `ρ` of `Q^ι(τ, W)` there is a field map `E → T` extending `ι` with
`X ↦ τ` and `v ↦ ρ`.

In characteristic zero the same presentation makes compatibility of derivations automatic on
`E` once it holds on `F` and at `X`: a derivation along a field map that kills `F` and `X` kills
`F(X)`, hence the separable algebraic `v`, hence `E`.
-/

open Polynomial IntermediateField

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem ratFuncEval_mem (X : E) (hX : Transcendental F X) (r : RatFunc F) :
    ratFuncEval X hX r ∈ F⟮X⟯ :=
  ((RatFunc.algEquivOfTranscendental X hX) r).2

theorem ratFuncEval_comp_algebraMap (X : E) (hX : Transcendental F X) :
    ((ratFuncEval X hX : RatFunc F →+* E)).comp (algebraMap (Polynomial F) (RatFunc F)) =
      eval₂RingHom (algebraMap F E) X := by
  apply Polynomial.ringHom_ext
  · intro c
    change ratFuncEval X hX (algebraMap (Polynomial F) (RatFunc F) (C c)) = eval₂ _ X (C c)
    rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, AlgHom.commutes, eval₂_C]
  · change ratFuncEval X hX (algebraMap (Polynomial F) (RatFunc F) Polynomial.X) = eval₂ _ X _
    rw [RatFunc.algebraMap_X, ratFuncEval_X, eval₂_X]

/-- The root `v` of `Q(X, W)` is integral over `F(X)`, and `Q` is its relation there. -/
theorem ratFuncEval_isIntegral_of_relIrr {X v : E} (hX : Transcendental F X)
    (Q : Polynomial (Polynomial F)) (hQ : Q.map (algebraMap (Polynomial F) (RatFunc F)) ≠ 0)
    (hv : Q.eval₂ (eval₂RingHom (algebraMap F E) X) v = 0) :
    letI : Algebra (RatFunc F) E := (ratFuncEval X hX : RatFunc F →+* E).toAlgebra
    IsIntegral (RatFunc F) v ∧ aeval v (Q.map (algebraMap (Polynomial F) (RatFunc F))) = 0 := by
  letI : Algebra (RatFunc F) E := (ratFuncEval X hX : RatFunc F →+* E).toAlgebra
  have hroot : aeval v (Q.map (algebraMap (Polynomial F) (RatFunc F))) = 0 := by
    rw [aeval_def, eval₂_map]
    change eval₂ (((ratFuncEval X hX : RatFunc F →+* E)).comp
      (algebraMap (Polynomial F) (RatFunc F))) v Q = 0
    rw [ratFuncEval_comp_algebraMap]
    exact hv
  exact ⟨IsAlgebraic.isIntegral ⟨_, hQ, hroot⟩, hroot⟩

/-- **Extension across `X` and `v`.** -/
theorem exists_ringHom_extension_of_relIrr {T : Type*} [Field T] {X v : E}
    (hX : Transcendental F X) (htop : adjoin F {X, v} = ⊤) (Q : Polynomial (Polynomial F))
    (hQ : Irreducible (Q.map (algebraMap (Polynomial F) (RatFunc F))))
    (hv : Q.eval₂ (eval₂RingHom (algebraMap F E) X) v = 0) (ι : F →+* T) {τ ρ : T}
    (hτ : Function.Injective (eval₂RingHom ι τ)) (hρ : Q.eval₂ (eval₂RingHom ι τ) ρ = 0) :
    ∃ ι' : E →+* T, ι'.comp (algebraMap F E) = ι ∧ ι' X = τ ∧ ι' v = ρ := by
  classical
  set J := ratFuncEval X hX with hJ
  letI algE : Algebra (RatFunc F) E := (J : RatFunc F →+* E).toAlgebra
  haveI : IsScalarTower F (RatFunc F) E :=
    IsScalarTower.of_algebraMap_eq fun c => (J.commutes c).symm
  let J' : RatFunc F →+* T := IsFractionRing.lift hτ
  letI algT : Algebra (RatFunc F) T := J'.toAlgebra
  have hJ'poly : J'.comp (algebraMap (Polynomial F) (RatFunc F)) = eval₂RingHom ι τ :=
    RingHom.ext fun p => IsFractionRing.lift_algebraMap hτ p
  obtain ⟨hint, hvroot⟩ := ratFuncEval_isIntegral_of_relIrr hX Q hQ.ne_zero hv
  have hmin := minpoly.eq_of_irreducible hQ hvroot
  have hρmin : eval₂ (algebraMap (RatFunc F) T) ρ (minpoly (RatFunc F) v) = 0 := by
    rw [← hmin, eval₂_mul, eval₂_map]
    change eval₂ (J'.comp (algebraMap (Polynomial F) (RatFunc F))) ρ Q * _ = 0
    rw [hJ'poly, hρ, zero_mul]
  obtain ⟨e₁, he₁⟩ := exists_adjoinSimple_algHom_of_minpoly_root v hint ρ hρmin
  have hXalg : X = algebraMap (RatFunc F) E RatFunc.X := (ratFuncEval_X X hX).symm
  have htop' : adjoin (RatFunc F) {v} = ⊤ := by
    rw [eq_top_iff]
    have hle : adjoin F {X, v} ≤ (adjoin (RatFunc F) {v}).restrictScalars F := by
      rw [adjoin_le_iff]
      rintro y (hy | hy)
      · rw [hy, hXalg]
        exact (adjoin (RatFunc F) {v}).algebraMap_mem _
      · rw [Set.mem_singleton_iff.mp hy]
        exact subset_adjoin (RatFunc F) {v} (Set.mem_singleton v)
    intro y _
    have hy : y ∈ adjoin F {X, v} := by
      rw [htop]
      trivial
    exact hle hy
  let ι' : E →ₐ[RatFunc F] T :=
    e₁.comp ((equivOfEq htop'.symm).toAlgHom.comp topEquiv.symm.toAlgHom)
  refine ⟨ι'.toRingHom, ?_, ?_, ?_⟩
  · refine RingHom.ext fun c => ?_
    change ι' (algebraMap F E c) = ι c
    rw [IsScalarTower.algebraMap_apply F (RatFunc F) E, ι'.commutes]
    change J' (algebraMap F (RatFunc F) c) = ι c
    rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, IsFractionRing.lift_algebraMap,
      coe_eval₂RingHom, eval₂_C]
  · change ι' X = τ
    rw [hXalg, ι'.commutes]
    change J' RatFunc.X = τ
    rw [← RatFunc.algebraMap_X, IsFractionRing.lift_algebraMap, coe_eval₂RingHom, eval₂_X]
  · change e₁ (equivOfEq htop'.symm (topEquiv.symm v)) = ρ
    have hgen : equivOfEq htop'.symm (topEquiv.symm v) = AdjoinSimple.gen (RatFunc F) v :=
      Subtype.ext rfl
    rw [hgen, he₁]

/-- **Derivation compatibility propagates across `X` and `v`.**  A derivation along a field map
that kills `F` and `X` kills `E = F(X, v)`. -/
theorem twisted_eq_zero_of_relIrr [CharZero F] {T : Type*} [Field T] {X v : E}
    (hX : Transcendental F X) (htop : adjoin F {X, v} = ⊤) (Q : Polynomial (Polynomial F))
    (hQ : Q.map (algebraMap (Polynomial F) (RatFunc F)) ≠ 0)
    (hv : Q.eval₂ (eval₂RingHom (algebraMap F E) X) v = 0) (ι : E →+* T) (D : E → T)
    (hadd : ∀ x y, D (x + y) = D x + D y) (hmul : ∀ x y, D (x * y) = ι x * D y + ι y * D x)
    (hF : ∀ c : F, D (algebraMap F E c) = 0) (hDX : D X = 0) (y : E) : D y = 0 := by
  letI : Algebra (RatFunc F) E := (ratFuncEval X hX : RatFunc F →+* E).toAlgebra
  let KI : IntermediateField F E :=
    (twistedKernel ι D hadd hmul).toIntermediateField fun c => hF c
  have hXK : F⟮X⟯ ≤ KI := adjoin_simple_le_iff.mpr hDX
  have hS : ∀ r : RatFunc F, D (algebraMap (RatFunc F) E r) = 0 := fun r =>
    hXK (ratFuncEval_mem X hX r)
  obtain ⟨hint, -⟩ := ratFuncEval_isIntegral_of_relIrr hX Q hQ hv
  have hDv : D v = 0 := twisted_eq_zero_of_isIntegral ι D hadd hmul hS hint
  have hle : adjoin F {X, v} ≤ KI := by
    rw [adjoin_le_iff]
    rintro z (hz | hz)
    · rw [hz]
      exact hDX
    · rw [Set.mem_singleton_iff.mp hz]
      exact hDv
  rw [htop] at hle
  exact hle (show y ∈ (⊤ : IntermediateField F E) from trivial)

end

end GaloisForLFunctions.HTGeometry
