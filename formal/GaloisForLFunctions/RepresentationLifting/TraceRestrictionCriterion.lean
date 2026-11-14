import GaloisForLFunctions.RepresentationLifting.CohomologicalTrace
import GaloisForLFunctions.RepresentationLifting.InternalHomExact

/-!
# A trace restriction criterion for group cohomology

For a short exact sequence `0 → A → P → C → 0`, a map `Φ : A → P`, and a
scalar cohomology class killed by the composite `A → P → C`, exactness produces
a class in the cohomology of `End(A)`. Its trace restricts to `trace(rΦ)` times
the original class wherever the inclusion admits an equivariant retraction `r`.

This is the argument of Scavia's Lemma 6.1 for ordinary group cohomology,
in every degree and without requiring `C = A`. No continuity or profinite
comparison is asserted here. Internal-Hom exactness and restriction naturality
are proved before extracting the trace class.
-/

noncomputable section
open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting
universe u

section Restriction

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- Restriction of the internal Hom has the expected conjugation action. -/
def internalHomRestriction (f : H →* G) (V W : Rep k G) :
    Rep.res f ((Rep.ihom V).obj W) ⟶
      (Rep.ihom (Rep.res f V)).obj (Rep.res f W) :=
  Rep.ofHom ⟨LinearMap.id, fun h => by
    apply LinearMap.ext
    intro T
    change V →ₗ[k] W at T
    apply LinearMap.ext
    intro v
    change W.ρ (f h) (T (V.ρ ((f h)⁻¹) v)) =
      W.ρ (f h) (T (V.ρ (f h⁻¹) v))
    rw [map_inv f h]⟩

/-- The functional `T ↦ trace(rT)` after restriction along a group homomorphism. -/
def restrictionHomTrace (f : H →* G) {V P : Rep k G}
    (r : Rep.res f P ⟶ Rep.res f V) :
    Rep.res f ((Rep.ihom V).obj P) ⟶ Rep.res f (Rep.trivial k G k) :=
  internalHomRestriction f V P ≫ (Rep.ihom (Rep.res f V)).map r ≫
    endomorphismTrace (Rep.res f V)

/-- A retraction recovers the trace on the original endomorphism representation. -/
theorem restrictionHomTrace_retraction (f : H →* G) {V P : Rep k G}
    (i : V ⟶ P) (r : Rep.res f P ⟶ Rep.res f V)
    (hr : (Rep.resFunctor f).map i ≫ r = 𝟙 _) :
    (Rep.resFunctor f).map ((Rep.ihom V).map i) ≫ restrictionHomTrace f r =
      (Rep.resFunctor f).map (endomorphismTrace V) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro T
  change V →ₗ[k] V at T
  change LinearMap.trace k V (r.hom.toLinearMap.comp (i.hom.toLinearMap.comp T)) =
    LinearMap.trace k V T
  have hri : r.hom.toLinearMap.comp i.hom.toLinearMap = LinearMap.id :=
    congrArg (fun m : Rep.res f V ⟶ Rep.res f V => m.hom.toLinearMap) hr
  rw [← LinearMap.comp_assoc, hri, LinearMap.id_comp]

/-- On the scalar line of `Φ`, the retraction functional is multiplication by `trace(rΦ)`. -/
theorem restrictionHomTrace_scalar (f : H →* G) {V P : Rep k G}
    (Φ : V ⟶ P) (r : Rep.res f P ⟶ Rep.res f V) :
    (Rep.resFunctor f).map (scalarHom Φ) ≫ restrictionHomTrace f r =
      LinearMap.trace k V (((Rep.resFunctor f).map Φ ≫ r).hom.toLinearMap) •
        𝟙 (Rep.res f (Rep.trivial k G k)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  change LinearMap.trace k V (r.hom.toLinearMap.comp (a • Φ.hom.toLinearMap)) =
    LinearMap.trace k V (r.hom.toLinearMap.comp Φ.hom.toLinearMap) • a
  rw [LinearMap.comp_smul, map_smul]
  exact mul_comm _ _

/-- Restriction and the retraction trace commute with the inclusion on cohomology. -/
theorem restrictionCohomology_trace_retraction (f : H →* G) {V P : Rep k G}
    (i : V ⟶ P) (r : Rep.res f P ⟶ Rep.res f V)
    (hr : (Rep.resFunctor f).map i ≫ r = 𝟙 _) (n : ℕ) :
    (groupCohomology.functor k G n).map ((Rep.ihom V).map i) ≫
        (groupCohomology.resNatTrans k f n).app ((Rep.ihom V).obj P) ≫
        (groupCohomology.functor k H n).map (restrictionHomTrace f r) =
      (groupCohomology.functor k G n).map (endomorphismTrace V) ≫
        (groupCohomology.resNatTrans k f n).app (Rep.trivial k G k) := by
  calc
    _ = (groupCohomology.resNatTrans k f n).app ((Rep.ihom V).obj V) ≫
        (groupCohomology.functor k H n).map ((Rep.resFunctor f).map ((Rep.ihom V).map i)) ≫
        (groupCohomology.functor k H n).map (restrictionHomTrace f r) :=
      (groupCohomology.resNatTrans k f n).naturality_assoc _ _
    _ = (groupCohomology.resNatTrans k f n).app ((Rep.ihom V).obj V) ≫
        (groupCohomology.functor k H n).map
          ((Rep.resFunctor f).map ((Rep.ihom V).map i) ≫ restrictionHomTrace f r) :=
      congrArg (fun m => (groupCohomology.resNatTrans k f n).app ((Rep.ihom V).obj V) ≫ m)
        ((groupCohomology.functor k H n).map_comp _ _).symm
    _ = (groupCohomology.resNatTrans k f n).app ((Rep.ihom V).obj V) ≫
        (groupCohomology.functor k H n).map ((Rep.resFunctor f).map (endomorphismTrace V)) :=
      congrArg (fun m => (groupCohomology.resNatTrans k f n).app ((Rep.ihom V).obj V) ≫
        (groupCohomology.functor k H n).map m) (restrictionHomTrace_retraction f i r hr)
    _ = _ := ((groupCohomology.resNatTrans k f n).naturality (endomorphismTrace V)).symm

/-- The scalar trace formula remains natural under restriction in every degree. -/
theorem restrictionCohomology_trace_scalar (f : H →* G) {V P : Rep k G}
    (Φ : V ⟶ P) (r : Rep.res f P ⟶ Rep.res f V) (n : ℕ) :
    (groupCohomology.functor k G n).map (scalarHom Φ) ≫
        (groupCohomology.resNatTrans k f n).app ((Rep.ihom V).obj P) ≫
        (groupCohomology.functor k H n).map (restrictionHomTrace f r) =
      LinearMap.trace k V (((Rep.resFunctor f).map Φ ≫ r).hom.toLinearMap) •
        (groupCohomology.resNatTrans k f n).app (Rep.trivial k G k) := by
  calc
    _ = (groupCohomology.resNatTrans k f n).app (Rep.trivial k G k) ≫
        (groupCohomology.functor k H n).map ((Rep.resFunctor f).map (scalarHom Φ)) ≫
        (groupCohomology.functor k H n).map (restrictionHomTrace f r) :=
      (groupCohomology.resNatTrans k f n).naturality_assoc _ _
    _ = (groupCohomology.resNatTrans k f n).app (Rep.trivial k G k) ≫
        (groupCohomology.functor k H n).map
          ((Rep.resFunctor f).map (scalarHom Φ) ≫ restrictionHomTrace f r) :=
      congrArg (fun m => (groupCohomology.resNatTrans k f n).app (Rep.trivial k G k) ≫ m)
        ((groupCohomology.functor k H n).map_comp _ _).symm
    _ = (groupCohomology.resNatTrans k f n).app (Rep.trivial k G k) ≫
        (groupCohomology.functor k H n).map
          (LinearMap.trace k V (((Rep.resFunctor f).map Φ ≫ r).hom.toLinearMap) •
            𝟙 (Rep.res f (Rep.trivial k G k))) :=
      congrArg (fun m => (groupCohomology.resNatTrans k f n).app (Rep.trivial k G k) ≫
        (groupCohomology.functor k H n).map m) (restrictionHomTrace_scalar f Φ r)
    _ = _ := by
      rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
      rfl

end Restriction

section Field

variable {k G : Type u} [Field k] [Group G]

/-- Exactness lifts a scalar-line class whose image in the quotient vanishes. -/
theorem scalarCohomology_lift (X : ShortComplex (Rep k G)) (hX : X.ShortExact)
    (V : Rep k G) (Φ : V ⟶ X.X₂) (n : ℕ)
    (b : groupCohomology (Rep.trivial k G k) n)
    (hb : ((groupCohomology.functor k G n).map (scalarHom (Φ ≫ X.g))).hom b = 0) :
    ∃ Γ : groupCohomology ((Rep.ihom V).obj X.X₁) n,
      ((groupCohomology.functor k G n).map ((Rep.ihom V).map X.f)).hom Γ =
        ((groupCohomology.functor k G n).map (scalarHom Φ)).hom b := by
  have hexact := (groupCohomology.mapShortComplex₂_exact
    (representationIHom_shortExact V X hX) n).moduleCat_range_eq_ker
  change LinearMap.range
      ((groupCohomology.functor k G n).map ((Rep.ihom V).map X.f)).hom =
    LinearMap.ker
      ((groupCohomology.functor k G n).map ((Rep.ihom V).map X.g)).hom at hexact
  have hcomp : (groupCohomology.functor k G n).map (scalarHom Φ) ≫
      (groupCohomology.functor k G n).map ((Rep.ihom V).map X.g) =
      (groupCohomology.functor k G n).map (scalarHom (Φ ≫ X.g)) := by
    rw [← CategoryTheory.Functor.map_comp, scalarHom_comp]
  have hbmem : ((groupCohomology.functor k G n).map (scalarHom Φ)).hom b ∈
      LinearMap.ker ((groupCohomology.functor k G n).map ((Rep.ihom V).map X.g)).hom :=
    (congrArg (fun m : groupCohomology (Rep.trivial k G k) n ⟶
      groupCohomology ((Rep.ihom V).obj X.X₃) n => m.hom b) hcomp).trans hb
  rw [← hexact] at hbmem
  exact hbmem


/-- A single global trace class satisfies the trace formula for every subgroup retraction. -/
theorem shortExact_cohomologyTrace_restriction
    (X : ShortComplex (Rep k G)) (hX : X.ShortExact) (Φ : X.X₁ ⟶ X.X₂)
    (n : ℕ) (b : groupCohomology (Rep.trivial k G k) n)
    (hb : ((groupCohomology.functor k G n).map (scalarHom (Φ ≫ X.g))).hom b = 0) :
    ∃ γ : groupCohomology (Rep.trivial k G k) n,
      ∀ (H : Subgroup G) (r : Rep.res H.subtype X.X₂ ⟶ Rep.res H.subtype X.X₁),
        (Rep.resFunctor H.subtype).map X.f ≫ r = 𝟙 _ →
        ((groupCohomology.resNatTrans k H.subtype n).app (Rep.trivial k G k)).hom γ =
          LinearMap.trace k X.X₁
            (((Rep.resFunctor H.subtype).map Φ ≫ r).hom.toLinearMap) •
          ((groupCohomology.resNatTrans k H.subtype n).app (Rep.trivial k G k)).hom b := by
  obtain ⟨Γ, hΓ⟩ := scalarCohomology_lift X hX X.X₁ Φ n b hb
  refine ⟨((groupCohomology.functor k G n).map (endomorphismTrace X.X₁)).hom Γ, ?_⟩
  intro H r hr
  have hl := congrArg
    (fun m : groupCohomology ((Rep.ihom X.X₁).obj X.X₁) n ⟶
      groupCohomology (Rep.res H.subtype (Rep.trivial k G k)) n => m.hom Γ)
    (restrictionCohomology_trace_retraction H.subtype X.f r hr n)
  have hr' := congrArg
    (fun m : groupCohomology (Rep.trivial k G k) n ⟶
      groupCohomology (Rep.res H.subtype (Rep.trivial k G k)) n => m.hom b)
    (restrictionCohomology_trace_scalar H.subtype Φ r n)
  exact hl.symm.trans ((congrArg (fun y =>
    ((groupCohomology.functor k H n).map (restrictionHomTrace H.subtype r)).hom
      (((groupCohomology.resNatTrans k H.subtype n).app ((Rep.ihom X.X₁).obj X.X₂)).hom y))
    hΓ).trans hr')

end Field

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.shortExact_cohomologyTrace_restriction
