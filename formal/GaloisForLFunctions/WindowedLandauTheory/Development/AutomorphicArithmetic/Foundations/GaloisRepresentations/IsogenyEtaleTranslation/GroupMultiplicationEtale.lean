import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GroupTangentCriteria
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.FiniteEtaleSourceDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.FiniteEtaleFibrePower
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! Multiplication by an invertible integer on a smooth proper
commutative group scheme with geometrically connected fibres is finite,
étale, and surjective. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.GrpTangent

open TangentCrit

variable {S : Scheme.{0}}

/-- Multiplication by a natural number on a group scheme. -/
def mulN (G : Over S) [GrpObj G] (n : ℕ) : G ⟶ G := 𝟙 G ^ n

theorem comp_mulN {G T : Over S} [GrpObj G] (x : T ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  rw [mulN, comp_pow, Category.comp_id]

instance isMonHom_mulN (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom (mulN G n) where
  one_hom := by rw [comp_mulN, one_eq_one, one_pow]
  mul_hom := by
    rw [comp_mulN, mul_eq_mul, comp_mul, mul_pow]
    congr 1 <;> simp [comp_mulN]

theorem pullback_map_mulN {S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (n : ℕ) :
    (Over.pullback p).map (mulN G n) = mulN ((Over.pullback p).obj G) n := by
  calc
    _ = ((Over.pullback p).map (𝟙 G)) ^ n := map_pow (Over.pullback p).homMonoidHom _ _
    _ = _ := congrArg (· ^ n) ((Over.pullback p).map_id G)

private theorem isPullback_baseChange {S T : Scheme.{0}} (t : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom t) ((Over.pullback t).map f).left f.left
      (pullback.fst Y.hom t) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom t) (v₂₂ := Y.hom) (h₃₁ := t) ?_ ?_
    (IsPullback.of_hasPullback Y.hom t)
  · let m : pullback X.hom t ⟶ pullback Y.hom t := ((Over.pullback t).map f).left
    have h1 : m ≫ pullback.snd Y.hom t = pullback.snd X.hom t :=
      pullback.lift_snd _ _ _
    change IsPullback (pullback.fst X.hom t) (m ≫ pullback.snd Y.hom t) (f.left ≫ Y.hom) t
    rw [h1, Over.w f]
    exact IsPullback.of_hasPullback X.hom t
  · exact (pullback.lift_fst _ _ _).symm

private theorem surjective_of_geomFibres {S : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Surjective ((Over.pullback t).map f).left) : Surjective f.left := by
  refine ⟨fun y => ?_⟩
  let K := AlgebraicClosure (Y.left.residueField y)
  let u : Spec (CommRingCat.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let t := u ≫ Y.hom
  have hs := h K t
  let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let v : Spec (CommRingCat.of K) ⟶ pullback Y.hom t := pullback.lift u (𝟙 _) (by simp [t])
  obtain ⟨x, hx⟩ := ((Over.pullback t).map f).left.surjective (v p)
  refine ⟨pullback.fst X.hom t x, ?_⟩
  have e := (isPullback_baseChange t f).w
  have e1 : f.left (pullback.fst X.hom t x) =
      pullback.fst Y.hom t (((Over.pullback t).map f).left x) :=
    congrArg (fun m : pullback X.hom t ⟶ Y.left => m x) e
  rw [e1, hx, ← Scheme.Hom.comp_apply]
  have : v ≫ pullback.fst Y.hom t = u := pullback.lift_fst _ _ _
  rw [this]
  exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply y _)

theorem tangentMap_mulN_bijective {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] {n : ℕ} (hn : IsUnit (n : R)) : Function.Bijective (tangentMap (mulN G n)) := by
  obtain ⟨u, hu⟩ := hn
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun w => ⟨epsScale (↑u⁻¹ : R) ≫ w.1, isTangent_epsScale _ w.2⟩, fun w => Subtype.ext ?_,
      fun w => Subtype.ext ?_⟩
  · simp only [tangentMap_coe]
    rw [comp_mulN, pow_eq_epsScale_comp w.2, epsScale_mul_assoc, ← hu, Units.inv_mul, epsScale_one,
      Category.id_comp]
  · simp only [tangentMap_coe]
    rw [comp_mulN, pow_eq_epsScale_comp (isTangent_epsScale _ w.2), epsScale_mul_assoc, ← hu,
      Units.mul_inv, epsScale_one, Category.id_comp]

variable (G : Over S) [GrpObj G]

lemma isUnit_natCast_of_point {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) {R : Type} [CommRing R]
    (p : Sp R ⟶ S) : IsUnit (n : R) := by
  simpa using hn.map (p.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom).hom

lemma tangentMap_pullback_mulN_bijective [IsCommMonObj G] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    {R : Type} [CommRing R] (p : Sp R ⟶ S) :
    Function.Bijective (tangentMap ((Over.pullback p).map (mulN G n))) := by
  convert tangentMap_mulN_bijective ((Over.pullback p).obj G) (isUnit_natCast_of_point hn p) using 2
  exact pullback_map_mulN p G n

theorem etale_mulN [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    Etale (mulN G n).left :=
  etale_of_tangentMap_bijective _ fun _ _ _ p => tangentMap_pullback_mulN_bijective G hn p

/-- Properness makes the invertible multiplication map finite.
Its image on each geometric fibre is nonempty, open, and closed. -/
theorem finiteEtaleSurjective_mulN [IsCommMonObj G] [Smooth G.hom] [IsProper G.hom]
    [GeometricallyConnected G.hom] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    IsFinite (mulN G n).left ∧ Etale (mulN G n).left ∧ Surjective (mulN G n).left := by
  let f := mulN G n
  haveI : Etale f.left := etale_mulN G hn
  haveI : IsProper (f.left ≫ G.hom) := (Over.w f).symm ▸ inferInstance
  haveI : IsProper f.left := IsProper.of_comp f.left G.hom
  haveI : LocallyQuasiFinite f.left := locallyQuasiFinite_of_formallyUnramified f.left
  haveI : IsFinite f.left := IsFinite.of_isProper_of_locallyQuasiFinite f.left
  refine ⟨inferInstance, inferInstance, surjective_of_geomFibres f fun K _ _ t => ?_⟩
  let g := ((Over.pullback t).map f).left
  haveI : IsFinite g := MorphismProperty.of_isPullback (isPullback_baseChange t f) ‹IsFinite f.left›
  haveI : Etale g := MorphismProperty.of_isPullback (isPullback_baseChange t f) ‹Etale f.left›
  haveI : ConnectedSpace ((Over.pullback t).obj G).left := by
    change ConnectedSpace ↥(pullback G.hom t)
    exact GeometricallyConnected.geometrically_connectedSpace _ _ _ (IsPullback.of_hasPullback G.hom t)
  have hcl : IsClopen (Set.range g) := ⟨g.isClosedMap.isClosed_range, g.isOpenMap.isOpen_range⟩
  exact ⟨Set.range_eq_univ.mp (hcl.eq_univ (Set.range_nonempty g))⟩

/-- Invertible scalar multiplication on a fibre power is finite étale
and surjective. -/
theorem finiteEtaleSurjective_mulN_fibrePower [IsCommMonObj G] [Smooth G.hom] [IsProper G.hom]
    [GeometricallyConnected G.hom] (r : ℕ) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    let f := Limits.Pi.map (fun _ : Fin r => mulN G n)
    IsFinite f.left ∧ Etale f.left ∧ Surjective f.left :=
  finiteEtaleSurjective_fibrePower_map G _ (fun _ => finiteEtaleSurjective_mulN G hn)

/-- A map with a two-sided quasi-inverse up to invertible multiplication
between abelian schemes is finite, étale, and surjective. -/
theorem finiteEtaleSurjective_of_quasiInverse {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B] [Smooth A.hom] [Smooth B.hom]
    [IsProper A.hom] [IsProper B.hom] [GeometricallyConnected A.hom] [GeometricallyConnected B.hom]
    {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) (f : A ⟶ B) (g : B ⟶ A)
    (hA : f ≫ g = mulN A n) (hB : g ≫ f = mulN B n) :
    IsFinite f.left ∧ Etale f.left ∧ Surjective f.left := by
  have ea : f.left ≫ g.left = (mulN A n).left := congrArg Over.Hom.left hA
  have eb : g.left ≫ f.left = (mulN B n).left := congrArg Over.Hom.left hB
  obtain ⟨ha₁, ha₂, -⟩ := finiteEtaleSurjective_mulN A hn
  obtain ⟨hb₁, hb₂, hb₃⟩ := finiteEtaleSurjective_mulN B hn
  haveI : IsFinite (f.left ≫ g.left) := ea.symm ▸ ha₁
  haveI : Etale (f.left ≫ g.left) := ea.symm ▸ ha₂
  haveI : IsFinite (g.left ≫ f.left) := eb.symm ▸ hb₁
  haveI : Etale (g.left ≫ f.left) := eb.symm ▸ hb₂
  haveI : Surjective (g.left ≫ f.left) := eb.symm ▸ hb₃
  haveI : IsProper (g.left ≫ A.hom) := (Over.w g).symm ▸ inferInstance
  haveI : IsProper g.left := IsProper.of_comp g.left A.hom
  obtain ⟨hfinite, hetale⟩ := finiteEtale_of_consecutive_composites f.left g.left f.left
  exact ⟨hfinite, hetale, Surjective.of_comp g.left f.left⟩

/-- A positive integer is a unit in the global sections of a scheme
over a rational algebra. -/
theorem isUnit_natCast_of_overRat {R : Type} [CommRing R] [Algebra ℚ R]
    (s : S ⟶ Spec (CommRingCat.of R)) {n : ℕ} (hn : 0 < n) :
    IsUnit (n : Γ(S, ⊤)) := by
  have hq : IsUnit (n : ℚ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hn.ne')
  have hR : IsUnit (n : R) := by simpa using hq.map (algebraMap ℚ R)
  simpa using hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom

end GlobalTheory.GrpTangent
