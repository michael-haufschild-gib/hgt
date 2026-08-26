import GaloisForLFunctions.HTGeometry.KaehlerFieldTowerInjective
import GaloisForLFunctions.HTGeometry.KaehlerFractionRingDenominator

/-!
# Generic vanishing of Kähler differentials under an injective field-valued point

This file packages pullback on Kähler differentials along an algebra homomorphism without exposing
the induced target algebra instance.  For an injective homomorphism from a domain to a
characteristic-zero field, vanishing after pullback implies that one nonzero element of the domain
annihilates the original differential.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped nonZeroDivisors

/-- Algebra structure on a target induced by an algebra homomorphism. -/
@[reducible] noncomputable def algHomTargetAlgebra
    {k R L : Type*} [CommRing k] [CommRing R] [CommRing L]
    [Algebra k R] [Algebra k L] (f : R →ₐ[k] L) : Algebra R L :=
  f.toRingHom.toAlgebra

/-- Pullback on Kähler differentials along an algebra homomorphism, restricted to the base
ring so that its type is independent of the induced target algebra instance. -/
noncomputable def algHomKaehlerMap
    {k R L : Type*} [CommRing k] [CommRing R] [CommRing L]
    [Algebra k R] [Algebra k L] (f : R →ₐ[k] L) :
    Ω[R⁄k] →ₗ[k] Ω[L⁄k] := by
  letI : Algebra R L := algHomTargetAlgebra f
  letI : IsScalarTower k R L :=
    IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  exact (KaehlerDifferential.map k k R L).restrictScalars k

theorem algHomKaehlerMap_D
    {k R L : Type*} [CommRing k] [CommRing R] [CommRing L]
    [Algebra k R] [Algebra k L] (f : R →ₐ[k] L) (r : R) :
    algHomKaehlerMap f (KaehlerDifferential.D k R r) =
      KaehlerDifferential.D k L (f r) := by
  letI : Algebra R L := algHomTargetAlgebra f
  letI : IsScalarTower k R L :=
    IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  unfold algHomKaehlerMap
  change KaehlerDifferential.map k k R L (KaehlerDifferential.D k R r) = _
  rw [KaehlerDifferential.map_D]
  rfl

theorem algHomKaehlerMap_smul
    {k R L : Type*} [CommRing k] [CommRing R] [CommRing L]
    [Algebra k R] [Algebra k L] (f : R →ₐ[k] L)
    (r : R) (w : Ω[R⁄k]) :
    algHomKaehlerMap f (r • w) = f r • algHomKaehlerMap f w := by
  letI : Algebra R L := algHomTargetAlgebra f
  letI : IsScalarTower k R L :=
    IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  unfold algHomKaehlerMap
  change KaehlerDifferential.map k k R L (r • w) = _
  rw [map_smul]
  rfl

/-- Kähler pullback along algebra homomorphisms is contravariantly functorial. -/
theorem algHomKaehlerMap_comp
    {k R S L : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing L]
    [Algebra k R] [Algebra k S] [Algebra k L]
    (g : S →ₐ[k] L) (f : R →ₐ[k] S) (w : Ω[R⁄k]) :
    algHomKaehlerMap (g.comp f) w =
      algHomKaehlerMap g (algHomKaehlerMap f w) := by
  have hw : w ∈ Submodule.span R
      (Set.range (KaehlerDifferential.D k R)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨r, rfl⟩
    simp only [algHomKaehlerMap_D]
    rfl
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · intro r x _ hx
    rw [algHomKaehlerMap_smul, algHomKaehlerMap_smul,
      algHomKaehlerMap_smul, hx]
    rfl

/-- A differential over a domain that vanishes after an injective map into a
characteristic-zero field is killed by one nonzero denominator in the domain. -/
theorem exists_nonzero_smul_eq_zero_of_algHomKaehlerMap_eq_zero
    {k R L : Type*} [Field k] [CommRing R] [IsDomain R] [Field L]
    [Algebra k R] [Algebra k L] [CharZero k]
    (f : R →ₐ[k] L) (hf : Function.Injective f) {w : Ω[R⁄k]}
    (h : algHomKaehlerMap f w = 0) :
    ∃ s : R, s ≠ 0 ∧ s • w = 0 := by
  let F := FractionRing R
  letI iRL : Algebra R L := algHomTargetAlgebra f
  letI : IsScalarTower k R L :=
    IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  let jRing : F →+* L := IsFractionRing.lift hf
  letI iFL : Algebra F L := jRing.toAlgebra
  letI : IsScalarTower k F L :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k L c = jRing (algebraMap k F c)
      rw [IsScalarTower.algebraMap_apply k R F,
        IsFractionRing.lift_algebraMap]
      exact (f.commutes c).symm
  letI : IsScalarTower R F L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change f r = jRing (algebraMap R F r)
      rw [IsFractionRing.lift_algebraMap]
      rfl
  have hcompat (z : Ω[R⁄k]) :
      KaehlerDifferential.map k k R L z =
        KaehlerDifferential.map k k F L
          (KaehlerDifferential.map k k R F z) := by
    have hz : z ∈ Submodule.span R
        (Set.range (KaehlerDifferential.D k R)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨r, rfl⟩
      simp only [KaehlerDifferential.map_D]
      rw [IsScalarTower.algebraMap_apply R F L]
    · simp
    · intro x y _ _ hx hy
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
    · intro r x _ hx
      calc
        KaehlerDifferential.map k k R L (r • x) =
            r • KaehlerDifferential.map k k R L x := by rw [map_smul]
        _ = r • KaehlerDifferential.map k k F L
              (KaehlerDifferential.map k k R F x) := congrArg (r • ·) hx
        _ = (algebraMap R F r) • KaehlerDifferential.map k k F L
              (KaehlerDifferential.map k k R F x) := by
                exact (IsScalarTower.algebraMap_smul F r _).symm
        _ = KaehlerDifferential.map k k F L
              ((algebraMap R F r) • KaehlerDifferential.map k k R F x) := by
                rw [map_smul]
        _ = KaehlerDifferential.map k k F L
              (KaehlerDifferential.map k k R F (r • x)) := by
                rw [(KaehlerDifferential.map k k R F).map_smul]
                congr 1
                exact IsScalarTower.algebraMap_smul F r _
  have hdirect : KaehlerDifferential.map k k R L w = 0 := by
    unfold algHomKaehlerMap at h
    change KaehlerDifferential.map k k R L w = 0 at h
    exact h
  have hgeneric : KaehlerDifferential.map k k F L
      (KaehlerDifferential.map k k R F w) = 0 := by
    rw [← hcompat]
    exact hdirect
  have hfrac : KaehlerDifferential.map k k R F w = 0 :=
    kaehlerMap_injective_of_fieldTower hgeneric
  exact exists_nonzero_smul_eq_zero_of_map_fractionRing_eq_zero hfrac

end

end GaloisForLFunctions.HTGeometry
