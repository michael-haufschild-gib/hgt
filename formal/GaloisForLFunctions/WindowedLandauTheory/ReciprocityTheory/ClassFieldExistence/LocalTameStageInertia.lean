import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalTameStage
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InertiaRestrictionUnramifiedArbitrary

/-! The rational uniformizer condition forces ramification index one
over the base. Restriction is then an isomorphism on absolute inertia. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField WithZero
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Reciprocity

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}
  {p n : ℕ} [Fact p.Prime] (D : LocalTameStage h p n)

theorem LocalTameStage.natCast_mem : (p : 𝓞 D.L) ∈ D.w.asIdeal := by
  have hmem := Ideal.absNorm_mem D.w.asIdeal
  change (normV D.w : 𝓞 D.L) ∈ D.w.asIdeal at hmem
  rw [D.cardinality, Nat.cast_pow] at hmem
  exact D.w.isPrime.mem_of_pow_mem n hmem

include D in
theorem LocalTameStage.base_natCast_mem : (p : 𝓞 K) ∈ v.asIdeal := by
  apply (h _).mp
  have hp := (D.hw _).mpr D.natCast_mem
  simpa only [map_natCast] using hp

theorem LocalTameStage.place_eq :
    finitePlaceAtAbsoluteValuation (L := D.L) A h = D.w := by
  apply HeightOneSpectrum.ext
  exact Ideal.ext fun x =>
    (finitePlaceAtAbsoluteValuation_isPlaceOver (L := D.L) A h x).symm.trans (D.hw x)

theorem LocalTameStage.ramificationIdx_one : D.w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  letI : D.w.asIdeal.LiesOver v.asIdeal := D.place_eq ▸ finitePlaceAtAbsoluteValuation_liesOver (L := D.L) A h
  have hmap : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 D.L)) v.asIdeal ≤ D.w.asIdeal ^ 2 := fun hle => D.uniformizer (by
    have hh := hle (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 D.L)) D.base_natCast_mem)
    rwa [map_natCast] at hh)
  have hlt := Ideal.ramificationIdx'_lt hmap
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal D.w.asIdeal v.ne_bot] at hlt
  have hp := Ideal.ramificationIdx_pos D.w.asIdeal (𝓞 K)
  omega

def LocalTameStage.inertiaEquiv : Ine (F := D.L) A ≃* Ine (F := K) A :=
  MulEquiv.ofBijective (inertiaRestrictScalars (K := K) (L := D.L) (A := A)) (by
    refine ⟨fun x y e => Subtype.ext (AlgEquiv.restrictScalars_injective K (congrArg Subtype.val e)), ?_⟩
    intro t
    have he : (finitePlaceAtAbsoluteValuation (L := D.L) A h).asIdeal.ramificationIdx (𝓞 K) = 1 := by
      rw [D.place_eq]
      exact D.ramificationIdx_one
    let s : Gal(Ω/D.L) := { t.val.toRingEquiv with
      commutes' := absoluteInertia_fixes_of_unramified_extension K Ω D.L h he t }
    have hs : s ∈ Ine (F := D.L) A := ⟨mem_Dec.mpr (mem_Dec.mp t.2.1), t.2.2⟩
    exact ⟨⟨s, hs⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩)

theorem LocalTameStage.continuous_inertiaEquiv_symm : Continuous D.inertiaEquiv.symm := by
  letI := compactSpace_Ine (E := D.L) A
  letI : T2Space Gal(Ω/K) := krullTopology_t2
  let e := D.inertiaEquiv.toEquiv
  have hc : Continuous e := continuous_inertiaRestrictScalars (K := K) (L := D.L) (A := A)
  exact (hc.homeoOfEquivCompactToT2 (f := e)).symm.continuous

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.LocalTameStage.inertiaEquiv
#print axioms GlobalTheory.Reciprocity.LocalTameStage.continuous_inertiaEquiv_symm
