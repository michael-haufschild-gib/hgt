import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.GlobalArtinEquivariance
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InverseArtinNorm

/-! Conjugation by a base Weil automorphism preserves the relative Weil
group. The inverse of local Artin is equivariant for this action. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  [NumberField L] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
  [w.asIdeal.LiesOver v.asIdeal] {hv : IsPlaceOver A v} {hw : IsPlaceOver A w}

def conjugateWeil (t : Weil hv) (s : Weil hw) : Weil hw := by
  let t₀ : Gal(Ω/K) := t.val
  let s₀ : Gal(Ω/L) := s.val
  let u := relativeAutConj K L Ω t₀ s₀
  have ht := Weil_le_Dec hv t.2
  have hs : s₀.restrictScalars K ∈ Dec (F := K) A :=
    mem_Dec.mpr (mem_Dec.mp (Weil_le_Dec hw s.2))
  have hu : u.restrictScalars K = t₀ * s₀.restrictScalars K * t₀⁻¹ :=
    AlgEquiv.ext fun _ => rfl
  have hdec : u ∈ Dec (F := L) A := by
    have h : u.restrictScalars K ∈ Dec (F := K) A := by
      rw [hu]
      exact (Dec (F := K) A).mul_mem ((Dec (F := K) A).mul_mem ht hs)
        ((Dec (F := K) A).inv_mem ht)
    exact mem_Dec.mpr (mem_Dec.mp h)
  refine ⟨u, ?_⟩
  obtain ⟨a, b, hab⟩ := s.2
  refine ⟨a, b, hdec, fun x hx => ?_⟩
  have hy := val_apply_le_one ((Dec (F := K) A).inv_mem ht) hx
  have h := (valuation_apply_lt_one_iff ht _).mpr (hab.2 _ hy)
  rw [map_sub, map_pow, map_pow, mul_inv_apply] at h
  exact h

@[simp] theorem weilRestrictScalars_conjugateWeil (t : Weil hv) (s : Weil hw) :
    weilRestrictScalars hv hw (conjugateWeil K Ω L t s) =
      t * weilRestrictScalars hv hw s * t⁻¹ :=
  Subtype.ext (AlgEquiv.ext fun _ => rfl)

theorem inverseArtin_conjugateWeil
    (b : CompactIdeleClassQuotient L →* Gal(maximalAbelianExtension L Ω/L))
    (hcb : Continuous b) (hb : MatchesFiniteIdelicArtin L Ω b)
    (β : Weil hw →* (w.adicCompletion L)ˣ)
    (hβ : ∀ s : Weil hw, b (toCompactIdeleClassQuotient L (finiteEmbedding w (β s))) =
      toMaxAb L Ω (s : Gal(Ω/L)))
    (t : Weil hv) (s : Weil hw)
    (ht : AlgEquiv.restrictNormalHom L t.val ∈ MulAction.stabilizer Gal(L/K) w.asIdeal) :
    β (conjugateWeil K Ω L t s) =
      Units.map (decompositionMulEquiv v w ⟨AlgEquiv.restrictNormalHom L t.val, ht⟩).toMonoidHom (β s) := by
  apply globalArtin_injective_finiteEmbedding b hcb hb w
  change b (toCompactIdeleClassQuotient L (finiteEmbedding w (β (conjugateWeil K Ω L t s)))) =
    b (toCompactIdeleClassQuotient L (finiteEmbedding w
      (Units.map (decompositionMulEquiv v w ⟨AlgEquiv.restrictNormalHom L t.val, ht⟩).toMonoidHom (β s))))
  rw [hβ]
  exact (globalArtin_finiteEmbedding_conjugate K Ω L v w b hb t.val ht (β s) s.val (hβ s)).symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.inverseArtin_conjugateWeil
