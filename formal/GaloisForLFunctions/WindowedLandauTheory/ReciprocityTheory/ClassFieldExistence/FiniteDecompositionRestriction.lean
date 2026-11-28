import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FinitePrimeHilbertFields

/-! Restriction to a Galois subextension maps the decomposition group
onto the decomposition group of the prime below. -/

noncomputable section

open NumberField IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.Reciprocity

variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [IsGalois K E] [IsGalois K L]

local notation "G" => Gal(L/K)
local notation "H" => Gal(E/K)

private theorem under_smul_restrictNormal (P : Ideal (𝓞 L)) (σ : G) :
    (σ • P).under (𝓞 E) = (AlgEquiv.restrictNormalHom E σ : H) • P.under (𝓞 E) := by
  let r : G →* H := AlgEquiv.restrictNormalHom E
  have he (τ : G) (x : 𝓞 E) : algebraMap (𝓞 E) (𝓞 L) (r τ • x) =
      τ • algebraMap (𝓞 E) (𝓞 L) x :=
    RingOfIntegers.ext (τ.restrictNormal_commutes E (x : E))
  refine Ideal.ext fun x => ?_
  change algebraMap (𝓞 E) (𝓞 L) x ∈ σ • P ↔ x ∈ r σ • P.under (𝓞 E)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    ← map_inv r]
  change σ⁻¹ • algebraMap (𝓞 E) (𝓞 L) x ∈ P ↔
    algebraMap (𝓞 E) (𝓞 L) (r σ⁻¹ • x) ∈ P
  rw [he]

theorem map_stabilizer_restrictNormalHom (w : HeightOneSpectrum (𝓞 L)) :
    (MulAction.stabilizer G w.asIdeal).map (AlgEquiv.restrictNormalHom E) =
      MulAction.stabilizer H (w.under (𝓞 E)).asIdeal := by
  let r : G →* H := AlgEquiv.restrictNormalHom E
  let P := w.asIdeal
  let Q := P.under (𝓞 E)
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    change r σ ∈ MulAction.stabilizer H Q
    rw [MulAction.mem_stabilizer_iff, ← under_smul_restrictNormal K E L P σ]
    rw [MulAction.mem_stabilizer_iff.mp hσ]
  intro τ hτ
  obtain ⟨σ, hσ⟩ := (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (E := L)) τ
  have hQ : (σ • P).under (𝓞 E) = P.under (𝓞 E) := by
    rw [under_smul_restrictNormal K E L P σ, hσ]
    exact MulAction.mem_stabilizer_iff.mp hτ
  letI : IsGalois E L := .tower_top_of_isGalois K E L
  letI : P.IsPrime := w.isPrime
  letI : (σ • P).IsPrime := Ideal.IsPrime.smul σ
  obtain ⟨γ, hγ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 E) (𝓞 L) Gal(L/E)
    (σ • P) P hQ
  have hr (δ : Gal(L/E)) : r (δ.restrictScalars K) = 1 := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E L).injective
    exact ((δ.restrictScalars K).restrictNormal_commutes E x).trans (δ.commutes x)
  refine ⟨γ.restrictScalars K * σ, ?_, ?_⟩
  · change γ.restrictScalars K * σ ∈ MulAction.stabilizer G P
    apply MulAction.mem_stabilizer_iff.mpr
    rw [mul_smul]
    exact hγ.symm
  · change r (γ.restrictScalars K * σ) = τ
    rw [map_mul, hr, one_mul]
    exact hσ

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.map_stabilizer_restrictNormalHom
