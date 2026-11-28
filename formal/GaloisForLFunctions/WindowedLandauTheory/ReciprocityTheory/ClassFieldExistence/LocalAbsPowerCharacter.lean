import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinData
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InverseArtinOnWeilGroup

/-! Real powers of the normalized absolute value on a completion
are smooth characters. Geometric inverse Artin pulls them back
to the corresponding unramified Weil characters. -/

noncomputable section

open NumberField IsDedekindDomain Multiplicative WithZero GaloisForLFunctions.HTGeometry
open scoped WithZero
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Reciprocity

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

local notation "Fv" => HeightOneSpectrum.adicCompletion K v

/-- A real power of the normalized local absolute value. -/
def completionAbsPow (v : HeightOneSpectrum (𝓞 K)) (s : ℝ) : (v.adicCompletion K)ˣ →* ℂˣ where
  toFun u := qPow v s ^ (-((tameValHom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) u).toAdd)
  map_one' := by rw [map_one]; simp
  map_mul' u z := by rw [map_mul, toAdd_mul, neg_add, zpow_add]

theorem completionAbsPow_eq_one_on_units (v : HeightOneSpectrum (𝓞 K)) (s : ℝ)
    {u : (v.adicCompletion K)ˣ} (hu : u ∈ unitsLevel v 0) : completionAbsPow v s u = 1 := by
  change qPow v s ^ (-((tameValHom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) u).toAdd) = _
  rw [(unitsLevel_zero_iff_tameValHom_eq_one (v := v) u).mp hu]
  simp

theorem isOpen_ker_completionAbsPow (v : HeightOneSpectrum (𝓞 K)) (s : ℝ) :
    IsOpen ((completionAbsPow v s).ker : Set (v.adicCompletion K)ˣ) :=
  Subgroup.isOpen_mono (H₁ := unitsLevel (K := K) v 0)
    (fun _ hu => completionAbsPow_eq_one_on_units v s hu) (isOpen_unitsLevel v 0)

@[simp] theorem completionAbsPow_zero (v : HeightOneSpectrum (𝓞 K)) : completionAbsPow v 0 = 1 := by
  apply MonoidHom.ext
  intro u
  change qPow v 0 ^ (-((tameValHom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) u).toAdd) = 1
  rw [qPow_zero, one_zpow]

theorem completionAbsPow_add (v : HeightOneSpectrum (𝓞 K)) (s t : ℝ) :
    completionAbsPow v (s + t) = completionAbsPow v s * completionAbsPow v t := by
  apply MonoidHom.ext
  intro u
  let d := -((tameValHom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) u).toAdd
  change qPow v (s + t) ^ d = qPow v s ^ d * qPow v t ^ d
  rw [qPow_add, mul_zpow]

theorem completionAbsPow_comp_inverseArtin {α : Weil h →* Fvˣ} (hα : IsLocalArtin K Ω α) (s : ℝ) :
    (completionAbsPow v s).comp α = unrChar h (qPow v s) := by
  apply MonoidHom.ext
  intro σ
  change qPow v s ^ (-((tameValHom (Valued.v : Valuation Fv ℤᵐ⁰)) (α σ)).toAdd) =
    qPow v s ^ deg σ
  rw [hα.ord_eq, neg_neg]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.completionAbsPow_comp_inverseArtin
