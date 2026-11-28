import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FixedFieldIdelicKernel

/-! A local idele at an unramified prime maps to its arithmetic
Frobenius raised to the additive valuation of its coordinate. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal WithZero GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative nonZeroDivisors

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K : Type} [Field K] [NumberField K]

theorem toFractionalIdeal_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    toFractionalIdeal (finiteEmbedding v x) =
      (idealUnit v.ne_bot : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ^ ord v (finiteEmbedding v x) := by
  change (∏ᶠ w : HeightOneSpectrum (𝓞 K), idealUnit w.ne_bot ^ ord w (finiteEmbedding v x)) = _
  refine finprod_eq_single _ v fun w hw => ?_
  rw [ord_finiteEmbedding_of_ne hw, zpow_zero]

theorem finiteEmbedding_mem_idelesOneMod_of_not_dvd (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.fin) (x : (v.adicCompletion K)ˣ) :
    finiteEmbedding v x ∈ idelesOneMod m := by
  apply (mem_idelesOneMod m).mpr
  constructor
  · intro w hw
    have h : w ≠ v := fun e => hv (e ▸ hw)
    rw [finiteProj_finiteEmbedding_of_ne h]
    exact one_mem _
  · intro w _
    rw [infiniteProj_finiteEmbedding, Units.val_one, map_one]
    exact zero_lt_one

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

local instance : CommGroup Gal(L/K) :=
  { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : Fintype Gal(L/K) := Fintype.ofFinite _

theorem finiteIdelicArtin_finiteEmbedding_of_unramified
    (f : IdeleGroup K →* Gal(L/K)) (hf : IsFiniteIdelicArtin f)
    (v : HeightOneSpectrum (𝓞 K)) (hv : IsUnramifiedPrime K L Gal(L/K) v) (x : (v.adicCompletion K)ˣ) :
    f (finiteEmbedding v x) =
      frobeniusElement K L Gal(L/K) v ^ (-log (Valued.v (x : v.adicCompletion K))) := by
  obtain ⟨m, hram, hArtin⟩ := hf
  have hv' : ¬ v.asIdeal ∣ m.fin := fun h => ((hram v).mp h) hv
  have h := hArtin ⟨finiteEmbedding v x, finiteEmbedding_mem_idelesOneMod_of_not_dvd m v hv' x⟩
  change f (finiteEmbedding v x) = artinMap K L Gal(L/K) (toFractionalIdeal (finiteEmbedding v x)) at h
  rw [h, toFractionalIdeal_finiteEmbedding, map_zpow, artinMap_idealUnit_prime, frobeniusOrOne,
    if_pos hv, ord_finiteEmbedding_self]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_finiteEmbedding_of_unramified
