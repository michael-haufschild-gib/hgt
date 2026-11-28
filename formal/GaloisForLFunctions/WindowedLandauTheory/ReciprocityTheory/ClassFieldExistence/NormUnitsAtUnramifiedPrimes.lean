import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionNormResidueLifts
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalProductNormPowers
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.NormUnitRayRefinement

/-! At an unramified prime away from the extension degree, an integral
unit lifts first in the residue field and then through principal units. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions
open scoped GlobalTheory.Reciprocity.AdicLiesOver IsMulCommutative

namespace GlobalTheory.Reciprocity

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

local notation "G" => Gal(L/K)

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : Fintype G := Fintype.ofFinite _

local notation "D" => Module.finrank K L

private theorem nonempty_finitePlacesAbove (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (finitePlacesAbove L v) := by
  obtain ⟨P, hP, hPv⟩ := exists_isMaximal_liesOver K L v
  letI : P.LiesOver v.asIdeal := hPv
  let w : HeightOneSpectrum (𝓞 L) :=
    ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  exact ⟨⟨w, (mem_finitePlacesAbove L v w).mpr hPv⟩⟩

private theorem ramificationIdx_eq_one_of_isUnramifiedPrime
    (v : HeightOneSpectrum (𝓞 K)) (w : finitePlacesAbove L v)
    (hv : IsUnramifiedPrime K L G v) : w.val.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  letI := v.isMaximal
  letI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Finite v.asIdeal.ResidueField :=
    Finite.of_surjective _ v.asIdeal.bijective_algebraMap_quotient_residueField.surjective
  have he : Nat.card (w.val.asIdeal.inertia G) = Ideal.ramificationIdxIn v.asIdeal (𝓞 L) :=
    Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal w.val.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.val.asIdeal G,
    hv w.val.asIdeal w.val.isMaximal inferInstance, Subgroup.card_bot] at he
  exact he.symm

theorem exists_integral_fibre_of_pow (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (hx : ∃ z : (v.adicCompletion K)ˣ, z ∈ unitsLevel v 0 ∧ z ^ D = x) :
    ∃ y : ∀ w : finitePlacesAbove L v, (w.val.adicCompletion L)ˣ,
      (∀ w, y w ∈ (Submonoid.ofClass (w.val.adicCompletionIntegers L)).units) ∧
        finiteLocalNorm L v y = x := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨fun w => Units.map (algebraMap (v.adicCompletion K) (w.val.adicCompletion L)).toMonoidHom z,
    fun w => ?_, finiteLocalNorm_of_scalar v z⟩
  rw [← unitsLevel_zero]
  exact completedScalar_mem_unitsLevel_zero v w.val z hz

theorem exists_integral_fibre_of_unramified
    (v : HeightOneSpectrum (𝓞 K)) (hv : IsUnramifiedPrime K L G v)
    (hD : Valued.v (D : v.adicCompletion K) = 1)
    (x : (v.adicCompletion K)ˣ) (hx : x ∈ unitsLevel v 0) :
    ∃ y : ∀ w : finitePlacesAbove L v, (w.val.adicCompletion L)ˣ,
      (∀ w, y w ∈ (Submonoid.ofClass (w.val.adicCompletionIntegers L)).units) ∧
        finiteLocalNorm L v y = x := by
  classical
  obtain ⟨w⟩ := nonempty_finitePlacesAbove (L := L) v
  obtain ⟨a, ha, hx'⟩ := exists_norm_lift_of_residueUnit v w.val
    (ramificationIdx_eq_one_of_isUnramifiedPrime v w hv) x hx
  let y := Pi.mulSingle (M := fun u : finitePlacesAbove L v => (u.val.adicCompletion L)ˣ) w a
  have hy (u : finitePlacesAbove L v) :
      y u ∈ (Submonoid.ofClass (u.val.adicCompletionIntegers L)).units := by
    rw [← unitsLevel_zero]
    by_cases h : u = w
    · subst u
      simpa [y, Pi.mulSingle_eq_same] using ha
    · dsimp only [y]
      rw [Pi.mulSingle_eq_of_ne h]
      exact one_mem _
  obtain ⟨s, -, hs, h⟩ := exists_unitsLevel_pow_roots v D (Module.finrank_pos (R := K) (M := L)).ne'
  rw [hs hD] at h
  rw [← finiteLocalNorm_mulSingle v w a] at hx'
  obtain ⟨z, hz, hn⟩ := exists_integral_fibre_of_pow (L := L) v _ (h _ hx')
  refine ⟨z * y, fun u => mul_mem (hz u) (hy u), ?_⟩
  rw [map_mul, hn, div_mul_cancel]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_integral_fibre_of_unramified
