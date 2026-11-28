import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PadicCompletionNormalization
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.UnramifiedCompletionOfDegree

/-! Above a p-adic completion, an unramified stage of prescribed degree
has residue cardinality p to that degree and retains p as uniformizer. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {p : ℕ} [Fact p.Prime]

theorem exists_unramified_padicStage (h : IsPlaceOver A v) (i : ℚ_[p] ≃+* v.adicCompletion K)
    (hi : Continuous i) {n : ℕ} (hn : 0 < n) :
    ∃ V : finiteAbelianExtensions K Ω,
      let L := (V : IntermediateField K Ω)
      letI := V.2.1
      letI := V.2.2
      letI : NumberField L := NumberField.of_module_finite K L
      let w := finitePlaceAtAbsoluteValuation (L := L) A h
      letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
        normV w = p ^ n ∧ (p : 𝓞 L) ∈ w.asIdeal ∧ (p : 𝓞 L) ∉ w.asIdeal ^ 2 := by
  obtain ⟨V, he, hf, -⟩ := exists_unramified_completion_of_degree K Ω h hn
  obtain ⟨-, -, hq, hv⟩ := padicIso_place_normalization v i hi
  let L := (V : IntermediateField K Ω)
  letI := V.2.1
  letI := V.2.2
  letI : NumberField L := NumberField.of_module_finite K L
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  letI := v.isMaximal
  letI := w.isMaximal
  have hcard : normV w = p ^ n := by
    have hr : normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 K) :=
      (Ideal.cardQuot_pow_inertiaDeg v.asIdeal w.asIdeal).symm
    rw [hr, hq, hf]
  have hval : Valued.v (p : w.adicCompletion L) = exp (-1 : ℤ) := by
    rw [← map_natCast (AdicLiesOver.completionMap v w) p, AdicLiesOver.valued_completionMap, hv]
    have hRam : Ideal.ramificationIdx' v.asIdeal w.asIdeal = 1 := by
      rwa [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
    rw [hRam, pow_one]
  have hp : w.intValuation (p : 𝓞 L) = exp (-1 : ℤ) := by
    have ht := valuedAdicCompletion_eq_valuation (K := L) (v := w) (p : 𝓞 L)
    rw [valuation_of_algebraMap] at ht
    change Valued.v (algebraMap (𝓞 L) (w.adicCompletion L) (p : 𝓞 L)) = _ at ht
    rw [map_natCast (algebraMap (𝓞 L) (w.adicCompletion L))] at ht
    exact ht.symm.trans hval
  refine ⟨V, he, hcard, (w.intValuation_lt_one_iff_mem _).mp ?_, fun hs => ?_⟩
  · rw [hp, ← exp_zero, exp_lt_exp]
    omega
  · have hx := (w.intValuation_le_pow_iff_mem (p : 𝓞 L) 2).mpr hs
    rw [hp, exp_le_exp] at hx
    norm_num at hx

end GlobalTheory.Reciprocity
