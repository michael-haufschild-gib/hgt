import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CyclotomicStageWeilDegree
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ArtinResidueDegree
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDecompositionGroup

/-! An unramified cyclotomic stage of prescribed Frobenius order has
completion of that degree at the prime selected by the valuation. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped IsMulCommutative GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

theorem exists_unramified_completion_withRoots (h : IsPlaceOver A v) {n : ℕ} (hn : 0 < n) :
    ∃ V : finiteAbelianExtensions K Ω,
      let L := (V : IntermediateField K Ω)
      letI := V.2.1
      letI := V.2.2
      letI : NumberField L := NumberField.of_module_finite K L
      let w := finitePlaceAtAbsoluteValuation (L := L) A h
      letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
        w.asIdeal.inertiaDeg (𝓞 K) = n ∧
        Module.finrank (v.adicCompletion K) (w.adicCompletion L) = n ∧
        HasEnoughRootsOfUnity L (normV v ^ n - 1) := by
  obtain ⟨V, hU, hV, hR⟩ := exists_unramified_cyclotomicStage_withRoots K Ω h n hn
  let L := (V : IntermediateField K Ω)
  letI : FiniteDimensional K L := V.2.1
  letI : IsAbelianGalois K L := V.2.2
  letI : NumberField L := NumberField.of_module_finite K L
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  letI := w.isMaximal
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  let σ := AlgEquiv.restrictNormalHom L (frob h : Gal(Ω/K))
  have hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal :=
    restrictNormalHom_isArithFrobAt A h (isFrob_frob (h := h))
  have hI := hU w.asIdeal inferInstance inferInstance
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal w.asIdeal, hI, Subgroup.card_bot]
  have hiff (i : ℤ) : (n : ℤ) ∣ i ↔ (w.asIdeal.inertiaDeg (𝓞 K) : ℤ) ∣ i := by
    have hi := arithFrobAt_zpow_mem_inertia_iff v w hσ i
    rw [hI, Subgroup.mem_bot, ← orderOf_dvd_iff_zpow_eq_one, show orderOf σ = n from hV] at hi
    exact hi
  have hf : w.asIdeal.inertiaDeg (𝓞 K) = n :=
    Nat.dvd_antisymm
      (Int.natCast_dvd_natCast.mp ((hiff n).mp (dvd_refl _)))
      (Int.natCast_dvd_natCast.mp ((hiff (w.asIdeal.inertiaDeg (𝓞 K))).mpr (dvd_refl _)))
  refine ⟨V, he, hf, ?_, hR⟩
  rw [finiteCompletion_finrank_eq_ramification_mul_inertia L v w, he, hf, one_mul]

theorem exists_unramified_completion_of_degree (h : IsPlaceOver A v) {n : ℕ} (hn : 0 < n) :
    ∃ V : finiteAbelianExtensions K Ω,
      let L := (V : IntermediateField K Ω)
      letI := V.2.1
      letI := V.2.2
      letI : NumberField L := NumberField.of_module_finite K L
      let w := finitePlaceAtAbsoluteValuation (L := L) A h
      letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
        w.asIdeal.inertiaDeg (𝓞 K) = n ∧
        Module.finrank (v.adicCompletion K) (w.adicCompletion L) = n := by
  obtain ⟨V, he, hf, hd, -⟩ := exists_unramified_completion_withRoots K Ω h hn
  exact ⟨V, he, hf, hd⟩

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_unramified_completion_of_degree

#print axioms GlobalTheory.Reciprocity.exists_unramified_completion_withRoots
