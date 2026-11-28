import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.OpenIdelicClassField
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.OpenIdelicSubgroupOfLocalPowers
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinDecompositionSurjectivity
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDecompositionGroup

/-! When the base contains the n-th roots of unity, some abelian number
field of exponent dividing n realizes all n-th power classes at the
chosen completion. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GlobalTheory.Kummer
open scoped IsMulCommutative Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem exists_saturated_completion_stage {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ V : finiteAbelianExtensions K Ω,
      let L := (V : IntermediateField K Ω)
      letI := V.2.1
      ∃ (E : IntermediateField K L) (hE : IsAbelianGalois K E),
        letI := hE
        letI := NumberField.of_module_finite K E
        (∀ σ : Gal(E/K), σ ^ n = 1) ∧
        ∀ (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal],
          Module.finrank (v.adicCompletion K) (w.adicCompletion E) =
            Nat.card (PowerClasses (v.adicCompletion K) n) := by
  let C := CompactIdeleClassQuotient K
  obtain ⟨N, hN, hNp, -, hNv⟩ :=
    exists_open_power_subgroup_with_local_comap (n := n) v (⊤ : Subgroup C) isOpen_univ le_top
  obtain ⟨V, E, hE, f, -, hfs, hfk, hf⟩ := exists_finite_idelic_artin_of_open K Ω N hN
  letI : FiniteDimensional K (V : IntermediateField K Ω) := V.2.1
  letI := hE
  letI : NumberField E := NumberField.of_module_finite K E
  have hd (x : Kˣ) : f (diagonal K x) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hfk]
    change toCompactIdeleClassQuotient K (diagonal K x) ∈ N
    rw [toCompactIdeleClassQuotient_diagonal]
    exact N.one_mem
  have hp (σ : Gal(E/K)) : σ ^ n = 1 := by
    obtain ⟨x, rfl⟩ := hfs σ
    rw [← map_pow]
    apply MonoidHom.mem_ker.mp
    rw [hfk]
    change toCompactIdeleClassQuotient K (x ^ n) ∈ N
    rw [map_pow]
    exact hNp ⟨toCompactIdeleClassQuotient K x, rfl⟩
  refine ⟨V, E, hE, hp, fun w _ => ?_⟩
  let r := f.comp (finiteEmbedding v)
  have hr : r.ker = (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range := by
    rw [← MonoidHom.comap_ker, hfk, Subgroup.comap_comap]
    exact hNv
  have hD : r.range = MulAction.stabilizer Gal(E/K) w.asIdeal :=
    finiteIdelicArtin_range_eq_decomposition f hf hd v w
  let q := (QuotientGroup.quotientMulEquivOfEq hr.symm).trans
    (QuotientGroup.quotientKerEquivRange r)
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr (decompositionMulEquiv v w).toEquiv,
    ← hD, ← Nat.card_congr q.toEquiv]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_saturated_completion_stage
