import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.UniformizerRadicalRamification
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FullDegreeLocalNorm
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinExistence
import Mathlib.FieldTheory.KummerExtension

/-! A uniformizer radical is fixed by inverse Artin at the signed
uniformizer and at powers of exponent equal to the radical degree.
Both classes are norms from the totally ramified Kummer stage. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped WithZero IsMulCommutative GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)

theorem inverseArtin_fixes_uniformizerRadical
    {m : ℕ} [NeZero m] [HasEnoughRootsOfUnity K m] (a : Kˣ)
    (ha : Valued.v (algebraMap K (v.adicCompletion K) (a : K)) = WithZero.exp (-1 : ℤ))
    (π : Ω) (hπ : π ^ m = algebraMap K Ω (a : K))
    {α : Weil h →* (v.adicCompletion K)ˣ} (hα : IsLocalArtin K Ω α) :
    (∀ s : Weil h, (α s)⁻¹ =
      (-1 : (v.adicCompletion K)ˣ) ^ (m - 1) *
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a → s.val π = π) ∧
    ∀ (s : Weil h) (x : (v.adicCompletion K)ˣ), (α s)⁻¹ = x ^ m → s.val π = π := by
  letI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  let L := K⟮π⟯
  let b := AdjoinSimple.gen K π
  letI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral π)
  letI : NumberField L := NumberField.of_module_finite K L
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  have hb : b ^ m = algebraMap K L (a : K) := Subtype.ext hπ
  have hgen : K⟮b⟯ = ⊤ := by
    apply lift_injective
    rw [lift_adjoin_simple, lift_top]
    rfl
  obtain ⟨hKL, he, hloc, hnorm⟩ :=
    degree_ramificationIdx_norm_of_uniformizer_radical v w (NeZero.pos m) (a : K) ha b hb hgen
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  have hζ' : (primitiveRoots m K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (NeZero.pos m)).mpr hζ⟩
  have hP : Irreducible (X ^ m - C (a : K)) := by
    rw [← hKL]
    exact irreducible_X_pow_sub_C_of_root_adjoin_eq_top (hKL.symm ▸ hb) hgen
  letI : IsSplittingField K L (X ^ m - C (a : K)) := by
    rw [← hKL]
    exact isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
      (hKL.symm ▸ hζ') (hKL.symm ▸ hb) hgen
  letI : IsGalois K L := isGalois_of_isSplittingField_X_pow_sub_C hζ' hP L
  letI : IsCyclic Gal(L/K) := isCyclic_of_isSplittingField_X_pow_sub_C hζ' hP L
  letI : IsAbelianGalois K L := { is_comm.comm := IsMulCommutative.is_comm.comm }
  obtain ⟨art, -, hart, -⟩ := exists_global_idelic_artin K Ω
  let V : finiteAbelianExtensions K Ω := ⟨L, inferInstance, inferInstance⟩
  let f := finiteStageArtin K Ω art V
  let i : finitePlacesAbove L v := ⟨w, (mem_finitePlacesAbove L v w).mpr inferInstance⟩
  have hfix (s : Weil h) (y : (w.adicCompletion L)ˣ)
      (hy : (α s)⁻¹ = Units.map (Algebra.norm (v.adicCompletion K)) y) : s.val π = π := by
    have he := finiteIdelicArtin_eq_one_on_single_local_norm f
      (finiteStageArtin_isFiniteIdelicArtin K Ω art hart V)
      (finiteStageArtin_diagonal K Ω art V) v i y
    rw [← hy] at he
    change restrictAbPi K Ω (art (toCompactIdeleClassQuotient K (finiteEmbedding v (α s)⁻¹))) V = 1 at he
    rw [hα.glob art hart, restrictAbPi_toMaxAb] at he
    exact (AlgEquiv.restrictNormal_commutes s.val L b).symm.trans
      (congrArg (fun σ : Gal(L/K) => (σ b : Ω)) he)
  constructor
  · intro s hs
    have hb0 : b ≠ 0 := by
      intro hz
      rw [hz, zero_pow (NeZero.ne m)] at hb
      exact a.ne_zero ((map_eq_zero_iff _ (algebraMap K L).injective).mp hb.symm)
    let y := Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom (Units.mk0 b hb0)
    apply hfix s y
    rw [hs]
    apply Units.ext
    change (-1 : v.adicCompletion K) ^ (m - 1) *
        algebraMap K (v.adicCompletion K) (a : K) =
      Algebra.norm (v.adicCompletion K) (algebraMap L (w.adicCompletion L) b)
    rw [localNorm_eq_globalNorm_of_full_degree v w (hloc.trans hKL.symm), hnorm,
      map_mul, map_pow, map_neg, map_one]
  · intro s x hs
    let y := Units.map (AdicLiesOver.completionMap v w).toMonoidHom x
    apply hfix s y
    rw [hs]
    apply Units.ext
    change (x : v.adicCompletion K) ^ m =
      Algebra.norm (v.adicCompletion K) (algebraMap (v.adicCompletion K) (w.adicCompletion L) x.val)
    rw [Algebra.norm_algebraMap, hloc]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.inverseArtin_fixes_uniformizerRadical
