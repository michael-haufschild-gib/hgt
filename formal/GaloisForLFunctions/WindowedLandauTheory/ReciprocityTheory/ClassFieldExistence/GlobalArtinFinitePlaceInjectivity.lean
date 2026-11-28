import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ApproximateArtinKernelSinglePlace
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CongruentGlobalUnitApproximation

/-! The global Artin map is injective on ideles supported at one finite place. -/

noncomputable section

open NumberField IsDedekindDomain WithZero

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem globalArtin_injective_finiteEmbedding
    (a : CompactIdeleClassQuotient K →* Gal(maximalAbelianExtension K Ω/K))
    (hc : Continuous a) (ha : MatchesFiniteIdelicArtin K Ω a) (w : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (fun x => a (toCompactIdeleClassQuotient K (finiteEmbedding w x))) := by
  let g := a.comp ((toCompactIdeleClassQuotient K).comp (finiteEmbedding w))
  change Function.Injective g
  apply (injective_iff_map_eq_one g).mpr
  intro x hx
  have approx (y : (w.adicCompletion K)ˣ) (hy : g y = 1) :
      HasCongruentGlobalApproximants w (y : w.adicCompletion K) :=
    fun b _ t ht => exists_global_approx_of_globalArtin_eq_one a hc ha w y hy b t ht
  have he : Valued.v (x : w.adicCompletion K) = 1 := by
    by_cases hle : Valued.v (x : w.adicCompletion K) ≤ 1
    · exact valuation_eq_one_of_congruent_global_approximants w _ x.ne_zero hle (approx x hx)
    · have hi : Valued.v ((x⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K) ≤ 1 := by
        rw [Units.val_inv_eq_inv_val, map_inv₀]
        exact (inv_le_one₀ (zero_lt_one.trans (lt_of_not_ge hle))).mpr (le_of_not_ge hle)
      have hxi : g x⁻¹ = 1 := by rw [map_inv, hx, inv_one]
      have key := valuation_eq_one_of_congruent_global_approximants w _ (x⁻¹).ne_zero hi (approx x⁻¹ hxi)
      rwa [Units.val_inv_eq_inv_val, map_inv₀, inv_eq_one] at key
  apply Units.ext
  exact eq_one_of_congruent_global_approximants w _ he (approx x hx)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.globalArtin_injective_finiteEmbedding
