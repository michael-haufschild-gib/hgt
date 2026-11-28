import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDecompositionGroup
import GaloisForLFunctions.HTGeometry.ABHN.CyclicHilbert90

/-! A finite local norm multiplies the additive valuation by the residue degree. -/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem valued_finiteCompletion_norm (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (x : w.adicCompletion L) :
    Valued.v (Algebra.norm (v.adicCompletion K) x) =
      Valued.v x ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have h := GaloisForLFunctions.HTGeometry.ABHN.valuation_algebraMap_norm_eq_pow_of_gal_invariant
    (K := v.adicCompletion K) (L := w.adicCompletion L) Valued.v
    (fun σ y => by
      obtain ⟨τ, rfl⟩ := (decompositionMulEquiv v w).surjective σ
      exact valued_decompositionMulEquiv v w τ y) x
  have hmap := AdicLiesOver.valued_completionMap v w (Algebra.norm (v.adicCompletion K) x)
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot] at hmap
  have he : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 :=
    (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  apply (pow_left_inj₀ zero_le zero_le he).mp
  rw [← hmap, ← pow_mul, mul_comm (w.asIdeal.inertiaDeg (𝓞 K)),
    ← finiteCompletion_finrank_eq_ramification_mul_inertia L v w]
  exact h

end GlobalTheory.Reciprocity
