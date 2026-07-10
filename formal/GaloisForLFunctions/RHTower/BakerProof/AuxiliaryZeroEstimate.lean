import GaloisForLFunctions.RHTower.BakerProof.AuxiliaryFunction
import GaloisForLFunctions.ZeroEstimateOrder

/-!
# The local zero estimate for the Baker auxiliary function

The auxiliary frequencies are distinct, so the existing Vandermonde zero estimate supplies a
nonzero derivative below the number of columns at every base point.  This makes every local
multiplicity finite with an explicit uniform order bound; it is the zero-estimate input needed by
the later extrapolation argument.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerProof

/-- At every point, a nonzero Baker auxiliary function has a nonzero derivative of order strictly
below its number of exponential monomials. -/
theorem Relation.exists_auxiliaryFunction_iteratedDeriv_ne_zero_lt_card
    (R : Relation) {L : ℕ} (η : R.Column L → 𝓞 R.CoefficientField) (hη : η ≠ 0)
    (z : ℂ) :
    ∃ k : Fin (Fintype.card (R.Column L)),
      iteratedDeriv (k : ℕ) (R.auxiliaryFunction η) z ≠ 0 := by
  let e : Fin (Fintype.card (R.Column L)) ≃ R.Column L := (Fintype.equivFin _).symm
  let μ : Fin (Fintype.card (R.Column L)) → ℂ := fun k => R.frequency (e k)
  let coeff : Fin (Fintype.card (R.Column L)) → ℂ := fun k =>
    R.integralCoeffEmbedding (η (e k))
  have hμ : Function.Injective μ := R.frequency_injective.comp e.injective
  have hcoeff : coeff ≠ 0 := by
    intro hzero
    apply hη
    funext m
    let k := e.symm m
    have hk := congrFun hzero k
    have he : e k = m := e.apply_symm_apply m
    change R.integralCoeffEmbedding (η (e k)) = 0 at hk
    rw [he] at hk
    exact R.integralCoeffEmbedding_injective (by simpa using hk)
  obtain ⟨k, hk⟩ := exponentialSum_has_nonzero_iteratedDeriv_lt_card hμ hcoeff z
  refine ⟨k, ?_⟩
  intro hzero
  apply hk
  have hfun : (fun w : ℂ => exponentialSum μ coeff w) = R.auxiliaryFunction η := by
    funext w
    unfold exponentialSum Relation.auxiliaryFunction
    change (∑ k, R.integralCoeffEmbedding (η (e k)) *
      Complex.exp (w * R.frequency (e k))) =
      ∑ m, R.integralCoeffEmbedding (η m) * Complex.exp (R.frequency m * w)
    calc
      _ = ∑ k, R.integralCoeffEmbedding (η (e k)) *
          Complex.exp (R.frequency (e k) * w) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_comm w]
      _ = ∑ m, R.integralCoeffEmbedding (η m) *
          Complex.exp (R.frequency m * w) :=
        e.sum_comp (fun m => R.integralCoeffEmbedding (η m) *
          Complex.exp (R.frequency m * w))
  rw [hfun]
  exact hzero

/-- The local zero multiplicity of a nonzero Baker auxiliary function is strictly smaller than its
number of exponential monomials. -/
theorem Relation.auxiliaryFunction_analyticOrderAt_lt_card
    (R : Relation) {L : ℕ} (η : R.Column L → 𝓞 R.CoefficientField) (hη : η ≠ 0)
    (z : ℂ) :
    analyticOrderAt (R.auxiliaryFunction η) z < Fintype.card (R.Column L) := by
  obtain ⟨k, hk⟩ := R.exists_auxiliaryFunction_iteratedDeriv_ne_zero_lt_card η hη z
  have hf : AnalyticAt ℂ (R.auxiliaryFunction η) z := by
    unfold Relation.auxiliaryFunction
    fun_prop
  by_contra hnot
  have hle : (Fintype.card (R.Column L) : ℕ∞) ≤
      analyticOrderAt (R.auxiliaryFunction η) z := le_of_not_gt hnot
  have hall := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp hle
  exact hk (hall k k.isLt)

/-- The prescribed kernel equations give multiplicity at least `T` at every selected sample. -/
theorem Relation.auxiliaryFunction_analyticOrderAt_ge (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (sample : Fin S) :
    T ≤ analyticOrderAt (R.auxiliaryFunction η) (sample : ℕ) := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero]
  · intro k hk
    exact R.auxiliaryFunction_iteratedDeriv_eq_zero c hc hint pivot η hker sample k hk
  · unfold Relation.auxiliaryFunction
    fun_prop

end GaloisForLFunctions.RHTower.BakerProof
