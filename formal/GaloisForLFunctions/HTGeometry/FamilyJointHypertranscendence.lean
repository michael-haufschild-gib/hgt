import GaloisForLFunctions.HTGeometry.FamilyBoundedRelationSurvival
import GaloisForLFunctions.HTGeometry.FamilyFormalMahlerDescent
import GaloisForLFunctions.HTGeometry.FamilyTaylorFormalBridge

/-!
# Joint hypertranscendence of a dilated bounded-relation family

The jets of the dilates `H(q_i X)` of a single bounded-relation source, together with the point
variable, are algebraically independent over `ℂ` — no algebraic differential relation with complex
coefficients holds between them.

Coefficient algebraicity, which the exponential survival argument needs, is not a hypothesis:
a complex relation is first normalized to a rational one, at the cost of raising the jet order.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The dilates of a bounded-relation source are jointly hypertranscendental.**  For every jet
order, the point variable together with all jets of all dilates is an algebraically independent
family over `ℂ`. -/
theorem algebraicIndependent_famJets_of_boundedRelation
    {b : ℕ → ℝ} {u : ℕ → ℂ} {H : PowerSeries ℂ} (q : ι → ℂ)
    (hH : ∀ i, PowerSeries.coeff i H = u i * Complex.exp (-(b i : ℂ)))
    (hbAlg : ∀ i, IsAlgebraic ℚ (b i)) (hconf : BoundedRelationConfinement b)
    (huAlg : ∀ i, IsAlgebraic ℚ (u i)) (hu0 : ∀ i, u i ≠ 0)
    (hqAlg : ∀ i, IsAlgebraic ℚ (q i)) (hq0 : ∀ i, q i ≠ 0) (hqinj : Function.Injective q)
    (n : ℕ) :
    AlgebraicIndependent ℂ (familyJets n (fun i => rescale (q i) H)) := by
  refine algebraicIndependent_iff.mpr fun Q hQann => ?_
  by_contra hQ0
  obtain ⟨n', Q', hQ'0, hQ'alg, hQ'ann⟩ := exists_rational_familyJets_relation hQ0 hQann
  obtain ⟨N, hN⟩ := exists_coeff_ne_zero_famJets_of_boundedRelation q hH hbAlg hconf huAlg hu0
    hqAlg hq0 hqinj Q' hQ'alg hQ'0
  exact hN (by rw [hQ'ann, map_zero])

/-- The Taylor series of a dilated function is the rescaled Taylor series. -/
theorem taylorPS_comp_const_mul {F : ℂ → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (c : ℂ) :
    taylorPS (fun z => F (c * z)) = rescale c (taylorPS F) := by
  ext k
  rw [coeff_taylorPS, PowerSeries.coeff_rescale, coeff_taylorPS,
    iteratedDeriv_comp_const_mul (hF.of_le (by exact_mod_cast le_top)) c]
  rw [mul_zero]
  ring

/-- **The dilates of an analytic bounded-relation source are jointly hypertranscendental.**  No
algebraic differential equation with complex coefficients relates the point to the jets of all the
dilates `z ↦ F (q i z)`. -/
theorem jointlyHypertranscendental_dilates_of_boundedRelation
    {b : ℕ → ℝ} {u : ℕ → ℂ} {F : ℂ → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (q : ι → ℂ)
    (hcoeff : ∀ i, PowerSeries.coeff i (taylorPS F) = u i * Complex.exp (-(b i : ℂ)))
    (hbAlg : ∀ i, IsAlgebraic ℚ (b i)) (hconf : BoundedRelationConfinement b)
    (huAlg : ∀ i, IsAlgebraic ℚ (u i)) (hu0 : ∀ i, u i ≠ 0)
    (hqAlg : ∀ i, IsAlgebraic ℚ (q i)) (hq0 : ∀ i, q i ≠ 0) (hqinj : Function.Injective q) :
    JointlyHypertranscendental (fun (i : ι) (z : ℂ) => F (q i * z)) := by
  refine jointlyHypertranscendental_of_aeval_survives _
    (fun i => hF.comp (contDiff_const.mul contDiff_id)) (fun m Q hQ hrel => hQ ?_)
  refine algebraicIndependent_iff.mp
    (algebraicIndependent_famJets_of_boundedRelation q hcoeff hbAlg hconf huAlg hu0
      hqAlg hq0 hqinj m) Q ?_
  rw [show (fun i => rescale (q i) (taylorPS F))
      = fun i => taylorPS (fun z => F (q i * z)) by
    funext i
    exact (taylorPS_comp_const_mul hF (q i)).symm]
  exact hrel

end

end GaloisForLFunctions
