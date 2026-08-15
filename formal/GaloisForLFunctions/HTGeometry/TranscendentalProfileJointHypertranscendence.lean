import GaloisForLFunctions.HTGeometry.TranscendentalProfileSurvival
import GaloisForLFunctions.HTGeometry.FamilyJointHypertranscendence

/-!
# Joint hypertranscendence of a dilated power-profile family, with arbitrary dilations

The dilations of a power-profile source need not be algebraic.  What the separation asks of them is
only that they lie in a field over which the base of the profile is transcendental: a complex
relation is first normalized to one with algebraic coefficients, and the grouped relation is then a
polynomial identity in the base over that field.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The dilates of a power-profile source are jointly hypertranscendental.**  For every jet order,
the point variable together with all jets of all dilates is an algebraically independent family
over `ℂ`. -/
theorem algebraicIndependent_famJets_of_transcendentalProfile
    {K : Subfield ℂ} {t : ℂ} {e : ℕ → ℕ} {H : PowerSeries ℂ} (q : ι → ℂ)
    (hH : ∀ i, PowerSeries.coeff i H = t ^ e i)
    (ht : Transcendental K t)
    (hKalg : ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ K)
    (hconf : BoundedRelationConfinement (fun n => ((e n : ℤ))))
    (hq0 : ∀ i, q i ≠ 0) (hqinj : Function.Injective q) (hqK : ∀ i, q i ∈ K)
    (n : ℕ) :
    AlgebraicIndependent ℂ (familyJets n (fun i => rescale (q i) H)) := by
  refine algebraicIndependent_iff.mpr fun Q hQann => ?_
  by_contra hQ0
  obtain ⟨n', Q', hQ'0, hQ'alg, hQ'ann⟩ := exists_rational_familyJets_relation hQ0 hQann
  obtain ⟨N, hN⟩ := exists_coeff_ne_zero_famJets_of_transcendentalProfile q hH ht hconf
    hq0 hqinj hqK Q' (fun m => hKalg _ (hQ'alg m)) hQ'0
  exact hN (by rw [hQ'ann, map_zero])

/-- **The dilates of an analytic power-profile source are jointly hypertranscendental.**  No
algebraic differential equation with complex coefficients relates the point to the jets of all the
dilates `z ↦ F (q i z)`, for arbitrary distinct nonzero dilations lying in a field over which the
base of the profile is transcendental. -/
theorem jointlyHypertranscendental_dilates_of_transcendentalProfile
    {K : Subfield ℂ} {t : ℂ} {e : ℕ → ℕ} {F : ℂ → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (q : ι → ℂ)
    (hcoeff : ∀ i, PowerSeries.coeff i (taylorPS F) = t ^ e i)
    (ht : Transcendental K t)
    (hKalg : ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ K)
    (hconf : BoundedRelationConfinement (fun n => ((e n : ℤ))))
    (hq0 : ∀ i, q i ≠ 0) (hqinj : Function.Injective q) (hqK : ∀ i, q i ∈ K) :
    JointlyHypertranscendental (fun (i : ι) (z : ℂ) => F (q i * z)) := by
  refine jointlyHypertranscendental_of_aeval_survives _
    (fun i => hF.comp (contDiff_const.mul contDiff_id)) (fun m Q hQ hrel => hQ ?_)
  refine algebraicIndependent_iff.mp
    (algebraicIndependent_famJets_of_transcendentalProfile q hcoeff ht hKalg hconf
      hq0 hqinj hqK m) Q ?_
  rw [show (fun i => rescale (q i) (taylorPS F))
      = fun i => taylorPS (fun z => F (q i * z)) by
    funext i
    exact (taylorPS_comp_const_mul hF (q i)).symm]
  exact hrel

end

end GaloisForLFunctions
