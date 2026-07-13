import GaloisForLFunctions.HTGeometry.EllipticGammaMixedFace
import GaloisForLFunctions.HTGeometry.AnalyticSubringFractionEvaluation
import GaloisForLFunctions.HTGeometry.MeromorphicPoleOrbitBoundaryLocal

/-!
# The external elliptic-gamma defect is not elliptic

For a structural period `σ` nontorsion modulo the theta lattice and an external shift `h`
nonresonant with that orbit, the external difference of the actual elliptic-gamma logarithmic
derivative cannot belong to the field of `(1, τ)`-elliptic meromorphic fractions.  The proof
combines the genuine gamma mixed-face identity with the punctured-local theta pole-orbit
obstruction.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance ellipticGammaExternalDefectDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaExternalDefectDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- **Order-one elliptic-field separation.** A nonresonant external difference of the logarithmic
derivative of the genuine elliptic-gamma product is not any globally elliptic quotient of two
entire functions. -/
theorem ellipticGammaExternalLogDerivDefect_ne_ellipticFraction
    {σ τ h : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hσnt : ThetaTranslationNontorsion τ σ)
    (hnonres : ThetaTranslationNonresonant τ σ h)
    {a b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfa : Germ.coeRingHom (𝓟 Set.univ) f = (a : Germ (𝓟 Set.univ) ℂ))
    (hgb : Germ.coeRingHom (𝓟 Set.univ) g = (b : Germ (𝓟 Set.univ) ℂ))
    (hperiodOne : Function.Periodic (fun z => f z / g z) 1)
    (hperiodTau : Function.Periodic (fun z => f z / g z) τ) :
    addTranslationMeroEquiv h (ellipticGammaLogDerivMero σ τ hσ hτ) -
        ellipticGammaLogDerivMero σ τ hσ hτ ≠
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) b := by
  intro heq
  let Q := thetaLogDerivDefectDenominatorAnalytic h τ hτ
  have hmap_ne {c : analyticSubring Set.univ} (hc : c ≠ 0) :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) c ≠ 0 :=
    fun hz => hc ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  have hTb : addTranslationAnalyticEquiv σ b ≠ 0 :=
    fun hz => hb ((addTranslationAnalyticEquiv σ).injective (by simpa using hz))
  have hQ : Q ≠ 0 := thetaLogDerivDefectDenominatorAnalytic_ne_zero h τ hτ
  have hfield : thetaLogDerivDefectMero h τ hτ =
      addTranslationMeroEquiv σ
          (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
            algebraMap (analyticSubring Set.univ) (meroField Set.univ) b) -
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b := by
    rw [← ellipticGammaLogDerivMero_mixed_face_sigma hσ hτ, heq]
  rw [thetaLogDerivDefectMero_eq_div,
    map_div₀, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap] at hfield
  dsimp [Q] at hQ
  field_simp [hmap_ne hQ, hmap_ne hb, hmap_ne hTb] at hfield
  simp only [← map_mul, ← map_sub] at hfield
  have hcross :
      thetaLogDerivDefectNumeratorAnalytic h τ hτ *
          (addTranslationAnalyticEquiv σ b * b) =
        thetaLogDerivDefectDenominatorAnalytic h τ hτ *
          (addTranslationAnalyticEquiv σ a * b -
            a * addTranslationAnalyticEquiv σ b) := by
    have hcross' := (IsFractionRing.injective
      (analyticSubring Set.univ) (meroField Set.univ)) hfield
    linear_combination hcross'
  have heval_a (z : ℂ) : univGermEval z (a : Germ (𝓟 Set.univ) ℂ) = f z := by
    rw [← hfa]
    rfl
  have heval_b (z : ℂ) : univGermEval z (b : Germ (𝓟 Set.univ) ℂ) = g z := by
    rw [← hgb]
    rfl
  have hcrossEval (z : ℂ) :
      univGermEval z
          (thetaLogDerivDefectNumeratorAnalytic h τ hτ :
            Germ (𝓟 Set.univ) ℂ) * (g (z + σ) * g z) =
        univGermEval z
          (thetaLogDerivDefectDenominatorAnalytic h τ hτ :
            Germ (𝓟 Set.univ) ℂ) *
          (f (z + σ) * g z - f z * g (z + σ)) := by
    have hz := congrArg (fun c : analyticSubring Set.univ =>
      univGermEval z (c : Germ (𝓟 Set.univ) ℂ)) hcross
    simpa only [univGermEval_analyticSubring_mul,
      univGermEval_analyticSubring_sub,
      univGermEval_addTranslationAnalyticEquiv, heval_a, heval_b] using hz
  let qfun : ℂ → ℂ := fun z => jacobiTheta₂ (z + h) τ * jacobiTheta₂ z τ
  have hqfun : AnalyticOnNhd ℂ qfun Set.univ := by
    intro z _
    have hadd : AnalyticAt ℂ (fun w : ℂ => w + h) z :=
      analyticAt_id.add analyticAt_const
    have hshift : AnalyticAt ℂ (fun w : ℂ => jacobiTheta₂ (w + h) τ) z := by
      change AnalyticAt ℂ ((fun w => jacobiTheta₂ w τ) ∘ fun w : ℂ => w + h) z
      exact AnalyticAt.comp (x := z) (g := fun w => jacobiTheta₂ w τ)
        (f := fun w : ℂ => w + h)
        ((jacobiTheta₂_analyticOnNhd_fst τ hτ) (z + h) (Set.mem_univ _)) hadd
    exact hshift.mul ((jacobiTheta₂_analyticOnNhd_fst τ hτ) z (Set.mem_univ _))
  have hqrep : Germ.coeRingHom (𝓟 Set.univ) qfun =
      (thetaLogDerivDefectDenominatorAnalytic h τ hτ : Germ (𝓟 Set.univ) ℂ) := by
    rfl
  have hgshift : AnalyticOnNhd ℂ (fun z => g (z + σ)) Set.univ :=
    hg.comp (analyticOnNhd_addTranslation σ _) (Set.mapsTo_univ _ _)
  have hgbshift : Germ.coeRingHom (𝓟 Set.univ) (fun z => g (z + σ)) =
      (addTranslationAnalyticEquiv σ b : Germ (𝓟 Set.univ) ℂ) := by
    change Germ.ofFun (l := 𝓟 Set.univ) (fun z => g (z + σ)) =
      (b : Germ (𝓟 Set.univ) ℂ).compTendsto (addTranslation σ)
        (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _))
    rw [← hgb]
    rfl
  have hlocal (n : ℤ) :
      (thetaLogDerivDefect h · τ) =ᶠ[
        𝓝[≠] additiveOrbitPoint (thetaHalfPeriod τ - h) σ n]
        (fun z => (f (z + σ) / g (z + σ)) - f z / g z) := by
    let z₀ := additiveOrbitPoint (thetaHalfPeriod τ - h) σ n
    have hqne := analyticSubring_rep_eventually_ne_zero
      (thetaLogDerivDefectDenominatorAnalytic_ne_zero h τ hτ) hqfun hqrep z₀
    have hgne := analyticSubring_rep_eventually_ne_zero hb hg hgb z₀
    have hgsne := analyticSubring_rep_eventually_ne_zero hTb hgshift hgbshift z₀
    filter_upwards [hqne, hgne, hgsne] with z hzq hzg hzgs
    have hzθprod : jacobiTheta₂ (z + h) τ ≠ 0 ∧ jacobiTheta₂ z τ ≠ 0 := by
      simpa only [qfun, mul_ne_zero_iff] using hzq
    have htheta := univGermEval_thetaLogDerivDefect_div_eq hτ hzθprod.2 hzθprod.1
    have hce := hcrossEval z
    have hqeval : univGermEval z
        (thetaLogDerivDefectDenominatorAnalytic h τ hτ :
          Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
      change qfun z ≠ 0
      exact hzq
    rw [thetaLogDerivDefect]
    rw [← htheta]
    field_simp [hqeval, hzg, hzgs]
    linear_combination hce
  apply thetaDifferentialOperator_ne_ellipticShiftCoboundary_of_eventuallyEq
    (L := (1 : Polynomial ℂ)) one_ne_zero hτ hσnt hnonres
    (fun z => f z / g z)
  · exact hf.meromorphicOn.div hg.meromorphicOn
  · exact hperiodOne
  · exact hperiodTau
  · intro n
    have hone : constantCoeffDifferentialOperator (1 : Polynomial ℂ)
        (thetaLogDerivDefect h · τ) = (thetaLogDerivDefect h · τ) := by
      funext z
      rw [constantCoeffDifferentialOperator, Polynomial.sum_def]
      have hsupp : (1 : Polynomial ℂ).support = {0} := by
        rw [show (1 : Polynomial ℂ) = Polynomial.C 1 by simp,
          Polynomial.support_C one_ne_zero]
      rw [hsupp]
      simp [iteratedDeriv_zero]
    rw [hone]
    exact hlocal n

end

end GaloisForLFunctions
