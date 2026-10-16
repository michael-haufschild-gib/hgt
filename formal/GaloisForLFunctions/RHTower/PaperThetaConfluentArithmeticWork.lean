import GaloisForLFunctions.RHTower.ThetaQuantileArithmeticForm
import GaloisForLFunctions.RHTower.PaperThetaConfluentCurrent
import GaloisForLFunctions.RHTower.PaperThetaMeyerFredholmMultiplicity

/-! # Nonlinear prime--Gamma work for every charged theta jet

Every real polynomial response of every real projection of every parameter
jet is admitted to the original full Weil form. Its singular theta-quantile
transport retains the complete arithmetic energy, and actual compact smooth
tests converge to it in the full graph. The terminal Meyer/Fredholm-rank jet
is included even though its original compact profile has a nonzero charge.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open Zeta23

namespace RHTower.PaperThetaEndpoint
open CHMDDoobGraph HedenmalmThetaSource HedenmalmQuantile

def cutJetResponse (n : ℕ) (z : ℂ) (a : ℝ) (ell : ℂ →L[ℝ] ℝ)
    (P : Polynomial ℝ) (x : ℝ) : ℝ := P.eval (ell (cutParameterJet n z a x))

theorem boundedVariation_cutJetResponse (n : ℕ) (z : ℂ) (a : ℝ)
    (ell : ℂ →L[ℝ] ℝ) (P : Polynomial ℝ) :
    BoundedVariationOn (cutJetResponse n z a ell P) univ :=
  boundedVariation_polynomial_comp
    (ell.lipschitz.comp_boundedVariationOn (boundedVariationOn_cutParameterJet n z a)) P

/-- A concrete original-source vector, with no arithmetic admission premise. -/
def cutJetArithmeticSource (n : ℕ) (z : ℂ) (a : ℝ) (ell : ℂ →L[ℝ] ℝ)
    (P : Polynomial ℝ) : SourceGraph :=
  bvLift (cutJetResponse n z a ell P) (boundedVariation_cutJetResponse n z a ell P)

theorem cutJetArithmeticSource_function (n : ℕ) (z : ℂ) (a : ℝ)
    (ell : ℂ →L[ℝ] ℝ) (P : Polynomial ℝ) :
    (cutJetArithmeticSource n z a ell P).val.fst =ᵐ[massMeasure] cutJetResponse n z a ell P :=
  bvLift_source _ _

def cutQuantileJetResponse (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1)
    (ell : ℂ →L[ℝ] ℝ) (P : Polynomial ℝ) (t : ℝ) : ℝ :=
  P.eval (ell (cutQuantileParameterJet n z c t))

/-- Complete nonlinear prime--Gamma/polar work commutes with the singular compactification. -/
theorem cutParameterJet_fullWeil_transport (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1)
    (ell : ℂ →L[ℝ] ℝ) (P : Polynomial ℝ) :
    ThetaQuantileArithmetic.weilEnergy (cutQuantileJetResponse n z c ell P) =
      sourceWeilEnergy (cutJetArithmeticSource n z (thetaSource.quantileFun c.val) ell P) := by
  calc
    _ = ThetaQuantileArithmetic.weilEnergy (ThetaQuantileArithmetic.pull
        (cutJetResponse n z (thetaSource.quantileFun c.val) ell P)) := by
      apply ThetaQuantileArithmetic.weilEnergy_congr
      intro t ht
      dsimp only [cutQuantileJetResponse, ThetaQuantileArithmetic.pull, cutJetResponse]
      rw [cutQuantileParameterJet_interior n z c ⟨t, ht⟩]
    _ = _ := ThetaQuantileArithmetic.weilEnergy_pull _
      (boundedVariation_cutJetResponse n z (thetaSource.quantileFun c.val) ell P)

/-- The source identity retains the Gamma continuum, all prime powers, mass and both poles. -/
theorem cutParameterJet_fullWeil_source (n : ℕ) (z : ℂ) (a : ℝ)
    (ell : ℂ →L[ℝ] ℝ) (P : Polynomial ℝ) :
    sourceWeilEnergy (cutJetArithmeticSource n z a ell P) =
      phiDoobArchJumpEnergy (cutJetResponse n z a ell P) +
        (∑' k, ∫ x, phiDoobPrimeJump (cutJetResponse n z a ell P) k x) -
        phiDoobCoshMass (fun x => cutJetResponse n z a ell P x^2) +
        2*phiDoobCoshMass (cutJetResponse n z a ell P)^2 -
        2*phiDoobSinhMass (cutJetResponse n z a ell P)^2 := sourceWeilEnergy_bvLift _ _

/-- The transported nonlinear value is the limit of the original compact-test Weil values. -/
theorem cutParameterJet_fullWeil_smooth_approximation (n : ℕ) (z : ℂ)
    (c : Ioo (0 : ℝ) 1) (ell : ℂ →L[ℝ] ℝ) (P : Polynomial ℝ) :
    ∃ (v : ℕ → ℝ → ℝ) (hv : ∀ k, ContDiff ℝ 2 (v k))
      (hc : ∀ k, HasCompactSupport (v k)),
      Tendsto (fun k => compactLift (v k) (hv k) (hc k)) atTop
        (𝓝 (cutJetArithmeticSource n z (thetaSource.quantileFun c.val) ell P)) ∧
      Tendsto (fun k =>
        (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
          (EF.weilTest (fun x => (phiDoobTest (v k) x : ℂ))
            (fun x => (phiDoobTest (v k) x : ℂ)))).re)
        atTop (𝓝 (ThetaQuantileArithmetic.weilEnergy (cutQuantileJetResponse n z c ell P))) := by
  rw [cutParameterJet_fullWeil_transport]
  exact exists_compact_Weil_approximation _

/-- Admission does not erase the first charged jet of the actual closed Meyer generator. -/
theorem meyerRank_cut_arithmetic_admission (rho : XiDivisorSupport) (c : Ioo (0 : ℝ) 1) :
    ¬ ContinuousAt (cutQuantileParameterJet (deningerMeyerHasseSpectralRank rho)
      (xiSpectralPointSupport rho) c) c.val ∧
    ∀ (ell : ℂ →L[ℝ] ℝ) (P : Polynomial ℝ),
      cutJetArithmeticSource (deningerMeyerHasseSpectralRank rho) (xiSpectralPointSupport rho)
        (thetaSource.quantileFun c.val) ell P ∈ closure (compactTests : Set SourceGraph) := by
  refine ⟨not_continuousAt_meyerSpectralRank_cut rho c, ?_⟩
  intro ell P
  exact dense_compactTests _

/-- A genuinely discontinuous real component of the terminal charged jet enters the full graph. -/
theorem meyerRank_exists_discontinuous_arithmetic_response
    (rho : XiDivisorSupport) (c : Ioo (0 : ℝ) 1) :
    ∃ ell : ℂ →L[ℝ] ℝ,
      ¬ ContinuousAt (cutQuantileJetResponse (deningerMeyerHasseSpectralRank rho)
        (xiSpectralPointSupport rho) c ell Polynomial.X) c.val ∧
      cutJetArithmeticSource (deningerMeyerHasseSpectralRank rho) (xiSpectralPointSupport rho)
        (thetaSource.quantileFun c.val) ell Polynomial.X ∈ closure (compactTests : Set SourceGraph) := by
  classical
  let f := cutQuantileParameterJet (deningerMeyerHasseSpectralRank rho)
    (xiSpectralPointSupport rho) c
  have hnot : ¬ ContinuousAt f c.val := not_continuousAt_meyerSpectralRank_cut rho c
  have hs : ¬ ContinuousAt (fun t => (f t).re) c.val ∨
      ¬ ContinuousAt (fun t => (f t).im) c.val := by
    by_contra h
    push Not at h
    apply hnot
    have hh := (Complex.continuous_ofReal.continuousAt.comp' h.1).add
      ((Complex.continuous_ofReal.continuousAt.comp' h.2).mul
        (continuousAt_const : ContinuousAt (fun _ : ℝ => Complex.I) c.val))
    change ContinuousAt (fun t => ((f t).re : ℂ) + ((f t).im : ℂ)*Complex.I) c.val at hh
    simpa only [Complex.re_add_im] using hh
  rcases hs with hr | hi
  · refine ⟨Complex.reCLM, ?_, dense_compactTests _⟩
    change ¬ ContinuousAt (fun t => (Polynomial.X : Polynomial ℝ).eval ((f t).re)) c.val
    simpa only [Polynomial.eval_X] using hr
  · refine ⟨Complex.imCLM, ?_, dense_compactTests _⟩
    change ¬ ContinuousAt (fun t => (Polynomial.X : Polynomial ℝ).eval ((f t).im)) c.val
    simpa only [Polynomial.eval_X] using hi

end RHTower.PaperThetaEndpoint
