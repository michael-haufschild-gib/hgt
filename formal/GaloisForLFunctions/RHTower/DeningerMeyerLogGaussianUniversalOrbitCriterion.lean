import GaloisForLFunctions.RHTower.DeningerMeyerInvariantEvaluationGaugeFrontier
import GaloisForLFunctions.HTGeometry.GaussianSchwartz

/-!
# Target-free log-Gaussian source for the Meyer frontier

The earlier fixed compact Meyer representative avoiding every actual Xi zero
uses one global modulation selected outside a bad set defined by the divisor.
That gives a valid reduction, but not a target-free source construction.

This file constructs the explicit log-Gaussian

`g(t) = exp (-π t²)`.

Every derivative is a polynomial times the Gaussian.  Polynomial growth and
quadratic exponential decay prove the full all-weight Meyer condition at both
logarithmic ends.  Its entire logarithmic Mellin transform is computed exactly:

`M_g(s) = exp (s² / (4π))`.

It is therefore nonzero at every complex spectral parameter, without using the
Xi divisor.  Its class in literal Meyer middle cohomology is consequently
nonzero under every actual zeroth Xi evaluation.

Completing the square then produces the reflection-adapted source

`h(t) = exp (-t / 2) exp (-π t²)`.

It is fixed by Paugam's weighted involution, belongs to the genuine reflected
Hodge sector, and has transform `exp ((s - 1/2)² / (4π))`, again nowhere zero.

The final theorem sharpens the positive-admission frontier to one explicit
source orbit: boundedness of every centered Xi evaluation along the orbit of
this single class is equivalent to RH.  The theorem does not assert that those
bounds hold; deriving them from arithmetic source geometry remains open.
-/

open Complex Filter Function Set Topology MeasureTheory Asymptotics
open scoped Real
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Explicit target-free Gaussian profile in logarithmic radius. -/
def deningerMeyerLogGaussianProfile (t : ℝ) : ℂ :=
  (gaussReal t : ℂ)

theorem deningerMeyerLogGaussianProfile_smooth :
    ContDiff ℝ (⊤ : ℕ∞) deningerMeyerLogGaussianProfile := by
  exact Complex.ofRealCLM.contDiff.comp contDiff_gaussReal

/-- Every iterated derivative of the complex log-Gaussian is the complexification
of a real polynomial times the Gaussian. -/
theorem exists_poly_iteratedDeriv_deningerMeyerLogGaussianProfile (n : ℕ) :
    ∃ p : Polynomial ℝ, ∀ t : ℝ,
      iteratedDeriv n deningerMeyerLogGaussianProfile t =
        ((p.eval t * gaussReal t : ℝ) : ℂ) := by
  induction n with
  | zero =>
      refine ⟨1, fun t => ?_⟩
      simp [iteratedDeriv_zero, deningerMeyerLogGaussianProfile]
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      let q := p.derivative - Polynomial.C (2 * π) * Polynomial.X * p
      refine ⟨q, fun t => ?_⟩
      have hfun : iteratedDeriv n deningerMeyerLogGaussianProfile =
          fun y => ((p.eval y * gaussReal y : ℝ) : ℂ) := funext hp
      rw [iteratedDeriv_succ, hfun]
      exact (hasDerivAt_poly_mul_gaussReal p t).ofReal_comp.deriv

private theorem poly_eval_isBigO_exp_atTop (p : Polynomial ℝ) :
    p.eval =O[atTop] Real.exp := by
  have hp : p.eval =O[atTop] (Polynomial.X ^ p.natDegree).eval :=
    p.isBigO_atTop_of_degree_le (Polynomial.X ^ p.natDegree) (by
      rw [Polynomial.degree_X_pow]
      exact p.degree_le_natDegree)
  have hpow : (Polynomial.X ^ p.natDegree).eval =
      fun t : ℝ => t ^ p.natDegree := by
    funext t
    simp
  rw [hpow] at hp
  exact hp.trans Real.isLittleO_pow_exp_atTop.isBigO

/-- A Gaussian beats an exponential with arbitrary real linear rate. -/
private theorem gaussian_isLittleO_exp_linear_atTop (r : ℝ) :
    (fun t : ℝ => Real.exp (-(π * t ^ (2 : ℕ)))) =o[atTop]
      fun t : ℝ => Real.exp (-r * t) := by
  rw [Real.isLittleO_exp_comp_exp_comp]
  let q : Polynomial ℝ :=
    Polynomial.C π * Polynomial.X ^ (2 : ℕ) +
      Polynomial.C (-r) * Polynomial.X + Polynomial.C 0
  have hqdeg : q.degree = 2 := by
    exact Polynomial.degree_quadratic Real.pi_ne_zero
  have hqlead : q.leadingCoeff = π := by
    exact Polynomial.leadingCoeff_quadratic Real.pi_ne_zero
  have hq := q.tendsto_atTop_of_leadingCoeff_nonneg (by
      rw [hqdeg]
      norm_num) (by
      rw [hqlead]
      exact Real.pi_pos.le)
  convert hq using 1
  funext t
  simp [q]
  ring

private theorem poly_mul_gaussReal_isBigO_exp_neg_atTop
    (p : Polynomial ℝ) (a : ℝ) :
    (fun t : ℝ => p.eval t * gaussReal t) =O[atTop]
      fun t : ℝ => Real.exp (-a * t) := by
  have hp := poly_eval_isBigO_exp_atTop p
  have hg := (gaussian_isLittleO_exp_linear_atTop (a + 1)).isBigO
  have hmul := hp.mul hg
  apply hmul.congr'
  · filter_upwards with t
    simp only [gaussReal]
  · filter_upwards with t
    rw [← Real.exp_add]
    congr 1
    ring

private theorem poly_mul_gaussReal_isBigO_exp_neg_atBot
    (p : Polynomial ℝ) (b : ℝ) :
    (fun t : ℝ => p.eval t * gaussReal t) =O[atBot]
      fun t : ℝ => Real.exp (b * t) := by
  let q : Polynomial ℝ := p.comp (-Polynomial.X)
  have htop := poly_mul_gaussReal_isBigO_exp_neg_atTop q b
  have hcomp := htop.comp_tendsto tendsto_neg_atBot_atTop
  apply hcomp.congr'
  · filter_upwards with t
    simp [q, gaussReal]
  · filter_upwards with t
    simp

/-- The log-Gaussian satisfies Meyer's full all-derivative, all-exponential-weight
decay condition. -/
theorem deningerMeyerLogGaussianProfile_strongLogDecay :
    DeningerMeyerStrongLogDecay deningerMeyerLogGaussianProfile where
  smooth := deningerMeyerLogGaussianProfile_smooth
  decayTop := by
    intro n a
    obtain ⟨p, hp⟩ :=
      exists_poly_iteratedDeriv_deningerMeyerLogGaussianProfile n
    have h := poly_mul_gaussReal_isBigO_exp_neg_atTop p a
    rw [show iteratedDeriv n deningerMeyerLogGaussianProfile =
        fun t => ((p.eval t * gaussReal t : ℝ) : ℂ) from funext hp]
    have hc : (fun t => ((p.eval t * gaussReal t : ℝ) : ℂ)) =O[atTop]
        (fun t : ℝ => Real.exp (-a * t)) := by
      rw [← isBigO_norm_left]
      simpa using h.norm_left
    apply hc.congr' (Eventually.of_forall fun _ => rfl)
    filter_upwards with t
    rw [← Real.exp_mul]
    congr 1
    ring
  decayBot := by
    intro n b
    obtain ⟨p, hp⟩ :=
      exists_poly_iteratedDeriv_deningerMeyerLogGaussianProfile n
    have h := poly_mul_gaussReal_isBigO_exp_neg_atBot p b
    rw [show iteratedDeriv n deningerMeyerLogGaussianProfile =
        fun t => ((p.eval t * gaussReal t : ℝ) : ℂ) from funext hp]
    have hc : (fun t => ((p.eval t * gaussReal t : ℝ) : ℂ)) =O[atBot]
        (fun t : ℝ => Real.exp (b * t)) := by
      rw [← isBigO_norm_left]
      simpa using h.norm_left
    apply hc.congr' (Eventually.of_forall fun _ => rfl)
    filter_upwards with t
    rw [← Real.exp_mul]
    congr 1
    ring

/-- Explicit all-weight Meyer representative defined without divisor data. -/
def deningerMeyerLogGaussianSource : DeningerMeyerStrongLogTarget :=
  ⟨deningerMeyerLogGaussianProfile,
    deningerMeyerLogGaussianProfile_strongLogDecay⟩

/-- Exact entire Mellin transform of the log-Gaussian. -/
theorem deningerMeyerLogGaussianSource_mellin (s : ℂ) :
    deningerMeyerStrongLogMellin deningerMeyerLogGaussianSource s =
      Complex.exp (s ^ (2 : ℕ) / (4 * π)) := by
  rw [deningerMeyerStrongLogMellin]
  simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul,
    deningerMeyerLogGaussianSource, deningerMeyerLogGaussianProfile]
  have h := integral_cexp_quadratic
    (b := -(π : ℂ)) (by
      simp only [neg_re, ofReal_re]
      exact neg_neg_of_pos Real.pi_pos)
    s 0
  rw [show (fun t : ℝ => Complex.exp (s * (t : ℂ)) * (gaussReal t : ℂ)) =
      fun t : ℝ =>
        Complex.exp (-(π : ℂ) * (t : ℂ) ^ (2 : ℕ) + s * (t : ℂ) + 0) by
    funext t
    rw [gaussReal, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring]
  rw [h]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (π : ℂ) / -(-(π : ℂ)) = 1 by field_simp]
  simp only [one_cpow, one_mul]
  congr 1
  field_simp
  ring

/-- The explicit transform is nonzero at every complex parameter. -/
theorem deningerMeyerLogGaussianSource_mellin_ne_zero (s : ℂ) :
    deningerMeyerStrongLogMellin deningerMeyerLogGaussianSource s ≠ 0 := by
  rw [deningerMeyerLogGaussianSource_mellin]
  exact Complex.exp_ne_zero _

/-- Literal Meyer middle-cohomology class of the log-Gaussian. -/
def deningerMeyerLogGaussianCohomologyClass :
    DeningerMeyerStrongLogCohomology :=
  Submodule.Quotient.mk deningerMeyerLogGaussianSource

/-- Every actual zeroth Xi evaluation survives on the same target-free class. -/
theorem deningerMeyerLogGaussianCohomologyClass_evaluation_ne_zero
    (rho : XiDivisorSupport) :
    deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho)
        deningerMeyerLogGaussianCohomologyClass ≠ 0 := by
  rw [deningerMeyerLogGaussianCohomologyClass,
    deningerMeyerXiSupportJetEvaluationLM_mk]
  simpa [deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] using
      deningerMeyerLogGaussianSource_mellin_ne_zero (rho : ℂ)

/-! ## Reflection-adapted Gaussian -/

/-- Shifted and normalized log-Gaussian whose profile is
`exp (-t/2) exp (-πt²)`.  Translation and scalar closure provide its all-weight
Meyer membership without any divisor input. -/
def deningerMeyerReflectedLogGaussianSource :
    DeningerMeyerStrongLogTarget :=
  Complex.exp (1 / (16 * (π : ℂ))) •
    deningerMeyerStrongLogFlow (-(1 / (4 * π) : ℝ))
      deningerMeyerLogGaussianSource

@[simp]
theorem deningerMeyerReflectedLogGaussianSource_apply (t : ℝ) :
    ((deningerMeyerReflectedLogGaussianSource :
      DeningerMeyerStrongLogTarget) : ℝ → ℂ) t =
      Complex.exp (-(t : ℂ) / 2) * (gaussReal t : ℂ) := by
  change
    Complex.exp (1 / (16 * (π : ℂ))) *
        (gaussReal (t - (-(1 / (4 * π) : ℝ))) : ℂ) = _
  rw [gaussReal, Complex.ofReal_exp, gaussReal, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- Exact centered transform of the reflection-adapted Gaussian. -/
theorem deningerMeyerReflectedLogGaussianSource_mellin (s : ℂ) :
    deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s =
      Complex.exp ((s - 1 / 2) ^ (2 : ℕ) / (4 * π)) := by
  change (deningerMeyerStrongLogMellinLM s)
      (Complex.exp (1 / (16 * (π : ℂ))) •
        deningerMeyerStrongLogFlow (-(1 / (4 * π) : ℝ))
          deningerMeyerLogGaussianSource) = _
  rw [(deningerMeyerStrongLogMellinLM s).map_smul]
  change Complex.exp (1 / (16 * (π : ℂ))) *
      deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogFlow (-(1 / (4 * π) : ℝ))
          deningerMeyerLogGaussianSource) s = _
  rw [deningerMeyerStrongLogMellin_flow,
    deningerMeyerLogGaussianSource_mellin,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

theorem deningerMeyerReflectedLogGaussianSource_mellin_ne_zero (s : ℂ) :
    deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s ≠ 0 := by
  rw [deningerMeyerReflectedLogGaussianSource_mellin]
  exact Complex.exp_ne_zero _

/-- The centered log-Gaussian lies in the positive eigensector of Paugam's
weighted reflection. -/
theorem deningerMeyerReflectedLogGaussianSource_J_fixed :
    deningerMeyerStrongLogJ deningerMeyerReflectedLogGaussianSource =
      deningerMeyerReflectedLogGaussianSource := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  change deningerMeyerStrongLogMellin
      (deningerMeyerStrongLogJ deningerMeyerReflectedLogGaussianSource) s =
    deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s
  rw [deningerMeyerStrongLogMellin_J,
    deningerMeyerReflectedLogGaussianSource_mellin,
    deningerMeyerReflectedLogGaussianSource_mellin]
  congr 1
  ring

/-- Reflected-sector class of the centered log-Gaussian. -/
def deningerMeyerReflectedLogGaussianCohomologyClass :
    DeningerMeyerStrongLogCohomology :=
  Submodule.Quotient.mk deningerMeyerReflectedLogGaussianSource

theorem deningerMeyerReflectedLogGaussianCohomologyClass_J_fixed :
    deningerMeyerStrongLogCohomologyJ
        deningerMeyerReflectedLogGaussianCohomologyClass =
      deningerMeyerReflectedLogGaussianCohomologyClass := by
  rw [deningerMeyerReflectedLogGaussianCohomologyClass,
    deningerMeyerStrongLogCohomologyJ_mk,
    deningerMeyerReflectedLogGaussianSource_J_fixed]

/-- Every actual zeroth Xi evaluation survives on the same reflected-sector
class. -/
theorem deningerMeyerReflectedLogGaussianCohomologyClass_evaluation_ne_zero
    (rho : XiDivisorSupport) :
    deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho)
        deningerMeyerReflectedLogGaussianCohomologyClass ≠ 0 := by
  rw [deningerMeyerReflectedLogGaussianCohomologyClass,
    deningerMeyerXiSupportJetEvaluationLM_mk]
  simpa [deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] using
      deningerMeyerReflectedLogGaussianSource_mellin_ne_zero (rho : ℂ)

/-- Boundedness of one nonvanishing exponential evaluation orbit forces zero
real character rate. -/
theorem re_eq_zero_of_bounded_eigenfunctional_orbit_at_nonzero_vector
    {X : Type*} [AddCommMonoid X] [Module ℂ X]
    (V : ℝ → X →ₗ[ℂ] X) (E : X →ₗ[ℂ] ℂ)
    (u : X) (hu : E u ≠ 0) (z : ℂ)
    (heigen : ∀ c : ℝ,
      E (V c u) = Complex.exp ((c : ℂ) * z) * E u)
    (hbounded : ∃ C : ℝ, ∀ c : ℝ, ‖E (V c u)‖ ≤ C) :
    z.re = 0 := by
  obtain ⟨C, hbound⟩ := hbounded
  let A : ℝ := ‖E u‖
  have hA : 0 < A := norm_pos_iff.mpr hu
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbound 0)
  let T : ℝ := C / A + 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  let c : ℝ := Real.log T / z.re
  by_contra hz
  have hcre : c * z.re = Real.log T := by
    dsimp [c]
    field_simp
  have hre : (((c : ℝ) : ℂ) * z).re = Real.log T := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact hcre
  have h := hbound c
  rw [heigen c, norm_mul, Complex.norm_exp,
    hre, Real.exp_log hT] at h
  change T * A ≤ C at h
  have hTA : T * A = C + A := by
    dsimp [T]
    rw [add_mul, div_mul_cancel₀ C hA.ne']
    ring
  rw [hTA] at h
  linarith

/-- Concrete source-derived bound left open by the target-free Gaussian
construction. -/
def DeningerMeyerLogGaussianCenteredOrbitBounded : Prop :=
  ∀ rho : XiDivisorSupport,
    ∃ C : ℝ, ∀ c : ℝ,
      ‖deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho)
        (deningerMeyerStrongLogCenteredCohomologyFlow c
          deningerMeyerLogGaussianCohomologyClass)‖ ≤ C

/-- **Target-free fixed-source frontier.**  Centered evaluation orbits of the
single explicit log-Gaussian class are bounded at every actual Xi point exactly
when RH holds. -/
theorem deningerMeyerLogGaussianCenteredOrbitBounded_iff_riemannHypothesis :
    DeningerMeyerLogGaussianCenteredOrbitBounded ↔ RiemannHypothesis := by
  constructor
  · intro hbounded
    rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
    intro rho
    apply
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).2
    have hz := re_eq_zero_of_bounded_eigenfunctional_orbit_at_nonzero_vector
      deningerMeyerStrongLogCenteredCohomologyFlow
      (deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho))
      deningerMeyerLogGaussianCohomologyClass
      (deningerMeyerLogGaussianCohomologyClass_evaluation_ne_zero rho)
      ((rho : ℂ) - 1 / 2)
      (deningerMeyerXiSupportEvaluationLM_centeredFlow rho ·
        deningerMeyerLogGaussianCohomologyClass)
      (hbounded rho)
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hz
    linarith
  · intro hRH rho
    have hre : (rho : ℂ).re = 1 / 2 := by
      have hfracture :=
        (xiBoundaryCharacterNeutral_iff_riemannHypothesis.mpr hRH) rho
      exact
        (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
          (rho : ℂ)).mp hfracture
    let E := deningerMeyerXiSupportJetEvaluationLM rho
      (⟨0, xiSupportMultiplicity_pos rho⟩ :
        DeningerArithmeticJetIndex rho)
    refine ⟨‖E deningerMeyerLogGaussianCohomologyClass‖, ?_⟩
    intro c
    rw [deningerMeyerXiSupportEvaluationLM_centeredFlow,
      norm_mul, Complex.norm_exp]
    have hexp : (((c : ℝ) : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
      rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
      rw [hre]
      ring
    rw [hexp, Real.exp_zero, one_mul]

/-- Source-derived bound for the single reflection-adapted Gaussian class. -/
def DeningerMeyerReflectedLogGaussianCenteredOrbitBounded : Prop :=
  ∀ rho : XiDivisorSupport,
    ∃ C : ℝ, ∀ c : ℝ,
      ‖deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho)
        (deningerMeyerStrongLogCenteredCohomologyFlow c
          deningerMeyerReflectedLogGaussianCohomologyClass)‖ ≤ C

/-- **Reflected-sector fixed-source frontier.**  Centered evaluation orbits of
one explicit target-free, Paugam-invariant class are bounded at every actual Xi
point exactly when RH holds. -/
theorem
    deningerMeyerReflectedLogGaussianCenteredOrbitBounded_iff_riemannHypothesis :
    DeningerMeyerReflectedLogGaussianCenteredOrbitBounded ↔
      RiemannHypothesis := by
  constructor
  · intro hbounded
    rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
    intro rho
    apply
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).2
    have hz := re_eq_zero_of_bounded_eigenfunctional_orbit_at_nonzero_vector
      deningerMeyerStrongLogCenteredCohomologyFlow
      (deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho))
      deningerMeyerReflectedLogGaussianCohomologyClass
      (deningerMeyerReflectedLogGaussianCohomologyClass_evaluation_ne_zero rho)
      ((rho : ℂ) - 1 / 2)
      (deningerMeyerXiSupportEvaluationLM_centeredFlow rho ·
        deningerMeyerReflectedLogGaussianCohomologyClass)
      (hbounded rho)
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hz
    linarith
  · intro hRH rho
    have hre : (rho : ℂ).re = 1 / 2 := by
      have hfracture :=
        (xiBoundaryCharacterNeutral_iff_riemannHypothesis.mpr hRH) rho
      exact
        (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
          (rho : ℂ)).mp hfracture
    let E := deningerMeyerXiSupportJetEvaluationLM rho
      (⟨0, xiSupportMultiplicity_pos rho⟩ :
        DeningerArithmeticJetIndex rho)
    refine ⟨‖E deningerMeyerReflectedLogGaussianCohomologyClass‖, ?_⟩
    intro c
    rw [deningerMeyerXiSupportEvaluationLM_centeredFlow,
      norm_mul, Complex.norm_exp]
    have hexp : (((c : ℝ) : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
      rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
      rw [hre]
      ring
    rw [hexp, Real.exp_zero, one_mul]

end

end RHTower
