import GaloisForLFunctions.HTGeometry.DirichletMaurerCartanMellinOrbitLaw
import GaloisForLFunctions.HTGeometry.FiniteLiouvillianHodgeGreenLaw
import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelopeBVShift
import GaloisForLFunctions.HTGeometry.MellinAntiderivativeStep
import GaloisForLFunctions.HTGeometry.SeibergWitten.FlatConnection
import GaloisForLFunctions.HTGeometry.StokesFormalContactInvariance
import GaloisForLFunctions.RHTower.Deninger.DeningerDlogPeriod
import GaloisForLFunctions.RHTower.Deninger.DeningerHarmonicMode

/-!
# Audit of the saddle/de Rham mechanisms in arXiv:2408.13292

This file transfers the mathematically valid local identities from arXiv:2408.13292 to concrete
objects already present in the corpus and formalizes counterexamples to its invalid transitions.
In particular:

* the two Mellin antiderivative identities are valid on their convergence domains;
* a critical radial exponent detects the critical line but does not locate zeta zeros;
* Hodge--Green decomposition retains a stationary summand;
* covariantly constant sections need not vanish;
* a closed logarithmic differential need not be exact;
* the two-dimensional one-form Hodge star has square `-1`, so a nonzero one-form is not fixed by it;
* on the unit circle `x * conj x = 1`, whereas `x ^ 2 = 1` is false in general;
* neither tangent reparametrization nor closedness erases nonzero arithmetic data.

No theorem in this file asserts the Riemann hypothesis or derives a zeta zero from these identities.
-/

open MeasureTheory Set Complex
open scoped ComplexConjugate PowerSeries

namespace RHTower

open GaloisForLFunctions.IrregularStokes.FormalUniformizer
open GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Complex right half-plane, packaging the Mellin convergence condition. -/
abbrev GhaboussiRightHalfPlane := {s : ℂ // 0 < s.re}

/-- A point in the open right half-plane cannot be zero. -/
theorem ghaboussiRightHalfPlane_coe_ne_zero (s : GhaboussiRightHalfPlane) :
    (s : ℂ) ≠ 0 := by
  intro h
  exact (ne_of_gt s.property) (congrArg Complex.re h)

/-- Positive real cutoffs, packaging the endpoint condition for Mellin integration. -/
abbrev GhaboussiPositiveReal := {p : ℝ // 0 < p}

/-- Corrected tail identity from the paper; positivity and convergence are carried by subtypes. -/
theorem ghaboussi_positive_tail_mellin_identity (p : GhaboussiPositiveReal)
    (s : GhaboussiRightHalfPlane) :
    ((p : ℝ) : ℂ) ^ (-(s : ℂ)) =
      (s : ℂ) * ∫ x in Ioi (p : ℝ),
        (x : ℂ) ^ (-(s : ℂ) - 1) := by
  rw [GaloisForLFunctions.HTGeometry.integral_Ioi_cpow_tail s.property]
  · field_simp [ghaboussiRightHalfPlane_coe_ne_zero s]
  · exact p.property

/-- Corrected head identity from the paper on every positive real cutoff. -/
theorem ghaboussi_positive_head_mellin_identity (p : GhaboussiPositiveReal)
    (s : GhaboussiRightHalfPlane) :
    ((p : ℝ) : ℂ) ^ (2 * (s : ℂ)) =
      (2 * (s : ℂ)) * ∫ x in (0 : ℝ)..(p : ℝ),
        (x : ℂ) ^ (2 * (s : ℂ) - 1) := by
  have hre : -1 < (2 * (s : ℂ) - 1).re := by
    rw [Complex.sub_re, Complex.mul_re, Complex.one_re]
    rw [show (2 : ℂ).re = 2 by exact Complex.ofReal_re 2,
      show (2 : ℂ).im = 0 by exact Complex.ofReal_im 2,
      zero_mul, sub_zero]
    linarith [s.property]
  rw [integral_cpow (Or.inl hre)]
  have hs₀ : (s : ℂ) ≠ 0 := ghaboussiRightHalfPlane_coe_ne_zero s
  have hs : 2 * (s : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero hs₀
  rw [show 2 * (s : ℂ) - 1 + 1 = 2 * (s : ℂ) by ring]
  simp only [ofReal_zero, zero_cpow hs, sub_zero]
  field_simp [hs, hs₀]

/-- Bases above one, packaging nondegeneracy of the radial character. -/
abbrev GhaboussiBaseAboveOne := {r : ℝ // 1 < r}

/-- The paper's real critical parameter, with `σ = 1/2` internalized. -/
abbrev GhaboussiCriticalRealPart := {σ : ℝ // σ = 1 / 2}

/-- Bundled critical real parameters make the paper's exponent exactly zero. -/
theorem ghaboussiCriticalRealPart_exponent_eq_zero
    (σ : GhaboussiCriticalRealPart) :
    2 * (σ : ℝ) - 1 = 0 := by
  rw [σ.property]
  ring

/-- At the real critical parameter, the paper's complex power is exactly constant. -/
theorem ghaboussi_critical_real_power_eq_one
    (σ : GhaboussiCriticalRealPart) (z : ℂ) :
    (-z) ^ ((2 * (σ : ℝ) - 1 : ℝ) : ℂ) = 1 := by
  simp [ghaboussiCriticalRealPart_exponent_eq_zero σ]

/-- Hence its first complex derivative vanishes, the valid part of the saddle calculation. -/
theorem ghaboussi_critical_real_power_hasDerivAt_zero
    (σ : GhaboussiCriticalRealPart) (z : ℂ) :
    HasDerivAt (fun w : ℂ =>
      (-w) ^ ((2 * (σ : ℝ) - 1 : ℝ) : ℂ)) 0 z := by
  simpa [ghaboussiCriticalRealPart_exponent_eq_zero σ] using
    (hasDerivAt_const z (1 : ℂ))

/-- The paper's exponent `2 Re(ρ)-1` detects the critical line only through radial unit norm. -/
theorem ghaboussi_radial_character_norm_one_iff
    (r : GhaboussiBaseAboveOne) (ρ : ℂ) :
    ‖((r : ℝ) : ℂ) ^ (2 * ρ - 1)‖ = 1 ↔ ρ.re = 1 / 2 :=
  GaloisForLFunctions.norm_radial_character_eq_one_iff r.property ρ

/-- Concrete finite Hodge--Green receiver: the stationary part survives beside the exact part. -/
theorem ghaboussi_finite_hodgeGreen_system
    (n : ℕ) (energy : Fin n → ℝ)
    (x : EuclideanSpace ℂ (Fin n × Fin n)) :
    HTGeometry.transitionGapLiouvillian energy
          (HTGeometry.transitionGapStationaryPart energy x) = 0 ∧
      HTGeometry.transitionGapStationaryPart energy x +
          HTGeometry.transitionGapLiouvillian energy
            (HTGeometry.transitionGapGreenPrimitive energy x) = x := by
  exact ⟨HTGeometry.transitionGapLiouvillian_stationaryPart_eq_zero energy x,
    HTGeometry.transitionGap_hodgeGreen_decomposition energy x⟩

/-- Covariant constancy does not imply vanishing: the flat unit section is parallel and nonzero. -/
theorem ghaboussi_parallel_section_can_be_nonzero (x : FourSpace) :
    flatDeterminantLineCovariantDerivative
          (flatConstantDeterminantLineSection 1) x = 0 ∧
      flatConstantDeterminantLineSection 1 x ≠ 0 := by
  exact ⟨flatDeterminantLineCovariantDerivative_constant 1 x, by
    simp [flatConstantDeterminantLineSection]⟩

/-- Corpus counterexample to closed-implies-exact: the stage-one `dlog` is closed and not exact. -/
theorem ghaboussi_dlog_closed_not_exact :
    (∀ z ∈ deningerStageTorus 1,
      extDeriv (deningerDlogForm 1 0) z = 0) ∧
    ¬ ∃ h : DeningerStageForm 1 0, DeningerIsHolomorphicForm h ∧
      ∀ z ∈ deningerStageTorus 1,
        extDeriv h z = deningerDlogForm 1 0 z := by
  constructor
  · intro z hz
    exact deningerDlogForm_closed 0 hz
  · exact deningerDlogForm_not_exact

/-- For the two-dimensional one-form star, a `+1` fixed vector must vanish. -/
theorem ghaboussi_oneForm_hodge_fixed_iff_zero (a : ℂ × ℂ) :
    deningerCxStar a = a ↔ a = 0 := by
  constructor
  · intro h
    apply neg_eq_self.mp
    calc
      -a = deningerCxStar (deningerCxStar a) := (deningerCxStar_star a).symm
      _ = deningerCxStar a := congrArg deningerCxStar h
      _ = a := h
  · rintro rfl
    simp [deningerCxStar]

/-- Every decaying Deninger mode is nonzero because its exponential profile is positive. -/
theorem ghaboussi_deningerMode_ne_zero (μ r : ℝ) :
    deningerMode μ r ≠ 0 := by
  intro h
  have hprofile : (deningerModeProfile μ r : ℂ) = 0 := by
    simpa using congrArg Prod.fst h
  have hreal : deningerModeProfile μ r = 0 := Complex.ofReal_eq_zero.mp hprofile
  exact (deningerModeProfile_pos μ r).ne' hreal

/-- Nonzero Deninger modes refute `⋆ω = ω` for the paper's two-dimensional one-form setting. -/
theorem ghaboussi_deningerMode_not_selfDual (μ r : ℝ) :
    deningerCxStar (deningerMode μ r) ≠ deningerMode μ r := by
  intro h
  exact ghaboussi_deningerMode_ne_zero μ r
    ((ghaboussi_oneForm_hodge_fixed_iff_zero (deningerMode μ r)).mp h)

/-- A closed, coclosed, nontrivially chiral unit-frequency one-form mode. -/
theorem ghaboussi_unitFrequency_mode_hodge_system (r : ℝ) :
    HasDerivAt (fun r => (deningerMode 1 r).2)
        (Complex.I * (1 : ℂ) * (deningerMode 1 r).1) r ∧
      HasDerivAt (fun r => (deningerMode 1 r).1)
        (-(Complex.I * (1 : ℂ) * (deningerMode 1 r).2)) r ∧
      deningerCxStar (deningerMode 1 r) =
        Complex.I • deningerMode 1 r := by
  refine ⟨deningerMode_closed one_ne_zero r, deningerMode_coclosed one_ne_zero r, ?_⟩
  simpa [deningerFreqSign] using deningerMode_chirality 1 r

/-- Denominator from the paper after its unit-circle substitution. -/
noncomputable def ghaboussiCircleDenominator (θ : ℝ) : ℂ :=
  Complex.exp (deningerCircle θ ^ 2) - 1

/-- Quarter-turn point on the corpus's Deninger circle. -/
@[simp]
theorem ghaboussi_deningerCircle_pi_div_two :
    deningerCircle (Real.pi / 2) = Complex.I := by
  simp [deningerCircle]

/-- Correct unit-circle identity: conjugate product, not ordinary square, is one. -/
theorem ghaboussi_unitCircle_conjugate_product (θ : ℝ) :
    deningerCircle θ * conj (deningerCircle θ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [deningerCircle, Complex.norm_exp_ofReal_mul_I]

/-- Direct counterexample to the paper's replacement of `x * conj x` by `x ^ 2`. -/
theorem ghaboussi_unitCircle_square_ne_one :
    deningerCircle (Real.pi / 2) ^ 2 ≠ 1 := by
  rw [ghaboussi_deningerCircle_pi_div_two, Complex.I_sq]
  exact neg_ne_self.mpr one_ne_zero

/-- Consequently the paper's transformed exponential denominator is not constant. -/
theorem ghaboussi_unitCircle_denominator_not_constant :
    ghaboussiCircleDenominator 0 ≠
      ghaboussiCircleDenominator (Real.pi / 2) := by
  rw [ghaboussiCircleDenominator, ghaboussiCircleDenominator,
    deningerCircle_zero, ghaboussi_deningerCircle_pi_div_two, Complex.I_sq]
  intro h
  simp only [one_pow] at h
  have hexp : Complex.exp (1 : ℂ) = Complex.exp (-1 : ℂ) := by
    simpa using congrArg (fun z : ℂ => z + 1) h
  have hre := congrArg Complex.re hexp
  have hre' : Real.exp 1 = Real.exp (-1) := by
    simpa [Complex.exp_re] using hre
  have : (1 : ℝ) = -1 := Real.exp_injective hre'
  linarith

/-- Tangent coordinate changes, with their unit condition bundled into the source. -/
abbrev GhaboussiTangentPowerSeries :=
  {u : PowerSeries ℂ // u.constantCoeff = 1}

/-- Series whose nonzero constant coefficient is bundled into the source. -/
abbrev GhaboussiNonzeroConstantPowerSeries :=
  {f : PowerSeries ℂ // f.constantCoeff ≠ 0}

/-- A tangent coordinate change cannot turn a nonzero constant coefficient into zero. -/
theorem ghaboussi_tangentReparametrization_preserves_nonzero_constant
    (E : ℕ) (u : GhaboussiTangentPowerSeries)
    (f : GhaboussiNonzeroConstantPowerSeries) :
    (tangentReparametrization E u u.property f).constantCoeff ≠ 0 :=
  tangentReparametrization_constantCoeff_ne_zero E u u.property f f.property

/-- The complex von Mangoldt current is nonzero, witnessed symbolically at the prime two. -/
theorem ghaboussi_complexVonMangoldt_ne_zero :
    GaloisForLFunctions.HTGeometry.complexVonMangoldt ≠ 0 := by
  intro hzero
  have htwo := congrArg
    (fun f : GaloisForLFunctions.HTGeometry.ComplexArithmeticFunction => f 2) hzero
  have hlog : (Real.log 2 : ℂ) = 0 := by
    simpa [GaloisForLFunctions.HTGeometry.complexVonMangoldt,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] using htwo
  have hreal : Real.log 2 = 0 := Complex.ofReal_eq_zero.mp hlog
  exact (Real.log_pos one_lt_two).ne' hreal

/-- A closed universal Dirichlet form retains a nonzero arithmetic contraction. -/
theorem ghaboussi_closed_dirichlet_form_has_nonzero_arithmetic_contraction :
    GaloisForLFunctions.HTGeometry.dirichletMaurerCartanExteriorDerivative = 0 ∧
      GaloisForLFunctions.HTGeometry.arithmeticLogDerivation.liftKaehlerDifferential
          GaloisForLFunctions.HTGeometry.dirichletMaurerCartanForm =
        GaloisForLFunctions.HTGeometry.complexVonMangoldt ∧
      GaloisForLFunctions.HTGeometry.complexVonMangoldt ≠ 0 := by
  exact ⟨GaloisForLFunctions.HTGeometry.dirichletMaurerCartanExteriorDerivative_eq_zero,
    GaloisForLFunctions.HTGeometry.contract_dirichletMaurerCartanForm_eq_vonMangoldt,
    ghaboussi_complexVonMangoldt_ne_zero⟩

end RHTower
