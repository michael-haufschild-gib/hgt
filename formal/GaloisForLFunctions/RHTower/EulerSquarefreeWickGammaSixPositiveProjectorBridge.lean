import GaloisForLFunctions.RHTower.EulerSquarefreeWickReplicaDensityOrientation
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixRelativeReflectionFraming

/-!
# EWQ–Gamma-six positive projector bridge

The literal EWQ pure state at prime `13` is exactly the bare Gamma-six reflection projector.  Two
canonical half-density extensions then expose a sharp trilemma:

* similarity preserves multiplication and idempotence, but preserves positivity only at neutral
  horizontal grade;
* congruence preserves positivity at every grade, but its idempotence defect is exactly one half of
  Gamma-six curvature;
* multiplication by the fixed arithmetic Pauli-X reporter converts the positive congruence image
  into the multiplicative similarity image.

Consequently, preservation of the literal source Pauli eigenlaw on every physical Xi fibre is
equivalent to RH.  The unconditional missing producer is now precise: a source law forcing that
fixed-reporter covariance after positive completion.
-/

open Complex Matrix
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder MatrixOrder

namespace GaloisForLFunctions.RHTower

noncomputable section

def eulerWickPrimeThirteen : Nat.Primes := ⟨13, by norm_num⟩

def eulerWickPrimeThirteenDepthOne : PrimePowerClockIndex :=
  (eulerWickPrimeThirteen, 0)

theorem quadraticResidueProductPrimeCoefficient_thirteen :
    quadraticResidueProductPrimeCoefficient eulerWickPrimeThirteen = 1 := by
  have hp : IsUnit (((eulerWickPrimeThirteen : Nat.Primes).1 : ℕ) : ZMod 12) := by
    rw [ZMod.isUnit_iff_coprime]
    norm_num [eulerWickPrimeThirteen]
  rw [quadraticResidueProductPrimeCoefficient_eq_quadraticCharacterTwelve_of_isUnit
    eulerWickPrimeThirteen hp]
  change quadraticCharacterTwelve (13 : ZMod 12) = 1
  rw [show (13 : ZMod 12) = 1 by decide, map_one]

theorem eulerWickQuadraticDepthCharacter_thirteen :
    eulerWickQuadraticDepthCharacter eulerWickPrimeThirteenDepthOne = 1 := by
  simp [eulerWickQuadraticDepthCharacter, eulerWickPrimeThirteenDepthOne,
    quadraticResidueProductPrimeCoefficient_thirteen]

theorem eulerWickReplicaPureProjector_thirteen_eq_bare :
    eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne =
      _root_.RHTower.sourceHorizontalGammaSixBareReflectionIdempotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickReplicaPureProjector_apply,
      eulerWickQuadraticDepthCharacter_thirteen,
      _root_.RHTower.sourceHorizontalGammaSixBareReflectionIdempotent]

theorem eulerWickReplicaPureProjector_thirteen_mul_pauliX :
    eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne *
        eulerWickReplicaPauliX =
      eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickReplicaPauliX, Matrix.mul_apply, Fin.sum_univ_two,
      eulerWickReplicaPureProjector_apply,
      eulerWickQuadraticDepthCharacter_thirteen]

def eulerWickGammaSixHalfDensitySimilarity (a : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  _root_.RHTower.sourceHorizontalGammaSixHalfDensityGauge a * M *
    _root_.RHTower.sourceHorizontalGammaSixHalfDensityGaugeInv a

def eulerWickGammaSixHalfDensityCongruence (a : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (_root_.RHTower.sourceHorizontalGammaSixHalfDensityGauge a)ᴴ * M *
    _root_.RHTower.sourceHorizontalGammaSixHalfDensityGauge a

theorem sourceHorizontalGammaSixHalfDensityGauge_conjTranspose (a : ℝ) :
    (_root_.RHTower.sourceHorizontalGammaSixHalfDensityGauge a)ᴴ =
      _root_.RHTower.sourceHorizontalGammaSixHalfDensityGauge a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [_root_.RHTower.sourceHorizontalGammaSixHalfDensityGauge,
      Matrix.conjTranspose_apply, -Complex.ofReal_exp]

theorem eulerWickGammaSixHalfDensitySimilarity_zero
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    eulerWickGammaSixHalfDensitySimilarity 0 M = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickGammaSixHalfDensitySimilarity,
      _root_.RHTower.sourceHorizontalGammaSixHalfDensityGauge,
      _root_.RHTower.sourceHorizontalGammaSixHalfDensityGaugeInv,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem eulerWickGammaSixHalfDensitySimilarity_projector_thirteen (a : ℝ) :
    eulerWickGammaSixHalfDensitySimilarity a
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) =
      _root_.RHTower.sourceHorizontalGammaSixTransportedReflectionIdempotent a := by
  rw [eulerWickGammaSixHalfDensitySimilarity,
    eulerWickReplicaPureProjector_thirteen_eq_bare,
    _root_.RHTower.sourceHorizontalGammaSixTransportedReflectionIdempotent_eq_halfDensity_conj]

theorem eulerWickGammaSixHalfDensityCongruence_projector_thirteen_posSemidef (a : ℝ) :
    (eulerWickGammaSixHalfDensityCongruence a
      (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne)).PosSemidef := by
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same
    (eulerWickReplicaPureProjector_posSemidef eulerWickPrimeThirteenDepthOne)
    (_root_.RHTower.sourceHorizontalGammaSixHalfDensityGauge a)

theorem eulerWickGammaSixHalfDensityCongruence_projector_thirteen_eq (a : ℝ) :
    eulerWickGammaSixHalfDensityCongruence a
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) =
      !![((Real.exp a : ℝ) : ℂ) / 2, 1 / 2;
         1 / 2, ((Real.exp (-a) : ℝ) : ℂ) / 2] := by
  rw [eulerWickGammaSixHalfDensityCongruence,
    sourceHorizontalGammaSixHalfDensityGauge_conjTranspose,
    eulerWickReplicaPureProjector_thirteen_eq_bare]
  have hpp :
      Real.exp (a / 2) * (1 / 2 : ℝ) * Real.exp (a / 2) = Real.exp a / 2 := by
    calc
      Real.exp (a / 2) * (1 / 2 : ℝ) * Real.exp (a / 2) =
          (Real.exp (a / 2) * Real.exp (a / 2)) / 2 := by ring
      _ = Real.exp a / 2 := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hpm :
      Real.exp (a / 2) * (1 / 2 : ℝ) * Real.exp (-a / 2) = 1 / 2 := by
    calc
      Real.exp (a / 2) * (1 / 2 : ℝ) * Real.exp (-a / 2) =
          (Real.exp (a / 2) * Real.exp (-a / 2)) / 2 := by ring
      _ = 1 / 2 := by
        rw [← Real.exp_add, show a / 2 + -a / 2 = 0 by ring, Real.exp_zero]
  have hmp :
      Real.exp (-a / 2) * (1 / 2 : ℝ) * Real.exp (a / 2) = 1 / 2 := by
    calc
      Real.exp (-a / 2) * (1 / 2 : ℝ) * Real.exp (a / 2) =
          Real.exp (a / 2) * (1 / 2 : ℝ) * Real.exp (-a / 2) := by ring
      _ = 1 / 2 := hpm
  have hmm :
      Real.exp (-a / 2) * (1 / 2 : ℝ) * Real.exp (-a / 2) = Real.exp (-a) / 2 := by
    calc
      Real.exp (-a / 2) * (1 / 2 : ℝ) * Real.exp (-a / 2) =
          (Real.exp (-a / 2) * Real.exp (-a / 2)) / 2 := by ring
      _ = Real.exp (-a) / 2 := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hhalf : (((2 : ℝ)⁻¹ : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [_root_.RHTower.sourceHorizontalGammaSixHalfDensityGauge,
      _root_.RHTower.sourceHorizontalGammaSixBareReflectionIdempotent,
      Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_exp]
  ·
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hpp
    simp only [Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_ofNat, one_div] at hc
    rw [hhalf] at hc
    exact hc
  ·
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hpm
    simp only [Complex.ofReal_mul, one_div] at hc
    rw [hhalf] at hc
    exact hc
  ·
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hmp
    simp only [Complex.ofReal_mul, one_div] at hc
    rw [hhalf] at hc
    exact hc
  ·
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hmm
    simp only [Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_ofNat, one_div] at hc
    rw [hhalf] at hc
    exact hc

/-- The fixed arithmetic reporter converts the positive congruence image into the multiplicative
similarity image.  It is invisible at the source projector, but becomes the full non-self-adjoint
orientation after half-density transport. -/
theorem eulerWickGammaSix_positiveCongruence_mul_pauliX_eq_multiplicativeSimilarity (a : ℝ) :
    eulerWickGammaSixHalfDensityCongruence a
          (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) *
        eulerWickReplicaPauliX =
      eulerWickGammaSixHalfDensitySimilarity a
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) := by
  rw [eulerWickGammaSixHalfDensityCongruence_projector_thirteen_eq,
    eulerWickGammaSixHalfDensitySimilarity_projector_thirteen]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickReplicaPauliX, Matrix.mul_apply, Fin.sum_univ_two,
      _root_.RHTower.sourceHorizontalGammaSixTransportedReflectionIdempotent]

theorem eulerWickGammaSixHalfDensityCongruence_projector_thirteen_squareDefect (a : ℝ) :
    let Q := eulerWickGammaSixHalfDensityCongruence a
      (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne)
    Q * Q - Q =
      ((_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) / 2) • Q := by
  dsimp only
  rw [eulerWickGammaSixHalfDensityCongruence_projector_thirteen_eq]
  have hcurv :
      _root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a =
        Real.exp a + Real.exp (-a) - 2 := by
    rw [_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
      Real.cosh_eq]
    ring
  rw [hcurv]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [-Complex.ofReal_exp]
  all_goals
    rw [Real.exp_neg]
    push_cast
    field_simp [Real.exp_ne_zero]

theorem eulerWickGammaSixHalfDensityCongruence_projector_thirteen_idempotent_iff (a : ℝ) :
    let Q := eulerWickGammaSixHalfDensityCongruence a
      (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne)
    Q * Q = Q ↔ a = 0 := by
  dsimp only
  constructor
  · intro h
    have hdef :
        eulerWickGammaSixHalfDensityCongruence a
              (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) *
            eulerWickGammaSixHalfDensityCongruence a
              (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) -
            eulerWickGammaSixHalfDensityCongruence a
              (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) = 0 :=
      sub_eq_zero.mpr h
    rw [eulerWickGammaSixHalfDensityCongruence_projector_thirteen_squareDefect] at hdef
    have h01 := congrFun (congrFun hdef (0 : Fin 2)) (1 : Fin 2)
    rw [eulerWickGammaSixHalfDensityCongruence_projector_thirteen_eq] at h01
    norm_num at h01
    have hcurv : _root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a = 0 := by
      exact_mod_cast h01
    exact (_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff a).1
      hcurv
  · rintro rfl
    rw [eulerWickGammaSixHalfDensityCongruence_projector_thirteen_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem eulerWickGammaSix_positiveCongruence_eq_multiplicativeSimilarity_iff (a : ℝ) :
    eulerWickGammaSixHalfDensityCongruence a
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) =
      eulerWickGammaSixHalfDensitySimilarity a
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) ↔
      a = 0 := by
  constructor
  · intro h
    have hsim := eulerWickGammaSixHalfDensitySimilarity_projector_thirteen a
    have hidem :
        eulerWickGammaSixHalfDensityCongruence a
              (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) *
            eulerWickGammaSixHalfDensityCongruence a
              (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) =
          eulerWickGammaSixHalfDensityCongruence a
            (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) := by
      rw [h, hsim]
      exact _root_.RHTower.sourceHorizontalGammaSixTransportedReflectionIdempotent_sq a
    exact (eulerWickGammaSixHalfDensityCongruence_projector_thirteen_idempotent_iff a).1 hidem
  · rintro rfl
    rw [eulerWickGammaSixHalfDensityCongruence_projector_thirteen_eq,
      eulerWickGammaSixHalfDensitySimilarity_zero,
      eulerWickReplicaPureProjector_thirteen_eq_bare]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [_root_.RHTower.sourceHorizontalGammaSixBareReflectionIdempotent]

/-- The source Pauli eigenlaw survives positive half-density completion exactly at neutral
horizontal grade. -/
theorem eulerWickGammaSix_positiveCongruence_pauliX_fixed_iff (a : ℝ) :
    eulerWickGammaSixHalfDensityCongruence a
          (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) *
        eulerWickReplicaPauliX =
      eulerWickGammaSixHalfDensityCongruence a
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) ↔
      a = 0 := by
  rw [eulerWickGammaSix_positiveCongruence_mul_pauliX_eq_multiplicativeSimilarity]
  simpa only [eq_comm] using
    eulerWickGammaSix_positiveCongruence_eq_multiplicativeSimilarity_iff a

def EulerWickGammaSixHalfDensitySimilarityPositive (a : ℝ) : Prop :=
  ∀ M : Matrix (Fin 2) (Fin 2) ℂ, M.PosSemidef →
    (eulerWickGammaSixHalfDensitySimilarity a M).PosSemidef

theorem eulerWickGammaSixHalfDensitySimilarityPositive_iff (a : ℝ) :
    EulerWickGammaSixHalfDensitySimilarityPositive a ↔ a = 0 := by
  constructor
  · intro h
    have htarget := h
      (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne)
      (eulerWickReplicaPureProjector_posSemidef eulerWickPrimeThirteenDepthOne)
    rw [eulerWickGammaSixHalfDensitySimilarity_projector_thirteen] at htarget
    exact (_root_.RHTower.sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose_eq_iff
      a).1 htarget.1
  · rintro rfl
    intro M hM
    rwa [eulerWickGammaSixHalfDensitySimilarity_zero]

theorem sourceHorizontalGammaSixTransportedReflectionIdempotent_posSemidef_iff (a : ℝ) :
    (_root_.RHTower.sourceHorizontalGammaSixTransportedReflectionIdempotent a).PosSemidef ↔
      a = 0 := by
  constructor
  · intro h
    exact (_root_.RHTower.sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose_eq_iff a).1
      h.1
  · rintro rfl
    rw [(_root_.RHTower.sourceHorizontalGammaSixTransportedReflectionIdempotent_eq_bare_iff
      0).2 rfl]
    rw [← eulerWickReplicaPureProjector_thirteen_eq_bare]
    exact eulerWickReplicaPureProjector_posSemidef eulerWickPrimeThirteenDepthOne

theorem eulerWickGammaSixHalfDensitySimilarity_projector_thirteen_posSemidef_iff (a : ℝ) :
    (eulerWickGammaSixHalfDensitySimilarity a
      (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne)).PosSemidef ↔
      a = 0 := by
  rw [eulerWickGammaSixHalfDensitySimilarity_projector_thirteen,
    sourceHorizontalGammaSixTransportedReflectionIdempotent_posSemidef_iff]

theorem eulerWickGammaSixPrimePhysicalProjector_posSemidef_iff
    (q : _root_.RHTower.XiZeroCopy) :
    (eulerWickGammaSixHalfDensitySimilarity
      (Real.log (13 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)
      (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne)).PosSemidef ↔
        (q.1 : ℂ).re = 1 / 2 := by
  rw [eulerWickGammaSixHalfDensitySimilarity_projector_thirteen_posSemidef_iff]
  have hlog : Real.log (13 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [mul_eq_zero]
  simp only [hlog, false_or]
  exact _root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1

/-- Every actual Xi multiplicity copy receives a positive multiplicative image of the fixed EWQ
projector.  This is the exact global positivity gate. -/
def EulerWickGammaSixPhysicalProjectorsPositive : Prop :=
  ∀ q : _root_.RHTower.XiZeroCopy,
    (eulerWickGammaSixHalfDensitySimilarity
      (Real.log (13 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)
      (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne)).PosSemidef

theorem eulerWickGammaSixPhysicalProjectorsPositive_iff_riemannHypothesis :
    EulerWickGammaSixPhysicalProjectorsPositive ↔
      RiemannHypothesis := by
  constructor
  · intro hpositive
    apply _root_.RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline :=
      (eulerWickGammaSixPrimePhysicalProjector_posSemidef_iff q).1 (hpositive q)
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [_root_.RHTower.xiSpectralPoint]
    · simp [_root_.RHTower.xiSpectralPoint, hline]
  · intro hRH q
    apply (eulerWickGammaSixPrimePhysicalProjector_posSemidef_iff q).2
    exact _root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1

/-- Positive congruence transports the arithmetic projector unconditionally.  Requiring its fixed
Pauli-X reporter law on every physical Xi fibre is exactly RH. -/
def EulerWickGammaSixPhysicalReporterCovariant : Prop :=
  ∀ q : _root_.RHTower.XiZeroCopy,
    let a := Real.log (13 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1
    eulerWickGammaSixHalfDensityCongruence a
          (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) *
        eulerWickReplicaPauliX =
      eulerWickGammaSixHalfDensityCongruence a
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne)

theorem eulerWickGammaSixPhysicalReporterCovariant_iff_riemannHypothesis :
    EulerWickGammaSixPhysicalReporterCovariant ↔
      RiemannHypothesis := by
  constructor
  · intro hcov
    apply _root_.RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hzero :=
      (eulerWickGammaSix_positiveCongruence_pauliX_fixed_iff
        (Real.log (13 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)).1 (hcov q)
    have hlog : Real.log (13 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hrate : _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hlog
    have hline :=
      (_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hrate
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [_root_.RHTower.xiSpectralPoint]
    · simp [_root_.RHTower.xiSpectralPoint, hline]
  · intro hRH q
    apply (eulerWickGammaSix_positiveCongruence_pauliX_fixed_iff
      (Real.log (13 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)).2
    rw [(_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2
      (_root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1), mul_zero]

end

end GaloisForLFunctions.RHTower
