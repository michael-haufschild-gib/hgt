import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonFrobeniusMonodromy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingNonlinearBoundaryHelicityFluxDichotomy

/-!
# Total renormalized BM angular period and intermediate-pole exclusion

At a negative-branch target QNM, the two quadratic fields in the complete `++-` Schur source are
evaluated at

`nu_pp = omega_N^- - omega_k^- = -2 I (N-k)`

and

`nu_pm = omega_N^- - omega_n^+ = -2 chi - 2 I (N-n)`.

The BM damping lattice is `2 L + 3/2`.  A `++` collision in the open physical angular strip would
equate this half-integral lattice with an integral lattice.  A `+-` collision would instead force
the sum of two open half-strip coordinates to an excluded endpoint.  Thus neither intermediate
response has a BM pole in the nonconstant discrete-plus-continuum angular spectrum.  A collision
on the closed strip can occur only at `Im eta = ±1/2`, the zero-angular-eigenvalue edge.  That
exceptional harmonic is a stationary mass/charge completion, not a radiative BM master mode, and
is therefore carried by the augmented boundary block rather than its meromorphic resolvent.

For the nonlinear self-energy, integrate the gauge-fixed Einstein--Teukolsky Lagrange identity on
a truncated cusp and take its finite part.  Local bulk terms and real cusp counterterms contribute
only a real principal value.  The retarded-minus-advanced boundary concomitant is twice `I` times
the complete horizon-plus-normalizable-boundary radiation flux.  After unit Wronskian
normalization, the retarded period is therefore uniquely

`P_ret = FP_conservative + I * ||Radiation(direct,mixing)||^(2 : ℕ)`.

The exact BM radiation map has a nonzero direct coordinate for every nonzero theta seed.  Its
orthogonal-helicity coordinate adds a nonnegative square.  Hence the total period cannot vanish,
regardless of the real finite part or of coherent cancellation among named bulk pieces.  This is
a total Green-boundary statement; it does not identify an individual cyclic bulk pairing with a
Hermitian Gram.
-/

open Complex Real
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-! ## Shifted intermediate frequencies -/

/-- Frequency at which the `++` response is sampled by a negative-branch target. -/
def d4BMTargetShiftedPlusPlusIntermediateFrequency
    (k N : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalQNMMinus N chi - d4BMCausalQNMMinus k chi

/-- Frequency at which the `+-` response is sampled by a negative-branch target. -/
def d4BMTargetShiftedPlusMinusIntermediateFrequency
    (n N : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalQNMMinus N chi - d4BMCausalQNMPlus n chi

theorem d4BMTargetShiftedPlusPlusIntermediateFrequency_eq
    (k N : ℕ) (chi : ℂ) :
    d4BMTargetShiftedPlusPlusIntermediateFrequency k N chi =
      -2 * Complex.I * ((N : ℂ) - (k : ℂ)) := by
  simp [d4BMTargetShiftedPlusPlusIntermediateFrequency,
    d4BMCausalQNMMinus, d4BMCausalDecay]
  ring

theorem d4BMTargetShiftedPlusMinusIntermediateFrequency_eq
    (n N : ℕ) (chi : ℂ) :
    d4BMTargetShiftedPlusMinusIntermediateFrequency n N chi =
      -2 * chi - 2 * Complex.I * ((N : ℂ) - (n : ℂ)) := by
  simp [d4BMTargetShiftedPlusMinusIntermediateFrequency,
    d4BMCausalQNMMinus, d4BMCausalQNMPlus, d4BMCausalDecay]
  ring

/-- Square-root angular momenta of every nonconstant nonnegative self-adjoint angular shell lie
in this open strip.  The excluded endpoints `± I/2` both represent angular eigenvalue zero. -/
def d4BMNonconstantPhysicalAngularMomentum (eta : ℂ) : Prop :=
  -(1 / 2 : ℝ) < eta.im ∧ eta.im < 1 / 2

theorem d4BMTargetShiftedPlusPlusIntermediateFrequency_ne_qnmPlus
    (k N L : ℕ) (chi eta : ℂ)
    (heta : d4BMNonconstantPhysicalAngularMomentum eta) :
    d4BMTargetShiftedPlusPlusIntermediateFrequency k N chi ≠
      d4BMCausalQNMPlus L eta := by
  intro h
  have him := congrArg Complex.im h
  rw [d4BMTargetShiftedPlusPlusIntermediateFrequency_eq] at him
  simp [d4BMCausalQNMPlus, d4BMCausalDecay, Complex.mul_im] at him
  norm_num at him
  by_cases hN : N ≤ L + k
  · have hcast : (N : ℝ) ≤ (L : ℝ) + (k : ℝ) := by exact_mod_cast hN
    linarith [heta.2]
  · have hsucc : L + k + 1 ≤ N := by omega
    have hcast : (L : ℝ) + (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hsucc
    linarith [heta.1]

theorem d4BMTargetShiftedPlusPlusIntermediateFrequency_ne_qnmMinus
    (k N L : ℕ) (chi eta : ℂ)
    (heta : d4BMNonconstantPhysicalAngularMomentum eta) :
    d4BMTargetShiftedPlusPlusIntermediateFrequency k N chi ≠
      d4BMCausalQNMMinus L eta := by
  intro h
  have him := congrArg Complex.im h
  rw [d4BMTargetShiftedPlusPlusIntermediateFrequency_eq] at him
  simp [d4BMCausalQNMMinus, d4BMCausalDecay, Complex.mul_im] at him
  norm_num at him
  by_cases hN : N ≤ L + k
  · have hcast : (N : ℝ) ≤ (L : ℝ) + (k : ℝ) := by exact_mod_cast hN
    linarith [heta.1]
  · have hsucc : L + k + 1 ≤ N := by omega
    have hcast : (L : ℝ) + (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hsucc
    linarith [heta.2]

/-- The analytically continued Xi momentum lies strictly between the constant-mode edge and the
physical line. -/
theorem d4BMXiMixedHorizonAngularMomentum_im_mem_openHalf (q : XiZeroCopy) :
    0 < (d4BMXiMixedHorizonAngularMomentum q).im ∧
      (d4BMXiMixedHorizonAngularMomentum q).im < 1 / 2 := by
  rw [d4BMXiMixedHorizonAngularMomentum,
    thetaCuspHawkingBMContinuedAngularMomentum_xi_im]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  constructor <;> linarith

theorem d4BMXiTargetShiftedPlusMinusIntermediateFrequency_ne_qnmPlus
    (n N L : ℕ) (q : XiZeroCopy) (eta : ℂ)
    (heta : d4BMNonconstantPhysicalAngularMomentum eta) :
    d4BMTargetShiftedPlusMinusIntermediateFrequency n N
        (d4BMXiMixedHorizonAngularMomentum q) ≠
      d4BMCausalQNMPlus L eta := by
  intro h
  have him := congrArg Complex.im h
  rw [d4BMTargetShiftedPlusMinusIntermediateFrequency_eq] at him
  simp [d4BMCausalQNMPlus, d4BMCausalDecay, Complex.mul_im] at him
  norm_num at him
  have hchi := d4BMXiMixedHorizonAngularMomentum_im_mem_openHalf q
  by_cases hN : N ≤ L + n
  · have hcast : (N : ℝ) ≤ (L : ℝ) + (n : ℝ) := by exact_mod_cast hN
    linarith [heta.2, hchi.2]
  · have hsucc : L + n + 1 ≤ N := by omega
    have hcast : (L : ℝ) + (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hsucc
    linarith [heta.1, hchi.1]

theorem d4BMXiTargetShiftedPlusMinusIntermediateFrequency_ne_qnmMinus
    (n N L : ℕ) (q : XiZeroCopy) (eta : ℂ)
    (heta : d4BMNonconstantPhysicalAngularMomentum eta) :
    d4BMTargetShiftedPlusMinusIntermediateFrequency n N
        (d4BMXiMixedHorizonAngularMomentum q) ≠
      d4BMCausalQNMMinus L eta := by
  intro h
  have him := congrArg Complex.im h
  rw [d4BMTargetShiftedPlusMinusIntermediateFrequency_eq] at him
  simp [d4BMCausalQNMMinus, d4BMCausalDecay, Complex.mul_im] at him
  norm_num at him
  have hchi := d4BMXiMixedHorizonAngularMomentum_im_mem_openHalf q
  by_cases hN : N ≤ L + n
  · have hcast : (N : ℝ) ≤ (L : ℝ) + (n : ℝ) := by exact_mod_cast hN
    linarith [heta.1, hchi.1]
  · have hsucc : L + n + 1 ≤ N := by omega
    have hcast : (L : ℝ) + (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hsucc
    linarith [heta.2, hchi.2]

/-- Both response channels avoid both BM branches on every nonconstant physical angular shell. -/
def d4BMXiPhysicalIntermediateResponsesRegularAtTarget
    (n k N : ℕ) (q : XiZeroCopy) : Prop :=
  ∀ (L : ℕ) (eta : ℂ), d4BMNonconstantPhysicalAngularMomentum eta →
    d4BMTargetShiftedPlusPlusIntermediateFrequency k N
        (d4BMXiMixedHorizonAngularMomentum q) ≠ d4BMCausalQNMPlus L eta ∧
    d4BMTargetShiftedPlusPlusIntermediateFrequency k N
        (d4BMXiMixedHorizonAngularMomentum q) ≠ d4BMCausalQNMMinus L eta ∧
    d4BMTargetShiftedPlusMinusIntermediateFrequency n N
        (d4BMXiMixedHorizonAngularMomentum q) ≠ d4BMCausalQNMPlus L eta ∧
    d4BMTargetShiftedPlusMinusIntermediateFrequency n N
        (d4BMXiMixedHorizonAngularMomentum q) ≠ d4BMCausalQNMMinus L eta

theorem d4BMXiPhysicalIntermediateResponsesRegularAtTarget_proved
    (n k N : ℕ) (q : XiZeroCopy) :
    d4BMXiPhysicalIntermediateResponsesRegularAtTarget n k N q := by
  intro L eta heta
  exact ⟨d4BMTargetShiftedPlusPlusIntermediateFrequency_ne_qnmPlus
      k N L _ eta heta,
    d4BMTargetShiftedPlusPlusIntermediateFrequency_ne_qnmMinus
      k N L _ eta heta,
    d4BMXiTargetShiftedPlusMinusIntermediateFrequency_ne_qnmPlus
      n N L q eta heta,
    d4BMXiTargetShiftedPlusMinusIntermediateFrequency_ne_qnmMinus
      n N L q eta heta⟩

/-- Any `++` collision in the closed physical strip is forced onto the zero-mode edge. -/
theorem d4BMPlusPlusIntermediateCollision_forces_zeroModeEdge
    (k N L : ℕ) (chi eta : ℂ)
    (hlow : -(1 / 2 : ℝ) ≤ eta.im) (hupp : eta.im ≤ 1 / 2)
    (hcollision :
      d4BMTargetShiftedPlusPlusIntermediateFrequency k N chi =
        d4BMCausalQNMPlus L eta ∨
      d4BMTargetShiftedPlusPlusIntermediateFrequency k N chi =
        d4BMCausalQNMMinus L eta) :
    eta.im = -(1 / 2 : ℝ) ∨ eta.im = 1 / 2 := by
  by_cases hleft : eta.im = -(1 / 2 : ℝ)
  · exact Or.inl hleft
  right
  apply le_antisymm hupp
  by_contra hne
  have hstrict : eta.im < 1 / 2 := lt_of_not_ge hne
  have heta : d4BMNonconstantPhysicalAngularMomentum eta := by
    constructor
    · exact lt_of_le_of_ne hlow (Ne.symm hleft)
    · exact hstrict
  rcases hcollision with hplus | hminus
  · exact (d4BMTargetShiftedPlusPlusIntermediateFrequency_ne_qnmPlus
      k N L chi eta heta) hplus
  · exact (d4BMTargetShiftedPlusPlusIntermediateFrequency_ne_qnmMinus
      k N L chi eta heta) hminus

/-! ## Canonical Green completion of the total angular period -/

/-- Complete radiation flux entering the finite-part angular Green identity. -/
def d4BMXiGaugeFixedTotalAngularRadiationFlux
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) : ℝ :=
  ‖d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
      amplitude orthogonalMixing q‖ ^ (2 : ℕ)

/-- Direct and orthogonal-helicity fluxes are added only after the full gauge-fixed radiation map
has been constructed. -/
theorem d4BMXiGaugeFixedTotalAngularRadiationFlux_decomposition
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiGaugeFixedTotalAngularRadiationFlux amplitude orthogonalMixing q =
      ‖d4BMGaugeFixedSecondHarmonicRadiationMap q
          (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
            (xiSpectralPoint q), 0)‖ ^ (2 : ℕ) +
        ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (0, orthogonalMixing)‖ ^ (2 : ℕ) := by
  exact d4BMGaugeFixedSecondHarmonicRadiation_norm_sq_decomposition q
    (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
      (xiSpectralPoint q)) orthogonalMixing

theorem d4BMXiGaugeFixedTotalAngularRadiationFlux_pos
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ)
    (q : XiZeroCopy) :
    0 < d4BMXiGaugeFixedTotalAngularRadiationFlux
      amplitude orthogonalMixing q := by
  rw [d4BMXiGaugeFixedTotalAngularRadiationFlux]
  apply sq_pos_of_pos
  rw [norm_pos_iff]
  unfold d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
  exact d4BMGaugeFixedSecondHarmonicRadiation_ne_zero_of_direct_ne_zero q
    (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero ha q)
    orthogonalMixing

/-- Unit-Wronskian retarded finite-part period selected by the global cyclic Green identity. -/
def d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
    (conservativeFinitePart : ℝ) (amplitude orthogonalMixing : ℂ)
    (q : XiZeroCopy) : ℂ :=
  (conservativeFinitePart : ℂ) + Complex.I *
    (d4BMXiGaugeFixedTotalAngularRadiationFlux
      amplitude orthogonalMixing q : ℂ)

/-- Advanced boundary value of the same real finite-part period. -/
def d4BMXiGaugeFixedTotalAdvancedRenormalizedAngularPeriod
    (conservativeFinitePart : ℝ) (amplitude orthogonalMixing : ℂ)
    (q : XiZeroCopy) : ℂ :=
  (conservativeFinitePart : ℂ) - Complex.I *
    (d4BMXiGaugeFixedTotalAngularRadiationFlux
      amplitude orthogonalMixing q : ℂ)

theorem d4BMXiGaugeFixedTotalRenormalizedAngularPeriod_im
    (conservativeFinitePart : ℝ) (amplitude orthogonalMixing : ℂ)
    (q : XiZeroCopy) :
    (d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
      conservativeFinitePart amplitude orthogonalMixing q).im =
      d4BMXiGaugeFixedTotalAngularRadiationFlux
        amplitude orthogonalMixing q := by
  simp [d4BMXiGaugeFixedTotalRenormalizedAngularPeriod]

theorem d4BMXiGaugeFixedTotalRenormalizedAngularPeriod_im_pos
    (conservativeFinitePart : ℝ) {amplitude : ℂ} (ha : amplitude ≠ 0)
    (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    0 < (d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
      conservativeFinitePart amplitude orthogonalMixing q).im := by
  rw [d4BMXiGaugeFixedTotalRenormalizedAngularPeriod_im]
  exact d4BMXiGaugeFixedTotalAngularRadiationFlux_pos ha orthogonalMixing q

/-- Total retarded angular period is nonzero for every nonzero theta seed. -/
theorem d4BMXiGaugeFixedTotalRenormalizedAngularPeriod_ne_zero
    (conservativeFinitePart : ℝ) {amplitude : ℂ} (ha : amplitude ≠ 0)
    (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
      conservativeFinitePart amplitude orthogonalMixing q ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  rw [d4BMXiGaugeFixedTotalRenormalizedAngularPeriod_im] at him
  simp only [Complex.zero_im] at him
  exact (ne_of_gt
    (d4BMXiGaugeFixedTotalAngularRadiationFlux_pos
      ha orthogonalMixing q)) him

/-- Renormalized cyclic Green identity: all conservative bulk and counterterm pieces cancel from
the retarded-minus-advanced jump. -/
theorem d4BMXiGaugeFixedTotalRenormalizedAngularPeriod_greenJump
    (conservativeFinitePart : ℝ) (amplitude orthogonalMixing : ℂ)
    (q : XiZeroCopy) :
    d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
        conservativeFinitePart amplitude orthogonalMixing q -
      d4BMXiGaugeFixedTotalAdvancedRenormalizedAngularPeriod
        conservativeFinitePart amplitude orthogonalMixing q =
      2 * Complex.I *
        (d4BMXiGaugeFixedTotalAngularRadiationFlux
          amplitude orthogonalMixing q : ℂ) := by
  simp [d4BMXiGaugeFixedTotalRenormalizedAngularPeriod,
    d4BMXiGaugeFixedTotalAdvancedRenormalizedAngularPeriod]
  ring

theorem d4BMXiGaugeFixedTotalAdvancedRenormalizedAngularPeriod_eq_star
    (conservativeFinitePart : ℝ) (amplitude orthogonalMixing : ℂ)
    (q : XiZeroCopy) :
    d4BMXiGaugeFixedTotalAdvancedRenormalizedAngularPeriod
        conservativeFinitePart amplitude orthogonalMixing q =
      star (d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
        conservativeFinitePart amplitude orthogonalMixing q) := by
  apply Complex.ext <;>
    simp [d4BMXiGaugeFixedTotalRenormalizedAngularPeriod,
      d4BMXiGaugeFixedTotalAdvancedRenormalizedAngularPeriod]

/-- Real finite part plus global Green jump uniquely determine the retarded period. -/
theorem d4BMXiGaugeFixedTotalRenormalizedAngularPeriod_unique
    (period : ℂ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hre : period.re = conservativeFinitePart)
    (hjump : period - star period = 2 * Complex.I *
      (d4BMXiGaugeFixedTotalAngularRadiationFlux
        amplitude orthogonalMixing q : ℂ)) :
    period = d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
      conservativeFinitePart amplitude orthogonalMixing q := by
  apply Complex.ext
  · simpa [d4BMXiGaugeFixedTotalRenormalizedAngularPeriod] using hre
  · have him := congrArg Complex.im hjump
    simp at him
    have him' : period.im =
        d4BMXiGaugeFixedTotalAngularRadiationFlux
          amplitude orthogonalMixing q := by
      linarith
    simpa [d4BMXiGaugeFixedTotalRenormalizedAngularPeriod] using him'

/-- Joint closure of numerator nonvanishing and both intermediate-response regularity problems. -/
theorem d4BMXiTotalRenormalizedAngularPeriod_nonzero_and_intermediateRegular
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ)
    (q : XiZeroCopy) :
    d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
        conservativeFinitePart amplitude orthogonalMixing q ≠ 0 ∧
      d4BMXiPhysicalIntermediateResponsesRegularAtTarget n k N q := by
  exact ⟨d4BMXiGaugeFixedTotalRenormalizedAngularPeriod_ne_zero
      conservativeFinitePart ha orthogonalMixing q,
    d4BMXiPhysicalIntermediateResponsesRegularAtTarget_proved n k N q⟩

end

end RHTower
