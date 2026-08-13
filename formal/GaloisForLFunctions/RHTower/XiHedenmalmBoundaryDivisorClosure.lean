import GaloisForLFunctions.RHTower.XiHedenmalmBoundaryValueProblem
import GaloisForLFunctions.RHTower.XiHedenmalmFourierEquation
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam
import GaloisForLFunctions.RHTower.XiCriticalLineIntegrality
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityTransversePick
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFullDensityWronskianNoGo
import GaloisForLFunctions.RHTower.XiSourceMatroidCircuitFracture

/-!
# Unconditional Hedenmalm boundary laws on the Xi divisor

The centered spectral coordinate of every actual Xi divisor point lies in the natural
Fourier--Laplace strip and is a zero of `XiC`.  The source anti-reflection identity, two-ended
weighted boundary condition, and unique normalized Hedenmalm boundary solution therefore hold at
every divisor point without RH, simplicity, or a positivity hypothesis.

This separates spectral realization from spectral confinement: the normalized boundary problem
realizes the complete Xi divisor, including any hypothetical off-critical zeros.  A self-adjoint or
positive source form is still needed to force those spectral parameters to be real.
-/

open Filter
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- Every Xi divisor point satisfies the source-only theta anti-reflection law. -/
theorem thetaCuspBoundaryAntiReflection_xiSpectralPointSupport
    (rho : XiDivisorSupport) :
    ThetaCuspBoundaryAntiReflection (xiSpectralPointSupport rho) := by
  exact (thetaCuspBoundaryAntiReflection_iff_XiC_eq_zero
    (abs_im_xiSpectralPointSupport_lt_one rho)).2
      (XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho)

/-- The explicit Hedenmalm boundary gauge vanishes at both logarithmic ends at every Xi divisor
point. -/
theorem xiHedenmalmBoundaryGauge_twoEnded_xiSpectralPointSupport
    (rho : XiDivisorSupport) :
    Tendsto (xiHedenmalmBoundaryGauge (xiSpectralPointSupport rho)) atBot (nhds 0) ∧
      Tendsto (xiHedenmalmBoundaryGauge (xiSpectralPointSupport rho)) atTop (nhds 0) := by
  exact (xiHedenmalmBoundaryGauge_twoEnded_iff_XiC_eq_zero
    (abs_im_xiSpectralPointSupport_lt_one rho)).2
      (XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho)

/-- Every Xi divisor point has a unique normalized Hedenmalm boundary eigenfunction. -/
theorem existsUnique_xiHedenmalmNormalizedBoundaryValueProblem_xiSpectralPointSupport
    (rho : XiDivisorSupport) :
    ∃! u : ℝ → ℂ,
      XiHedenmalmNormalizedBoundaryValueProblem (xiSpectralPointSupport rho) u := by
  exact (existsUnique_xiHedenmalmNormalizedBoundaryValueProblem_iff
    (abs_im_xiSpectralPointSupport_lt_one rho)).2
      (XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho)

/-- At every Xi divisor point the transformed theta-source equation has exactly one continuous
solution: the removable Hedenmalm quotient. -/
theorem xiThetaFourierSolutionSet_xiSpectralPointSupport_eq_singleton
    (rho : XiDivisorSupport) :
    xiThetaFourierSolutionSet (xiSpectralPointSupport rho) =
      {xiThetaEigenFourierContinuous (xiSpectralPointSupport rho)} :=
  xiThetaFourierSolutionSet_eq_singleton
    (XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho)

/-- The unique divisor-attached Hedenmalm quotient solves the concrete theta-source Fourier
equation on the real frequency axis without a separate Xi-zero premise. -/
theorem xiThetaEigenFourier_xiSpectralPointSupport_real_source_equation
    (rho : XiDivisorSupport) (t : ℝ) :
    (xiSpectralPointSupport rho - (t : ℂ)) *
      xiThetaEigenFourier (xiSpectralPointSupport rho) (t : ℂ) =
      -Complex.I * (𝓕 xiThetaSchwartzSource) t :=
  xiThetaEigenFourier_real_source_equation
    (XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho) t

/-- Divisor-wide source package: anti-reflection, two-ended decay, and unique normalized
boundary solvability are simultaneous unconditional laws of the complete Xi divisor. -/
theorem xiDivisorSupport_hedenmalmBoundarySourceLaw (rho : XiDivisorSupport) :
    ThetaCuspBoundaryAntiReflection (xiSpectralPointSupport rho) ∧
      (Tendsto (xiHedenmalmBoundaryGauge (xiSpectralPointSupport rho))
          atBot (nhds 0) ∧
        Tendsto (xiHedenmalmBoundaryGauge (xiSpectralPointSupport rho))
          atTop (nhds 0)) ∧
      ∃! u : ℝ → ℂ,
        XiHedenmalmNormalizedBoundaryValueProblem (xiSpectralPointSupport rho) u := by
  exact ⟨thetaCuspBoundaryAntiReflection_xiSpectralPointSupport rho,
    xiHedenmalmBoundaryGauge_twoEnded_xiSpectralPointSupport rho,
    existsUnique_xiHedenmalmNormalizedBoundaryValueProblem_xiSpectralPointSupport rho⟩

/-- Boundary/Fourier dual realization of every Xi divisor point: the normalized physical-side
boundary problem and transformed continuous source equation are both uniquely solvable at the
same centered spectral parameter. -/
theorem xiDivisorSupport_hedenmalmBoundaryFourierSourceLaw
    (rho : XiDivisorSupport) :
    (∃! u : ℝ → ℂ,
        XiHedenmalmNormalizedBoundaryValueProblem (xiSpectralPointSupport rho) u) ∧
      xiThetaFourierSolutionSet (xiSpectralPointSupport rho) =
        {xiThetaEigenFourierContinuous (xiSpectralPointSupport rho)} :=
  ⟨existsUnique_xiHedenmalmNormalizedBoundaryValueProblem_xiSpectralPointSupport rho,
    xiThetaFourierSolutionSet_xiSpectralPointSupport_eq_singleton rho⟩

/-- A Xi divisor point strictly left of the critical line is simultaneously a collision in the
completed-density de Branges chart and a zero of the full-density quotient.  The source strip,
Xi-zero, and denominator-nonvanishing premises are all discharged by divisor data. -/
theorem xiDivisorSupport_completedDensityCollisions_of_re_lt_half
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re < 1 / 2) :
    thetaCuspTailSecondDensityDeBrangesProjectiveRatio
        (xiSpectralPointSupport rho) = -1 ∧
      xiFullDensityQuotientValue (xiSpectralPointSupport rho) = 0 := by
  have him : 0 < (xiSpectralPointSupport rho).im := by
    rw [xiSpectralPointSupport_im_eq_half_sub_re]
    linarith
  have himlt : (xiSpectralPointSupport rho).im < 1 :=
    (abs_lt.mp (abs_im_xiSpectralPointSupport_lt_one rho)).2
  have hzero := XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho
  exact ⟨
    (thetaCuspTailSecondDensityDeBrangesProjectiveRatio_eq_neg_one_iff_upper
      him himlt).2 hzero,
    (xiFullDensityQuotientValue_eq_zero_iff him).2 hzero⟩

/-- On the actual Xi divisor, the diagonal Hedenmalm Bezoutian is the square of the Xi derivative;
the generic `XiC z = 0` premise is supplied by source data. -/
theorem xiHedenmalmBezoutian_self_xiSpectralPointSupport
    (rho : XiDivisorSupport) :
    xiHedenmalmBezoutian (xiSpectralPointSupport rho)
        (xiSpectralPointSupport rho) =
      deriv XiC (xiSpectralPointSupport rho) ^ 2 :=
  xiHedenmalmBezoutian_self_of_zero
    (XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho)

/-- Distinct divisor points are off-diagonally orthogonal for the source-defined Hedenmalm
Bezoutian, with both generic Xi-zero premises discharged by divisor membership. -/
theorem xiHedenmalmBezoutian_xiSpectralPointSupport_eq_zero_of_ne
    (rho tau : XiDivisorSupport) (h : rho ≠ tau) :
    xiHedenmalmBezoutian (xiSpectralPointSupport rho)
        (xiSpectralPointSupport tau) = 0 := by
  apply xiHedenmalmBezoutian_eq_zero_of_distinct_zeros
  · exact XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho
  · exact XiC_xiSpectralPointSupport_eq_zero_sourceCircuit tau
  · intro heq
    exact h (xiSpectralPointSupport_injective heq.symm)

/-- Exact divisor kernel law: the Hedenmalm Bezoutian is diagonal on the complete Xi divisor,
including multiple zeros, and its diagonal weight is the squared Xi derivative. -/
theorem xiHedenmalmBezoutian_xiDivisorSupport
    (rho tau : XiDivisorSupport) :
    xiHedenmalmBezoutian (xiSpectralPointSupport rho)
        (xiSpectralPointSupport tau) =
      if rho = tau then deriv XiC (xiSpectralPointSupport rho) ^ 2 else 0 := by
  by_cases h : rho = tau
  · subst tau
    simpa using xiHedenmalmBezoutian_self_xiSpectralPointSupport rho
  · rw [if_neg h]
    exact xiHedenmalmBezoutian_xiSpectralPointSupport_eq_zero_of_ne rho tau h

/-- Exact evaluation kernel of the removable Hedenmalm Fourier quotient on the complete Xi
divisor.  Divisor membership supplies both Xi-zero premises, while injectivity of the centered
spectral coordinate identifies the diagonal. -/
theorem xiThetaEigenFourier_xiDivisorSupport
    (rho tau : XiDivisorSupport) :
    xiThetaEigenFourier (xiSpectralPointSupport rho)
        (xiSpectralPointSupport tau) =
      if rho = tau then
        Complex.I * deriv XiC (xiSpectralPointSupport rho)
      else 0 := by
  by_cases h : rho = tau
  · subst tau
    simpa using xiThetaEigenFourier_self (xiSpectralPointSupport rho)
  · rw [if_neg h]
    apply xiThetaEigenFourier_eq_zero_of_XiC_eq_zero
    · exact XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho
    · exact XiC_xiSpectralPointSupport_eq_zero_sourceCircuit tau
    · intro heq
      exact h (xiSpectralPointSupport_injective heq.symm)

/-- On the Xi divisor, the source-defined Bezoutian is exactly the negative product of the two
oppositely based removable Fourier quotient evaluations.  This is an unconditional
boundary/Fourier factorization and remains valid at multiple zeros. -/
theorem xiHedenmalmBezoutian_eq_neg_thetaEigenFourier_mul_swap
    (rho tau : XiDivisorSupport) :
    xiHedenmalmBezoutian (xiSpectralPointSupport rho)
        (xiSpectralPointSupport tau) =
      -xiThetaEigenFourier (xiSpectralPointSupport rho)
          (xiSpectralPointSupport tau) *
        xiThetaEigenFourier (xiSpectralPointSupport tau)
          (xiSpectralPointSupport rho) := by
  by_cases h : rho = tau
  · subst tau
    rw [xiHedenmalmBezoutian_self_xiSpectralPointSupport,
      xiThetaEigenFourier_self]
    calc
      deriv XiC (xiSpectralPointSupport rho) ^ 2 =
          -((Complex.I * Complex.I) *
            deriv XiC (xiSpectralPointSupport rho) ^ 2) := by
            rw [Complex.I_mul_I]
            ring
      _ = -(Complex.I * deriv XiC (xiSpectralPointSupport rho)) *
          (Complex.I * deriv XiC (xiSpectralPointSupport rho)) := by ring
  · rw [xiHedenmalmBezoutian_xiSpectralPointSupport_eq_zero_of_ne rho tau h,
      xiThetaEigenFourier_xiDivisorSupport, if_neg h]
    ring

/-! ## Unconditional Weil pairing on the Hedenmalm divisor basis -/

/-- A divisor-based Hedenmalm quotient forms an absolutely summable Weil pair with every test
function.  Its first evaluation factor is supported on the finite multiplicity fiber of its base
zero, so no decay or RH premise is needed. -/
theorem xiWeilPairSummable_thetaEigenFourier_xiSpectralPointSupport_left
    (rho : XiDivisorSupport) (G : ℂ → ℂ) :
    XiWeilPairSummable
      (xiThetaEigenFourier (xiSpectralPointSupport rho)) G := by
  unfold XiWeilPairSummable
  apply summable_of_hasFiniteSupport
  apply (finite_xiSpectralPoint_fiber (xiSpectralPointSupport rho)).subset
  intro q hq
  simp only [Function.mem_support] at hq
  by_contra hne
  apply hq
  rw [xiThetaEigenFourier_spectralPoint_eq_zero
    (XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho) q hne, zero_mul]

/-- Every pair of divisor-based Hedenmalm quotients satisfies the named absolute-convergence
interface of the Xi Weil polarization, unconditionally. -/
theorem xiWeilPairSummable_thetaEigenFourier_xiDivisorSupport
    (rho tau : XiDivisorSupport) :
    XiWeilPairSummable
      (xiThetaEigenFourier (xiSpectralPointSupport rho))
      (xiThetaEigenFourier (xiSpectralPointSupport tau)) :=
  xiWeilPairSummable_thetaEigenFourier_xiSpectralPointSupport_left rho _

/-- Exact unconditional Weil kernel of the divisor-based Hedenmalm quotients.  The Weil sharp
involution pairs a spectral fiber only with its complex-conjugate fiber.  Thus the kernel is zero
off those conjugate fibers; on them it is analytic multiplicity times the square of the Xi
derivative. -/
theorem xiWeilPolarization_thetaEigenFourier_xiDivisorSupport
    (rho tau : XiDivisorSupport) :
    xiWeilPolarization
        (xiThetaEigenFourier (xiSpectralPointSupport rho))
        (xiThetaEigenFourier (xiSpectralPointSupport tau)) =
      if xiSpectralPointSupport tau =
          (starRingEnd ℂ) (xiSpectralPointSupport rho) then
        (xiSpectralMultiplicity (xiSpectralPointSupport rho) : ℂ) *
          deriv XiC (xiSpectralPointSupport rho) ^ 2
      else 0 := by
  let alpha : ℂ := xiSpectralPointSupport rho
  let beta : ℂ := xiSpectralPointSupport tau
  have halpha : XiC alpha = 0 :=
    XiC_xiSpectralPointSupport_eq_zero_sourceCircuit rho
  have hbeta : XiC beta = 0 :=
    XiC_xiSpectralPointSupport_eq_zero_sourceCircuit tau
  have hconj : XiC ((starRingEnd ℂ) alpha) = 0 := by
    rw [xiHedenmalm_XiC_conj, halpha, map_zero]
  change xiWeilPolarization (xiThetaEigenFourier alpha)
      (xiThetaEigenFourier beta) =
    if beta = (starRingEnd ℂ) alpha then
      (xiSpectralMultiplicity alpha : ℂ) * deriv XiC alpha ^ 2
    else 0
  by_cases hab : beta = (starRingEnd ℂ) alpha
  · rw [if_pos hab]
    unfold xiWeilPolarization
    let S : Set XiZeroCopy := {q | xiSpectralPoint q = alpha}
    let T : Finset XiZeroCopy := (finite_xiSpectralPoint_fiber alpha).toFinset
    let c : ℂ := deriv XiC alpha ^ 2
    let g : XiZeroCopy → ℂ := fun q => if q ∈ S then c else 0
    have heq (q : XiZeroCopy) :
        xiThetaEigenFourier alpha (xiSpectralPoint q) *
            xiWeilSharp (xiThetaEigenFourier beta) (xiSpectralPoint q) =
          g q := by
      by_cases hq : xiSpectralPoint q = alpha
      · have hqS : q ∈ S := by
          simpa only [S, Set.mem_setOf_eq] using hq
        change xiThetaEigenFourier alpha (xiSpectralPoint q) *
            xiWeilSharp (xiThetaEigenFourier beta) (xiSpectralPoint q) =
          (if q ∈ S then c else 0)
        rw [if_pos hqS]
        change xiThetaEigenFourier alpha (xiSpectralPoint q) *
            (starRingEnd ℂ)
              (xiThetaEigenFourier beta
                ((starRingEnd ℂ) (xiSpectralPoint q))) =
          c
        rw [hq, xiThetaEigenFourier_self, ← hab, xiThetaEigenFourier_self,
          hab, deriv_XiC_conj]
        simp [c]
        calc
          -(Complex.I * deriv XiC alpha *
              (Complex.I * deriv XiC alpha)) =
              -(Complex.I ^ 2 * deriv XiC alpha ^ 2) := by ring
          _ = deriv XiC alpha ^ 2 := by rw [Complex.I_sq]; ring
      · rw [xiThetaEigenFourier_spectralPoint_eq_zero halpha q hq, zero_mul]
        simp only [g, S, Set.mem_setOf_eq, hq, if_false]
    calc
      (∑' q : XiZeroCopy,
          xiThetaEigenFourier alpha (xiSpectralPoint q) *
            xiWeilSharp (xiThetaEigenFourier beta) (xiSpectralPoint q)) =
          ∑' q : XiZeroCopy, g q := tsum_congr heq
      _ = ∑ q ∈ T, g q := by
        apply tsum_eq_sum
        intro q hqT
        have hqS : q ∉ S := by
          intro hqS
          apply hqT
          simpa only [T, Set.Finite.mem_toFinset, S] using hqS
        simp [g, hqS]
      _ = (T.card : ℂ) * c := by
        have hmem : ∀ q ∈ T, q ∈ S := by
          intro q hq
          simpa only [T, Set.Finite.mem_toFinset, S] using hq
        calc
          ∑ q ∈ T, g q = ∑ _q ∈ T, c := by
            apply Finset.sum_congr rfl
            intro q hq
            change (if q ∈ S then c else 0) = c
            rw [if_pos (hmem q hq)]
          _ = (T.card : ℂ) * c := by simp
      _ = (xiSpectralMultiplicity alpha : ℂ) * deriv XiC alpha ^ 2 := by
        rfl
  · rw [if_neg hab]
    unfold xiWeilPolarization
    have hterm : (fun q : XiZeroCopy =>
        xiThetaEigenFourier alpha (xiSpectralPoint q) *
          xiWeilSharp (xiThetaEigenFourier beta) (xiSpectralPoint q)) = 0 := by
      funext q
      by_cases hq : xiSpectralPoint q = alpha
      · change xiThetaEigenFourier alpha (xiSpectralPoint q) *
            (starRingEnd ℂ)
              (xiThetaEigenFourier beta
                ((starRingEnd ℂ) (xiSpectralPoint q))) = 0
        rw [hq, xiThetaEigenFourier_eq_zero_of_XiC_eq_zero
          hbeta hconj (Ne.symm hab), map_zero, mul_zero]
      · rw [xiThetaEigenFourier_spectralPoint_eq_zero halpha q hq, zero_mul]
        simp
    rw [hterm]
    exact tsum_zero

/-- Critical-line reflection on the Xi divisor is complex conjugation in the centered spectral
coordinate. -/
theorem xiSpectralPointSupport_lineConj_boundaryClosure (rho : XiDivisorSupport) :
    xiSpectralPointSupport (xiZeroLineConjEquiv rho) =
      (starRingEnd ℂ) (xiSpectralPointSupport rho) := by
  rw [xiSpectralPointSupport, xiSpectralPointSupport,
    xiZeroLineConjEquiv_apply]
  simp only [map_mul, map_sub, map_neg, Complex.conj_I]
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.conj_ofReal]
  rw [hhalf]
  ring

/-- Orbit form of the exact Weil kernel: the Hedenmalm divisor basis is paired by the
critical-line-reflection involution, with no spectral-coordinate equality left in the interface. -/
theorem xiWeilPolarization_thetaEigenFourier_xiDivisorSupport_orbit
    (rho tau : XiDivisorSupport) :
    xiWeilPolarization
        (xiThetaEigenFourier (xiSpectralPointSupport rho))
        (xiThetaEigenFourier (xiSpectralPointSupport tau)) =
      if tau = xiZeroLineConjEquiv rho then
        (xiSpectralMultiplicity (xiSpectralPointSupport rho) : ℂ) *
          deriv XiC (xiSpectralPointSupport rho) ^ 2
      else 0 := by
  rw [xiWeilPolarization_thetaEigenFourier_xiDivisorSupport]
  have hiff :
      xiSpectralPointSupport tau =
          (starRingEnd ℂ) (xiSpectralPointSupport rho) ↔
        tau = xiZeroLineConjEquiv rho := by
    rw [← xiSpectralPointSupport_lineConj_boundaryClosure]
    constructor
    · intro h
      exact xiSpectralPointSupport_injective h
    · intro h
      rw [h]
  simp only [hiff]

/-- Diagonal classification: a Hedenmalm divisor vector is isotropic precisely off the fixed
orbit of critical-line reflection; at a fixed orbit its exact diagonal is multiplicity times the
squared Xi derivative. -/
theorem xiWeilPolarization_thetaEigenFourier_xiDivisorSupport_self
    (rho : XiDivisorSupport) :
    xiWeilPolarization
        (xiThetaEigenFourier (xiSpectralPointSupport rho))
        (xiThetaEigenFourier (xiSpectralPointSupport rho)) =
      if xiZeroLineConjEquiv rho = rho then
        (xiSpectralMultiplicity (xiSpectralPointSupport rho) : ℂ) *
          deriv XiC (xiSpectralPointSupport rho) ^ 2
      else 0 := by
  simpa only [eq_comm] using
    xiWeilPolarization_thetaEigenFourier_xiDivisorSupport_orbit rho rho

end RHTower
