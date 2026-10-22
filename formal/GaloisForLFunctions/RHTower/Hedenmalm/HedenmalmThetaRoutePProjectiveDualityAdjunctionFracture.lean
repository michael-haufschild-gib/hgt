import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPoleUnitPrimeCellDyadicParityProvenance
import GaloisForLFunctions.RHTower.ProjectivePrimeWeylModel

/-!
# Route-P projective duality--adjunction fracture

The full alternating Gamma/co-Poisson current of P-G51 is realized here on the literal residue
projective clock.  A squarefree source rate `sigma` selects marked weight

`z_p(sigma) = (1 - sigma) log(p) / 2`,

whose marked-to-bulk odds are `p^-sigma`.  The squared fidelity of two such projective states is
therefore exactly the Route-P squarefree parity Gram, and its logarithm is P-G51's full current
second difference.

This retains the two transports before scalarization.  Positive residue-Weyl adjunction changes
the marked point while preserving `sigma`; centered functional-equation duality changes `sigma`
to `2-sigma`.  Their projective states coincide exactly at `sigma = 1`.  The result classifies the
missing source-naturality equation; it does not assume or prove that equation on Xi divisors.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Oriented projective weight selected by a squarefree Route-P source rate. -/
def routePProjectiveNaturalWeight (p : Nat.Primes) (sigma : ℝ) : ℝ :=
  (1 - sigma) * Real.log (p : ℝ) / 2

theorem exp_two_mul_routePProjectiveNaturalWeight
    (p : Nat.Primes) (sigma : ℝ) :
    Real.exp (2 * routePProjectiveNaturalWeight p sigma) =
      (p : ℝ) ^ (1 - sigma) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [routePProjectiveNaturalWeight, Real.rpow_def_of_pos hp]
  congr 1
  ring

theorem exp_add_routePProjectiveNaturalWeight
    (p : Nat.Primes) (sigma tau : ℝ) :
    Real.exp
        (routePProjectiveNaturalWeight p sigma +
          routePProjectiveNaturalWeight p tau) =
      (p : ℝ) ^ (1 - (sigma + tau) / 2) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [routePProjectiveNaturalWeight, routePProjectiveNaturalWeight,
    Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- Literal Euler producer state in the projective prime clock. -/
def routePProjectiveProducerState (p : Nat.Primes) (sigma : ℝ) :
    EuclideanSpace ℂ (Option (ZMod (p : ℕ))) :=
  RHTower.projNatural none (routePProjectiveNaturalWeight p sigma)

/-- Positive-adjoint reporter obtained by residue Weyl transport. -/
def routePProjectiveAdjointState (p : Nat.Primes) (sigma : ℝ) :
    EuclideanSpace ℂ (Option (ZMod (p : ℕ))) :=
  RHTower.projPermute (RHTower.weylInversion (p : ℕ))
    (routePProjectiveProducerState p sigma)

/-- Functional-equation-dual reporter at the reflected centered rate. -/
def routePProjectiveDualState (p : Nat.Primes) (sigma : ℝ) :
    EuclideanSpace ℂ (Option (ZMod (p : ℕ))) :=
  RHTower.projNatural (some (0 : ZMod (p : ℕ)))
    (routePProjectiveNaturalWeight p (2 - sigma))

theorem routePProjectiveAdjointState_eq_reporter
    (p : Nat.Primes) (sigma : ℝ) :
    routePProjectiveAdjointState p sigma =
      RHTower.projNatural (some (0 : ZMod (p : ℕ)))
        (routePProjectiveNaturalWeight p sigma) := by
  rw [routePProjectiveAdjointState, routePProjectiveProducerState,
    RHTower.projPermute_projNatural, RHTower.weylInversion_infinity]

theorem routePProjectiveNaturalWeight_reflection
    (p : Nat.Primes) (sigma : ℝ) :
    routePProjectiveNaturalWeight p (2 - sigma) =
      -routePProjectiveNaturalWeight p sigma := by
  rw [routePProjectiveNaturalWeight, routePProjectiveNaturalWeight]
  ring

private theorem routePProjectiveReporter_injective (p : Nat.Primes) :
    Function.Injective
      (fun z : ℝ =>
        RHTower.projNatural (some (0 : ZMod (p : ℕ))) z) := by
  intro z y hzy
  have hnone := congrArg
    (fun v : EuclideanSpace ℂ (Option (ZMod (p : ℕ))) => v none) hzy
  have hzero := congrArg
    (fun v : EuclideanSpace ℂ (Option (ZMod (p : ℕ))) => v (some 0)) hzy
  have hcard := RHTower.two_le_card_optionZMod (p : ℕ)
  have hNz : 0 < RHTower.projNorm (Option (ZMod (p : ℕ))) z :=
    RHTower.projNorm_pos hcard z
  have hNy : 0 < RHTower.projNorm (Option (ZMod (p : ℕ))) y :=
    RHTower.projNorm_pos hcard y
  have hnone' : (((1 / RHTower.projNorm (Option (ZMod (p : ℕ))) z : ℝ) : ℂ)) =
      (((1 / RHTower.projNorm (Option (ZMod (p : ℕ))) y : ℝ) : ℂ)) := by
    simpa [RHTower.projNatural] using hnone
  have hzero' :
      (((Real.exp z / RHTower.projNorm (Option (ZMod (p : ℕ))) z : ℝ) : ℂ)) =
        (((Real.exp y / RHTower.projNorm (Option (ZMod (p : ℕ))) y : ℝ) : ℂ)) := by
    simpa [RHTower.projNatural] using hzero
  have hnoneReal :
      1 / RHTower.projNorm (Option (ZMod (p : ℕ))) z =
        1 / RHTower.projNorm (Option (ZMod (p : ℕ))) y := by
    exact_mod_cast hnone'
  have hNorm : RHTower.projNorm (Option (ZMod (p : ℕ))) z =
      RHTower.projNorm (Option (ZMod (p : ℕ))) y := by
    rw [one_div, one_div] at hnoneReal
    exact inv_injective hnoneReal
  have hzeroReal :
      Real.exp z / RHTower.projNorm (Option (ZMod (p : ℕ))) z =
        Real.exp y / RHTower.projNorm (Option (ZMod (p : ℕ))) y := by
    exact_mod_cast hzero'
  rw [hNorm] at hzeroReal
  have hexp : Real.exp z = Real.exp y := by
    exact (div_left_inj' hNy.ne').mp hzeroReal
  exact Real.exp_injective hexp

/-- The two non-scalar transports agree only at the centered source rate. -/
theorem routePProjectiveAdjointState_eq_dualState_iff
    (p : Nat.Primes) (sigma : ℝ) :
    routePProjectiveAdjointState p sigma =
        routePProjectiveDualState p sigma ↔
      sigma = 1 := by
  rw [routePProjectiveAdjointState_eq_reporter,
    routePProjectiveDualState]
  constructor
  · intro h
    have hw := routePProjectiveReporter_injective p h
    rw [routePProjectiveNaturalWeight, routePProjectiveNaturalWeight] at hw
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.prop.one_lt)
    nlinarith
  · rintro rfl
    norm_num [routePProjectiveNaturalWeight]

/-- Squared fidelity of two source rates in one projective producer polarization. -/
def routePProjectiveFidelitySq (p : Nat.Primes) (sigma tau : ℝ) : ℝ :=
  (inner ℂ (routePProjectiveProducerState p sigma)
    (routePProjectiveProducerState p tau)).re ^ 2

/-- The projective fidelity is the literal squarefree parity Gram. -/
theorem routePProjectiveFidelitySq_eq_squarefreePrimeParityGramSq
    (p : Nat.Primes) (sigma tau : ℝ) :
    routePProjectiveFidelitySq p sigma tau =
      squarefreePrimeParityGramSq p sigma tau := by
  have hcard := RHTower.two_le_card_optionZMod (p : ℕ)
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hNs := RHTower.projNorm_sq hcard
    (routePProjectiveNaturalWeight p sigma)
  have hNt := RHTower.projNorm_sq hcard
    (routePProjectiveNaturalWeight p tau)
  have hNsp : 0 < RHTower.projNorm (Option (ZMod (p : ℕ)))
      (routePProjectiveNaturalWeight p sigma) := RHTower.projNorm_pos hcard _
  have hNtp : 0 < RHTower.projNorm (Option (ZMod (p : ℕ)))
      (routePProjectiveNaturalWeight p tau) := RHTower.projNorm_pos hcard _
  have hsigma : (p : ℝ) ^ (1 - sigma) =
      (p : ℝ) * (p : ℝ) ^ (-sigma) := by
    rw [show 1 - sigma = 1 + (-sigma) by ring, Real.rpow_add hp,
      Real.rpow_one]
  have htau : (p : ℝ) ^ (1 - tau) =
      (p : ℝ) * (p : ℝ) ^ (-tau) := by
    rw [show 1 - tau = 1 + (-tau) by ring, Real.rpow_add hp,
      Real.rpow_one]
  have hmid : (p : ℝ) ^ (1 - (sigma + tau) / 2) =
      (p : ℝ) * (p : ℝ) ^ (-((sigma + tau) / 2)) := by
    rw [show 1 - (sigma + tau) / 2 = 1 + (-((sigma + tau) / 2)) by ring,
      Real.rpow_add hp, Real.rpow_one]
  simp only [routePProjectiveFidelitySq, routePProjectiveProducerState]
  rw [RHTower.inner_projNatural_same hcard,
    RHTower.projDeg_optionZMod]
  simp only [ofReal_re]
  rw [div_pow, mul_pow, hNs, hNt, RHTower.projDeg_optionZMod,
    ← RHTower.exp_two_mul_eq
      (routePProjectiveNaturalWeight p sigma),
    ← RHTower.exp_two_mul_eq
      (routePProjectiveNaturalWeight p tau),
    exp_two_mul_routePProjectiveNaturalWeight,
    exp_two_mul_routePProjectiveNaturalWeight,
    exp_add_routePProjectiveNaturalWeight,
    squarefreePrimeParityGramSq, hsigma, htau, hmid]
  field_simp [hp.ne']

/-- At the forced affine Route-P rates, projective fidelity is the literal prime-cell Gram. -/
theorem routePProjectiveFidelitySq_eq_squarefreeMobiusPrimeCellGramSq
    (p : Nat.Primes) (epsilon x z : ℝ) :
    routePProjectiveFidelitySq p (1 + x * epsilon) (1 + z * epsilon) =
      squarefreeMobiusPrimeCellGramSq p epsilon x z := by
  rw [routePProjectiveFidelitySq_eq_squarefreePrimeParityGramSq,
    squarefreePrimeParityGramSq_eq_squarefreeMobiusPrimeCellGramSq]

/-- **Vector/current weld.**  The logarithm of literal projective fidelity is exactly the full
alternating Gamma/co-Poisson current second difference from P-G51. -/
theorem log_routePProjectiveFidelitySq_eq_squarefreeGammaCoPoissonSecondDifference
    (p : Nat.Primes) (epsilon x z : ℝ) :
    Real.log
        (routePProjectiveFidelitySq p (1 + x * epsilon) (1 + z * epsilon)) =
      squarefreeGammaCoPoissonPrimeCurrent p (1 + x * epsilon) +
        squarefreeGammaCoPoissonPrimeCurrent p (1 + z * epsilon) -
          2 * squarefreeGammaCoPoissonPrimeCurrent p
            (1 + ((x + z) / 2) * epsilon) := by
  rw [routePProjectiveFidelitySq_eq_squarefreeMobiusPrimeCellGramSq,
    log_squarefreeMobiusPrimeCellGramSq_eq_squarefreeGammaCoPoissonSecondDifference]

end

end RHTower.HedenmalmThetaSource
