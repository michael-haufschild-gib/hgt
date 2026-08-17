import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPositiveStarUntwisting
import GaloisForLFunctions.RHTower.FrankensteinMeyerPrimeKoszulGammaReporter
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GasGNS

/-!
# Meyer modular untwisting of the Gamma-six cyclic source

The full integral Gamma quadratic ghost and the genuine Xi-selected Meyer/Koszul character are
not parallel detectors.  If `chi_p(rho)` is the already-constructed Meyer prime-flow character,
then this file proves the coefficient-level identity

`GammaGhost(rho,p) = -multiplicity(rho) * (norm chi_p(rho) - norm chi_p(rho)⁻¹)^2`.

Consequently positive-star descent, unit modulus of the Meyer character, and untwisting of the
physical Gamma-six covariant boundary are the same operation.  This identifies a precise
cross-corpus producer target: preserve the norm of the genuine Meyer reporter at one prime.

The obvious positive receiver does not manufacture that target.  The Abelian-zeta-gas GNS
generator is a proper one-sided isometry: `W*V=1` but `V*W != 1`.  Hence the canonical assignment
of the Laurent generator and its inverse to `V` and `W` cannot be a ring landing.  A successful
positive receiver must be genuinely bilateral or selected before the Toeplitz compression.
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_deningerMeyerXiPrimeGammaCharacter_eq_halfGammaClock
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    ‖deningerMeyerXiPrimeGammaCharacter rho p‖ =
      Real.exp (-(Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) / 2) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [deningerMeyerXiPrimeGammaCharacter_eq_deltaS,
    norm_deltaS p.2.pos, Real.rpow_def_of_pos hp]
  congr 1
  unfold primeDepthBVWoldXiCenteredRate
  ring

/-- Product of the opposite Gamma defects is minus the square of half-density modular imbalance. -/
theorem sourceHorizontalGammaSixUnitDefects_mul_eq_neg_halfDensityImbalance_sq
    (a : ℝ) :
    sourceHorizontalGammaSixUnitForwardBoundaryDefect a *
        sourceHorizontalGammaSixUnitReflectedBoundaryDefect a =
      -(Real.exp (-a / 2) - (Real.exp (-a / 2))⁻¹) ^ 2 := by
  rw [sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
    sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]
  have hinv : (Real.exp (-a / 2))⁻¹ = Real.exp (a / 2) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hpos : Real.exp a = Real.exp (a / 2) * Real.exp (a / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hneg : Real.exp (-a) = Real.exp (-a / 2) * Real.exp (-a / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hunit : Real.exp (a / 2) * Real.exp (-a / 2) = 1 := by
    rw [← Real.exp_add, show a / 2 + -a / 2 = 0 by ring, Real.exp_zero]
  rw [hinv, hpos, hneg]
  nlinarith

/-- Norm imbalance of the genuine Xi-selected Meyer character at one retained prime. -/
def deningerMeyerXiPrimeGammaNormImbalance
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  ‖deningerMeyerXiPrimeGammaCharacter rho p‖ -
    ‖deningerMeyerXiPrimeGammaCharacter rho p‖⁻¹

/-- Full integral Gamma ghost is the negative Hermitian square of Meyer modular imbalance, with
the actual Xi divisor multiplicity retained. -/
theorem DeningerXiFullIntegralGammaProducer.quadraticGhost_eq_neg_meyerNormImbalance_sq
    {rho : XiDivisorSupport} {p : Nat.Primes}
    (h : DeningerXiFullIntegralGammaProducer rho p) :
    h.evaluation
        (deningerIntegralGammaMultiplicityQuadraticGhost
          (xiSupportMultiplicity rho)) =
      -(xiSupportMultiplicity rho : ℝ) *
        deningerMeyerXiPrimeGammaNormImbalance rho p ^ 2 := by
  rw [h.quadraticGhost_coefficient,
    sourceHorizontalGammaSixUnitDefects_mul_eq_neg_halfDensityImbalance_sq]
  unfold deningerMeyerXiPrimeGammaNormImbalance
  rw [norm_deningerMeyerXiPrimeGammaCharacter_eq_halfGammaClock]
  ring

/-- Nonnegative full-source ghost is exactly modular norm balance. -/
theorem deningerXiFullIntegralGammaProducer_quadraticGhost_nonneg_iff_meyerNormBalanced
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    0 ≤ (deningerXiFullIntegralGammaProducer rho p).evaluation
        (deningerIntegralGammaMultiplicityQuadraticGhost
          (xiSupportMultiplicity rho)) ↔
      deningerMeyerXiPrimeGammaNormImbalance rho p = 0 := by
  rw [(deningerXiFullIntegralGammaProducer rho p).quadraticGhost_eq_neg_meyerNormImbalance_sq]
  have hm : (0 : ℝ) < xiSupportMultiplicity rho := by
    exact_mod_cast xiSupportMultiplicity_pos rho
  constructor
  · intro h
    have hprod : (xiSupportMultiplicity rho : ℝ) *
        deningerMeyerXiPrimeGammaNormImbalance rho p ^ 2 ≤ 0 := by
      nlinarith
    have hsquare : deningerMeyerXiPrimeGammaNormImbalance rho p ^ 2 ≤ 0 := by
      by_contra hn
      have hsquarepos : 0 < deningerMeyerXiPrimeGammaNormImbalance rho p ^ 2 :=
        lt_of_not_ge hn
      have := mul_pos hm hsquarepos
      linarith
    exact sq_eq_zero_iff.mp (le_antisymm hsquare (sq_nonneg _))
  · rintro h
    rw [h]
    norm_num

/-- Since the Meyer character norm is strictly positive, reciprocal norm balance is exactly
unitarity. -/
theorem deningerMeyerXiPrimeGammaNormImbalance_eq_zero_iff_unitary
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    deningerMeyerXiPrimeGammaNormImbalance rho p = 0 ↔
      ‖deningerMeyerXiPrimeGammaCharacter rho p‖ = 1 := by
  let r : ℝ := ‖deningerMeyerXiPrimeGammaCharacter rho p‖
  have hr : 0 < r := norm_pos_iff.mpr
    (by
      rw [deningerMeyerXiPrimeGammaCharacter]
      exact Complex.exp_ne_zero _)
  change r - r⁻¹ = 0 ↔ r = 1
  constructor
  · intro h
    have hinv : r = r⁻¹ := sub_eq_zero.mp h
    have hsq : r ^ 2 = 1 := by
      calc
        r ^ 2 = r * r := pow_two r
        _ = r⁻¹ * r := congrArg (fun x => x * r) hinv
        _ = 1 := inv_mul_cancel₀ hr.ne'
    nlinarith
  · intro h
    rw [h]
    norm_num

/-- **Cross-corpus untwisting theorem.** Fixed Gamma-six source and unitary Meyer prime character
are equivalent for every retained Xi copy and every retained prime. -/
theorem sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff_meyerCharacter_unitary
    (q : XiZeroCopy) (p : Nat.Primes) :
    sourceHorizontalGammaSixPhysicalCovariantBoundary q =
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap ↔
      ‖deningerMeyerXiPrimeGammaCharacter q.1 p‖ = 1 := by
  rw [sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff,
    deningerMeyerXiPrimeGammaCharacter_eq_deltaS,
    norm_deltaS_eq_one_iff p.2.two_le]

/-- Meyer character unitarity directly untwists the physical covariant differential. -/
theorem sourceHorizontalGammaSixPhysicalCovariantBoundary_untwist_of_meyerCharacter_unitary
    (q : XiZeroCopy) (p : Nat.Primes)
    (hunit : ‖deningerMeyerXiPrimeGammaCharacter q.1 p‖ = 1) :
    sourceHorizontalGammaSixPhysicalCovariantBoundary q =
      (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap :=
  (sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff_meyerCharacter_unitary
    q p).2 hunit

/-- The minimal positive-star law is exactly unitarity of the genuine Meyer character. -/
theorem sourceHorizontalGammaSixPhysicalStarPositive_iff_meyerCharacter_unitary
    (q : XiZeroCopy) (p : Nat.Primes) :
    SourceHorizontalGammaSixPhysicalStarPositive q ↔
      ‖deningerMeyerXiPrimeGammaCharacter q.1 p‖ = 1 := by
  rw [sourceHorizontalGammaSixPhysicalStarPositive_iff_line,
    deningerMeyerXiPrimeGammaCharacter_eq_deltaS,
    norm_deltaS_eq_one_iff p.2.two_le]

/-- Full-producer nonnegativity on the quadratic ghost directly untwists the cyclic source. -/
theorem sourceHorizontalGammaSixPhysicalCovariantBoundary_untwist_of_fullGhost_nonneg
    (q : XiZeroCopy) (p : Nat.Primes)
    (hpos : 0 ≤ (deningerXiFullIntegralGammaProducer q.1 p).evaluation
      (deningerIntegralGammaMultiplicityQuadraticGhost
        (xiSupportMultiplicity q.1))) :
    sourceHorizontalGammaSixPhysicalCovariantBoundary q =
      (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap := by
  apply sourceHorizontalGammaSixPhysicalCovariantBoundary_untwist_of_meyerCharacter_unitary q p
  apply (deningerMeyerXiPrimeGammaNormImbalance_eq_zero_iff_unitary q.1 p).1
  exact
    (deningerXiFullIntegralGammaProducer_quadraticGhost_nonneg_iff_meyerNormBalanced q.1 p).1 hpos

/-! ## Canonical Toeplitz-gas receiver obstruction -/

/-- In a gas word, the isometry followed by its coisometry is the nontrivial range projection. -/
theorem sourceHorizontalGas_gen_mul_cogen_ne_one
    {M : Type*} (i : M) :
    GasWord.gen i * GasWord.cogen i ≠ 1 := by
  intro h
  have hi := congrArg (fun x : GasWord M => x.raise i) h
  simp [GasWord.gen, GasWord.cogen] at hi

/-- The same range projection is nontrivial in the gas monoid algebra. -/
theorem sourceHorizontalGasV_mul_gasW_ne_one
    {M : Type*} (i : M) :
    gasV i * gasW i ≠ (1 : GasAlgebra M) := by
  intro h
  have hword : GasWord.gen i * GasWord.cogen i ≠ (1 : GasWord M) :=
    sourceHorizontalGas_gen_mul_cogen_ne_one i
  have hcoeff := congrArg
    (fun a : GasAlgebra M => a.coeff (GasWord.gen i * GasWord.cogen i)) h
  rw [gasV, gasW, MonoidAlgebra.single_mul_single, mul_one] at hcoeff
  simp [MonoidAlgebra.one_def, hword] at hcoeff

/-- Positive-temperature Gibbs state detects the one-sided range projection, so it cannot descend
to a bilateral source which identifies that projection with the unit. -/
theorem sourceHorizontalGasGibbs_rangeProjection_ne_unitValue
    (theta : AbelianZetaParameters) (i : AbelianZetaMode) :
    gasGibbs theta (gasV i * gasW i) ≠ gasGibbs theta 1 := by
  have hrange := gasGibbs_rangeProj theta i 1
  simp only [pow_one] at hrange
  rw [hrange, gasGibbs_one]
  intro h
  have hnorm := norm_gasNome_lt_one theta i
  rw [h, norm_one] at hnorm
  linarith

/-- No canonical Laurent landing sends the invertible source generator to the one-sided gas
isometry and its inverse to the gas coisometry. -/
theorem not_exists_sourceHorizontalCanonicalLaurentToGasLanding
    {M : Type*} (i : M) :
    ¬ ∃ phi : DeningerIntegralCartierSourceRing →+* GasAlgebra M,
      phi (LaurentPolynomial.T 1) = gasV i ∧
      phi (LaurentPolynomial.T (-1)) = gasW i := by
  rintro ⟨phi, hV, hW⟩
  apply sourceHorizontalGasV_mul_gasW_ne_one i
  rw [← hV, ← hW, ← map_mul, ← LaurentPolynomial.T_add]
  norm_num

end

end RHTower
