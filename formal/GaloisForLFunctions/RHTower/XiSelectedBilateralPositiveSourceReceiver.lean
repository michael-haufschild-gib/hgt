import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixMeyerModularUntwisting
import GaloisForLFunctions.RHTower.RiemannCenteredFlowCapacityIntertwining
import GaloisForLFunctions.RHTower.FrankensteinXiBidirectionalIntegralCartierSource

/-!
# Xi-selected bilateral positive source receiver

Let `chi = chi_p(rho)` be the genuine Meyer/Koszul character of one retained Xi divisor at one
ordinary-prime clock.  Two source orientations prescribe the moment matrix

```text
M_can(chi) = [[1, chi], [chi⁻¹, 1]].
```

This is the minimal coefficient-faithful bilateral positive receiver: both orientations are
literal, and both source diagonals have the same fixed unit normalization.  Positivity of this
matrix forces its two off-diagonal entries to be Hermitian mates, hence `chi⁻¹ = star chi` and
`‖chi‖ = 1`.  Conversely unit modulus makes the matrix a rank-one Gram.

There is an important unconditional countermodel to weaker formulations.  The source-derived
modular weight `Delta = ‖chi‖²` gives

```text
Delta * chi⁻¹ = star chi,
M_mod(chi) = [[1, chi], [Delta * chi⁻¹, Delta]],
```

and `M_mod` is always a positive rank-one Gram.  Moreover `Delta` is simultaneously the literal
inverse-oriented Gamma ghost and the prime-time arithmetic source countercharacter.  Thus
positive, bilateral, source-natural *covariant* reception does not prove RH: fixed-star/unit-mass
descent is the load-bearing requirement.

No Toeplitz gas, unilateral shift, range projection, or Gibbs state is used here.  The final
theorems classify canonical receiver existence pointwise by the critical line and globally by RH;
they do not assert the still-missing arithmetic positivity producer.
-/

open Complex Matrix
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Source-derived modular weight of the actual Meyer prime character. -/
def deningerMeyerXiPrimeGammaModularWeight
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  ‖deningerMeyerXiPrimeGammaCharacter rho p‖ ^ 2

/-- Literal coefficient-faithful two-orientation source moment matrix. -/
def deningerMeyerXiPrimeGammaCanonicalBilateralReceiver
    (rho : XiDivisorSupport) (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  let chi := deningerMeyerXiPrimeGammaCharacter rho p
  !![(1 : ℂ), chi; chi⁻¹, 1]

/-- Modular-covariant receiver.  The inverse orientation and second source mass carry the same
source-derived Radon--Nikodym weight. -/
def deningerMeyerXiPrimeGammaModularBilateralReceiver
    (rho : XiDivisorSupport) (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  let chi := deningerMeyerXiPrimeGammaCharacter rho p
  let Delta := deningerMeyerXiPrimeGammaModularWeight rho p
  !![(1 : ℂ), chi; (Delta : ℂ) * chi⁻¹, (Delta : ℂ)]

/-- Pointwise producer target: the literal bilateral receiver is positive on one Xi divisor and
one retained prime label. -/
def XiSelectedBilateralPositiveSourceReceiverAt
    (rho : XiDivisorSupport) (p : Nat.Primes) : Prop :=
  (deningerMeyerXiPrimeGammaCanonicalBilateralReceiver rho p).PosSemidef

/-- Global producer target over every retained Xi divisor and prime label. -/
def EveryXiSelectedBilateralPositiveSourceReceiver : Prop :=
  ∀ (rho : XiDivisorSupport) (p : Nat.Primes),
    XiSelectedBilateralPositiveSourceReceiverAt rho p

/-- Fixed-star descent stripped of positivity and diagonal normalization: literal source inversion
is identified with the Hilbert-space star on the selected Meyer character. -/
def DeningerMeyerXiPrimeGammaFixedStarDescendsAt
    (rho : XiDivisorSupport) (p : Nat.Primes) : Prop :=
  star (deningerMeyerXiPrimeGammaCharacter rho p) =
    (deningerMeyerXiPrimeGammaCharacter rho p)⁻¹

/-- Literal forward and inverse coefficients with completely unrestricted diagonal masses.  This
tests whether unit diagonal, rather than fixed star, carries any part of the RH obstruction. -/
def deningerMeyerXiPrimeGammaUnnormalizedFixedStarReceiver
    (rho : XiDivisorSupport) (p : Nat.Primes) (d0 d1 : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let chi := deningerMeyerXiPrimeGammaCharacter rho p
  !![d0, chi; chi⁻¹, d1]

/-- Diagonal-free producer target: some positive receiver retains both literal source
orientations, but its two diagonal masses may be arbitrary complex numbers. -/
def XiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt
    (rho : XiDivisorSupport) (p : Nat.Primes) : Prop :=
  ∃ d0 d1 : ℂ,
    (deningerMeyerXiPrimeGammaUnnormalizedFixedStarReceiver rho p d0 d1).PosSemidef

/-- Global arbitrary-diagonal fixed-star producer target. -/
def EveryXiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiver : Prop :=
  ∀ (rho : XiDivisorSupport) (p : Nat.Primes),
    XiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt rho p

/-- The actual Meyer character never vanishes. -/
theorem deningerMeyerXiPrimeGammaCharacter_ne_zero
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    deningerMeyerXiPrimeGammaCharacter rho p ≠ 0 := by
  rw [deningerMeyerXiPrimeGammaCharacter]
  exact Complex.exp_ne_zero _

/-- The modular weight is strictly positive. -/
theorem deningerMeyerXiPrimeGammaModularWeight_pos
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    0 < deningerMeyerXiPrimeGammaModularWeight rho p := by
  rw [deningerMeyerXiPrimeGammaModularWeight]
  exact pow_pos (norm_pos_iff.mpr
    (deningerMeyerXiPrimeGammaCharacter_ne_zero rho p)) 2

/-- Exact modular-star identity.  The unique positive correction turning literal inversion into
the Hilbert adjoint is the Hermitian square of the character. -/
theorem deningerMeyerXiPrimeGammaModularWeight_mul_inv_eq_star
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    ((deningerMeyerXiPrimeGammaModularWeight rho p : ℝ) : ℂ) *
        (deningerMeyerXiPrimeGammaCharacter rho p)⁻¹ =
      star (deningerMeyerXiPrimeGammaCharacter rho p) := by
  let chi := deningerMeyerXiPrimeGammaCharacter rho p
  have hchi : chi ≠ 0 := deningerMeyerXiPrimeGammaCharacter_ne_zero rho p
  have hmul : chi * star chi = (Complex.normSq chi : ℂ) := Complex.mul_conj chi
  rw [deningerMeyerXiPrimeGammaModularWeight, ← Complex.normSq_eq_norm_sq]
  calc
    ((Complex.normSq chi : ℝ) : ℂ) * chi⁻¹ = (chi * star chi) * chi⁻¹ := by rw [hmul]
    _ = star chi := by field_simp

/-- Uniqueness of the modular correction.  No alternative common determinant factor can repair
the two literal coefficients while preserving the ordinary complex star. -/
theorem deningerMeyerXiPrimeGammaModularWeight_unique
    (rho : XiDivisorSupport) (p : Nat.Primes) {c : ℝ}
    (hstar : (c : ℂ) * (deningerMeyerXiPrimeGammaCharacter rho p)⁻¹ =
      star (deningerMeyerXiPrimeGammaCharacter rho p)) :
    c = deningerMeyerXiPrimeGammaModularWeight rho p := by
  have hchi : deningerMeyerXiPrimeGammaCharacter rho p ≠ 0 :=
    deningerMeyerXiPrimeGammaCharacter_ne_zero rho p
  have hinv : (deningerMeyerXiPrimeGammaCharacter rho p)⁻¹ ≠ 0 := inv_ne_zero hchi
  have hc : (c : ℂ) =
      (deningerMeyerXiPrimeGammaModularWeight rho p : ℂ) := by
    apply mul_right_cancel₀ hinv
    exact hstar.trans
      (deningerMeyerXiPrimeGammaModularWeight_mul_inv_eq_star rho p).symm
  exact_mod_cast hc

/-- The same modular weight is the coefficient-faithful inverse-oriented Gamma ghost. -/
theorem deningerMeyerXiPrimeGammaModularWeight_eq_inverseGammaGhost
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    deningerMeyerXiPrimeGammaModularWeight rho p =
      primeGammaLocalInverseOrientedGhost
        (primeDepthBVWoldXiCenteredRate rho) p := by
  exact norm_sq_deningerMeyerXiPrimeGammaCharacter rho p

/-- Frankenstein source identification: the Meyer/Gamma modular weight is literally the
prime-time countercharacter of the arithmetic centered-flow capacity. -/
theorem deningerMeyerXiPrimeGammaModularWeight_eq_sourceCountercharacter
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    deningerMeyerXiPrimeGammaModularWeight rho p =
      xiCenteredFlowSourceCountercharacter rho (Real.log (p : ℝ)) := by
  rw [deningerMeyerXiPrimeGammaModularWeight,
    norm_sq_deningerMeyerXiPrimeGammaCharacter,
    primeGammaLocalInverseOrientedGhost,
    xiCenteredFlowSourceCountercharacter,
    riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [Real.rpow_def_of_pos hp]
  congr 1
  simp only [sourceCayleyTransverseRate, primeDepthBVWoldXiCenteredRate,
    sub_re, one_re]
  ring

/-- The modular-covariant matrix is the Gram of the vector `(1, star chi)`. -/
theorem deningerMeyerXiPrimeGammaModularBilateralReceiver_eq_vecMulVec
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    deningerMeyerXiPrimeGammaModularBilateralReceiver rho p =
      Matrix.vecMulVec
        ![(1 : ℂ), star (deningerMeyerXiPrimeGammaCharacter rho p)]
        (star ![(1 : ℂ), star (deningerMeyerXiPrimeGammaCharacter rho p)]) := by
  rw [deningerMeyerXiPrimeGammaModularBilateralReceiver]
  have hinv := deningerMeyerXiPrimeGammaModularWeight_mul_inv_eq_star rho p
  have hdiag : ((deningerMeyerXiPrimeGammaModularWeight rho p : ℝ) : ℂ) =
      star (deningerMeyerXiPrimeGammaCharacter rho p) *
        deningerMeyerXiPrimeGammaCharacter rho p := by
    rw [deningerMeyerXiPrimeGammaModularWeight, ← Complex.normSq_eq_norm_sq]
    simpa [mul_comm] using
      (Complex.mul_conj (deningerMeyerXiPrimeGammaCharacter rho p)).symm
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.vecMulVec]
  · simp [Matrix.vecMulVec]
  · simpa [Matrix.vecMulVec] using hinv
  · simpa [Matrix.vecMulVec] using hdiag

/-- Unconditional positive source-natural receiver with the exact modular correction. -/
theorem deningerMeyerXiPrimeGammaModularBilateralReceiver_posSemidef
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    (deningerMeyerXiPrimeGammaModularBilateralReceiver rho p).PosSemidef := by
  rw [deningerMeyerXiPrimeGammaModularBilateralReceiver_eq_vecMulVec]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- Fixed source normalization agrees with modular-covariant normalization exactly when the
modular weight is trivial. -/
theorem deningerMeyerXiPrimeGammaCanonical_eq_modular_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    deningerMeyerXiPrimeGammaCanonicalBilateralReceiver rho p =
        deningerMeyerXiPrimeGammaModularBilateralReceiver rho p ↔
      deningerMeyerXiPrimeGammaModularWeight rho p = 1 := by
  constructor
  · intro h
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
      M (1 : Fin 2) (1 : Fin 2)) h
    have hc : (1 : ℂ) =
        (deningerMeyerXiPrimeGammaModularWeight rho p : ℂ) := by
      simpa [deningerMeyerXiPrimeGammaCanonicalBilateralReceiver,
        deningerMeyerXiPrimeGammaModularBilateralReceiver] using hentry
    exact_mod_cast hc.symm
  · intro hweight
    rw [deningerMeyerXiPrimeGammaCanonicalBilateralReceiver,
      deningerMeyerXiPrimeGammaModularBilateralReceiver]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hweight]

/-- Hard direction: positivity of the literal two-orientation matrix proves unit modulus.  The
proof uses only Hermitian symmetry forced by positivity and the existing exact norm imbalance
classification. -/
theorem norm_deningerMeyerXiPrimeGammaCharacter_eq_one_of_bilateralPositive
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hpositive : XiSelectedBilateralPositiveSourceReceiverAt rho p) :
    ‖deningerMeyerXiPrimeGammaCharacter rho p‖ = 1 := by
  let chi := deningerMeyerXiPrimeGammaCharacter rho p
  have hstar : star chi = chi⁻¹ := by
    simpa [XiSelectedBilateralPositiveSourceReceiverAt,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver, chi] using
        hpositive.isHermitian.apply (1 : Fin 2) (0 : Fin 2)
  apply (deningerMeyerXiPrimeGammaNormImbalance_eq_zero_iff_unitary rho p).1
  rw [deningerMeyerXiPrimeGammaNormImbalance, sub_eq_zero]
  have hnorm := congrArg norm hstar
  simpa [chi] using hnorm

/-- Unit modulus identifies fixed and modular receivers, so the canonical receiver is positive. -/
theorem xiSelectedBilateralPositiveSourceReceiverAt_of_norm_eq_one
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hunit : ‖deningerMeyerXiPrimeGammaCharacter rho p‖ = 1) :
    XiSelectedBilateralPositiveSourceReceiverAt rho p := by
  have hweight : deningerMeyerXiPrimeGammaModularWeight rho p = 1 := by
    simp [deningerMeyerXiPrimeGammaModularWeight, hunit]
  have heq :=
    (deningerMeyerXiPrimeGammaCanonical_eq_modular_iff rho p).2 hweight
  rw [XiSelectedBilateralPositiveSourceReceiverAt, heq]
  exact deningerMeyerXiPrimeGammaModularBilateralReceiver_posSemidef rho p

/-- Exact pointwise receiver classification. -/
theorem xiSelectedBilateralPositiveSourceReceiverAt_iff_norm_eq_one
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    XiSelectedBilateralPositiveSourceReceiverAt rho p ↔
      ‖deningerMeyerXiPrimeGammaCharacter rho p‖ = 1 := by
  exact ⟨norm_deningerMeyerXiPrimeGammaCharacter_eq_one_of_bilateralPositive rho p,
    xiSelectedBilateralPositiveSourceReceiverAt_of_norm_eq_one rho p⟩

/-! ## Fixed-star descent without diagonal normalization -/

/-- Literal inversion equals Hilbert star exactly at unit character norm. -/
theorem deningerMeyerXiPrimeGammaFixedStarDescendsAt_iff_norm_eq_one
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    DeningerMeyerXiPrimeGammaFixedStarDescendsAt rho p ↔
      ‖deningerMeyerXiPrimeGammaCharacter rho p‖ = 1 := by
  constructor
  · intro hstar
    apply (deningerMeyerXiPrimeGammaNormImbalance_eq_zero_iff_unitary rho p).1
    rw [deningerMeyerXiPrimeGammaNormImbalance, sub_eq_zero]
    have hnorm := congrArg norm hstar
    simpa [DeningerMeyerXiPrimeGammaFixedStarDescendsAt] using hnorm
  · intro hunit
    have hpositive :=
      xiSelectedBilateralPositiveSourceReceiverAt_of_norm_eq_one rho p hunit
    simpa [DeningerMeyerXiPrimeGammaFixedStarDescendsAt,
      XiSelectedBilateralPositiveSourceReceiverAt,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver] using
        hpositive.isHermitian.apply (1 : Fin 2) (0 : Fin 2)

/-- **Unit-diagonal elimination.**  Positivity with arbitrary diagonal masses still forces unit
character norm.  The proof uses only Hermitian symmetry of the two literal off-diagonal
coefficients; neither diagonal entry occurs. -/
theorem norm_deningerMeyerXiPrimeGammaCharacter_eq_one_of_unnormalizedFixedStarPositive
    (rho : XiDivisorSupport) (p : Nat.Primes) (d0 d1 : ℂ)
    (hpositive :
      (deningerMeyerXiPrimeGammaUnnormalizedFixedStarReceiver rho p d0 d1).PosSemidef) :
    ‖deningerMeyerXiPrimeGammaCharacter rho p‖ = 1 := by
  apply (deningerMeyerXiPrimeGammaFixedStarDescendsAt_iff_norm_eq_one rho p).1
  simpa [DeningerMeyerXiPrimeGammaFixedStarDescendsAt,
    deningerMeyerXiPrimeGammaUnnormalizedFixedStarReceiver] using
      hpositive.isHermitian.apply (1 : Fin 2) (0 : Fin 2)

/-- Some arbitrary-diagonal positive receiver with literal forward/inverse coefficients exists
exactly when the character has unit norm.  The reverse direction chooses the canonical unit
diagonal receiver. -/
theorem xiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt_iff_norm_eq_one
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    XiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt rho p ↔
      ‖deningerMeyerXiPrimeGammaCharacter rho p‖ = 1 := by
  constructor
  · rintro ⟨d0, d1, hpositive⟩
    exact
      norm_deningerMeyerXiPrimeGammaCharacter_eq_one_of_unnormalizedFixedStarPositive
        rho p d0 d1 hpositive
  · intro hunit
    refine ⟨1, 1, ?_⟩
    have hpositive :=
      xiSelectedBilateralPositiveSourceReceiverAt_of_norm_eq_one rho p hunit
    simpa [deningerMeyerXiPrimeGammaUnnormalizedFixedStarReceiver,
      XiSelectedBilateralPositiveSourceReceiverAt,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver] using hpositive

/-- Fixed-star equality, arbitrary-diagonal positive reception, and unit-diagonal positive
reception are exactly the same pointwise descent law. -/
theorem deningerMeyerXiPrimeGammaFixedStarDescendsAt_iff_unnormalizedPositive
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    DeningerMeyerXiPrimeGammaFixedStarDescendsAt rho p ↔
      XiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt rho p := by
  rw [deningerMeyerXiPrimeGammaFixedStarDescendsAt_iff_norm_eq_one,
    xiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt_iff_norm_eq_one]

theorem xiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt_iff_unitDiagonal
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    XiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt rho p ↔
      XiSelectedBilateralPositiveSourceReceiverAt rho p := by
  rw [xiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt_iff_norm_eq_one,
    xiSelectedBilateralPositiveSourceReceiverAt_iff_norm_eq_one]

/-- Fixed-star bilateral positivity is exactly triviality of the source-derived modular
countercharacter at the retained prime time. -/
theorem xiSelectedBilateralPositiveSourceReceiverAt_iff_sourceCountercharacter_eq_one
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    XiSelectedBilateralPositiveSourceReceiverAt rho p ↔
      xiCenteredFlowSourceCountercharacter rho (Real.log (p : ℝ)) = 1 := by
  rw [xiSelectedBilateralPositiveSourceReceiverAt_iff_norm_eq_one]
  have hnonneg : 0 ≤ ‖deningerMeyerXiPrimeGammaCharacter rho p‖ := norm_nonneg _
  rw [← deningerMeyerXiPrimeGammaModularWeight_eq_sourceCountercharacter,
    deningerMeyerXiPrimeGammaModularWeight]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    nlinarith

/-- Pointwise arithmetic content: one canonical bilateral positive receiver is equivalent to
critical-line placement of its selected Xi divisor. -/
theorem xiSelectedBilateralPositiveSourceReceiverAt_iff_re_eq_half
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    XiSelectedBilateralPositiveSourceReceiverAt rho p ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [xiSelectedBilateralPositiveSourceReceiverAt_iff_norm_eq_one,
    deningerMeyerXiPrimeGammaCharacter_eq_deltaS,
    norm_deltaS_eq_one_iff p.2.two_le]

/-- Arbitrary diagonal freedom does not weaken the arithmetic endpoint. -/
theorem xiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt_iff_re_eq_half
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    XiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt rho p ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [xiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt_iff_unitDiagonal,
    xiSelectedBilateralPositiveSourceReceiverAt_iff_re_eq_half]

/-- Integral Cartier descent and canonical bilateral positivity are the same fixed-star producer,
expressed respectively as an additive source reporter and a positive moment receiver. -/
theorem xiSelectedBilateralPositiveSourceReceiverAt_iff_integralGammaReporter
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    XiSelectedBilateralPositiveSourceReceiverAt rho p ↔
      Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p) := by
  rw [xiSelectedBilateralPositiveSourceReceiverAt_iff_re_eq_half,
    deningerXiBidirectionalIntegralGammaReporter_nonempty_iff]

/-- Off the critical line the modular-covariant receiver remains positive, but it cannot equal
the fixed-star coefficient-faithful receiver. -/
theorem deningerMeyerXiPrimeGammaModularReceiver_ne_canonical_of_re_ne_half
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    deningerMeyerXiPrimeGammaModularBilateralReceiver rho p ≠
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver rho p := by
  intro heq
  have hpositive : XiSelectedBilateralPositiveSourceReceiverAt rho p := by
    rw [XiSelectedBilateralPositiveSourceReceiverAt, ← heq]
    exact deningerMeyerXiPrimeGammaModularBilateralReceiver_posSemidef rho p
  exact hoff ((xiSelectedBilateralPositiveSourceReceiverAt_iff_re_eq_half rho p).1 hpositive)

/-- Global endpoint: constructing fixed-star bilateral positive receivers for all retained Xi
divisors is exactly RH. -/
theorem everyXiSelectedBilateralPositiveSourceReceiver_iff_riemannHypothesis :
    EveryXiSelectedBilateralPositiveSourceReceiver ↔ RiemannHypothesis := by
  constructor
  · intro hreceiver
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (xiSelectedBilateralPositiveSourceReceiverAt_iff_re_eq_half
      rho (⟨2, Nat.prime_two⟩ : Nat.Primes)).1
        (hreceiver rho (⟨2, Nat.prime_two⟩ : Nat.Primes))
  · intro hRH rho p
    exact (xiSelectedBilateralPositiveSourceReceiverAt_iff_re_eq_half rho p).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

/-- Global sharpening: even existence of arbitrary-diagonal positive fixed-star receivers for all
selected Xi divisors is exactly RH.  Unit diagonal is therefore not part of the open producer. -/
theorem everyXiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiver_iff_riemannHypothesis :
    EveryXiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiver ↔
      RiemannHypothesis := by
  constructor
  · intro hreceiver
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact
      (xiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt_iff_re_eq_half
        rho (⟨2, Nat.prime_two⟩ : Nat.Primes)).1
          (hreceiver rho (⟨2, Nat.prime_two⟩ : Nat.Primes))
  · intro hRH rho p
    exact
      (xiSelectedBilateralUnnormalizedFixedStarPositiveSourceReceiverAt_iff_re_eq_half
        rho p).2 (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
