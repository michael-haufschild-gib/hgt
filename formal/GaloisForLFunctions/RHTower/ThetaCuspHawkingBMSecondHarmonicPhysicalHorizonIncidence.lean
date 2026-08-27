import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicHorizonBasisGreenKrein

/-!
# Physical BM second-harmonic horizon incidence

Birmingham--Mokhtari write the physical master field as
`exp (-i * omega * tau) * z^alpha * F(z)`, with `alpha = -i * omega / 2` and
`c = 1 - i * omega`.  Hence `c = 1 + 2 * alpha`.  Dressing the regular reduced
solution gives the ingoing phase `exp (-i * omega * (tau + log z / 2))`; dressing the
complementary reduced solution adds `z^(1-c)` and gives the outgoing phase
`exp (-i * omega * (tau - log z / 2))`.

This identifies the exact regular/complementary horizon lines, and therefore their
normalizable-AdS Green blocks, as frequency-domain ingoing/outgoing blocks.  It does not identify
the same-complex-frequency outgoing block with a Schwarz-conjugate advanced distribution; that
still requires conjugate-frequency transport and time-domain support.

`[LITERATURE-DERIVED] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Birmingham--Mokhtari ingoing horizon exponent `alpha = -i omega / 2`. -/
def d4BMIngoingHorizonExponent (omega : ℂ) : ℂ :=
  -Complex.I * omega / 2

/-- Opposite Birmingham--Mokhtari horizon exponent. -/
def d4BMOutgoingHorizonExponent (omega : ℂ) : ℂ :=
  -d4BMIngoingHorizonExponent omega

/-- Exact BM parameter relation `c = 1 + 2 alpha`. -/
theorem d4BMCausalRadialC_eq_one_add_two_ingoingHorizonExponent
    (omega : ℂ) :
    d4BMCausalRadialC omega = 1 + 2 * d4BMIngoingHorizonExponent omega := by
  simp [d4BMCausalRadialC, d4BMIngoingHorizonExponent]
  ring

/-- Dressing the complementary reduced branch changes the full exponent from `alpha` to
`-alpha`. -/
theorem d4BMIngoingHorizonExponent_add_complementary_eq_outgoing
    (omega : ℂ) :
    d4BMIngoingHorizonExponent omega + (1 - d4BMCausalRadialC omega) =
      d4BMOutgoingHorizonExponent omega := by
  rw [d4BMCausalRadialC_eq_one_add_two_ingoingHorizonExponent]
  simp [d4BMOutgoingHorizonExponent]
  ring

/-- Positive-ray realization of a complex radial power. -/
def d4BMHorizonLogPower (exponent : ℂ) (z : ℝ) : ℂ :=
  Complex.exp (exponent * (Real.log z : ℂ))

/-- Fourier time phase used by the BM master-field convention. -/
def d4BMFourierTimePhase (omega : ℂ) (tau : ℝ) : ℂ :=
  Complex.exp (-Complex.I * omega * (tau : ℂ))

/-- Dimensionless future-horizon asymptotic null coordinate. -/
def d4BMIngoingHorizonCoordinate (tau z : ℝ) : ℝ :=
  tau + Real.log z / 2

/-- Dimensionless past-horizon asymptotic null coordinate. -/
def d4BMOutgoingHorizonCoordinate (tau z : ℝ) : ℝ :=
  tau - Real.log z / 2

/-- Time phase times the BM ingoing power is exactly a function of the future-horizon coordinate. -/
theorem d4BMFourierTimePhase_mul_ingoingHorizonLogPower
    (omega : ℂ) (tau z : ℝ) :
    d4BMFourierTimePhase omega tau *
        d4BMHorizonLogPower (d4BMIngoingHorizonExponent omega) z =
      Complex.exp
        (-Complex.I * omega * (d4BMIngoingHorizonCoordinate tau z : ℂ)) := by
  rw [d4BMFourierTimePhase, d4BMHorizonLogPower, ← Complex.exp_add]
  congr 1
  simp [d4BMIngoingHorizonExponent, d4BMIngoingHorizonCoordinate]
  ring

/-- Time phase times the opposite BM power is exactly a function of the past-horizon coordinate. -/
theorem d4BMFourierTimePhase_mul_outgoingHorizonLogPower
    (omega : ℂ) (tau z : ℝ) :
    d4BMFourierTimePhase omega tau *
        d4BMHorizonLogPower (d4BMOutgoingHorizonExponent omega) z =
      Complex.exp
        (-Complex.I * omega * (d4BMOutgoingHorizonCoordinate tau z : ℂ)) := by
  rw [d4BMFourierTimePhase, d4BMHorizonLogPower, ← Complex.exp_add]
  congr 1
  simp [d4BMOutgoingHorizonExponent, d4BMIngoingHorizonExponent,
    d4BMOutgoingHorizonCoordinate]
  ring

/-- The common ingoing power times `z^(1-c)` is the outgoing power. -/
theorem d4BMIngoingHorizonLogPower_mul_complementary_eq_outgoing
    (omega : ℂ) (z : ℝ) :
    d4BMHorizonLogPower (d4BMIngoingHorizonExponent omega) z *
        d4BMHorizonLogPower (1 - d4BMCausalRadialC omega) z =
      d4BMHorizonLogPower (d4BMOutgoingHorizonExponent omega) z := by
  rw [d4BMHorizonLogPower, d4BMHorizonLogPower, d4BMHorizonLogPower,
    ← Complex.exp_add]
  congr 1
  rw [← add_mul, d4BMIngoingHorizonExponent_add_complementary_eq_outgoing]

/-- Physical BM master field obtained by dressing the regular reduced `++` solution. -/
def d4BMPlusPlusRegularPhysicalMasterField
    (n : ℕ) (chi : ℂ) (tau z : ℝ) : ℂ :=
  let omega := d4BMCausalPlusPlusFrequency n chi
  d4BMFourierTimePhase omega tau *
      d4BMHorizonLogPower (d4BMIngoingHorizonExponent omega) z *
    d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ)

/-- Physical BM master field obtained by dressing the complementary reduced `++` solution. -/
def d4BMPlusPlusComplementaryPhysicalMasterField
    (n : ℕ) (chi : ℂ) (tau z : ℝ) : ℂ :=
  let omega := d4BMCausalPlusPlusFrequency n chi
  d4BMFourierTimePhase omega tau *
      d4BMHorizonLogPower (d4BMIngoingHorizonExponent omega) z *
    d4BMPlusPlusComplementaryHypergeometricSolution n chi z

/-- The regular physical master field has exact ingoing horizon phase. -/
theorem d4BMPlusPlusRegularPhysicalMasterField_eq_ingoingPhase
    (n : ℕ) (chi : ℂ) (tau z : ℝ) :
    d4BMPlusPlusRegularPhysicalMasterField n chi tau z =
      Complex.exp
          (-Complex.I * d4BMCausalPlusPlusFrequency n chi *
            (d4BMIngoingHorizonCoordinate tau z : ℂ)) *
        d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) := by
  rw [d4BMPlusPlusRegularPhysicalMasterField]
  exact congrArg
    (fun x : ℂ => x * d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ))
    (d4BMFourierTimePhase_mul_ingoingHorizonLogPower
      (d4BMCausalPlusPlusFrequency n chi) tau z)

/-- The complementary physical master field has exact outgoing horizon phase. -/
theorem d4BMPlusPlusComplementaryPhysicalMasterField_eq_outgoingPhase
    (n : ℕ) (chi : ℂ) (tau z : ℝ) :
    d4BMPlusPlusComplementaryPhysicalMasterField n chi tau z =
      Complex.exp
          (-Complex.I * d4BMCausalPlusPlusFrequency n chi *
            (d4BMOutgoingHorizonCoordinate tau z : ℂ)) *
        d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ) := by
  rw [d4BMPlusPlusComplementaryPhysicalMasterField,
    d4BMPlusPlusComplementaryHypergeometricSolution,
    d4BMPlusPlusLeadingComplementaryFrobeniusBranch]
  have hlam : d4BMPlusPlusComplementaryFrobeniusExponent n chi =
      1 - d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) := rfl
  rw [hlam]
  change
    (d4BMFourierTimePhase (d4BMCausalPlusPlusFrequency n chi) tau *
      d4BMHorizonLogPower
        (d4BMIngoingHorizonExponent (d4BMCausalPlusPlusFrequency n chi)) z) *
        (d4BMHorizonLogPower
            (1 - d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) z *
          d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ)) = _
  calc
    _ = d4BMFourierTimePhase (d4BMCausalPlusPlusFrequency n chi) tau *
          (d4BMHorizonLogPower
              (d4BMIngoingHorizonExponent (d4BMCausalPlusPlusFrequency n chi)) z *
            d4BMHorizonLogPower
              (1 - d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) z) *
          d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ) := by ring
    _ = _ := by
      rw [d4BMIngoingHorizonLogPower_mul_complementary_eq_outgoing,
        d4BMFourierTimePhase_mul_outgoingHorizonLogPower]

/-- Both BM analytic horizon amplitudes use canonical unit normalization. -/
theorem d4BMPlusPlusPhysicalHorizonAnalyticAmplitudes_eq_one
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusRegularHypergeometricSolution n chi 0 = 1 ∧
      d4BMPlusPlusComplementaryHypergeometricFactor n chi 0 = 1 := by
  simp

/-- Combined exact ingoing/outgoing incidence of the canonical `++` horizon basis. -/
theorem d4BMPlusPlusCanonicalPhysicalHorizonIncidence
    (n : ℕ) (chi : ℂ) :
    (∀ tau z : ℝ,
        d4BMPlusPlusRegularPhysicalMasterField n chi tau z =
          Complex.exp
              (-Complex.I * d4BMCausalPlusPlusFrequency n chi *
                (d4BMIngoingHorizonCoordinate tau z : ℂ)) *
            d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ)) ∧
      (∀ tau z : ℝ,
        d4BMPlusPlusComplementaryPhysicalMasterField n chi tau z =
          Complex.exp
              (-Complex.I * d4BMCausalPlusPlusFrequency n chi *
                (d4BMOutgoingHorizonCoordinate tau z : ℂ)) *
            d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ)) := by
  exact ⟨d4BMPlusPlusRegularPhysicalMasterField_eq_ingoingPhase n chi,
    d4BMPlusPlusComplementaryPhysicalMasterField_eq_outgoingPhase n chi⟩

/-- Every actual Xi fibre has exact canonical ingoing/outgoing BM horizon incidence. -/
theorem d4BMXiPlusPlusCanonicalPhysicalHorizonIncidence
    (n : ℕ) (q : XiZeroCopy) :
    (∀ tau z : ℝ,
        d4BMPlusPlusRegularPhysicalMasterField n
            (d4BMXiMixedHorizonAngularMomentum q) tau z =
          Complex.exp
              (-Complex.I *
                d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q) *
                (d4BMIngoingHorizonCoordinate tau z : ℂ)) *
            d4BMPlusPlusRegularHypergeometricSolution n
              (d4BMXiMixedHorizonAngularMomentum q) (z : ℂ)) ∧
      (∀ tau z : ℝ,
        d4BMPlusPlusComplementaryPhysicalMasterField n
            (d4BMXiMixedHorizonAngularMomentum q) tau z =
          Complex.exp
              (-Complex.I *
                d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q) *
                (d4BMOutgoingHorizonCoordinate tau z : ℂ)) *
            d4BMPlusPlusComplementaryHypergeometricFactor n
              (d4BMXiMixedHorizonAngularMomentum q) (z : ℂ)) :=
  d4BMPlusPlusCanonicalPhysicalHorizonIncidence n
    (d4BMXiMixedHorizonAngularMomentum q)

/-- Ingoing frequency-domain right Green block: regular horizon line plus normalizable AdS line. -/
def d4BMPlusPlusIngoingAdSNormalizableRightEndpointGreenKernel
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularAdSNormalizableRightEndpointGreenKernel n chi t z

/-- Outgoing frequency-domain right Green block: complementary horizon line plus normalizable AdS
line. -/
def d4BMPlusPlusOutgoingAdSNormalizableRightEndpointGreenKernel
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusComplementaryAdSNormalizableRightEndpointGreenKernel n chi t z

/-- Exact rank-one difference of physical ingoing and outgoing frequency-domain Green blocks. -/
theorem d4BMPlusPlusIngoing_sub_outgoingRightEndpointGreenKernel
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusIngoingAdSNormalizableRightEndpointGreenKernel n chi t z -
        d4BMPlusPlusOutgoingAdSNormalizableRightEndpointGreenKernel n chi t z =
      -d4BMPlusPlusComplementaryFrobeniusExponent n chi *
          d4BMPlusPlusAdSNormalizableSolution n chi t *
          d4BMPlusPlusAdSNormalizableSolution n chi z /
        (d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t *
          d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t) := by
  exact d4BMPlusPlusHorizonBasisRightEndpointGreenKernel_sub n chi hchi ht0 ht1

/-- Finite source response through the physical ingoing frequency-domain Green block. -/
def d4BMPlusPlusFiniteIngoingAdSNormalizableRightEndpointGreenResponse
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusFiniteRegularAdSNormalizableRightEndpointGreenResponse
    S point source n chi z

/-- Finite source response through the physical outgoing frequency-domain Green block. -/
def d4BMPlusPlusFiniteOutgoingAdSNormalizableRightEndpointGreenResponse
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusFiniteComplementaryAdSNormalizableRightEndpointGreenResponse
    S point source n chi z

/-- Physical ingoing-minus-outgoing finite response is source-global and rank one. -/
theorem d4BMPlusPlusFiniteIngoing_sub_outgoingRightEndpointGreenResponse
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (z : ℝ)
    (hpoint : ∀ i ∈ S, 0 < point i ∧ point i < 1) :
    d4BMPlusPlusFiniteIngoingAdSNormalizableRightEndpointGreenResponse
          S point source n chi z -
        d4BMPlusPlusFiniteOutgoingAdSNormalizableRightEndpointGreenResponse
          S point source n chi z =
      d4BMPlusPlusFiniteHorizonBasisGreenSourceProjection S point source n chi *
        d4BMPlusPlusAdSNormalizableSolution n chi z := by
  exact d4BMPlusPlusFiniteHorizonBasisRightEndpointGreenResponse_sub
    S point source n chi hchi z hpoint

/-- Actual Xi fibres inherit the source-global physical ingoing-minus-outgoing Green identity. -/
theorem d4BMXiPlusPlusFiniteIngoing_sub_outgoingRightEndpointGreenResponse
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (q : XiZeroCopy) (z : ℝ)
    (hpoint : ∀ i ∈ S, 0 < point i ∧ point i < 1) :
    d4BMPlusPlusFiniteIngoingAdSNormalizableRightEndpointGreenResponse S point source n
          (d4BMXiMixedHorizonAngularMomentum q) z -
        d4BMPlusPlusFiniteOutgoingAdSNormalizableRightEndpointGreenResponse S point source n
          (d4BMXiMixedHorizonAngularMomentum q) z =
      d4BMPlusPlusFiniteHorizonBasisGreenSourceProjection S point source n
          (d4BMXiMixedHorizonAngularMomentum q) *
        d4BMPlusPlusAdSNormalizableSolution n
          (d4BMXiMixedHorizonAngularMomentum q) z := by
  exact d4BMXiPlusPlusFiniteHorizonBasisRightEndpointGreenResponse_sub
    S point source n q z hpoint

end

end RHTower
