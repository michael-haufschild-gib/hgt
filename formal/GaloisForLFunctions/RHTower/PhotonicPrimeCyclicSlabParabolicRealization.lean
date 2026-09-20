import GaloisForLFunctions.RHTower.PhotonicParabolicReturn
import GaloisForLFunctions.RHTower.PhotonicReturnMonodromy
import GaloisForLFunctions.HTGeometry.UnipotentDiagonalizationObstruction
import GaloisForLFunctions.HTGeometry.RabiHatanoNelsonAlgebra
import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalDynamicChirality
import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalComplexModulation
import GaloisForLFunctions.RHTower.BilateralModerationXiDivisorBridge

/-!
# Prime-impedance cyclic oscillator-slab realization of the PTR transfer

## PTR proof-chain position

The PTR receiver needs a non-scalar parabolic transfer.  The source no-gos
already force any all-prime realization to use both prime-dependent frame data
and a genuinely coupled two-channel transfer.  This module constructs that
remaining algebraic transfer layer exactly.

For each prime, use impedance `log p` in two literal oscillator-slab transfer
matrices with impedance ratio `1 : 4` and common rational phase data
`cos = 3/5`, `sin = 4/5`.  Their cyclic product is the prime-frame conjugate of
the corpus's exact binary slab cell; after two cycles it intertwines with
`photonicParabolic`.  Its nonzero off-diagonal entry proves it is genuinely
coupled, not a scalar multiplier.

The two-slab construction itself is not a Maxwell boundary-condition
derivation.  The later resonant Rabi/BdG section supplies the same parabolic
transfer from the corpus's literal mean-field amplitude equation.  The later
constitutive section identifies its coupling with a prime-rate, order-four PTC
harmonic and an exact OAM-resolved selector.  The remaining physical PTR burden
is to derive that selector as a prime-dependent time-crystal/Maxwell temporal
interface operator.  Its Floquet reduction must be an infinite sideband ladder
or prove an exact boundary-dark-mode overlap law: the literal nonzero material
harmonic cannot define a finite closed channel model.  Then establish the
ramified phase and defect-confinement law.  The complex-PTC conormal section
below fixes the infinite-ladder target exactly: its moderation at every Xi
divisor copy is equivalent to RH, but a literal Maxwell amplitude derivation
remains open.
-/

open Complex Matrix
open scoped Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.RabiHatanoNelson

/-- Exact two-channel oscillator-slab transfer with rational phase data. -/
noncomputable def photonicOscillatorSlab (κ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![3 / 5, (4 / 5) / κ; -(4 / 5) * κ, 3 / 5]

/-- Continuous harmonic two-channel transfer at impedance `κ` and phase `t`. -/
noncomputable def photonicOscillatorFlow (κ : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Real.cos t, (Real.sin t : ℂ) / κ; -(Real.sin t : ℂ) * κ, Real.cos t]

/-- The exact phase with cosine `3/5` and positive sine `4/5`. -/
noncomputable def photonicRationalSlabPhase : ℝ := Real.arccos (3 / 5)

theorem photonicRationalSlabPhase_cos :
    Real.cos photonicRationalSlabPhase = 3 / 5 := by
  apply Real.cos_arccos <;> norm_num [photonicRationalSlabPhase]

theorem photonicRationalSlabPhase_sin :
    Real.sin photonicRationalSlabPhase = 4 / 5 := by
  rw [photonicRationalSlabPhase, Real.sin_arccos]
  rw [Real.sqrt_eq_iff_mul_self_eq]
  · norm_num
  · norm_num
  · norm_num

/-- Harmonic transfer composes exactly over consecutive phase intervals. -/
theorem photonicOscillatorFlow_add (κ : ℂ) (hκ : κ ≠ 0) (s t : ℝ) :
    photonicOscillatorFlow κ (s + t) =
      photonicOscillatorFlow κ s * photonicOscillatorFlow κ t := by
  rw [photonicOscillatorFlow, photonicOscillatorFlow, photonicOscillatorFlow,
    Real.cos_add, Real.sin_add]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> push_cast <;>
    field_simp [hκ] <;> ring

/-- The rational slab is a literal sample of the continuous harmonic transfer flow. -/
theorem photonicOscillatorSlab_eq_flow (κ : ℂ) :
    photonicOscillatorSlab κ = photonicOscillatorFlow κ photonicRationalSlabPhase := by
  rw [photonicOscillatorSlab, photonicOscillatorFlow,
    photonicRationalSlabPhase_cos, photonicRationalSlabPhase_sin]
  norm_num

/-- Prime impedance forced by the source-normal derivative of `p⁻ᵘ`. -/
noncomputable def photonicPrimeImpedance (p : Nat.Primes) : ℂ :=
  Real.log ((p : ℕ) : ℝ)

/-- The prime-dependent value/derivative channel frame. -/
noncomputable def photonicPrimeFrame (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, photonicPrimeImpedance p]

/-- Inverse of the prime-dependent channel frame. -/
noncomputable def photonicPrimeFrameInv (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, (photonicPrimeImpedance p)⁻¹]

/-- One prime's two-slab cyclic transfer, at impedances `4 log p` then `log p`. -/
noncomputable def photonicPrimeCyclicSlabCell (p : Nat.Primes) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  photonicOscillatorSlab (4 * photonicPrimeImpedance p) *
    photonicOscillatorSlab (photonicPrimeImpedance p)

/-- The arithmetic prime-clock drive rate, equal to `1 / log p`. -/
noncomputable def photonicPrimeDriveRate (p : Nat.Primes) : ℝ :=
  (Real.log ((p : ℕ) : ℝ))⁻¹

/-- Physical period whose prime-clock phase advance is one logarithmic-cover deck turn. -/
noncomputable def photonicPrimeDeckPeriod (p : Nat.Primes) : ℝ :=
  2 * Real.pi / photonicPrimeDriveRate p

/-- Canonical logarithmic-cover coordinate of physical prime-clock time. -/
noncomputable def photonicPrimeDeckCoordinate (p : Nat.Primes) (t : ℝ) : ℂ :=
  Complex.I * ((photonicPrimeDriveRate p * t : ℝ) : ℂ)

/-- Physical duration which accumulates the fixed rational slab phase at the prime drive rate. -/
noncomputable def photonicPrimeSlabDuration (p : Nat.Primes) : ℝ :=
  photonicRationalSlabPhase / photonicPrimeDriveRate p

/-- Harmonic flow driven at angular rate `Ω` for physical duration `τ`. -/
noncomputable def photonicDrivenOscillatorFlow (κ : ℂ) (Ω τ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  photonicOscillatorFlow κ (Ω * τ)

/-- One prime's literal two-slab periodic driven cell. -/
noncomputable def photonicPrimeCyclicTimeCrystalCell (p : Nat.Primes) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  photonicDrivenOscillatorFlow (4 * photonicPrimeImpedance p)
      (photonicPrimeDriveRate p) (photonicPrimeSlabDuration p) *
    photonicDrivenOscillatorFlow (photonicPrimeImpedance p)
      (photonicPrimeDriveRate p) (photonicPrimeSlabDuration p)

theorem photonicPrimeImpedance_ne_zero (p : Nat.Primes) :
    photonicPrimeImpedance p ≠ 0 := by
  change (Real.log ((p : ℕ) : ℝ) : ℂ) ≠ 0
  exact_mod_cast (Nat.Prime.log_pos p.property).ne'

theorem photonicPrimeDriveRate_pos (p : Nat.Primes) : 0 < photonicPrimeDriveRate p := by
  exact inv_pos.mpr (Nat.Prime.log_pos p.property)

theorem photonicPrimeDriveRate_ne_zero (p : Nat.Primes) : photonicPrimeDriveRate p ≠ 0 :=
  (photonicPrimeDriveRate_pos p).ne'

/-- One physical prime-clock period is exactly the positive deck generator. -/
theorem photonicPrimeDeckCoordinate_period (p : Nat.Primes) (t : ℝ) :
    photonicPrimeDeckCoordinate p (t + photonicPrimeDeckPeriod p) =
      photonicPrimeDeckCoordinate p t + 2 * (Real.pi : ℂ) * Complex.I := by
  unfold photonicPrimeDeckCoordinate photonicPrimeDeckPeriod
  rw [mul_add, mul_div_cancel₀ _ (photonicPrimeDriveRate_ne_zero p)]
  push_cast
  ring

/-- The physical prime-clock lift exponentiates to the unit-circle phase. -/
theorem norm_exp_photonicPrimeDeckCoordinate (p : Nat.Primes) (t : ℝ) :
    ‖Complex.exp (photonicPrimeDeckCoordinate p t)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [photonicPrimeDeckCoordinate, Complex.mul_re]

/-- The return lift undergoes its exact monodromy after one physical prime-clock period. -/
theorem photonicReturnLift_primeDeck_period (s : ℂ) (p : Nat.Primes) (t : ℝ) :
    photonicReturnLift s (photonicPrimeDeckCoordinate p (t + photonicPrimeDeckPeriod p)) =
      photonicReturnCharacter s * photonicReturnLift s (photonicPrimeDeckCoordinate p t) +
        (1 - photonicReturnCharacter s) *
          photonicRegularPhase s (Complex.exp (photonicPrimeDeckCoordinate p t)) := by
  rw [photonicPrimeDeckCoordinate_period]
  exact photonicReturnLift_deck s (photonicPrimeDeckCoordinate p t)

/-- Interfacial time-crystal base frequency making the `q = 0` photon detuning prime-exact. -/
noncomputable def photonicPrimeRabiBandEdgeBase (p : Nat.Primes) (J : ℝ) : ℝ :=
  2 * J + photonicPrimeDriveRate p

/-- Literal `q = 0` photon detuning of the calibrated interfacial time crystal. -/
noncomputable def photonicPrimeRabiBandEdgeDetuning (p : Nat.Primes) (J : ℝ) : ℝ :=
  photonDetuning (photonicPrimeRabiBandEdgeBase p J) J 0

theorem photonicPrimeRabiBandEdgeDetuning_eq_driveRate (p : Nat.Primes) (J : ℝ) :
    photonicPrimeRabiBandEdgeDetuning p J = photonicPrimeDriveRate p := by
  simp [photonicPrimeRabiBandEdgeDetuning, photonicPrimeRabiBandEdgeBase, photonDetuning]

/-- The `q = 0` physical detuning induces exactly the canonical prime deck coordinate. -/
noncomputable def photonicPrimeRabiBandEdgeDeckCoordinate
    (p : Nat.Primes) (J t : ℝ) : ℂ :=
  Complex.I * ((photonicPrimeRabiBandEdgeDetuning p J * t : ℝ) : ℂ)

theorem photonicPrimeRabiBandEdgeDeckCoordinate_eq_primeDeckCoordinate
    (p : Nat.Primes) (J t : ℝ) :
    photonicPrimeRabiBandEdgeDeckCoordinate p J t = photonicPrimeDeckCoordinate p t := by
  rw [photonicPrimeRabiBandEdgeDeckCoordinate,
    photonicPrimeRabiBandEdgeDetuning_eq_driveRate]
  rfl

/-- The physical calibrated detuning gives the return deck law once per prime-clock period. -/
theorem photonicReturnLift_primeRabiBandEdge_period
    (s : ℂ) (p : Nat.Primes) (J t : ℝ) :
    photonicReturnLift s
        (photonicPrimeRabiBandEdgeDeckCoordinate p J (t + photonicPrimeDeckPeriod p)) =
      photonicReturnCharacter s *
          photonicReturnLift s (photonicPrimeRabiBandEdgeDeckCoordinate p J t) +
        (1 - photonicReturnCharacter s) *
          photonicRegularPhase s (Complex.exp (photonicPrimeRabiBandEdgeDeckCoordinate p J t)) := by
  rw [photonicPrimeRabiBandEdgeDeckCoordinate_eq_primeDeckCoordinate,
    photonicPrimeRabiBandEdgeDeckCoordinate_eq_primeDeckCoordinate]
  exact photonicReturnLift_primeDeck_period s p t

/-- Prime-rate hopping is necessarily nonreciprocal in the interfacial time-crystal model. -/
theorem photonicPrimeRabiBandEdge_nonreciprocal (p : Nat.Primes) (J : ℝ) :
    ((J - photonicPrimeDriveRate p : ℝ) : ℂ) ≠
      star ((J + photonicPrimeDriveRate p : ℝ) : ℂ) := by
  intro h
  have hzero := (directionalHopping_reverseAdjoint_iff J (photonicPrimeDriveRate p)).mp h
  exact (photonicPrimeDriveRate_pos p).ne' hzero

/-- Quarter-mode detuning at the same prime rate in the interfacial time crystal. -/
noncomputable def photonicPrimeRabiQuarterDetuning (p : Nat.Primes) (J : ℝ) : ℝ :=
  photonDetuning (photonicPrimeDriveRate p) J (Real.pi / 2)

theorem photonicPrimeRabiQuarterDetuning_eq_driveRate (p : Nat.Primes) (J : ℝ) :
    photonicPrimeRabiQuarterDetuning p J = photonicPrimeDriveRate p := by
  rw [photonicPrimeRabiQuarterDetuning, photonDetuning_quarter]

/-- The nonreciprocal prime-rate quarter mode lies exactly on the model's periodic boundary. -/
theorem photonicPrimeRabiQuarterMode_on_periodic_boundary (p : Nat.Primes) (Ω J : ℝ) :
    pbcRealResidual Ω (-photonicPrimeDriveRate p) 0 (photonicPrimeDriveRate p)
        (photonicPrimeRabiQuarterDetuning p J) 0 (Real.pi / 2) = 0 ∧
      pbcImagResidual Ω (-photonicPrimeDriveRate p) 0 (photonicPrimeDriveRate p)
        (photonicPrimeRabiQuarterDetuning p J) 0 (Real.pi / 2) = 0 := by
  simpa only [photonicPrimeRabiQuarterDetuning] using
    pbc_lossless_quarter_mode_on_boundary Ω (photonicPrimeDriveRate p)
      (photonicPrimeDriveRate p) J

/-! ### Constitutive harmonic calibration -/

/-- The positive helical Fourier component in the literal rotating PTC permittivity. -/
noncomputable def photonicPositiveConstitutiveHarmonic
    (εbar δε : ℝ) (m : ℤ) (θ Ω t : ℝ) : ℂ :=
  ((εbar * δε / 2 : ℝ) : ℂ) * rotatingPositiveHarmonic m θ Ω t

/--
The two helical constitutive components reconstruct the corpus's literal
rotating complex permittivity, together with its base and loss terms.
-/
theorem rotatingComplexPermittivity_eq_constitutive_harmonics
    (εbar δε εLoss : ℝ) (m : ℤ) (θ Ω t : ℝ) :
    rotatingComplexPermittivity εbar δε εLoss m θ Ω t =
      (εbar : ℂ) +
        photonicPositiveConstitutiveHarmonic εbar δε m θ Ω t +
        ((εbar * δε / 2 : ℝ) : ℂ) * rotatingNegativeHarmonic m θ Ω t +
        Complex.I * (εLoss : ℂ) := by
  rw [rotatingComplexPermittivity_helical_decomposition,
    photonicPositiveConstitutiveHarmonic]
  ring

/-- At quadrature the positive helical component is exactly `i`, independently of drive rate. -/
theorem rotatingPositiveHarmonic_quadrature (Ω : ℝ) :
    rotatingPositiveHarmonic 1 (Real.pi / 2) Ω 0 = Complex.I := by
  rw [rotatingPositiveHarmonic, rotatingModulationPhase]
  convert Complex.exp_pi_div_two_mul_I using 1
  push_cast
  ring_nf

/-- The corpus's order-four dynamic-chirality pattern reaches the same quadrature phase at `π/8`. -/
theorem rotatingPositiveHarmonic_orderFour_quadrature (Ω : ℝ) :
    rotatingPositiveHarmonic 4 (Real.pi / 8) Ω 0 = Complex.I := by
  rw [rotatingPositiveHarmonic, rotatingModulationPhase]
  convert Complex.exp_pi_div_two_mul_I using 1
  push_cast
  ring_nf

/--
Quadrature is rigid: the positive constitutive harmonic equals the required
imaginary coupling `i r / 2` exactly when the material product is `εbar δε = r`.
-/
theorem photonicPositiveConstitutiveHarmonic_quadrature_eq_iff
    (εbar δε Ω r : ℝ) :
    photonicPositiveConstitutiveHarmonic εbar δε 1 (Real.pi / 2) Ω 0 =
        Complex.I * ((r : ℂ) / 2) ↔
      εbar * δε = r := by
  rw [photonicPositiveConstitutiveHarmonic, rotatingPositiveHarmonic_quadrature]
  constructor
  · intro h
    have him := congrArg Complex.im h
    simp [Complex.mul_im] at him
    linarith
  · intro h
    subst r
    push_cast
    ring

/-- Prime-rate quadrature harmonic of the unit-baseline rotating PTC material. -/
noncomputable def photonicPrimeConstitutiveHarmonic (p : Nat.Primes) : ℂ :=
  photonicPositiveConstitutiveHarmonic 1 (photonicPrimeDriveRate p) 4
    (Real.pi / 8) (photonicPrimeDriveRate p) 0

/-- The literal prime rotating-material harmonic is the resonant Rabi coupling. -/
theorem photonicPrimeConstitutiveHarmonic_eq_resonantCoupling (p : Nat.Primes) :
    photonicPrimeConstitutiveHarmonic p =
      Complex.I * ((photonicPrimeDriveRate p : ℂ) / 2) := by
  rw [photonicPrimeConstitutiveHarmonic,
    photonicPositiveConstitutiveHarmonic, rotatingPositiveHarmonic_orderFour_quadrature]
  push_cast
  ring

/-- The literal scalar PTC permittivity at the same quadrature phase. -/
noncomputable def photonicPrimeRotatingPermittivityAtQuadrature (p : Nat.Primes) : ℂ :=
  rotatingComplexPermittivity 1 (photonicPrimeDriveRate p) 0 4
    (Real.pi / 8) (photonicPrimeDriveRate p) 0

/--
At quadrature the two scalar helicities cancel in the instantaneous constitutive
value, even though the positive helical Fourier coefficient is nonzero.
-/
theorem photonicPrimeRotatingPermittivityAtQuadrature_eq_one (p : Nat.Primes) :
    photonicPrimeRotatingPermittivityAtQuadrature p = 1 := by
  have hphase :
      rotatingModulationPhase 4 (Real.pi / 8) (photonicPrimeDriveRate p) 0 =
        Real.pi / 2 := by
    simp [rotatingModulationPhase]
    ring
  simp [photonicPrimeRotatingPermittivityAtQuadrature, rotatingComplexPermittivity,
    hphase, Real.cos_pi_div_two]

theorem photonicPrimeConstitutiveHarmonic_ne_zero (p : Nat.Primes) :
    photonicPrimeConstitutiveHarmonic p ≠ 0 := by
  rw [photonicPrimeConstitutiveHarmonic_eq_resonantCoupling]
  apply mul_ne_zero Complex.I_ne_zero
  apply div_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (photonicPrimeDriveRate_ne_zero p)
  · exact OfNat.ofNat_ne_zero 2

/--
No helicity-blind instantaneous scalar constitutive deviation can be the
nonzero prime Rabi coupling.  A viable Maxwell interface must retain a helical
Fourier component (or equivalently be Floquet/non-instantaneous at this step).
-/
theorem not_photonicPrimeConstitutiveHarmonic_eq_instantaneousScalarDeviation
    (p : Nat.Primes) :
    photonicPrimeConstitutiveHarmonic p ≠
      photonicPrimeRotatingPermittivityAtQuadrature p - 1 := by
  rw [photonicPrimeRotatingPermittivityAtQuadrature_eq_one]
  simp only [sub_self]
  exact photonicPrimeConstitutiveHarmonic_ne_zero p

/-- OAM-resolved selector for the order-four dynamic-chirality sideband channels. -/
noncomputable def photonicOrderFourOAMProject (n : ℤ) (z : ℂ) : ℂ :=
  if floquetSidebandAngularMomentum 1 4 n = 5 then z else 0

/-- The negative-helical constitutive companion of the calibrated prime harmonic. -/
noncomputable def photonicPrimeNegativeConstitutiveHarmonic (p : Nat.Primes) : ℂ :=
  ((photonicPrimeDriveRate p / 2 : ℝ) : ℂ) *
    rotatingNegativeHarmonic 4 (Real.pi / 8) (photonicPrimeDriveRate p) 0

/--
Order-four chirality supplies a literal channel distinction: the `+1` sideband
is retained by the `+5` OAM projector.
-/
theorem photonicOrderFourOAMProject_positive (z : ℂ) :
    photonicOrderFourOAMProject 1 z = z := by
  obtain ⟨hplus, _, _, _⟩ := dynamicChirality_orderFour_channels
  simp [photonicOrderFourOAMProject, hplus]

/-- The same OAM projector rejects the counter-helical `-1` sideband. -/
theorem photonicOrderFourOAMProject_negative (z : ℂ) :
    photonicOrderFourOAMProject (-1) z = 0 := by
  obtain ⟨_, hminus, _, _⟩ := dynamicChirality_orderFour_channels
  simp [photonicOrderFourOAMProject, hminus]

/--
The OAM-resolved channel projection retains exactly the prime coupling harmonic
and annihilates its negative-helicity companion.
-/
theorem photonicPrimeOAMProject_selects_constitutiveHarmonic (p : Nat.Primes) :
    photonicOrderFourOAMProject 1 (photonicPrimeConstitutiveHarmonic p) =
      photonicPrimeConstitutiveHarmonic p ∧
    photonicOrderFourOAMProject (-1) (photonicPrimeNegativeConstitutiveHarmonic p) = 0 := by
  exact ⟨photonicOrderFourOAMProject_positive _, photonicOrderFourOAMProject_negative _⟩

/-- Matrix realization of the order-four OAM selector on the positive/negative channel pair. -/
noncomputable def photonicOrderFourOAMProjectionMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0;
     0, 0]

theorem photonicOrderFourOAMProjectionMatrix_mulVec (x y : ℂ) :
    photonicOrderFourOAMProjectionMatrix *ᵥ ![x, y] =
      ![photonicOrderFourOAMProject 1 x, photonicOrderFourOAMProject (-1) y] := by
  obtain ⟨hplus, hminus, _, _⟩ := dynamicChirality_orderFour_channels
  ext i
  fin_cases i <;>
    simp [photonicOrderFourOAMProjectionMatrix, photonicOrderFourOAMProject,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, hplus, hminus]

/-- The OAM selector has no right inverse. -/
theorem photonicOrderFourOAMProjectionMatrix_mul_ne_one (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    photonicOrderFourOAMProjectionMatrix * Q ≠ 1 := by
  intro h
  have hentry := congrFun (congrFun h (1 : Fin 2)) (1 : Fin 2)
  simp [photonicOrderFourOAMProjectionMatrix, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two] at hentry

/-- The OAM selector has no left inverse. -/
theorem mul_photonicOrderFourOAMProjectionMatrix_ne_one (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    Q * photonicOrderFourOAMProjectionMatrix ≠ 1 := by
  intro h
  have hentry := congrFun (congrFun h (1 : Fin 2)) (1 : Fin 2)
  simp [photonicOrderFourOAMProjectionMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/--
No finite invertible two-channel transfer can realize the exact OAM selector.
Hence the surviving temporal interface must be open/non-invertible (or realize
selection only after a larger Floquet-channel dilation).
-/
theorem not_exists_photonicOrderFourOAMProjectionMatrix_twoSidedInverse :
    ¬ ∃ Q : Matrix (Fin 2) (Fin 2) ℂ,
      Q * photonicOrderFourOAMProjectionMatrix = 1 ∧
        photonicOrderFourOAMProjectionMatrix * Q = 1 := by
  rintro ⟨Q, _, hright⟩
  exact photonicOrderFourOAMProjectionMatrix_mul_ne_one Q hright

/--
Minimal conservative three-channel dilation: it leaves the retained channel
fixed and swaps the rejected channel into an explicit outgoing port.
-/
noncomputable def photonicOrderFourOAMDilation : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

/-- Inclusion of the observed positive/negative pair into the three-channel dilation. -/
noncomputable def photonicOrderFourOAMEmbed : Matrix (Fin 3) (Fin 2) ℂ :=
  !![1, 0;
     0, 1;
     0, 0]

/-- Readout of the two observed output channels. -/
noncomputable def photonicOrderFourOAMReadout : Matrix (Fin 2) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, 1, 0]

/-- Readout of the outgoing channel carrying the rejected helicity. -/
noncomputable def photonicOrderFourOAMLeakReadout : Matrix (Fin 1) (Fin 3) ℂ :=
  !![0, 0, 1]

/-- The three-channel dilation is conservative on the input side. -/
theorem photonicOrderFourOAMDilation_unitary_left :
    photonicOrderFourOAMDilationᴴ * photonicOrderFourOAMDilation = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicOrderFourOAMDilation, Matrix.mul_apply, Fin.sum_univ_three]

/-- The three-channel dilation is conservative on the output side. -/
theorem photonicOrderFourOAMDilation_unitary_right :
    photonicOrderFourOAMDilation * photonicOrderFourOAMDilationᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicOrderFourOAMDilation, Matrix.mul_apply, Fin.sum_univ_three]

/-- Compression of the conservative dilation is exactly the OAM selector. -/
theorem photonicOrderFourOAMDilation_compresses :
    photonicOrderFourOAMReadout * photonicOrderFourOAMDilation *
        photonicOrderFourOAMEmbed = photonicOrderFourOAMProjectionMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicOrderFourOAMReadout, photonicOrderFourOAMDilation,
      photonicOrderFourOAMEmbed, photonicOrderFourOAMProjectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_three]

/-- The discarded helicity is routed intact to the explicit outgoing channel. -/
theorem photonicOrderFourOAMDilation_routes_rejected :
    photonicOrderFourOAMLeakReadout * photonicOrderFourOAMDilation *
        photonicOrderFourOAMEmbed = !![0, 1] := by
  ext i j
  fin_cases j <;>
    simp [photonicOrderFourOAMLeakReadout, photonicOrderFourOAMDilation,
      photonicOrderFourOAMEmbed, Matrix.mul_apply, Fin.sum_univ_three]

/-- Fixed auxiliary-port phase completing a quarter rotation to the OAM dilation. -/
noncomputable def photonicOrderFourOAMPortPhase : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, -1]

/-- Continuous rotation coupling the rejected OAM channel to the outgoing port. -/
noncomputable def photonicOAMPortRotation (r t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, Real.cos (r * t), Real.sin (r * t);
     0, -Real.sin (r * t), Real.cos (r * t)]

/-- Real three-port representation of a complex helical constitutive phase. -/
noncomputable def photonicHelicalPhasePortRealification (z : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, z.re, -z.im;
     0, z.im, z.re]

/--
The temporal port rotation is exactly the realification of the literal
order-four positive helical PTC phase at a fixed spatial angle.
-/
theorem photonicOAMPortRotation_eq_helicalPhase_realification (r t : ℝ) :
    photonicOAMPortRotation r t =
      photonicHelicalPhasePortRealification (rotatingPositiveHarmonic 4 0 r t) := by
  rw [photonicOAMPortRotation, photonicHelicalPhasePortRealification,
    rotatingPositiveHarmonic, rotatingModulationPhase]
  have hphase : ((4 : ℤ) : ℝ) * 0 - r * t = -(r * t) := by ring
  have hexp :
      Complex.exp (Complex.I * ((-(r * t) : ℝ) : ℂ)) =
        (Real.cos (-(r * t)) : ℂ) + (Real.sin (-(r * t)) : ℂ) * Complex.I := by
    rw [← Complex.exp_ofReal_mul_I]
    congr 1
    push_cast
    ring
  rw [hphase, hexp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-Complex.ofReal_mul, Real.cos_neg, Real.sin_neg]

/-- Duration of one quarter port rotation at rate `r`. -/
noncomputable def photonicOAMPortDuration (r : ℝ) : ℝ := Real.pi / (2 * r)

theorem photonicOAMPortRotation_zero (r : ℝ) : photonicOAMPortRotation r 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicOAMPortRotation]

/-- The port coupling is an exact one-parameter temporal Floquet flow. -/
theorem photonicOAMPortRotation_add (r s t : ℝ) :
    photonicOAMPortRotation r (s + t) =
      photonicOAMPortRotation r s * photonicOAMPortRotation r t := by
  have hphase : r * (s + t) = r * s + r * t := by ring
  simp only [photonicOAMPortRotation]
  rw [hphase, Real.cos_add, Real.sin_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem photonicOAMPortRate_mul_duration (r : ℝ) (hr : r ≠ 0) :
    r * photonicOAMPortDuration r = Real.pi / 2 := by
  unfold photonicOAMPortDuration
  field_simp [hr]

/-- A quarter port rotation followed by the auxiliary phase is the OAM dilation. -/
theorem photonicOAMPortPhase_mul_rotation_duration (r : ℝ) (hr : r ≠ 0) :
    photonicOrderFourOAMPortPhase *
        photonicOAMPortRotation r (photonicOAMPortDuration r) =
      photonicOrderFourOAMDilation := by
  rw [photonicOAMPortRotation, photonicOAMPortRate_mul_duration r hr,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicOrderFourOAMPortPhase, photonicOrderFourOAMDilation,
      Matrix.mul_apply, Fin.sum_univ_three]

/-- The OAM dilation occurs at exactly one quarter of the physical prime deck period. -/
theorem photonicPrimeOAMPortDuration_eq_deckQuarter (p : Nat.Primes) :
    photonicOAMPortDuration (photonicPrimeDriveRate p) = photonicPrimeDeckPeriod p / 4 := by
  unfold photonicOAMPortDuration photonicPrimeDeckPeriod
  field_simp [photonicPrimeDriveRate_ne_zero p]
  ring

/-- The prime-clock quarter rotation realizes the conservative OAM dilation. -/
theorem photonicPrimeOAMPortPhase_mul_rotation :
    ∀ p : Nat.Primes,
      photonicOrderFourOAMPortPhase *
          photonicOAMPortRotation (photonicPrimeDriveRate p)
            (photonicOAMPortDuration (photonicPrimeDriveRate p)) =
        photonicOrderFourOAMDilation := by
  intro p
  exact photonicOAMPortPhase_mul_rotation_duration _ (photonicPrimeDriveRate_ne_zero p)

/--
The observed two-channel action of the conservative dilation is the exact
order-four OAM selection law.
-/
theorem photonicOrderFourOAMDilation_observed_selector (x y : ℂ) :
    (photonicOrderFourOAMReadout * photonicOrderFourOAMDilation *
        photonicOrderFourOAMEmbed) *ᵥ ![x, y] =
      ![photonicOrderFourOAMProject 1 x, photonicOrderFourOAMProject (-1) y] := by
  rw [photonicOrderFourOAMDilation_compresses]
  exact photonicOrderFourOAMProjectionMatrix_mulVec x y

/-! ### Resonant mean-field amplitude source -/

/--
Two-channel invariant amplitude chain in the corpus's real transverse-spin
mean-field coordinates.  It is the physical chain on which the resonant
periodic Rabi/BdG linearization reduces to the PTR transfer.
-/
noncomputable def photonicRabiResonantAmplitudeChain :
    Matrix (Fin 4) (Fin 2) ℂ :=
  !![1, 0;
     -1, 0;
     0, 2;
     0, 0]

/--
Resonant mean-field amplitude generator: zero particle/hole and spin
diagonals, with imaginary coupling `i r / 2`.  This is a literal
specialization of `meanFieldJacobianMatrix`, which is similar to `-i` times
the corpus's periodic BdG matrix.
-/
noncomputable def photonicRabiResonantAmplitudeGenerator (r : ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  meanFieldJacobianMatrix 0 0 (Complex.I * (r / 2)) 0

/-- The exact two-channel reduced amplitude generator. -/
noncomputable def photonicRabiResonantReducedGenerator (r : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, r;
     0, 0]

/-- Exact finite-time flow of the square-zero resonant amplitude generator. -/
noncomputable def photonicRabiResonantAmplitudeFlow (r : ℂ) (t : ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  1 + (t : ℂ) • photonicRabiResonantAmplitudeGenerator r

/-- The literal mean-field amplitude generator preserves the two-channel chain. -/
theorem photonicRabiResonantAmplitudeGenerator_chain (r : ℂ) :
    photonicRabiResonantAmplitudeGenerator r * photonicRabiResonantAmplitudeChain =
      photonicRabiResonantAmplitudeChain * photonicRabiResonantReducedGenerator r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicRabiResonantAmplitudeGenerator, photonicRabiResonantAmplitudeChain,
      photonicRabiResonantReducedGenerator, meanFieldJacobianMatrix,
      Matrix.mul_apply, Fin.sum_univ_four]
  all_goals rw [← mul_assoc, Complex.I_mul_I]
  all_goals ring

/-- The resonant mean-field amplitude generator is nontrivially square-zero. -/
theorem photonicRabiResonantAmplitudeGenerator_sq (r : ℂ) :
    photonicRabiResonantAmplitudeGenerator r * photonicRabiResonantAmplitudeGenerator r = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicRabiResonantAmplitudeGenerator, meanFieldJacobianMatrix,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem photonicRabiResonantAmplitudeFlow_zero (r : ℂ) :
    photonicRabiResonantAmplitudeFlow r 0 = 1 := by
  simp [photonicRabiResonantAmplitudeFlow]

/-- The finite-time resonant amplitude flow is an exact one-parameter flow. -/
theorem photonicRabiResonantAmplitudeFlow_add (r : ℂ) (s t : ℝ) :
    photonicRabiResonantAmplitudeFlow r (s + t) =
      photonicRabiResonantAmplitudeFlow r s * photonicRabiResonantAmplitudeFlow r t := by
  have hzero :
      ((s : ℂ) • photonicRabiResonantAmplitudeGenerator r) *
        ((t : ℂ) • photonicRabiResonantAmplitudeGenerator r) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      photonicRabiResonantAmplitudeGenerator_sq, smul_zero]
  unfold photonicRabiResonantAmplitudeFlow
  push_cast
  rw [add_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hzero,
    add_zero]
  ac_rfl

/-- The exact mean-field amplitude flow reduces to the two-channel amplitude flow. -/
theorem photonicRabiResonantAmplitudeFlow_chain (r : ℂ) (t : ℝ) :
    photonicRabiResonantAmplitudeFlow r t * photonicRabiResonantAmplitudeChain =
      photonicRabiResonantAmplitudeChain *
        (1 + (t : ℂ) • photonicRabiResonantReducedGenerator r) := by
  calc
    photonicRabiResonantAmplitudeFlow r t * photonicRabiResonantAmplitudeChain =
        1 * photonicRabiResonantAmplitudeChain +
          ((t : ℂ) • photonicRabiResonantAmplitudeGenerator r) *
            photonicRabiResonantAmplitudeChain :=
      Matrix.add_mul _ _ _
    _ = photonicRabiResonantAmplitudeChain +
        (t : ℂ) •
          (photonicRabiResonantAmplitudeGenerator r * photonicRabiResonantAmplitudeChain) := by
      rw [Matrix.one_mul, Matrix.smul_mul]
    _ = photonicRabiResonantAmplitudeChain +
        (t : ℂ) •
          (photonicRabiResonantAmplitudeChain * photonicRabiResonantReducedGenerator r) := by
      rw [photonicRabiResonantAmplitudeGenerator_chain]
    _ = photonicRabiResonantAmplitudeChain * (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        photonicRabiResonantAmplitudeChain *
          ((t : ℂ) • photonicRabiResonantReducedGenerator r) := by
      rw [Matrix.mul_one, Matrix.mul_smul]
    _ = photonicRabiResonantAmplitudeChain *
        (1 + (t : ℂ) • photonicRabiResonantReducedGenerator r) :=
      (Matrix.mul_add _ _ _).symm

/-- Prime-rate resonant mean-field amplitude generator. -/
noncomputable def photonicPrimeRabiResonantAmplitudeGenerator (p : Nat.Primes) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  meanFieldJacobianMatrix 0 0 (photonicPrimeConstitutiveHarmonic p) 0

/-- The prime mean-field generator uses exactly the calibrated constitutive harmonic. -/
theorem photonicPrimeRabiResonantAmplitudeGenerator_eq_generic (p : Nat.Primes) :
    photonicPrimeRabiResonantAmplitudeGenerator p =
      photonicRabiResonantAmplitudeGenerator (photonicPrimeDriveRate p : ℂ) := by
  rw [photonicPrimeRabiResonantAmplitudeGenerator,
    photonicRabiResonantAmplitudeGenerator,
    photonicPrimeConstitutiveHarmonic_eq_resonantCoupling]

/-- The real physical duration which turns the prime-rate amplitude generator parabolic. -/
noncomputable def photonicPrimeRabiResonantAmplitudeDuration (p : Nat.Primes) : ℝ :=
  (photonicPrimeDriveRate p)⁻¹

/-- Exact prime-rate finite-time propagator of the literal mean-field amplitude equation. -/
noncomputable def photonicPrimeRabiResonantAmplitudePropagator (p : Nat.Primes) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  1 + ((photonicPrimeRabiResonantAmplitudeDuration p : ℝ) : ℂ) •
    photonicPrimeRabiResonantAmplitudeGenerator p

/--
The literal prime-rate mean-field amplitude propagator is exactly the PTR
parabolic transfer on its invariant two-channel amplitude chain.
-/
theorem photonicPrimeRabiResonantAmplitudePropagator_intertwines (p : Nat.Primes) :
    photonicPrimeRabiResonantAmplitudePropagator p * photonicRabiResonantAmplitudeChain =
      photonicRabiResonantAmplitudeChain * photonicParabolic := by
  have htime :
      ((photonicPrimeRabiResonantAmplitudeDuration p : ℝ) : ℂ) *
          (photonicPrimeDriveRate p : ℂ) = 1 := by
    simpa [photonicPrimeRabiResonantAmplitudeDuration] using
      congrArg (fun x : ℝ => (x : ℂ))
        (inv_mul_cancel₀ (photonicPrimeDriveRate_ne_zero p))
  have hreduced :
      1 + ((photonicPrimeRabiResonantAmplitudeDuration p : ℝ) : ℂ) •
          photonicRabiResonantReducedGenerator (photonicPrimeDriveRate p : ℂ) =
        photonicParabolic := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [photonicRabiResonantReducedGenerator, photonicParabolic, photonicUpper]
    · simpa [photonicRabiResonantReducedGenerator, photonicParabolic, photonicUpper] using htime
    · simp [photonicRabiResonantReducedGenerator, photonicParabolic, photonicUpper]
    · simp [photonicRabiResonantReducedGenerator, photonicParabolic, photonicUpper]
  unfold photonicPrimeRabiResonantAmplitudePropagator
  rw [photonicPrimeRabiResonantAmplitudeGenerator_eq_generic]
  change photonicRabiResonantAmplitudeFlow (photonicPrimeDriveRate p : ℂ)
      (photonicPrimeRabiResonantAmplitudeDuration p) *
        photonicRabiResonantAmplitudeChain =
      photonicRabiResonantAmplitudeChain * photonicParabolic
  rw [photonicRabiResonantAmplitudeFlow_chain, hreduced]

/-! ### Principal-Bragg PTC envelope calibration -/

/--
Linear principal-Bragg envelope generator for a scalar temporally modulated
Maxwell PTC.  Its two off-diagonal coefficients are the published
principal-gap coefficients `c₁,c₂`; this definition records that normal form
exactly, without claiming that an envelope truncation is a full-Maxwell
identity.
-/
noncomputable def photonicPrincipalBraggEnvelopeGenerator (a Δ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, ((1 / 2 * ((1 + Δ / 2) * a - 1) : ℝ) : ℂ);
     ((1 / 2 * (1 - (1 - Δ / 2) * a) : ℝ) : ℂ), 0]

/--
At the upper principal-Bragg edge, the scalar PTC envelope has precisely the
square-zero cyclic-Peierls normal form.  This is the exact algebraic survivor
of the Maxwell-envelope attack: remaining work is a nonperturbative modal
reduction for the rotating-cylinder PTC, not identification of its target
normal form.
-/
theorem photonicPrincipalBraggEnvelopeGenerator_upperEdge_eq_reduced
    (r : ℝ) (hr : r ≠ -1) :
    photonicPrincipalBraggEnvelopeGenerator (1 + r) (2 * r / (1 + r)) =
      photonicRabiResonantReducedGenerator (r : ℂ) := by
  have hdenR : 1 + r ≠ 0 := by
    intro h
    apply hr
    linarith
  have hden : 1 + (r : ℂ) ≠ 0 := by
    exact_mod_cast hdenR
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicPrincipalBraggEnvelopeGenerator,
      photonicRabiResonantReducedGenerator]
  all_goals field_simp [hden]
  all_goals ring

/-- Prime-indexed upper-edge Mathieu parameters forced by the PTR drive rate. -/
noncomputable def photonicPrimePrincipalBraggParameter (p : Nat.Primes) : ℝ :=
  1 + photonicPrimeDriveRate p

noncomputable def photonicPrimePrincipalBraggDepth (p : Nat.Primes) : ℝ :=
  2 * photonicPrimeDriveRate p / (1 + photonicPrimeDriveRate p)

/-- The prime calibration is physically positive and stays below the singular depth `2`. -/
theorem photonicPrimePrincipalBraggDepth_mem (p : Nat.Primes) :
    0 < photonicPrimePrincipalBraggDepth p ∧
      photonicPrimePrincipalBraggDepth p < 2 := by
  unfold photonicPrimePrincipalBraggDepth
  have hr := photonicPrimeDriveRate_pos p
  constructor
  · positivity
  · rw [div_lt_iff₀]
    · nlinarith
    · positivity

/--
The prime-dependent principal-Bragg PTC envelope is exactly the reduced
resonant cyclic-Peierls generator already realized inside the Rabi/BdG chain.
-/
theorem photonicPrimePrincipalBraggEnvelopeGenerator_eq_reduced (p : Nat.Primes) :
    photonicPrincipalBraggEnvelopeGenerator
        (photonicPrimePrincipalBraggParameter p)
        (photonicPrimePrincipalBraggDepth p) =
      photonicRabiResonantReducedGenerator (photonicPrimeDriveRate p : ℂ) := by
  unfold photonicPrimePrincipalBraggParameter photonicPrimePrincipalBraggDepth
  exact photonicPrincipalBraggEnvelopeGenerator_upperEdge_eq_reduced _
    (by linarith [photonicPrimeDriveRate_pos p])

/-- Exact nilpotence of the calibrated principal-Bragg envelope generator. -/
theorem photonicPrimePrincipalBraggEnvelopeGenerator_sq (p : Nat.Primes) :
    photonicPrincipalBraggEnvelopeGenerator
        (photonicPrimePrincipalBraggParameter p)
        (photonicPrimePrincipalBraggDepth p) *
      photonicPrincipalBraggEnvelopeGenerator
        (photonicPrimePrincipalBraggParameter p)
        (photonicPrimePrincipalBraggDepth p) = 0 := by
  rw [photonicPrimePrincipalBraggEnvelopeGenerator_eq_reduced]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicRabiResonantReducedGenerator, Matrix.mul_apply,
      Fin.sum_univ_two]

/--
One reciprocal-prime-rate envelope interval is exactly the PTR parabolic
transfer.  This discharges the normal-form match from principal-Bragg PTC
envelope data to the cyclic-Peierls transfer; it does not discharge the
full-Maxwell reduction of the rotating-cylinder geometry.
-/
theorem photonicPrimePrincipalBraggEnvelope_propagator_eq_parabolic
    (p : Nat.Primes) :
    1 + ((photonicPrimeDriveRate p)⁻¹ : ℂ) •
      photonicPrincipalBraggEnvelopeGenerator
        (photonicPrimePrincipalBraggParameter p)
        (photonicPrimePrincipalBraggDepth p) = photonicParabolic := by
  rw [photonicPrimePrincipalBraggEnvelopeGenerator_eq_reduced]
  have hrate : ((photonicPrimeDriveRate p)⁻¹ : ℂ) *
      (photonicPrimeDriveRate p : ℂ) = 1 := by
    simpa using congrArg (fun x : ℝ => (x : ℂ))
      (inv_mul_cancel₀ (photonicPrimeDriveRate_ne_zero p))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicRabiResonantReducedGenerator, photonicParabolic,
      photonicUpper]
  · exact hrate

/-! ### Exact finite-Floquet-truncation obstruction -/

/--
An upper Floquet step with amplitude `coupling n` preserves a finite channel
truncation only when its upper escaping boundary channel is dark.  This is the
minimal exactness condition behind any finite Floquet model; a numerical
truncation need not satisfy it.
-/
def PhotonicFloquetPositiveStepInvariant (coupling : ℤ → ℂ)
    (channels : Finset ℤ) : Prop :=
  ∀ n : ℤ, n ∈ channels → n + 1 ∉ channels → coupling n = 0

/-- Every nonempty finite Floquet channel set has an upper unit-shift escape. -/
theorem photonicFiniteFloquetTruncation_exists_upper_escape
    (channels : Finset ℤ) (hchannels : channels.Nonempty) :
    ∃ n : ℤ, n ∈ channels ∧ n + 1 ∉ channels := by
  classical
  refine ⟨channels.max' hchannels, Finset.max'_mem _ _, ?_⟩
  intro hnext
  have hle : channels.max' hchannels + 1 ≤ channels.max' hchannels :=
    Finset.le_max' channels _ hnext
  exact (not_le_of_gt (lt_add_one (channels.max' hchannels))) hle

/--
Thus every finite exact positive-step Floquet truncation has a dark upper
boundary channel.  The theorem does not assume a modal-overlap formula; it
isolates non-vanishing of that formula as the remaining physical obligation.
-/
theorem photonicFiniteFloquetTruncation_has_dark_upper_boundary
    (coupling : ℤ → ℂ) (channels : Finset ℤ) (hchannels : channels.Nonempty)
    (hinvariant : PhotonicFloquetPositiveStepInvariant coupling channels) :
    ∃ n : ℤ, n ∈ channels ∧ n + 1 ∉ channels ∧ coupling n = 0 := by
  obtain ⟨n, hn, hnext⟩ :=
    photonicFiniteFloquetTruncation_exists_upper_escape channels hchannels
  exact ⟨n, hn, hnext, hinvariant n hn hnext⟩

/--
No nonempty finite Floquet truncation can be exact for a nonvanishing upper
sideband coupling on all retained channels.  Consequently, the finite-channel
Floquet calculation in the rotating-PTC source cannot be promoted to a literal
closed amplitude model unless it proves a boundary-dark-mode law.
-/
theorem not_photonicFiniteFloquetTruncation_positiveStepInvariant_of_nonzero
    (coupling : ℤ → ℂ) (channels : Finset ℤ) (hchannels : channels.Nonempty)
    (hnonzero : ∀ n : ℤ, n ∈ channels → coupling n ≠ 0) :
    ¬ PhotonicFloquetPositiveStepInvariant coupling channels := by
  intro hinvariant
  obtain ⟨n, hn, hnext, hzero⟩ :=
    photonicFiniteFloquetTruncation_has_dark_upper_boundary coupling channels hchannels hinvariant
  exact hnonzero n hn hzero

/--
The literal positive prime material harmonic, viewed as the bare one-step
Floquet coupling.  This deliberately precedes any modal-overlap projection.
-/
noncomputable def photonicPrimeBareFloquetPositiveCoupling
    (p : Nat.Primes) (_ : ℤ) : ℂ :=
  photonicPrimeConstitutiveHarmonic p

/-- Every channel has nonzero bare positive-helical prime coupling. -/
theorem photonicPrimeBareFloquetPositiveCoupling_ne_zero
    (p : Nat.Primes) (n : ℤ) : photonicPrimeBareFloquetPositiveCoupling p n ≠ 0 := by
  exact photonicPrimeConstitutiveHarmonic_ne_zero p

/--
The literal nonzero prime material harmonic admits no nonempty finite closed
Floquet truncation.  Hence a finite exact realization must not identify its
modal coupling with the bare constitutive coefficient: it needs either an
infinite sideband ladder or a proved boundary-dark-mode overlap law.
-/
theorem not_photonicPrimeBareFloquetPositiveCoupling_finiteInvariant
    (p : Nat.Primes) (channels : Finset ℤ) (hchannels : channels.Nonempty) :
    ¬ PhotonicFloquetPositiveStepInvariant
      (photonicPrimeBareFloquetPositiveCoupling p) channels := by
  apply not_photonicFiniteFloquetTruncation_positiveStepInvariant_of_nonzero
    _ channels hchannels
  intro n hn
  exact photonicPrimeBareFloquetPositiveCoupling_ne_zero p n

/-! ### Complex-PTC half-density conormal bridge -/

/--
Prime-calibrated complex-PTC Floquet multiplier.  Its period is `log p`; its
phase and gain coordinates are the imaginary and real parts of `s`,
respectively.  This is an exact multiplier dictionary, not a claim that the
rotating-cylinder Maxwell amplitudes have already been derived.
-/
noncomputable def photonicPrimePCMHalfDensityMultiplier
    (p : Nat.Primes) (s : ℂ) : ℂ :=
  pcmFloquetMultiplier (s.im * Real.log ((p : ℕ) : ℝ))
    ((1 / 2 : ℝ) - s.re) (Real.log ((p : ℕ) : ℝ))

/--
The prime-calibrated complex PTC multiplier is exactly the bilateral
half-density character `p^(1/2-s)`.  Thus its gain, not only its phase, carries
the off-critical-line coordinate required by the moderation selector.
-/
theorem photonicPrimePCMHalfDensityMultiplier_eq_bilateralHalfDensityCharacter
    (p : Nat.Primes) (s : ℂ) :
    photonicPrimePCMHalfDensityMultiplier p s =
      bilateralHalfDensityCharacter (p : ℕ) s := by
  rw [photonicPrimePCMHalfDensityMultiplier, pcmFloquetMultiplier,
    pcmFloquetQuasifrequencyPeriod, bilateralHalfDensityCharacter]
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (by exact_mod_cast p.property.pos : (0 : ℝ) < ((p : ℕ) : ℝ))
  rw [Complex.cpow_def_of_ne_zero hp0]
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  rw [← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ ((p : ℕ) : ℝ))]
  congr 1
  push_cast
  rw [← Complex.re_add_im s]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- Canonical infinite PTC sideband conormal family. -/
noncomputable def photonicPrimePCMConormalSideband
    (p : Nat.Primes) (s : ℂ) (e : ℤ) : ℂ :=
  photonicPrimePCMHalfDensityMultiplier p s ^ (-e)

/-- The complex-PTC conormal sidebands are the corpus's canonical eigenfamily. -/
theorem photonicPrimePCMConormalSideband_eq_bilateralEigenFamily
    (p : Nat.Primes) (s : ℂ) :
    photonicPrimePCMConormalSideband p s =
      bilateralEigenFamily (bilateralHalfDensityCharacter (p : ℕ) s) := by
  funext e
  rw [photonicPrimePCMConormalSideband,
    photonicPrimePCMHalfDensityMultiplier_eq_bilateralHalfDensityCharacter]
  rfl

/-- The canonical complex-PTC conormal family is nonzero. -/
theorem photonicPrimePCMConormalSideband_ne_zero
    (p : Nat.Primes) (s : ℂ) : photonicPrimePCMConormalSideband p s ≠ 0 := by
  rw [photonicPrimePCMConormalSideband_eq_bilateralEigenFamily]
  exact bilateralEigenFamily_ne_zero _

/-- The canonical infinite PTC sidebands satisfy the exact bilateral sewing recursion. -/
theorem photonicPrimePCMConormalSideband_sewing
    (p : Nat.Primes) (s : ℂ) (e : ℤ) :
    photonicPrimePCMConormalSideband p s (e - 1) =
      photonicPrimePCMHalfDensityMultiplier p s *
        photonicPrimePCMConormalSideband p s e := by
  rw [photonicPrimePCMConormalSideband_eq_bilateralEigenFamily,
    photonicPrimePCMHalfDensityMultiplier_eq_bilateralHalfDensityCharacter]
  exact bilateralEigenFamily_sewing
    (bilateralHalfDensityCharacter_ne_zero p.property.pos _) e

/--
Moderation of the canonical infinite complex-PTC sideband family is exactly
critical-line rigidity.  This is a closed physical-multiplier criterion, with
no zeta-zero or Maxwell-amplitude premise.
-/
theorem bilateralModerate_photonicPrimePCMConormalSideband_iff_re_eq_half
    (p : Nat.Primes) (s : ℂ) :
    bilateralModerate (photonicPrimePCMConormalSideband p s) ↔ s.re = 1 / 2 := by
  constructor
  · intro hmod
    apply re_eq_half_of_moderate_bilateral_eigen p.property.two_le
      (photonicPrimePCMConormalSideband_ne_zero p s) hmod
    intro e
    rw [photonicPrimePCMConormalSideband_sewing,
      photonicPrimePCMHalfDensityMultiplier_eq_bilateralHalfDensityCharacter]
  · intro hre
    rw [photonicPrimePCMConormalSideband_eq_bilateralEigenFamily]
    apply bilateralModerate_eigenFamily_of_norm_eq_one
    exact (norm_bilateralHalfDensityCharacter_eq_one_iff p.property.two_le s).mpr hre

/--
RH is equivalent to moderation of the canonical complex-PTC conormal ladder at
every actual Xi divisor copy.  The remaining PTR physical theorem is therefore
precise: derive this infinite conormal ladder from a literal Maxwell source.
-/
theorem riemannHypothesis_iff_forall_xiZero_photonicPrimePCMConormalSidebandModerate
    (p : Nat.Primes) :
    (∀ q : XiZeroCopy, bilateralModerate
      (photonicPrimePCMConormalSideband p (deningerDivisorThetaEigen q))) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (riemannHypothesis_iff_forall_xiZero_exists_moderate_eigen
      p.property.two_le).mp
    intro q
    exact ⟨photonicPrimePCMConormalSideband p (deningerDivisorThetaEigen q),
      photonicPrimePCMConormalSideband_ne_zero p _, h q,
      by
        intro e
        rw [photonicPrimePCMConormalSideband_sewing,
          photonicPrimePCMHalfDensityMultiplier_eq_bilateralHalfDensityCharacter]⟩
  · intro hRH q
    apply (bilateralModerate_photonicPrimePCMConormalSideband_iff_re_eq_half p _).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

/--
The multiplier of one fixed complex-PTC device: its material gain `b` does not
vary with a divisor copy.  The phase remains spectrally resolved.  A literal
Maxwell realization must establish this fixed-device law rather than tune the
gain separately at each zero.
-/
noncomputable def photonicPrimePCMFixedGainMultiplier
    (p : Nat.Primes) (b : ℝ) (s : ℂ) : ℂ :=
  pcmFloquetMultiplier (s.im * Real.log ((p : ℕ) : ℝ)) b
    (Real.log ((p : ℕ) : ℝ))

/--
Exact matching of a fixed-gain PCM multiplier to a half-density character fixes
the gain to the character's real coordinate.  This uses no Xi-zero premise.
-/
theorem photonicPrimePCMFixedGainMultiplier_eq_halfDensity_gain
    (p : Nat.Primes) (b : ℝ) (s : ℂ)
    (h : photonicPrimePCMFixedGainMultiplier p b s =
      bilateralHalfDensityCharacter (p : ℕ) s) :
    b = (1 / 2 : ℝ) - s.re := by
  have hnorm :
      Real.exp (b * Real.log ((p : ℕ) : ℝ)) =
        Real.exp (((1 / 2 : ℝ) - s.re) * Real.log ((p : ℕ) : ℝ)) := by
    calc
      Real.exp (b * Real.log ((p : ℕ) : ℝ)) =
          ‖photonicPrimePCMFixedGainMultiplier p b s‖ := by
        rw [photonicPrimePCMFixedGainMultiplier, norm_pcmFloquetMultiplier]
      _ = ‖bilateralHalfDensityCharacter (p : ℕ) s‖ := congrArg norm h
      _ = ‖photonicPrimePCMHalfDensityMultiplier p s‖ := by
        rw [photonicPrimePCMHalfDensityMultiplier_eq_bilateralHalfDensityCharacter]
      _ = Real.exp (((1 / 2 : ℝ) - s.re) * Real.log ((p : ℕ) : ℝ)) := by
        rw [photonicPrimePCMHalfDensityMultiplier, norm_pcmFloquetMultiplier]
  have harg : b * Real.log ((p : ℕ) : ℝ) =
      ((1 / 2 : ℝ) - s.re) * Real.log ((p : ℕ) : ℝ) :=
    Real.exp_injective hnorm
  have hlog : Real.log ((p : ℕ) : ℝ) ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast p.property.pos : 0 < ((p : ℕ) : ℝ))
      (by exact_mod_cast p.property.ne_one : ((p : ℕ) : ℝ) ≠ 1)
  exact (mul_right_cancel₀ hlog) (by simpa [mul_sub] using harg)

/--
**Fixed-device PCM rigidity.** RH is equivalent to the existence of one
prime-calibrated PCM gain whose multiplier matches the half-density character
on every actual Xi divisor copy.  Functional-equation reflection forces this
single gain to be zero; hence a literal physical proof need only derive one
fixed-device amplitude law, not a zero-dependent gain calibration.
-/
theorem riemannHypothesis_iff_exists_photonicPrimePCMFixedGain_match
    (p : Nat.Primes) :
    RiemannHypothesis ↔ ∃ b : ℝ, ∀ q : XiZeroCopy,
      photonicPrimePCMFixedGainMultiplier p b (deningerDivisorThetaEigen q) =
        bilateralHalfDensityCharacter (p : ℕ) (deningerDivisorThetaEigen q) := by
  constructor
  · intro hRH
    refine ⟨0, ?_⟩
    intro q
    rw [← photonicPrimePCMHalfDensityMultiplier_eq_bilateralHalfDensityCharacter]
    have hre := xi_divisor_support_re_eq_half_of_rh hRH q.1
    unfold photonicPrimePCMFixedGainMultiplier
      photonicPrimePCMHalfDensityMultiplier
    congr 2
    change 0 = (1 / 2 : ℝ) - (q.1 : ℂ).re
    rw [hre]
    exact (sub_self (1 / 2 : ℝ)).symm
  · rintro ⟨b, hb⟩
    apply (riemannHypothesis_iff_forall_xiZero_exists_moderate_eigen
      p.property.two_le).mp
    intro q
    have hq := photonicPrimePCMFixedGainMultiplier_eq_halfDensity_gain p b
      (deningerDivisorThetaEigen q) (hb q)
    have hreflect := photonicPrimePCMFixedGainMultiplier_eq_halfDensity_gain p b
      (deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q))
      (hb (xiZeroCopyReflectEquiv q))
    have hsum := congrArg Complex.re (deningerDivisorThetaEigen_add_reflect q)
    have hre : (deningerDivisorThetaEigen q).re = 1 / 2 := by
      simp only [Complex.add_re, Complex.one_re] at hsum
      linarith
    refine ⟨photonicPrimePCMConormalSideband p (deningerDivisorThetaEigen q),
      photonicPrimePCMConormalSideband_ne_zero p _, ?_, ?_⟩
    · exact (bilateralModerate_photonicPrimePCMConormalSideband_iff_re_eq_half p _).mpr hre
    · intro e
      rw [photonicPrimePCMConormalSideband_sewing,
        photonicPrimePCMHalfDensityMultiplier_eq_bilateralHalfDensityCharacter]

/-- Prime drive rate times its physical slab duration is the exact rational phase. -/
theorem photonicPrimeDriveRate_mul_slabDuration (p : Nat.Primes) :
    photonicPrimeDriveRate p * photonicPrimeSlabDuration p = photonicRationalSlabPhase := by
  rw [photonicPrimeSlabDuration, mul_div_cancel₀ _ (photonicPrimeDriveRate_ne_zero p)]

/-- The driven prime cell is exactly the coupled cyclic slab cell. -/
theorem photonicPrimeCyclicTimeCrystalCell_eq_slabCell (p : Nat.Primes) :
    photonicPrimeCyclicTimeCrystalCell p = photonicPrimeCyclicSlabCell p := by
  unfold photonicPrimeCyclicTimeCrystalCell photonicDrivenOscillatorFlow
  rw [photonicPrimeDriveRate_mul_slabDuration]
  rw [← photonicOscillatorSlab_eq_flow]
  rw [← photonicOscillatorSlab_eq_flow]
  rfl

/-- The explicit nilpotent part of the square of the prime-driven cyclic cell. -/
noncomputable def photonicPrimeDrivenNilpotent (p : Nat.Primes) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(12 / 5), -(6 / 5) / photonicPrimeImpedance p;
    (24 / 5) * photonicPrimeImpedance p, 12 / 5]

theorem photonicPrimeCyclicSlabCell_sq_eq_one_add_nilpotent (p : Nat.Primes) :
    photonicPrimeCyclicSlabCell p * photonicPrimeCyclicSlabCell p =
      1 + photonicPrimeDrivenNilpotent p := by
  have hp := photonicPrimeImpedance_ne_zero p
  simp only [photonicPrimeCyclicSlabCell, photonicOscillatorSlab,
    photonicPrimeDrivenNilpotent, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> simp <;>
    field_simp [hp] <;> ring

theorem photonicPrimeDrivenNilpotent_sq (p : Nat.Primes) :
    photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent p = 0 := by
  have hp := photonicPrimeImpedance_ne_zero p
  simp only [photonicPrimeDrivenNilpotent, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> field_simp [hp] <;> ring

theorem photonicPrimeDrivenNilpotent_ne_zero (p : Nat.Primes) :
    photonicPrimeDrivenNilpotent p ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  norm_num [photonicPrimeDrivenNilpotent] at hentry

/--
No positive-definite metric is invariant under the literal prime cyclic slab
cell.  A physical realization must therefore retain the PTR's indefinite flux
or use gain/loss; a passive positive-energy source is closed.
-/
theorem not_photonicPrimeCyclicSlabCell_positive_metric
    (p : Nat.Primes) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hQ : GaloisForLFunctions.HTGeometry.IsPositiveDefiniteMetric Q) :
    (photonicPrimeCyclicSlabCell p)ᴴ * Q * photonicPrimeCyclicSlabCell p ≠ Q := by
  exact GaloisForLFunctions.HTGeometry.not_conjTranspose_mul_mul_eq_of_mul_self_unipotent
    (photonicPrimeDrivenNilpotent_sq p)
    (photonicPrimeDrivenNilpotent_ne_zero p)
    (photonicPrimeCyclicSlabCell_sq_eq_one_add_nilpotent p) hQ

/-- The unscaled first slab is the first literal slab of `photonicBinaryCell`. -/
theorem photonicOscillatorSlab_one_eq :
    photonicOscillatorSlab 1 = !![3 / 5, 4 / 5; -4 / 5, 3 / 5] := by
  norm_num [photonicOscillatorSlab]

/-- The unscaled second slab is the second literal slab of `photonicBinaryCell`. -/
theorem photonicOscillatorSlab_four_eq :
    photonicOscillatorSlab 4 = !![3 / 5, 1 / 5; -16 / 5, 3 / 5] := by
  norm_num [photonicOscillatorSlab]

theorem photonicPrimeFrame_mul_inv (p : Nat.Primes) :
    photonicPrimeFrame p * photonicPrimeFrameInv p = 1 := by
  have hp := photonicPrimeImpedance_ne_zero p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicPrimeFrame, photonicPrimeFrameInv, hp]

theorem photonicPrimeFrameInv_mul (p : Nat.Primes) :
    photonicPrimeFrameInv p * photonicPrimeFrame p = 1 := by
  have hp := photonicPrimeImpedance_ne_zero p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [photonicPrimeFrame, photonicPrimeFrameInv, hp]

/-- The prime cyclic cell is exactly the prime-frame conjugate of the binary slab cell. -/
theorem photonicPrimeCyclicSlabCell_eq_conjugated_binary (p : Nat.Primes) :
    photonicPrimeCyclicSlabCell p =
      photonicPrimeFrame p * photonicBinaryCell * photonicPrimeFrameInv p := by
  have hp := photonicPrimeImpedance_ne_zero p
  simp only [photonicPrimeCyclicSlabCell, photonicOscillatorSlab,
    photonicPrimeFrame, photonicPrimeFrameInv, photonicBinaryCell, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> field_simp [hp] <;> ring

/-- Concrete nonzero coupling coefficient of the prime cyclic cell. -/
theorem photonicPrimeCyclicSlabCell_offdiag_eq (p : Nat.Primes) :
    photonicPrimeCyclicSlabCell p 0 1 =
      3 / (5 * photonicPrimeImpedance p) := by
  have hp := photonicPrimeImpedance_ne_zero p
  simp only [photonicPrimeCyclicSlabCell, photonicOscillatorSlab, Matrix.mul_fin_two]
  dsimp
  field_simp [hp]
  ring

theorem photonicPrimeCyclicSlabCell_offdiag_ne_zero (p : Nat.Primes) :
    photonicPrimeCyclicSlabCell p 0 1 ≠ 0 := by
  rw [photonicPrimeCyclicSlabCell_offdiag_eq]
  have hp := photonicPrimeImpedance_ne_zero p
  exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hp)

/-- Each prime cyclic cell is genuinely non-scalar and hence two-channel coupled. -/
theorem photonicPrimeCyclicSlabCell_ne_scalar (p : Nat.Primes) (μ : ℂ) :
    photonicPrimeCyclicSlabCell p ≠ Matrix.scalar (Fin 2) μ := by
  intro h
  have hentry := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  have hzero : photonicPrimeCyclicSlabCell p 0 1 = 0 := by
    simpa [Matrix.scalar] using hentry
  exact photonicPrimeCyclicSlabCell_offdiag_ne_zero p hzero

/--
After two literal prime-impedance slab cycles, the transfer is exactly the PTR
parabolic cell in its forced prime-dependent frame.
-/
theorem photonicPrimeCyclicSlabCell_square_intertwines (p : Nat.Primes) :
    photonicPrimeCyclicSlabCell p ^ 2 *
        (photonicPrimeFrame p * photonicParabolicBasis) =
      (photonicPrimeFrame p * photonicParabolicBasis) * photonicParabolic := by
  have hp := photonicPrimeImpedance_ne_zero p
  simp only [photonicPrimeCyclicSlabCell, photonicOscillatorSlab,
    photonicPrimeFrame, photonicParabolicBasis, photonicParabolic,
    photonicUpper, Matrix.mul_fin_two, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> field_simp [hp] <;> ring

/-- The literal prime-driven two-slab cell has the PTR parabolic transfer after two cycles. -/
theorem photonicPrimeCyclicTimeCrystalCell_square_intertwines (p : Nat.Primes) :
    photonicPrimeCyclicTimeCrystalCell p ^ 2 *
        (photonicPrimeFrame p * photonicParabolicBasis) =
      (photonicPrimeFrame p * photonicParabolicBasis) * photonicParabolic := by
  rw [photonicPrimeCyclicTimeCrystalCell_eq_slabCell]
  exact photonicPrimeCyclicSlabCell_square_intertwines p

/-- The literal prime-driven cell is not passive for any positive energy metric. -/
theorem not_photonicPrimeCyclicTimeCrystalCell_positive_metric
    (p : Nat.Primes) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hQ : GaloisForLFunctions.HTGeometry.IsPositiveDefiniteMetric Q) :
    (photonicPrimeCyclicTimeCrystalCell p)ᴴ * Q * photonicPrimeCyclicTimeCrystalCell p ≠ Q := by
  rw [photonicPrimeCyclicTimeCrystalCell_eq_slabCell]
  exact not_photonicPrimeCyclicSlabCell_positive_metric p Q hQ

end RHTower
