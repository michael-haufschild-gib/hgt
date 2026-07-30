import GaloisForLFunctions.HTGeometry.CayleyPoleResidueTransport
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.XiCayleyWardDynamicalVisibility
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.RHTower.XiHurwitzPrincipalPhaseGrowth
import GaloisForLFunctions.RHTower.XiThermalProjectiveFreeEnergyRadius

/-!
# Source--Cayley order-space conservation for the Riemann divisor

Multiply the completed Riemann logarithmic response by

```text
exp (x / (s - 1))
```

before extracting a zero residue.  A zero `rho` of arbitrary multiplicity
is transported into the coherent mode

```text
m(rho) * exp (x / (rho - 1)).
```

Its evolution derivatives form an exact Poisson packet in derivative-order
space.  The packet drift and exponential rate are

```text
d(rho)     = |rho - 1|⁻²,
kappa(rho) = (2 Re rho - 1) d(rho).
```

They reconstruct `Re rho` and `Im rho` up to conjugation.  In particular,
every strict-right Xi zero has positive exponential rate.  Multiplicity
normalization identifies these arithmetic residue jets with the
endpoint-Ward-weighted Cayley coherent jets.  An adjacent-order exterior
determinant removes the rotating conjugate phase without losing the
Poisson packet, its strict sign, or its complete exponential mass.

The capstone theorem packages this source realization with the Hurwitz
phase chart, the projective zero-temperature chart, the Ward time-zero
mass, the exact height--order visibility bound, and the bounded-tower
criterion for RH.
-/

open Complex Filter Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Cayley evolution at the arithmetic source point `s = 1`. -/
def xiCayleyEvolutionKernel (x s : ℂ) : ℂ :=
  Complex.exp ((s - 1)⁻¹ * x)

/-- Completed logarithmic response after Cayley evolution and before
residue extraction. -/
def xiCayleyEvolvedLogDeriv (x s : ℂ) : ℂ :=
  logDeriv xi s * xiCayleyEvolutionKernel x s

/-- Multiplicity-weighted coherent mode transported from a Xi residue. -/
def xiCayleySourceResidueMode (rho x : ℂ) : ℂ :=
  ((analyticOrderAt xi rho).toNat : ℂ) *
    Complex.exp ((rho - 1)⁻¹ * x)

theorem continuousAt_xiCayleyEvolutionKernel
    (x : ℂ) {rho : ℂ} (hrho : rho ≠ 1) :
    ContinuousAt (xiCayleyEvolutionKernel x) rho := by
  unfold xiCayleyEvolutionKernel
  exact Complex.continuous_exp.continuousAt.comp
    (((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.mpr hrho)).mul continuousAt_const)

/-- The evolved completed response has the exact transported residue at
every point, with no simplicity assumption. -/
theorem xiCayleyEvolvedLogDeriv_residue_transport
    {rho : ℂ} (hrho : rho ≠ 1) (x : ℂ) :
    Tendsto
      (fun s : ℂ => (s - rho) * xiCayleyEvolvedLogDeriv x s)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (xiCayleySourceResidueMode rho x)) := by
  have hbase := xi_normalizedLogDeriv_tendsto_order rho
  have hkernel : Tendsto (xiCayleyEvolutionKernel x)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (xiCayleyEvolutionKernel x rho)) :=
    (continuousAt_xiCayleyEvolutionKernel x hrho).tendsto.mono_left
      nhdsWithin_le_nhds
  have hmul := hbase.mul hkernel
  simpa only [xiCayleyEvolvedLogDeriv, xiCayleySourceResidueMode,
    xiCayleyEvolutionKernel, mul_assoc] using hmul

/-- On the Euler half-plane the evolved response is explicitly the
prime--Gamma arithmetic source multiplied by the Cayley kernel. -/
theorem xiCayleyEvolvedLogDeriv_eq_arithmetic
    (x : ℂ) {s : ℂ} (hs : 1 < s.re) :
    xiCayleyEvolvedLogDeriv x s =
      (s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) *
          xiCayleyEvolutionKernel x s := by
  rw [xiCayleyEvolvedLogDeriv, logDeriv_xi_eq_arithmetic hs]

/-- All evolution derivatives of the Xi residue are exact coherent
exponential jets. -/
theorem iteratedDeriv_xiCayleySourceResidueMode
    (rho x : ℂ) (r : ℕ) :
    iteratedDeriv r (xiCayleySourceResidueMode rho) x =
      ((analyticOrderAt xi rho).toNat : ℂ) *
        (rho - 1)⁻¹ ^ r * Complex.exp ((rho - 1)⁻¹ * x) := by
  change iteratedDeriv r
    (fun x : ℂ => ((analyticOrderAt xi rho).toNat : ℂ) *
      Complex.exp ((rho - 1)⁻¹ * x)) x = _
  rw [iteratedDeriv_const_mul
    ((analyticOrderAt xi rho).toNat : ℂ)
    (by fun_prop :
      ContDiffAt ℂ r
        (fun x : ℂ => Complex.exp ((rho - 1)⁻¹ * x)) x)]
  rw [GaloisForLFunctions.iteratedDeriv_exp_linear]
  ring

/-- Coherent shift transported from one strict-right upper Xi zero. -/
def xiSourceCayleyShift (q : XiRightUpperZeroCopy) : ℂ :=
  ((q.1.1.1 : ℂ) - 1)⁻¹

/-- Order-space drift of one transported Xi residue. -/
def xiSourceCayleyDrift (q : XiRightUpperZeroCopy) : ℝ :=
  HTGeometry.cayleyFockDrift (xiSourceCayleyShift q)

/-- Exponential order-space rate of one transported Xi residue. -/
def xiSourceCayleyExponent (q : XiRightUpperZeroCopy) : ℝ :=
  HTGeometry.cayleyFockExponent (xiSourceCayleyShift q)

private theorem xiSourceCayley_rho_ne_one
    (q : XiRightUpperZeroCopy) :
    (q.1.1.1 : ℂ) ≠ 1 := by
  intro h
  exact xi_divisor_support_im_ne_zero q.1.1.1 (by simp [h])

/-- The source shift is exactly the coherent displacement obtained from
the inverse Li-Cayley node. -/
theorem xiSourceCayleyShift_eq_inverseLiShift
    (q : XiRightUpperZeroCopy) :
    xiSourceCayleyShift q = (xiWardLiCayleyNode q)⁻¹ - 1 := by
  rw [xiSourceCayleyShift, xiWardLiCayleyNode, wCoordinate]
  have hrho : (q.1.1.1 : ℂ) ≠ 0 := by
    intro h
    exact xi_divisor_support_im_ne_zero q.1.1.1 (by simp [h])
  field_simp [hrho, xiSourceCayley_rho_ne_one q]
  have hsub : (q.1.1.1 : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (xiSourceCayley_rho_ne_one q)
  field_simp [hsub]
  ring

/-- The source residue mode is the exact Poisson completion of the
inverse Li--Cayley orbit.  This identifies the continuous source
evolution with the factorial completion of the discrete Li dynamics. -/
theorem xiCayleySourceResidueMode_eq_poissonCompletedLiOrbit
    (q : XiRightUpperZeroCopy) (x : ℂ) :
    xiCayleySourceResidueMode (q.1.1.1 : ℂ) x =
      ((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ) *
        HTGeometry.poissonCompletedGeometricOrbit
          (xiWardLiCayleyNode q)⁻¹ x := by
  rw [xiCayleySourceResidueMode,
    HTGeometry.poissonCompletedGeometricOrbit_eq]
  change
    ((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ) *
        Complex.exp (xiSourceCayleyShift q * x) =
      ((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ) *
        Complex.exp (((xiWardLiCayleyNode q)⁻¹ - 1) * x)
  rw [xiSourceCayleyShift_eq_inverseLiShift]

/-- The packet drift is inverse squared distance to the arithmetic source
point. -/
theorem xiSourceCayleyDrift_eq (q : XiRightUpperZeroCopy) :
    xiSourceCayleyDrift q =
      (Complex.normSq ((q.1.1.1 : ℂ) - 1))⁻¹ := by
  rw [xiSourceCayleyDrift, xiSourceCayleyShift,
    HTGeometry.cayleyFockDrift_of_rho
      (xiSourceCayley_rho_ne_one q)]

/-- The packet rate is transverse displacement times packet drift. -/
theorem xiSourceCayleyExponent_eq (q : XiRightUpperZeroCopy) :
    xiSourceCayleyExponent q =
      (2 * (q.1.1.1 : ℂ).re - 1) *
        xiSourceCayleyDrift q := by
  rw [xiSourceCayleyExponent, xiSourceCayleyDrift,
    xiSourceCayleyShift,
    HTGeometry.cayleyFockExponent_of_rho
      (xiSourceCayley_rho_ne_one q)]

theorem xiSourceCayleyDrift_pos (q : XiRightUpperZeroCopy) :
    0 < xiSourceCayleyDrift q := by
  rw [xiSourceCayleyDrift, HTGeometry.cayleyFockDrift,
    xiSourceCayleyShift]
  exact sq_pos_of_pos
    (norm_pos_iff.mpr
      (inv_ne_zero
        (sub_ne_zero.mpr (xiSourceCayley_rho_ne_one q))))

/-- Every strict-right Xi zero is a strictly unstable transported source
residue. -/
theorem xiSourceCayleyExponent_pos (q : XiRightUpperZeroCopy) :
    0 < xiSourceCayleyExponent q := by
  rw [xiSourceCayleyExponent_eq]
  apply mul_pos
  · have h := xiRightCenteredZero_re_pos q.1
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at h
    simp only [Complex.sub_re] at h
    norm_num at h
    linarith
  · exact xiSourceCayleyDrift_pos q

/-- Packet drift and rate reconstruct the real part of the zero. -/
theorem xiSourceCayley_rho_re_reconstruction
    (q : XiRightUpperZeroCopy) :
    (q.1.1.1 : ℂ).re =
      1 / 2 * (1 +
        xiSourceCayleyExponent q / xiSourceCayleyDrift q) := by
  simpa only [xiSourceCayleyExponent, xiSourceCayleyDrift,
    xiSourceCayleyShift] using
      (HTGeometry.rho_re_from_cayleyFock_ridge
        (xiSourceCayley_rho_ne_one q))

/-- Packet drift and rate reconstruct the squared height of the zero. -/
theorem xiSourceCayley_rho_im_sq_reconstruction
    (q : XiRightUpperZeroCopy) :
    (q.1.1.1 : ℂ).im ^ 2 =
      1 / xiSourceCayleyDrift q -
        1 / 4 * (1 -
          xiSourceCayleyExponent q / xiSourceCayleyDrift q) ^ 2 := by
  simpa only [xiSourceCayleyExponent, xiSourceCayleyDrift,
    xiSourceCayleyShift] using
      (HTGeometry.rho_im_sq_from_cayleyFock_ridge
        (xiSourceCayley_rho_ne_one q))

/-- Multiplicity-normalized derivative jet transported from the source
residue. -/
def xiCayleyNormalizedSourceResidueJet
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) : ℂ :=
  (xiSourceCayleyShift q) ^ r *
    Complex.exp (xiSourceCayleyShift q * (x : ℂ))

/-- Endpoint-Ward-weighted transported residue jet. -/
def xiSourceCayleyWardCoherentJet
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) : ℂ :=
  HTGeometry.coherentExponentialJet
    (Real.sqrt (xiEndpointWardPairWeight q) : ℂ)
    (xiSourceCayleyShift q) x r

theorem xiCayleyWardCoherentJet_eq_sourceResidueJet
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    xiSourceCayleyWardCoherentJet q x r =
      (Real.sqrt (xiEndpointWardPairWeight q) : ℂ) *
        xiCayleyNormalizedSourceResidueJet q x r := by
  simp only [xiSourceCayleyWardCoherentJet,
    HTGeometry.coherentExponentialJet,
    xiCayleyNormalizedSourceResidueJet]
  ring

/-- The Ward coherent jet is an exact rescaling of the arithmetic residue
jet, with analytic multiplicity divided out. -/
theorem xiSourceCayleyWardCoherentJet_eq_scaled_residueMode_jet
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    xiSourceCayleyWardCoherentJet q x r =
      (Real.sqrt (xiEndpointWardPairWeight q) : ℂ) /
          ((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ) *
        iteratedDeriv r
          (xiCayleySourceResidueMode (q.1.1.1 : ℂ)) (x : ℂ) := by
  rw [iteratedDeriv_xiCayleySourceResidueMode]
  have hm :
      ((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr
      (xi_order_toNat_ne_zero
        (xi_eq_zero_of_mem_divisor_support q.1.1.1))
  simp only [xiSourceCayleyWardCoherentJet,
    HTGeometry.coherentExponentialJet, xiSourceCayleyShift]
  field_simp [hm]

/-- **Source-residue Poisson conservation.**  Every derivative-order
channel is an exact Poisson packet with total off-critical exponential
rate. -/
theorem xiSourceCayleyWardCoherentJet_poisson_conservation
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial *
        ‖xiSourceCayleyWardCoherentJet q x r‖ ^ 2 =
      xiEndpointWardPairWeight q *
        Real.exp (xiSourceCayleyExponent q * x) *
          HTGeometry.poissonOrderWeight
            (xiSourceCayleyDrift q * x) r := by
  rw [xiSourceCayleyWardCoherentJet,
    xiSourceCayleyExponent, xiSourceCayleyDrift,
    HTGeometry.coherentExponentialJet_poisson_conservation]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (xiEndpointWardPairWeight_pos q).le]

/-- **Parabolic conservation for an actual Xi divisor mode.**
Observation at inverse-drift time removes the zero height exactly from
both the packet location and its total exponential rate.  The surviving
rate is precisely the transverse displacement `2 Re rho - 1`. -/
theorem xiCayleySourceResidueMode_parabolic_conservation
    (q : XiRightUpperZeroCopy) (tau : ℝ) (r : ℕ) :
    let x := tau / xiSourceCayleyDrift q
    x ^ r / r.factorial *
        ‖iteratedDeriv r
          (xiCayleySourceResidueMode (q.1.1.1 : ℂ)) (x : ℂ)‖ ^ 2 =
      ‖((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ)‖ ^ 2 *
        Real.exp ((2 * (q.1.1.1 : ℂ).re - 1) * tau) *
          HTGeometry.poissonOrderWeight tau r := by
  dsimp only
  change
    (tau / xiSourceCayleyDrift q) ^ r / r.factorial *
        ‖iteratedDeriv r
          (HTGeometry.cayleyPoleResidueMode
            ((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ)
            1 (q.1.1.1 : ℂ))
          ((tau / xiSourceCayleyDrift q : ℝ) : ℂ)‖ ^ 2 = _
  rw [HTGeometry.cayleyPoleResidueMode_poisson_conservation]
  change
    ‖((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ)‖ ^ 2 *
          Real.exp
            (xiSourceCayleyExponent q *
              (tau / xiSourceCayleyDrift q)) *
          HTGeometry.poissonOrderWeight
            (xiSourceCayleyDrift q *
              (tau / xiSourceCayleyDrift q)) r =
      _
  have hd : xiSourceCayleyDrift q ≠ 0 :=
    ne_of_gt (xiSourceCayleyDrift_pos q)
  have hdrift :
      xiSourceCayleyDrift q *
          (tau / xiSourceCayleyDrift q) = tau := by
    field_simp
  have hexponent :
      xiSourceCayleyExponent q *
          (tau / xiSourceCayleyDrift q) =
        (2 * (q.1.1.1 : ℂ).re - 1) * tau := by
    rw [xiSourceCayleyExponent_eq]
    field_simp
  rw [hdrift, hexponent]

/-- Adjacent-order exterior packet of the conjugate transported modes. -/
def xiSourceCayleyWardExteriorPacket
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) : ℂ :=
  HTGeometry.twoModeCoherentExterior
    (Real.sqrt (xiEndpointWardPairWeight q) : ℂ)
    (Real.sqrt (xiEndpointWardPairWeight q) : ℂ)
    (xiSourceCayleyShift q)
    ((starRingEnd ℂ) (xiSourceCayleyShift q)) x r

/-- Removing rotating phase preserves the exact Poisson packet. -/
theorem neg_re_xiSourceCayleyWardExteriorPacket_poisson_conservation
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial *
        (-(xiSourceCayleyWardExteriorPacket q x r).re) =
      4 * xiEndpointWardPairWeight q *
        (xiSourceCayleyShift q).im ^ 2 *
        Real.exp (xiSourceCayleyExponent q * x) *
          HTGeometry.poissonOrderWeight
            (xiSourceCayleyDrift q * x) r := by
  rw [xiSourceCayleyWardExteriorPacket,
    xiSourceCayleyExponent, xiSourceCayleyDrift,
    HTGeometry.neg_re_twoModeCoherentExterior_conj_poisson_conservation]
  rw [Real.sq_sqrt (xiEndpointWardPairWeight_pos q).le]

/-- Complete exterior order summation returns the exact signed exponential
instability. -/
theorem tsum_xiSourceCayleyWardExteriorPacket
    (q : XiRightUpperZeroCopy) (x : ℝ) :
    ∑' r : ℕ, ((x : ℂ) ^ r / r.factorial) *
        xiSourceCayleyWardExteriorPacket q x r =
      ((xiEndpointWardPairWeight q : ℝ) : ℂ) *
        (xiSourceCayleyShift q -
          (starRingEnd ℂ) (xiSourceCayleyShift q)) ^ 2 *
        Complex.exp ((xiSourceCayleyExponent q * x : ℝ) : ℂ) := by
  simp_rw [xiSourceCayleyWardExteriorPacket]
  rw [xiSourceCayleyExponent,
    HTGeometry.tsum_twoModeCoherentExterior_conj]
  rw [Real.sq_sqrt (xiEndpointWardPairWeight_pos q).le]

/-- Every phase-free exterior channel has the same strict orientation. -/
theorem xiSourceCayleyWardExteriorPacket_re_neg
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    (xiSourceCayleyWardExteriorPacket q x r).re < 0 := by
  rw [xiSourceCayleyWardExteriorPacket,
    HTGeometry.twoModeCoherentExterior_conj_eq]
  rw [show (xiSourceCayleyShift q -
      (starRingEnd ℂ) (xiSourceCayleyShift q)) ^ 2 =
      (((-4 * (xiSourceCayleyShift q).im ^ 2 : ℝ) : ℂ)) by
    rw [Complex.sub_conj, mul_pow, Complex.I_sq]
    push_cast
    ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, mul_zero]
  have him : (xiSourceCayleyShift q).im ≠ 0 := by
    rw [xiSourceCayleyShift, Complex.inv_im]
    apply div_ne_zero
    · simp only [Complex.sub_im, Complex.one_im, sub_zero]
      exact neg_ne_zero.mpr
        (xi_divisor_support_im_ne_zero q.1.1.1)
    · exact ne_of_gt
        (Complex.normSq_pos.mpr
          (sub_ne_zero.mpr (xiSourceCayley_rho_ne_one q)))
  have hweight :
      0 < Real.sqrt (xiEndpointWardPairWeight q) ^ 2 := by
    rw [Real.sq_sqrt (xiEndpointWardPairWeight_pos q).le]
    exact xiEndpointWardPairWeight_pos q
  have hnorm : 0 < ‖xiSourceCayleyShift q‖ ^ (2 * r) := by
    have hne : xiSourceCayleyShift q ≠ 0 := by
      rw [xiSourceCayleyShift]
      exact inv_ne_zero
        (sub_ne_zero.mpr (xiSourceCayley_rho_ne_one q))
    positivity
  have hexp : 0 < Real.exp (2 * (xiSourceCayleyShift q).re * x) :=
    Real.exp_pos _
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hweight
      (by nlinarith [sq_pos_of_ne_zero him]))
    (mul_pos hnorm hexp)

/-- Complete theorem surface of the source--Cayley order-space law. -/
structure XiSourceCayleyOrderSpaceConservationCertificate : Prop where
  arithmeticResponse :
    ∀ (x : ℂ) {s : ℂ}, 1 < s.re →
      xiCayleyEvolvedLogDeriv x s =
        (s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s -
          LSeries (fun n =>
            (ArithmeticFunction.vonMangoldt n : ℂ)) s) *
            xiCayleyEvolutionKernel x s
  residueTransport :
    ∀ (rho : XiDivisorSupport) (x : ℂ),
      Tendsto
        (fun s : ℂ =>
          (s - (rho : ℂ)) * xiCayleyEvolvedLogDeriv x s)
        (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ))
        (nhds (xiCayleySourceResidueMode (rho : ℂ) x))
  residueJets :
    ∀ (rho : XiDivisorSupport) (x : ℂ) (r : ℕ),
      iteratedDeriv r
          (xiCayleySourceResidueMode (rho : ℂ)) x =
        ((analyticOrderAt xi (rho : ℂ)).toNat : ℂ) *
          ((rho : ℂ) - 1)⁻¹ ^ r *
            Complex.exp (((rho : ℂ) - 1)⁻¹ * x)
  liCayleyConjugacy :
    ∀ q : XiRightUpperZeroCopy,
      xiSourceCayleyShift q = (xiWardLiCayleyNode q)⁻¹ - 1
  poissonCompletionOfLiOrbit :
    ∀ (q : XiRightUpperZeroCopy) (x : ℂ),
      xiCayleySourceResidueMode (q.1.1.1 : ℂ) x =
        ((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ) *
          HTGeometry.poissonCompletedGeometricOrbit
            (xiWardLiCayleyNode q)⁻¹ x
  parabolicXiResidueRenormalization :
    ∀ (q : XiRightUpperZeroCopy) (tau : ℝ) (r : ℕ),
      let x := tau / xiSourceCayleyDrift q
      x ^ r / r.factorial *
          ‖iteratedDeriv r
            (xiCayleySourceResidueMode (q.1.1.1 : ℂ)) (x : ℂ)‖ ^ 2 =
        ‖((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ)‖ ^ 2 *
          Real.exp ((2 * (q.1.1.1 : ℂ).re - 1) * tau) *
            HTGeometry.poissonOrderWeight tau r
  wardJetsAreSourceResidueJets :
    ∀ (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ),
      xiSourceCayleyWardCoherentJet q x r =
        (Real.sqrt (xiEndpointWardPairWeight q) : ℂ) /
            ((analyticOrderAt xi (q.1.1.1 : ℂ)).toNat : ℂ) *
          iteratedDeriv r
            (xiCayleySourceResidueMode (q.1.1.1 : ℂ)) (x : ℂ)
  poissonConservation :
    ∀ (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ),
      x ^ r / r.factorial *
          ‖xiSourceCayleyWardCoherentJet q x r‖ ^ 2 =
        xiEndpointWardPairWeight q *
          Real.exp (xiSourceCayleyExponent q * x) *
            HTGeometry.poissonOrderWeight
              (xiSourceCayleyDrift q * x) r
  strictRightInstability :
    ∀ q : XiRightUpperZeroCopy, 0 < xiSourceCayleyExponent q
  zeroReconstruction :
    ∀ q : XiRightUpperZeroCopy,
      (q.1.1.1 : ℂ).re =
          1 / 2 * (1 +
            xiSourceCayleyExponent q / xiSourceCayleyDrift q) ∧
        (q.1.1.1 : ℂ).im ^ 2 =
          1 / xiSourceCayleyDrift q -
            1 / 4 * (1 -
              xiSourceCayleyExponent q /
                xiSourceCayleyDrift q) ^ 2
  phaseFreeExterior :
    ∀ (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ),
      (xiSourceCayleyWardExteriorPacket q x r).re < 0 ∧
      x ^ r / r.factorial *
          (-(xiSourceCayleyWardExteriorPacket q x r).re) =
        4 * xiEndpointWardPairWeight q *
          (xiSourceCayleyShift q).im ^ 2 *
          Real.exp (xiSourceCayleyExponent q * x) *
            HTGeometry.poissonOrderWeight
              (xiSourceCayleyDrift q * x) r
  completeExteriorMass :
    ∀ (q : XiRightUpperZeroCopy) (x : ℝ),
      ∑' r : ℕ, ((x : ℂ) ^ r / r.factorial) *
          xiSourceCayleyWardExteriorPacket q x r =
        ((xiEndpointWardPairWeight q : ℝ) : ℂ) *
          (xiSourceCayleyShift q -
            (starRingEnd ℂ) (xiSourceCayleyShift q)) ^ 2 *
          Complex.exp
            ((xiSourceCayleyExponent q * x : ℝ) : ℂ)
  hurwitzPhaseChart :
    ∀ q : XiRightZeroCopy,
      xiHurwitzRightPrincipalPhase q =
        (xiRightCenteredZero q).re
  projectiveFreeEnergyChart :
    Tendsto
      (fun j : ℕ =>
        Real.log
            (xiThermalProjectiveColdTruncation j j) / (j : ℝ))
      atTop (nhds xiProjectiveReflectionRadius)
  wardTimeZero :
    xiEndpointWeightedWardIndex =
      (8 * Real.pi) * xiCayleyWardRadialVisibility 0
  heightOrderVisibility :
    ∀ (q : XiRightUpperZeroCopy) (n : ℕ),
      1 / ((q.1.1.1 : ℂ).im ^ 2 + 1) *
          (1 - (2 * (q.1.1.1 : ℂ).re - 1) /
            Complex.normSq (q.1.1.1 : ℂ))⁻¹ ^ n ≤
        xiCayleyWardRadialVisibility (2 * n)
  boundedTowerIffRH :
    (∃ K : ℝ, ∀ n : ℕ,
      xiCayleyWardRadialVisibility n ≤ K) ↔
        RiemannHypothesis
  falseRHExponentialInstability :
    ¬RiemannHypothesis →
      ∃ m c : ℝ, 0 < m ∧ 1 < c ∧
        ∀ n : ℕ,
          m * c ^ n ≤ xiCayleyWardRadialVisibility n

/-- **Riemann source--Cayley order-space conservation law.**  The
arithmetic response transports every Xi residue into an exact Poisson
packet.  Packet drift and rate reconstruct the zero, strict-right zeros
are exponentially unstable, phase-free exterior channels retain a strict
sign, and the Ward, Hurwitz, projective, and complete Cayley-order charts
are exact projections of this source dynamics. -/
theorem xiSourceCayleyOrderSpaceConservation_law :
    XiSourceCayleyOrderSpaceConservationCertificate := by
  refine {
    arithmeticResponse :=
      fun x _s hs =>
        xiCayleyEvolvedLogDeriv_eq_arithmetic x hs
    residueTransport := ?_
    residueJets :=
      fun rho x r =>
        iteratedDeriv_xiCayleySourceResidueMode
          (rho : ℂ) x r
    liCayleyConjugacy :=
      xiSourceCayleyShift_eq_inverseLiShift
    poissonCompletionOfLiOrbit :=
      xiCayleySourceResidueMode_eq_poissonCompletedLiOrbit
    parabolicXiResidueRenormalization :=
      xiCayleySourceResidueMode_parabolic_conservation
    wardJetsAreSourceResidueJets :=
      xiSourceCayleyWardCoherentJet_eq_scaled_residueMode_jet
    poissonConservation :=
      xiSourceCayleyWardCoherentJet_poisson_conservation
    strictRightInstability :=
      xiSourceCayleyExponent_pos
    zeroReconstruction := ?_
    phaseFreeExterior := ?_
    completeExteriorMass :=
      tsum_xiSourceCayleyWardExteriorPacket
    hurwitzPhaseChart :=
      xiHurwitzRightPrincipalPhase_eq_transverse
    projectiveFreeEnergyChart :=
      tendsto_xiThermalProjectiveColdDiagonal_log_div
    wardTimeZero :=
      xiEndpointWeightedWardIndex_eq_eightPi_mul_cayleyVisibility_zero
    heightOrderVisibility :=
      xiCayleyWardRadialVisibility_heightOrder_lowerBound
    boundedTowerIffRH :=
      xiCayleyWardRadialVisibility_bounded_iff_rh
    falseRHExponentialInstability :=
      exists_exponential_lowerBound_xiCayleyWardRadialVisibility }
  · intro rho x
    have hrho : (rho : ℂ) ≠ 1 := by
      intro h
      have hs := xi_divisor_support_re_mem_open_unit rho
      rw [h] at hs
      norm_num at hs
    exact xiCayleyEvolvedLogDeriv_residue_transport hrho x
  · intro q
    exact ⟨
      xiSourceCayley_rho_re_reconstruction q,
      xiSourceCayley_rho_im_sq_reconstruction q⟩
  · intro q x r
    exact ⟨
      xiSourceCayleyWardExteriorPacket_re_neg q x r,
      neg_re_xiSourceCayleyWardExteriorPacket_poisson_conservation
        q x r⟩

end

end RHTower
