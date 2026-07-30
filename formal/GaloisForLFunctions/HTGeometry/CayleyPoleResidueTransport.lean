import GaloisForLFunctions.HTGeometry.CayleyFockOrderSpaceConservation
import GaloisForLFunctions.HTGeometry.DirectionalVandermondePhaseJet
import GaloisForLFunctions.HTGeometry.ExponentialSumDA
import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization

/-!
# Cayley transport of a pole residue

Let a response have residue `m` at `rho`, and choose a distinguished source
point `c`.  Multiplication before residue extraction by

```text
exp (x / (s - c))
```

transports the residue into the coherent mode

```text
m * exp (x / (rho - c)).
```

Every evolution derivative is therefore an exact coherent jet.  Its
factorially normalized energy is the Poisson order packet from
`CayleyFockOrderSpaceConservation`: the packet drift is
`‖(rho-c)⁻¹‖²`, and its total mass has exponential rate
`‖1 + (rho-c)⁻¹‖² - 1`.

The theorem is local and universal.  It assumes only the residue limit and
does not assume that the pole is simple.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cayley evolution based at the distinguished source point `c`. -/
def cayleyPoleEvolutionKernel (c x s : ℂ) : ℂ :=
  Complex.exp ((s - c)⁻¹ * x)

/-- A response after Cayley evolution and before residue extraction. -/
def cayleyPoleEvolvedResponse
    (c x : ℂ) (response : ℂ → ℂ) (s : ℂ) : ℂ :=
  response s * cayleyPoleEvolutionKernel c x s

/-- Coherent mode obtained by transporting residue `m` at `rho`. -/
def cayleyPoleResidueMode (m c rho x : ℂ) : ℂ :=
  m * Complex.exp ((rho - c)⁻¹ * x)

/-- Finite divisor transport as a constant-coefficient exponential
spectrum in evolution time. -/
def finiteCayleyResidueCarrier {n : ℕ}
    (m rho : Fin n → ℂ) (c : ℂ) : ℂ → ℂ :=
  phasePolynomial (fun j => (rho j - c)⁻¹) m

/-- Every finite transported divisor carrier is differentially
algebraic in evolution time, even when the ambient meromorphic
function is hypertranscendental. -/
theorem finiteCayleyResidueCarrier_differentiallyAlgebraic
    {n : ℕ} (m rho : Fin n → ℂ) (c : ℂ) :
    DifferentiallyAlgebraic
      (finiteCayleyResidueCarrier m rho c) := by
  unfold finiteCayleyResidueCarrier phasePolynomial
  exact differentiallyAlgebraic_finset_expSum_general
    Finset.univ m (fun j => (rho j - c)⁻¹)

/-- The finite transported divisor satisfies the explicit
constant-coefficient ODE whose characteristic roots are the inverse
source displacements. -/
theorem finiteCayleyResidueCarrier_ode
    {n : ℕ} (m rho : Fin n → ℂ) (c x : ℂ) :
    let lam : Fin n → ℂ := fun j => (rho j - c)⁻¹
    let p := expSumAnnihilator Finset.univ lam
    ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j *
          iteratedDeriv j
            (finiteCayleyResidueCarrier m rho c) x = 0 := by
  dsimp only
  unfold finiteCayleyResidueCarrier phasePolynomial
  exact expSumAnnihilator_ode Finset.univ m
    (fun j => (rho j - c)⁻¹) x

/-- **Finite source spectra are jet-faithful.** Distinct divisor
points give distinct inverse-source frequencies. Hence a nonzero
finite residue vector cannot disappear: at every evolution time one
of the first `n` jets is nonzero. -/
theorem finiteCayleyResidueCarrier_jetFaithful
    {n : ℕ} {m rho : Fin n → ℂ} {c x : ℂ}
    (hrho : Function.Injective rho) (hm : m ≠ 0) :
    ∃ r : Fin n,
      iteratedDeriv (r : ℕ)
        (finiteCayleyResidueCarrier m rho c) x ≠ 0 := by
  apply phaseJet_exists_ne_zero
  · intro i j hij
    apply hrho
    have hinv :=
      congrArg (fun z : ℂ => z⁻¹) hij
    simpa only [inv_inv, sub_left_inj] using hinv
  · exact hm

/-- Poisson completion of the discrete geometric orbit `a ^ n`.

The factorial weights analytically continue the Poisson expectation
`E[a^N]`, with `N` of mean `x`, to complex `a` and `x`. -/
def poissonCompletedGeometricOrbit (a x : ℂ) : ℂ :=
  ∑' n : ℕ,
    Complex.exp (-x) * (x ^ n / n.factorial) * a ^ n

/-- **Poisson completion law.** The Poisson completion of a geometric
orbit is the coherent exponential mode with displacement `a - 1`. -/
theorem poissonCompletedGeometricOrbit_eq
    (a x : ℂ) :
    poissonCompletedGeometricOrbit a x =
      Complex.exp ((a - 1) * x) := by
  have hsum :=
    (NormedSpace.expSeries_div_hasSum_exp (a * x)).mul_left
      (Complex.exp (-x))
  rw [show
      (fun n : ℕ =>
        Complex.exp (-x) * ((a * x) ^ n / n.factorial)) =
      (fun n : ℕ =>
        Complex.exp (-x) * (x ^ n / n.factorial) * a ^ n) by
        funext n
        rw [mul_pow]
        ring] at hsum
  rw [poissonCompletedGeometricOrbit, hsum.tsum_eq]
  rw [← Complex.exp_eq_exp_ℂ]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- A transported pole residue is exactly the Poisson completion of its
Cayley orbit `a = 1 + (rho - c)⁻¹`. -/
theorem cayleyPoleResidueMode_eq_poissonCompletion
    (m c rho x : ℂ) :
    cayleyPoleResidueMode m c rho x =
      m * poissonCompletedGeometricOrbit
        (1 + (rho - c)⁻¹) x := by
  rw [cayleyPoleResidueMode, poissonCompletedGeometricOrbit_eq]
  congr 2
  ring

/-- Canonical observation time centered at source `c`. -/
def sourceCayleyObservationTime
    (c rho : ℂ) (tau : ℝ) : ℝ :=
  Complex.normSq (rho - c) * tau

/-- Signed transverse rate measured from the neutral source horizon
`Re (rho - c) = -1/2`. -/
def sourceCayleyTransverseRate (c rho : ℂ) : ℝ :=
  2 * (rho - c).re + 1

/-- Every source `c` determines the exact neutral horizon
`Re rho = Re c - 1/2`. -/
theorem sourceCayleyTransverseRate_eq_zero_iff
    (c rho : ℂ) :
    sourceCayleyTransverseRate c rho = 0 ↔
      rho.re = c.re - 1 / 2 := by
  simp only [sourceCayleyTransverseRate, Complex.sub_re]
  constructor <;> intro h <;> linarith

/-- The source mode is unstable exactly to the right of its neutral
horizon. -/
theorem sourceCayleyTransverseRate_pos_iff
    (c rho : ℂ) :
    0 < sourceCayleyTransverseRate c rho ↔
      c.re - 1 / 2 < rho.re := by
  simp only [sourceCayleyTransverseRate, Complex.sub_re]
  constructor <;> intro h <;> linarith

/-- Canonical source observation cancels inverse-square packet drift
exactly. -/
theorem sourceCayley_drift_observationTime
    (c rho : ℂ) (tau : ℝ) (hrho : rho ≠ c) :
    cayleyFockDrift ((rho - c)⁻¹) *
        sourceCayleyObservationTime c rho tau =
      tau := by
  rw [cayleyFockDrift, Complex.sq_norm, Complex.normSq_inv,
    sourceCayleyObservationTime]
  have hden : Complex.normSq (rho - c) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (sub_ne_zero.mpr hrho))
  field_simp

/-- Source-Cayley time is not an independently chosen scale: it is
exactly the unique clock forced by universal Poisson drift
normalization. -/
theorem sourceCayleyObservationTime_eq_coherentGeneratorTime
    (c rho : ℂ) (tau : ℝ) (hrho : rho ≠ c) :
    sourceCayleyObservationTime c rho tau =
      coherentGeneratorObservationTime ((rho - c)⁻¹) tau := by
  exact coherentGenerator_observationTime_unique
    ((rho - c)⁻¹) tau
      (sourceCayleyObservationTime c rho tau)
      (inv_ne_zero (sub_ne_zero.mpr hrho))
      (sourceCayley_drift_observationTime c rho tau hrho)

/-- The source horizon is the pullback of the universal reciprocal
generator horizon. -/
theorem coherentGeneratorDualRate_sourceCayley
    (c rho : ℂ) :
    coherentGeneratorDualRate ((rho - c)⁻¹) =
      sourceCayleyTransverseRate c rho := by
  rw [coherentGeneratorDualRate, sourceCayleyTransverseRate, inv_inv]

/-- **Source inversion law.** Canonical observation converts reciprocal
Cayley displacement into conjugate direct displacement. -/
theorem sourceCayley_inverse_observationTime
    (c rho : ℂ) (tau : ℝ) (hrho : rho ≠ c) :
    (rho - c)⁻¹ *
        (sourceCayleyObservationTime c rho tau : ℂ) =
      (starRingEnd ℂ) (rho - c) * (tau : ℂ) := by
  rw [sourceCayleyObservationTime, Complex.inv_def]
  have hden : Complex.normSq (rho - c) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (sub_ne_zero.mpr hrho))
  have hdenC : (Complex.normSq (rho - c) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  push_cast
  field_simp [hdenC]

/-- At canonical time, the full complex residue mode is a direct
conjugate spectral mode; radial escape becomes oscillatory phase rather
than information loss. -/
theorem cayleyPoleResidueMode_observationTime_eq
    (m c rho : ℂ) (tau : ℝ) (hrho : rho ≠ c) :
    cayleyPoleResidueMode m c rho
        (sourceCayleyObservationTime c rho tau : ℂ) =
      m * Complex.exp
        ((starRingEnd ℂ) (rho - c) * (tau : ℂ)) := by
  rw [cayleyPoleResidueMode,
    sourceCayley_inverse_observationTime c rho tau hrho]

/-- At canonical source observation time, total packet growth loses
all radial information and retains only signed distance from the source
horizon. -/
theorem sourceCayley_exponent_observationTime
    (c rho : ℂ) (tau : ℝ) (hrho : rho ≠ c) :
    cayleyFockExponent ((rho - c)⁻¹) *
        sourceCayleyObservationTime c rho tau =
      sourceCayleyTransverseRate c rho * tau := by
  rw [cayleyFockExponent_eq, cayleyFockDrift, Complex.sq_norm,
    Complex.normSq_inv, Complex.inv_re,
    sourceCayleyObservationTime, sourceCayleyTransverseRate]
  have hden : Complex.normSq (rho - c) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (sub_ne_zero.mpr hrho))
  field_simp

/-- Vertical pole family at horizontal displacement `a` from the
critical boundary `Re rho = 1/2`. -/
def parabolicCayleyPole (a T : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (a : ℂ) + (T : ℂ) * Complex.I

/-- Canonical parabolic observation time for a pole at height `T`. -/
def parabolicCayleyTime (a T tau : ℝ) : ℝ :=
  ((a - 1 / 2) ^ 2 + T ^ 2) * tau

theorem parabolicCayleyPole_ne_one
    (a T : ℝ) (hT : T ≠ 0) :
    parabolicCayleyPole a T ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  simp [parabolicCayleyPole] at him
  exact hT him

theorem normSq_parabolicCayleyPole_sub_one
    (a T : ℝ) :
    Complex.normSq (parabolicCayleyPole a T - 1) =
      (a - 1 / 2) ^ 2 + T ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [parabolicCayleyPole, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.sub_re, Complex.one_re,
    Complex.add_im, Complex.mul_im, mul_one,
    Complex.sub_im, Complex.one_im]
  norm_num
  ring

/-- Under parabolic time rescaling, inverse-square packet drift loses
all dependence on pole height. -/
theorem parabolicCayley_drift_time
    (a T tau : ℝ) (hT : T ≠ 0) :
    cayleyFockDrift
          ((parabolicCayleyPole a T - 1)⁻¹) *
        parabolicCayleyTime a T tau =
      tau := by
  rw [cayleyFockDrift_of_rho
    (parabolicCayleyPole_ne_one a T hT)]
  rw [normSq_parabolicCayleyPole_sub_one, parabolicCayleyTime]
  have hden : (a - 1 / 2) ^ 2 + T ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hT]
  field_simp [hden]

/-- Under the same rescaling, total packet growth retains exactly the
signed transverse displacement and loses all dependence on height. -/
theorem parabolicCayley_exponent_time
    (a T tau : ℝ) (hT : T ≠ 0) :
    cayleyFockExponent
          ((parabolicCayleyPole a T - 1)⁻¹) *
        parabolicCayleyTime a T tau =
      2 * a * tau := by
  rw [cayleyFockExponent_of_rho
    (parabolicCayleyPole_ne_one a T hT)]
  have hre : (parabolicCayleyPole a T).re = 1 / 2 + a := by
    simp [parabolicCayleyPole]
  rw [hre]
  calc
    (2 * (1 / 2 + a) - 1) *
          cayleyFockDrift
            ((parabolicCayleyPole a T - 1)⁻¹) *
          parabolicCayleyTime a T tau =
        (2 * (1 / 2 + a) - 1) *
          (cayleyFockDrift
            ((parabolicCayleyPole a T - 1)⁻¹) *
              parabolicCayleyTime a T tau) := by ring
    _ = (2 * (1 / 2 + a) - 1) * tau := by
      rw [parabolicCayley_drift_time a T tau hT]
    _ = 2 * a * tau := by ring

theorem continuousAt_cayleyPoleEvolutionKernel
    (c x : ℂ) {rho : ℂ} (hrho : rho ≠ c) :
    ContinuousAt (cayleyPoleEvolutionKernel c x) rho := by
  unfold cayleyPoleEvolutionKernel
  exact Complex.continuous_exp.continuousAt.comp
    (((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.mpr hrho)).mul continuousAt_const)

/-- **Universal Cayley residue transport.** Multiplying a response by the
Cayley evolution before taking its residue transports the residue into one
coherent exponential mode. -/
theorem cayleyPoleEvolvedResponse_residue_transport
    (response : ℂ → ℂ) {m c rho : ℂ} (hrho : rho ≠ c)
    (hresidue :
      Tendsto (fun s : ℂ => (s - rho) * response s)
        (nhdsWithin rho ({rho}ᶜ)) (nhds m))
    (x : ℂ) :
    Tendsto
      (fun s : ℂ =>
        (s - rho) * cayleyPoleEvolvedResponse c x response s)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (cayleyPoleResidueMode m c rho x)) := by
  have hkernel : Tendsto (cayleyPoleEvolutionKernel c x)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (cayleyPoleEvolutionKernel c x rho)) :=
    (continuousAt_cayleyPoleEvolutionKernel c x hrho).tendsto.mono_left
      nhdsWithin_le_nhds
  have hmul := hresidue.mul hkernel
  simpa only [cayleyPoleEvolvedResponse, cayleyPoleResidueMode,
    cayleyPoleEvolutionKernel, mul_assoc] using hmul

/-- A meromorphic zero or pole of any integer order generates the
parabolic coherent residue mode after source evolution. -/
theorem parabolicLogDerivEvolvedResponse_residue_transport
    (f : ℂ → ℂ) {m : ℤ} (a T : ℝ) (hT : T ≠ 0)
    (hf : MeromorphicAt f (parabolicCayleyPole a T))
    (horder :
      meromorphicOrderAt f (parabolicCayleyPole a T) = m)
    (x : ℂ) :
    Tendsto
      (fun s : ℂ =>
        (s - parabolicCayleyPole a T) *
          cayleyPoleEvolvedResponse 1 x (logDeriv f) s)
      (nhdsWithin (parabolicCayleyPole a T)
        ({parabolicCayleyPole a T}ᶜ))
      (nhds
        (cayleyPoleResidueMode (m : ℂ) 1
          (parabolicCayleyPole a T) x)) := by
  apply cayleyPoleEvolvedResponse_residue_transport
    (logDeriv f) (parabolicCayleyPole_ne_one a T hT)
  exact logDeriv_residue_of_meromorphicOrder hf horder

/-- All evolution derivatives of a transported residue are coherent
exponential jets. -/
theorem iteratedDeriv_cayleyPoleResidueMode
    (m c rho x : ℂ) (r : ℕ) :
    iteratedDeriv r (cayleyPoleResidueMode m c rho) x =
      m * (rho - c)⁻¹ ^ r *
        Complex.exp ((rho - c)⁻¹ * x) := by
  change iteratedDeriv r
    (fun x : ℂ => m * Complex.exp ((rho - c)⁻¹ * x)) x = _
  rw [iteratedDeriv_const_mul m
    (by fun_prop :
      ContDiffAt ℂ r
        (fun x : ℂ => Complex.exp ((rho - c)⁻¹ * x)) x)]
  rw [GaloisForLFunctions.iteratedDeriv_exp_linear]
  ring

/-- **Residue-to-Poisson order-space conservation.**  The exact derivative
energy of a transported residue is a Poisson packet. -/
theorem cayleyPoleResidueMode_poisson_conservation
    (m c rho : ℂ) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial *
        ‖iteratedDeriv r (cayleyPoleResidueMode m c rho) (x : ℂ)‖ ^ 2 =
      ‖m‖ ^ 2 *
        Real.exp (cayleyFockExponent ((rho - c)⁻¹) * x) *
          poissonOrderWeight
            (cayleyFockDrift ((rho - c)⁻¹) * x) r := by
  rw [iteratedDeriv_cayleyPoleResidueMode]
  simpa only [coherentExponentialJet] using
    coherentExponentialJet_poisson_conservation
      m ((rho - c)⁻¹) x r

/-- **Universal source-horizon conservation law.**  At the canonical
observation time `|rho-c|² tau`, every transported residue has an exact
height-free Poisson order packet.  Its only surviving exponential datum
is signed distance from the neutral source horizon. -/
theorem sourceCayleyResidueMode_horizon_conservation
    (m c rho : ℂ) (tau : ℝ) (r : ℕ) (hrho : rho ≠ c) :
    let x := sourceCayleyObservationTime c rho tau
    x ^ r / r.factorial *
        ‖iteratedDeriv r
          (cayleyPoleResidueMode m c rho) (x : ℂ)‖ ^ 2 =
      ‖m‖ ^ 2 *
        Real.exp (sourceCayleyTransverseRate c rho * tau) *
          poissonOrderWeight tau r := by
  dsimp only
  rw [cayleyPoleResidueMode_poisson_conservation]
  rw [sourceCayley_exponent_observationTime c rho tau hrho,
    sourceCayley_drift_observationTime c rho tau hrho]

/-- **Parabolic residue-renormalization law.**  A residue escaping to
height `T` has an exactly height-independent Poisson order packet when
observed at its canonical quadratic time.  Its remaining exponential
rate is exactly twice the horizontal displacement `a`. -/
theorem parabolicCayleyResidueMode_renormalization
    (m : ℂ) (a T tau : ℝ) (r : ℕ) (hT : T ≠ 0) :
    let x := parabolicCayleyTime a T tau
    x ^ r / r.factorial *
        ‖iteratedDeriv r
          (cayleyPoleResidueMode m 1
            (parabolicCayleyPole a T)) (x : ℂ)‖ ^ 2 =
      ‖m‖ ^ 2 * Real.exp (2 * a * tau) *
        poissonOrderWeight tau r := by
  dsimp only
  rw [cayleyPoleResidueMode_poisson_conservation]
  rw [parabolicCayley_exponent_time a T tau hT,
    parabolicCayley_drift_time a T tau hT]

end

end GaloisForLFunctions.HTGeometry
