import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingGaussianDivisibilityEndpoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingMinimumPhaseEndpoint
import GaloisForLFunctions.RHTower.XiHerglotzCriterion
import GaloisForLFunctions.HTGeometry.FiniteKMSFluctuationDissipation

/-!
# Theta-cusp Hawking Nambu--KMS influence-response receiver (hostile audit)

The raw theta-cusp Hawking Born amplitude is not a passive impedance: the boundary-sign no-go in
`ThetaCuspHawkingUVTransparentImpedanceEndpoint` proves that such an approximation would contradict
Hardy sign oscillation.  Pair creation does supply a genuine off-diagonal Bogoliubov interaction,
and the finite Nambu/KMS response below is a valid passive susceptibility built from that literal
kernel.  It does **not**, however, derive the proposed target

`logDeriv thetaCuspHawkingDeembeddedPairAmplitude = logDeriv XiC`,

from Hawking backreaction.

This file gives a finite regulator that retains the literal Hawking pair kernel.  Exterior modes
have modular energy `+E_a`, partner modes have modular energy `-E_b`, so an exterior/partner
transition has the physical pair frequency `E_a + E_b`.  The pair kernel occupies one Nambu block
and its adjoint occupies the reverse block.  The resulting observable is exactly Hermitian.
KMS fluctuation--dissipation makes every finite response anti-Herglotz; Hermiticity also makes it
exactly odd, matching the parity of `logDeriv XiC` but not identifying the two functions.

**[LITERATURE]** Perturbative moving-mirror influence functionals produce quadratic/convolutional
noise and dissipation kernels over two environmental channels at the pair resonance
`w = u + v`; see Butera, arXiv:2306.03813.  They do not produce a scattering-amplitude logarithmic
derivative.  The coefficient-faithful continuum observable is instead formalized in
`ThetaCuspHawkingPairEmissionSpectralDensity`.

**[CIRCULAR] [OPEN CORE] [NOVELTY UNVERIFIED]** The thermodynamic-limit structure below assumes
convergence to `logDeriv XiC`.  Since every finite response is anti-Herglotz, that convergence
already imports the sign condition which implies RH.  Real regulator data and the literal pair
block do not prevent a cutoff schedule from encoding the target.  Keep this module as a precise
conditional receiver and no-go diagnostic, not as a source-derived Hawking producer.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Exact finite Hawking Nambu regulator -/

/-- Quadrature-weighted theta-cusp Hawking pair-creation block.  Only real regulator data are
allowed; the complex dependence is the literal source kernel. -/
def thetaCuspHawkingFiniteWeightedPairBlock {n : ℕ}
    (energy weight : Fin (n + 1) → ℝ) (coupling : ℝ)
    (a b : Fin (n + 1)) : ℂ :=
  (((coupling * Real.sqrt (weight a) * Real.sqrt (weight b) : ℝ) : ℂ) *
    thetaCuspHawkingBornPairKernel (energy a : ℂ) (energy b : ℂ))

/-- Doubled modular/Liouville energy: exterior branch `0` carries `+E`, partner branch `1`
carries `-E`. -/
def thetaCuspHawkingFiniteNambuEnergy {n : ℕ}
    (energy : Fin (n + 1) → ℝ) (a : Fin 2 × Fin (n + 1)) : ℝ :=
  if a.1 = 0 then energy a.2 else -energy a.2

/-- Hermitian Nambu completion of the theta Hawking pair block.  Same-branch matrix elements
vanish; the reverse partner/exterior block is the adjoint of the exterior/partner block. -/
def thetaCuspHawkingFiniteNambuAmplitude {n : ℕ}
    (energy weight : Fin (n + 1) → ℝ) (coupling : ℝ)
    (a b : Fin 2 × Fin (n + 1)) : ℂ :=
  if a.1 = 0 ∧ b.1 = 1 then
    thetaCuspHawkingFiniteWeightedPairBlock energy weight coupling a.2 b.2
  else if a.1 = 1 ∧ b.1 = 0 then
    star (thetaCuspHawkingFiniteWeightedPairBlock energy weight coupling b.2 a.2)
  else 0

/-- **[PAPER-PROVED] [LEAN-PROVED]** The doubled observable containing the literal Hawking pair
kernel is exactly Hermitian. -/
theorem thetaCuspHawkingFiniteNambuAmplitude_hermitian {n : ℕ}
    (energy weight : Fin (n + 1) → ℝ) (coupling : ℝ) :
    ∀ a b, thetaCuspHawkingFiniteNambuAmplitude energy weight coupling b a =
      star (thetaCuspHawkingFiniteNambuAmplitude energy weight coupling a b) := by
  rintro ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    simp [thetaCuspHawkingFiniteNambuAmplitude]

/-- **[PAPER-PROVED] [LEAN-PROVED] Hawking pair-frequency law.**  A transition from partner mode
`b` to exterior mode `a` has modular energy gap `E_a + E_b`, not an arbitrary difference. -/
theorem thetaCuspHawkingFiniteNambuEnergy_exterior_partner_gap {n : ℕ}
    (energy : Fin (n + 1) → ℝ) (a b : Fin (n + 1)) :
    thetaCuspHawkingFiniteNambuEnergy energy (0, a) -
        thetaCuspHawkingFiniteNambuEnergy energy (1, b) =
      energy a + energy b := by
  simp [thetaCuspHawkingFiniteNambuEnergy]

/-- The exterior/partner block is exactly the quadrature-weighted theta Hawking Born kernel. -/
theorem thetaCuspHawkingFiniteNambuAmplitude_exterior_partner {n : ℕ}
    (energy weight : Fin (n + 1) → ℝ) (coupling : ℝ)
    (a b : Fin (n + 1)) :
    thetaCuspHawkingFiniteNambuAmplitude energy weight coupling (0, a) (1, b) =
      thetaCuspHawkingFiniteWeightedPairBlock energy weight coupling a b := by
  simp [thetaCuspHawkingFiniteNambuAmplitude]

/-! ## Finite KMS/FDT susceptibility -/

/-- Finite phase-sensitive response of the doubled theta Hawking pair observable. -/
def thetaCuspHawkingFiniteNambuKMSInfluenceResponse {n : ℕ}
    (beta : ℝ) (energy weight : Fin (n + 1) → ℝ)
    (coupling : ℝ) (z : ℂ) : ℂ :=
  HTGeometry.finiteTransitionPassiveResponse
    (HTGeometry.finiteKMSDissipativeTransitionIntensity beta
      (thetaCuspHawkingFiniteNambuEnergy energy)
      (thetaCuspHawkingFiniteNambuAmplitude energy weight coupling))
    (thetaCuspHawkingFiniteNambuEnergy energy) z

/-- **[BRIDGE] [LEAN-PROVED] Finite Hawking FDT passivity.**  Positive inverse Hawking
temperature forces the imaginary part of every regulated influence response to be nonpositive in
the upper half-plane. -/
theorem thetaCuspHawkingFiniteNambuKMSInfluenceResponse_im_nonpos {n : ℕ}
    (beta : ℝ) (energy weight : Fin (n + 1) → ℝ)
    (coupling : ℝ) (hbeta : 0 ≤ beta) {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspHawkingFiniteNambuKMSInfluenceResponse
      beta energy weight coupling z).im ≤ 0 := by
  exact HTGeometry.finiteKMSDissipativeTransitionPassiveResponse_im_nonpos
    beta (thetaCuspHawkingFiniteNambuEnergy energy)
      (thetaCuspHawkingFiniteNambuAmplitude energy weight coupling) hbeta hz

/-- **[BRIDGE] [LEAN-PROVED] Finite parity audit.**  Nambu Hermiticity makes every regulated
Hawking influence response exactly odd. -/
theorem thetaCuspHawkingFiniteNambuKMSInfluenceResponse_neg {n : ℕ}
    (beta : ℝ) (energy weight : Fin (n + 1) → ℝ)
    (coupling : ℝ) (z : ℂ) :
    thetaCuspHawkingFiniteNambuKMSInfluenceResponse beta energy weight coupling (-z) =
      -thetaCuspHawkingFiniteNambuKMSInfluenceResponse beta energy weight coupling z := by
  exact HTGeometry.finiteKMSDissipativeTransitionPassiveResponse_neg
    beta (thetaCuspHawkingFiniteNambuEnergy energy)
      (thetaCuspHawkingFiniteNambuAmplitude energy weight coupling)
      (thetaCuspHawkingFiniteNambuAmplitude_hermitian energy weight coupling) z

/-! ## Proposed logarithmic target and causal rotation -/

/-- Proposed phase-sensitive logarithmic target of the source-normalized Hawking pair amplitude.
This definition is algebraic; it is not a derived moving-mirror influence response. -/
def thetaCuspHawkingInfluenceResponse (z : ℂ) : ℂ :=
  logDeriv thetaCuspHawkingDeembeddedPairAmplitude z

/-- **[PAPER-PROVED] [LEAN-PROVED]** The deembedded Hawking influence response is exactly the
completed-Xi logarithmic derivative. -/
theorem thetaCuspHawkingInfluenceResponse_eq_logDeriv_XiC (z : ℂ) :
    thetaCuspHawkingInfluenceResponse z = logDeriv XiC z := by
  rfl

/-- Target parity agrees exactly with every finite Hermitian Nambu response. -/
theorem thetaCuspHawkingInfluenceResponse_neg (z : ℂ) :
    thetaCuspHawkingInfluenceResponse (-z) =
      -thetaCuspHawkingInfluenceResponse z := by
  rw [thetaCuspHawkingInfluenceResponse_eq_logDeriv_XiC,
    thetaCuspHawkingInfluenceResponse_eq_logDeriv_XiC, logDeriv_XiC_neg]

/-- Proposed causal right-half-plane logarithmic target, obtained algebraically by differentiating
the normalized Hawking Born form factor. -/
def thetaCuspHawkingCausalInfluenceResponse (p : ℂ) : ℂ :=
  logDeriv thetaCuspHawkingBornCausalFormFactor p

/-- **[PAPER-PROVED] [LEAN-PROVED] Causal rotation law.**  The causal response is `i` times the
upper-half-plane Hawking influence response at `i p`. -/
theorem thetaCuspHawkingCausalInfluenceResponse_eq (p : ℂ) :
    thetaCuspHawkingCausalInfluenceResponse p =
      Complex.I * thetaCuspHawkingInfluenceResponse (Complex.I * p) := by
  have hfun : thetaCuspHawkingBornCausalFormFactor =
      XiC ∘ (fun q : ℂ => Complex.I * q) := by
    funext q
    rw [thetaCuspHawkingBornCausalFormFactor,
      HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all]
    rfl
  rw [thetaCuspHawkingCausalInfluenceResponse, hfun,
    logDeriv_comp (XiC_differentiable (Complex.I * p)) (by fun_prop)]
  have hderiv : deriv (fun q : ℂ => Complex.I * q) p = Complex.I := by
    simp
  rw [hderiv, thetaCuspHawkingInfluenceResponse_eq_logDeriv_XiC]
  ring

/-! ## Source-specific thermodynamic limit -/

/-- **[CIRCULAR] [OPEN CORE] [NOVELTY UNVERIFIED]** A proposed thermodynamic regulator of the theta
moving mirror.  Its convergence field is exactly the unproved RH-strength identification:
coefficient-faithful finite Hawking susceptibilities must converge to `logDeriv XiC`.  Known
moving-mirror influence functionals yield quadratic pair-channel convolutions, not this
logarithmic target. -/
structure ThetaCuspHawkingNambuKMSInfluenceLimit where
  beta : ℝ
  beta_pos : 0 < beta
  energy : (n : ℕ) → Fin (n + 1) → ℝ
  energy_nonneg : ∀ n a, 0 ≤ energy n a
  weight : (n : ℕ) → Fin (n + 1) → ℝ
  weight_nonneg : ∀ n a, 0 ≤ weight n a
  coupling : ℕ → ℝ
  converges : ∀ z : ℂ, 0 < z.im → XiC z ≠ 0 →
    Tendsto
      (fun n => thetaCuspHawkingFiniteNambuKMSInfluenceResponse
        beta (energy n) (weight n) (coupling n) z)
      atTop (nhds (thetaCuspHawkingInfluenceResponse z))

/-- **[BRIDGE] [LEAN-PROVED] Closed sign survives the Hawking thermodynamic limit.** -/
theorem thetaCuspHawkingInfluenceResponse_im_nonpos_of_NambuKMSLimit
    (model : ThetaCuspHawkingNambuKMSInfluenceLimit)
    (z : ℂ) (hz : 0 < z.im) (hXi : XiC z ≠ 0) :
    (logDeriv XiC z).im ≤ 0 := by
  have hlim := model.converges z hz hXi
  have himlim : Tendsto
      (fun n => (thetaCuspHawkingFiniteNambuKMSInfluenceResponse
        model.beta (model.energy n) (model.weight n) (model.coupling n) z).im)
      atTop (nhds (thetaCuspHawkingInfluenceResponse z).im) :=
    (Complex.continuous_im.tendsto _).comp hlim
  have hsign : (thetaCuspHawkingInfluenceResponse z).im ≤ 0 :=
    isClosed_Iic.mem_of_tendsto himlim
      (Filter.Eventually.of_forall fun n =>
        thetaCuspHawkingFiniteNambuKMSInfluenceResponse_im_nonpos
          model.beta (model.energy n) (model.weight n) (model.coupling n)
          model.beta_pos.le hz)
  simpa only [thetaCuspHawkingInfluenceResponse_eq_logDeriv_XiC] using hsign

/-- The same limit makes the causal logarithmic response positive-real wherever the Hawking Born
form factor is nonzero. -/
theorem thetaCuspHawkingCausalInfluenceResponse_re_nonneg_of_NambuKMSLimit
    (model : ThetaCuspHawkingNambuKMSInfluenceLimit)
    (p : ℂ) (hp : 0 < p.re) (hXi : XiC (Complex.I * p) ≠ 0) :
    0 ≤ (thetaCuspHawkingCausalInfluenceResponse p).re := by
  rw [thetaCuspHawkingCausalInfluenceResponse_eq,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
    neg_nonneg]
  exact thetaCuspHawkingInfluenceResponse_im_nonpos_of_NambuKMSLimit
    model (Complex.I * p) (by simpa [Complex.mul_im]) hXi

/-- **[REDISCOVERED] [BRIDGE] Conditional Nambu--KMS receiver.**  The abstract
anti-Herglotz-to-RH criterion is already in the corpus.  This implication exposes the exact
circular burden carried by `ThetaCuspHawkingNambuKMSInfluenceLimit`; it is not evidence that the
Hawking pair kernel produces the assumed limit. -/
theorem riemannHypothesis_of_thetaCuspHawkingNambuKMSInfluenceLimit
    (model : ThetaCuspHawkingNambuKMSInfluenceLimit) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_im_logDeriv_nonpos
  intro z hz hXi
  exact thetaCuspHawkingInfluenceResponse_im_nonpos_of_NambuKMSLimit
    model z hz hXi

end RHTower
