import GaloisForLFunctions.RHTower.ThetaCuspHawkingMinimumPhaseEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingModularSuperselectionEndpoint
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.XiEndpointCompletedValue
import GaloisForLFunctions.HTGeometry.FiniteKMSFluctuationDissipation
import GaloisForLFunctions.HTGeometry.PositiveRealPartRigidity
import GaloisForLFunctions.HTGeometry.RightHalfPlaneWitnesses

/-!
# UV-transparent Hawking-impedance limit endpoint

This file replaces a false purity shortcut by a causal moving-mirror stability problem.
Jaekel--Reynaud (`arXiv:quant-ph/0101080`) show that a causal, unitary, partially transmitting
mirror with high-frequency cutoff has Laplace-domain mechanical impedance

`Z(p) = ∫ dPhi(rho) (1 - i p rho) / (p - i rho) + k / p + p (m - mu)`,

where `dPhi` is nonnegative, `k` is the suspension stiffness, and `mu` is the induced
high-frequency mass.  If `mu <= m`, this is positive-real and has no runaway zero in `Re p > 0`.
The finite atomic version is formalized below.  Existing KMS fluctuation--dissipation theory then
supplies its nonnegative spectral weights without an added passivity premise.

The theta-cusp backreaction route identifies `p |-> XiC (i p)` as a causal Hawking *amplitude*.
The attempted endpoint below asked finite KMS/FDT impedances to converge to that raw amplitude.

**[FALSIFIED]** This producer cannot exist.  Positive-real convergence would make `Xi t`
nonnegative on the entire real boundary.  The corpus Hardy theorem excludes every eventually
one-signed Xi tail.  Thus the raw scattering/Bogoliubov amplitude is not itself a passive
impedance.  The surviving Hawking-specific observable must instead be a response derived from the
amplitude, such as its logarithmic derivative (the influence-functional or Wigner--Smith response).
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-! ## Jaekel--Reynaud positive-real spectral impedance -/

/-- Atomic spectral kernel in the Jaekel--Reynaud Laplace-domain impedance formula. -/
def thetaCuspHawkingJaekelReynaudSpectralKernel (rho : ℝ) (p : ℂ) : ℂ :=
  (1 - Complex.I * p * (rho : ℂ)) / (p - Complex.I * (rho : ℂ))

/-- **[PAPER-PROVED] Spectral-kernel real-part law.**  Every atomic mirror channel has strictly
positive real part in the causal half-plane. -/
theorem thetaCuspHawkingJaekelReynaudSpectralKernel_re
    (rho : ℝ) {p : ℂ} (hp : 0 < p.re) :
    (thetaCuspHawkingJaekelReynaudSpectralKernel rho p).re =
      p.re * (1 + rho ^ 2) /
        Complex.normSq (p - Complex.I * (rho : ℂ)) := by
  have hden : p - Complex.I * (rho : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero,
      Complex.zero_re] at hre
    linarith
  rw [thetaCuspHawkingJaekelReynaudSpectralKernel, Complex.div_re]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, zero_mul, one_mul, sub_zero, zero_sub]
  rw [show Complex.normSq (p - Complex.I * (rho : ℂ)) =
      p.re ^ 2 + (p.im - rho) ^ 2 by
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    ring]
  field_simp [(Complex.normSq_pos.mpr hden).ne']
  ring

/-- Every Jaekel--Reynaud atomic spectral channel is strictly positive-real. -/
theorem thetaCuspHawkingJaekelReynaudSpectralKernel_re_pos
    (rho : ℝ) {p : ℂ} (hp : 0 < p.re) :
    0 < (thetaCuspHawkingJaekelReynaudSpectralKernel rho p).re := by
  rw [thetaCuspHawkingJaekelReynaudSpectralKernel_re rho hp]
  exact div_pos (mul_pos hp (by positivity))
    (Complex.normSq_pos.mpr (by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero,
        Complex.zero_re] at hre
      linarith))

/-- Finite atomic Jaekel--Reynaud impedance.  `bareMass - inducedMass` is the inertial margin. -/
def thetaCuspHawkingFiniteSpectralImpedance {ι : Type*} [Fintype ι]
    (weight frequency : ι → ℝ) (spring bareMass inducedMass : ℝ) (p : ℂ) : ℂ :=
  ∑ i, (weight i : ℂ) *
      thetaCuspHawkingJaekelReynaudSpectralKernel (frequency i) p +
    (spring : ℂ) / p + ((bareMass - inducedMass : ℝ) : ℂ) * p

/-- **[LEAN-PROVED] Finite UV-transparent passivity law.**  Nonnegative dissipative spectrum and
spring, together with strict induced-mass margin, make the full impedance strictly positive-real.
The strict margin is the realistic `mu < m` regime; it avoids a degenerate zero impedance when all
other coefficients vanish. -/
theorem thetaCuspHawkingFiniteSpectralImpedance_re_pos
    {ι : Type*} [Fintype ι]
    (weight frequency : ι → ℝ) (spring bareMass inducedMass : ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hspring : 0 ≤ spring)
    (hmass : inducedMass < bareMass) {p : ℂ} (hp : 0 < p.re) :
    0 < (thetaCuspHawkingFiniteSpectralImpedance
      weight frequency spring bareMass inducedMass p).re := by
  have hpne : p ≠ 0 := by
    intro h
    rw [h] at hp
    simp at hp
  have hsum : 0 ≤
      (∑ i, (weight i : ℂ) *
        thetaCuspHawkingJaekelReynaudSpectralKernel (frequency i) p).re := by
    change 0 ≤ Complex.reCLM
      (∑ i, (weight i : ℂ) *
        thetaCuspHawkingJaekelReynaudSpectralKernel (frequency i) p)
    rw [map_sum Complex.reCLM]
    exact Finset.sum_nonneg fun i _ => by
      change 0 ≤ ((weight i : ℂ) *
        thetaCuspHawkingJaekelReynaudSpectralKernel (frequency i) p).re
      rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (hweight i)
        (thetaCuspHawkingJaekelReynaudSpectralKernel_re_pos
          (frequency i) hp).le
  have hspringTerm : 0 ≤ ((spring : ℂ) / p).re := by
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_div]
    exact div_nonneg (mul_nonneg hspring hp.le) (Complex.normSq_nonneg p)
  have hmassTerm : 0 < (((bareMass - inducedMass : ℝ) : ℂ) * p).re := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (sub_pos.mpr hmass) hp
  rw [thetaCuspHawkingFiniteSpectralImpedance,
    Complex.add_re, Complex.add_re]
  linarith

/-! ## KMS fluctuation--dissipation realization -/

/-- Finite-temperature Jaekel--Reynaud impedance whose atomic weights are the exact KMS/FDT
dissipative transition intensities already formalized in the corpus. -/
def thetaCuspHawkingFiniteKMSFDTImpedance {n : ℕ}
    (beta : ℝ) (energy : Fin (n + 1) → ℝ)
    (amplitude : Fin (n + 1) → Fin (n + 1) → ℂ)
    (spring bareMass inducedMass : ℝ) (p : ℂ) : ℂ :=
  thetaCuspHawkingFiniteSpectralImpedance
    (fun ab : Fin (n + 1) × Fin (n + 1) =>
      HTGeometry.finiteKMSDissipativeTransitionIntensity
        beta energy amplitude ab.1 ab.2)
    (fun ab => energy ab.1 - energy ab.2)
    spring bareMass inducedMass p

/-- **[BRIDGE] KMS/FDT-to-impedance passivity.**  Nonnegative inverse temperature supplies every
spectral-weight sign required by the UV-transparent mechanical impedance. -/
theorem thetaCuspHawkingFiniteKMSFDTImpedance_re_pos {n : ℕ}
    (beta : ℝ) (energy : Fin (n + 1) → ℝ)
    (amplitude : Fin (n + 1) → Fin (n + 1) → ℂ)
    (spring bareMass inducedMass : ℝ)
    (hbeta : 0 ≤ beta) (hspring : 0 ≤ spring)
    (hmass : inducedMass < bareMass) {p : ℂ} (hp : 0 < p.re) :
    0 < (thetaCuspHawkingFiniteKMSFDTImpedance
      beta energy amplitude spring bareMass inducedMass p).re := by
  apply thetaCuspHawkingFiniteSpectralImpedance_re_pos
  · intro ab
    exact
      HTGeometry.finiteKMSDissipativeTransitionIntensity_nonneg
        beta energy amplitude hbeta ab.1 ab.2
  · exact hspring
  · exact hmass
  · exact hp

/-! ## Source-specific cofinal impedance limit -/

/-- **[FALSIFIED] Source-normalized UV-transparent impedance limit.**  A cofinal family of finite
KMS/FDT material impedances, with nonnegative temperature and strict mass margin at every cutoff,
converges locally uniformly to the exact theta-cusp Hawking form factor on `Re p > 0`.

No value of this structure exists: see
`not_nonempty_thetaCuspHawkingUVTransparentKMSFDTImpedanceLimit`. -/
structure ThetaCuspHawkingUVTransparentKMSFDTImpedanceLimit where
  beta : ℕ → ℝ
  energy : (n : ℕ) → Fin (n + 1) → ℝ
  amplitude : (n : ℕ) → Fin (n + 1) → Fin (n + 1) → ℂ
  spring : ℕ → ℝ
  bareMass : ℕ → ℝ
  inducedMass : ℕ → ℝ
  beta_nonneg : ∀ n, 0 ≤ beta n
  spring_nonneg : ∀ n, 0 ≤ spring n
  mass_margin : ∀ n, inducedMass n < bareMass n
  converges : TendstoLocallyUniformlyOn
    (fun n => thetaCuspHawkingFiniteKMSFDTImpedance
      (beta n) (energy n) (amplitude n)
      (spring n) (bareMass n) (inducedMass n))
    thetaCuspHawkingBornCausalFormFactor atTop
    GaloisForLFunctions.rightHalfPlane

/-- **[LEAN-PROVED] Positive-real limit rigidity.**  The exact theta Hawking form factor has
strictly positive real part throughout the causal half-plane under the UV-transparent KMS/FDT
limit.  Local uniform convergence gives weak sign; `XiC (i/2) = 1/2` supplies the strict anchor. -/
theorem thetaCuspHawkingBornCausalFormFactor_re_pos_of_UVTransparentKMSFDTLimit
    (model : ThetaCuspHawkingUVTransparentKMSFDTImpedanceLimit)
    {p : ℂ} (hp : 0 < p.re) :
    0 < (thetaCuspHawkingBornCausalFormFactor p).re := by
  let U := GaloisForLFunctions.rightHalfPlane
  have hnonneg : ∀ z ∈ U,
      0 ≤ (thetaCuspHawkingBornCausalFormFactor z).re :=
    GaloisForLFunctions.HTGeometry.re_nonneg_of_tendstoLocallyUniformlyOn
      model.converges (Filter.Eventually.of_forall fun n z hz =>
        (thetaCuspHawkingFiniteKMSFDTImpedance_re_pos
          (model.beta n) (model.energy n) (model.amplitude n)
          (model.spring n) (model.bareMass n) (model.inducedMass n)
          (model.beta_nonneg n) (model.spring_nonneg n) (model.mass_margin n)
          hz).le)
  have hdiff : DifferentiableOn ℂ thetaCuspHawkingBornCausalFormFactor U := by
    intro z hz
    unfold thetaCuspHawkingBornCausalFormFactor
    simpa [Function.comp_def] using
      ((differentiable_thetaCuspFourierLaplace_all
        ((Complex.I : ℂ) * z)).comp z
          ((differentiableAt_const (c := Complex.I)).mul
            differentiableAt_id)).differentiableWithinAt
  have hhalfMem : ((1 / 2 : ℝ) : ℂ) ∈ U := by
    exact GaloisForLFunctions.ofReal_mem_rightHalfPlane (by norm_num)
  have hhalfPos : 0 <
      (thetaCuspHawkingBornCausalFormFactor ((1 / 2 : ℝ) : ℂ)).re := by
    rw [thetaCuspHawkingBornCausalFormFactor,
      thetaCuspFourierLaplace_eq_XiC_all,
      show Complex.I * (((1 / 2 : ℝ) : ℂ)) = Complex.I / 2 by
        congr 1
        norm_num,
      XiC_I_half_eq]
    norm_num
  exact GaloisForLFunctions.HTGeometry.re_pos_of_re_nonneg_of_exists_pos
    GaloisForLFunctions.isOpen_rightHalfPlane
    (convex_halfSpace_re_gt 0).isPreconnected
    hdiff hnonneg hhalfMem hhalfPos p hp

/-- The source-normalized theta Hawking response has no causal right-half-plane zero under the
UV-transparent KMS/FDT limit. -/
theorem thetaCuspHawkingBornCausalFormFactor_ne_zero_of_UVTransparentKMSFDTLimit
    (model : ThetaCuspHawkingUVTransparentKMSFDTImpedanceLimit)
    {p : ℂ} (hp : 0 < p.re) :
    thetaCuspHawkingBornCausalFormFactor p ≠ 0 := by
  intro hzero
  have hpos :=
    thetaCuspHawkingBornCausalFormFactor_re_pos_of_UVTransparentKMSFDTLimit
      model hp
  rw [hzero] at hpos
  simp at hpos

/-! ## Boundary-sign obstruction -/

/-- **[PAPER-PROVED] [LEAN-PROVED] Raw-impedance boundary consequence.**  A hypothetical
UV-transparent impedance limit would force the completed Xi function to be nonnegative on the
whole real axis. -/
theorem Xi_nonneg_of_thetaCuspHawkingUVTransparentKMSFDTImpedanceLimit
    (model : ThetaCuspHawkingUVTransparentKMSFDTImpedanceLimit)
    (t : ℝ) :
    0 ≤ Xi t := by
  let p : ℕ → ℂ := fun n =>
    (((1 : ℝ) / (n + 1) : ℝ) : ℂ) - Complex.I * (t : ℂ)
  have hp : ∀ n, 0 < (p n).re := by
    intro n
    simp only [p, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero]
    positivity
  have hnonneg : ∀ n, 0 ≤ (XiC (Complex.I * p n)).re := by
    intro n
    have hpos :=
      thetaCuspHawkingBornCausalFormFactor_re_pos_of_UVTransparentKMSFDTLimit
        model (hp n)
    rw [thetaCuspHawkingBornCausalFormFactor,
      thetaCuspFourierLaplace_eq_XiC_all] at hpos
    exact hpos.le
  have hpinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpzero : Tendsto p atTop (nhds (-(Complex.I * (t : ℂ)))) := by
    have hcast : Tendsto
        (fun n : ℕ => (((1 : ℝ) / (n + 1) : ℝ) : ℂ)) atTop (nhds 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hpinv
    simpa only [p, zero_sub] using
      hcast.sub_const (Complex.I * (t : ℂ))
  have harg : Tendsto (fun n => Complex.I * p n) atTop (nhds (t : ℂ)) := by
    have hmul : Tendsto (fun n => Complex.I * p n) atTop
        (nhds (Complex.I * (-(Complex.I * (t : ℂ))))) :=
      tendsto_const_nhds.mul hpzero
    simpa only [mul_neg, ← mul_assoc, Complex.I_mul_I, neg_mul,
      one_mul, neg_neg] using hmul
  have hlim : Tendsto (fun n => (XiC (Complex.I * p n)).re) atTop
      (nhds (XiC (t : ℂ)).re) :=
    (Complex.continuous_re.tendsto _).comp
      (((XiC_analytic (t : ℂ) (Set.mem_univ _)).continuousAt.tendsto).comp harg)
  have hXi : 0 ≤ (XiC (t : ℂ)).re :=
    isClosed_Ici.mem_of_tendsto hlim
      (Filter.Eventually.of_forall hnonneg)
  simpa only [XiC_ofReal, Complex.ofReal_re] using hXi

/-- **[FALSIFIED] [LEAN-PROVED] Raw-amplitude impedance no-go.**  Hardy sign oscillation
contradicts the global boundary nonnegativity forced by a positive-real approximation. -/
theorem not_nonempty_thetaCuspHawkingUVTransparentKMSFDTImpedanceLimit :
    ¬ Nonempty ThetaCuspHawkingUVTransparentKMSFDTImpedanceLimit := by
  rintro ⟨model⟩
  refine false_of_hardyXiDensity_tail_sign (W := 1) (σ := -1)
    (by norm_num) (by norm_num) ?_
  intro w _hw
  have hXi : 0 ≤ Xi (4 * Real.pi * w) :=
    Xi_nonneg_of_thetaCuspHawkingUVTransparentKMSFDTImpedanceLimit
      model (4 * Real.pi * w)
  rw [neg_one_mul, neg_nonneg, hardyXiDensity]
  have hden : 0 ≤ (4 * Real.pi * w) ^ 2 + 1 / 4 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hXi]) hden

/-- **[LEAN-PROVED] UV stability excludes positive horizon charge.**  A positive-charge theta
backreaction resonance would be a forbidden zero of the positive-real limiting impedance. -/
theorem no_positive_thetaCuspHawkingHorizonCharge_of_UVTransparentKMSFDTLimit
    (model : ThetaCuspHawkingUVTransparentKMSFDTImpedanceLimit)
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hpos : 0 < thetaCuspHawkingBackreactionHorizonCharge r) : False := by
  have hp : 0 < (thetaCuspHawkingCausalZero r).re := by
    rw [thetaCuspHawkingCausalZero_re,
      ← thetaCuspHawkingBackreactionHorizonCharge_eq_im]
    exact hpos
  exact
    (thetaCuspHawkingBornCausalFormFactor_ne_zero_of_UVTransparentKMSFDTLimit
      model hp)
      (thetaCuspHawkingBornCausalFormFactor_resonance_zero r)

/-- **[FALSIFIED] Vacuous raw-amplitude Hawking-impedance endpoint.**  The implication is valid,
but its premise is uninhabited by the boundary-sign obstruction above. -/
theorem riemannHypothesis_of_thetaCuspHawkingUVTransparentKMSFDTImpedanceLimit
    (model : ThetaCuspHawkingUVTransparentKMSFDTImpedanceLimit) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real]
  intro alpha hres
  let r : ThetaCuspHawkingBackreactionResonantMode := ⟨alpha, hres⟩
  have hnonpos : r.1.im ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    exact
      no_positive_thetaCuspHawkingHorizonCharge_of_UVTransparentKMSFDTLimit
        model r (by
          rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im]
          exact hpos)
  let rr := thetaCuspHawkingBackreactionReflectedResonantMode r
  have hrefNonpos : rr.1.im ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    exact
      no_positive_thetaCuspHawkingHorizonCharge_of_UVTransparentKMSFDTLimit
        model rr (by
          rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im]
          exact hpos)
  rw [thetaCuspHawkingBackreactionReflectedResonantMode_im] at hrefNonpos
  change alpha.im = 0
  dsimp only [r] at hnonpos
  linarith

end RHTower
