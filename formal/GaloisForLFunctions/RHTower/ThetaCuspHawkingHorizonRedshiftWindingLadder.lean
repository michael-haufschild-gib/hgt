import GaloisForLFunctions.RHTower.ThetaCuspHawkingHorizonRedshiftPassivityEndpoint

/-!
# Fulling--Davies horizon winding ladder and cold-horizon dark cascade

This module keeps the actual exponential-horizon scattering phase

`exp(i eta exp(-kappa v))`

to every order in outgoing eikonal parameter `eta`.  The `n`-th derivative inserts the `n`-fold
horizon redshift `exp(-n kappa v)`, giving the exact, nonperturbative jet law

`d^n/deta^n A_kappa(0, omega) = i^n XiC(omega - i n kappa)`.

This exposes a Hawking-native resonance phenomenon absent from fixed mass-dilation and cubic-shell
routes.  A lower-half-plane theta resonance `omega` makes every positive winding order dark at
surface gravity

`kappa_n = -Im(omega) / n`.

Thus false RH produces an infinite hierarchy of invisible deformation jets accumulating toward the
zero-surface-gravity, cold end of the Hawking family: the large-mass limit for Schwarzschild and an
extremal analogue for charged or rotating holes.  Conversely, observability of every real-carrier
winding throughout positive-surface-gravity evaporation is exactly RH.

**[PAPER-PROVED] [LEAN-PROVED]** All differentiation, integrability, shifted-Xi identities, dark
cascade, and RH equivalence below are unconditional.

**[OPEN PHYSICAL PRODUCER]** Scattering theory does not generically forbid transmission zeros.
One still needs a theta-specific horizon observability or phase-sensitive optical theorem showing
that gravitational backreaction cannot hide a nonzero mirror-deformation jet.  KMS, CCR, Krein,
unitarity, and canonical Cayley completion alone do not imply that law.

**[CONJECTURAL NEXT TEST]** In the present dimensionless theta-source clock and at real carrier zero,
complex-`eta` analyticity should change sharply at `kappa = 2`: entire for `kappa < 2`, radius `pi`
at `kappa = 2`, and zero Taylor radius for `kappa > 2`.  This comes from competition between horizon
peeling `exp(kappa |v|)` and the first theta atom `exp(-pi exp(2 |v|))`; it is deliberately not
asserted as a theorem here.
-/

open Complex Real MeasureTheory Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open HedenmalmThetaSource

def thetaCuspHawkingHorizonRedshiftWindingFactor
    (n : ℕ) (kappa v : ℝ) : ℂ :=
  (Complex.I * ((Real.exp (-kappa * v) : ℝ) : ℂ)) ^ n

def thetaCuspHawkingHorizonRedshiftWindingAmplitude
    (n : ℕ) (kappa eta : ℝ) (omega : ℂ) : ℂ :=
  ∫ v : ℝ, thetaCuspHawkingHorizonRedshiftPhase kappa eta v *
    thetaCuspHawkingHorizonRedshiftWindingFactor n kappa v *
      thetaCuspFourierLaplaceIntegrand omega v

theorem norm_thetaCuspHawkingHorizonRedshiftWindingFactor
    (n : ℕ) (kappa v : ℝ) :
    ‖thetaCuspHawkingHorizonRedshiftWindingFactor n kappa v‖ =
      Real.exp (-((n : ℝ) * kappa) * v) := by
  rw [thetaCuspHawkingHorizonRedshiftWindingFactor, norm_pow, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  congr 1
  ring

private theorem integrable_horizonRedshiftWindingMajorant
    (n : ℕ) (kappa : ℝ) (omega : ℂ) :
    Integrable (fun v : ℝ =>
      Real.exp (-((n : ℝ) * kappa) * v) *
        ‖thetaCuspFourierLaplaceIntegrand omega v‖) := by
  have h := HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource
    (omega.im - (n : ℝ) * kappa)
  convert h using 1
  funext v
  rw [thetaCuspFourierLaplaceIntegrand, norm_mul, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs]
  have hsource : 0 ≤ thetaCuspFullSource v :=
    (thetaCuspFullSource_pos_all v).le
  rw [abs_of_nonneg hsource]
  have hre : (-Complex.I * omega * (v : ℂ)).re = omega.im * v := by
    simp [Complex.mul_re]
  rw [hre, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem integrable_horizonRedshiftWindingDensity
    (n : ℕ) (kappa : ℝ) (omega : ℂ) :
    Integrable (fun v : ℝ =>
      thetaCuspHawkingHorizonRedshiftWindingFactor n kappa v *
        thetaCuspFourierLaplaceIntegrand omega v) := by
  have hmajor := integrable_horizonRedshiftWindingMajorant n kappa omega
  apply Integrable.mono hmajor
  · exact ((by
      unfold thetaCuspHawkingHorizonRedshiftWindingFactor
      fun_prop : Continuous (fun v : ℝ =>
        thetaCuspHawkingHorizonRedshiftWindingFactor n kappa v))).aestronglyMeasurable.mul
        (integrable_thetaCuspFourierLaplaceIntegrand_all omega).aestronglyMeasurable
  · filter_upwards with v
    rw [norm_mul, norm_thetaCuspHawkingHorizonRedshiftWindingFactor]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]

theorem hasDerivAt_thetaCuspHawkingHorizonRedshiftWindingAmplitude
    (n : ℕ) (kappa eta : ℝ) (omega : ℂ) :
    HasDerivAt (fun t : ℝ =>
      thetaCuspHawkingHorizonRedshiftWindingAmplitude n kappa t omega)
      (thetaCuspHawkingHorizonRedshiftWindingAmplitude (n + 1) kappa eta omega) eta := by
  let m : ℝ → ℝ → ℂ := thetaCuspHawkingHorizonRedshiftPhase kappa
  let m' : ℝ → ℝ → ℂ := fun t v =>
    thetaCuspHawkingHorizonRedshiftPhase kappa t v *
      thetaCuspHawkingHorizonRedshiftWindingFactor 1 kappa v
  let h : ℝ → ℂ := fun v =>
    thetaCuspHawkingHorizonRedshiftWindingFactor n kappa v *
      thetaCuspFourierLaplaceIntegrand omega v
  let g : ℝ → ℝ := fun v => Real.exp (-kappa * v)
  have hmcont (t : ℝ) : Continuous (fun v => m t v) := by
    dsimp only [m]
    unfold thetaCuspHawkingHorizonRedshiftPhase
    fun_prop
  have hm_meas (t : ℝ) : AEStronglyMeasurable (fun v => m t v * h v) :=
    (hmcont t).aestronglyMeasurable.mul
      (integrable_horizonRedshiftWindingDensity n kappa omega).aestronglyMeasurable
  have hm_int : Integrable (fun v => m eta v * h v) := by
    apply (integrable_horizonRedshiftWindingDensity n kappa omega).bdd_mul
      ((hmcont eta).aestronglyMeasurable)
    filter_upwards with v
    dsimp only [m]
    rw [norm_thetaCuspHawkingHorizonRedshiftPhase]
  have hm'_meas : AEStronglyMeasurable (fun v => m' eta v * h v) := by
    have hm'cont : Continuous (fun v => m' eta v) := by
      dsimp only [m']
      unfold thetaCuspHawkingHorizonRedshiftPhase
        thetaCuspHawkingHorizonRedshiftWindingFactor
      fun_prop
    exact hm'cont.aestronglyMeasurable.mul
      (integrable_horizonRedshiftWindingDensity n kappa omega).aestronglyMeasurable
  have hderiv (t v : ℝ) : HasDerivAt (fun r : ℝ => m r v) (m' t v) t := by
    simpa [m, m', thetaCuspHawkingHorizonRedshiftWindingFactor] using
      hasDerivAt_thetaCuspHawkingHorizonRedshiftPhase kappa t v
  have hbound (t v : ℝ) : ‖m' t v‖ ≤ g v := by
    dsimp only [m', g]
    rw [norm_mul, norm_thetaCuspHawkingHorizonRedshiftPhase,
      one_mul, norm_thetaCuspHawkingHorizonRedshiftWindingFactor]
    simp
  have hg : Integrable (fun v => g v * ‖h v‖) := by
    have hmajor := integrable_horizonRedshiftWindingMajorant (n + 1) kappa omega
    convert hmajor using 1
    funext v
    dsimp only [g, h]
    rw [norm_mul, norm_thetaCuspHawkingHorizonRedshiftWindingFactor]
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hmain := hasDerivAt_integral_symbol (μ := volume) (m := m) (m' := m')
    (h := h) (g := g) eta hm_meas hm_int hm'_meas hderiv hbound hg
  convert hmain using 1
  · funext t
    unfold thetaCuspHawkingHorizonRedshiftWindingAmplitude
    apply integral_congr_ae
    filter_upwards with v
    dsimp only [m, h]
    ring
  · apply integral_congr_ae
    filter_upwards with v
    dsimp only [m', h]
    unfold thetaCuspHawkingHorizonRedshiftWindingFactor
    rw [pow_succ']
    ring

theorem thetaCuspHawkingHorizonRedshiftWindingFactor_eq
    (n : ℕ) (kappa v : ℝ) :
    thetaCuspHawkingHorizonRedshiftWindingFactor n kappa v =
      Complex.I ^ n *
        Complex.exp (-((((n : ℝ) * kappa * v : ℝ) : ℂ))) := by
  unfold thetaCuspHawkingHorizonRedshiftWindingFactor
  rw [mul_pow]
  congr 1
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

theorem thetaCuspHawkingHorizonRedshiftWindingAmplitude_zero
    (n : ℕ) (kappa : ℝ) (omega : ℂ) :
    thetaCuspHawkingHorizonRedshiftWindingAmplitude n kappa 0 omega =
      Complex.I ^ n *
        XiC (omega - (((n : ℝ) * kappa : ℝ) : ℂ) * Complex.I) := by
  rw [← thetaCuspFourierLaplace_eq_XiC_all,
    thetaCuspFourierLaplace, ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  rw [thetaCuspHawkingHorizonRedshiftPhase,
    thetaCuspHawkingHorizonRedshiftWindingFactor_eq,
    thetaCuspFourierLaplaceIntegrand,
    thetaCuspFourierLaplaceIntegrand]
  simp only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  have hexponent :
      -((((n : ℝ) * kappa * v : ℝ) : ℂ)) +
          (-Complex.I * omega * (v : ℂ)) =
        -Complex.I *
          (omega - (((n : ℝ) * kappa : ℝ) : ℂ) * Complex.I) * (v : ℂ) := by
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  calc
    Complex.I ^ n * Complex.exp (-((((n : ℝ) * kappa * v : ℝ) : ℂ))) *
          (Complex.exp (-Complex.I * omega * (v : ℂ)) *
            (thetaCuspFullSource v : ℂ)) =
        Complex.I ^ n *
          (Complex.exp (-((((n : ℝ) * kappa * v : ℝ) : ℂ))) *
            Complex.exp (-Complex.I * omega * (v : ℂ))) *
          (thetaCuspFullSource v : ℂ) := by ring
    _ = Complex.I ^ n *
          (Complex.exp (-Complex.I *
            (omega - (((n : ℝ) * kappa : ℝ) : ℂ) * Complex.I) * (v : ℂ)) *
          (thetaCuspFullSource v : ℂ)) := by
      rw [← Complex.exp_add, hexponent]
      ring

theorem iteratedDeriv_thetaCuspHawkingHorizonRedshiftAmplitude_eq_winding
    (n : ℕ) (kappa eta : ℝ) (omega : ℂ) :
    iteratedDeriv n
        (fun t : ℝ => thetaCuspHawkingHorizonRedshiftAmplitude kappa t omega) eta =
      thetaCuspHawkingHorizonRedshiftWindingAmplitude n kappa eta omega := by
  induction n generalizing eta with
  | zero =>
      simp only [iteratedDeriv_zero]
      unfold thetaCuspHawkingHorizonRedshiftAmplitude
        thetaCuspHawkingHorizonRedshiftWindingAmplitude
        thetaCuspHawkingHorizonRedshiftWindingFactor
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq :
          iteratedDeriv n
              (fun t : ℝ => thetaCuspHawkingHorizonRedshiftAmplitude kappa t omega) =
            fun t : ℝ =>
              thetaCuspHawkingHorizonRedshiftWindingAmplitude n kappa t omega := by
        funext t
        exact ih t
      rw [heq]
      exact (hasDerivAt_thetaCuspHawkingHorizonRedshiftWindingAmplitude
        n kappa eta omega).deriv

/-- Exact all-winding Fulling--Davies scattering jet. -/
theorem iteratedDeriv_thetaCuspHawkingHorizonRedshiftAmplitude_zero
    (n : ℕ) (kappa : ℝ) (omega : ℂ) :
    iteratedDeriv n
        (fun eta : ℝ => thetaCuspHawkingHorizonRedshiftAmplitude kappa eta omega) 0 =
      Complex.I ^ n *
        XiC (omega - (((n : ℝ) * kappa : ℝ) : ℂ) * Complex.I) := by
  rw [iteratedDeriv_thetaCuspHawkingHorizonRedshiftAmplitude_eq_winding,
    thetaCuspHawkingHorizonRedshiftWindingAmplitude_zero]

/-- Surface gravity at which winding order `n` sees a lower-half-plane resonance. -/
def thetaCuspHawkingDarkWindingSurfaceGravity (n : ℕ) (omega : ℂ) : ℝ :=
  -omega.im / (n : ℝ)

theorem thetaCuspHawkingDarkWindingSurfaceGravity_pos
    {n : ℕ} (hn : 0 < n) {omega : ℂ} (homega : omega.im < 0) :
    0 < thetaCuspHawkingDarkWindingSurfaceGravity n omega := by
  unfold thetaCuspHawkingDarkWindingSurfaceGravity
  exact div_pos (neg_pos.mpr homega) (Nat.cast_pos.mpr hn)

theorem thetaCuspHawkingDarkWinding_shift_eq
    {n : ℕ} (hn : 0 < n) (omega : ℂ) :
    (omega.re : ℂ) -
        ((((n : ℝ) * thetaCuspHawkingDarkWindingSurfaceGravity n omega : ℝ) : ℂ) *
          Complex.I) =
      omega := by
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr hn.ne')
  apply Complex.ext
  · simp
  · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero]
    unfold thetaCuspHawkingDarkWindingSurfaceGravity
    field_simp
    simp

/-- One lower-half-plane resonance creates a dark Hawking jet at every positive winding order. -/
theorem thetaCuspHawking_extremalDarkWindingCascade
    {omega : ℂ} (homega : XiC omega = 0) {n : ℕ} (hn : 0 < n) :
    iteratedDeriv n
        (fun eta : ℝ => thetaCuspHawkingHorizonRedshiftAmplitude
          (thetaCuspHawkingDarkWindingSurfaceGravity n omega) eta (omega.re : ℂ)) 0 = 0 := by
  rw [iteratedDeriv_thetaCuspHawkingHorizonRedshiftAmplitude_zero,
    thetaCuspHawkingDarkWinding_shift_eq hn omega, homega, mul_zero]

/-- No real-carrier winding becomes dark anywhere along positive-surface-gravity evaporation. -/
def ThetaCuspHawkingEvaporationWindingObservable : Prop :=
  ∀ (n : ℕ) (kappa x : ℝ), 0 < n → 0 < kappa →
    iteratedDeriv n
      (fun eta : ℝ => thetaCuspHawkingHorizonRedshiftAmplitude kappa eta (x : ℂ)) 0 ≠ 0

/-- Exact RH receiver supplied by the full exponential-horizon winding ladder. -/
theorem thetaCuspHawkingEvaporationWindingObservable_iff_riemannHypothesis :
    ThetaCuspHawkingEvaporationWindingObservable ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hobservable omega homega
    by_contra him
    rcases lt_or_gt_of_ne him with himneg | himpos
    · have hkappa := thetaCuspHawkingDarkWindingSurfaceGravity_pos
          (n := 1) (by norm_num) himneg
      exact (hobservable 1
        (thetaCuspHawkingDarkWindingSurfaceGravity 1 omega) omega.re
        (by norm_num) hkappa)
        (thetaCuspHawking_extremalDarkWindingCascade homega (by norm_num))
    · have hnegim : (-omega).im < 0 := by
        change -omega.im < 0
        exact neg_lt_zero.mpr himpos
      have hnegzero : XiC (-omega) = 0 := by rw [XiC_even]; exact homega
      have hkappa := thetaCuspHawkingDarkWindingSurfaceGravity_pos
          (n := 1) (by norm_num) hnegim
      exact (hobservable 1
        (thetaCuspHawkingDarkWindingSurfaceGravity 1 (-omega)) (-omega).re
        (by norm_num) hkappa)
        (thetaCuspHawking_extremalDarkWindingCascade hnegzero (by norm_num))
  · intro hreal n kappa x hn hkappa
    rw [iteratedDeriv_thetaCuspHawkingHorizonRedshiftAmplitude_zero]
    apply mul_ne_zero (pow_ne_zero n Complex.I_ne_zero)
    intro hzero
    have him := hreal
      ((x : ℂ) - (((n : ℝ) * kappa : ℝ) : ℂ) * Complex.I) hzero
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      zero_sub] at him
    nlinarith

end RHTower
