import GaloisForLFunctions.HTGeometry.MassDispersionUnitExpansion
import GaloisForLFunctions.RHTower.ExponentialSumMeanSquareLower

/-!
# Finite-packet separation on the sub-square-root chirp schedule

On the schedule `a(u) = u^θ`, `t(u) = u^{1-θ}` with `1/3 < θ < 1/2`, the mass trace of a finite
conjugation-closed packet of spectral points detects criticality exactly.

Every point of the packet contributes `exp(−(σ+iu)√(a²+α²))`.  The principal-root expansion
`√(a²+α²) = a + α²/(2a) + O(a^{-3})` is exact up to the explicit remainder proved in
`MassDispersionUnitExpansion`, and `u·a^{-3} = u^{1−3θ} → 0`, so after removing the common factor
`exp(−(σ+iu)a)` each contribution is `exp(−iα²t/2)` up to a factor tending to one.  Writing
`α = R + iJ` gives `−iα²/2 = RJ − i(R²−J²)/2`, so the packet becomes a finite exponential sum in
`t` with real growth rates `RJ` and real frequencies `(R²−J²)/2`.

If every point is critical (`J = 0`) the dispersion is real and at least `a`, so the trace decays
like `e^{−σa}`.  If some point is off line, the top growth layer is a nonzero exponential sum with
positive coefficients, hence frequently bounded below by the Bohr--Cesàro mean square, while the
gain `e^{ct − σa} = e^{cu^{1−θ} − σu^θ}` diverges because `θ < 1/2`.
-/

open Filter Topology Complex GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **(24.100)** The sub-square-root mass gauge `a(u) = u^θ`. -/
def chirpGauge (theta u : ℝ) : ℝ := u ^ theta

/-- **(24.100)** The conjugate chirp time `t(u) = u/a(u) = u^{1-θ}`. -/
def chirpTime (theta u : ℝ) : ℝ := u ^ (1 - theta)

theorem chirpGauge_pos {theta u : ℝ} (hu : 0 < u) : 0 < chirpGauge theta u :=
  Real.rpow_pos_of_pos hu _

theorem chirpTime_mul_chirpGauge {theta u : ℝ} (hu : 0 < u) :
    chirpTime theta u * chirpGauge theta u = u := by
  rw [chirpTime, chirpGauge, ← Real.rpow_add hu]
  simp

/-- The mass trace of a finite packet along the chirp schedule. -/
def packetMassTrace (S : Finset ℂ) (m : ℂ → ℝ) (sigma theta u : ℝ) : ℂ :=
  ∑ alpha ∈ S, (m alpha : ℂ)
    * Complex.exp (-((sigma : ℂ) + (u : ℝ) * Complex.I)
        * Complex.sqrt (((chirpGauge theta u : ℝ) : ℂ) ^ 2 + alpha ^ 2))

/-! ## The critical packet decays -/

/-- For a critical point the dispersion is a real number at least the gauge. -/
theorem sqrt_gauge_of_im_eq_zero {a : ℝ} (ha : 0 < a) {alpha : ℂ} (hal : alpha.im = 0) :
    ∃ r : ℝ, a ≤ r ∧ Complex.sqrt ((a : ℂ) ^ 2 + alpha ^ 2) = (r : ℂ) := by
  have hre : alpha = ((alpha.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hal]
  have hz : ((a : ℂ) ^ 2 + alpha ^ 2) = (((a ^ 2 + alpha.re ^ 2 : ℝ)) : ℂ) := by
    apply Complex.ext <;>
      simp [pow_two, Complex.mul_re, Complex.mul_im, hal]
  have hnn : (0 : ℝ) ≤ a ^ 2 + alpha.re ^ 2 := by positivity
  refine ⟨Real.sqrt (a ^ 2 + alpha.re ^ 2), ?_, ?_⟩
  · have hle : a ^ 2 ≤ a ^ 2 + alpha.re ^ 2 := by nlinarith [sq_nonneg alpha.re]
    have hsq := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq ha.le] at hsq
  · rw [hz, Complex.sqrt_of_nonneg (by
      rw [Complex.zero_le_real]
      exact hnn), Complex.ofReal_re]

/-- **(24.105, easy half)** A critical packet has a decaying mass trace. -/
theorem tendsto_packetMassTrace_of_critical (S : Finset ℂ) (m : ℂ → ℝ) {sigma theta : ℝ}
    (hsigma : 0 < sigma) (htheta : 0 < theta)
    (hcrit : ∀ alpha ∈ S, alpha.im = 0) :
    Tendsto (fun u : ℝ => packetMassTrace S m sigma theta u) atTop (𝓝 0) := by
  set M : ℝ := ∑ alpha ∈ S, |m alpha| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hmaj : Tendsto (fun u : ℝ => M * Real.exp (-(sigma * chirpGauge theta u))) atTop (𝓝 0) := by
    have hrp : Tendsto (fun u : ℝ => u ^ theta) atTop atTop := tendsto_rpow_atTop htheta
    have hgauge : Tendsto (fun u : ℝ => sigma * chirpGauge theta u) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hsigma hrp
    have hneg : Tendsto (fun u : ℝ => -(sigma * chirpGauge theta u)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hgauge
    have hexp : Tendsto (fun u : ℝ => Real.exp (-(sigma * chirpGauge theta u))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    simpa using hexp.const_mul M
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hapos : 0 < chirpGauge theta u := chirpGauge_pos hu
  refine le_trans (norm_sum_le _ _) ?_
  rw [hM, Finset.sum_mul]
  refine Finset.sum_le_sum fun alpha halpha => ?_
  obtain ⟨r, hr, hreq⟩ := sqrt_gauge_of_im_eq_zero hapos (hcrit alpha halpha)
  rw [norm_mul, hreq, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hre : (-((sigma : ℂ) + (u : ℝ) * Complex.I) * (r : ℂ)).re = -(sigma * r) := by
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  rw [hre]
  have hmono : Real.exp (-(sigma * r)) ≤ Real.exp (-(sigma * chirpGauge theta u)) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hr hsigma.le
    linarith
  exact mul_le_mul_of_nonneg_left hmono (abs_nonneg _)


/-! ## The chirp normal form -/

/-- The exponential growth rate of a spectral point on the chirp clock. -/
def chirpGrowth (alpha : ℂ) : ℝ := alpha.re * alpha.im

/-- The chirp frequency of a spectral point. -/
def chirpFreq (alpha : ℂ) : ℝ := (alpha.re ^ 2 - alpha.im ^ 2) / 2

/-- **(24.102)** The quadratic chirp phase splits into growth and frequency. -/
theorem neg_I_mul_sq_div_two (alpha : ℂ) :
    -Complex.I * alpha ^ 2 / 2
      = (chirpGrowth alpha : ℝ) - Complex.I * (chirpFreq alpha : ℝ) := by
  apply Complex.ext <;>
    simp [chirpGrowth, chirpFreq, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The remainder of the principal-root expansion at the chirp gauge. -/
def chirpRemainder (theta u : ℝ) (alpha : ℂ) : ℂ :=
  Complex.sqrt (((chirpGauge theta u : ℝ) : ℂ) ^ 2 + alpha ^ 2)
    - (((chirpGauge theta u : ℝ) : ℂ)
      + ((1 / (2 * chirpGauge theta u) : ℝ) : ℂ) * alpha ^ 2)

theorem norm_chirpRemainder_le {theta u : ℝ} (hu : 0 < u) {alpha : ℂ}
    (hsmall : ‖alpha‖ ^ 2 ≤ chirpGauge theta u ^ 2 / 2) :
    ‖chirpRemainder theta u alpha‖ ≤ ‖alpha‖ ^ 4 / (3 * chirpGauge theta u ^ 3) :=
  norm_sqrt_sq_add_sub_le (chirpGauge_pos hu) hsmall

/-- The multiplicative defect of the chirp normal form at one spectral point. -/
def chirpDefect (sigma theta u : ℝ) (alpha : ℂ) : ℂ :=
  Complex.exp (-(((sigma / (2 * chirpGauge theta u) : ℝ)) : ℂ) * alpha ^ 2
    - ((sigma : ℂ) + (u : ℝ) * Complex.I) * chirpRemainder theta u alpha)

theorem chirpGauge_pow_eq {theta u : ℝ} (hu : 0 < u) (n : ℕ) :
    chirpGauge theta u ^ n = u ^ (theta * n) := by
  rw [chirpGauge, ← Real.rpow_natCast (u ^ theta) n, ← Real.rpow_mul hu.le]

theorem tendsto_chirpGauge_inv {theta : ℝ} (htheta : 0 < theta) :
    Tendsto (fun u : ℝ => 1 / chirpGauge theta u) atTop (𝓝 0) := by
  have hneg : Tendsto (fun u : ℝ => u ^ (-theta)) atTop (𝓝 0) := tendsto_rpow_neg_atTop htheta
  refine hneg.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [chirpGauge, Real.rpow_neg hu.le, one_div]

theorem tendsto_chirpTail {sigma theta : ℝ} (h3 : 1 / 3 < theta) :
    Tendsto (fun u : ℝ => (sigma + u) / (3 * chirpGauge theta u ^ 3)) atTop (𝓝 0) := by
  have htheta : 0 < theta := by linarith
  have hpow : Tendsto (fun u : ℝ => u ^ (-(3 * theta))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hpow2 : Tendsto (fun u : ℝ => u ^ (1 - 3 * theta)) atTop (𝓝 0) := by
    have heq : (1 : ℝ) - 3 * theta = -(3 * theta - 1) := by ring
    rw [funext fun u : ℝ => congrArg (fun e : ℝ => u ^ e) heq]
    exact tendsto_rpow_neg_atTop (by linarith)
  have hsum : Tendsto (fun u : ℝ => (sigma / 3) * u ^ (-(3 * theta))
      + (1 / 3) * u ^ (1 - 3 * theta)) atTop (𝓝 0) := by
    have := (hpow.const_mul (sigma / 3)).add (hpow2.const_mul (1 / 3))
    simpa using this
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hg : chirpGauge theta u ^ 3 = u ^ (theta * 3) := chirpGauge_pow_eq hu 3
  have hgpos : (0 : ℝ) < u ^ (theta * 3) := Real.rpow_pos_of_pos hu _
  have h1 : u ^ (-(3 * theta)) = 1 / u ^ (theta * 3) := by
    rw [show -(3 * theta) = -(theta * 3) by ring, Real.rpow_neg hu.le, one_div]
  have h2 : u ^ (1 - 3 * theta) = u / u ^ (theta * 3) := by
    rw [show (1 : ℝ) - 3 * theta = 1 + -(theta * 3) by ring, Real.rpow_add hu,
      Real.rpow_neg hu.le, Real.rpow_one]
    ring
  rw [hg, h1, h2]
  field_simp


theorem eventually_small_alpha {theta : ℝ} (htheta : 0 < theta) (alpha : ℂ) :
    ∀ᶠ u : ℝ in atTop, ‖alpha‖ ^ 2 ≤ chirpGauge theta u ^ 2 / 2 := by
  have hpow : Tendsto (fun u : ℝ => u ^ (theta * 2)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  have hsq : Tendsto (fun u : ℝ => chirpGauge theta u ^ 2) atTop atTop := by
    refine hpow.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact (chirpGauge_pow_eq hu 2).symm
  exact (hsq.atTop_div_const (by norm_num)).eventually_ge_atTop _

/-- **(24.101)** The chirp defect tends to one: the principal-root remainder and the real part of
the quadratic term both vanish at the sub-square-root scale. -/
theorem tendsto_chirpDefect {sigma theta : ℝ} (hsigma : 0 < sigma) (h3 : 1 / 3 < theta)
    (alpha : ℂ) :
    Tendsto (fun u : ℝ => chirpDefect sigma theta u alpha) atTop (𝓝 1) := by
  have htheta : 0 < theta := by linarith
  have hmaj : Tendsto (fun u : ℝ =>
      (sigma * ‖alpha‖ ^ 2 / 2) * (1 / chirpGauge theta u)
        + ‖alpha‖ ^ 4 * ((sigma + u) / (3 * chirpGauge theta u ^ 3))) atTop (𝓝 0) := by
    have h1 := (tendsto_chirpGauge_inv htheta).const_mul (sigma * ‖alpha‖ ^ 2 / 2)
    have h2 := (tendsto_chirpTail (sigma := sigma) h3).const_mul (‖alpha‖ ^ 4)
    simpa using h1.add h2
  have hexp : Tendsto (fun u : ℝ =>
      -(((sigma / (2 * chirpGauge theta u) : ℝ)) : ℂ) * alpha ^ 2
        - ((sigma : ℂ) + (u : ℝ) * Complex.I) * chirpRemainder theta u alpha)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_small_alpha htheta alpha] with u hu hsm
    have hapos : 0 < chirpGauge theta u := chirpGauge_pos hu
    have hfirst : ‖-(((sigma / (2 * chirpGauge theta u) : ℝ)) : ℂ) * alpha ^ 2‖
        = (sigma * ‖alpha‖ ^ 2 / 2) * (1 / chirpGauge theta u) := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity), norm_pow]
      field_simp
    have hcoef : ‖((sigma : ℂ) + (u : ℝ) * Complex.I)‖ ≤ sigma + u := by
      refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp [abs_of_pos hsigma, abs_of_pos hu]
    have hsecond : ‖((sigma : ℂ) + (u : ℝ) * Complex.I) * chirpRemainder theta u alpha‖
        ≤ ‖alpha‖ ^ 4 * ((sigma + u) / (3 * chirpGauge theta u ^ 3)) := by
      rw [norm_mul]
      have hrem := norm_chirpRemainder_le hu hsm
      have hstep : ‖((sigma : ℂ) + (u : ℝ) * Complex.I)‖ * ‖chirpRemainder theta u alpha‖
          ≤ (sigma + u) * (‖alpha‖ ^ 4 / (3 * chirpGauge theta u ^ 3)) :=
        mul_le_mul hcoef hrem (norm_nonneg _) (by linarith)
      refine le_trans hstep ?_
      rw [le_iff_eq_or_lt]
      left
      field_simp
    calc ‖-(((sigma / (2 * chirpGauge theta u) : ℝ)) : ℂ) * alpha ^ 2
            - ((sigma : ℂ) + (u : ℝ) * Complex.I) * chirpRemainder theta u alpha‖
        ≤ ‖-(((sigma / (2 * chirpGauge theta u) : ℝ)) : ℂ) * alpha ^ 2‖
            + ‖((sigma : ℂ) + (u : ℝ) * Complex.I) * chirpRemainder theta u alpha‖ :=
          norm_sub_le _ _
      _ ≤ (sigma * ‖alpha‖ ^ 2 / 2) * (1 / chirpGauge theta u)
            + ‖alpha‖ ^ 4 * ((sigma + u) / (3 * chirpGauge theta u ^ 3)) := by
          rw [hfirst]
          linarith [hsecond]
  have hcont := (Complex.continuous_exp.tendsto 0).comp hexp
  simpa [chirpDefect, Function.comp_def] using hcont


/-- **(24.102)** The square of a spectral point in growth/frequency coordinates. -/
theorem sq_eq_freq_add_growth (alpha : ℂ) :
    alpha ^ 2 = 2 * (chirpFreq alpha : ℝ) + 2 * Complex.I * (chirpGrowth alpha : ℝ) := by
  apply Complex.ext <;>
    simp [chirpFreq, chirpGrowth, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem sqrt_eq_add_chirpRemainder (theta u : ℝ) (alpha : ℂ) :
    Complex.sqrt (((chirpGauge theta u : ℝ) : ℂ) ^ 2 + alpha ^ 2)
      = ((chirpGauge theta u : ℝ) : ℂ)
        + ((1 / (2 * chirpGauge theta u) : ℝ) : ℂ) * alpha ^ 2
        + chirpRemainder theta u alpha := by
  rw [chirpRemainder]
  ring

/-- **(24.101)** The exponent of one packet term in chirp normal form. -/
theorem chirp_exponent_identity {sigma theta c u : ℝ} (hu : 0 < u) (alpha : ℂ) :
    -((sigma : ℂ) + (u : ℝ) * Complex.I)
        * Complex.sqrt (((chirpGauge theta u : ℝ) : ℂ) ^ 2 + alpha ^ 2)
      + ((sigma : ℂ) + (u : ℝ) * Complex.I) * ((chirpGauge theta u : ℝ) : ℂ)
      + (-((c * chirpTime theta u : ℝ) : ℂ))
    = (((chirpGrowth alpha - c) * chirpTime theta u : ℝ) : ℂ)
      + (-Complex.I * (chirpFreq alpha : ℝ) * ((chirpTime theta u : ℝ) : ℂ))
      + (-(((sigma / (2 * chirpGauge theta u) : ℝ)) : ℂ) * alpha ^ 2
        - ((sigma : ℂ) + (u : ℝ) * Complex.I) * chirpRemainder theta u alpha) := by
  have hapos : 0 < chirpGauge theta u := chirpGauge_pos hu
  have hane : ((chirpGauge theta u : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hapos
  have hut : ((u : ℝ) : ℂ)
      = ((chirpTime theta u : ℝ) : ℂ) * ((chirpGauge theta u : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, chirpTime_mul_chirpGauge hu]
  rw [sqrt_eq_add_chirpRemainder, sq_eq_freq_add_growth alpha]
  push_cast
  rw [hut]
  field_simp
  linear_combination (-(((chirpTime theta u : ℝ) : ℂ) * ((chirpGauge theta u : ℝ) : ℂ)
    * ((chirpGrowth alpha : ℝ) : ℂ))) * Complex.I_sq

/-- **(24.101)** The chirp normal form of one packet term. -/
theorem chirp_term_identity {sigma theta c u : ℝ} (hu : 0 < u) (alpha : ℂ) :
    Complex.exp (-((sigma : ℂ) + (u : ℝ) * Complex.I)
        * Complex.sqrt (((chirpGauge theta u : ℝ) : ℂ) ^ 2 + alpha ^ 2))
      * Complex.exp (((sigma : ℂ) + (u : ℝ) * Complex.I) * ((chirpGauge theta u : ℝ) : ℂ))
      * Complex.exp (-((c * chirpTime theta u : ℝ) : ℂ))
    = ((Real.exp ((chirpGrowth alpha - c) * chirpTime theta u) : ℝ) : ℂ)
      * Complex.exp (-Complex.I * (chirpFreq alpha : ℝ) * ((chirpTime theta u : ℝ) : ℂ))
      * chirpDefect sigma theta u alpha := by
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.ofReal_exp, chirpDefect,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  exact chirp_exponent_identity (c := c) hu alpha


/-! ## The top growth layer -/

/-- The packet trace with the common gauge factor and the top growth rate removed. -/
def shiftedPacketTrace (S : Finset ℂ) (m : ℂ → ℝ) (sigma theta c u : ℝ) : ℂ :=
  packetMassTrace S m sigma theta u
    * Complex.exp (((sigma : ℂ) + (u : ℝ) * Complex.I) * ((chirpGauge theta u : ℝ) : ℂ))
    * Complex.exp (-((c * chirpTime theta u : ℝ) : ℂ))

/-- The top growth layer of the packet. -/
def topLayer (S : Finset ℂ) (c : ℝ) : Finset ℂ :=
  S.filter (fun alpha => chirpGrowth alpha = c)

theorem shiftedPacketTrace_eq (S : Finset ℂ) (m : ℂ → ℝ) {sigma theta c u : ℝ} (hu : 0 < u) :
    shiftedPacketTrace S m sigma theta c u
      = ∑ alpha ∈ S, (m alpha : ℂ)
          * (((Real.exp ((chirpGrowth alpha - c) * chirpTime theta u) : ℝ) : ℂ)
            * Complex.exp (-Complex.I * (chirpFreq alpha : ℝ) * ((chirpTime theta u : ℝ) : ℂ))
            * chirpDefect sigma theta u alpha) := by
  rw [shiftedPacketTrace, packetMassTrace, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun alpha _ => ?_
  rw [← chirp_term_identity (c := c) hu alpha]
  ring

theorem tendsto_chirpTime_atTop {theta : ℝ} (h1 : theta < 1) :
    Tendsto (fun u : ℝ => chirpTime theta u) atTop atTop :=
  tendsto_rpow_atTop (by linarith)

theorem norm_exp_neg_I_mul_ofReal_finitePacketChirpSeparation (x y : ℝ) :
    ‖Complex.exp (-Complex.I * (x : ℝ) * ((y : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]


/-- **(24.103)** The shifted trace converges to the top-layer exponential sum. -/
theorem tendsto_shiftedPacketTrace_sub (S : Finset ℂ) (m : ℂ → ℝ) {sigma theta c : ℝ}
    (hsigma : 0 < sigma) (h3 : 1 / 3 < theta) (h1 : theta < 1)
    (hle : ∀ alpha ∈ S, chirpGrowth alpha ≤ c) :
    Tendsto (fun u : ℝ => shiftedPacketTrace S m sigma theta c u
        - ∑ alpha ∈ topLayer S c, (m alpha : ℂ)
            * Complex.exp (-Complex.I * (chirpFreq alpha : ℝ) * ((chirpTime theta u : ℝ) : ℂ)))
      atTop (𝓝 0) := by
  classical
  have htime := tendsto_chirpTime_atTop h1
  have hterm : ∀ alpha ∈ S, Tendsto (fun u : ℝ =>
      (m alpha : ℂ)
        * (((Real.exp ((chirpGrowth alpha - c) * chirpTime theta u) : ℝ) : ℂ)
          * Complex.exp (-Complex.I * (chirpFreq alpha : ℝ) * ((chirpTime theta u : ℝ) : ℂ))
          * chirpDefect sigma theta u alpha)
        - (if chirpGrowth alpha = c then
            (m alpha : ℂ)
              * Complex.exp (-Complex.I * (chirpFreq alpha : ℝ) * ((chirpTime theta u : ℝ) : ℂ))
          else 0)) atTop (𝓝 0) := by
    intro alpha halpha
    by_cases htop : chirpGrowth alpha = c
    · simp only [if_pos htop]
      have hzero : ∀ u : ℝ, (Real.exp ((chirpGrowth alpha - c) * chirpTime theta u) : ℝ) = 1 := by
        intro u
        rw [htop]
        simp
      have hdef := tendsto_chirpDefect (sigma := sigma) (theta := theta) hsigma h3 alpha
      have hbase : Tendsto (fun u : ℝ =>
          (m alpha : ℂ)
            * Complex.exp (-Complex.I * (chirpFreq alpha : ℝ) * ((chirpTime theta u : ℝ) : ℂ))
            * (chirpDefect sigma theta u alpha - 1)) atTop (𝓝 0) := by
        refine squeeze_zero_norm'
          (a := fun u : ℝ => ‖(m alpha : ℂ)‖ * ‖chirpDefect sigma theta u alpha - 1‖) ?_ ?_
        · filter_upwards with u
          rw [norm_mul, norm_mul, norm_exp_neg_I_mul_ofReal_finitePacketChirpSeparation, mul_one]
        · have hd : Tendsto (fun u : ℝ => ‖chirpDefect sigma theta u alpha - 1‖) atTop (𝓝 0) := by
            have := (hdef.sub_const 1).norm
            simpa using this
          have := hd.const_mul ‖(m alpha : ℂ)‖
          simpa using this
      refine hbase.congr fun u => ?_
      rw [hzero u]
      push_cast
      ring
    · simp only [if_neg htop, sub_zero]
      have hlt : chirpGrowth alpha - c < 0 := by
        have := hle alpha halpha
        rcases lt_or_eq_of_le this with h | h
        · linarith
        · exact absurd h htop
      have hdecay : Tendsto (fun u : ℝ =>
          Real.exp ((chirpGrowth alpha - c) * chirpTime theta u)) atTop (𝓝 0) := by
        have hpos : Tendsto (fun u : ℝ => (-(chirpGrowth alpha - c)) * chirpTime theta u)
            atTop atTop := Filter.Tendsto.const_mul_atTop (by linarith) htime
        have hmul : Tendsto (fun u : ℝ => (chirpGrowth alpha - c) * chirpTime theta u)
            atTop atBot := by
          have hneg : Tendsto (fun u : ℝ => -((-(chirpGrowth alpha - c)) * chirpTime theta u))
              atTop atBot := tendsto_neg_atTop_atBot.comp hpos
          refine hneg.congr fun u => ?_
          ring
        exact Real.tendsto_exp_atBot.comp hmul
      have hdef := tendsto_chirpDefect (sigma := sigma) (theta := theta) hsigma h3 alpha
      have hnormdef : Tendsto (fun u : ℝ => ‖chirpDefect sigma theta u alpha‖) atTop (𝓝 1) := by
        simpa using hdef.norm
      refine squeeze_zero_norm'
        (a := fun u : ℝ => ‖(m alpha : ℂ)‖ * (Real.exp ((chirpGrowth alpha - c) * chirpTime theta u)
          * ‖chirpDefect sigma theta u alpha‖)) ?_ ?_
      · filter_upwards with u
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          norm_exp_neg_I_mul_ofReal_finitePacketChirpSeparation, mul_one]
        rw [abs_of_pos (Real.exp_pos _)]
      · have := (hdecay.mul hnormdef).const_mul ‖(m alpha : ℂ)‖
        simpa using this
  have hsum := tendsto_finsetSum S hterm
  rw [Finset.sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [shiftedPacketTrace_eq S m hu, topLayer, Finset.sum_filter, ← Finset.sum_sub_distrib]


/-! ## The separation theorem -/

/-- **(24.103)** The frequency-grouped coefficients of the top growth layer. -/
def topCoeff (S : Finset ℂ) (m : ℂ → ℝ) (c om : ℝ) : ℂ :=
  ∑ alpha ∈ (topLayer S c).filter (fun alpha => chirpFreq alpha = om), (m alpha : ℂ)

theorem topLayer_sum_eq (S : Finset ℂ) (m : ℂ → ℝ) (c t : ℝ) :
    ∑ alpha ∈ topLayer S c, (m alpha : ℂ)
        * Complex.exp (-Complex.I * (chirpFreq alpha : ℝ) * ((t : ℝ) : ℂ))
      = expSum_exponentialSumMeanSquareLower ((topLayer S c).image chirpFreq) (topCoeff S m c) id t := by
  classical
  rw [expSum_exponentialSumMeanSquareLower]
  have hmaps : ∀ alpha ∈ topLayer S c, chirpFreq alpha ∈ (topLayer S c).image chirpFreq :=
    fun alpha ha => Finset.mem_image_of_mem _ ha
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun alpha => (m alpha : ℂ)
      * Complex.exp (-Complex.I * (chirpFreq alpha : ℝ) * ((t : ℝ) : ℂ)))]
  refine Finset.sum_congr rfl fun om hom => ?_
  rw [topCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun alpha ha => ?_
  rw [Finset.mem_filter] at ha
  rw [ha.2]
  rfl

theorem topCoeff_eq_ofReal (S : Finset ℂ) (m : ℂ → ℝ) (c om : ℝ) :
    topCoeff S m c om
      = ((∑ alpha ∈ (topLayer S c).filter (fun alpha => chirpFreq alpha = om), m alpha : ℝ) : ℂ) := by
  rw [topCoeff, Complex.ofReal_sum]

theorem topCoeff_norm_pos (S : Finset ℂ) (m : ℂ → ℝ) {c om : ℝ}
    (hm : ∀ alpha ∈ S, 0 < m alpha) (hom : om ∈ (topLayer S c).image chirpFreq) :
    0 < ‖topCoeff S m c om‖ := by
  classical
  obtain ⟨beta, hbeta, hbetaom⟩ := Finset.mem_image.1 hom
  have hbetaS : beta ∈ S := (Finset.mem_filter.1 hbeta).1
  have hmemfib : beta ∈ (topLayer S c).filter (fun alpha => chirpFreq alpha = om) :=
    Finset.mem_filter.2 ⟨hbeta, hbetaom⟩
  have hpos : 0 < ∑ alpha ∈ (topLayer S c).filter (fun alpha => chirpFreq alpha = om), m alpha := by
    refine Finset.sum_pos' (fun alpha ha => ?_) ⟨beta, hmemfib, hm beta hbetaS⟩
    exact le_of_lt (hm alpha ((Finset.mem_filter.1 (Finset.mem_filter.1 ha).1).1))
  rw [topCoeff_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact abs_pos.2 (ne_of_gt hpos)


/-- The mass gauge is eventually dominated by the chirp gain below the square-root threshold. -/
theorem tendsto_exp_chirpGap {sigma c theta : ℝ} (hc : 0 < c)
    (htheta : 0 < theta) (h2 : theta < 1 / 2) :
    Tendsto (fun u : ℝ => Real.exp (sigma * chirpGauge theta u - c * chirpTime theta u))
      atTop (𝓝 0) := by
  have hgap : Tendsto (fun u : ℝ => sigma * chirpGauge theta u - c * chirpTime theta u)
      atTop atBot := by
    have hneg : Tendsto (fun u : ℝ => -(chirpGauge theta u)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop htheta)
    refine tendsto_atBot_mono' _ ?_ hneg
    filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 1 - 2 * theta by linarith)).eventually_ge_atTop
      ((sigma + 1) / c), eventually_gt_atTop (0 : ℝ)] with u hu hu0
    have hapos : 0 < chirpGauge theta u := chirpGauge_pos hu0
    have hsplit : chirpTime theta u = u ^ (1 - 2 * theta) * chirpGauge theta u := by
      rw [chirpTime, chirpGauge, ← Real.rpow_add hu0]
      congr 1
      ring
    have h1 : sigma + 1 ≤ c * u ^ (1 - 2 * theta) := by
      rw [div_le_iff₀ hc] at hu
      linarith
    have h2' : (sigma + 1) * chirpGauge theta u
        ≤ (c * u ^ (1 - 2 * theta)) * chirpGauge theta u :=
      mul_le_mul_of_nonneg_right h1 hapos.le
    have hct : (sigma + 1) * chirpGauge theta u ≤ c * chirpTime theta u := by
      rw [hsplit]
      calc (sigma + 1) * chirpGauge theta u
          ≤ (c * u ^ (1 - 2 * theta)) * chirpGauge theta u := h2'
        _ = c * (u ^ (1 - 2 * theta) * chirpGauge theta u) := by ring
    linarith [hct]
  exact Real.tendsto_exp_atBot.comp hgap

/-- **(24.105, hard half)** A packet with an off-line point does not have a decaying mass trace. -/
theorem not_tendsto_packetMassTrace_of_offline (S : Finset ℂ) (m : ℂ → ℝ)
    {sigma theta : ℝ} (hsigma : 0 < sigma) (h3 : 1 / 3 < theta) (h2 : theta < 1 / 2)
    (hm : ∀ alpha ∈ S, 0 < m alpha)
    (hre : ∀ alpha ∈ S, 0 < alpha.re)
    (hconj : ∀ alpha ∈ S, (starRingEnd ℂ) alpha ∈ S)
    (hoff : ∃ alpha ∈ S, alpha.im ≠ 0) :
    ¬ Tendsto (fun u : ℝ => packetMassTrace S m sigma theta u) atTop (𝓝 0) := by
  classical
  intro htend
  have htheta : 0 < theta := by linarith
  have hth1 : theta < 1 := by linarith
  obtain ⟨alpha0, halpha0, hne0⟩ := hoff
  have hSne : S.Nonempty := ⟨alpha0, halpha0⟩
  set c : ℝ := S.sup' hSne chirpGrowth with hcdef
  have hle : ∀ alpha ∈ S, chirpGrowth alpha ≤ c := fun alpha ha => Finset.le_sup' _ ha
  have hcpos : 0 < c := by
    rcases lt_or_gt_of_ne hne0 with hneg | hpos
    · have hcj : (starRingEnd ℂ) alpha0 ∈ S := hconj alpha0 halpha0
      have hgrow : 0 < chirpGrowth ((starRingEnd ℂ) alpha0) := by
        rw [chirpGrowth, Complex.conj_re, Complex.conj_im]
        nlinarith [hre alpha0 halpha0, hneg]
      exact lt_of_lt_of_le hgrow (hle _ hcj)
    · have hgrow : 0 < chirpGrowth alpha0 := by
        rw [chirpGrowth]
        nlinarith [hre alpha0 halpha0, hpos]
      exact lt_of_lt_of_le hgrow (hle _ halpha0)
  obtain ⟨beta, hbetaS, hbeta⟩ := Finset.exists_mem_eq_sup' hSne chirpGrowth
  have htopne : (topLayer S c).Nonempty :=
    ⟨beta, Finset.mem_filter.2 ⟨hbetaS, hbeta.symm⟩⟩
  set F : Finset ℝ := (topLayer S c).image chirpFreq with hFdef
  have hFne : F.Nonempty := htopne.image _
  set Q : ℝ := ∑ om ∈ F, ‖topCoeff S m c om‖ ^ 2 with hQdef
  have hQpos : 0 < Q := by
    refine Finset.sum_pos (fun om hom => ?_) hFne
    exact pow_pos (topCoeff_norm_pos S m hm hom) 2
  set delta : ℝ := Real.sqrt (Q / 2) with hdeltadef
  have hdpos : 0 < delta := Real.sqrt_pos.2 (by linarith)
  have hdsq : delta ^ 2 = Q / 2 := Real.sq_sqrt (by linarith)
  have hdlt : delta ^ 2 < Q := by
    rw [hdsq]
    linarith
  have hfreq : ∃ᶠ t : ℝ in atTop, delta < ‖expSum_exponentialSumMeanSquareLower F (topCoeff S m c) id t‖ :=
    frequently_lt_norm_expSum F (topCoeff S m c) id Function.injective_id.injOn hdlt
  have hfreq' : ∃ᶠ u : ℝ in atTop,
      delta < ‖expSum_exponentialSumMeanSquareLower F (topCoeff S m c) id (chirpTime theta u)‖ := by
    rw [Filter.frequently_atTop] at hfreq ⊢
    intro A
    obtain ⟨t, ht, hQt⟩ := hfreq (max A 1 ^ (1 - theta))
    have hB1 : (1 : ℝ) ≤ max A 1 := le_max_right _ _
    have hB0 : (0 : ℝ) < max A 1 := lt_of_lt_of_le zero_lt_one hB1
    have hBp : (0 : ℝ) < max A 1 ^ (1 - theta) := Real.rpow_pos_of_pos hB0 _
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hBp ht
    have hinv : (0 : ℝ) < 1 / (1 - theta) := by positivity
    refine ⟨t ^ (1 / (1 - theta)), ?_, ?_⟩
    · have hmono : (max A 1 ^ (1 - theta)) ^ (1 / (1 - theta)) ≤ t ^ (1 / (1 - theta)) :=
        Real.rpow_le_rpow hBp.le ht hinv.le
      have hid : (max A 1 ^ (1 - theta)) ^ (1 / (1 - theta)) = max A 1 := by
        rw [← Real.rpow_mul hB0.le]
        rw [mul_one_div, div_self (by linarith : (1 : ℝ) - theta ≠ 0), Real.rpow_one]
      rw [hid] at hmono
      exact le_trans (le_max_left A 1) hmono
    · have hid : chirpTime theta (t ^ (1 / (1 - theta))) = t := by
        rw [chirpTime, ← Real.rpow_mul ht0.le, one_div,
          inv_mul_cancel₀ (by linarith : (1 : ℝ) - theta ≠ 0), Real.rpow_one]
      rw [hid]
      exact hQt
  have hnorm : ∀ u : ℝ, ‖shiftedPacketTrace S m sigma theta c u‖
      = ‖packetMassTrace S m sigma theta u‖
        * Real.exp (sigma * chirpGauge theta u - c * chirpTime theta u) := by
    intro u
    rw [shiftedPacketTrace, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, mul_assoc,
      ← Real.exp_add]
    congr 2
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
    ring
  have hshift : Tendsto (fun u : ℝ => shiftedPacketTrace S m sigma theta c u) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hprod := (htend.norm).mul (tendsto_exp_chirpGap (sigma := sigma) hcpos htheta h2)
    rw [mul_zero] at hprod
    refine hprod.congr fun u => ?_
    rw [hnorm u]
  have hsub := tendsto_shiftedPacketTrace_sub S m hsigma h3 hth1 hle
  have hzero : Tendsto (fun u : ℝ =>
      expSum_exponentialSumMeanSquareLower F (topCoeff S m c) id (chirpTime theta u)) atTop (𝓝 0) := by
    have hdiff := hshift.sub hsub
    rw [sub_zero] at hdiff
    refine hdiff.congr fun u => ?_
    rw [topLayer_sum_eq S m c (chirpTime theta u)]
    ring
  have heve : ∀ᶠ u : ℝ in atTop,
      ‖expSum_exponentialSumMeanSquareLower F (topCoeff S m c) id (chirpTime theta u)‖ < delta := by
    have hn : Tendsto (fun u : ℝ => ‖expSum_exponentialSumMeanSquareLower F (topCoeff S m c) id (chirpTime theta u)‖)
        atTop (𝓝 0) := by
      simpa using hzero.norm
    exact hn.eventually (gt_mem_nhds hdpos)
  obtain ⟨u, hu1, hu2⟩ := (hfreq'.and_eventually heve).exists
  linarith


/-- **(24.105) The exact finite-packet receiver.**  For a finite conjugation-closed packet of
mass-shifted spectral points with positive multiplicities, the chirp mass trace decays exactly when
every point of the packet is critical.  No zero-gap hypothesis and no pointwise phase limit is
used: the off-line case is settled by the Bohr--Cesàro mean square of the top growth layer. -/
theorem tendsto_packetMassTrace_iff_critical (S : Finset ℂ) (m : ℂ → ℝ)
    {sigma theta : ℝ} (hsigma : 0 < sigma) (h3 : 1 / 3 < theta) (h2 : theta < 1 / 2)
    (hm : ∀ alpha ∈ S, 0 < m alpha) (hre : ∀ alpha ∈ S, 0 < alpha.re)
    (hconj : ∀ alpha ∈ S, (starRingEnd ℂ) alpha ∈ S) :
    Tendsto (fun u : ℝ => packetMassTrace S m sigma theta u) atTop (𝓝 0)
      ↔ ∀ alpha ∈ S, alpha.im = 0 := by
  constructor
  · intro htend
    by_contra hcon
    push Not at hcon
    exact not_tendsto_packetMassTrace_of_offline S m hsigma h3 h2 hm hre hconj hcon htend
  · intro hcrit
    exact tendsto_packetMassTrace_of_critical S m hsigma (by linarith) hcrit


end

end RHTower
