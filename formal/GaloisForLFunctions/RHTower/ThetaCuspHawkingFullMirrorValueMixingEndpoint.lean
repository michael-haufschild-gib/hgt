import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorWeakCouplingOrderEndpoint

/-!
# Full theta-mirror value mixing and eikonal-fed Hawking KMS dilation

The exact Davies--Fulling eikonal numerator is differentiated to every coupling order. Its
`n`th jet is the Fourier transform of the positive source power `k_a^n`. Existing peak
concentration then supplies a nonzero jet in every tilted frequency sector. A function with a
nonzero jet cannot vanish on a full coupling neighbourhood, so every positive balanced sector has
nonzero exact moving-mirror amplitude at arbitrarily weak nonzero coupling, without RH.

The second half constructs a lossless two-port Cayley completion whose transition numerator is
that exact full-mirror amplitude and couples its horizon port to a Hawking KMS probe. It proves
unitarity, detailed balance, and repeated-interaction mixing exactly. This is a conservative
dilation fed by the source-derived scattering numerator, not a claim that Davies--Fulling dynamics
selects the Cayley completion as its Bogoliubov S-matrix. The existing even-jet obstruction rules
out that stronger identification. RH remains exactly the first-order/no-order-jump condition.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap
open scoped ComplexConjugate

noncomputable section

namespace RHTower

private def fullMirrorCouplingJetIntegrand
    (a total : ℝ) (n : ℕ) (t v : ℝ) : ℂ :=
  Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I) *
    (Complex.exp (Complex.I * ((-t * thetaCuspTiltedSource a v : ℝ) : ℂ)) *
      (-Complex.I * (thetaCuspTiltedSource a v : ℂ)) ^ n)

private theorem hasDerivAt_fullMirrorCouplingJetIntegrand
    (a total : ℝ) (n : ℕ) (t v : ℝ) :
    HasDerivAt (fun q : ℝ => fullMirrorCouplingJetIntegrand a total n q v)
      (fullMirrorCouplingJetIntegrand a total (n + 1) t v) t := by
  let base : ℂ := Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I)
  let rate : ℂ := -Complex.I * (thetaCuspTiltedSource a v : ℂ)
  have hq : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hphase : HasDerivAt (fun q : ℝ => Complex.exp ((q : ℂ) * rate))
      (Complex.exp ((t : ℂ) * rate) * rate) t := by
    simpa using (hq.mul_const rate).cexp
  have hmain := (hphase.mul_const (rate ^ n)).const_mul base
  have hphaseEq (q : ℝ) :
      Complex.I * ((-q * thetaCuspTiltedSource a v : ℝ) : ℂ) =
        (q : ℂ) * rate := by
    dsimp [rate]
    push_cast
    ring
  unfold fullMirrorCouplingJetIntegrand
  simp_rw [hphaseEq]
  change HasDerivAt
    (fun q : ℝ => base * (Complex.exp ((q : ℂ) * rate) * rate ^ n))
    (base * (Complex.exp ((t : ℂ) * rate) * rate ^ (n + 1))) t
  simpa only [pow_succ', mul_assoc] using hmain

private theorem norm_fullMirrorCouplingJetIntegrand
    (a total : ℝ) (n : ℕ) (t v : ℝ) :
    ‖fullMirrorCouplingJetIntegrand a total n t v‖ =
      thetaCuspTiltedSource a v ^ n := by
  rw [fullMirrorCouplingJetIntegrand, norm_mul, Complex.norm_exp]
  have hbase : ((((-total * v : ℝ) : ℂ) * Complex.I)).re = 0 := by simp
  rw [hbase, Real.exp_zero, one_mul, norm_mul, Complex.norm_exp]
  have hphase :
      (Complex.I * ((-t * thetaCuspTiltedSource a v : ℝ) : ℂ)).re = 0 := by simp
  rw [hphase, Real.exp_zero, one_mul, norm_pow, norm_mul, norm_neg, norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by
      unfold thetaCuspTiltedSource
      exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all v))]

private theorem integrable_thetaCuspTiltedSource_pow
    (a : ℝ) (ha : |a| < 1) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun v : ℝ => thetaCuspTiltedSource a v ^ n) := by
  let source : 𝓢(ℝ, ℝ) := thetaCuspTiltedSchwartzReal a ha
  let C : ℝ := SchwartzMap.seminorm ℝ 0 0 source
  have hC : 0 ≤ C := apply_nonneg _ source
  have hmajor : Integrable (fun v : ℝ => C ^ (n - 1) * source v) :=
    source.integrable.const_mul (C ^ (n - 1))
  apply Integrable.mono hmajor
  · exact ((contDiff_thetaCuspTiltedSource a).continuous.pow n).aestronglyMeasurable
  · filter_upwards with v
    have hpos : 0 < thetaCuspTiltedSource a v := by
      unfold thetaCuspTiltedSource
      exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all v)
    have hbound : thetaCuspTiltedSource a v ≤ C := by
      have hnorm := SchwartzMap.norm_le_seminorm ℝ source v
      simpa [source, C, Real.norm_eq_abs, abs_of_pos hpos] using hnorm
    have hsource : source v = thetaCuspTiltedSource a v := rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hpos.le _),
      Real.norm_eq_abs, hsource,
      abs_of_nonneg (mul_nonneg (pow_nonneg hC _) hpos.le)]
    rw [show n = (n - 1) + 1 by omega, pow_succ]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hpos.le hbound (n - 1)) hpos.le

def thetaCuspHawkingFullMirrorCouplingJetIntegral
    (a total : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∫ v : ℝ, fullMirrorCouplingJetIntegrand a total n t v

/-- Public pointwise integral form of the exact coupling jet. -/
theorem thetaCuspHawkingFullMirrorCouplingJetIntegral_eq_integral
    (a total : ℝ) (n : ℕ) (t : ℝ) :
    thetaCuspHawkingFullMirrorCouplingJetIntegral a total n t =
      ∫ v : ℝ,
        Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I) *
          (Complex.exp
              (Complex.I * ((-t * thetaCuspTiltedSource a v : ℝ) : ℂ)) *
            (-Complex.I * (thetaCuspTiltedSource a v : ℂ)) ^ n) := rfl

private theorem hasDerivAt_fullMirrorCouplingJetIntegral
    (a : ℝ) (ha : |a| < 1) (total : ℝ) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    HasDerivAt (thetaCuspHawkingFullMirrorCouplingJetIntegral a total n)
      (thetaCuspHawkingFullMirrorCouplingJetIntegral a total (n + 1) t) t := by
  have hnSucc : 1 ≤ n + 1 := by omega
  have hmajor := integrable_thetaCuspTiltedSource_pow a ha hnSucc
  have hbasePower := integrable_thetaCuspTiltedSource_pow a ha hn
  have hbase : Integrable (fun v : ℝ =>
      fullMirrorCouplingJetIntegrand a total n t v) := by
    exact hbasePower.mono'
      (by
        have hk : Continuous (thetaCuspTiltedSource a) :=
          (contDiff_thetaCuspTiltedSource a).continuous
        apply Continuous.aestronglyMeasurable
        unfold fullMirrorCouplingJetIntegrand
        fun_prop)
      (by
        filter_upwards with v
        rw [norm_fullMirrorCouplingJetIntegrand])
  have hderivMeas : AEStronglyMeasurable (fun v : ℝ =>
      fullMirrorCouplingJetIntegrand a total (n + 1) t v) := by
    have hk : Continuous (thetaCuspTiltedSource a) :=
      (contDiff_thetaCuspTiltedSource a).continuous
    apply Continuous.aestronglyMeasurable
    unfold fullMirrorCouplingJetIntegrand
    fun_prop
  have hdom : ∀ᵐ v : ℝ, ∀ q ∈ (Set.univ : Set ℝ),
      ‖fullMirrorCouplingJetIntegrand a total (n + 1) q v‖ ≤
        thetaCuspTiltedSource a v ^ (n + 1) := by
    filter_upwards with v
    intro q _
    rw [norm_fullMirrorCouplingJetIntegrand]
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun q v => fullMirrorCouplingJetIntegrand a total n q v)
    (F' := fun q v => fullMirrorCouplingJetIntegrand a total (n + 1) q v)
    (x₀ := t) (s := Set.univ)
    (bound := fun v => thetaCuspTiltedSource a v ^ (n + 1))
    (by simp)
    (Filter.Eventually.of_forall fun q => by
      have hk : Continuous (thetaCuspTiltedSource a) :=
        (contDiff_thetaCuspTiltedSource a).continuous
      apply Continuous.aestronglyMeasurable
      unfold fullMirrorCouplingJetIntegrand
      fun_prop)
    hbase hderivMeas hdom hmajor
    (by
      filter_upwards with v
      intro q _
      exact hasDerivAt_fullMirrorCouplingJetIntegrand a total n q v)
  exact hresult.2

private def fullMirrorCouplingDefectIntegrand
    (a total t v : ℝ) : ℂ :=
  Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I) *
    thetaCuspHawkingEikonalPhaseDefect a t v

private theorem integrable_thetaCuspHawkingEikonalPhaseDefect'
    (a : ℝ) (ha : |a| < 1) (t : ℝ) :
    Integrable (thetaCuspHawkingEikonalPhaseDefect a t) := by
  let source : 𝓢(ℝ, ℂ) := thetaCuspTiltedSchwartz a ha
  have hmajor : Integrable (fun v : ℝ => ((|t| : ℝ) : ℂ) * source v) :=
    source.integrable.const_mul ((|t| : ℝ) : ℂ)
  apply Integrable.mono hmajor
  · apply Continuous.aestronglyMeasurable
    have hg : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
    unfold thetaCuspHawkingEikonalPhaseDefect thetaCuspTiltedSource
    fun_prop
  · filter_upwards with v
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le
      (x := -t * thetaCuspTiltedSource a v)
    rw [Real.norm_eq_abs, abs_mul, abs_neg] at h
    have hkpos : 0 < thetaCuspTiltedSource a v := by
      unfold thetaCuspTiltedSource
      exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all _)
    rw [abs_of_pos hkpos] at h
    have hsourceNorm : ‖source v‖ = thetaCuspTiltedSource a v := by
      rw [show source v = ((thetaCuspTiltedSource a v : ℝ) : ℂ) by rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkpos]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs, hsourceNorm]
    simpa [thetaCuspHawkingEikonalPhaseDefect] using h

private theorem hasDerivAt_fullMirrorCouplingDefectIntegrand
    (a total t v : ℝ) :
    HasDerivAt (fun q : ℝ => fullMirrorCouplingDefectIntegrand a total q v)
      (fullMirrorCouplingJetIntegrand a total 1 t v) t := by
  let base : ℂ := Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I)
  let rate : ℂ := -Complex.I * (thetaCuspTiltedSource a v : ℂ)
  have hq : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hphase : HasDerivAt (fun q : ℝ => Complex.exp ((q : ℂ) * rate))
      (Complex.exp ((t : ℂ) * rate) * rate) t := by
    simpa using (hq.mul_const rate).cexp
  have hmain := (hphase.sub_const 1).const_mul base
  have hphaseEq (q : ℝ) :
      Complex.I * ((-q * thetaCuspTiltedSource a v : ℝ) : ℂ) =
        (q : ℂ) * rate := by
    dsimp [rate]
    push_cast
    ring
  unfold fullMirrorCouplingDefectIntegrand thetaCuspHawkingEikonalPhaseDefect
    fullMirrorCouplingJetIntegrand
  simp_rw [hphaseEq]
  change HasDerivAt
    (fun q : ℝ => base * (Complex.exp ((q : ℂ) * rate) - 1))
    (base * (Complex.exp ((t : ℂ) * rate) * rate ^ (1 : ℕ))) t
  simpa only [pow_one] using hmain

/-- Exact first coupling derivative of the full eikonal Fourier response at every real coupling. -/
theorem hasDerivAt_thetaCuspHawkingEikonalFourier_all
    (a : ℝ) (ha : |a| < 1) (total t : ℝ) :
    HasDerivAt (fun q : ℝ => thetaCuspHawkingEikonalFourier a q total)
      (thetaCuspHawkingFullMirrorCouplingJetIntegral a total 1 t) t := by
  have hsource : Integrable (thetaCuspTiltedSource a) := by
    let source : 𝓢(ℝ, ℝ) := thetaCuspTiltedSchwartzReal a ha
    exact source.integrable
  have hdefect := integrable_thetaCuspHawkingEikonalPhaseDefect' a ha t
  have hbase : Integrable (fun v : ℝ =>
      fullMirrorCouplingDefectIntegrand a total t v) := by
    have hphaseMeas : AEStronglyMeasurable (fun v : ℝ =>
        Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I)) := by
      apply Continuous.aestronglyMeasurable
      fun_prop
    have hmul := hdefect.bdd_mul (c := 1)
      hphaseMeas
      (by
        filter_upwards with v
        rw [Complex.norm_exp]
        simp)
    simpa only [fullMirrorCouplingDefectIntegrand] using hmul
  have hderivMeas : AEStronglyMeasurable (fun v : ℝ =>
      fullMirrorCouplingJetIntegrand a total 1 t v) := by
    have hk : Continuous (thetaCuspTiltedSource a) :=
      (contDiff_thetaCuspTiltedSource a).continuous
    apply Continuous.aestronglyMeasurable
    unfold fullMirrorCouplingJetIntegrand
    fun_prop
  have hdom : ∀ᵐ v : ℝ, ∀ q ∈ (Set.univ : Set ℝ),
      ‖fullMirrorCouplingJetIntegrand a total 1 q v‖ ≤
        thetaCuspTiltedSource a v := by
    filter_upwards with v
    intro q _
    rw [norm_fullMirrorCouplingJetIntegrand, pow_one]
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun q v => fullMirrorCouplingDefectIntegrand a total q v)
    (F' := fun q v => fullMirrorCouplingJetIntegrand a total 1 q v)
    (x₀ := t) (s := Set.univ) (bound := thetaCuspTiltedSource a)
    (by simp)
    (Filter.Eventually.of_forall fun q => by
      have hk : Continuous (thetaCuspTiltedSource a) :=
        (contDiff_thetaCuspTiltedSource a).continuous
      apply Continuous.aestronglyMeasurable
      unfold fullMirrorCouplingDefectIntegrand thetaCuspHawkingEikonalPhaseDefect
      fun_prop)
    hbase hderivMeas hdom hsource
    (by
      filter_upwards with v
      intro q _
      exact hasDerivAt_fullMirrorCouplingDefectIntegrand a total q v)
  have hfun : (fun q : ℝ => thetaCuspHawkingEikonalFourier a q total) =
      fun q : ℝ => ∫ v : ℝ, fullMirrorCouplingDefectIntegrand a total q v := by
    funext q
    rw [thetaCuspHawkingEikonalFourier,
      Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with v
    simp only [smul_eq_mul]
    unfold fullMirrorCouplingDefectIntegrand
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hfun]
  exact hresult.2

theorem iteratedDeriv_thetaCuspHawkingEikonalFourier_eq_jetIntegral
    (a : ℝ) (ha : |a| < 1) (total : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1)
        (fun t : ℝ => thetaCuspHawkingEikonalFourier a t total) =
      thetaCuspHawkingFullMirrorCouplingJetIntegral a total (n + 1) := by
  induction n with
  | zero =>
      rw [show 0 + 1 = 1 by omega, iteratedDeriv_one]
      funext t
      exact (hasDerivAt_thetaCuspHawkingEikonalFourier_all a ha total t).deriv
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        iteratedDeriv_succ, ih]
      funext t
      exact (hasDerivAt_fullMirrorCouplingJetIntegral
        a ha total (n + 1) (by omega) t).deriv

theorem thetaCuspHawkingFullMirrorCouplingJetIntegral_zero_eq_powerMoment
    (a total : ℝ) (n : ℕ) :
    thetaCuspHawkingFullMirrorCouplingJetIntegral a total n 0 =
      (-Complex.I) ^ n * thetaCuspTiltedPowerMoment a n total := by
  rw [thetaCuspHawkingFullMirrorCouplingJetIntegral, thetaCuspTiltedPowerMoment,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  rw [fullMirrorCouplingJetIntegrand]
  simp only [zero_mul, neg_zero, ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  push_cast
  ring

theorem iteratedDeriv_thetaCuspHawkingEikonalFourier_zero_eq_powerMoment
    (a : ℝ) (ha : |a| < 1) (total : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1)
        (fun t : ℝ => thetaCuspHawkingEikonalFourier a t total) 0 =
      (-Complex.I) ^ (n + 1) *
        thetaCuspTiltedPowerMoment a (n + 1) total := by
  rw [congrFun (iteratedDeriv_thetaCuspHawkingEikonalFourier_eq_jetIntegral
    a ha total n) 0,
    thetaCuspHawkingFullMirrorCouplingJetIntegral_zero_eq_powerMoment]

theorem iteratedDeriv_thetaCuspHawkingEikonalFourier_zero_eq_powerMoment_of_pos
    (a : ℝ) (ha : |a| < 1) (total : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    iteratedDeriv n
        (fun t : ℝ => thetaCuspHawkingEikonalFourier a t total) 0 =
      (-Complex.I) ^ n * thetaCuspTiltedPowerMoment a n total := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [Nat.succ_eq_add_one] using
    iteratedDeriv_thetaCuspHawkingEikonalFourier_zero_eq_powerMoment
      a ha total m

private theorem exists_ne_zero_arbitrarily_close_of_iteratedDeriv_ne_zero
    {f : ℝ → ℂ} {n : ℕ}
    (hf0 : f 0 = 0) (hjet : iteratedDeriv n f 0 ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ t : ℝ, 0 < |t| ∧ |t| < ε ∧ f t ≠ 0 := by
  intro ε hε
  by_contra hnone
  push Not at hnone
  have heq : f =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => 0) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)] with t ht
    have habs : |t| < ε := by simpa [Real.dist_eq] using ht
    by_cases ht0 : t = 0
    · simpa [ht0] using hf0
    · exact hnone t (abs_pos.mpr ht0) habs
  have hderivEq := heq.iteratedDeriv_eq n
  apply hjet
  simpa using hderivEq

/-- Exact eikonal dynamics activates every tilted frequency at arbitrarily weak nonzero coupling.
This is stronger than formal nonvanishing of some power moment: it is value-level activity of the
full nonlinear Fourier amplitude. -/
theorem exists_arbitrarily_weak_thetaCuspHawkingEikonalFourier_ne_zero
    (a total : ℝ) (ha : |a| < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < |t| ∧ |t| < ε ∧
      thetaCuspHawkingEikonalFourier a t total ≠ 0 := by
  let n := thetaCuspHawkingFullMirrorSectorCouplingOrder a total ha
  have hn := thetaCuspHawkingFullMirrorSectorCouplingOrder_spec a total ha
  have hjet : iteratedDeriv n
      (fun t : ℝ => thetaCuspHawkingEikonalFourier a t total) 0 ≠ 0 := by
    rw [iteratedDeriv_thetaCuspHawkingEikonalFourier_zero_eq_powerMoment_of_pos
      a ha total hn.1]
    exact mul_ne_zero
      (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)) hn.2
  have hf0 : thetaCuspHawkingEikonalFourier a 0 total = 0 := by
    have hzero : thetaCuspHawkingEikonalPhaseDefect a 0 = 0 := by
      funext v
      simp [thetaCuspHawkingEikonalPhaseDefect]
    rw [thetaCuspHawkingEikonalFourier,
      Real.fourier_real_eq_integral_exp_smul, hzero]
    simp
  exact exists_ne_zero_arbitrarily_close_of_iteratedDeriv_ne_zero
    hf0 hjet ε hε

/-- Every positive balanced physical theta-mirror sector has nonzero exact transition amplitude
at arbitrarily weak nonzero mirror coupling. -/
theorem exists_arbitrarily_weak_thetaCuspHawkingFullMirrorAmplitude_ne_zero
    (a w : ℝ) (ha : |a| < 1) (hw : 0 < w) (ε : ℝ) (hε : 0 < ε) :
    ∃ lambda : ℝ, 0 < |lambda| ∧ |lambda| < ε ∧
      thetaCuspHawkingFullMirrorAmplitude a lambda (w / 2) (w / 2) ≠ 0 := by
  have hw2 : 0 < w / 2 := by linarith
  obtain ⟨t, ht0, htε, htne⟩ :=
    exists_arbitrarily_weak_thetaCuspHawkingEikonalFourier_ne_zero
      a w ha (ε * (w / 2)) (mul_pos hε hw2)
  refine ⟨t / (w / 2), ?_, ?_, ?_⟩
  · rw [abs_div]
    positivity
  · rw [abs_div, div_lt_iff₀ (abs_pos.mpr hw2.ne')]
    rw [abs_of_pos hw2]
    simpa [mul_comm] using htε
  · rw [thetaCuspHawkingFullMirrorAmplitude_eq_eikonalFourier
      a ha (t / (w / 2)) (w / 2) (w / 2)]
    have hscale : t / (w / 2) * (w / 2) = t := by
      field_simp [hw.ne']
    have htotal : w / 2 + w / 2 = w := by ring
    rw [hscale, htotal]
    have hfac : (-2 * (w / 2) : ℝ) ≠ 0 := by nlinarith
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hfac) htne

/-! ## Exact-eikonal-fed conservative Hawking collision -/

/-- Balanced positive-frequency channel of the exact nonlinear mirror numerator. -/
def thetaCuspHawkingBalancedFullMirrorAmplitude
    (a lambda omega : ℝ) : ℂ :=
  thetaCuspHawkingFullMirrorAmplitude a lambda (omega / 2) (omega / 2)

/-- Cayley load formed from the exact nonlinear mirror amplitude. This is a conservative
completion of the exact on-shell numerator, not an identification with the moving-mirror
Bogoliubov matrix. -/
def thetaCuspHawkingFullMirrorCayleyLoad
    (a lambda omega : ℝ) : ℝ :=
  Complex.normSq (thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega) / 4

def thetaCuspHawkingFullMirrorCayleyRetention
    (a lambda omega : ℝ) : ℝ :=
  (1 - thetaCuspHawkingFullMirrorCayleyLoad a lambda omega) /
    (1 + thetaCuspHawkingFullMirrorCayleyLoad a lambda omega)

def thetaCuspHawkingFullMirrorCayleyTransition
    (a lambda omega : ℝ) : ℂ :=
  thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega /
    ((1 + thetaCuspHawkingFullMirrorCayleyLoad a lambda omega : ℝ) : ℂ)

theorem thetaCuspHawkingFullMirrorCayleyLoad_nonneg
    (a lambda omega : ℝ) :
    0 ≤ thetaCuspHawkingFullMirrorCayleyLoad a lambda omega := by
  unfold thetaCuspHawkingFullMirrorCayleyLoad
  exact div_nonneg
    (Complex.normSq_nonneg _) (by norm_num)

theorem thetaCuspHawkingFullMirrorCayley_denominator_pos
    (a lambda omega : ℝ) :
    0 < 1 + thetaCuspHawkingFullMirrorCayleyLoad a lambda omega := by
  linarith [thetaCuspHawkingFullMirrorCayleyLoad_nonneg a lambda omega]

/-- Exact lossless law for the Cayley completion fed by the full eikonal amplitude. -/
theorem thetaCuspHawkingFullMirrorCayleyRetention_sq_add_transition_normSq
    (a lambda omega : ℝ) :
    thetaCuspHawkingFullMirrorCayleyRetention a lambda omega ^ (2 : ℕ) +
        Complex.normSq
          (thetaCuspHawkingFullMirrorCayleyTransition a lambda omega) = 1 := by
  let A : ℂ := thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega
  let j : ℝ := thetaCuspHawkingFullMirrorCayleyLoad a lambda omega
  have hj : j = Complex.normSq A / 4 := rfl
  have hfour : Complex.normSq A = 4 * j := by rw [hj]; ring
  have hden : 1 + j ≠ 0 :=
    (thetaCuspHawkingFullMirrorCayley_denominator_pos a lambda omega).ne'
  rw [thetaCuspHawkingFullMirrorCayleyRetention,
    thetaCuspHawkingFullMirrorCayleyTransition]
  change ((1 - j) / (1 + j)) ^ (2 : ℕ) +
      Complex.normSq (A / ((1 + j : ℝ) : ℂ)) = 1
  rw [Complex.normSq_div, Complex.normSq_ofReal]
  field_simp [hden]
  rw [hfour]
  ring

def thetaCuspHawkingFullMirrorCayleyExteriorOutput
    (a lambda omega : ℝ) (x h : ℂ) : ℂ :=
  (thetaCuspHawkingFullMirrorCayleyRetention a lambda omega : ℂ) * x -
    conj (thetaCuspHawkingFullMirrorCayleyTransition a lambda omega) * h

def thetaCuspHawkingFullMirrorCayleyHorizonOutput
    (a lambda omega : ℝ) (x h : ℂ) : ℂ :=
  thetaCuspHawkingFullMirrorCayleyTransition a lambda omega * x +
    (thetaCuspHawkingFullMirrorCayleyRetention a lambda omega : ℂ) * h

/-- Exact conservative two-port dilation of the full eikonal numerator. -/
theorem thetaCuspHawkingFullMirrorCayley_preserves_hermitian
    (a lambda omega : ℝ) (x h : ℂ) :
    conj (thetaCuspHawkingFullMirrorCayleyExteriorOutput a lambda omega x h) *
          thetaCuspHawkingFullMirrorCayleyExteriorOutput a lambda omega x h +
        conj (thetaCuspHawkingFullMirrorCayleyHorizonOutput a lambda omega x h) *
          thetaCuspHawkingFullMirrorCayleyHorizonOutput a lambda omega x h =
      conj x * x + conj h * h := by
  let r : ℝ := thetaCuspHawkingFullMirrorCayleyRetention a lambda omega
  let t : ℂ := thetaCuspHawkingFullMirrorCayleyTransition a lambda omega
  have hunit :=
    thetaCuspHawkingFullMirrorCayleyRetention_sq_add_transition_normSq
      a lambda omega
  have hunitC := congrArg (fun y : ℝ => (y : ℂ)) hunit
  push_cast at hunitC
  have hnorm : (Complex.normSq t : ℂ) = conj t * t := by
    rw [Complex.normSq_eq_conj_mul_self]
  rw [hnorm] at hunitC
  change conj ((r : ℂ) * x - conj t * h) * ((r : ℂ) * x - conj t * h) +
      conj (t * x + (r : ℂ) * h) * (t * x + (r : ℂ) * h) =
        conj x * x + conj h * h
  simp only [map_sub, map_add, map_mul, conj_ofReal, conj_conj]
  linear_combination (conj x * x + conj h * h) * hunitC

theorem thetaCuspHawkingFullMirrorCayleyTransition_ne_zero_iff
    (a lambda omega : ℝ) :
    thetaCuspHawkingFullMirrorCayleyTransition a lambda omega ≠ 0 ↔
      thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega ≠ 0 := by
  have hden :=
    (thetaCuspHawkingFullMirrorCayley_denominator_pos a lambda omega).ne'
  have hdenC :
      (((1 + thetaCuspHawkingFullMirrorCayleyLoad a lambda omega : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  rw [thetaCuspHawkingFullMirrorCayleyTransition]
  rw [div_ne_zero_iff, and_iff_left hdenC]

/-- Excited population of the fresh Hawking Gibbs horizon mode. -/
def thetaCuspHawkingFullMirrorKMSExcitedPopulation
    (kappa omega : ℝ) : ℝ :=
  let q := thetaCuspHawkingKMSBoltzmannRatio kappa omega
  q / (1 + q)

theorem thetaCuspHawkingFullMirrorKMSExcitedPopulation_pos
    (kappa omega : ℝ) :
    0 < thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega := by
  unfold thetaCuspHawkingFullMirrorKMSExcitedPopulation
  exact div_pos (thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega)
    (by linarith [thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega])

/-- One exact collision with a fresh Hawking Gibbs horizon mode. -/
def thetaCuspHawkingFullMirrorKMSPopulationChannel
    (kappa a lambda omega p : ℝ) : ℝ :=
  thetaCuspHawkingFullMirrorCayleyRetention a lambda omega ^ (2 : ℕ) * p +
    Complex.normSq (thetaCuspHawkingFullMirrorCayleyTransition a lambda omega) *
      thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega

theorem thetaCuspHawkingFullMirrorKMSPopulationChannel_sub_gibbs
    (kappa a lambda omega p : ℝ) :
    thetaCuspHawkingFullMirrorKMSPopulationChannel
        kappa a lambda omega p -
        thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega =
      thetaCuspHawkingFullMirrorCayleyRetention a lambda omega ^ (2 : ℕ) *
        (p - thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega) := by
  have hunit :=
    thetaCuspHawkingFullMirrorCayleyRetention_sq_add_transition_normSq
      a lambda omega
  unfold thetaCuspHawkingFullMirrorKMSPopulationChannel
  linear_combination
    (thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega) * hunit

/-- Exact upward/downward detailed balance for the full-eikonal-fed collision. -/
theorem thetaCuspHawkingFullMirrorKMSDetailedBalance
    (kappa a lambda omega : ℝ) :
    Complex.normSq (thetaCuspHawkingFullMirrorCayleyTransition a lambda omega) *
        thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega =
      thetaCuspHawkingKMSBoltzmannRatio kappa omega *
        (Complex.normSq
            (thetaCuspHawkingFullMirrorCayleyTransition a lambda omega) *
          (1 - thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega)) := by
  let q := thetaCuspHawkingKMSBoltzmannRatio kappa omega
  have hq : 1 + q ≠ 0 := by
    linarith [thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega]
  rw [thetaCuspHawkingFullMirrorKMSExcitedPopulation]
  change _ * (q / (1 + q)) = q * (_ * (1 - q / (1 + q)))
  field_simp [hq]
  ring

/-- Population after repeated collisions with fresh Hawking Gibbs modes. -/
def thetaCuspHawkingFullMirrorKMSPopulationAfter
    (kappa a lambda omega : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega +
    (thetaCuspHawkingFullMirrorCayleyRetention a lambda omega ^ (2 : ℕ)) ^ n *
      (p - thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega)

theorem thetaCuspHawkingFullMirrorKMSPopulationAfter_zero
    (kappa a lambda omega p : ℝ) :
    thetaCuspHawkingFullMirrorKMSPopulationAfter
      kappa a lambda omega 0 p = p := by
  simp [thetaCuspHawkingFullMirrorKMSPopulationAfter]

theorem thetaCuspHawkingFullMirrorKMSPopulationAfter_succ
    (kappa a lambda omega p : ℝ) (n : ℕ) :
    thetaCuspHawkingFullMirrorKMSPopulationAfter
        kappa a lambda omega (n + 1) p =
      thetaCuspHawkingFullMirrorKMSPopulationChannel kappa a lambda omega
        (thetaCuspHawkingFullMirrorKMSPopulationAfter
          kappa a lambda omega n p) := by
  have hdev := thetaCuspHawkingFullMirrorKMSPopulationChannel_sub_gibbs
    kappa a lambda omega
      (thetaCuspHawkingFullMirrorKMSPopulationAfter
        kappa a lambda omega n p)
  have hchannel :
      thetaCuspHawkingFullMirrorKMSPopulationChannel kappa a lambda omega
          (thetaCuspHawkingFullMirrorKMSPopulationAfter
            kappa a lambda omega n p) =
        thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega +
          thetaCuspHawkingFullMirrorCayleyRetention a lambda omega ^ (2 : ℕ) *
            (thetaCuspHawkingFullMirrorKMSPopulationAfter
                kappa a lambda omega n p -
              thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega) := by
    linarith
  rw [hchannel]
  simp only [thetaCuspHawkingFullMirrorKMSPopulationAfter]
  rw [pow_succ]
  ring

def ThetaCuspHawkingFullMirrorKMSCayleySectorMixes
    (kappa a lambda omega : ℝ) : Prop :=
  ∀ p : ℝ, p ∈ Set.Icc 0 1 →
    Tendsto
      (fun n : ℕ => thetaCuspHawkingFullMirrorKMSPopulationAfter
        kappa a lambda omega n p)
      atTop (𝓝 (thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega))

/-- Exact mixing criterion for the eikonal-fed Hawking collision dilation. -/
theorem thetaCuspHawkingFullMirrorKMSCayleySectorMixes_iff
    {kappa a lambda omega : ℝ} :
    ThetaCuspHawkingFullMirrorKMSCayleySectorMixes kappa a lambda omega ↔
      thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega ≠ 0 := by
  constructor
  · intro hmix hA
    have hlim := hmix 0 (by constructor <;> norm_num)
    have hpH := thetaCuspHawkingFullMirrorKMSExcitedPopulation_pos kappa omega
    have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (𝓝 (thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega)) := by
      simpa [thetaCuspHawkingFullMirrorKMSPopulationAfter,
        thetaCuspHawkingFullMirrorCayleyRetention,
        thetaCuspHawkingFullMirrorCayleyLoad, hA] using hlim
    have hzero := tendsto_const_nhds_iff.mp hconst
    linarith
  · intro hA p _hp
    have ht : thetaCuspHawkingFullMirrorCayleyTransition a lambda omega ≠ 0 :=
      (thetaCuspHawkingFullMirrorCayleyTransition_ne_zero_iff
        a lambda omega).2 hA
    have htpos : 0 < Complex.normSq
        (thetaCuspHawkingFullMirrorCayleyTransition a lambda omega) :=
      Complex.normSq_pos.mpr ht
    have hunit :=
      thetaCuspHawkingFullMirrorCayleyRetention_sq_add_transition_normSq
        a lambda omega
    have hr0 : 0 ≤ thetaCuspHawkingFullMirrorCayleyRetention
        a lambda omega ^ (2 : ℕ) := sq_nonneg _
    have hr1 : thetaCuspHawkingFullMirrorCayleyRetention
        a lambda omega ^ (2 : ℕ) < 1 := by linarith
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hdev := hpow.mul_const
      (p - thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega)
    have hsum : Tendsto
        (fun n : ℕ => thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega +
          (thetaCuspHawkingFullMirrorCayleyRetention a lambda omega ^ (2 : ℕ)) ^ n *
            (p - thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega))
        atTop
        (𝓝 (thetaCuspHawkingFullMirrorKMSExcitedPopulation kappa omega + 0)) :=
      tendsto_const_nhds.add (by simpa using hdev)
    simpa [thetaCuspHawkingFullMirrorKMSPopulationAfter] using hsum

/-- Full nonlinear dynamics makes every positive tilted Hawking resonance sector mix in an exact
thermal scattering dilation at arbitrarily weak nonzero coupling, without RH. RH distinguishes
principal-order response, not value-level finite-coupling activity. -/
theorem exists_arbitrarily_weak_thetaCuspHawkingFullMirrorKMSCayleySectorMixes
    (kappa a omega : ℝ) (ha : |a| < 1) (homega : 0 < omega)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ lambda : ℝ, 0 < |lambda| ∧ |lambda| < ε ∧
      ThetaCuspHawkingFullMirrorKMSCayleySectorMixes
        kappa a lambda omega := by
  obtain ⟨lambda, hlambda0, hlambdaε, hA⟩ :=
    exists_arbitrarily_weak_thetaCuspHawkingFullMirrorAmplitude_ne_zero
      a omega ha homega ε hε
  exact ⟨lambda, hlambda0, hlambdaε,
    (thetaCuspHawkingFullMirrorKMSCayleySectorMixes_iff).2 hA⟩

end RHTower
