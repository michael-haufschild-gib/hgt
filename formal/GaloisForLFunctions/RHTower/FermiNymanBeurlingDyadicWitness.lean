import GaloisForLFunctions.RHTower.NymanMellinGaugeCollapse
import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion
import GaloisForLFunctions.RHTower.FZZParityAreaResponseDyadicClockBridge

/-!
# Dyadic witnesses of the alternating Nyman–Beurling system

The alternating (Fermi) Nyman generators `φ_a(x) = {1/(ax)} − 2{1/(2ax)}` are supported in `(0, 1/a]`
and have Mellin transform `−a^{−s}(1 − 2^{1−s})ζ(s)/s`: the Dirichlet eta function, i.e. the
parity-delay source of the FZZ cigar, in Nyman–Beurling form.

A *witness* is a continuous square-integrable function on `(0,1]` orthogonal to every `φ_a`,
`a ≥ 1`.  Witnesses come in two kinds.

* **Spurious (dyadic) witnesses.**  The factor `1 − 2^{1−s}` vanishes at `s_k = 1 + 2πik/log 2`;
  the power `t^{−2πik/log 2}` is a witness for every `k`, and it is *dyadically self-similar*:
  `w(t/2) = w(t)`.  These are the non-passive modes of the FZZ parity source.
* **Zero witnesses.**  A zero `ρ` of `ζ` with `½ < Re ρ < 1` gives the witness `t^{ρ̄−1}`, and
  `w(t/2) = 2^{1−ρ̄} w(t)` with `|2^{1−ρ̄}| = 2^{1−Re ρ} > 1`: it is never self-similar.

The dyadic dilation `w ↦ w(·/2)` preserves the witness class.  The divisor-selective Hermitian
identity is made explicit: the Hermitian form `q(w) = ∫_0^{1/2} |w|² − ½ ∫_0^1 |w|²` vanishes on every
self-similar witness, and on a zero witness equals `(2^{1−2Re ρ} − ½) ∫_0^1 |w|² ≠ 0`.  Hence:

* if every witness is dyadically self-similar, the Riemann hypothesis holds;
* if every witness carries exactly half of its mass on `(0, 1/2]`, the Riemann hypothesis holds.

The FZZ normalized area response of the mode `ρ` equals `3/4 + (m + m⁻¹)/8` with
`m = 2^{1−2Re ρ}` the dyadic mass fraction of its witness: the physical passivity premise reads the
mass fraction of the witness state.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin

/-! ## The alternating generators -/

/-- The alternating Nyman generator `φ_a(x) = {1/(ax)} − 2{1/(2ax)}`. -/
def fermiNymanGen (a : ℝ) : ℝ → ℂ := fun x => nymanGen a x - 2 * nymanGen (2 * a) x

theorem fermiNymanGen_eq_zero_of_inv_lt {a x : ℝ} (ha : 0 < a) (hx : 1 / a < x) :
    fermiNymanGen a x = 0 := by
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hax : 1 < a * x := by
    rw [div_lt_iff₀ ha] at hx; linarith
  have h1 : 1 / (a * x) < 1 := by rw [div_lt_one (by positivity)]; exact hax
  have h2 : 1 / (2 * a * x) < 1 := by rw [div_lt_one (by positivity)]; linarith
  unfold fermiNymanGen nymanGen
  rw [Int.fract_eq_self.2 ⟨by positivity, h1⟩, Int.fract_eq_self.2 ⟨by positivity, h2⟩]
  push_cast
  field_simp
  ring

theorem norm_nymanGen_le (a x : ℝ) : ‖nymanGen a x‖ ≤ 1 := by
  unfold nymanGen
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

theorem norm_fermiNymanGen_le (a x : ℝ) : ‖fermiNymanGen a x‖ ≤ 3 := by
  unfold fermiNymanGen
  calc ‖nymanGen a x - 2 * nymanGen (2 * a) x‖ ≤ ‖nymanGen a x‖ + ‖2 * nymanGen (2 * a) x‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 2 * 1 := by
        rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
        gcongr
        · exact norm_nymanGen_le _ _
        · exact norm_nymanGen_le _ _
    _ = 3 := by norm_num

theorem measurable_nymanGen (a : ℝ) : Measurable (nymanGen a) := by
  unfold nymanGen
  exact Complex.measurable_ofReal.comp
    (measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id)))

theorem measurable_fermiNymanGen (a : ℝ) : Measurable (fermiNymanGen a) := by
  unfold fermiNymanGen
  exact (measurable_nymanGen a).sub (measurable_const.mul (measurable_nymanGen (2 * a)))

/-- Dyadic rescaling of the generators: `φ_a(2u) = φ_{2a}(u)`. -/
theorem fermiNymanGen_two_mul (a u : ℝ) : fermiNymanGen a (2 * u) = fermiNymanGen (2 * a) u := by
  unfold fermiNymanGen nymanGen
  rw [show a * (2 * u) = 2 * a * u by ring, show 2 * a * (2 * u) = 2 * (2 * a) * u by ring]

/-! ## The Mellin transform -/

theorem cpow_neg_two_mul {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (((2 * a : ℝ) : ℂ)) ^ (-s) = (2 : ℂ) ^ (-s) * ((a : ℝ) : ℂ) ^ (-s) := by
  have h := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le (-s)
  push_cast at h ⊢
  exact h

theorem two_mul_two_cpow_neg (s : ℂ) : 2 * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]

/-- **Mellin transform on the strip.**  `M[φ_a](s) = −a^{−s}(1 − 2^{1−s})ζ(s)/s`. -/
theorem mellin_fermiNymanGen {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {a : ℝ} (ha : 0 < a) :
    mellin (fermiNymanGen a) s =
      -((((a : ℝ) : ℂ) ^ (-s)) * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s / s) := by
  have h1 := mellinConvergent_nymanGen hs0 hs1 ha
  have h2 := mellinConvergent_nymanGen hs0 hs1 (by positivity : (0 : ℝ) < 2 * a)
  have hsplit : mellin (fermiNymanGen a) s = mellin (nymanGen a) s - 2 * mellin (nymanGen (2 * a)) s := by
    unfold mellin fermiNymanGen
    have hfun : (fun t : ℝ => (t : ℂ) ^ (s - 1) • (nymanGen a t - 2 * nymanGen (2 * a) t)) =
        fun t : ℝ => (t : ℂ) ^ (s - 1) • nymanGen a t -
          2 * ((t : ℂ) ^ (s - 1) • nymanGen (2 * a) t) := by
      funext t; simp only [smul_eq_mul]; ring
    rw [hfun, integral_sub h1 (h2.const_mul 2), integral_const_mul]
  rw [hsplit, mellin_nymanGen hs0 hs1 ha, mellin_nymanGen hs0 hs1 (by positivity),
    cpow_neg_two_mul ha, ← two_mul_two_cpow_neg]
  have hs : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  field_simp
  ring

/-- The right-hand side of the Mellin identity. -/
def fermiNymanMellinRHS (a : ℝ) (s : ℂ) : ℂ :=
  -((((a : ℝ) : ℂ) ^ (-s)) * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s / s)

theorem fermiNymanGen_isBigO_atTop (a : ℝ) (ha : 0 < a) (r : ℝ) :
    (fermiNymanGen a) =O[atTop] fun x : ℝ => x ^ (-r) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop (1 / a)] with x hx
  rw [fermiNymanGen_eq_zero_of_inv_lt ha hx, norm_zero, zero_mul]

theorem fermiNymanGen_isBigO_zero (a : ℝ) :
    (fermiNymanGen a) =O[𝓝[>] 0] fun x : ℝ => x ^ (-(0 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 3 ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_fermiNymanGen_le a x

theorem integrableOn_Ioi_zero_fermiNymanGen {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fermiNymanGen a) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ 1 / a)]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 3) measure_Ioc_lt_top.ne
      (measurable_fermiNymanGen a).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => norm_fermiNymanGen_le a x
  · refine (integrableOn_zero).congr_fun (fun x hx => ?_) measurableSet_Ioi
    exact (fermiNymanGen_eq_zero_of_inv_lt ha hx).symm

theorem differentiableAt_mellin_fermiNymanGen {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (fermiNymanGen a)) s :=
  mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    (integrableOn_Ioi_zero_fermiNymanGen ha).locallyIntegrableOn
    (fermiNymanGen_isBigO_atTop a ha _) (by linarith) (fermiNymanGen_isBigO_zero a) hs

theorem differentiableAt_fermiNymanMellinRHS {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : s ∈ puncturedRightHalfPlane) :
    DifferentiableAt ℂ (fermiNymanMellinRHS a) s := by
  have hs0 : s ≠ 0 := by
    intro h; have := hs.1; rw [h, Complex.zero_re] at this; exact lt_irrefl 0 this
  have ha0 : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  unfold fermiNymanMellinRHS
  have hA : DifferentiableAt ℂ (fun w : ℂ => (((a : ℝ) : ℂ)) ^ (-w)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl ha0)
  have hB : DifferentiableAt ℂ (fun w : ℂ => 1 - (2 : ℂ) ^ (1 - w)) s :=
    (differentiableAt_const _).sub
      (((differentiableAt_const _).sub differentiableAt_id).const_cpow
        (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))
  exact (((hA.mul hB).mul (differentiableAt_riemannZeta hs.2)).div differentiableAt_id hs0).neg

/-- **Analytic continuation.**  The Mellin identity holds on the whole punctured right half-plane. -/
theorem mellin_fermiNymanGen_of_mem {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : s ∈ puncturedRightHalfPlane) :
    mellin (fermiNymanGen a) s = fermiNymanMellinRHS a s := by
  have hFd : DifferentiableOn ℂ (mellin (fermiNymanGen a)) puncturedRightHalfPlane :=
    fun z hz => (differentiableAt_mellin_fermiNymanGen ha hz.1).differentiableWithinAt
  have hGd : DifferentiableOn ℂ (fermiNymanMellinRHS a) puncturedRightHalfPlane :=
    fun z hz => (differentiableAt_fermiNymanMellinRHS ha hz).differentiableWithinAt
  have hFa := hFd.analyticOnNhd isOpen_puncturedRightHalfPlane
  have hGa := hGd.analyticOnNhd isOpen_puncturedRightHalfPlane
  have hmem : ((1 / 2 : ℝ) : ℂ) ∈ puncturedRightHalfPlane := by
    refine ⟨by simp, fun h => ?_⟩
    have := congrArg Complex.re h
    simp at this
  have heq : mellin (fermiNymanGen a) =ᶠ[𝓝 ((1 / 2 : ℝ) : ℂ)] fermiNymanMellinRHS a := by
    have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (by simp; norm_num)) fun w hw => ?_
    exact mellin_fermiNymanGen hw.1 hw.2 ha
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa isPreconnected_puncturedRightHalfPlane
    hmem heq hs

/-! ## Spurious modes -/

/-- The spurious modes `s_k = 1 + 2πik/log 2` of the eta factor. -/
def dyadicSpuriousMode (k : ℤ) : ℂ := 1 + ((2 * Real.pi * k / Real.log 2 : ℝ) : ℂ) * I

theorem dyadicSpuriousMode_re (k : ℤ) : (dyadicSpuriousMode k).re = 1 := by
  simp only [dyadicSpuriousMode, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem dyadicSpuriousMode_im (k : ℤ) :
    (dyadicSpuriousMode k).im = 2 * Real.pi * k / Real.log 2 := by
  simp only [dyadicSpuriousMode, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem conj_dyadicSpuriousMode (k : ℤ) :
    (starRingEnd ℂ) (dyadicSpuriousMode k) = dyadicSpuriousMode (-k) := by
  apply Complex.ext
  · rw [Complex.conj_re, dyadicSpuriousMode_re, dyadicSpuriousMode_re]
  · rw [Complex.conj_im, dyadicSpuriousMode_im, dyadicSpuriousMode_im]
    push_cast
    ring

theorem two_cpow_one_sub_dyadicSpuriousMode (k : ℤ) :
    (2 : ℂ) ^ (1 - dyadicSpuriousMode k) = 1 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlogC : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast hlog
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    ← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
  unfold dyadicSpuriousMode
  have : (Real.log 2 : ℂ) * (1 - (1 + ((2 * Real.pi * k / Real.log 2 : ℝ) : ℂ) * I)) =
      ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    push_cast
    field_simp
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem dyadicSpuriousMode_mem {k : ℤ} (hk : k ≠ 0) :
    dyadicSpuriousMode k ∈ puncturedRightHalfPlane := by
  refine ⟨by rw [dyadicSpuriousMode_re]; norm_num, fun h => ?_⟩
  have him := congrArg Complex.im h
  rw [dyadicSpuriousMode_im, Complex.one_im] at him
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [div_eq_zero_iff] at him
  rcases him with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · norm_num at h3
      · exact Real.pi_ne_zero h3
    · exact hk' h2
  · exact hlog.ne' h1

theorem mellin_fermiNymanGen_dyadicSpuriousMode {a : ℝ} (ha : 0 < a) {k : ℤ} (hk : k ≠ 0) :
    mellin (fermiNymanGen a) (dyadicSpuriousMode k) = 0 := by
  rw [mellin_fermiNymanGen_of_mem ha (dyadicSpuriousMode_mem hk), fermiNymanMellinRHS,
    two_cpow_one_sub_dyadicSpuriousMode]
  simp

/-! ## Witnesses -/

/-- A continuous square-integrable function on `(0,1]` orthogonal to every generator `φ_a`, `a ≥ 1`. -/
def IsFermiNymanWitness (w : ℝ → ℂ) : Prop :=
  ContinuousOn w (Ioc 0 1) ∧ IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1) ∧
    ∀ a : ℝ, 1 ≤ a → ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ) (w t) = 0

/-- The power witness `t ↦ t^{z−1}`. -/
def powerWitness (z : ℂ) : ℝ → ℂ := fun t => (t : ℂ) ^ (z - 1)

theorem integral_Ioc_fermiNymanGen_mul_cpow {a : ℝ} (ha : 1 ≤ a) (s : ℂ) :
    (∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (t : ℂ) ^ (s - 1)) = mellin (fermiNymanGen a) s := by
  unfold mellin
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  · refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp only [smul_eq_mul]; ring
  · intro t ht
    have ht1 : 1 < t := by
      rcases ht with ⟨ht0, htn⟩
      simp only [mem_Ioc, not_and, not_le] at htn
      exact htn ht0
    have : 1 / a < t := lt_of_le_of_lt (by rw [div_le_one ha0]; exact ha) ht1
    rw [fermiNymanGen_eq_zero_of_inv_lt ha0 this, smul_zero]

theorem conj_ofReal_cpow {t : ℝ} (ht : 0 < t) (z : ℂ) :
    (starRingEnd ℂ) ((t : ℂ) ^ z) = (t : ℂ) ^ (starRingEnd ℂ z) := by
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem integrableOn_normSq_powerWitness {z : ℂ} (hz : 1 / 2 < z.re) :
    IntegrableOn (fun t => ‖powerWitness z t‖ ^ 2) (Ioc 0 1) := by
  have hr : (-1 : ℝ) < 2 * (z.re - 1) := by linarith
  have hint := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hr)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hint
  refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioc
  unfold powerWitness
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1, ← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
  simp only [Complex.sub_re, Complex.one_re, Nat.cast_ofNat]
  ring_nf

theorem continuousOn_powerWitness (z : ℂ) : ContinuousOn (powerWitness z) (Ioc 0 1) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  unfold powerWitness
  exact (Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
    (Complex.ofReal_mem_slitPlane.2 ht.1)

theorem half_cpow_eq_two_cpow (w : ℂ) : ((1 / 2 : ℝ) : ℂ) ^ (w - 1) = (2 : ℂ) ^ (1 - w) := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.cpow_def_of_ne_zero (by norm_num),
    ← Complex.ofReal_log (by norm_num), ← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
  congr 1
  rw [one_div, Real.log_inv]
  push_cast
  ring

/-- The dyadic eigen-relation `w(t/2) = 2^{1−z} w(t)`. -/
theorem powerWitness_half (z : ℂ) {t : ℝ} (ht : 0 < t) :
    powerWitness z (t / 2) = (2 : ℂ) ^ (1 - z) * powerWitness z t := by
  unfold powerWitness
  have h := Complex.mul_cpow_ofReal_nonneg ht.le (by norm_num : (0 : ℝ) ≤ 1 / 2) (z - 1)
  rw [show ((t / 2 : ℝ) : ℂ) = (t : ℂ) * ((1 / 2 : ℝ) : ℂ) by push_cast; ring, h,
    half_cpow_eq_two_cpow, mul_comm]

/-- **Zero witnesses.**  A zero of `ζ` with `½ < Re ρ < 1` gives the witness `t^{ρ̄−1}`. -/
theorem isFermiNymanWitness_powerWitness_of_zeta_eq_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (h1 : 1 / 2 < ρ.re) (h2 : ρ.re < 1) :
    IsFermiNymanWitness (powerWitness ((starRingEnd ℂ) ρ)) := by
  refine ⟨continuousOn_powerWitness _, integrableOn_normSq_powerWitness (by simpa using h1),
    fun a ha => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hconj : ∀ t ∈ Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ)
      (powerWitness ((starRingEnd ℂ) ρ) t) = fermiNymanGen a t * (t : ℂ) ^ (ρ - 1) := by
    intro t ht
    unfold powerWitness
    rw [conj_ofReal_cpow ht.1, map_sub, Complex.conj_conj, map_one]
  rw [setIntegral_congr_fun measurableSet_Ioc hconj, integral_Ioc_fermiNymanGen_mul_cpow ha,
    mellin_fermiNymanGen (by linarith) h2 ha0, hζ]
  simp

/-- **Spurious witnesses.**  Every mode `s_k`, `k ≠ 0`, gives the witness `t^{−2πik/log 2}`. -/
theorem isFermiNymanWitness_spurious {k : ℤ} (hk : k ≠ 0) :
    IsFermiNymanWitness (powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode k))) := by
  refine ⟨continuousOn_powerWitness _, integrableOn_normSq_powerWitness ?_, fun a ha => ?_⟩
  · rw [Complex.conj_re, dyadicSpuriousMode_re]; norm_num
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hconj : ∀ t ∈ Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ)
      (powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode k)) t) =
      fermiNymanGen a t * (t : ℂ) ^ (dyadicSpuriousMode k - 1) := by
    intro t ht
    unfold powerWitness
    rw [conj_ofReal_cpow ht.1, map_sub, Complex.conj_conj, map_one]
  rw [setIntegral_congr_fun measurableSet_Ioc hconj, integral_Ioc_fermiNymanGen_mul_cpow ha,
    mellin_fermiNymanGen_dyadicSpuriousMode ha0 hk]

/-- Spurious witnesses are dyadically self-similar. -/
theorem powerWitness_spurious_half (k : ℤ) {t : ℝ} (ht : 0 < t) :
    powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode k)) (t / 2) =
      powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode k)) t := by
  rw [powerWitness_half _ ht]
  rw [conj_dyadicSpuriousMode, two_cpow_one_sub_dyadicSpuriousMode, one_mul]

/-- Zero witnesses are never dyadically self-similar. -/
theorem powerWitness_half_ne_of_re_lt_one {z : ℂ} (hz : z.re < 1) :
    powerWitness z (1 / 2) ≠ powerWitness z 1 := by
  intro h
  have hn := congrArg norm h
  unfold powerWitness at hn
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.norm_cpow_eq_rpow_re_of_pos
    (by norm_num), Real.one_rpow] at hn
  have : 1 < (1 / 2 : ℝ) ^ ((z - 1).re) :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) (by simp; linarith)
  linarith

/-- **The self-similarity identity implies the Riemann hypothesis.**  If every witness of the
alternating Nyman–Beurling system is dyadically self-similar, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_fermiNymanWitness_selfSimilar
    (h : ∀ w : ℝ → ℂ, IsFermiNymanWitness w → ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hζ, h1, h2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  have hw := h _ (isFermiNymanWitness_powerWitness_of_zeta_eq_zero hζ h1 h2) 1 ⟨one_pos, le_rfl⟩
  exact powerWitness_half_ne_of_re_lt_one (z := (starRingEnd ℂ) ρ) (by simpa using h2) hw

/-! ## The witness class is dyadically invariant -/

theorem integral_Ioc_comp_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ t in Ioc (0 : ℝ) 1, f (t / 2)) = (2 : ℝ) • ∫ u in Ioc (0 : ℝ) (1 / 2), f u := by
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le (by norm_num)]
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) f
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  simp only [mul_zero, mul_one] at h
  rw [show (fun t : ℝ => f (t / 2)) = fun t => f (1 / 2 * t) by funext t; ring_nf, h]
  norm_num

theorem integral_Ioc_eq_half_of_support {g : ℝ → ℂ} (hg : ∀ t, 1 / 2 < t → g t = 0) :
    (∫ t in Ioc (0 : ℝ) 1, g t) = ∫ t in Ioc (0 : ℝ) (1 / 2), g t := by
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc_right (by norm_num)) (fun t ht => ?_)
  refine hg t ?_
  rcases ht with ⟨ht1, ht2⟩
  simp only [mem_Ioc, not_and, not_le] at ht2
  exact ht2 ht1.1

/-- **Dyadic invariance.**  The dilation `w ↦ w(·/2)` maps witnesses to witnesses. -/
theorem IsFermiNymanWitness.halfDilate {w : ℝ → ℂ} (hw : IsFermiNymanWitness w) :
    IsFermiNymanWitness (fun t => w (t / 2)) := by
  obtain ⟨hc, hsq, horth⟩ := hw
  refine ⟨?_, ?_, fun a ha => ?_⟩
  · refine hc.comp (continuousOn_id.div_const 2) (fun t ht => ⟨?_, ?_⟩)
    · show 0 < t / 2; linarith [ht.1]
    · show t / 2 ≤ 1; linarith [ht.2]
  · have hsq' : IntervalIntegrable (fun t => ‖w t‖ ^ 2) volume 0 (1 / 2) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
      exact hsq.mono_set (Ioc_subset_Ioc_right (by norm_num))
    have h2 := hsq'.comp_mul_left (c := 1 / 2) (by simp) (by simp)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h2
    norm_num at h2
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only; ring_nf
  · have ha2 : 1 ≤ 2 * a := by linarith
    have ha0 : 0 < a := by linarith
    have hpt : ∀ t : ℝ, fermiNymanGen a t = fermiNymanGen (2 * a) (t / 2) := by
      intro t
      rw [← fermiNymanGen_two_mul]
      congr 1
      ring
    have hstep : (∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ) (w (t / 2))) =
        (2 : ℝ) • ∫ u in Ioc (0 : ℝ) (1 / 2), fermiNymanGen (2 * a) u * (starRingEnd ℂ) (w u) := by
      rw [← integral_Ioc_comp_half (fun u => fermiNymanGen (2 * a) u * (starRingEnd ℂ) (w u))]
      refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
      simp only [hpt t]
    rw [hstep, ← integral_Ioc_eq_half_of_support (fun t ht => by
      rw [fermiNymanGen_eq_zero_of_inv_lt (by positivity) (lt_of_le_of_lt (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith) ht), zero_mul]),
      horth (2 * a) ha2, smul_zero]

/-! ## Dyadic mass fractions -/

theorem integral_Ioc_normSq_powerWitness {z : ℂ} (hz : 1 / 2 < z.re) {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioc (0 : ℝ) c, ‖powerWitness z t‖ ^ 2) = c ^ (2 * z.re - 1) / (2 * z.re - 1) := by
  have hr : (-1 : ℝ) < 2 * (z.re - 1) := by linarith
  have hcongr : ∀ t ∈ Ioc (0 : ℝ) c, ‖powerWitness z t‖ ^ 2 = t ^ (2 * (z.re - 1)) := by
    intro t ht
    unfold powerWitness
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1, ← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
    simp only [Complex.sub_re, Complex.one_re, Nat.cast_ofNat]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, ← intervalIntegral.integral_of_le hc.le,
    integral_rpow (Or.inl hr), Real.zero_rpow (by linarith)]
  ring_nf

/-- **Mass fraction of a zero witness.**  `∫_0^{1/2} |w|² = 2^{1−2Re z} ∫_0^1 |w|²`. -/
theorem integral_half_normSq_powerWitness {z : ℂ} (hz : 1 / 2 < z.re) :
    (∫ t in Ioc (0 : ℝ) (1 / 2), ‖powerWitness z t‖ ^ 2) =
      (2 : ℝ) ^ (1 - 2 * z.re) * ∫ t in Ioc (0 : ℝ) 1, ‖powerWitness z t‖ ^ 2 := by
  rw [integral_Ioc_normSq_powerWitness hz (by norm_num), integral_Ioc_normSq_powerWitness hz one_pos,
    Real.one_rpow, one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  ring_nf

/-- **Self-similar witnesses carry exactly half their mass on `(0, 1/2]`.** -/
theorem integral_half_normSq_of_selfSimilar {w : ℝ → ℂ}
    (hw : ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t) :
    (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2) = (1 / 2) * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2 := by
  have h := integral_Ioc_comp_half (fun u => ‖w u‖ ^ 2)
  have hcongr : (∫ t in Ioc (0 : ℝ) 1, ‖w (t / 2)‖ ^ 2) = ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => by simp only [hw t ht])
  rw [hcongr, smul_eq_mul] at h
  linarith

/-- **The Hermitian identity implies the Riemann hypothesis.**  If every witness of the alternating
Nyman–Beurling system carries exactly half of its `L²` mass on `(0, 1/2]` — the Hermitian form
`∫_0^{1/2}|w|² − ½∫_0^1|w|²` vanishes on the witness class — the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_fermiNymanWitness_halfMass
    (h : ∀ w : ℝ → ℂ, IsFermiNymanWitness w →
      (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2) = (1 / 2) * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hζ, h1, h2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  set z := (starRingEnd ℂ) ρ with hz
  have hzre : z.re = ρ.re := by rw [hz, Complex.conj_re]
  have hz1 : 1 / 2 < z.re := by rw [hzre]; exact h1
  have hw := h _ (isFermiNymanWitness_powerWitness_of_zeta_eq_zero hζ h1 h2)
  rw [integral_half_normSq_powerWitness hz1, integral_Ioc_normSq_powerWitness hz1 one_pos,
    Real.one_rpow] at hw
  have hpos : 0 < 1 / (2 * z.re - 1) := by
    have : 0 < 2 * z.re - 1 := by linarith
    positivity
  have hlt : (1 / 2 : ℝ) < (2 : ℝ) ^ (1 - 2 * z.re) := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (show (-1 : ℝ) < 1 - 2 * z.re by rw [hzre]; linarith)
    rwa [Real.rpow_neg_one, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at this
  have := mul_lt_mul_of_pos_right hlt hpos
  linarith

/-! ## The FZZ response reads the mass fraction -/

/-- **FZZ area response = function of the dyadic mass fraction.**  At the canonical parity-Mellin twist,
`R(ρ) = 3/4 + (m + m⁻¹)/8` with `m = 2^{1−2Re ρ}`. -/
theorem fzzAreaResponse_mellinTwist_eq_massFraction (ρ : ℂ) :
    fzzLinearReplicaAreaNormalizedResponse 1 (fzzCigarParityMellinTorusTwist ρ).im =
      3 / 4 + ((2 : ℝ) ^ (1 - 2 * ρ.re) + ((2 : ℝ) ^ (1 - 2 * ρ.re))⁻¹) / 8 := by
  rw [fzzAreaResponse_mellinTwist_eq_dyadicClockOrbitAverage, norm_dyadicPrimeClock,
    norm_dyadicPrimeClock, lineReflect_re, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
  push_cast
  ring_nf

/-- The FZZ response of a zero mode is the response of its witness's dyadic mass fraction. -/
theorem fzzAreaResponse_eq_witness_massFraction {ρ : ℂ} (h1 : 1 / 2 < ρ.re) :
    let w := powerWitness ((starRingEnd ℂ) ρ)
    let m := (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2) / ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2
    fzzLinearReplicaAreaNormalizedResponse 1 (fzzCigarParityMellinTorusTwist ρ).im =
      3 / 4 + (m + m⁻¹) / 8 := by
  intro w m
  have hz1 : 1 / 2 < ((starRingEnd ℂ) ρ).re := by rw [Complex.conj_re]; exact h1
  have hI : (∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2) ≠ 0 := by
    rw [integral_Ioc_normSq_powerWitness hz1 one_pos, Real.one_rpow]
    have : 0 < 2 * ((starRingEnd ℂ) ρ).re - 1 := by linarith
    positivity
  have hm : m = (2 : ℝ) ^ (1 - 2 * ρ.re) := by
    simp only [m, w]
    rw [integral_half_normSq_powerWitness hz1, Complex.conj_re, mul_div_assoc,
      div_self (by simpa [w] using hI), mul_one]
  rw [hm, fzzAreaResponse_mellinTwist_eq_massFraction]

end RHTower
