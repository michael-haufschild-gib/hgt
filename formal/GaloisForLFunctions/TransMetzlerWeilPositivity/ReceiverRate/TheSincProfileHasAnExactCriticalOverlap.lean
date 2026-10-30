import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheSincProfileHasALogLogTail
import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheCriticalOverlapIsLogLogTimesLogSquared
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The exact critical overlap of the sinc profile

For `sincProfile` the Fourier tail energy `τ(c) = ∫_{ξ > c} |𝓕 sincProfile(ξ)|² dξ` (`sincTail`)
satisfies `c e^{−K c/log² c} ≤ τ(c) ≤ 4W μ_{12}(c)` (`eventually_mul_exp_le_sincTail`,
`sincTail_le`), so the exact critical overlap `c*_N` = least `c ≥ 1` with `τ(c) log N ≤ 1`
(`sincCriticalOverlap`) is of order `L (log L)²`, `L = log log N`
(`eventually_le_sincCriticalOverlap`, `eventually_sincCriticalOverlap_le`). In these units:

* every overlap `r_N c*_N` with `r_N → ∞` is an RH receiver
  (`riemannHypothesis_iff_nonneg_of_sincCritical_rate`);
* RH holds iff every bounded multiple `K c*_N` is eventually nonnegative
  (`riemannHypothesis_iff_forall_sincCritical_multiple`);
* one bounded multiple `K` gives Weil positivity on every `C²` test supported in `[−R, R]` with
  `288 e ⌈1 + e^{2(R+1)}⌉ < K/(4 K_τ)` (`nonneg_of_sincCritical_multiple`), `K_τ = 8π/3 + 3000`.
-/

noncomputable section

open MeasureTheory Filter Topology Real RHTower
open scoped ContDiff FourierTransform

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- The Fourier tail energy of the sinc profile beyond `c`. -/
def sincTail (c : ℝ) : ℝ := ∫ ξ in Set.Ioi c, ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ^ 2

/-- The exact critical overlap: the least `c ≥ 1` with `τ(c) log N ≤ 1`. -/
def sincCriticalOverlap (N : ℕ) : ℝ := sInf {c : ℝ | 1 ≤ c ∧ sincTail c * Real.log N ≤ 1}

/-- The exponent constant of the tail lower bound. -/
def sincTailConst : ℝ := 8 * π / 3 + 3000

/-- The constant of the decay `|𝓕 sincProfile(ξ)| ≤ W ξ^{−2}`. -/
def sincDecayConst : ℝ := 144 * dcLogWeight 2 / π ^ 2

theorem sincTailConst_pos : 0 < sincTailConst := by
  unfold sincTailConst; have := Real.pi_pos; positivity

theorem sincDecayConst_pos : 0 < sincDecayConst := by
  unfold sincDecayConst; have := Real.pi_pos; have := dcLogWeight_pos 2; positivity

/-! ### Pointwise bounds on the transform -/

theorem hasCompactSupport_sincProfile : HasCompactSupport sincProfile :=
  hasCompactSupport_of_vanishes sincProfile_vanishesOff

theorem continuous_norm_fourier_sincProfile :
    Continuous fun ξ => ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ :=
  (HTGeometry.continuous_fourier ((contDiff_sincProfile.continuous.integrable_of_hasCompactSupport
    hasCompactSupport_sincProfile).ofReal)).norm

theorem norm_fourier_sincProfile_le_integral (ξ : ℝ) :
    ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ≤ ∫ x, |sincProfile x| := by
  have h := HTGeometry.norm_fourierReal_le_integral_norm (fun x => (sincProfile x : ℂ)) ξ
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

theorem norm_fourier_sincProfile_le_majorant {ξ : ℝ} (hξ : 0 < ξ) :
    ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ≤ 4 * dcMajorant 12 (2 * π * ξ) := by
  have h := norm_fourier_le_dcMajorant contDiff_sincProfile hasCompactSupport_sincProfile
    integral_abs_iteratedDeriv_sincProfile_le hξ.ne'
  rwa [abs_of_pos hξ] at h

theorem dcMajorant_nonneg {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) : 0 ≤ dcMajorant B c :=
  le_ciInf fun q => by have := dcLogWeight_pos q; positivity

/-- `|𝓕 sincProfile(ξ)| ≤ W ξ^{−2}` for `ξ > 0`, from the second derivative. -/
theorem norm_fourier_sincProfile_le_rpow {ξ : ℝ} (hξ : 0 < ξ) :
    ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ≤ sincDecayConst * ξ ^ (-2 : ℝ) := by
  have hπ := Real.pi_pos
  refine (norm_fourier_sincProfile_le_majorant hξ).trans ?_
  have h2 := dcMajorant_le_term (B := 12) (by norm_num) (by positivity : 0 < 2 * π * ξ) 2
  rw [Real.rpow_neg hξ.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc 4 * dcMajorant 12 (2 * π * ξ) ≤ 4 * (12 ^ 2 * dcLogWeight 2 / (2 * π * ξ) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = sincDecayConst * (ξ ^ 2)⁻¹ := by unfold sincDecayConst; field_simp; ring

/-! ### The tail energy -/

theorem integrableOn_norm_fourier_sincProfile_sq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun ξ => ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ^ 2) (Set.Ioi c) := by
  set A₀ := ∫ x, |sincProfile x|
  have hg : IntegrableOn (fun ξ : ℝ => A₀ * (sincDecayConst * ξ ^ (-2 : ℝ))) (Set.Ioi c) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hc).const_mul sincDecayConst).const_mul A₀
  refine Integrable.mono' hg (continuous_norm_fourier_sincProfile.pow 2).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun ξ hξ => ?_)
  have hξ0 : 0 < ξ := hc.trans hξ
  rw [Real.norm_of_nonneg (by positivity), sq]
  exact mul_le_mul (norm_fourier_sincProfile_le_integral ξ)
    (norm_fourier_sincProfile_le_rpow hξ0) (norm_nonneg _)
    ((norm_nonneg _).trans (norm_fourier_sincProfile_le_integral ξ))

theorem sincTail_antitone {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') : sincTail c' ≤ sincTail c :=
  setIntegral_mono_set (integrableOn_norm_fourier_sincProfile_sq hc)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Set.Ioi_subset_Ioi hcc).eventuallyLE

theorem integral_le_sincTail {c : ℝ} (hc : 0 < c) :
    ∫ ξ in c..2 * c, ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ^ 2 ≤ sincTail c := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  exact setIntegral_mono_set (integrableOn_norm_fourier_sincProfile_sq hc)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) Set.Ioc_subset_Ioi_self.eventuallyLE

/-- **Lower bound.** `τ(c) ≥ c exp(−K_τ c/log² c)` for all large `c`. -/
theorem eventually_mul_exp_le_sincTail :
    ∀ᶠ c : ℝ in atTop, c * Real.exp (-(sincTailConst * (c / Real.log c ^ 2))) ≤ sincTail c := by
  filter_upwards [exp_mul_le_integral_norm_fourier_sincProfile_sq, eventually_gt_atTop 0]
    with c h hc
  exact h.trans (integral_le_sincTail hc)

/-- **Upper bound.** `τ(c) ≤ 4W μ_{12}(c)` for `c ≥ 1`. -/
theorem sincTail_le {c : ℝ} (hc : 1 ≤ c) : sincTail c ≤ 4 * sincDecayConst * dcMajorant 12 c := by
  have hπ := Real.pi_pos
  have hc0 : 0 < c := by linarith
  have hμ0 := dcMajorant_nonneg (B := 12) (by norm_num) hc0
  have hW := sincDecayConst_pos
  have hg : IntegrableOn (fun ξ : ℝ => 4 * dcMajorant 12 c * (sincDecayConst * ξ ^ (-2 : ℝ)))
      (Set.Ioi c) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hc0).const_mul sincDecayConst).const_mul _
  have hle : sincTail c ≤ ∫ ξ in Set.Ioi c, 4 * dcMajorant 12 c * (sincDecayConst * ξ ^ (-2 : ℝ)) := by
    refine setIntegral_mono_on (integrableOn_norm_fourier_sincProfile_sq hc0) hg measurableSet_Ioi
      fun ξ hξ => ?_
    have hξ0 : 0 < ξ := hc0.trans hξ
    have hmaj : ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ≤ 4 * dcMajorant 12 c :=
      (norm_fourier_sincProfile_le_majorant hξ0).trans (mul_le_mul_of_nonneg_left
        (dcMajorant_antitone (by norm_num) hc0 (by
          have := Real.pi_gt_three
          nlinarith [Set.mem_Ioi.mp hξ])) (by norm_num))
    rw [sq]
    exact mul_le_mul hmaj (norm_fourier_sincProfile_le_rpow hξ0) (norm_nonneg _) (by positivity)
  have hint : ∫ ξ in Set.Ioi c, 4 * dcMajorant 12 c * (sincDecayConst * ξ ^ (-2 : ℝ)) =
      4 * dcMajorant 12 c * (sincDecayConst * c⁻¹) := by
    rw [integral_const_mul, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hc0]
    norm_num [Real.rpow_neg_one]
  rw [hint] at hle
  have hinv : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  calc sincTail c ≤ 4 * dcMajorant 12 c * (sincDecayConst * c⁻¹) := hle
    _ ≤ 4 * dcMajorant 12 c * (sincDecayConst * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv hW.le) (by positivity)
    _ = 4 * sincDecayConst * dcMajorant 12 c := by ring

/-! ### The exact critical overlap -/

private theorem loglog_atTop'' :
    Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem log_natCast_pos_of_loglog {N : ℕ} (h : 0 < Real.log (Real.log N)) :
    0 < Real.log N := by
  rcases (Real.log_natCast_nonneg N).lt_or_eq with h' | h'
  · exact h'
  · rw [← h', Real.log_zero] at h; exact absurd h (lt_irrefl 0)

/-- **Upper bound.** Eventually `c*_N ≤ 96 e L (log L)²`. -/
theorem eventually_sincCriticalOverlap_le :
    ∀ᶠ N : ℕ in atTop, sincCriticalOverlap N ≤ 96 * Real.exp 1 * dcScale N ∧
      (96 * Real.exp 1 * dcScale N) ∈ {c : ℝ | 1 ≤ c ∧ sincTail c * Real.log N ≤ 1} := by
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  set C := 96 * Real.exp 1 with hC
  have hC1 : 1 ≤ C := by rw [hC]; nlinarith
  have hW := sincDecayConst_pos
  have ho := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1)).bound
    (show (0 : ℝ) < 1 / (2 * C) by positivity)
  have hP : ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧ 1 ≤ Real.log L ∧ C * L * Real.log L ^ 2 + 3 ≤ L ^ 2 ∧
      Real.log (4 * sincDecayConst) + 1 ≤ L := by
    filter_upwards [ho, eventually_ge_atTop (Real.exp 1 + 6),
      eventually_ge_atTop (Real.log (4 * sincDecayConst) + 1)] with L hoL hL hL'
    have hL0 : 0 < L := by linarith
    have hlL : 1 ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le hL0]; linarith
    refine ⟨by linarith, hlL, ?_, hL'⟩
    rw [Real.rpow_two, Real.rpow_one, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg hL0.le] at hoL
    have h1 : C * L * Real.log L ^ 2 ≤ L ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left hoL (by positivity : (0 : ℝ) ≤ C * L)
      have e : C * L * (1 / (2 * C) * L) = L ^ 2 / 2 := by field_simp
      linarith
    nlinarith
  filter_upwards [loglog_atTop''.eventually hP] with N ⟨hL2, hl1, hLL, hLW⟩
  set L := Real.log (Real.log N) with hLdef
  have hL0 : 0 < L := by linarith
  have hlogN := log_natCast_pos_of_loglog hL0
  set c₁ := C * dcScale N with hc₁
  have hc₁eq : c₁ = C * L * Real.log L ^ 2 := by rw [hc₁, dcScale]; ring
  have hc₁1 : 1 ≤ c₁ := by
    rw [hc₁eq]
    have : 1 ≤ Real.log L ^ 2 := one_le_pow₀ hl1
    have h2 : 1 ≤ C * L := by nlinarith
    nlinarith
  have hmem : c₁ ∈ {c : ℝ | 1 ≤ c ∧ sincTail c * Real.log N ≤ 1} := by
    refine ⟨hc₁1, ?_⟩
    have hμ := dcMajorant_le_exp (by norm_num : (1 : ℝ) ≤ 12) hc₁1
    have hlog : Real.log (c₁ + 3) ≤ 2 * Real.log L := by
      have h := Real.log_le_log (show (0 : ℝ) < c₁ + 3 by linarith)
        (show c₁ + 3 ≤ L ^ 2 by rw [hc₁eq]; exact hLL)
      rwa [Real.log_pow, Nat.cast_ofNat] at h
    have hl3 : 0 < Real.log (c₁ + 3) := Real.log_pos (by linarith)
    have hx : 2 * L ≤ c₁ / (Real.exp 1 * 12 * Real.log (c₁ + 3) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have hsq : Real.log (c₁ + 3) ^ 2 ≤ 4 * Real.log L ^ 2 := by nlinarith
      have hE : 0 ≤ Real.exp 1 * 12 := by positivity
      have h1 := mul_le_mul_of_nonneg_left hsq (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * L) hE)
      have h2 : 2 * L * (Real.exp 1 * 12) * (4 * Real.log L ^ 2) = c₁ := by
        rw [hc₁eq, hC]; ring
      nlinarith
    have htail := sincTail_le hc₁1
    calc sincTail c₁ * Real.log N
        ≤ 4 * sincDecayConst * Real.exp (1 - c₁ / (Real.exp 1 * 12 * Real.log (c₁ + 3) ^ 2)) *
            Real.exp L := by
          rw [hLdef, Real.exp_log hlogN]
          exact mul_le_mul_of_nonneg_right (htail.trans
            (mul_le_mul_of_nonneg_left hμ (by positivity))) hlogN.le
      _ ≤ Real.exp (Real.log (4 * sincDecayConst)) * Real.exp (1 - 2 * L) * Real.exp L := by
          have e4 : Real.exp (Real.log (4 * sincDecayConst)) = 4 * sincDecayConst :=
            Real.exp_log (by linarith)
          rw [e4]
          have h1 : Real.exp (1 - c₁ / (Real.exp 1 * 12 * Real.log (c₁ + 3) ^ 2)) ≤
              Real.exp (1 - 2 * L) := Real.exp_le_exp.mpr (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith))
            (Real.exp_pos L).le
      _ = Real.exp (Real.log (4 * sincDecayConst) + 1 - L) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact ⟨csInf_le ⟨1, fun _ h => h.1⟩ hmem, hmem⟩

/-- **Lower bound.** Eventually `L (log L)² /(4 K_τ) ≤ c*_N`: below that overlap the tail still
exceeds `(log N)^{−1/4}`. -/
theorem eventually_le_sincCriticalOverlap :
    ∀ᶠ N : ℕ in atTop, dcScale N / (4 * sincTailConst) ≤ sincCriticalOverlap N := by
  have hK := sincTailConst_pos
  set δ := 1 / (4 * sincTailConst) with hδ
  have hδ0 : 0 < δ := by positivity
  have hc₀ : Tendsto (fun L : ℝ => δ * L * Real.log L ^ 2) atTop atTop := by
    have h1 : Tendsto (fun L : ℝ => δ * L) atTop atTop := tendsto_id.const_mul_atTop hδ0
    refine tendsto_atTop_mono' atTop ?_ h1
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with L hL
    have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
    have : 1 ≤ Real.log L := by rw [Real.le_log_iff_exp_le hL0]; exact hL
    have : 1 ≤ Real.log L ^ 2 := one_le_pow₀ this
    have h2 : 0 ≤ δ * L := by positivity
    nlinarith
  have hsq : Tendsto (fun L : ℝ => δ * Real.log L ^ 2) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop).const_mul_atTop
      hδ0
  have hP : ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧ 1 ≤ δ * Real.log L ^ 2 ∧
      (δ * L * Real.log L ^ 2) * Real.exp (-(sincTailConst * ((δ * L * Real.log L ^ 2) /
        Real.log (δ * L * Real.log L ^ 2) ^ 2))) ≤ sincTail (δ * L * Real.log L ^ 2) := by
    filter_upwards [eventually_ge_atTop (Real.exp 1), hsq.eventually_ge_atTop 1,
      hc₀.eventually eventually_mul_exp_le_sincTail] with L h1 h2 h3
    exact ⟨h1, h2, h3⟩
  filter_upwards [loglog_atTop''.eventually hP, eventually_sincCriticalOverlap_le]
    with N ⟨hLe, hδl, htail⟩ ⟨_, hmem⟩
  set L := Real.log (Real.log N) with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hlogN := log_natCast_pos_of_loglog hL0
  have hlL : 1 ≤ Real.log L := by rw [Real.le_log_iff_exp_le hL0]; exact hLe
  set c₀ := δ * L * Real.log L ^ 2 with hc₀def
  have hscale : dcScale N / (4 * sincTailConst) = c₀ := by
    rw [hc₀def, hδ, dcScale]; ring
  rw [hscale]
  have hc₀L : L ≤ c₀ := by
    have := mul_le_mul_of_nonneg_left hδl hL0.le
    rw [hc₀def]; nlinarith
  have hc₀1 : 1 ≤ c₀ := by
    have : (1 : ℝ) ≤ L := by have := Real.add_one_le_exp 1; linarith
    linarith
  refine le_csInf ⟨_, hmem⟩ fun c ⟨hc1, hcτ⟩ => ?_
  by_contra hlt
  push Not at hlt
  have hlogc₀ : Real.log L ≤ Real.log c₀ := Real.log_le_log hL0 hc₀L
  have hE : sincTailConst * (c₀ / Real.log c₀ ^ 2) ≤ L / 4 := by
    have hlc0 : 0 < Real.log c₀ ^ 2 := by
      have : 0 < Real.log c₀ := by linarith
      positivity
    have hsq' : Real.log L ^ 2 ≤ Real.log c₀ ^ 2 := pow_le_pow_left₀ (by linarith) hlogc₀ 2
    rw [mul_div_assoc', div_le_iff₀ hlc0]
    have e : sincTailConst * c₀ = L / 4 * Real.log L ^ 2 := by
      rw [hc₀def, hδ]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hsq' (by linarith)
  have hτ : c₀ * Real.exp (-(L / 4)) ≤ sincTail c :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by linarith)).trans
      (htail.trans (sincTail_antitone (by linarith) hlt.le))
  have hgt : 1 < c₀ * Real.exp (-(L / 4)) * Real.log N := by
    rw [show Real.log N = Real.exp L from (Real.exp_log hlogN).symm, mul_assoc, ← Real.exp_add]
    have : 1 < Real.exp (-(L / 4) + L) := Real.one_lt_exp_iff.mpr (by linarith)
    nlinarith
  have := mul_le_mul_of_nonneg_right hτ hlogN.le
  linarith

/-! ### The rate law in exact Fourier-tail units -/

private theorem eventually_sincCritical_pos : ∀ᶠ N : ℕ in atTop, 0 < sincCriticalOverlap N := by
  filter_upwards [eventually_le_sincCriticalOverlap, dcScale_atTop.eventually_gt_atTop 0]
    with N h hS
  have := sincTailConst_pos
  exact lt_of_lt_of_le (by positivity) h

/-- The dilation `N/(K c*_N)` tends to infinity. -/
theorem tendsto_div_mul_sincCriticalOverlap {K : ℝ} (hK : 0 < K) :
    Tendsto (fun N : ℕ => (N : ℝ) / (K * sincCriticalOverlap N)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_div_const_mul_dcScale (show (0 : ℝ) < K * (96 * Real.exp 1) by positivity))
  filter_upwards [eventually_sincCriticalOverlap_le, eventually_sincCritical_pos] with N hle hpos
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
  have := mul_le_mul_of_nonneg_left hle.1 hK.le
  linarith

/-- **Every divergent multiple of the exact critical overlap is a receiver.** -/
theorem riemannHypothesis_iff_nonneg_of_sincCritical_rate {r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop)
    (hrN : Tendsto (fun N : ℕ => (N : ℝ) / (r N * sincCriticalOverlap N)) atTop atTop) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / (r N * sincCriticalOverlap N))
        sincProfile)) := by
  refine riemannHypothesis_iff_nonneg_of_divergent_rate contDiff_sincProfile
    sincProfile_vanishesOff integral_sincProfile (by norm_num : (0 : ℝ) ≤ 12)
    integral_abs_iteratedDeriv_sincProfile_le ?_ hrN
  have hδ : (0 : ℝ) < 1 / (4 * sincTailConst) := by have := sincTailConst_pos; positivity
  refine tendsto_atTop_mono' atTop ?_ (hr.atTop_mul_const hδ)
  filter_upwards [eventually_le_sincCriticalOverlap, dcScale_atTop.eventually_gt_atTop 0,
    hr.eventually_ge_atTop 0] with N h hS hr0
  rw [le_div_iff₀ hS]
  have := mul_le_mul_of_nonneg_left h hr0
  calc r N * (1 / (4 * sincTailConst)) * dcScale N = r N * (dcScale N / (4 * sincTailConst)) := by
        ring
    _ ≤ r N * sincCriticalOverlap N := this

/-- **A single bounded multiple of the exact critical overlap sees a window of radius
`½ log K + O(1)`.** -/
theorem nonneg_of_sincCritical_multiple {K : ℝ} (hK : 4 * sincTailConst ≤ K)
    (H : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / (K * sincCriticalOverlap N)) sincProfile)))
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R) (hgR : SupportedIn R g)
    (hRK : 24 * 12 * blockSize (R + 1) * Real.exp 1 < K / (4 * sincTailConst)) :
    0 ≤ weilQuad g := by
  have hKτ := sincTailConst_pos
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K / (4 * sincTailConst) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hcN := tendsto_div_mul_sincCriticalOverlap hK0
  have hrate : ∀ᶠ N : ℕ in atTop, K / (4 * sincTailConst) ≤
      dcRate (fun N : ℕ => (N : ℝ) / (K * sincCriticalOverlap N)) N := by
    have hc1 : ∀ᶠ N : ℕ in atTop, 1 ≤ K * sincCriticalOverlap N := by
      filter_upwards [eventually_le_sincCriticalOverlap,
        dcScale_atTop.eventually_ge_atTop (4 * sincTailConst)] with N h hS
      have h1 : 1 ≤ dcScale N / (4 * sincTailConst) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have h2 : 1 ≤ K := by
        have : (1 : ℝ) ≤ 4 * sincTailConst := by unfold sincTailConst; nlinarith [Real.pi_pos]
        linarith
      nlinarith
    filter_upwards [eventually_div_dcScale_le_dcRate hcN hc1, eventually_le_sincCriticalOverlap,
      dcScale_atTop.eventually_gt_atTop 0] with N h hlow hS
    refine le_trans ?_ h
    rw [le_div_iff₀ hS]
    calc K / (4 * sincTailConst) * dcScale N = K * (dcScale N / (4 * sincTailConst)) := by ring
      _ ≤ K * sincCriticalOverlap N := mul_le_mul_of_nonneg_left hlow hK0.le
  exact nonneg_of_atomicFamilies_nonneg_of_rate stableForm_weilQuad contDiff_sincProfile
    sincProfile_vanishesOff integral_sincProfile (by norm_num : (0 : ℝ) ≤ 12)
    integral_abs_iteratedDeriv_sincProfile_le hcN hK1 hrate H hg hR hgR hRK

/-- **RH is the union of the bounded multiples of the exact critical overlap.** -/
theorem riemannHypothesis_iff_forall_sincCritical_multiple :
    RiemannHypothesis ↔ ∀ K : ℝ, 1 ≤ K → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / (K * sincCriticalOverlap N))
        sincProfile)) := by
  have hφ2 : ContDiff ℝ 2 sincProfile := contDiff_sincProfile.of_le (natCast_le_infty 2)
  constructor
  · intro hRH K hK
    filter_upwards [(tendsto_div_mul_sincCriticalOverlap
      (by linarith : (0 : ℝ) < K)).eventually_gt_atTop 0] with N hk x
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ2 sincProfile_vanishesOff hk N x
    exact RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH _ h2 hc
  · intro H
    refine RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mpr fun g hg hgc => ?_
    obtain ⟨R, -, -, hR, hgR, -, -⟩ := exists_test_bounds hg hgc
    have hKτ := sincTailConst_pos
    set K : ℝ := 4 * sincTailConst * (24 * 12 * blockSize (R + 1) * Real.exp 1 + 1)
    have hb : (0 : ℝ) ≤ 24 * 12 * blockSize (R + 1) * Real.exp 1 := by positivity
    have hK4 : 4 * sincTailConst ≤ K := by nlinarith
    have hK1 : 1 ≤ K := by
      have : (1 : ℝ) ≤ 4 * sincTailConst := by unfold sincTailConst; nlinarith [Real.pi_pos]
      linarith
    refine nonneg_of_sincCritical_multiple hK4 (H K hK1) hg hR hgR ?_
    have hKdiv : K / (4 * sincTailConst) = 24 * 12 * blockSize (R + 1) * Real.exp 1 + 1 :=
      mul_div_cancel_left₀ _ (by positivity)
    rw [hKdiv]
    linarith

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_le_sincCriticalOverlap
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_sincCriticalOverlap_le
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.riemannHypothesis_iff_nonneg_of_sincCritical_rate
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.nonneg_of_sincCritical_multiple
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.riemannHypothesis_iff_forall_sincCritical_multiple
