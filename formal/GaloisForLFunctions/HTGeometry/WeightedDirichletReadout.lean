import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.Complex.Convex
import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient

/-!
# Weighted Dirichlet readouts on horizontal lines

For coefficients `c : ℕ → ℂ` with `Σ ‖cₙ‖ n^η < ∞` (`η ≥ 0`), the readout

`F(z) = Σ_{n ≥ 1} cₙ n^{iz} = LSeries c (-iz)`

converges absolutely on the closed half-plane `Im z ≥ -η`, where `‖F‖ ≤ Σ ‖cₙ‖ n^η`, and is
holomorphic on the open half-plane `Im z > -η`.  On the real line it is an absolutely convergent
exponential series with the injective frequencies `log n`, so its Bohr coefficient at `log m` is
`c m`: the coefficients are recovered from the real values, and a readout vanishing on the real line
has zero coefficients.  A readout agreeing with an entire function on a nonempty open real interval
agrees with it on the whole half-plane.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set LSeries

namespace GaloisForLFunctions.HTGeometry

/-- `Σ ‖cₙ‖ n^η < ∞`. -/
def WeightedAbsSummable (c : ℕ → ℂ) (η : ℝ) : Prop :=
  Summable fun n : ℕ => ‖c n‖ * (n : ℝ) ^ η

/-- The readout `F(z) = Σ_{n ≥ 1} cₙ n^{iz}`. -/
def dirichletReadout (c : ℕ → ℂ) (z : ℂ) : ℂ := LSeries c (-(I * z))

theorem re_neg_I_mul_eq_im (z : ℂ) : (-(I * z)).re = z.im := by simp

theorem norm_term_le_weighted (c : ℕ → ℂ) {η : ℝ} {s : ℂ} (hs : -η ≤ s.re) (n : ℕ) :
    ‖term c s n‖ ≤ ‖c n‖ * (n : ℝ) ^ η := by
  rw [norm_term_eq]
  split_ifs with hn
  · by_cases hη : η = 0
    · subst hη; simp
    · rw [hn]; simp [Real.zero_rpow hη]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hpos : (0 : ℝ) < n := by linarith
    rw [div_eq_mul_inv, ← Real.rpow_neg hpos.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      (norm_nonneg _)

theorem WeightedAbsSummable.summable_norm_term {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η)
    {s : ℂ} (hs : -η ≤ s.re) : Summable fun n => ‖term c s n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le_weighted c hs) hc

theorem WeightedAbsSummable.lSeriesSummable {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η)
    {s : ℂ} (hs : -η ≤ s.re) : LSeriesSummable c s :=
  Summable.of_norm (hc.summable_norm_term hs)

theorem WeightedAbsSummable.summable_norm {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η)
    (hη : 0 ≤ η) : Summable fun n => ‖c n‖ := by
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_nat_add_iff 1).mpr hc)
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
  calc ‖c (n + 1)‖ = ‖c (n + 1)‖ * 1 := (mul_one _).symm
    _ ≤ ‖c (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ η := by
        gcongr; exact Real.one_le_rpow h1 hη

theorem WeightedAbsSummable.mono {c : ℕ → ℂ} {η η' : ℝ} (hc : WeightedAbsSummable c η)
    (hη' : 0 < η') (hle : η' ≤ η) : WeightedAbsSummable c η' := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hc
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, Real.zero_rpow hη'.ne', mul_zero]
    positivity
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hle) (norm_nonneg _)

/-- **The readout is bounded by the weighted mass on `Im z ≥ -η`.** -/
theorem norm_dirichletReadout_le {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η) {z : ℂ}
    (hz : -η ≤ z.im) : ‖dirichletReadout c z‖ ≤ ∑' n, ‖c n‖ * (n : ℝ) ^ η := by
  have hs : -η ≤ (-(I * z)).re := by rw [re_neg_I_mul_eq_im]; exact hz
  unfold dirichletReadout LSeries
  exact (norm_tsum_le_tsum_norm (hc.summable_norm_term hs)).trans
    ((hc.summable_norm_term hs).tsum_le_tsum (norm_term_le_weighted c hs) hc)

theorem abscissaOfAbsConv_le_of_weighted {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η) :
    abscissaOfAbsConv c ≤ ((-η : ℝ) : EReal) := by
  have h := (hc.lSeriesSummable (s := ((-η : ℝ) : ℂ)) (by simp)).abscissaOfAbsConv_le
  simpa using h

/-- **The readout is holomorphic on `Im z > -η`.** -/
theorem differentiableOn_dirichletReadout {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η) :
    DifferentiableOn ℂ (dirichletReadout c) {z : ℂ | -η < z.im} := by
  have hmaps : MapsTo (fun z : ℂ => -(I * z)) {z : ℂ | -η < z.im}
      {s : ℂ | abscissaOfAbsConv c < (s.re : EReal)} := by
    intro z hz
    simp only [mem_setOf_eq] at hz ⊢
    rw [re_neg_I_mul_eq_im]
    exact (abscissaOfAbsConv_le_of_weighted hc).trans_lt (EReal.coe_lt_coe_iff.mpr hz)
  exact (LSeries_differentiableOn c).comp
    ((differentiableOn_id.const_mul I).neg) hmaps

theorem isOpen_halfPlane_im_gt (η : ℝ) : IsOpen {z : ℂ | -η < z.im} :=
  isOpen_lt continuous_const continuous_im

theorem analyticOnNhd_dirichletReadout {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η) :
    AnalyticOnNhd ℂ (dirichletReadout c) {z : ℂ | -η < z.im} :=
  (differentiableOn_dirichletReadout hc).analyticOnNhd (isOpen_halfPlane_im_gt η)

/-! ### The real line: an exponential series -/

theorem natCast_cpow_I_mul (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (I * (t : ℂ)) = GaloisForLFunctions.expChar (Real.log n) t := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [GaloisForLFunctions.expChar, cpow_def_of_ne_zero (by exact_mod_cast hn),
    ← ofReal_natCast, ← ofReal_log hpos.le]
  congr 1
  push_cast
  ring

/-- On the real line the readout is the exponential series `Σ c_{m+1} e^{i t log (m+1)}`. -/
theorem dirichletReadout_ofReal {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η) (hη : 0 ≤ η)
    (t : ℝ) :
    dirichletReadout c t = GaloisForLFunctions.expSeriesCarrier (fun m => c (m + 1))
      (fun m => Real.log ((m + 1 : ℕ) : ℝ)) t := by
  have hs : LSeriesSummable c (-(I * (t : ℂ))) := hc.lSeriesSummable (by simp; linarith)
  unfold dirichletReadout LSeries GaloisForLFunctions.expSeriesCarrier
  rw [hs.tsum_eq_zero_add]
  simp only [term_zero, zero_add]
  refine tsum_congr fun m => ?_
  rw [term_of_ne_zero (Nat.succ_ne_zero m), cpow_neg, div_inv_eq_mul,
    natCast_cpow_I_mul (m + 1) (Nat.succ_ne_zero m)]

theorem injective_log_succ : Function.Injective fun m : ℕ => Real.log ((m + 1 : ℕ) : ℝ) := by
  intro a b h
  have ha : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
  have hb : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) := by positivity
  have := Real.log_injOn_pos ha hb h
  exact_mod_cast Nat.succ_injective (by exact_mod_cast this)

/-- **Bohr coefficients recover the Dirichlet coefficients.** -/
theorem bohrCoefficient_dirichletReadout {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η)
    (hη : 0 ≤ η) {m : ℕ} (hm : 0 < m) :
    GaloisForLFunctions.bohrCoefficient (fun t : ℝ => dirichletReadout c t) (Real.log m) = c m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hsum : Summable fun i => ‖c (i + 1)‖ :=
    (summable_nat_add_iff 1).mpr (hc.summable_norm hη)
  have e : (fun t : ℝ => dirichletReadout c t) = GaloisForLFunctions.expSeriesCarrier
      (fun m => c (m + 1)) (fun m => Real.log ((m + 1 : ℕ) : ℝ)) :=
    funext (dirichletReadout_ofReal hc hη)
  rw [e]
  exact GaloisForLFunctions.bohrCoefficient_expSeriesCarrier hsum injective_log_succ k

theorem bohrCoefficient_zero_fun (lam : ℝ) :
    GaloisForLFunctions.bohrCoefficient (fun _ : ℝ => (0 : ℂ)) lam = 0 := by
  have h := GaloisForLFunctions.tendsto_windowAverage_bohrCoefficient
    (f := fun _ : ℝ => (0 : ℂ)) continuous_const
    (GaloisForLFunctions.isBohrAlmostPeriodic_const 0) lam
  have h0 : (GaloisForLFunctions.windowAverage fun t : ℝ =>
      (fun _ : ℝ => (0 : ℂ)) t * GaloisForLFunctions.bohrChar lam t) = fun _ => 0 := by
    funext T
    simp [GaloisForLFunctions.windowAverage]
  rw [h0] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **Uniqueness.**  A readout vanishing on the real line has zero coefficients. -/
theorem coeff_eq_zero_of_dirichletReadout_eq_zero {c : ℕ → ℂ} {η : ℝ}
    (hc : WeightedAbsSummable c η) (hη : 0 ≤ η) (h : ∀ t : ℝ, dirichletReadout c t = 0) {m : ℕ}
    (hm : 0 < m) : c m = 0 := by
  rw [← bohrCoefficient_dirichletReadout hc hη hm]
  have e : (fun t : ℝ => dirichletReadout c t) = fun _ => 0 := funext h
  rw [e, bohrCoefficient_zero_fun]

/-- Readouts with the same values on the real line have the same coefficients. -/
theorem coeff_eq_of_dirichletReadout_eq {c d : ℕ → ℂ} {η : ℝ}
    (hc : WeightedAbsSummable c η) (hd : WeightedAbsSummable d η) (hη : 0 ≤ η)
    (h : ∀ t : ℝ, dirichletReadout c t = dirichletReadout d t) {m : ℕ} (hm : 0 < m) :
    c m = d m := by
  rw [← bohrCoefficient_dirichletReadout hc hη hm, ← bohrCoefficient_dirichletReadout hd hη hm]
  exact congrArg (fun f => GaloisForLFunctions.bohrCoefficient f (Real.log m)) (funext h)

/-! ### Analytic continuation from an interval -/

/-- **Identity theorem.**  A readout agreeing with an entire function on a nonempty open real
interval agrees with it on the whole half-plane `Im z > -η`. -/
theorem dirichletReadout_eq_of_eqOn_Ioo {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η)
    (hη : 0 < η) {g : ℂ → ℂ} (hg : Differentiable ℂ g) {a b : ℝ} (hab : a < b)
    (h : ∀ t ∈ Ioo a b, dirichletReadout c t = g t) {z : ℂ} (hz : -η < z.im) :
    dirichletReadout c z = g z := by
  set t₀ : ℝ := (a + b) / 2
  have hU : IsPreconnected {z : ℂ | -η < z.im} := (convex_halfSpace_im_gt (-η)).isPreconnected
  have hmem : ((t₀ : ℝ) : ℂ) ∈ {z : ℂ | -η < z.im} := by simp; linarith
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] t₀, dirichletReadout c (t : ℂ) = g (t : ℂ) := by
    have hI : Ioo a b ∈ 𝓝 t₀ := Ioo_mem_nhds (by simp [t₀]; linarith) (by simp [t₀]; linarith)
    filter_upwards [nhdsWithin_le_nhds hI] with t ht using h t ht
  have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] t₀) (𝓝[≠] ((t₀ : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_ofReal.tendsto t₀).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact fun h' => ht (ofReal_injective h')
  have hfreq : ∃ᶠ z in 𝓝[≠] ((t₀ : ℝ) : ℂ), dirichletReadout c z = g z :=
    htend.frequently hev.frequently
  exact (analyticOnNhd_dirichletReadout hc).eqOn_of_preconnected_of_frequently_eq
    ((hg.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)) hU hmem hfreq hz

end GaloisForLFunctions.HTGeometry
