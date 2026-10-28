import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheEulerMaclaurinSynthesis

/-!
# The overlap law at every root

For a smooth profile the Euler–Maclaurin synthesis (`TheEulerMaclaurinSynthesis`) is accurate to
every order `(k/n₀)^p`, so the overlap ratio needed to synthesize a fixed test drops from `√(log N)`
(first order, `TheCriticalExponent`) and `(log N)^{1/4}` (second order, `TheSecondOrderSynthesis`)
to `(log N)^ε` for every `ε > 0`.

* **Smooth negative tests** (`exists_smooth_weilQuad_neg`): if Weil's form is negative on a `C²`
  test, it is negative on a smooth one. Convolving with a dilated smooth profile `φ_m` moves the
  test by `O(1/m)` in supremum with Lipschitz constant `O(m)`, hence by `O((log m)/m²)` in the Lévy
  energy, and Weil's form is continuous in the Lévy norm.
* **Overlap growth of order `q`** (`OverlapGrowthPow`): `κ_N → ∞` and `(κ_N/N)^q log κ_N → 0`.
  It weakens as `q` grows (`OverlapGrowthPow.mono`).
* **The overlap law at every root** (`riemannHypothesis_iff_atomicFamilies_nonneg_of_growthPow`):
  for every smooth profile `φ` supported in `[−1, 1]` with `∫ φ = 1`, every `q`, and every dilation
  sequence of overlap growth of order `q`, RH holds iff Weil's form is eventually nonnegative on the
  atomic families of width `1/κ_N`. In particular at widths `(log N)^α/N` for every `α > 0`
  (`riemannHypothesis_iff_atomicFamilies_nonneg_log_pos`): positivity is RH as soon as the overlap
  ratio is unbounded at any power of `log N`.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower
open scoped Real ContDiff Convolution

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### Smooth negative tests -/

section Mollify

variable {φ g : ℝ → ℝ}

/-- The mollification `g_m(x) = ∫ g(t) φ_m(x − t) dt`. -/
def mollify (g φ : ℝ → ℝ) (m : ℝ) (x : ℝ) : ℝ := ∫ t, g t * dilate m φ (x - t)

theorem mollify_eq_convolution (g φ : ℝ → ℝ) (m : ℝ) :
    mollify g φ m = g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] dilate m φ := by
  funext x; rfl

theorem contDiff_dilate_smooth (hφ : ContDiff ℝ ∞ φ) (m : ℝ) : ContDiff ℝ ∞ (dilate m φ) :=
  contDiff_const.mul (hφ.comp (contDiff_const.mul contDiff_id))

theorem hasCompactSupport_dilate_of (hφ1 : VanishesOff φ) {m : ℝ} (hm : 0 < m) :
    HasCompactSupport (dilate m φ) :=
  hasCompactSupport_of_vanishes fun _ hs => dilate_vanishes hφ1 hm hs

theorem contDiff_mollify (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hg : Continuous g)
    {m : ℝ} (hm : 0 < m) : ContDiff ℝ ∞ (mollify g φ m) := by
  rw [mollify_eq_convolution]
  exact (hasCompactSupport_dilate_of hφ1 hm).contDiff_convolution_right _
    (hg.locallyIntegrable (μ := volume)) (contDiff_dilate_smooth hφ m)

/-- **The mollified test is `O(m)`-Lipschitz**: `|g_m′| ≤ M m ‖φ′‖₁`. -/
theorem abs_mollify_sub_le (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hg : Continuous g)
    {M : ℝ} (hgM : ∀ t, |g t| ≤ M) {m : ℝ} (hm : 0 < m) (u v : ℝ) :
    |mollify g φ m u - mollify g φ m v| ≤ M * (m * ∫ s, |deriv φ s|) * |u - v| := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (natCast_le_infty 2)
  have hψc := hasCompactSupport_dilate_of hφ1 hm
  have hψ1 : ContDiff ℝ 1 (dilate m φ) := (contDiff_dilate_smooth hφ m).of_le (natCast_le_infty 1)
  have hderiv : ∀ x, deriv (dilate m φ) x = dilate m (fun s => m * deriv φ s) x := fun x =>
    (hasDerivAt_dilate_profile hφ2 x).deriv
  refine abs_sub_le_of_hasDerivAt (f := mollify g φ m)
    (f' := fun x => ∫ t, g t * deriv (dilate m φ) (x - t)) (fun x => ?_) (fun x => ?_) u v
  · rw [mollify_eq_convolution]
    exact hψc.hasDerivAt_convolution_right _ (hg.locallyIntegrable (μ := volume)) hψ1 x
  · have hint : Integrable (deriv (dilate m φ)) := by
      have hc : Continuous (deriv (dilate m φ)) :=
        (contDiff_dilate_smooth hφ m).continuous_deriv (by simp)
      exact hc.integrable_of_hasCompactSupport hψc.deriv
    have h := abs_integral_mul_le_sup_mul hgM hint x
    have he : ∫ s, |deriv (dilate m φ) s| = m * ∫ s, |deriv φ s| := by
      simp_rw [hderiv]; exact integral_abs_dilate_mul hm (deriv φ)
    rwa [he] at h

/-- The mollified test lives in `[−(R+1), R+1]` for `m ≥ 1`. -/
theorem mollify_supportedIn (hφ1 : VanishesOff φ) {R : ℝ} (hgR : SupportedIn R g) {m : ℝ}
    (hm : 1 ≤ m) : SupportedIn (R + 1) (mollify g φ m) := by
  intro x hx
  have hm0 : 0 < m := by linarith
  unfold mollify
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  show g t * dilate m φ (x - t) = 0
  by_cases ht : |t| ≤ R
  · rw [dilate_vanishes hφ1 hm0 (by
      have h1 : 1 / m ≤ 1 := by rw [div_le_one hm0]; exact hm
      have := abs_sub_abs_le_abs_sub x t
      linarith), mul_zero]
  · push Not at ht
    rw [hgR t ht, zero_mul]

/-- **The mollification as a perturbation**: `D = g_m − g` is a `C²` test supported in
`[−(R+1), R+1]` with `|D| ≤ L ‖φ‖₁/m` and Lipschitz constant `M m ‖φ′‖₁ + L`. -/
theorem mollify_perturbation (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    (hg : ContDiff ℝ 2 g) {R M L : ℝ} (hgR : SupportedIn R g) (hgM : ∀ t, |g t| ≤ M)
    (hgL : ∀ u v, |g u - g v| ≤ L * |u - v|) {m : ℝ} (hm : 1 ≤ m) :
    ContDiff ℝ 2 (fun x => mollify g φ m x - g x) ∧
      SupportedIn (R + 1) (fun x => mollify g φ m x - g x) ∧
      (∀ x, |mollify g φ m x - g x| ≤ L * (1 / m) * ∫ s, |φ s|) ∧
      ∀ u v, |(mollify g φ m u - g u) - (mollify g φ m v - g v)| ≤
        (M * (m * ∫ s, |deriv φ s|) + L) * |u - v| := by
  have hm0 : 0 < m := by linarith
  have hgR1 : SupportedIn (R + 1) g := fun u hu => hgR u (by linarith)
  refine ⟨((contDiff_mollify hφ hφ1 hg.continuous hm0).of_le (natCast_le_infty 2)).sub hg,
    fun u hu => by simp only [mollify_supportedIn hφ1 hgR hm u hu, hgR1 u hu, sub_zero],
    fun x => ?_, fun u v => ?_⟩
  · have := abs_integral_mul_sub_le hg.continuous (contDiff_dilate_smooth hφ m).continuous
      (hasCompactSupport_dilate_of hφ1 hm0) (by rw [integral_dilate hm0, hφint])
      (fun s hs => dilate_vanishes hφ1 hm0 hs) hgL x
    rwa [integral_abs_dilate hm0] at this
  · rw [show (mollify g φ m u - g u) - (mollify g φ m v - g v) =
      (mollify g φ m u - mollify g φ m v) - (g u - g v) by ring]
    refine (abs_sub _ _).trans ?_
    have := add_le_add (abs_mollify_sub_le hφ hφ1 hg.continuous hgM hm0 u v) (hgL u v)
    linarith

/-- The mollification errors vanish: `L ‖φ‖₁/m → 0` and its Lévy bound tends to `0`. -/
theorem tendsto_mollifyErr (L A0 M A1 R' : ℝ) :
    Tendsto (fun n : ℕ => L * (1 / (n : ℝ)) * A0) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => synthLevy R' (L * (1 / (n : ℝ)) * A0) (M * ((n : ℝ) * A1) + L) n)
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log n * (L * (1 / (n : ℝ)) * A0) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (M * ((n : ℝ) * A1) + L) * (1 / (n : ℝ))) atTop (𝓝 (M * A1)) := by
  have hm : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simp only [one_div]; exact hm.inv_tendsto_atTop
  have he : Tendsto (fun n : ℕ => L * (1 / (n : ℝ)) * A0) atTop (𝓝 0) := by
    simpa using (hinv.const_mul L).mul_const A0
  have hlog : Tendsto (fun n : ℕ => Real.log n * (1 / (n : ℝ)) ^ 2) atTop (𝓝 0) := by
    refine ((tendsto_log_mul_rpow_neg two_pos).comp hm).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp]
    rw [Real.rpow_neg hn0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hlog' : Tendsto (fun n : ℕ => Real.log n * (L * (1 / (n : ℝ)) * A0) ^ 2) atTop (𝓝 0) := by
    have := hlog.const_mul ((L * A0) ^ 2)
    rw [mul_zero] at this
    exact this.congr fun n => by ring
  have hLD : Tendsto (fun n : ℕ => (M * ((n : ℝ) * A1) + L) * (1 / (n : ℝ))) atTop
      (𝓝 (M * A1)) := by
    have := (tendsto_const_nhds (x := M * A1)).add (hinv.const_mul L)
    rw [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
  refine ⟨he, ?_, hlog', hLD⟩
  have h1 := ((tendsto_const_nhds (x := M * A1)).add (hinv.const_mul L)).mul he
  have h2 := (hlog.const_mul (2 * (L * A0) ^ 2 * (2 * R')))
  have h3 := ((he.pow 2).const_mul (levyLipConstant * (2 * R')))
  have := ((h1.const_mul (Real.exp (1 / 2) * (2 * R'))).add h2).add h3
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold synthLevy
  field_simp
  ring

/-- Radius, supremum and Lipschitz bounds of a `C²` test with compact support. -/
theorem exists_test_bounds (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∃ R M L : ℝ, 0 ≤ R ∧ SupportedIn R g ∧ (∀ t, |g t| ≤ M) ∧
      ∀ u v, |g u - g v| ≤ L * |u - v| := by
  obtain ⟨R0, hR0⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  refine ⟨max R0 0, M, C, le_max_right _ _, fun u hu => ?_, fun t => by
    simpa [Real.norm_eq_abs] using hM t, fun u v => by
    simpa [Real.dist_eq] using hC.dist_le_mul u v⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hR0 hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left R0 0]

/-- **Smooth negative tests**: if Weil's form is negative on a `C²` test with compact support, it is
negative on a smooth test with compact support. -/
theorem exists_smooth_weilQuad_neg (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hneg : weilQuad g < 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ weilQuad G < 0 := by
  obtain ⟨R, M, L, hR, hgR, hgM, hgL⟩ := exists_test_bounds hg hgc
  obtain ⟨he, hV, -, -⟩ := tendsto_mollifyErr L (∫ s, |φ s|) M (∫ s, |deriv φ s|) (R + 1)
  have hErr := tendsto_weilErr g (R + 1) he hV
  obtain ⟨n, hn1, hn2⟩ := ((hErr.eventually (gt_mem_nhds
    (show (0 : ℝ) < -weilQuad g by linarith))).and (eventually_ge_atTop 1)).exists
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn2
  refine ⟨mollify g φ n, contDiff_mollify hφ hφ1 hg.continuous (by linarith),
    hasCompactSupport_of_vanishes (mollify_supportedIn hφ1 hgR hn), ?_⟩
  obtain ⟨hD2, hDR, hsup, hlip⟩ := mollify_perturbation hφ hφ1 hφint hg hgR hgM hgL hn
  have h := weilQuad_add_le_of_lip hg hgc (fun u hu => hgR u (by linarith)) hD2 hDR
    (by linarith) hsup hlip hn
  have he' : (fun u => g u + (mollify g φ n u - g u)) = mollify g φ n := by funext u; ring
  rw [he'] at h
  linarith

end Mollify

/-! ### Overlap growth of order `q` -/

section Growth

/-- **Overlap growth of order `q`**: dilations `κ_N → ∞` whose overlap ratio `N/κ_N` beats
`(log κ_N)^{1/q}`, i.e. `(κ_N/N)^q log κ_N → 0`. Order `2` is `OverlapGrowth`, order `4` is
`OverlapGrowthTwo`. -/
def OverlapGrowthPow (q : ℕ) (κ : ℕ → ℝ) : Prop :=
  Tendsto κ atTop atTop ∧ Tendsto (fun N : ℕ => (κ N / N) ^ q * Real.log (κ N)) atTop (𝓝 0)

/-- Overlap growth of order `q` is overlap growth of every higher order. -/
theorem OverlapGrowthPow.mono {q q' : ℕ} {κ : ℕ → ℝ} (hκ : OverlapGrowthPow q κ)
    (hqq : q ≤ q') : OverlapGrowthPow q' κ := by
  obtain ⟨hk, hkl⟩ := hκ
  refine ⟨hk, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (κ N)) atTop atTop := Real.tendsto_log_atTop.comp hk
  have hrq : Tendsto (fun N : ℕ => (κ N / N) ^ q) atTop (𝓝 0) := by
    refine (hkl.div_atTop hlog).congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with N hN
    field_simp
  have hr1 : ∀ᶠ N : ℕ in atTop, 0 ≤ κ N / N ∧ κ N / N ≤ 1 := by
    filter_upwards [hrq.eventually (gt_mem_nhds one_pos), hk.eventually_ge_atTop 0] with N h1 h0
    have h0' : 0 ≤ κ N / N := div_nonneg h0 (Nat.cast_nonneg _)
    refine ⟨h0', ?_⟩
    by_contra h
    push Not at h
    have := one_le_pow₀ (n := q) h.le
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hkl ?_ ?_
  · filter_upwards [hr1, hk.eventually_ge_atTop 1] with N ⟨h0, _⟩ h1
    exact mul_nonneg (pow_nonneg h0 _) (Real.log_nonneg h1)
  · filter_upwards [hr1, hk.eventually_ge_atTop 1] with N ⟨h0, h1⟩ hk1
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one h0 h1 hqq) (Real.log_nonneg hk1)

theorem emErr_sq_le (M A : ℕ → ℝ) (m : ℕ) (k : ℝ) (n₀ : ℕ) :
    emErr M A m k n₀ ^ 2 ≤ 2 * emConst M A m ^ 2 * (k / n₀) ^ (2 * (2 * m + 2)) +
      2 * (M 1 * A 0) ^ 2 * (1 / k) ^ 2 := by
  unfold emErr
  rw [pow_mul']
  nlinarith [sq_nonneg (emConst M A m * (k / n₀) ^ (2 * m + 2) - M 1 * (1 / k) * A 0)]

/-- The synthesis errors vanish along any sequence `k_n → ∞` with `(k_n/n)^{2p} log k_n → 0`. -/
theorem tendsto_em_aux {K : ℕ → ℝ} {m : ℕ} (hK : Tendsto K atTop atTop)
    (hρl : Tendsto (fun n : ℕ => (K n / n) ^ (2 * (2 * m + 2)) * Real.log (K n)) atTop (𝓝 0))
    {M A : ℕ → ℝ} {R' : ℝ} :
    Tendsto (fun n : ℕ => emErr M A m (K n) n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => synthLevy R' (emErr M A m (K n) n) (emLip M A (K n) n) (K n))
        atTop (𝓝 0) ∧
      Tendsto (fun n => Real.log (K n) * emErr M A m (K n) n ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => emLip M A (K n) n * (1 / K n)) atTop (𝓝 (M 0 * A 1)) := by
  have hlogK : Tendsto (fun n => Real.log (K n)) atTop atTop := Real.tendsto_log_atTop.comp hK
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ K n ∧ 1 ≤ n := (hK.eventually_ge_atTop 1).and
    (eventually_ge_atTop 1)
  have hρ0 : ∀ᶠ n : ℕ in atTop, 0 ≤ K n / n := by
    filter_upwards [hev] with n ⟨h1, _⟩
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hρ2p : Tendsto (fun n : ℕ => (K n / n) ^ (2 * (2 * m + 2))) atTop (𝓝 0) := by
    refine (hρl.div_atTop hlogK).congr' ?_
    filter_upwards [hlogK.eventually_gt_atTop 0] with n hn
    field_simp
  have hρ : Tendsto (fun n : ℕ => K n / n) atTop (𝓝 0) := by
    have := hρ2p.rpow_const (p := ((2 * (2 * m + 2) : ℕ) : ℝ)⁻¹) (Or.inr (by positivity))
    rw [Real.zero_rpow (by positivity)] at this
    refine this.congr' ?_
    filter_upwards [hρ0] with n hn
    exact Real.pow_rpow_inv_natCast hn (by positivity)
  have hinv : Tendsto (fun n => 1 / K n) atTop (𝓝 0) := by
    simp only [one_div]; exact hK.inv_tendsto_atTop
  have hlinv : Tendsto (fun n => (1 / K n) ^ 2 * Real.log (K n)) atTop (𝓝 0) := by
    refine ((tendsto_log_mul_rpow_neg two_pos).comp hK).congr' ?_
    filter_upwards [hK.eventually_gt_atTop 0] with n hn
    simp only [Function.comp]
    rw [Real.rpow_neg hn.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have he : Tendsto (fun n => emErr M A m (K n) n) atTop (𝓝 0) := by
    have := ((hρ.pow (2 * m + 2)).const_mul (emConst M A m)).add
      ((hinv.const_mul (M 1)).mul_const (A 0))
    rw [zero_pow (by omega), mul_zero, mul_zero, zero_mul, add_zero] at this
    exact this
  have hLE : Tendsto (fun n => Real.log (K n) * emErr M A m (K n) n ^ 2) atTop (𝓝 0) := by
    have hup := (hρl.const_mul (2 * emConst M A m ^ 2)).add
      (hlinv.const_mul (2 * (M 1 * A 0) ^ 2))
    simp only [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hev] with n ⟨h1, _⟩
      exact mul_nonneg (Real.log_nonneg h1) (sq_nonneg _)
    · filter_upwards [hev] with n ⟨h1, _⟩
      have hl := Real.log_nonneg h1
      have := mul_le_mul_of_nonneg_left (emErr_sq_le M A m (K n) n) hl
      linarith
  set E' := emConst M (fun q => A (q + 1)) 0
  have hG : Tendsto (fun n : ℕ => M 0 * A 1 + E' * (K n / n) ^ 2 + M 1 * (1 / K n)) atTop
      (𝓝 (M 0 * A 1 + E' * 0 ^ 2 + M 1 * 0)) :=
    (tendsto_const_nhds.add ((hρ.pow 2).const_mul E')).add (hinv.const_mul (M 1))
  have hLD : ∀ᶠ n : ℕ in atTop,
      emLip M A (K n) n * (1 / K n) = M 0 * A 1 + E' * (K n / n) ^ 2 + M 1 * (1 / K n) := by
    filter_upwards [hev] with n ⟨h1, hn⟩
    have hK0 : 0 < K n := by linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [emLip, E']
    field_simp
  have hLDt : Tendsto (fun n => emLip M A (K n) n * (1 / K n)) atTop (𝓝 (M 0 * A 1)) := by
    have := hG
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
      at this
    exact this.congr' (hLD.mono fun n h => h.symm)
  refine ⟨he, ?_, hLE, hLDt⟩
  have hV := ((hG.mul he).const_mul (Real.exp (1 / 2) * (2 * R'))).add
    (((hLE.const_mul 2).add ((he.pow 2).const_mul levyLipConstant)).mul_const (2 * R'))
  simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hV
  refine hV.congr' ?_
  filter_upwards [hLD] with n hLD
  unfold synthLevy
  rw [show Real.exp (1 / 2) * emLip M A (K n) n * (1 / K n) * (2 * R' * emErr M A m (K n) n) =
    Real.exp (1 / 2) * (emLip M A (K n) n * (1 / K n)) * (2 * R' * emErr M A m (K n) n) by ring,
    hLD]
  ring

/-- **The Euler–Maclaurin synthesis errors vanish** under overlap growth of order `2(2m+2)`: along
the levels `n B`, with `k = κ_{nB}`, the supremum error and the Lévy bound tend to `0`. -/
theorem tendsto_em {κ : ℕ → ℝ} {m : ℕ} (hκ : OverlapGrowthPow (2 * (2 * m + 2)) κ) {B : ℕ}
    (hB : 1 ≤ B) {M A : ℕ → ℝ} {R' : ℝ} :
    Tendsto (fun n : ℕ => emErr M A m (κ (n * B)) n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => synthLevy R' (emErr M A m (κ (n * B)) n) (emLip M A (κ (n * B)) n)
        (κ (n * B))) atTop (𝓝 0) ∧
      Tendsto (fun n => Real.log (κ (n * B)) * emErr M A m (κ (n * B)) n ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => emLip M A (κ (n * B)) n * (1 / κ (n * B))) atTop (𝓝 (M 0 * A 1)) := by
  obtain ⟨hk, hkl⟩ := hκ
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  refine tendsto_em_aux (K := fun n => κ (n * B)) (hk.comp hNB) ?_
  have := (hkl.comp hNB).const_mul ((B : ℝ) ^ (2 * (2 * m + 2)))
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (B : ℝ) * (κ (n * B) / ((n * B : ℕ) : ℝ)) = κ (n * B) / n := by
    push_cast; field_simp
  show (B : ℝ) ^ (2 * (2 * m + 2)) * ((κ (n * B) / ((n * B : ℕ) : ℝ)) ^ (2 * (2 * m + 2)) *
    Real.log (κ (n * B))) = (κ (n * B) / n) ^ (2 * (2 * m + 2)) * Real.log (κ (n * B))
  rw [← hx, mul_pow]
  ring

/-- Widths `(log N)^α/N` — overlap ratio `(log N)^α` — have overlap growth of every order `q`
with `qα > 1`. -/
theorem overlapGrowthPow_log {α : ℝ} (hα : 0 < α) {q : ℕ} (hq : 1 < q * α) :
    OverlapGrowthPow q fun N : ℕ => (N : ℝ) / Real.log N ^ α := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hκ : Tendsto (fun N : ℕ => (N : ℝ) / Real.log N ^ α) atTop atTop := by
    have ho := (isLittleO_log_rpow_rpow_atTop α one_pos).tendsto_div_nhds_zero
    have hpos : ∀ᶠ y : ℝ in atTop, 0 < Real.log y ^ α / y ^ (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop 1] with y hy
      exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hy) α) (by positivity)
    have hinv := (tendsto_nhdsWithin_iff.mpr ⟨ho, hpos⟩).inv_tendsto_nhdsGT_zero
    refine (hinv.comp tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp, Real.rpow_one, Pi.inv_apply, inv_div]
  refine ⟨hκ, ?_⟩
  have hup : Tendsto (fun N : ℕ => Real.log N ^ (-(q * α - 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hκ.eventually_ge_atTop 1] with N h1
    exact mul_nonneg (by positivity) (Real.log_nonneg h1)
  · filter_upwards [hκ.eventually_ge_atTop 1, hlog.eventually_ge_atTop 1,
      eventually_ge_atTop 1] with N h1 hl hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hl0 : 0 < Real.log N := by linarith
    have hpow : 1 ≤ Real.log N ^ α := Real.one_le_rpow hl hα.le
    have hκN : (N : ℝ) / Real.log N ^ α ≤ N := div_le_self hN0.le hpow
    have hlk : Real.log ((N : ℝ) / Real.log N ^ α) ≤ Real.log N :=
      Real.log_le_log (by linarith) hκN
    have hsq : ((N : ℝ) / Real.log N ^ α / N) ^ q = Real.log N ^ (-(q * α)) := by
      rw [div_div_cancel_left' hN0.ne', Real.rpow_neg hl0.le, inv_pow,
        ← Real.rpow_natCast, ← Real.rpow_mul hl0.le, mul_comm α]
    rw [hsq, show -(q * α - 1) = -(q * α) + 1 by ring, Real.rpow_add hl0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hlk (Real.rpow_nonneg hl0.le _)

end Growth

/-! ### The overlap law at every root -/

section EveryRoot

variable {φ : ℝ → ℝ}

/-- **The overlap law at every root**: for every smooth profile `φ` supported in `[−1, 1]` with
`∫ φ = 1`, every order `q` and every dilation sequence `κ` with `(κ_N/N)^q log κ_N → 0`, RH
holds iff for all large `N` Weil's form is nonnegative on every atomic test
`Σ_{n ≤ N} x_n φ_κ(· − log n)` of width `1/κ_N`. -/
theorem riemannHypothesis_iff_atomicFamilies_nonneg_of_growthPow {κ : ℕ → ℝ} {q : ℕ}
    (hκ : OverlapGrowthPow q κ) (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate (κ N) φ)) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (natCast_le_infty 2)
  constructor
  · intro hRH
    filter_upwards [hκ.1.eventually_gt_atTop 0] with N hk x
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ2 hφ1 hk N x
    exact RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH _ h2 hc
  · intro H
    by_contra hRH
    rw [RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive] at hRH
    push Not at hRH
    obtain ⟨g, hg, hgc, hneg⟩ := hRH
    change weilQuad g < 0 at hneg
    -- a smooth negative test
    obtain ⟨G, hG, hGc, hGneg⟩ := exists_smooth_weilQuad_neg hφ hφ1 hφint hg hgc hneg
    obtain ⟨R0, hR0⟩ := hGc.isCompact.isBounded.subset_closedBall 0
    set R := max R0 0
    have hR : 0 ≤ R := le_max_right _ _
    have hGR : SupportedIn R G := fun u hu => by
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hR0 hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith [le_max_left R0 0]
    -- bounds on every derivative
    have hbd : ∀ l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv l G t| ≤ C := fun l => by
      obtain ⟨C, hC⟩ := (hasCompactSupport_iteratedDeriv hGc l).exists_bound_of_continuous
        (hG.continuous_iteratedDeriv l (natCast_le_infty l))
      exact ⟨max C 0, le_max_right _ _, fun t =>
        (by simpa [Real.norm_eq_abs] using hC t : |iteratedDeriv l G t| ≤ C).trans
          (le_max_left _ _)⟩
    choose M hM0 hM using hbd
    -- the order of the synthesis
    have hκ' : OverlapGrowthPow (2 * (2 * q + 2)) κ := hκ.mono (by omega)
    set B := blockSize R
    have hB : 1 ≤ B := by
      have h := Nat.le_ceil (1 + Real.exp (2 * R))
      have : (1 : ℝ) ≤ B := by
        have := Real.exp_pos (2 * R)
        simp only [B, blockSize] at h ⊢
        linarith
      exact_mod_cast this
    have hA : ∀ j, 0 ≤ ∫ s, |iteratedDeriv j φ s| := fun j => integral_nonneg fun s => abs_nonneg _
    obtain ⟨he, hV, -, -⟩ := tendsto_em hκ' hB (M := M)
      (A := fun j => ∫ s, |iteratedDeriv j φ s|) (R' := R + 1)
    have hErr := tendsto_weilErr G (R + 1) he hV
    have h1 := hErr.eventually (gt_mem_nhds (show (0 : ℝ) < -weilQuad G by linarith))
    have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
    have h2 := hNB.eventually H
    have h3 := hNB.eventually (hκ.1.eventually_ge_atTop 1)
    obtain ⟨n, hn1, hn2, hk, hn3⟩ := (h1.and (h2.and (h3.and (eventually_ge_atTop 2)))).exists
    obtain ⟨x, hx⟩ := exists_atomicTest_weilQuad_le_em hφ hφ1 hφint hG hGc hR hGR hM hM0 hn3 hk q
    have := hn2 x
    linarith

/-- **The logarithmic overlap law at every root**: for every `α > 0` and every smooth profile, RH
holds iff for all large `N` Weil's form is nonnegative on the atomic families of width
`(log N)^α/N`, overlap ratio `(log N)^α`. -/
theorem riemannHypothesis_iff_atomicFamilies_nonneg_log_pos {α : ℝ} (hα : 0 < α)
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / Real.log N ^ α) φ)) := by
  set q := ⌈1 / α⌉₊ + 1
  have hq : 1 < q * α := by
    have h := Nat.le_ceil (1 / α)
    have : (q : ℝ) = ⌈1 / α⌉₊ + 1 := by simp [q]
    rw [this]
    have h1 : 1 / α * α = 1 := by field_simp
    nlinarith
  exact riemannHypothesis_iff_atomicFamilies_nonneg_of_growthPow (overlapGrowthPow_log hα hq)
    hφ hφ1 hφint

end EveryRoot

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
