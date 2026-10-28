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
open scoped Real ContDiff

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
    hg.locallyIntegrable (contDiff_dilate_smooth hφ m)

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
    exact hψc.hasDerivAt_convolution_right _ hg.locallyIntegrable hψ1 x
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

/-- The mollification error `L ‖φ‖₁/m`, its Lipschitz constant `M m ‖φ′‖₁ + L`, and the resulting
motion of Weil's form. -/
theorem weilQuad_mollify_le (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {R M L : ℝ} (hR : 0 ≤ R)
    (hgR : SupportedIn R g) (hgM : ∀ t, |g t| ≤ M) (hgL : ∀ u v, |g u - g v| ≤ L * |u - v|)
    {m : ℝ} (hm : 1 ≤ m) :
    weilQuad (mollify g φ m) ≤ weilQuad g + weilErr g (R + 1) (L * (1 / m) * ∫ s, |φ s|)
      (synthLevy (R + 1) (L * (1 / m) * ∫ s, |φ s|)
        (M * (m * ∫ s, |deriv φ s|) + L) m) := by
  have hm0 : 0 < m := by linarith
  set D : ℝ → ℝ := fun x => mollify g φ m x - g x
  have hD2 : ContDiff ℝ 2 D :=
    ((contDiff_mollify hφ hφ1 hg.continuous hm0).of_le (natCast_le_infty 2)).sub hg
  have hgR1 : SupportedIn (R + 1) g := fun u hu => hgR u (by linarith)
  have hDR : SupportedIn (R + 1) D := fun u hu => by
    simp only [D, mollify_supportedIn hφ1 hgR hm u hu, hgR1 u hu, sub_zero]
  have hsup : ∀ x, |D x| ≤ L * (1 / m) * ∫ s, |φ s| := fun x => by
    have := abs_integral_mul_sub_le hg.continuous (contDiff_dilate_smooth hφ m).continuous
      (hasCompactSupport_dilate_of hφ1 hm0) (by rw [integral_dilate hm0, hφint])
      (fun s hs => dilate_vanishes hφ1 hm0 hs) hgL x
    rwa [integral_abs_dilate hm0] at this
  have hlip : ∀ u v, |D u - D v| ≤ (M * (m * ∫ s, |deriv φ s|) + L) * |u - v| := fun u v => by
    have e : D u - D v = (mollify g φ m u - mollify g φ m v) - (g u - g v) := by
      simp only [D]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have := add_le_add (abs_mollify_sub_le hφ hφ1 hg.continuous hgM hm0 u v) (hgL u v)
    linarith
  have h := weilQuad_add_le_of_lip hg hgc hgR1 hD2 hDR (by linarith) hsup hlip hm
  have he : (fun u => g u + D u) = mollify g φ m := by funext u; simp only [D]; ring
  rwa [he] at h

/-- **Smooth negative tests**: if Weil's form is negative on a `C²` test with compact support, it is
negative on a smooth test with compact support. -/
theorem exists_smooth_weilQuad_neg (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hneg : weilQuad g < 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ weilQuad G < 0 := by
  obtain ⟨R0, hR0⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  set R := max R0 0
  have hR : 0 ≤ R := le_max_right _ _
  have hgR : SupportedIn R g := fun u hu => by
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have := hR0 hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_max_left R0 0]
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hM' : ∀ t, |g t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hL : ∀ u v, |g u - g v| ≤ C * |u - v| := fun u v => by
    simpa [Real.dist_eq] using hC.dist_le_mul u v
  set A0 := ∫ s, |φ s|
  set A1 := ∫ s, |deriv φ s|
  set L : ℝ := C
  -- the error and the Lévy bound vanish as `m → ∞`
  have hm : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using hm.inv_tendsto_atTop
  have he : Tendsto (fun n : ℕ => L * (1 / (n : ℝ)) * A0) atTop (𝓝 0) := by
    simpa using (hinv.const_mul L).mul_const A0
  have hlog : Tendsto (fun n : ℕ => Real.log n * (1 / (n : ℝ)) ^ 2) atTop (𝓝 0) := by
    refine ((tendsto_log_mul_rpow_neg two_pos).comp hm).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp]
    rw [Real.rpow_neg hn0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hV : Tendsto (fun n : ℕ => synthLevy (R + 1) (L * (1 / (n : ℝ)) * A0)
      (M * ((n : ℝ) * A1) + L) n) atTop (𝓝 0) := by
    have h1 := ((tendsto_const_nhds (x := M * A1)).add (hinv.const_mul L)).mul he
    have h2 := (hlog.const_mul (2 * (L * A0) ^ 2 * (2 * (R + 1))))
    have h3 := ((he.pow 2).const_mul (levyLipConstant * (2 * (R + 1))))
    have := ((h1.const_mul (Real.exp (1 / 2) * (2 * (R + 1)))).add h2).add h3
    simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    unfold synthLevy
    field_simp
    ring
  have hErr := tendsto_weilErr g (R + 1) he hV
  obtain ⟨n, hn1, hn2⟩ := ((hErr.eventually (gt_mem_nhds
    (show (0 : ℝ) < -weilQuad g by linarith))).and (eventually_ge_atTop 1)).exists
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn2
  refine ⟨mollify g φ n, contDiff_mollify hφ hφ1 hg.continuous (by linarith),
    hasCompactSupport_of_vanishes (mollify_supportedIn hφ1 hgR hn), ?_⟩
  have := weilQuad_mollify_le hφ hφ1 hφint hg hgc hR hgR hM' hL hn
  linarith

end Mollify

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
