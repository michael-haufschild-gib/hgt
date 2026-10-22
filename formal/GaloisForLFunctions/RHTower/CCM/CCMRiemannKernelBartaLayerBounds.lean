import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilCrossFormBound
import GaloisForLFunctions.RHTower.CCM.CCMRiemannKernelBartaSources

/-!
# The edge layer of a truncated Riemann kernel against smooth sources

Fix `b` large and `w = e^{-2b}`. The layer `T = Φ(χ_{b+2,1} - χ_{b-w,w})` is a smooth interior
source at aperture `b + 3`, supported in `b - 2w < |t| < b + 2`, with `0 ≤ T ≤ Φ`. With
`Φ₀ = Φ(b - 2w)`, every quantity in `norm_ccmRestrictedWeilForm_smooth_le` is at most `Φ₀` times a
factor of polynomial size in `b`:

* `T ≤ Φ₀`;
* the pole lag integral is `O(e^{-b}) Φ₀`, since `∫_{|t| ≥ s} Φ ≤ 2Φ(s)/(πe^{2s})`;
* the prime lag sum is `O(1) Φ₀`, because the logarithms of integers are sparse at the decay scale
  `1/(πe^{2s})` of `Φ` (`sum_rpow_tail_le`);
* `|T'| ≤ Φ₀ e^{O(b)}`.

Hence `|Q_{b+3}(v, T)| ≤ C (1 + b) Φ₀ ‖v‖₁` for every smooth interior source `v`.
-/

open Real Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-! ## A sparse tail sum -/

/-- **Sparse tail sum.** For `K > 1` and `k₀ > 0`,
`Σ_{k ∈ s, k ≥ k₀} (k₀/k)^K ≤ 1 + k₀/(K - 1)`. -/
theorem sum_rpow_tail_le {K k₀ : ℝ} (hK : 1 < K) (hk₀ : 0 < k₀) (s : Finset ℕ) :
    ∑ k ∈ s, (if k₀ ≤ (k : ℝ) then k₀ ^ K * (k : ℝ) ^ (-K) else 0) ≤ 1 + k₀ / (K - 1) := by
  set g : ℕ → ℝ := fun k => if k₀ ≤ (k : ℝ) then k₀ ^ K * (k : ℝ) ^ (-K) else 0 with hg
  have hk₀K : 0 < k₀ ^ K := Real.rpow_pos_of_pos hk₀ K
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    simp only [hg]
    split_ifs with h
    · exact mul_nonneg hk₀K.le (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    · exact le_rfl
  set f : ℝ → ℝ := fun t => k₀ ^ K * t ^ (-K) with hf
  set m : ℕ := ⌈k₀⌉₊ with hm
  have hmk : k₀ ≤ (m : ℝ) := Nat.le_ceil k₀
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hk₀ hmk
  have hlt : ∀ k : ℕ, k < m → g k = 0 := by
    intro k hk
    have : (k : ℝ) < k₀ := Nat.lt_ceil.mp hk
    simp only [hg, if_neg (not_le.mpr this)]
  have hgm : g m ≤ 1 := by
    simp only [hg, if_pos hmk]
    have h1 : k₀ ^ K * (m : ℝ) ^ (-K) = (k₀ / m) ^ K := by
      rw [Real.div_rpow hk₀.le hm0.le, Real.rpow_neg hm0.le, div_eq_mul_inv]
    rw [h1]
    exact Real.rpow_le_one (div_nonneg hk₀.le hm0.le) ((div_le_one hm0).mpr hmk) (by linarith)
  set M : ℕ := max (s.sup id) m with hM
  have hsub : s ⊆ Finset.range (M + 1) := by
    intro k hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.le_sup (f := id) hk).trans (le_max_left _ _))
  have hmM : m ≤ M := le_max_right _ _
  -- the integral comparison on `[m, M]`
  have hanti : AntitoneOn f (Icc (m : ℝ) M) := by
    intro x hx y hy hxy
    simp only [hf]
    have hx0 : 0 < x := lt_of_lt_of_le hm0 hx.1
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith))
      hk₀K.le
  have hsumint := AntitoneOn.sum_le_integral_Ico (f := f) hmM hanti
  have hfInt : IntegrableOn f (Ioi k₀) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -K < -1) hk₀).const_mul _
  have hint : ∫ x in (m : ℝ)..(M : ℝ), f x ≤ k₀ / (K - 1) := by
    rw [intervalIntegral.integral_of_le (by exact_mod_cast hmM)]
    calc ∫ x in Ioc (m : ℝ) M, f x ≤ ∫ x in Ioi k₀, f x := by
          refine setIntegral_mono_set hfInt ?_ ?_
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            simp only [hf]
            exact mul_nonneg hk₀K.le (Real.rpow_nonneg (le_of_lt (lt_trans hk₀ hx)) _)
          · exact Eventually.of_forall fun x hx => lt_of_le_of_lt hmk hx.1
      _ = k₀ / (K - 1) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -K < -1) hk₀]
          have hK1 : (-K + 1) ≠ 0 := by linarith
          rw [show -K + 1 = -(K - 1) by ring, Real.rpow_neg hk₀.le]
          have : k₀ ^ (K - 1) = k₀ ^ K / k₀ := by
            rw [Real.rpow_sub hk₀, Real.rpow_one]
          rw [this]
          field_simp
  -- assemble
  have hsplit : ∑ k ∈ Finset.range (M + 1), g k =
      ∑ k ∈ Finset.range (m + 1), g k + ∑ k ∈ Finset.Ico (m + 1) (M + 1), g k := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)]
  have hfirst : ∑ k ∈ Finset.range (m + 1), g k = g m := by
    rw [Finset.sum_eq_single m]
    · intro k hk hkm
      exact hlt k (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkm)
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h
  have hsecond : ∑ k ∈ Finset.Ico (m + 1) (M + 1), g k = ∑ i ∈ Finset.Ico m M, f ((i + 1 : ℕ) : ℝ) := by
    rw [← Finset.sum_Ico_add' (f := g) (c := 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : m ≤ i := (Finset.mem_Ico.mp hi).1
    have hle : k₀ ≤ ((i + 1 : ℕ) : ℝ) := by
      have : (m : ℝ) ≤ i := by exact_mod_cast him
      push_cast; linarith
    simp only [hg, hf, if_pos hle]
  calc ∑ k ∈ s, g k ≤ ∑ k ∈ Finset.range (M + 1), g k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hg0 k
    _ = g m + ∑ i ∈ Finset.Ico m M, f ((i + 1 : ℕ) : ℝ) := by rw [hsplit, hfirst, hsecond]
    _ ≤ 1 + k₀ / (K - 1) := add_le_add hgm (hsumint.trans hint)

/-! ## Facts about `Φ` on the tail -/

/-- `Φ(s) ≥ e^{-πe^{2s}}` for `s ≥ 0` (the first cusp term). -/
theorem exp_neg_pi_exp_le_riemannKernelReal {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-π * Real.exp (2 * s)) ≤ riemannKernelReal s := by
  rw [riemannKernelReal_of_nonneg hs]
  have hfirst : cuspTerm riemannCuspPoly (0 + 1) s ≤ cuspSeries riemannCuspPoly s := by
    unfold cuspSeries
    exact (summable_cuspTerm riemannCuspPoly s).le_tsum 0
      (fun j _ => (cuspTerm_riemannCuspPoly_pos (by omega) hs).le)
  refine le_trans ?_ hfirst
  unfold cuspTerm
  rw [riemannCuspPoly_eval]
  push_cast
  simp only [one_pow, one_mul]
  set Y := Real.exp (2 * s) with hY
  have hY1 : 1 ≤ Y := Real.one_le_exp (by linarith)
  have hR : 1 ≤ 4 * π ^ 2 * Y ^ 2 - 6 * π * Y := by
    have hπ := Real.pi_gt_three
    have h1 : 6 ≤ 4 * π * Y - 6 := by nlinarith
    have h2 : 3 ≤ π * Y := by nlinarith
    have h3 : 6 * 3 ≤ (4 * π * Y - 6) * (π * Y) := mul_le_mul h1 h2 (by norm_num) (by linarith)
    nlinarith
  have hE : 1 ≤ Real.exp (s / 2) := Real.one_le_exp (by linarith)
  have hP := Real.exp_pos (-π * Y)
  calc Real.exp (-π * Y) = 1 * 1 * Real.exp (-π * Y) := by ring
    _ ≤ Real.exp (s / 2) * (4 * π ^ 2 * Y ^ 2 - 6 * π * Y) * Real.exp (-π * Y) := by
        gcongr

/-- The cusp derivative of `R` has degree at most `3`. -/
theorem natDegree_cuspDeriv_riemannCuspPoly_le : (cuspDeriv riemannCuspPoly).natDegree ≤ 3 :=
  (natDegree_cuspDeriv_le _).trans (by linarith [natDegree_riemannCuspPoly_le])

/-- `|Φ'(t)| ≤ C e^{13t/2} e^{-πe^{2t}}` for `t ≥ 0`, in cusp-series form. -/
theorem abs_cuspSeries_cuspDeriv_riemannCuspPoly_le {t : ℝ} (ht : 0 ≤ t) :
    |cuspSeries (cuspDeriv riemannCuspPoly) t| ≤
      cuspDecayConst (cuspDeriv riemannCuspPoly) * Real.exp (13 / 2 * t) *
        Real.exp (-π * Real.exp (2 * t)) := by
  have h := abs_cuspSeries_le (cuspDeriv riemannCuspPoly) ht
  have hdeg : (2 * ((cuspDeriv riemannCuspPoly).natDegree : ℝ) * t) ≤ 6 * t := by
    have : ((cuspDeriv riemannCuspPoly).natDegree : ℝ) ≤ 3 := by
      exact_mod_cast natDegree_cuspDeriv_riemannCuspPoly_le
    nlinarith
  have hC := cuspDecayConst_nonneg (cuspDeriv riemannCuspPoly)
  refine h.trans ?_
  calc cuspDecayConst (cuspDeriv riemannCuspPoly) * Real.exp (t / 2) *
        Real.exp (2 * ((cuspDeriv riemannCuspPoly).natDegree : ℝ) * t) *
        Real.exp (-π * Real.exp (2 * t))
      ≤ cuspDecayConst (cuspDeriv riemannCuspPoly) * Real.exp (t / 2) * Real.exp (6 * t) *
        Real.exp (-π * Real.exp (2 * t)) := by
        gcongr
    _ = _ := by
        rw [mul_assoc (cuspDecayConst _), ← Real.exp_add]
        ring_nf

/-- The derivative of `Φ` away from the origin. -/
theorem hasDerivAt_riemannKernelReal_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt riemannKernelReal (cuspSeries (cuspDeriv riemannCuspPoly) x) x := by
  have heq : riemannKernelReal =ᶠ[𝓝 x] cuspSeries riemannCuspPoly := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact riemannKernelReal_of_nonneg (le_of_lt ht)
  exact (hasDerivAt_cuspSeries riemannCuspPoly x).congr_of_eventuallyEq heq

theorem hasDerivAt_riemannKernelReal_of_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt riemannKernelReal (-cuspSeries (cuspDeriv riemannCuspPoly) (-x)) x := by
  have heq : riemannKernelReal =ᶠ[𝓝 x] fun t => cuspSeries riemannCuspPoly (-t) := by
    filter_upwards [Iio_mem_nhds hx] with t ht
    rw [riemannKernelReal, abs_of_neg ht]
  have h := (hasDerivAt_cuspSeries riemannCuspPoly (-x)).comp x (hasDerivAt_neg x)
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  ring

theorem abs_deriv_riemannKernelReal_le {x : ℝ} (hx : x ≠ 0) :
    ∃ d : ℝ, HasDerivAt riemannKernelReal d x ∧
      |d| ≤ cuspDecayConst (cuspDeriv riemannCuspPoly) * Real.exp (13 / 2 * |x|) *
        Real.exp (-π * Real.exp (2 * |x|)) := by
  rcases lt_or_gt_of_ne hx with h | h
  · refine ⟨_, hasDerivAt_riemannKernelReal_of_neg h, ?_⟩
    rw [abs_neg, abs_of_neg h]
    exact abs_cuspSeries_cuspDeriv_riemannCuspPoly_le (by linarith)
  · refine ⟨_, hasDerivAt_riemannKernelReal_of_pos h, ?_⟩
    rw [abs_of_pos h]
    exact abs_cuspSeries_cuspDeriv_riemannCuspPoly_le h.le

/-- `∫_{t > s} Φ ≤ Φ(s)/(πe^{2s})` for `s ≥ ½ log 2`. -/
theorem setIntegral_Ioi_riemannKernelReal_le {s : ℝ} (hs : Real.log 2 / 2 ≤ s) :
    IntegrableOn riemannKernelReal (Ioi s) ∧
      ∫ t in Ioi s, riemannKernelReal t ≤ riemannKernelReal s / (π * Real.exp (2 * s)) := by
  set K : ℝ := π * Real.exp (2 * s) with hK
  have hKpos : 0 < K := by positivity
  have hexpInt : IntegrableOn (fun t => Real.exp (-K * t)) (Ioi s) :=
    integrableOn_exp_mul_Ioi (by linarith) s
  have hbound : ∀ t ∈ Ioi s, riemannKernelReal t ≤
      riemannKernelReal s * Real.exp (K * s) * Real.exp (-K * t) := by
    intro t ht
    have h := riemannKernelReal_le_mul_exp hs (le_of_lt ht)
    refine h.trans (le_of_eq ?_)
    rw [mul_assoc (riemannKernelReal s), ← Real.exp_add]
    congr 2
    rw [hK]
    ring
  have hint : IntegrableOn riemannKernelReal (Ioi s) := by
    refine (hexpInt.const_mul (riemannKernelReal s * Real.exp (K * s))).mono'
      continuous_riemannKernelReal.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (riemannKernelReal_pos t)]
    exact hbound t ht
  refine ⟨hint, ?_⟩
  calc ∫ t in Ioi s, riemannKernelReal t
      ≤ ∫ t in Ioi s, riemannKernelReal s * Real.exp (K * s) * Real.exp (-K * t) :=
        setIntegral_mono_on hint (hexpInt.const_mul _) measurableSet_Ioi hbound
    _ = riemannKernelReal s * Real.exp (K * s) * (Real.exp (-K * s) / K) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) s]
        field_simp
    _ = riemannKernelReal s / K := by
        rw [show Real.exp (-K * s) = (Real.exp (K * s))⁻¹ by rw [neg_mul, Real.exp_neg]]
        have := Real.exp_pos (K * s)
        field_simp

/-! ## The layer at scale `b` -/

/-- The transition width `w = e^{-2b}`. -/
def bartaWidth (b : ℝ) : ℝ := Real.exp (-2 * b)

theorem bartaWidth_pos (b : ℝ) : 0 < bartaWidth b := Real.exp_pos _

theorem seven_lt_exp_two : (7 : ℝ) < Real.exp 2 := by
  have he := Real.exp_one_gt_d9
  calc (7 : ℝ) < 2.7182818283 ^ 2 := by norm_num
    _ ≤ Real.exp 1 ^ 2 := by gcongr
    _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num

theorem bartaWidth_le {b : ℝ} (hb : 1 ≤ b) : bartaWidth b ≤ 1 / 7 := by
  unfold bartaWidth
  have h1 : Real.exp (-2 * b) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
  have h3 := seven_lt_exp_two
  have h4 := Real.exp_pos (-2 : ℝ)
  nlinarith

/-- The inner radius `s = b - 2w`, beyond which the layer lives. -/
def bartaInner (b : ℝ) : ℝ := b - 2 * bartaWidth b

/-- The edge value `Φ₀ = Φ(b - 2w)`. -/
def bartaEdge (b : ℝ) : ℝ := riemannKernelReal (bartaInner b)

/-- The decay rate `K = πe^{2s}` of `Φ` beyond the inner radius. -/
def bartaRate (b : ℝ) : ℝ := π * Real.exp (2 * bartaInner b)

theorem bartaInner_ge {b : ℝ} (hb : 1 ≤ b) : b - 2 / 7 ≤ bartaInner b := by
  unfold bartaInner; linarith [bartaWidth_le hb]

theorem log_two_half_le_bartaInner {b : ℝ} (hb : 1 ≤ b) : Real.log 2 / 2 ≤ bartaInner b := by
  have := bartaInner_ge hb
  have hl := Real.log_two_lt_d9
  linarith

theorem bartaInner_pos {b : ℝ} (hb : 1 ≤ b) : 0 < bartaInner b := by
  have := bartaInner_ge hb; linarith

theorem bartaEdge_pos (b : ℝ) : 0 < bartaEdge b := riemannKernelReal_pos _

theorem exp_two_le_bartaRate {b : ℝ} (hb : 1 ≤ b) : Real.exp (2 * b) ≤ bartaRate b := by
  unfold bartaRate bartaInner
  have hw := bartaWidth_le hb
  have hsplit : Real.exp (2 * (b - 2 * bartaWidth b)) =
      Real.exp (2 * b) * Real.exp (-(4 * bartaWidth b)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have h1 : 1 - 4 * bartaWidth b ≤ Real.exp (-(4 * bartaWidth b)) := by
    linarith [Real.add_one_le_exp (-(4 * bartaWidth b))]
  have hE := Real.exp_pos (2 * b)
  have hπ := Real.pi_gt_three
  have h2 : 1 ≤ π * Real.exp (-(4 * bartaWidth b)) := by
    have h3 : 3 / 7 ≤ 1 - 4 * bartaWidth b := by linarith
    nlinarith
  calc Real.exp (2 * b) = Real.exp (2 * b) * 1 := (mul_one _).symm
    _ ≤ Real.exp (2 * b) * (π * Real.exp (-(4 * bartaWidth b))) :=
        mul_le_mul_of_nonneg_left h2 hE.le
    _ = π * (Real.exp (2 * b) * Real.exp (-(4 * bartaWidth b))) := by ring

theorem half_exp_two_le_bartaRate_sub_one {b : ℝ} (hb : 1 ≤ b) :
    Real.exp (2 * b) / 2 ≤ bartaRate b - 1 := by
  have h1 := exp_two_le_bartaRate hb
  have h2 : (2 : ℝ) ≤ Real.exp (2 * b) := by
    have := Real.add_one_le_exp (2 * b); linarith
  linarith

/-- The layer `L = Φ(χ_{b+2,1} - χ_{b-w,w})`. -/
def bartaLayerFn (b t : ℝ) : ℝ :=
  bartaProfile (b + 2) 1 t - bartaProfile (b - bartaWidth b) (bartaWidth b) t

theorem bartaLayerFn_bounds (b t : ℝ) :
    0 ≤ bartaLayerFn b t ∧ bartaLayerFn b t ≤ riemannKernelReal t := by
  have hw := bartaWidth_pos b
  exact bartaLayer_bounds hw one_pos (by linarith) t

theorem bartaLayerFn_eq_zero_of_abs_le {b t : ℝ} (ht : |t| ≤ bartaInner b) :
    bartaLayerFn b t = 0 := by
  have hw := bartaWidth_pos b
  unfold bartaInner at ht
  exact bartaLayer_eq_zero hw one_pos (by linarith) (by linarith)

theorem bartaLayerFn_eq_zero_of_le_abs {b t : ℝ} (ht : b + 2 ≤ |t|) : bartaLayerFn b t = 0 := by
  have hw := bartaWidth_pos b
  unfold bartaLayerFn
  rw [bartaProfile_eq_zero one_pos ht, bartaProfile_eq_zero hw (by linarith), sub_zero]

theorem riemannKernelReal_abs (t : ℝ) : riemannKernelReal |t| = riemannKernelReal t := by
  simp [riemannKernelReal, abs_abs]

theorem bartaLayerFn_le_edge {b : ℝ} (hb : 1 ≤ b) (t : ℝ) : bartaLayerFn b t ≤ bartaEdge b := by
  rcases le_or_gt |t| (bartaInner b) with ht | ht
  · rw [bartaLayerFn_eq_zero_of_abs_le ht]; exact (bartaEdge_pos b).le
  · calc bartaLayerFn b t ≤ riemannKernelReal t := (bartaLayerFn_bounds b t).2
      _ = riemannKernelReal |t| := (riemannKernelReal_abs t).symm
      _ ≤ bartaEdge b := riemannKernelReal_antitoneOn (log_two_half_le_bartaInner hb)
          (le_trans (log_two_half_le_bartaInner hb) ht.le) ht.le

theorem bartaLayerFn_le_decay {b : ℝ} (hb : 1 ≤ b) {t : ℝ} (ht : bartaInner b ≤ |t|) :
    bartaLayerFn b t ≤ bartaEdge b * Real.exp (-(bartaRate b * (|t| - bartaInner b))) := by
  calc bartaLayerFn b t ≤ riemannKernelReal t := (bartaLayerFn_bounds b t).2
    _ = riemannKernelReal |t| := (riemannKernelReal_abs t).symm
    _ ≤ _ := by
        have := riemannKernelReal_le_mul_exp (log_two_half_le_bartaInner hb) ht
        simpa [bartaEdge, bartaRate, mul_assoc] using this

theorem continuous_bartaLayerFn (b : ℝ) : Continuous (bartaLayerFn b) :=
  (contDiff_bartaProfile (n := 0) _ _).continuous.sub (contDiff_bartaProfile (n := 0) _ _).continuous

theorem bartaLayerFn_neg (b t : ℝ) : bartaLayerFn b (-t) = bartaLayerFn b t := by
  have hc : ∀ c w : ℝ, bartaCutoff c w (-t) = bartaCutoff c w t := by
    intro c w; unfold bartaCutoff; rw [mul_comm]; ring_nf
  unfold bartaLayerFn bartaProfile
  rw [hc, hc, ← riemannKernelReal_abs (-t), abs_neg, riemannKernelReal_abs]

theorem integrable_bartaLayerFn (b : ℝ) : Integrable (bartaLayerFn b) := by
  refine (continuous_bartaLayerFn b).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(b + 2)) (b := b + 2))
    fun t ht => ?_
  by_contra h
  apply ht
  apply bartaLayerFn_eq_zero_of_le_abs
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact le_trans (by linarith) (neg_le_abs t)
  · exact le_trans h.le (le_abs_self t)

/-- `∫ L ≤ 2Φ₀/K`. -/
theorem integral_bartaLayerFn_le {b : ℝ} (hb : 1 ≤ b) :
    ∫ t, bartaLayerFn b t ≤ 2 * (bartaEdge b / bartaRate b) := by
  have hs := log_two_half_le_bartaInner hb
  have hs0 := bartaInner_pos hb
  obtain ⟨hint, htail⟩ := setIntegral_Ioi_riemannKernelReal_le hs
  have heven : ∫ t, bartaLayerFn b t = ∫ t, bartaLayerFn b |t| := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    dsimp only
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, bartaLayerFn_neg]
  rw [heven, integral_comp_abs]
  have hind : IntegrableOn ((Ioi (bartaInner b)).indicator riemannKernelReal) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioi).mpr hint).integrableOn
  have hle : ∫ t in Ioi (0 : ℝ), bartaLayerFn b t ≤
      ∫ t in Ioi (0 : ℝ), (Ioi (bartaInner b)).indicator riemannKernelReal t := by
    refine setIntegral_mono_on (integrable_bartaLayerFn b).integrableOn hind measurableSet_Ioi
      fun t ht => ?_
    by_cases hts : t ∈ Ioi (bartaInner b)
    · rw [indicator_of_mem hts]; exact (bartaLayerFn_bounds b t).2
    · rw [indicator_of_notMem hts]
      have : |t| ≤ bartaInner b := by rw [abs_of_pos ht]; exact not_lt.mp hts
      rw [bartaLayerFn_eq_zero_of_abs_le this]
  have hsame : ∫ t in Ioi (0 : ℝ), (Ioi (bartaInner b)).indicator riemannKernelReal t =
      ∫ t in Ioi (bartaInner b), riemannKernelReal t := by
    have hset : Ioi (0 : ℝ) ∩ Ioi (bartaInner b) = Ioi (bartaInner b) :=
      Set.ext fun t => ⟨fun h => h.2, fun h => ⟨lt_trans hs0 h, h⟩⟩
    rw [setIntegral_indicator measurableSet_Ioi, hset]
  have := htail
  unfold bartaEdge bartaRate
  linarith

/-! ## Lag bounds for the layer -/

theorem cosh_half_le_exp {h R : ℝ} (h0 : 0 ≤ h) (hR : h ≤ 2 * R) :
    Real.cosh (h / 2) ≤ Real.exp R := by
  rw [Real.cosh_eq]
  have h1 : Real.exp (-(h / 2)) ≤ Real.exp (h / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (h / 2) ≤ Real.exp R := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- **Pole lag bound.** `∫_0^{2(b+3)} (L(y+h) + L(y-h)) 2cosh(h/2) dh ≤ 8e^{b+3} Φ₀/K`. -/
theorem bartaLayer_pole_lag_le {b : ℝ} (hb : 1 ≤ b) (y : ℝ) :
    ∫ h in Ioc (0 : ℝ) (2 * (b + 3)),
      (bartaLayerFn b (y + h) + bartaLayerFn b (y - h)) * (2 * Real.cosh (h / 2)) ≤
        8 * Real.exp (b + 3) * (bartaEdge b / bartaRate b) := by
  have hL := integrable_bartaLayerFn b
  have hshift1 : Integrable fun h => bartaLayerFn b (y + h) := hL.comp_add_left y
  have hshift2 : Integrable fun h => bartaLayerFn b (y - h) := hL.comp_sub_left y
  have hsum : Integrable fun h => bartaLayerFn b (y + h) + bartaLayerFn b (y - h) :=
    hshift1.add hshift2
  have hnn : ∀ h, 0 ≤ bartaLayerFn b (y + h) + bartaLayerFn b (y - h) := fun h =>
    add_nonneg (bartaLayerFn_bounds b _).1 (bartaLayerFn_bounds b _).1
  have hE := Real.exp_pos (b + 3)
  calc ∫ h in Ioc (0 : ℝ) (2 * (b + 3)),
        (bartaLayerFn b (y + h) + bartaLayerFn b (y - h)) * (2 * Real.cosh (h / 2))
      ≤ ∫ h in Ioc (0 : ℝ) (2 * (b + 3)),
        (bartaLayerFn b (y + h) + bartaLayerFn b (y - h)) * (2 * Real.exp (b + 3)) := by
        refine setIntegral_mono_on ?_ (hsum.mul_const _).integrableOn measurableSet_Ioc
          fun h hh => ?_
        · refine ((hsum.mul_const (2 * Real.exp (b + 3))).integrableOn).mono' ?_ ?_
          · exact ((continuous_bartaLayerFn b).comp (continuous_const.add continuous_id) |>.add
              ((continuous_bartaLayerFn b).comp (continuous_const.sub continuous_id)) |>.mul
              (by fun_prop : Continuous fun h : ℝ => 2 * Real.cosh (h / 2))).aestronglyMeasurable
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn h)
              (by have := Real.cosh_pos (h / 2); linarith))]
            exact mul_le_mul_of_nonneg_left (by linarith [cosh_half_le_exp hh.1.le hh.2]) (hnn h)
        · exact mul_le_mul_of_nonneg_left (by linarith [cosh_half_le_exp hh.1.le hh.2]) (hnn h)
    _ ≤ ∫ h, (bartaLayerFn b (y + h) + bartaLayerFn b (y - h)) * (2 * Real.exp (b + 3)) :=
        setIntegral_le_integral (hsum.mul_const _) (ae_of_all _ fun h =>
          mul_nonneg (hnn h) (by positivity))
    _ = 2 * Real.exp (b + 3) * (2 * ∫ t, bartaLayerFn b t) := by
        rw [integral_mul_const, integral_add hshift1 hshift2,
          integral_add_left_eq_self (fun t => bartaLayerFn b t) y,
          integral_sub_left_eq_self (fun t => bartaLayerFn b t) volume y]
        ring
    _ ≤ 2 * Real.exp (b + 3) * (2 * (2 * (bartaEdge b / bartaRate b))) := by
        gcongr
        exact integral_bartaLayerFn_le hb
    _ = 8 * Real.exp (b + 3) * (bartaEdge b / bartaRate b) := by ring

theorem criticalMellinAtomWeight_le_two (k : ℕ) : criticalMellinAtomWeight k ≤ 2 := by
  unfold criticalMellinAtomWeight
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log k ≤ (k : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div hk0.le (by norm_num)
  have hΛ : ArithmeticFunction.vonMangoldt k ≤ Real.log k := ArithmeticFunction.vonMangoldt_le_log
  have hprod : (k : ℝ) ^ (-1 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hk0]; norm_num
  have hpos : 0 ≤ (k : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hk0.le _
  calc (k : ℝ) ^ (-1 / 2 : ℝ) * ArithmeticFunction.vonMangoldt k
      ≤ (k : ℝ) ^ (-1 / 2 : ℝ) * ((k : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) :=
        mul_le_mul_of_nonneg_left (hΛ.trans hlog) hpos
    _ = 2 * ((k : ℝ) ^ (-1 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ)) := by ring
    _ = 2 := by rw [hprod, mul_one]

theorem exp_four_lt : Real.exp 4 < 55 := by
  have he := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    _ < 2.7182818286 ^ 4 := by gcongr
    _ < 55 := by norm_num

/-- The tail summand `(k₀/k)^K` of `sum_rpow_tail_le`. -/
def bartaTail (K k₀ : ℝ) (k : ℕ) : ℝ := if k₀ ≤ (k : ℝ) then k₀ ^ K * (k : ℝ) ^ (-K) else 0

theorem bartaTail_nonneg (K : ℝ) {k₀ : ℝ} (hk₀ : 0 < k₀) (k : ℕ) : 0 ≤ bartaTail K k₀ k := by
  unfold bartaTail
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg hk₀.le _) (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  · exact le_rfl

theorem exp_mul_rpow_neg {K c : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    Real.exp c ^ K * (k : ℝ) ^ (-K) = Real.exp (-(K * (Real.log k - c))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.exp_mul, Real.rpow_def_of_pos hk0, ← Real.exp_add]
  congr 1; ring

/-- The layer at `y + log k` is bounded by a tail term plus a term living on `k ≤ 54`. -/
theorem bartaLayerFn_add_log_le {b : ℝ} (hb : 1 ≤ b) {y : ℝ} (hy : |y| ≤ b + 3) {k : ℕ}
    (hk : 1 ≤ k) :
    bartaLayerFn b (y + Real.log k) ≤ bartaEdge b *
      (bartaTail (bartaRate b) (Real.exp (bartaInner b - y)) k + if k ≤ 54 then 1 else 0) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hE := bartaEdge_pos b
  have hsmall0 : (0 : ℝ) ≤ if k ≤ 54 then 1 else 0 := by split_ifs <;> norm_num
  have htail0 := bartaTail_nonneg (bartaRate b) (Real.exp_pos (bartaInner b - y)) k
  set z := y + Real.log k with hz
  rcases le_or_gt |z| (bartaInner b) with hzs | hzs
  · rw [bartaLayerFn_eq_zero_of_abs_le hzs]; positivity
  rcases le_or_gt 0 z with hz0 | hz0
  · -- positive side: a tail term
    rw [abs_of_nonneg hz0] at hzs
    have hdec := bartaLayerFn_le_decay hb (show bartaInner b ≤ |z| by rw [abs_of_nonneg hz0]; exact hzs.le)
    rw [abs_of_nonneg hz0] at hdec
    have hk₀ : Real.exp (bartaInner b - y) ≤ (k : ℝ) := by
      rw [← Real.exp_log hk0]; exact Real.exp_le_exp.mpr (by linarith)
    have htail : bartaTail (bartaRate b) (Real.exp (bartaInner b - y)) k =
        Real.exp (-(bartaRate b * (z - bartaInner b))) := by
      unfold bartaTail
      rw [if_pos hk₀, exp_mul_rpow_neg hk]
      congr 1; rw [hz]; ring
    rw [htail]
    nlinarith
  · -- negative side: `k ≤ 54`
    rw [abs_of_neg hz0] at hzs
    have hs := bartaInner_ge hb
    have hlogk : Real.log k < 4 := by
      have := neg_abs_le y
      linarith
    have hk54 : k ≤ 54 := by
      have : (k : ℝ) < 55 := by
        calc (k : ℝ) = Real.exp (Real.log k) := (Real.exp_log hk0).symm
          _ < Real.exp 4 := Real.exp_lt_exp.mpr hlogk
          _ < 55 := exp_four_lt
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    rw [if_pos hk54]
    have := bartaLayerFn_le_edge hb z
    nlinarith

/-- The layer at `y - log k` is bounded by a tail term plus a term living on `k ≤ 54`. -/
theorem bartaLayerFn_sub_log_le {b : ℝ} (hb : 1 ≤ b) {y : ℝ} (hy : |y| ≤ b + 3) {k : ℕ}
    (hk : 1 ≤ k) :
    bartaLayerFn b (y - Real.log k) ≤ bartaEdge b *
      (bartaTail (bartaRate b) (Real.exp (bartaInner b + y)) k + if k ≤ 54 then 1 else 0) := by
  have h := bartaLayerFn_add_log_le hb (y := -y) (by rwa [abs_neg]) hk
  rw [show -y + Real.log k = -(y - Real.log k) by ring, bartaLayerFn_neg,
    show bartaInner b - -y = bartaInner b + y by ring] at h
  exact h

/-- **Prime lag bound.** For `|y| ≤ b + 3`, the prime lag sum of the layer is at most
`2Φ₀ (2(1 + 2e³) + 110)`. -/
theorem bartaLayer_prime_lag_le {b : ℝ} (hb : 1 ≤ b) {y : ℝ} (hy : |y| ≤ b + 3) (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, criticalMellinAtomWeight k *
      (bartaLayerFn b (y + Real.log k) + bartaLayerFn b (y - Real.log k)) ≤
        2 * bartaEdge b * (2 * (1 + 2 * Real.exp 3) + 110) := by
  set K := bartaRate b with hK
  set k₁ := Real.exp (bartaInner b - y) with hk₁
  set k₂ := Real.exp (bartaInner b + y) with hk₂
  have hE := bartaEdge_pos b
  have hK1 : 1 < K := by
    have h1 := exp_two_le_bartaRate hb
    have h2 : (2 : ℝ) ≤ Real.exp (2 * b) := by have := Real.add_one_le_exp (2 * b); linarith
    linarith
  have hKsub := half_exp_two_le_bartaRate_sub_one hb
  have hs : bartaInner b ≤ b := by unfold bartaInner; linarith [bartaWidth_pos b]
  have hk₁le : k₁ ≤ Real.exp (2 * b + 3) := Real.exp_le_exp.mpr (by linarith [neg_abs_le y])
  have hk₂le : k₂ ≤ Real.exp (2 * b + 3) := Real.exp_le_exp.mpr (by linarith [le_abs_self y])
  have hratio : ∀ k₀ : ℝ, 0 < k₀ → k₀ ≤ Real.exp (2 * b + 3) → k₀ / (K - 1) ≤ 2 * Real.exp 3 := by
    intro k₀ hk₀ hle
    rw [div_le_iff₀ (by linarith)]
    have h3 : Real.exp (2 * b + 3) = Real.exp 3 * Real.exp (2 * b) := by
      rw [← Real.exp_add]; ring_nf
    have := Real.exp_pos 3
    nlinarith
  have hsum1 := sum_rpow_tail_le hK1 (Real.exp_pos _) (Finset.Icc 2 N) (k₀ := k₁)
  have hsum2 := sum_rpow_tail_le hK1 (Real.exp_pos _) (Finset.Icc 2 N) (k₀ := k₂)
  have hsmall : ∑ k ∈ Finset.Icc 2 N, (if k ≤ 54 then (1 : ℝ) else 0) ≤ 55 := by
    rw [Finset.sum_boole]
    have : (Finset.filter (fun k => k ≤ 54) (Finset.Icc 2 N)).card ≤ 55 := by
      calc (Finset.filter (fun k => k ≤ 54) (Finset.Icc 2 N)).card
          ≤ (Finset.range 55).card := Finset.card_le_card fun k hk => by
            simp only [Finset.mem_filter] at hk
            exact Finset.mem_range.mpr (by omega)
        _ = 55 := Finset.card_range 55
    exact_mod_cast this
  have hterm : ∀ k ∈ Finset.Icc 2 N, criticalMellinAtomWeight k *
      (bartaLayerFn b (y + Real.log k) + bartaLayerFn b (y - Real.log k)) ≤
        2 * bartaEdge b * (bartaTail K k₁ k + bartaTail K k₂ k + 2 * (if k ≤ 54 then 1 else 0)) := by
    intro k hk
    have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
    have h1 := bartaLayerFn_add_log_le hb hy hk1
    have h2 := bartaLayerFn_sub_log_le hb hy hk1
    have hw := criticalMellinAtomWeight_le_two k
    have hw0 := criticalMellinAtomWeight_nonneg k
    have hL0 : 0 ≤ bartaLayerFn b (y + Real.log k) + bartaLayerFn b (y - Real.log k) :=
      add_nonneg (bartaLayerFn_bounds b _).1 (bartaLayerFn_bounds b _).1
    calc criticalMellinAtomWeight k *
          (bartaLayerFn b (y + Real.log k) + bartaLayerFn b (y - Real.log k))
        ≤ 2 * (bartaLayerFn b (y + Real.log k) + bartaLayerFn b (y - Real.log k)) :=
          mul_le_mul_of_nonneg_right hw hL0
      _ ≤ 2 * (bartaEdge b * (bartaTail K k₁ k + if k ≤ 54 then 1 else 0) +
          bartaEdge b * (bartaTail K k₂ k + if k ≤ 54 then 1 else 0)) := by
          gcongr
      _ = 2 * bartaEdge b * (bartaTail K k₁ k + bartaTail K k₂ k +
          2 * (if k ≤ 54 then 1 else 0)) := by ring
  calc ∑ k ∈ Finset.Icc 2 N, criticalMellinAtomWeight k *
        (bartaLayerFn b (y + Real.log k) + bartaLayerFn b (y - Real.log k))
      ≤ ∑ k ∈ Finset.Icc 2 N, 2 * bartaEdge b *
          (bartaTail K k₁ k + bartaTail K k₂ k + 2 * (if k ≤ 54 then 1 else 0)) :=
        Finset.sum_le_sum hterm
    _ = 2 * bartaEdge b * ((∑ k ∈ Finset.Icc 2 N, bartaTail K k₁ k) +
          (∑ k ∈ Finset.Icc 2 N, bartaTail K k₂ k) +
          2 * ∑ k ∈ Finset.Icc 2 N, (if k ≤ 54 then (1 : ℝ) else 0)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * bartaEdge b * ((1 + 2 * Real.exp 3) + (1 + 2 * Real.exp 3) + 2 * 55) := by
        gcongr
        · exact hsum1.trans (by linarith [hratio k₁ (Real.exp_pos _) hk₁le])
        · exact hsum2.trans (by linarith [hratio k₂ (Real.exp_pos _) hk₂le])
    _ = 2 * bartaEdge b * (2 * (1 + 2 * Real.exp 3) + 110) := by ring

/-! ## The derivative of the layer -/

theorem hasDerivAt_bartaCutoff (c w t : ℝ) :
    HasDerivAt (bartaCutoff c w)
      (deriv Real.smoothTransition ((c - t) / w) * (-1 / w) *
          Real.smoothTransition ((c + t) / w) +
        Real.smoothTransition ((c - t) / w) *
          (deriv Real.smoothTransition ((c + t) / w) * (1 / w))) t := by
  have hd : ∀ x : ℝ, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    fun x => ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => (c - t) / w) (-1 / w) t := by
    have := ((hasDerivAt_const t c).sub (hasDerivAt_id t)).div_const w
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => (c + t) / w) (1 / w) t := by
    have := ((hasDerivAt_const t c).add (hasDerivAt_id t)).div_const w
    simpa using this
  exact ((hd _).comp t h1).mul ((hd _).comp t h2)

theorem abs_deriv_bartaCutoff_le {c w Λ : ℝ} (hw : 0 < w)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (t : ℝ) :
    |deriv (bartaCutoff c w) t| ≤ 2 * Λ / w := by
  rw [(hasDerivAt_bartaCutoff c w t).deriv]
  have hΛ0 : 0 ≤ Λ := le_trans (abs_nonneg _) (hΛ 0)
  have e1 := hΛ ((c - t) / w); have e2 := hΛ ((c + t) / w)
  have s1 := Real.smoothTransition.nonneg ((c - t) / w)
  have s2 := Real.smoothTransition.nonneg ((c + t) / w)
  have t1 := Real.smoothTransition.le_one ((c - t) / w)
  have t2 := Real.smoothTransition.le_one ((c + t) / w)
  have hinv : 0 < 1 / w := by positivity
  calc |deriv Real.smoothTransition ((c - t) / w) * (-1 / w) * Real.smoothTransition ((c + t) / w) +
        Real.smoothTransition ((c - t) / w) * (deriv Real.smoothTransition ((c + t) / w) * (1 / w))|
      ≤ |deriv Real.smoothTransition ((c - t) / w)| * (1 / w) * 1 +
          1 * (|deriv Real.smoothTransition ((c + t) / w)| * (1 / w)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_mul, show |(-1 / w)| = 1 / w by rw [neg_div, abs_neg, abs_of_pos hinv],
            abs_of_nonneg s2]
          gcongr
        · rw [abs_mul, abs_mul, abs_of_nonneg s1, abs_of_pos hinv]
          gcongr
    _ ≤ Λ * (1 / w) * 1 + 1 * (Λ * (1 / w)) := by gcongr
    _ = 2 * Λ / w := by ring

theorem bartaLayerFn_eventually_zero_of_lt {b x : ℝ} (hx : |x| < bartaInner b) :
    bartaLayerFn b =ᶠ[𝓝 x] fun _ => 0 := by
  have hopen : IsOpen {t : ℝ | |t| < bartaInner b} :=
    isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds hx] with t ht
  exact bartaLayerFn_eq_zero_of_abs_le (le_of_lt ht)

theorem bartaLayerFn_eventually_zero_of_gt {b x : ℝ} (hx : b + 2 < |x|) :
    bartaLayerFn b =ᶠ[𝓝 x] fun _ => 0 := by
  have hopen : IsOpen {t : ℝ | b + 2 < |t|} :=
    isOpen_lt continuous_const continuous_abs
  filter_upwards [hopen.mem_nhds hx] with t ht
  exact bartaLayerFn_eq_zero_of_le_abs (le_of_lt ht)

/-- The constant `C_D` of the derivative bound for `Φ`. -/
def bartaDerivConst : ℝ := cuspDecayConst (cuspDeriv riemannCuspPoly)

/-- **Derivative bound.** `|L'(x)| ≤ Φ₀ (C_D e^{13(b+2)/2} + 2Λ + 2Λe^{2b})`. -/
theorem abs_deriv_bartaLayerFn_le {b Λ : ℝ} (hb : 1 ≤ b)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (x : ℝ) :
    |deriv (bartaLayerFn b) x| ≤ bartaEdge b *
      (bartaDerivConst * Real.exp (13 / 2 * (b + 2)) + 2 * Λ + 2 * Λ * Real.exp (2 * b)) := by
  have hE := bartaEdge_pos b
  have hΛ0 : 0 ≤ Λ := le_trans (abs_nonneg _) (hΛ 0)
  have hC0 : 0 ≤ bartaDerivConst := cuspDecayConst_nonneg _
  have hrhs : 0 ≤ bartaEdge b *
      (bartaDerivConst * Real.exp (13 / 2 * (b + 2)) + 2 * Λ + 2 * Λ * Real.exp (2 * b)) := by
    positivity
  rcases lt_or_ge |x| (bartaInner b) with hx | hx
  · rw [(bartaLayerFn_eventually_zero_of_lt hx).deriv_eq, deriv_const, abs_zero]; exact hrhs
  rcases lt_or_ge (b + 2) |x| with hx' | hx'
  · rw [(bartaLayerFn_eventually_zero_of_gt hx').deriv_eq, deriv_const, abs_zero]; exact hrhs
  -- the layer region `s ≤ |x| ≤ b + 2`
  have hs0 := bartaInner_pos hb
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx; linarith
  obtain ⟨d, hd, hdbound⟩ := abs_deriv_riemannKernelReal_le hx0
  set w := bartaWidth b with hw
  have hw0 := bartaWidth_pos b
  have hχ₂ := hasDerivAt_bartaCutoff (b + 2) 1 x
  have hχ₁ := hasDerivAt_bartaCutoff (b - w) w x
  have hL : HasDerivAt (bartaLayerFn b)
      (d * bartaCutoff (b + 2) 1 x + riemannKernelReal x * deriv (bartaCutoff (b + 2) 1) x -
        (d * bartaCutoff (b - w) w x + riemannKernelReal x * deriv (bartaCutoff (b - w) w) x)) x := by
    have h1 := hd.mul hχ₂.differentiableAt.hasDerivAt
    have h2 := hd.mul hχ₁.differentiableAt.hasDerivAt
    exact h1.sub h2
  rw [hL.deriv]
  have hc1 := abs_deriv_bartaCutoff_le (c := b + 2) one_pos hΛ x
  have hc2 := abs_deriv_bartaCutoff_le (c := b - w) hw0 hΛ x
  have hΦx : riemannKernelReal x ≤ bartaEdge b := by
    rw [← riemannKernelReal_abs]
    exact riemannKernelReal_antitoneOn (log_two_half_le_bartaInner hb)
      (le_trans (log_two_half_le_bartaInner hb) hx) hx
  have hΦ0 := (riemannKernelReal_pos x).le
  -- the bound on `d`
  have hdΦ : |d| ≤ bartaDerivConst * Real.exp (13 / 2 * (b + 2)) * bartaEdge b := by
    have hlow := exp_neg_pi_exp_le_riemannKernelReal hs0.le
    have h1 : Real.exp (13 / 2 * |x|) ≤ Real.exp (13 / 2 * (b + 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-π * Real.exp (2 * |x|)) ≤ Real.exp (-π * Real.exp (2 * bartaInner b)) := by
      apply Real.exp_le_exp.mpr
      have := Real.exp_le_exp.mpr (show 2 * bartaInner b ≤ 2 * |x| by linarith)
      nlinarith [Real.pi_pos]
    calc |d| ≤ bartaDerivConst * Real.exp (13 / 2 * |x|) * Real.exp (-π * Real.exp (2 * |x|)) := hdbound
      _ ≤ bartaDerivConst * Real.exp (13 / 2 * (b + 2)) * Real.exp (-π * Real.exp (2 * bartaInner b)) := by
          gcongr
      _ ≤ bartaDerivConst * Real.exp (13 / 2 * (b + 2)) * bartaEdge b := by
          gcongr
          exact hlow
  have hcut2 := bartaCutoff_nonneg (b + 2) 1 x
  have hcut1 := bartaCutoff_nonneg (b - w) w x
  have hcut2' := bartaCutoff_le_one (b + 2) 1 x
  have hcut1' := bartaCutoff_le_one (b - w) w x
  have hwinv : 2 * Λ / w = 2 * Λ * Real.exp (2 * b) := by
    rw [hw, bartaWidth, div_eq_mul_inv, ← Real.exp_neg]; ring_nf
  have hdiff : |bartaCutoff (b + 2) 1 x - bartaCutoff (b - w) w x| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc |d * bartaCutoff (b + 2) 1 x + riemannKernelReal x * deriv (bartaCutoff (b + 2) 1) x -
        (d * bartaCutoff (b - w) w x + riemannKernelReal x * deriv (bartaCutoff (b - w) w) x)|
      = |d * (bartaCutoff (b + 2) 1 x - bartaCutoff (b - w) w x) +
          riemannKernelReal x * (deriv (bartaCutoff (b + 2) 1) x -
            deriv (bartaCutoff (b - w) w) x)| := by ring_nf
    _ ≤ |d| * 1 + riemannKernelReal x * (2 * Λ / 1 + 2 * Λ / w) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
        · rw [abs_mul, abs_of_nonneg hΦ0]
          refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hc1 hc2)) hΦ0
    _ ≤ bartaDerivConst * Real.exp (13 / 2 * (b + 2)) * bartaEdge b * 1 +
          bartaEdge b * (2 * Λ / 1 + 2 * Λ / w) := by
        gcongr
    _ = bartaEdge b * (bartaDerivConst * Real.exp (13 / 2 * (b + 2)) + 2 * Λ +
          2 * Λ * Real.exp (2 * b)) := by
        rw [← hwinv]; ring

/-! ## The edge bound -/

/-- The aperture `b + 3` hosting the layer. -/
def bartaAperture (b : ℝ) (hb : 1 ≤ b) : SuzukiPositiveAperture := ⟨b + 3, by linarith⟩

/-- The layer `T_b = Φ(χ_{b+2,1} - χ_{b-w,w})` as a smooth interior source at aperture `b + 3`. -/
def bartaLayerAt (b : ℝ) (hb : 1 ≤ b) : CCMComplexSmoothInteriorSource (bartaAperture b hb) :=
  bartaLayerSource (bartaAperture b hb) (b - bartaWidth b) (bartaWidth b) (b + 2) 1
    (bartaWidth_pos b) one_pos
    (by show b - bartaWidth b < b + 3; linarith [bartaWidth_pos b])
    (by show b + 2 < b + 3; linarith)

theorem bartaLayerAt_apply (b : ℝ) (hb : 1 ≤ b) (t : ℝ) :
    bartaLayerAt b hb t = ((bartaLayerFn b t : ℝ) : ℂ) := by
  simp [bartaLayerAt, bartaLayerFn]

theorem norm_bartaLayerAt (b : ℝ) (hb : 1 ≤ b) (t : ℝ) :
    ‖bartaLayerAt b hb t‖ = bartaLayerFn b t := by
  rw [bartaLayerAt_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bartaLayerFn_bounds b t).1]

theorem norm_deriv_bartaLayerAt (b : ℝ) (hb : 1 ≤ b) (x : ℝ) :
    ‖deriv (bartaLayerAt b hb) x‖ = |deriv (bartaLayerFn b) x| := by
  have hdiff : DifferentiableAt ℝ (bartaLayerFn b) x :=
    ((contDiff_bartaProfile (n := 1) _ _).sub (contDiff_bartaProfile (n := 1) _ _)).differentiable
      (by norm_num) x
  have hfun : (bartaLayerAt b hb : ℝ → ℂ) = fun t => ((bartaLayerFn b t : ℝ) : ℂ) :=
    funext (bartaLayerAt_apply b hb)
  rw [hfun, (hdiff.hasDerivAt.ofReal_comp).deriv, Complex.norm_real, Real.norm_eq_abs]

/-- **The edge bound.** There is `C` such that for all `b ≥ 1` and every smooth interior source
`v` at aperture `b + 3`, `|Q_{b+3}(v, T_b)| ≤ C (1 + b) Φ(b - 2w) ∫|v|`. -/
theorem exists_bartaEdge_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ) (hb : 1 ≤ b)
    (v : CCMComplexSmoothInteriorSource (bartaAperture b hb)),
    ‖ccmRestrictedWeilForm (bartaAperture b hb) v.toCCMFormVector
        (bartaLayerAt b hb).toCCMFormVector‖ ≤
      (∫ y : ℝ, ‖v y‖) * (bartaEdge b * (C * (1 + b))) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hCD := cuspDecayConst_nonneg (cuspDeriv riemannCuspPoly)
  set C₀ : ℝ := 8 * Real.exp 3 + 2 * (2 * (1 + 2 * Real.exp 3) + 110) + 17 +
    3 * (Real.log (1 + bartaDerivConst + 4 * Λ) + 13) with hC₀
  have hlogpos : 0 ≤ Real.log (1 + bartaDerivConst + 4 * Λ) :=
    Real.log_nonneg (by unfold bartaDerivConst; linarith)
  have hC₀pos : 0 ≤ C₀ := by positivity
  refine ⟨C₀ + 20, by linarith, fun b hb v => ?_⟩
  set T := bartaLayerAt b hb with hT
  set Φ₀ := bartaEdge b with hΦ₀
  set K := bartaRate b with hK
  set ρ : ℝ := bartaDerivConst * Real.exp (13 / 2 * (b + 2)) + 2 * Λ + 2 * Λ * Real.exp (2 * b)
    with hρ
  have hΦ₀pos : 0 < Φ₀ := bartaEdge_pos b
  have hρ0 : 0 ≤ ρ := by unfold bartaDerivConst at hρ; positivity
  have hKpos : 0 < K := lt_of_lt_of_le (Real.exp_pos _) (exp_two_le_bartaRate hb)
  have haval : (bartaAperture b hb).1 = b + 3 := rfl
  -- the four inputs
  have hP : ∀ y : ℝ, |y| ≤ (bartaAperture b hb).1 →
      ∫ h in Ioc (0 : ℝ) (2 * (bartaAperture b hb).1),
      (‖T (y + h)‖ + ‖T (y - h)‖) * (2 * Real.cosh (h / 2)) ≤
        8 * Real.exp (b + 3) * (Φ₀ / K) := by
    intro y _
    simp only [hT, norm_bartaLayerAt, haval]
    exact bartaLayer_pole_lag_le hb y
  have hS : ∀ y : ℝ, |y| ≤ (bartaAperture b hb).1 →
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (bartaAperture b hb).1)⌋₊,
      criticalMellinAtomWeight k * (‖T (y + Real.log k)‖ + ‖T (y - Real.log k)‖) ≤
        2 * Φ₀ * (2 * (1 + 2 * Real.exp 3) + 110) := by
    intro y hy
    simp only [hT, norm_bartaLayerAt]
    exact bartaLayer_prime_lag_le hb (by rwa [haval] at hy) _
  have hA : ∀ x, ‖T x‖ ≤ Φ₀ := fun x => by
    simp only [hT, norm_bartaLayerAt]; exact bartaLayerFn_le_edge hb x
  have hA' : ∀ x, ‖deriv T x‖ ≤ Φ₀ * ρ := fun x => by
    simp only [hT]
    rw [norm_deriv_bartaLayerAt]
    exact abs_deriv_bartaLayerFn_le hb hΛ x
  have hδ : 0 < 1 / (1 + ρ) := by positivity
  have hδ1 : 1 / (1 + ρ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hmain := norm_ccmRestrictedWeilForm_smooth_le v T hP hS hA hA' hδ hδ1
  set N : ℝ := ∫ y : ℝ, ‖v y‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  refine hmain.trans ?_
  apply mul_le_mul_of_nonneg_left _ hN0
  -- the bracket
  have hlogδ : Real.log (1 / (1 / (1 + ρ))) = Real.log (1 + ρ) := by
    rw [one_div_one_div]
  have hρle : 1 + ρ ≤ (1 + bartaDerivConst + 4 * Λ) * Real.exp (13 / 2 * (b + 2)) := by
    have h1 : 1 ≤ Real.exp (13 / 2 * (b + 2)) := Real.one_le_exp (by linarith)
    have h2 : Real.exp (2 * b) ≤ Real.exp (13 / 2 * (b + 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hD : 0 ≤ bartaDerivConst := hCD
    rw [hρ]; nlinarith
  have hloglin : Real.log (1 + ρ) ≤ Real.log (1 + bartaDerivConst + 4 * Λ) + 13 / 2 * (b + 2) := by
    have hpos : 0 < 1 + bartaDerivConst + 4 * Λ := by unfold bartaDerivConst; positivity
    calc Real.log (1 + ρ) ≤ Real.log ((1 + bartaDerivConst + 4 * Λ) * Real.exp (13 / 2 * (b + 2))) :=
          Real.log_le_log (by linarith) hρle
      _ = Real.log (1 + bartaDerivConst + 4 * Λ) + 13 / 2 * (b + 2) := by
          rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hpole : 8 * Real.exp (b + 3) * (Φ₀ / K) ≤ Φ₀ * (8 * Real.exp 3) := by
    have hK' := exp_two_le_bartaRate hb
    rw [mul_div_assoc', div_le_iff₀ hKpos]
    have h1 : Real.exp (b + 3) ≤ Real.exp 3 * Real.exp (2 * b) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have := Real.exp_pos 3
    nlinarith [mul_le_mul_of_nonneg_left hK' (show 0 ≤ Φ₀ * (8 * Real.exp 3) by positivity)]
  have hδmul : 1 / (1 + ρ) * (Φ₀ + Φ₀ * ρ) = Φ₀ := by field_simp
  rw [hlogδ, hδmul]
  have hb0 : 0 ≤ b := by linarith
  calc 8 * Real.exp (b + 3) * (Φ₀ / K) + 2 * Φ₀ * (2 * (1 + 2 * Real.exp 3) + 110) +
        2 * Φ₀ * (8 + 3 / 2 * Real.log (1 + ρ)) + Φ₀
      ≤ Φ₀ * (8 * Real.exp 3) + 2 * Φ₀ * (2 * (1 + 2 * Real.exp 3) + 110) +
        2 * Φ₀ * (8 + 3 / 2 * (Real.log (1 + bartaDerivConst + 4 * Λ) + 13 / 2 * (b + 2))) + Φ₀ := by
        gcongr
    _ = Φ₀ * (C₀ + 39 / 2 * b) := by rw [hC₀]; ring
    _ ≤ Φ₀ * ((C₀ + 20) * (1 + b)) := by
        apply mul_le_mul_of_nonneg_left _ hΦ₀pos.le
        nlinarith

end

end RHTower
