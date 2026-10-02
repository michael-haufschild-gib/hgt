import GaloisForLFunctions.RHTower.DeBruijnPolynomialGaussianAverage
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountAntitone
import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount

/-!
# Polynomial approximation controls the nonreal count of the flow

Let real polynomials `R_n` converge to `H_0 = Ξ` locally uniformly on `ℂ`, with a Gaussian bound
`|R_n(w)| ≤ C e^{S|w|²}` and at most `K` nonreal roots each.  Both `H_t` and the polynomial heat
flows `e^{−tD²}R_n` are Gaussian averages in the imaginary direction
(`riemannHeat_eq_integral_gaussian_shift`, `polyHeat_map_eval_eq_integral`).  For `8St < 1` the
Gaussian bound dominates these averages, so `e^{−tD²}R_n → H_t` locally uniformly
(`tendstoLocallyUniformly_gaussian_average`).  Every heat flow has at most `K` nonreal roots
(`nonrealRootCount_polyHeat_le`), and Hurwitz's theorem on isolating discs gives
`N(t) ≤ K` (`nonrealZeroCount_le_of_approx`).
-/

open Complex MeasureTheory Filter Topology Set Metric Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- `H_t(z) = ∫ g_t(u) H_0(z − iu) du`. -/
theorem riemannHeat_eq_integral_gaussian_shift {t : ℝ} (ht : 0 < t) (z : ℂ) :
    riemannHeat t z = ∫ u : ℝ, (gaussDensity t u : ℂ) * riemannHeat 0 (z - I * u) := by
  rw [riemannHeat_eq_integral_gaussian_xi ht]
  congr 1
  funext u
  rw [riemannHeat_zero]
  congr 2
  ring_nf
  rw [I_sq]
  ring

/-- `(e^{−tD²}R)(z) = ∫ g_t(u) R(z − iu) du` for a real polynomial `R`. -/
theorem polyHeat_map_eval_eq_integral {t : ℝ} (ht : 0 < t) (R : ℝ[X]) (z : ℂ) :
    ((polyHeat t R).map Complex.ofRealHom).eval z =
      ∫ u : ℝ, (gaussDensity t u : ℂ) * (R.map Complex.ofRealHom).eval (z - I * u) := by
  rw [integral_gaussDensity_mul_eval_sub ht, natDegree_map_eq_of_injective
    Complex.ofRealHom.injective, polyHeat, Polynomial.map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.map_mul, map_C, eval_mul, eval_C, ← iterate_derivative_map]
  congr 1
  rw [Complex.ofRealHom_eq_coe]
  push_cast
  ring

/-! ## Locally uniform convergence of Gaussian averages -/

theorem integrable_gaussDensity_mul_exp_sq {t S : ℝ} (ht : 0 < t) (htS : 8 * S * t < 1) :
    Integrable (fun u : ℝ => gaussDensity t u * Real.exp (2 * S * u ^ 2)) := by
  have hb : 0 < 1 / (4 * t) - 2 * S := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]; linarith
  have h := (integrable_exp_neg_mul_sq hb).const_mul ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)))
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [gaussDensity]
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Gaussian averages of Gaussian-bounded functions converge locally uniformly.** -/
theorem tendstoLocallyUniformly_gaussian_average {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hFc : ∀ n, Continuous (F n)) (hfc : Continuous f)
    (hconv : TendstoLocallyUniformly F f atTop) {C S t : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S)
    (ht : 0 < t) (htS : 8 * S * t < 1)
    (hFb : ∀ n w, ‖F n w‖ ≤ C * Real.exp (S * ‖w‖ ^ 2))
    (hfb : ∀ w, ‖f w‖ ≤ C * Real.exp (S * ‖w‖ ^ 2)) :
    TendstoLocallyUniformly (fun n z => ∫ u : ℝ, (gaussDensity t u : ℂ) * F n (z - I * u))
      (fun z => ∫ u : ℝ, (gaussDensity t u : ℂ) * f (z - I * u)) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨r₀, hr₀⟩ := hK.isBounded.exists_norm_le
  set r := max r₀ 0
  have hr : 0 ≤ r := le_max_right _ _
  -- the dominating function
  set D : ℝ → ℝ := fun u => 2 * C * Real.exp (2 * S * r ^ 2) *
    (gaussDensity t u * Real.exp (2 * S * u ^ 2))
  have hDint : Integrable D := (integrable_gaussDensity_mul_exp_sq ht htS).const_mul _
  have hbound : ∀ (G : ℂ → ℂ), (∀ w, ‖G w‖ ≤ C * Real.exp (S * ‖w‖ ^ 2)) → ∀ z : ℂ, ‖z‖ ≤ r →
      ∀ u : ℝ, ‖(gaussDensity t u : ℂ) * G (z - I * u)‖ ≤ D u / 2 := by
    intro G hG z hz u
    have hw : ‖z - I * u‖ ≤ r + |u| := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      linarith
    have hsq : ‖z - I * u‖ ^ 2 ≤ 2 * r ^ 2 + 2 * u ^ 2 := by
      have h0 : 0 ≤ ‖z - I * u‖ := norm_nonneg _
      have hu2 : |u| ^ 2 = u ^ 2 := sq_abs u
      nlinarith [sq_nonneg (r - |u|), abs_nonneg u]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos ht u)]
    have hg := (gaussDensity_pos ht u).le
    calc gaussDensity t u * ‖G (z - I * u)‖
        ≤ gaussDensity t u * (C * Real.exp (S * (2 * r ^ 2 + 2 * u ^ 2))) := by
          gcongr
          exact (hG _).trans (by gcongr)
      _ = D u / 2 := by
          simp only [D]
          rw [show S * (2 * r ^ 2 + 2 * u ^ 2) = 2 * S * r ^ 2 + 2 * S * u ^ 2 by ring,
            Real.exp_add]
          ring
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- a tail beyond `U` of size `< ε/2`
  have htail : Tendsto (fun U : ℝ => ∫ u : ℝ, Set.indicator {u : ℝ | U < |u|} D u) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (l := atTop)
      (bound := fun u => |D u|)
      (F := fun U u => Set.indicator {u : ℝ | U < |u|} D u) (f := fun _ => (0 : ℝ))
      (Eventually.of_forall fun U => (hDint.indicator (measurableSet_lt measurable_const
        measurable_id.abs)).aestronglyMeasurable)
      (Eventually.of_forall fun U => Eventually.of_forall fun u => by
        simp only [Set.indicator, Real.norm_eq_abs]
        split_ifs <;> simp [abs_nonneg])
      hDint.abs (Eventually.of_forall fun u => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (|u|)] with U hU
        simp only [Set.indicator, Set.mem_setOf_eq]
        rw [if_neg (not_lt.mpr hU)])
    simpa using h
  obtain ⟨U, hU⟩ := (Metric.tendsto_atTop.mp htail) (ε / 2) (by positivity)
  have hUt := hU (max U 0) (le_max_left _ _)
  set U' := max U 0
  rw [Real.dist_eq, sub_zero] at hUt
  have hUt' : ∫ u : ℝ, Set.indicator {u : ℝ | U' < |u|} D u < ε / 2 := (le_abs_self _).trans_lt hUt
  -- uniform closeness on the compact part
  have hunif := (Metric.tendstoUniformlyOn_iff.mp
    ((tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) _ (isCompact_closedBall 0 (r + U'))))
    (ε / 2) (by positivity)
  filter_upwards [hunif] with n hn z hz
  have hzr : ‖z‖ ≤ r := (hr₀ z hz).trans (le_max_left _ _)
  have hint1 : Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * f (z - I * u)) :=
    hDint.div_const 2 |>.mono' (((continuous_ofReal.comp
      (by unfold gaussDensity; fun_prop)).mul (hfc.comp (by fun_prop))).aestronglyMeasurable)
      (Eventually.of_forall fun u => hbound f hfb z hzr u)
  have hint2 : Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * F n (z - I * u)) :=
    hDint.div_const 2 |>.mono' (((continuous_ofReal.comp
      (by unfold gaussDensity; fun_prop)).mul ((hFc n).comp (by fun_prop))).aestronglyMeasurable)
      (Eventually.of_forall fun u => hbound (F n) (hFb n) z hzr u)
  rw [dist_eq_norm, ← integral_sub hint1 hint2]
  -- the piecewise bound
  set b : ℝ → ℝ := fun u => gaussDensity t u * (ε / 2) + Set.indicator {u : ℝ | U' < |u|} D u
  have hbint : Integrable b := by
    have h1 : Integrable (fun u : ℝ => gaussDensity t u * (ε / 2)) := by
      have := (integrable_gaussDensity_mul_pow ht 0).mul_const (ε / 2)
      simpa using this
    exact h1.add (hDint.indicator (measurableSet_lt measurable_const measurable_id.abs))
  have hle : ∀ u : ℝ, ‖(gaussDensity t u : ℂ) * f (z - I * u) -
      (gaussDensity t u : ℂ) * F n (z - I * u)‖ ≤ b u := by
    intro u
    have hg := (gaussDensity_pos ht u).le
    by_cases hu : |u| ≤ U'
    · have hw : z - I * u ∈ closedBall (0 : ℂ) (r + U') := by
        rw [mem_closedBall, dist_zero_right]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        linarith
      have h1 := hn _ hw
      rw [dist_eq_norm] at h1
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
      have hind : Set.indicator {u : ℝ | U' < |u|} D u = 0 := by
        simp only [Set.indicator, Set.mem_setOf_eq]; rw [if_neg (not_lt.mpr hu)]
      simp only [b, hind, add_zero]
      exact mul_le_mul_of_nonneg_left h1.le hg
    · have hind : Set.indicator {u : ℝ | U' < |u|} D u = D u := by
        simp only [Set.indicator, Set.mem_setOf_eq]; rw [if_pos (not_le.mp hu)]
      have h1 := hbound f hfb z hzr u
      have h2 := hbound (F n) (hFb n) z hzr u
      simp only [b, hind]
      have : 0 ≤ gaussDensity t u * (ε / 2) := by positivity
      calc _ ≤ ‖(gaussDensity t u : ℂ) * f (z - I * u)‖ +
            ‖(gaussDensity t u : ℂ) * F n (z - I * u)‖ := norm_sub_le _ _
        _ ≤ D u / 2 + D u / 2 := add_le_add h1 h2
        _ ≤ gaussDensity t u * (ε / 2) + D u := by linarith
  calc ‖∫ u, ((gaussDensity t u : ℂ) * f (z - I * u) - (gaussDensity t u : ℂ) * F n (z - I * u))‖
      ≤ ∫ u, b u := norm_integral_le_of_norm_le hbint (Eventually.of_forall hle)
    _ = ε / 2 * 1 + ∫ u : ℝ, Set.indicator {u : ℝ | U' < |u|} D u := by
        have hg1 : Integrable (fun u : ℝ => gaussDensity t u * (ε / 2)) := by
          have := (integrable_gaussDensity_mul_pow ht 0).mul_const (ε / 2)
          simpa using this
        have h1 := integral_gaussDensity_mul_rexp ht 0
        simp only [mul_zero, Real.exp_zero, mul_one] at h1
        show ∫ u, (gaussDensity t u * (ε / 2) + Set.indicator {u : ℝ | U' < |u|} D u) = _
        have hms : MeasurableSet {u : ℝ | U' < |u|} :=
          measurableSet_lt measurable_const measurable_id.abs
        rw [integral_add hg1 (hDint.indicator hms), integral_mul_const, h1]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
          Real.exp_zero]
        ring
    _ < ε := by linarith

/-! ## Hurwitz -/

/-- **Polynomial approximation bounds the nonreal count.** Let real polynomials `R_n` converge to
`H_0` locally uniformly on `ℂ`, with `|R_n(w)| ≤ C e^{S|w|²}` and at most `K` nonreal roots each.
Then `N(t) ≤ K` for `0 < t` with `8St < 1`. -/
theorem nonrealZeroCount_le_of_approx {R : ℕ → ℝ[X]} {K : ℕ} {C S : ℝ} (hC : 0 ≤ C)
    (hS : 0 ≤ S) (hR : ∀ n, R n ≠ 0) (hK : ∀ n, nonrealRootCount (R n) ≤ K)
    (hconv : TendstoLocallyUniformly (fun n z => ((R n).map Complex.ofRealHom).eval z)
      (riemannHeat 0) atTop)
    (hdom : ∀ n w, ‖((R n).map Complex.ofRealHom).eval w‖ ≤ C * Real.exp (S * ‖w‖ ^ 2))
    {t : ℝ} (ht : 0 < t) (htS : 8 * S * t < 1) : nonrealZeroCount t ≤ K := by
  classical
  have hH0 : ∀ w, ‖riemannHeat 0 w‖ ≤ C * Real.exp (S * ‖w‖ ^ 2) := fun w =>
    le_of_tendsto' ((TendstoLocallyUniformly.tendstoLocallyUniformlyOn hconv
      (s := Set.univ)).tendsto_at (Set.mem_univ w)).norm (fun n => hdom n w)
  set G : ℕ → ℂ → ℂ := fun n z => ((polyHeat t (R n)).map Complex.ofRealHom).eval z with hGdef
  have hGconv : TendstoLocallyUniformly G (riemannHeat t) atTop := by
    have h := tendstoLocallyUniformly_gaussian_average
      (F := fun n z => ((R n).map Complex.ofRealHom).eval z) (f := riemannHeat 0)
      (fun n => Polynomial.continuous _) (differentiable_riemannHeat le_rfl).continuous hconv
      hC hS ht htS hdom hH0
    have e1 : G = fun n z => ∫ u : ℝ, (gaussDensity t u : ℂ) *
        ((R n).map Complex.ofRealHom).eval (z - I * u) := by
      funext n z; exact polyHeat_map_eval_eq_integral ht (R n) z
    have e2 : riemannHeat t = fun z => ∫ u : ℝ, (gaussDensity t u : ℂ) *
        riemannHeat 0 (z - I * u) := by
      funext z; exact riemannHeat_eq_integral_gaussian_shift ht z
    rw [e1, e2]
    exact h
  have hGd : ∀ n, Differentiable ℂ (G n) := fun n => Polynomial.differentiable _
  -- isolating discs around the nonreal zeros of `H_t`
  set Zt := (riemannHeat_nonreal_zeros_finite ht).toFinset with hZt
  have hmemZ : ∀ e, e ∈ Zt ↔ riemannHeat t e = 0 ∧ e.im ≠ 0 := by
    intro e; rw [hZt, Set.Finite.mem_toFinset]; rfl
  choose ρ₀ hρ₀ hρ₀prop using fun e => eventually_zeroSumBall_riemannHeat_eq ht e
  obtain ⟨d, hd, hdsep⟩ := exists_pos_sep Zt
  set r : ℂ → ℝ := fun e => min (ρ₀ e) (min (|e.im| / 2) (d / 3)) with hrdef
  have hrpos : ∀ e ∈ Zt, 0 < r e := fun e he =>
    lt_min (hρ₀ e) (lt_min (by have := abs_pos.mpr ((hmemZ e).mp he).2; linarith) (by linarith))
  have hrρ : ∀ e, r e ≤ ρ₀ e := fun e => min_le_left _ _
  have havoid : ∀ e ∈ Zt, ∀ w ∈ ball e (r e), w.im ≠ 0 := by
    intro e he w hw hw0
    have h1 : |(w - e).im| ≤ ‖w - e‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hw0, zero_sub, abs_neg] at h1
    rw [mem_ball, dist_eq_norm] at hw
    have := (min_le_right _ _).trans (min_le_left (|e.im| / 2) (d / 3)) |>.trans_eq' (rfl : r e = _)
    have hpos := abs_pos.mpr ((hmemZ e).mp he).2
    have hr2 : r e ≤ |e.im| / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hdisj : ∀ e ∈ Zt, ∀ e' ∈ Zt, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')) := by
    intro e he e' he' hne
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hdsep e he e' he' hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    have h3 : r e ≤ d / 3 := (min_le_right _ _).trans (min_le_right _ _)
    have h4 : r e' ≤ d / 3 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  -- the count of `H_t`
  have hNt : nonrealZeroCount t = ∑ e ∈ Zt, zeroMult (riemannHeat t) e := by
    rw [nonrealZeroCount_eq ht]
  -- eventually the heat flows carry the same disc counts
  have hev : ∀ e ∈ Zt, ∀ᶠ n in atTop,
      zeroSumBall (G n) e (r e) = (zeroMult (riemannHeat t) e : ℂ) ∧
        ∀ w ∈ sphere e (r e), G n w ≠ 0 := by
    intro e he
    obtain ⟨hsph, hcount, -⟩ := hρ₀prop e (r e) (hrpos e he) (hrρ e)
    have h1 := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hGd
      (differentiable_riemannHeat ht.le) hGconv (hrpos e he)
      (by linarith [hrpos e he] : r e < 2 * r e) hsph
    have h2 := eventually_ne_zero_on_sphere (differentiable_riemannHeat ht.le).continuous hGconv
      (hrpos e he).le hsph
    filter_upwards [h1, h2] with n hn1 hn2
    exact ⟨by rw [hn1, hcount], hn2⟩
  obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset Zt).mpr hev).exists
  have hP := natDegree_polyHeat t (hR n)
  have hBn : (polyHeat t (R n)).map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hP.2
  have hsum := sum_le_card_nonreal_roots hBn (E := Zt) (r := r)
    (n := fun e => zeroMult (riemannHeat t) e) hrpos havoid hdisj
    (fun e he => (hn e he).2) (fun e he => (hn e he).1)
  rw [← nonrealRootCount_eq] at hsum
  rw [hNt]
  exact hsum.trans ((nonrealRootCount_polyHeat_le ht (hR n)).trans (hK n))

end

end RHTower.DeBruijn
