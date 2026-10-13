import GaloisForLFunctions.RHTower.WeilLagOneSidedConfigurationRigidity

/-!
# Exponentially rare excursions force positive configurations on-line

For a configuration with positive summable weights `c_i` and locally finite exponents `w_i`,
`Re w_i ≤ B`, put `Φ(t) = Re Σ_i c_i e^{t w_i}`.

**Theorem** (`re_nonpos_of_lag_le_except`). If `Φ(t) ≤ M` for every `t ≥ 0` outside a measurable
set `E` with `∫_E e^{κu} du < ∞` for some `κ > 0`, then `Re w_i ≤ 0` for every `i`. In particular
(`re_nonpos_of_integrableOn_exp_excursion`), the excursion set `{t ≥ 0 : Φ(t) > M}` of an off-line
configuration never has `∫ e^{κt} dt < ∞`.

**Theorem** (`exists_re_gt_of_lag_le_finiteMeasure`). If `Φ ≤ M` on `[0, ∞)` outside a set of finite
measure, then no exponent with positive real part attains `sup_i Re w_i`.

So the positive excursions of an off-line configuration are never exponentially rare, and they have
infinite measure unless the top is not attained. The Fejér-block configuration of
`AlmostEverySpacing` has excursions of finite measure and a non-attained top.

**Proof.**
*One round* (`re_le_of_lag_le_except`). Replace `Φ` by `M` on `E`. The Laplace transform then
changes by `∫_E (Φ − M) e^{−su} du`, which is holomorphic on `Re s > B − κ`
(`hasDerivAt_laplace_of_integrable`). So Landau across a real pole (`false_of_realPole`) excludes
every real exponent `p > max(B − κ, 0)`, and the twist `1 + cos(t Im w_j)` reduces off-line exponents
to real ones: `Re w_i ≤ max(B − κ, 0)`.
*Bootstrap.* Each round lowers the bound `B` by the fixed amount `κ`; after `⌈B/κ⌉` rounds
`Re w_i ≤ 0`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.LocallyFiniteExponentialSumRigidity

namespace RHTower.OneSidedConfiguration

noncomputable section

variable {ι : Type*}

/-! ## Holomorphy of a Laplace transform with an exponential majorant -/

/-- If `‖g(u)‖ e^{−bu}` is integrable on `(0, ∞)` for every `b > α`, then
`s ↦ ∫_0^∞ g(u) e^{−su} du` is complex differentiable at every `z` with `Re z > α`. -/
theorem hasDerivAt_laplace_of_integrable {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0:ℝ)))) {α : ℝ}
    (hint : ∀ b : ℝ, α < b →
      Integrable (fun u => ‖g u‖ * Real.exp (-b * u)) (volume.restrict (Ioi (0:ℝ))))
    {z : ℂ} (hz : α < z.re) :
    HasDerivAt (fun s : ℂ => ∫ u in Ioi (0:ℝ), g u * cexp (-s * u))
      (∫ u in Ioi (0:ℝ), g u * (-(u : ℂ) * cexp (-z * u))) z := by
  set ε : ℝ := (z.re - α) / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hb : α < z.re - 2 * ε := by rw [hε]; linarith
  have hcexp : ∀ x : ℂ, Continuous fun u : ℝ => cexp (-x * u) := fun x =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hmeasF : ∀ᶠ x : ℂ in 𝓝 z,
      AEStronglyMeasurable (fun u : ℝ => g u * cexp (-x * u)) (volume.restrict (Ioi (0:ℝ))) :=
    Filter.Eventually.of_forall fun x => hg.mul (hcexp x).aestronglyMeasurable
  have hInt : Integrable (fun u : ℝ => g u * cexp (-z * u)) (volume.restrict (Ioi (0:ℝ))) := by
    refine (hint _ hz).mono' (hg.mul (hcexp z).aestronglyMeasurable) ?_
    filter_upwards with u
    rw [norm_mul, norm_cexp_neg_mul]
  have hmeasF' : AEStronglyMeasurable (fun u : ℝ => g u * (-(u : ℂ) * cexp (-z * u)))
      (volume.restrict (Ioi (0:ℝ))) :=
    hg.mul ((Complex.continuous_ofReal.neg.mul (hcexp z)).aestronglyMeasurable)
  have hue : ∀ u : ℝ, 0 ≤ u → u * Real.exp (-(ε * u)) ≤ 1 / ε := by
    intro u hu
    have h4 := Real.add_one_le_exp (ε * u)
    have h5 : ε * u * Real.exp (-(ε * u)) ≤ 1 := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    calc u * Real.exp (-(ε * u)) = ε * u * Real.exp (-(ε * u)) / ε := by field_simp
      _ ≤ 1 / ε := div_le_div_of_nonneg_right h5 hε0.le
  have hdom : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (0:ℝ))), ∀ x ∈ Metric.ball z ε,
      ‖g u * (-(u : ℂ) * cexp (-x * u))‖ ≤
        1 / ε * (‖g u‖ * Real.exp (-(z.re - 2 * ε) * u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu x hx
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have hxre : z.re - ε < x.re := by
      have h1 : |x.re - z.re| ≤ ‖x - z‖ := by simpa using Complex.abs_re_le_norm (x - z)
      have h2 : ‖x - z‖ < ε := by rw [← Complex.dist_eq]; exact Metric.mem_ball.mp hx
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 h2)).1]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hu0,
      norm_cexp_neg_mul]
    have h1 : u * Real.exp (-x.re * u) ≤ u * Real.exp (-(z.re - ε) * u) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hu0
    have h2 : u * Real.exp (-(z.re - ε) * u) =
        (u * Real.exp (-(ε * u))) * Real.exp (-(z.re - 2 * ε) * u) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have h3 : u * Real.exp (-x.re * u) ≤ 1 / ε * Real.exp (-(z.re - 2 * ε) * u) := by
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (hue u hu0) (Real.exp_pos _).le)
    calc ‖g u‖ * (u * Real.exp (-x.re * u))
        ≤ ‖g u‖ * (1 / ε * Real.exp (-(z.re - 2 * ε) * u)) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = 1 / ε * (‖g u‖ * Real.exp (-(z.re - 2 * ε) * u)) := by ring
  have hbound : Integrable (fun u => 1 / ε * (‖g u‖ * Real.exp (-(z.re - 2 * ε) * u)))
      (volume.restrict (Ioi (0:ℝ))) := (hint _ hb).const_mul _
  have hderiv : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (0:ℝ))), ∀ x ∈ Metric.ball z ε,
      HasDerivAt (fun y : ℂ => g u * cexp (-y * u)) (g u * (-(u : ℂ) * cexp (-x * u))) x := by
    filter_upwards with u x _
    have h1 : HasDerivAt (fun y : ℂ => -y * (u : ℂ)) (-(u : ℂ)) x := by
      have h0 : HasDerivAt (fun y : ℂ => (-(u : ℂ)) * y) ((-(u : ℂ)) * 1) x :=
        (hasDerivAt_id x).const_mul (-(u : ℂ))
      refine h0.congr_deriv (by ring) |>.congr_of_eventuallyEq ?_
      filter_upwards with y
      ring
    have h2 := (h1.cexp).const_mul (g u)
    refine h2.congr_deriv ?_
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℂ) (u : ℝ) => g u * cexp (-x * u))
    (F' := fun (x : ℂ) (u : ℝ) => g u * (-(u : ℂ) * cexp (-x * u)))
    (Metric.ball_mem_nhds z hε0) hmeasF hInt hmeasF' hdom hbound hderiv).2

theorem analyticAt_laplace_of_integrable {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0:ℝ)))) {α : ℝ}
    (hint : ∀ b : ℝ, α < b →
      Integrable (fun u => ‖g u‖ * Real.exp (-b * u)) (volume.restrict (Ioi (0:ℝ))))
    {z : ℂ} (hz : α < z.re) :
    AnalyticAt ℂ (fun s : ℂ => ∫ u in Ioi (0:ℝ), g u * cexp (-s * u)) z := by
  have hopen : IsOpen {s : ℂ | α < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticAt (s := {s : ℂ | α < s.re}) (fun s hs => ?_)
    (hopen.mem_nhds hz)
  exact (hasDerivAt_laplace_of_integrable hg hint hs).differentiableAt.differentiableWithinAt

/-! ## The exceptional correction -/

/-- `Φ` continued to `t < 0` by its value at `0`. -/
def lagMax (a w : ι → ℂ) (t : ℝ) : ℝ := (∑' i, a i * cexp ((max t 0 : ℝ) * w i)).re

theorem continuous_lagMax {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) : Continuous (lagMax a w) :=
  Complex.continuous_re.comp (continuous_lagSum_max ha hB)

theorem lagMax_eq {a w : ι → ℂ} {t : ℝ} (ht : 0 ≤ t) : lagMax a w t = lagRe a w t := by
  simp only [lagMax, max_eq_left ht, lagRe]

theorem abs_lagRe_le {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    |lagRe a w t| ≤ (∑' i, ‖a i‖) * Real.exp (t * B) :=
  (Complex.abs_re_le_norm _).trans (norm_lagSum_le ha hB ht)

/-- The pointwise majorant of the exceptional correction. -/
theorem norm_exceptIndicator_mul_exp_le {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i, (w i).re ≤ B) (E : Set ℝ) (M κ : ℝ) {b : ℝ} (hb : B - κ ≤ b)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖E.indicator (fun u => ((lagMax a w u - M : ℝ) : ℂ)) u‖ * Real.exp (-b * u) ≤
      (|M| + ∑' i, ‖a i‖) * E.indicator (fun u => Real.exp (κ * u)) u := by
  by_cases huE : u ∈ E
  · rw [Set.indicator_of_mem huE, Set.indicator_of_mem huE, Complex.norm_real, Real.norm_eq_abs,
      lagMax_eq hu]
    have hA := abs_lagRe_le ha hB hu (a := a)
    have hA0 : 0 ≤ ∑' i, ‖a i‖ := tsum_nonneg fun _ => norm_nonneg _
    have h1 : Real.exp (u * B) * Real.exp (-b * u) ≤ Real.exp (κ * u) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (-b * u) ≤ Real.exp (κ * u) := Real.exp_le_exp.mpr (by nlinarith)
    have h3 := abs_sub (lagRe a w u) M
    have hexp := Real.exp_pos (-b * u)
    calc |lagRe a w u - M| * Real.exp (-b * u)
        ≤ ((∑' i, ‖a i‖) * Real.exp (u * B) + |M|) * Real.exp (-b * u) :=
          mul_le_mul_of_nonneg_right (by linarith) hexp.le
      _ = (∑' i, ‖a i‖) * (Real.exp (u * B) * Real.exp (-b * u)) + |M| * Real.exp (-b * u) := by
          ring
      _ ≤ (∑' i, ‖a i‖) * Real.exp (κ * u) + |M| * Real.exp (κ * u) := by
          gcongr
      _ = (|M| + ∑' i, ‖a i‖) * Real.exp (κ * u) := by ring
  · rw [Set.indicator_of_notMem huE, Set.indicator_of_notMem huE, norm_zero, zero_mul, mul_zero]

theorem integrable_exceptIndicator {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i, (w i).re ≤ B) {E : Set ℝ} (hE : MeasurableSet E) (M : ℝ) {κ : ℝ}
    (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E) {b : ℝ} (hb : B - κ ≤ b) :
    Integrable (fun u => ‖E.indicator (fun u => ((lagMax a w u - M : ℝ) : ℂ)) u‖ *
      Real.exp (-b * u)) (volume.restrict (Ioi (0:ℝ))) := by
  have hc := continuous_lagMax ha hB
  have hI : Integrable (fun u => (|M| + ∑' i, ‖a i‖) * E.indicator (fun u => Real.exp (κ * u)) u)
      (volume.restrict (Ioi (0:ℝ))) :=
    (((integrable_indicator_iff hE).mpr hEint).restrict).const_mul _
  refine hI.mono' ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    exact ((((Complex.measurable_ofReal.comp (hc.measurable.sub measurable_const)).indicator
      hE).norm).mul (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    exact norm_exceptIndicator_mul_exp_le ha hB0 hB E M κ hb (le_of_lt hu)

/-! ## One round of Landau across the exceptional set -/

/-- **One round, sharp form.** A real exponent of a configuration bounded above off a set `E` with
`∫_E e^{κu} du < ∞`, `κ ≥ 0`, is `< B − κ` or `≤ 0`. For `κ = 0` (finite measure) a positive real
exponent cannot reach the bound `B`. -/
theorem re_lt_or_nonpos_of_real_except_quarter [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB0 : 0 ≤ B) (hB4 : B ≤ 1 / 4) (hB : ∀ i, (w i).re ≤ B) (hmax : MaxRealPositive a w)
    {E : Set ℝ} (hE : MeasurableSet E) {κ : ℝ} (hκ : 0 ≤ κ)
    (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe a w t ≤ M) (j : ι) (hj : (w j).im = 0) :
    (w j).re < B - κ ∨ (w j).re ≤ 0 := by
  classical
  by_contra hcon
  simp only [not_or, not_lt, not_le] at hcon
  obtain ⟨hjB, hj0'⟩ := hcon
  have hBq : ∀ i, (w i).re ≤ 1 / 4 := fun i => (hB i).trans hB4
  have hPfin : {i | (w i).im = 0 ∧ 0 < (w i).re}.Finite := (hfin (1 / 4)).subset fun i hi => by
    have h1 := Complex.norm_le_abs_re_add_abs_im (w i)
    rw [hi.1, abs_zero, add_zero, abs_of_pos hi.2] at h1
    exact h1.trans (hBq i)
  obtain ⟨k, hkP, hkmax⟩ := Set.exists_max_image {i | (w i).im = 0 ∧ 0 < (w i).re}
    (fun i => (w i).re) hPfin ⟨j, hj, hj0'⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, (w k).re = p := ⟨_, rfl⟩
  have hwk : w k = p := Complex.ext (by simp [hp]) (by simp [hkP.1])
  have hpj : (w j).re ≤ p := hp ▸ hkmax j ⟨hj, hj0'⟩
  have hp0 : 0 < p := lt_of_lt_of_le hj0' hpj
  have hpB : B - κ ≤ p := hjB.trans hpj
  have hp1 : p < 1 := by linarith [hBq k]
  have hA0 : 0 ≤ ∑' i, ‖a i‖ := tsum_nonneg fun _ => norm_nonneg _
  have hΦc : Continuous (lagMax a w) := continuous_lagMax ha hB
  set g : ℝ → ℂ := E.indicator (fun u => ((lagMax a w u - M : ℝ) : ℂ)) with hg
  have hgm : Measurable g :=
    (Complex.measurable_ofReal.comp (hΦc.measurable.sub measurable_const)).indicator hE
  have hint : ∀ b : ℝ, B - κ < b →
      Integrable (fun u => ‖g u‖ * Real.exp (-b * u)) (volume.restrict (Ioi (0:ℝ))) :=
    fun b hb => integrable_exceptIndicator ha hB0 hB hE M hEint hb.le
  set φ : ℝ → ℝ := fun u => if u ∈ E then M else lagMax a w u with hφ
  have hφm : Measurable φ := Measurable.ite hE measurable_const hΦc.measurable
  have hK : ∀ u, 0 < u → |φ u| ≤ (|M| + ∑' i, ‖a i‖) * Real.exp (u / 2) := by
    intro u hu
    have he1 : 1 ≤ Real.exp (u / 2) := Real.one_le_exp (by linarith)
    have he2 : Real.exp (u * B) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by nlinarith)
    simp only [hφ]
    split_ifs with huE
    · nlinarith [abs_nonneg M]
    · rw [lagMax_eq hu.le]
      have := abs_lagRe_le ha hB hu.le (a := a)
      nlinarith [abs_nonneg M]
  have hMφ : ∀ u, 0 ≤ u → φ u ≤ M := by
    intro u hu
    simp only [hφ]
    split_ifs with huE
    · exact le_rfl
    · rw [lagMax_eq hu]; exact hM u hu huE
  set Λ : ℂ → ℂ := fun s => pairSeries a w s - ∫ u in Ioi (0:ℝ), g u * cexp (-s * u) with hΛ
  have hΛφ : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ u in Ioi (0:ℝ), (φ u : ℂ) * cexp (-s * (u : ℂ)) = Λ s := by
    intro s hs
    have hcexp : Continuous fun u : ℝ => cexp (-s * u) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    have hpt : ∀ u : ℝ, (φ u : ℂ) * cexp (-s * u) =
        (lagMax a w u : ℂ) * cexp (-s * u) - g u * cexp (-s * u) := by
      intro u
      simp only [hφ, hg]
      by_cases huE : u ∈ E
      · rw [if_pos huE, Set.indicator_of_mem huE]; push_cast; ring
      · rw [if_neg huE, Set.indicator_of_notMem huE]; ring
    have hInt1 : Integrable (fun u : ℝ => (lagMax a w u : ℂ) * cexp (-s * u))
        (volume.restrict (Ioi (0:ℝ))) := by
      have hmaj : Integrable (fun u : ℝ => (∑' i, ‖a i‖) * Real.exp (-(s.re - 1 / 4) * u))
          (volume.restrict (Ioi (0:ℝ))) :=
        (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
      refine hmaj.mono' ((Complex.continuous_ofReal.comp hΦc).mul hcexp).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_neg_mul, lagMax_eq hu.le]
      have h1 := abs_lagRe_le ha hBq hu.le (a := a)
      calc |lagRe a w u| * Real.exp (-s.re * u)
          ≤ (∑' i, ‖a i‖) * Real.exp (u * (1 / 4)) * Real.exp (-s.re * u) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = (∑' i, ‖a i‖) * Real.exp (-(s.re - 1 / 4) * u) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have hInt2 : Integrable (fun u : ℝ => g u * cexp (-s * u)) (volume.restrict (Ioi (0:ℝ))) := by
      refine (hint s.re (by linarith)).mono' (hgm.aestronglyMeasurable.mul
        hcexp.aestronglyMeasurable) ?_
      filter_upwards with u
      rw [norm_mul, norm_cexp_neg_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi fun u _ => hpt u, integral_sub hInt1 hInt2]
    have hL : ∫ u in Ioi (0:ℝ), (lagMax a w u : ℂ) * cexp (-s * u) = pairSeries a w s := by
      rw [← integral_lagRe_mul_cexp ha hBq (by linarith : (1 / 4 : ℝ) < s.re)]
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      simp only [lagMax_eq (le_of_lt (show (0:ℝ) < u from hu))]
    rw [hL]
  have hΛan : ∀ t : ℝ, p < t → AnalyticAt ℂ Λ t := by
    intro t ht
    have hne : ∀ i, w i ≠ t := by
      intro i hi
      have him : (w i).im = 0 := by rw [hi]; simp
      have hre : (w i).re = t := by rw [hi]; simp
      have hle : (w i).re ≤ (w k).re := hkmax i ⟨him, by rw [hre]; linarith⟩
      linarith
    have h1 := analyticAt_pairSeries ha hfin hne fun i hi => hne i (by
      rw [← Complex.conj_conj (w i), hi, Complex.conj_ofReal])
    have h2 := analyticAt_laplace_of_integrable hgm.aestronglyMeasurable hint
      (z := (t : ℂ)) (by simp; linarith)
    exact h1.sub h2
  obtain ⟨hk0, hkF⟩ := hmax k hkP.1 hkP.2 fun i hi hi0 => hkmax i ⟨hi, hi0⟩
  have hposp : ∀ i, w i = p → 0 ≤ (a i).re := fun i hi => hkF i (by rw [hi, hwk])
  set C₀ : ℝ := (|M| + ∑' i, ‖a i‖) * ∫ u in E, Real.exp (κ * u) with hC₀
  have hcorr : ∀ σ : ℝ, p < σ → ‖∫ u in Ioi (0:ℝ), g u * cexp (-(σ : ℂ) * u)‖ ≤ C₀ := by
    intro σ hσ
    have hσb : B - κ ≤ σ := by linarith
    refine (norm_integral_le_integral_norm _).trans ?_
    have hI : Integrable (fun u => (|M| + ∑' i, ‖a i‖) * E.indicator (fun u => Real.exp (κ * u)) u)
        := ((integrable_indicator_iff hE).mpr hEint).const_mul _
    calc ∫ u in Ioi (0:ℝ), ‖g u * cexp (-(σ : ℂ) * u)‖
        ≤ ∫ u in Ioi (0:ℝ), (|M| + ∑' i, ‖a i‖) * E.indicator (fun u => Real.exp (κ * u)) u := by
          refine setIntegral_mono_on ?_ hI.integrableOn measurableSet_Ioi fun u hu => ?_
          · refine (hint σ (by linarith)).congr ?_
            filter_upwards with u
            rw [norm_mul, norm_cexp_neg_mul, Complex.ofReal_re]
          · rw [norm_mul, norm_cexp_neg_mul, Complex.ofReal_re]
            exact norm_exceptIndicator_mul_exp_le ha hB0 hB E M κ hσb (le_of_lt hu)
      _ ≤ ∫ u, (|M| + ∑' i, ‖a i‖) * E.indicator (fun u => Real.exp (κ * u)) u :=
          setIntegral_le_integral hI (Filter.Eventually.of_forall fun u =>
            mul_nonneg (by positivity) (Set.indicator_nonneg (fun u _ => (Real.exp_pos _).le) u))
      _ = C₀ := by rw [integral_const_mul, integral_indicator hE]
  have hblow : ∀ N : ℝ, ∃ σ : ℝ, p < σ ∧ N ≤ (Λ σ).re := by
    intro N
    obtain ⟨σ, hσ, hN⟩ := exists_re_pairSeries_ge ha hfin hwk hk0 hposp (N + C₀)
    refine ⟨σ, hσ, ?_⟩
    have h1 := Complex.re_le_norm (∫ u in Ioi (0:ℝ), g u * cexp (-(σ : ℂ) * u))
    have h2 := hcorr σ hσ
    simp only [hΛ, Complex.sub_re]
    linarith
  exact false_of_realPole hφm hK hMφ hΛφ hp0 hp1 hΛan hblow

theorem re_le_of_real_except_quarter [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB0 : 0 ≤ B) (hB4 : B ≤ 1 / 4) (hB : ∀ i, (w i).re ≤ B) (hmax : MaxRealPositive a w)
    {E : Set ℝ} (hE : MeasurableSet E) {κ : ℝ} (hκ : 0 < κ)
    (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe a w t ≤ M) (j : ι) (hj : (w j).im = 0) :
    (w j).re ≤ max (B - κ) 0 := by
  rcases re_lt_or_nonpos_of_real_except_quarter ha hfin hB0 hB4 hB hmax hE hκ.le hEint hM j hj
    with h | h
  · exact h.le.trans (le_max_left _ _)
  · exact h.trans (le_max_right _ _)

/-- **One round, any bound `B ≥ 0`.** A real exponent of a configuration that is bounded above off a
set `E` with `∫_E e^{κu} du < ∞`, `κ ≥ 0`, is `< B − κ` or `≤ 0`. -/
theorem re_lt_or_nonpos_of_real_except [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i, (w i).re ≤ B) (hmax : MaxRealPositive a w)
    {E : Set ℝ} (hE : MeasurableSet E) {κ : ℝ} (hκ : 0 ≤ κ)
    (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe a w t ≤ M) (j : ι) (hj : (w j).im = 0) :
    (w j).re < B - κ ∨ (w j).re ≤ 0 := by
  set l : ℝ := 4 * (B + 1) with hl
  have hl0 : 0 < l := by positivity
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  have him : ∀ i, (w i / l).im = 0 ↔ (w i).im = 0 := fun i => by
    rw [Complex.div_ofReal_im, div_eq_zero_iff]
    exact ⟨fun h => h.resolve_right hl0.ne', Or.inl⟩
  have hre : ∀ i, (w i / l).re = (w i).re / l := fun i => Complex.div_ofReal_re _ _
  have hEl : MeasurableSet ((fun t : ℝ => t / l) ⁻¹' E) := hE.preimage (measurable_id.div_const l)
  have key := re_lt_or_nonpos_of_real_except_quarter (w := fun i => w i / l) (B := B / l) ha ?_
    (by positivity) ?_ ?_ ?_ hEl (κ := κ / l) (div_nonneg hκ hl0.le) ?_ (M := M) ?_ j
    ((him j).mpr hj)
  · rw [hre, ← sub_div] at key
    rcases key with h | h
    · exact Or.inl ((div_lt_div_iff_of_pos_right hl0).mp h)
    · exact Or.inr ((div_nonpos_iff.mp h).elim (fun h' => absurd h'.2 (not_le.mpr hl0))
        fun h' => h'.1)
  · intro R
    refine (hfin (R * l)).subset fun i hi => ?_
    simp only [mem_setOf_eq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl0] at hi ⊢
    exact (div_le_iff₀ hl0).mp hi
  · rw [div_le_iff₀ hl0]; linarith
  · intro i; rw [hre]; exact div_le_div_of_nonneg_right (hB i) hl0.le
  · intro k hk hk0 hkmax
    have hk0' : 0 < (w k).re := by
      rw [hre] at hk0; exact (div_pos_iff_of_pos_right hl0).mp hk0
    obtain ⟨h1, h2⟩ := hmax k ((him k).mp hk) hk0' fun i hi hi0 => by
      have := hkmax i ((him i).mpr hi) (by rw [hre]; exact div_pos hi0 hl0)
      rw [hre, hre] at this
      exact (div_le_div_iff_of_pos_right hl0).mp this
    exact ⟨h1, fun i hi => h2 i ((div_left_inj' hl').mp hi)⟩
  · rw [← integrable_indicator_iff hEl]
    have h := ((integrable_indicator_iff hE).mpr hEint).comp_div hl0.ne'
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    show E.indicator (fun u => Real.exp (κ * u)) (t / l) =
      ((fun t : ℝ => t / l) ⁻¹' E).indicator (fun u => Real.exp (κ / l * u)) t
    by_cases ht : t / l ∈ E
    · rw [Set.indicator_of_mem ht,
        Set.indicator_of_mem (show t ∈ (fun t : ℝ => t / l) ⁻¹' E from ht)]
      congr 1; ring
    · rw [Set.indicator_of_notMem ht,
        Set.indicator_of_notMem (show t ∉ (fun t : ℝ => t / l) ⁻¹' E from ht)]
  · intro t ht htE
    have h := hM (t / l) (div_nonneg ht hl0.le) htE
    have heq : lagRe a (fun i => w i / l) t = lagRe a w (t / l) := by
      unfold lagRe
      congr 1
      refine tsum_congr fun i => ?_
      congr 2
      push_cast
      field_simp
    rw [heq]; exact h

theorem re_le_of_real_except [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i, (w i).re ≤ B) (hmax : MaxRealPositive a w)
    {E : Set ℝ} (hE : MeasurableSet E) {κ : ℝ} (hκ : 0 ≤ κ)
    (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe a w t ≤ M) (j : ι) (hj : (w j).im = 0) :
    (w j).re ≤ max (B - κ) 0 := by
  rcases re_lt_or_nonpos_of_real_except ha hfin hB0 hB hmax hE hκ hEint hM j hj with h | h
  · exact h.le.trans (le_max_left _ _)
  · exact h.trans (le_max_right _ _)

/-! ## The twist of a positive configuration -/

theorem summable_norm_twistCoef {c : ι → ℝ} {w : ι → ℂ} (hc0 : ∀ i, 0 ≤ c i)
    (hcs : Summable c) {B : ℝ} (hB : ∀ i, (w i).re ≤ B) (γ : ℝ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁) :
    Summable fun q : Fin 3 × ι => ‖twistCoef γ s₁ c w q‖ := by
  have hcoef : ∀ q : Fin 3 × ι, ‖twistCoef γ s₁ c w q‖ ≤ c q.2 * Real.exp (s₁ * B) := by
    intro q
    rw [twistCoef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hc0 _) (twistWeight_pos _).le), Complex.norm_exp]
    have hre : ((s₁ : ℂ) * twistExp γ w q).re = s₁ * (w q.2).re := by
      rw [Complex.re_ofReal_mul, re_twistExp]
    rw [hre]
    exact mul_le_mul (mul_le_of_le_one_right (hc0 _) (twistWeight_le_one _))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hB _) hs₁)) (Real.exp_pos _).le (hc0 _)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoef ?_
  exact (summable_prod_of_nonneg fun q => mul_nonneg (hc0 q.2) (Real.exp_pos _).le).mpr
    ⟨fun k => hcs.mul_right _, Summable.of_finite⟩

theorem finite_twistExp {w : ι → ℂ} (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) (γ : ℝ) :
    ∀ R : ℝ, {q : Fin 3 × ι | ‖twistExp γ w q‖ ≤ R}.Finite := by
  intro R
  refine ((Set.finite_univ : (univ : Set (Fin 3)).Finite).prod (hfin (R + |γ|))).subset
    fun q hq => ⟨mem_univ _, ?_⟩
  simp only [mem_setOf_eq, twistExp] at hq ⊢
  have h1 := norm_sub_le (w q.2 + twistShift γ q.1) (twistShift γ q.1)
  rw [add_sub_cancel_right] at h1
  linarith [norm_twistShift_le γ q.1]

theorem re_twistCoef_pos {c : ι → ℝ} {w : ι → ℂ} (hc : ∀ i, 0 < c i) (γ s₁ : ℝ)
    (q : Fin 3 × ι) (him : (twistExp γ w q).im = 0) : 0 < (twistCoef γ s₁ c w q).re := by
  have hx : twistExp γ w q = ((twistExp γ w q).re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [twistCoef, hx, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  exact mul_pos (mul_pos (hc _) (twistWeight_pos _)) (Real.exp_pos _)

/-! ## Exponentially rare excursions -/

/-- **One round.** If `Φ ≤ M` on `[0, ∞)` outside `E` with `∫_E e^{κu} du < ∞`, `κ ≥ 0`, then
every `Re w_i` is `< B − κ` or `≤ 0`. -/
theorem re_lt_or_nonpos_of_lag_le_except [Countable ι] {c : ι → ℝ} {w : ι → ℂ}
    (hc : ∀ i, 0 < c i) (hcs : Summable c) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i, (w i).re ≤ B) {E : Set ℝ} (hE : MeasurableSet E) {κ : ℝ}
    (hκ : 0 ≤ κ) (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe (fun i => (c i : ℂ)) w t ≤ M) (j : ι) :
    (w j).re < B - κ ∨ (w j).re ≤ 0 := by
  have hc0 : ∀ i, 0 ≤ c i := fun i => (hc i).le
  set γ := (w j).im with hγ
  have hMQ : ∀ t : ℝ, 0 ≤ t → t ∉ E →
      lagRe (twistCoef γ 0 c w) (twistExp γ w) t ≤ 2 * max M 0 := by
    intro t ht htE
    rw [lagRe_twist hc0 hcs hB γ le_rfl ht, add_zero]
    have h1 := hM t ht htE
    have hcos := Real.neg_one_le_cos (γ * t)
    have hcos' := Real.cos_le_one (γ * t)
    have hm := le_max_left M 0
    have hm0 := le_max_right M 0
    nlinarith
  have hjQ : (twistExp γ w (2, j)).im = 0 := by simp [twistExp, twistShift, hγ]
  have key := re_lt_or_nonpos_of_real_except (summable_norm_twistCoef hc0 hcs hB γ le_rfl)
    (finite_twistExp hfin γ) hB0 (fun q => by rw [re_twistExp]; exact hB _)
    (maxRealPositive_of_pos fun q hq _ => re_twistCoef_pos hc γ 0 q hq) hE hκ hEint hMQ (2, j)
    hjQ
  rwa [re_twistExp] at key

theorem re_le_of_lag_le_except [Countable ι] {c : ι → ℝ} {w : ι → ℂ} (hc : ∀ i, 0 < c i)
    (hcs : Summable c) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i, (w i).re ≤ B) {E : Set ℝ} (hE : MeasurableSet E) {κ : ℝ} (hκ : 0 < κ)
    (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe (fun i => (c i : ℂ)) w t ≤ M) (j : ι) :
    (w j).re ≤ max (B - κ) 0 := by
  rcases re_lt_or_nonpos_of_lag_le_except hc hcs hfin hB0 hB hE hκ.le hEint hM j with h | h
  · exact h.le.trans (le_max_left _ _)
  · exact h.trans (le_max_right _ _)

/-- **Finite-measure excursions exclude attained tops.** If `Φ ≤ M` on `[0, ∞)` outside a set of
finite measure, then no exponent with positive real part attains `sup_i Re w_i`. The Fejér-block
configuration (`AlmostEverySpacing`) shows that a non-attained top is possible. -/
theorem exists_re_gt_of_lag_le_finiteMeasure [Countable ι] {c : ι → ℝ} {w : ι → ℂ}
    (hc : ∀ i, 0 < c i) (hcs : Summable c) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe (fun i => (c i : ℂ)) w t ≤ M) (j : ι)
    (hj : 0 < (w j).re) : ∃ i, (w j).re < (w i).re := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hEint : IntegrableOn (fun u => Real.exp (0 * u)) E := by
    simp only [zero_mul, Real.exp_zero]
    exact integrableOn_const hEfin
  rcases re_lt_or_nonpos_of_lag_le_except hc hcs hfin hj.le hcon hE le_rfl hEint hM j with h | h
  · linarith
  · linarith

/-- **Exponentially rare excursions force positive configurations on-line.** Let `c_i > 0` be
summable and the exponents `w_i` locally finite with `Re w_i ≤ B`. If `Re Σ_i c_i e^{t w_i} ≤ M`
for every `t ≥ 0` outside a measurable set `E` with `∫_E e^{κu} du < ∞`, `κ > 0`, then `Re w_i ≤ 0`
for every `i`. -/
theorem re_nonpos_of_lag_le_except [Countable ι] {c : ι → ℝ} {w : ι → ℂ} (hc : ∀ i, 0 < c i)
    (hcs : Summable c) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) {E : Set ℝ} (hE : MeasurableSet E) {κ : ℝ} (hκ : 0 < κ)
    (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe (fun i => (c i : ℂ)) w t ≤ M) (j : ι) :
    (w j).re ≤ 0 := by
  have hstep : ∀ n : ℕ, ∀ i, (w i).re ≤ max (max B 0 - n * κ) 0 := by
    intro n
    induction n with
    | zero =>
      intro i
      simp only [Nat.cast_zero, zero_mul, sub_zero]
      exact (hB i).trans ((le_max_left _ _).trans (le_max_left _ _))
    | succ n ih =>
      intro i
      refine (re_le_of_lag_le_except hc hcs hfin (le_max_right _ _) ih hE hκ hEint hM i).trans
        (le_of_eq ?_)
      push_cast
      rcases le_total (max B 0 - n * κ) 0 with h1 | h1
      · rw [max_eq_right h1, zero_sub, max_eq_right (by linarith),
          max_eq_right (by linarith)]
      · rw [max_eq_left h1]; ring_nf
  have h := hstep ⌈max B 0 / κ⌉₊ j
  have hn : max B 0 ≤ (⌈max B 0 / κ⌉₊ : ℝ) * κ := (div_le_iff₀ hκ).mp (Nat.le_ceil _)
  rwa [max_eq_right (by linarith)] at h

/-- **The excursion set of an off-line configuration is never exponentially rare.** If
`∫_{\{t ≥ 0 : Φ(t) > M\}} e^{κt} dt < ∞` for some `κ > 0`, then `Re w_i ≤ 0` for every `i`. -/
theorem re_nonpos_of_integrableOn_exp_excursion [Countable ι] {c : ι → ℝ} {w : ι → ℂ}
    (hc : ∀ i, 0 < c i) (hcs : Summable c) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) {M κ : ℝ} (hκ : 0 < κ)
    (hint : IntegrableOn (fun u => Real.exp (κ * u))
      {t : ℝ | 0 ≤ t ∧ M < lagRe (fun i => (c i : ℂ)) w t}) (j : ι) : (w j).re ≤ 0 := by
  have hsumC : Summable fun i => ‖(c i : ℂ)‖ := by
    refine hcs.congr fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc i)]
  have hset : {t : ℝ | 0 ≤ t ∧ M < lagRe (fun i => (c i : ℂ)) w t} =
      {t : ℝ | 0 ≤ t ∧ M < lagMax (fun i => (c i : ℂ)) w t} := by
    ext t
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨ht, h⟩; exact ⟨ht, by rw [lagMax_eq ht]; exact h⟩
    · rintro ⟨ht, h⟩; exact ⟨ht, by rw [← lagMax_eq ht]; exact h⟩
  have hE : MeasurableSet {t : ℝ | 0 ≤ t ∧ M < lagRe (fun i => (c i : ℂ)) w t} := by
    rw [hset]
    exact measurableSet_Ici.inter
      (measurableSet_lt measurable_const (continuous_lagMax hsumC hB).measurable)
  exact re_nonpos_of_lag_le_except hc hcs hfin hB hE hκ hint (M := M)
    (fun t ht htE => not_lt.mp fun h => htE ⟨ht, h⟩) j

end

end RHTower.OneSidedConfiguration
