import Mathlib

/-!
# Locally finite exponential sums cannot vanish on a half-line

**Theorem** (`eq_zero_of_hasSum_cexp_eq_zero`). Let `w_i` be distinct points with `Re w_i ≤ B`, only
finitely many in each disc, and let `Σ ‖a_i‖ < ∞`. If `Σ_i a_i e^{s w_i} = 0` for every real
`s ≥ s₀`, then every `a_i` is zero.

**Proof.** Put `b_i = a_i e^{s₁ w_i}` with `s₁ = max(s₀, 0)` and `C(z) = Σ_i b_i/(z − w_i)`. For
`Re z > B`, `1/(z − w) = ∫_0^∞ e^{−(z − w)t} dt`, so `C(z) = ∫_0^∞ e^{−zt} Σ_i a_i e^{(s₁ + t)w_i} dt = 0`.
Local finiteness makes `C` holomorphic off the countable closed set `{w_i}`, whose complement is
connected, so `C ≡ 0` there by the identity theorem. Near `w_j` the series minus `b_j/(z − w_j)` is
bounded, so `b_j = 0`.
-/

open MeasureTheory Set Complex Metric Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.LocallyFiniteExponentialSumRigidity

variable {ι : Type*}

/-- Points of a locally finite family other than `z₀` keep a positive distance from `z₀`. -/
theorem exists_pos_le_dist {w : ι → ℂ} (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) (z₀ : ℂ) :
    ∃ δ > 0, ∀ i, w i ≠ z₀ → δ ≤ dist z₀ (w i) := by
  set F : Set ℂ := (w '' {i | ‖w i‖ ≤ ‖z₀‖ + 1}) \ {z₀} with hFdef
  have hF : F.Finite := ((hfin _).image w).sdiff
  have hz : z₀ ∉ F := fun h => h.2 rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hF.isClosed.isOpen_compl z₀ hz
  refine ⟨min δ 1, lt_min hδ one_pos, fun i hi => ?_⟩
  by_cases hR : ‖w i‖ ≤ ‖z₀‖ + 1
  · have hmem : w i ∈ F := ⟨⟨i, hR, rfl⟩, hi⟩
    have hnot : w i ∉ ball z₀ δ := fun h => hball h hmem
    rw [mem_ball, not_lt, dist_comm] at hnot
    exact (min_le_left _ _).trans hnot
  · push Not at hR
    have h1 : 1 ≤ dist z₀ (w i) := by
      rw [dist_comm, dist_eq_norm]
      have := norm_sub_norm_le (w i) z₀
      linarith
    exact (min_le_right _ _).trans h1

theorem isClosed_range {w : ι → ℂ} (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) :
    IsClosed (range w) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro z hz
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_dist hfin z
  refine ⟨δ, hδ, fun y hy hyr => ?_⟩
  obtain ⟨i, hi⟩ := hyr
  have hne : w i ≠ z := fun h => hz ⟨i, h⟩
  have h1 := hsep i hne
  rw [hi] at h1
  rw [mem_ball, dist_comm] at hy
  linarith

/-- The Cauchy series `Σ_i b_i/(z − w_i)`. -/
def cauchySeries (w : ι → ℂ) (b : ι → ℂ) (z : ℂ) : ℂ := ∑' i, b i / (z - w i)

theorem norm_div_sub_le {b z w : ℂ} {η : ℝ} (hη : 0 < η) (h : η ≤ ‖z - w‖) :
    ‖b / (z - w)‖ ≤ ‖b‖ / η := by
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hη h

theorem summable_cauchy {w : ι → ℂ} (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {b : ι → ℂ}
    (hb : Summable fun i => ‖b i‖) {z : ℂ} (hz : z ∉ range w) :
    Summable fun i => b i / (z - w i) := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_dist hfin z
  refine Summable.of_norm_bounded (hb.div_const δ) fun i => norm_div_sub_le hδ ?_
  have := hsep i fun h => hz ⟨i, h⟩
  rwa [dist_eq_norm] at this

theorem differentiableOn_cauchySeries {w : ι → ℂ} (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    {b : ι → ℂ} (hb : Summable fun i => ‖b i‖) :
    DifferentiableOn ℂ (cauchySeries w b) (range w)ᶜ := by
  intro z₀ hz₀
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_dist hfin z₀
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hfar : ∀ i, ∀ z ∈ ball z₀ (δ / 2), δ / 2 ≤ ‖z - w i‖ := by
    intro i z hz
    have h1 := hsep i fun h => hz₀ ⟨i, h⟩
    rw [mem_ball] at hz
    have h2 := dist_triangle z₀ z (w i)
    rw [dist_comm] at hz
    rw [← dist_eq_norm]
    linarith
  have hU : DifferentiableOn ℂ (cauchySeries w b) (ball z₀ (δ / 2)) := by
    refine differentiableOn_tsum_of_summable_norm (u := fun i => ‖b i‖ / (δ / 2)) (hb.div_const _)
      (fun i => ?_) isOpen_ball (fun i z hz => norm_div_sub_le hδ2 (hfar i z hz))
    refine DifferentiableOn.div (differentiableOn_const _) (differentiableOn_id.sub_const _)
      fun z hz h => ?_
    have := hfar i z hz
    rw [h, norm_zero] at this
    linarith
  exact (hU.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ2))).differentiableWithinAt

/-- For `Re z > B`, the Cauchy series of a configuration whose exponential sums vanish on `[0, ∞)`
vanishes. -/
theorem cauchySeries_eq_zero_of_hasSum {w : ι → ℂ} [Countable ι] {b : ι → ℂ} {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) (hb : Summable fun i => ‖b i‖)
    (hvan : ∀ t : ℝ, 0 ≤ t → HasSum (fun i => b i * cexp (t * w i)) 0) {z : ℂ} (hz : B < z.re) :
    cauchySeries w b z = 0 := by
  have hre : ∀ i, (-(z - w i)).re < 0 := fun i => by simp; linarith [hB i]
  have hterm : ∀ i, b i / (z - w i) = ∫ t in Ioi (0 : ℝ), b i * cexp (-(z - w i) * t) := by
    intro i
    have hne : z - w i ≠ 0 := fun h => by have := hre i; rw [h] at this; simp at this
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (hre i) 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
  have hint : ∀ i, Integrable (fun t : ℝ => b i * cexp (-(z - w i) * t)) (volume.restrict (Ioi 0)) :=
    fun i => (integrableOn_exp_mul_complex_Ioi (hre i) 0).const_mul _
  have hpos : ∀ i, 0 < z.re - (w i).re := fun i => by linarith [hB i]
  have hnorm : ∀ i, ∫ t in Ioi (0 : ℝ), ‖b i * cexp (-(z - w i) * t)‖ = ‖b i‖ / (z.re - (w i).re) := by
    intro i
    have hfun : (fun t : ℝ => ‖b i * cexp (-(z - w i) * t)‖) =
        fun t => ‖b i‖ * Real.exp (-(z.re - (w i).re) * t) := by
      funext t
      rw [norm_mul, Complex.norm_exp]
      congr 2
      simp
    rw [hfun, integral_const_mul, integral_exp_mul_Ioi (by linarith [hpos i]) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  have hsum : Summable fun i => ∫ t in Ioi (0 : ℝ), ‖b i * cexp (-(z - w i) * t)‖ := by
    simp_rw [hnorm]
    have hη : 0 < z.re - B := by linarith
    refine Summable.of_nonneg_of_le (fun i => div_nonneg (norm_nonneg _) (hpos i).le)
      (fun i => div_le_div_of_nonneg_left (norm_nonneg _) hη (by linarith [hB i])) (hb.div_const _)
  unfold cauchySeries
  simp_rw [hterm]
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  have hzero : ∀ t ∈ Ioi (0 : ℝ), ∑' i, b i * cexp (-(z - w i) * t) = 0 := by
    intro t ht
    have hfac : ∀ i, b i * cexp (-(z - w i) * t) = cexp (-z * t) * (b i * cexp (t * w i)) := by
      intro i
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; ring
    simp_rw [hfac]
    rw [tsum_mul_left, (hvan t (le_of_lt ht)).tsum_eq, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hzero, integral_zero]

/-- **Locally finite exponential sums cannot vanish on a half-line.** -/
theorem eq_zero_of_hasSum_cexp_eq_zero [Countable ι] {w : ι → ℂ} {a : ι → ℂ}
    (hinj : Function.Injective w) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) (ha : Summable fun i => ‖a i‖) {s₀ : ℝ}
    (hvan : ∀ s : ℝ, s₀ ≤ s → HasSum (fun i => a i * cexp (s * w i)) 0) (j : ι) : a j = 0 := by
  classical
  set s₁ := max s₀ 0 with hs₁
  have hs₁0 : 0 ≤ s₁ := le_max_right _ _
  set b : ι → ℂ := fun i => a i * cexp (s₁ * w i) with hbdef
  have hbn : ∀ i, ‖b i‖ ≤ ‖a i‖ * Real.exp (s₁ * B) := by
    intro i
    rw [hbdef, norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (↑s₁ * w i).re = s₁ * (w i).re := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (hB i) hs₁0
  have hb : Summable fun i => ‖b i‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbn (ha.mul_right _)
  have hvan' : ∀ t : ℝ, 0 ≤ t → HasSum (fun i => b i * cexp (t * w i)) 0 := by
    intro t ht
    have h := hvan (s₁ + t) (by linarith [le_max_left s₀ 0])
    convert h using 2 with i
    rw [hbdef, mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  -- the Cauchy series vanishes off the points
  have hopen : IsOpen (range w)ᶜ := (isClosed_range hfin).isOpen_compl
  have hC0 : ∀ z ∈ (range w)ᶜ, cauchySeries w b z = 0 := by
    have han := (differentiableOn_cauchySeries hfin hb).analyticOnNhd hopen
    have hconn : IsPreconnected (range w)ᶜ :=
      ((countable_range w).isPathConnected_compl_of_one_lt_rank
        (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
    set z₀ : ℂ := ((B + 1 : ℝ) : ℂ) with hz₀def
    have hz₀re : z₀.re = B + 1 := by simp [hz₀def]
    have hz₀ : z₀ ∈ (range w)ᶜ := by
      rintro ⟨i, hi⟩
      have := hB i
      rw [hi, hz₀re] at this
      linarith
    have hev : cauchySeries w b =ᶠ[𝓝 z₀] fun _ => 0 := by
      have hnhds : {z : ℂ | B < z.re} ∈ 𝓝 z₀ :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp [hz₀re])
      filter_upwards [hnhds] with z hz using cauchySeries_eq_zero_of_hasSum hB hb hvan' hz
    exact fun z hz => han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn hz₀ hev hz
  -- the residue at `w j`
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_dist hfin (w j)
  have hother : ∀ i, i ≠ j → δ ≤ dist (w j) (w i) := fun i hij =>
    hsep i fun h => hij (hinj h)
  set M := (∑' i, ‖b i‖) / (δ / 2) with hM
  have hbound : ∀ r : ℝ, 0 < r → r < δ / 2 → ‖b j‖ ≤ r * M := by
    intro r hr hrδ
    set z : ℂ := w j + r with hzdef
    have hzj : ‖z - w j‖ = r := by rw [hzdef, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
    have hfar : ∀ i, i ≠ j → δ / 2 ≤ ‖z - w i‖ := by
      intro i hij
      have h1 := hother i hij
      have h2 := dist_triangle (w j) z (w i)
      rw [dist_eq_norm (w j) z, norm_sub_rev, hzj, dist_eq_norm z (w i)] at h2
      linarith
    have hz : z ∉ range w := by
      rintro ⟨i, hi⟩
      by_cases hij : i = j
      · subst hij
        rw [← hi, sub_self, norm_zero] at hzj
        linarith
      · have := hfar i hij
        rw [hi, sub_self, norm_zero] at this
        linarith
    have hsumz := summable_cauchy hfin hb hz
    have hsplit := hsumz.tsum_eq_add_tsum_ite j
    have hC := hC0 z hz
    unfold cauchySeries at hC
    rw [hsplit] at hC
    set D := ∑' i, if i = j then (0 : ℂ) else b i / (z - w i) with hD
    have hDb : ‖D‖ ≤ M := by
      have hle : ∀ i, ‖if i = j then (0 : ℂ) else b i / (z - w i)‖ ≤ ‖b i‖ / (δ / 2) := by
        intro i
        split_ifs with hij
        · rw [norm_zero]; exact div_nonneg (norm_nonneg _) (half_pos hδ).le
        · exact norm_div_sub_le (half_pos hδ) (hfar i hij)
      calc ‖D‖ ≤ ∑' i, ‖b i‖ / (δ / 2) :=
            tsum_of_norm_bounded (hb.div_const _).hasSum hle
        _ = M := by rw [hM, tsum_div_const]
    have hzne : z - w j ≠ 0 := by
      intro h; rw [h, norm_zero] at hzj; linarith
    have hbj : b j = -(z - w j) * D := by
      field_simp at hC
      linear_combination hC
    rw [hbj, norm_mul, norm_neg, hzj]
    exact mul_le_mul_of_nonneg_left hDb hr.le
  have hbj0 : b j = 0 := by
    rw [← norm_eq_zero]
    refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
    set Mp := max M 1 with hMp
    have hMp0 : 0 < Mp := lt_of_lt_of_le one_pos (le_max_right _ _)
    set r := min (δ / 4) (ε / (2 * Mp)) with hr
    have hr0 : 0 < r := lt_min (by linarith) (by positivity)
    have hrδ : r < δ / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h := hbound r hr0 hrδ
    have h2 : r * M ≤ r * Mp := mul_le_mul_of_nonneg_left (le_max_left _ _) hr0.le
    have h3 : r * Mp ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_right (min_le_right (δ / 4) (ε / (2 * Mp))) hMp0.le
      rw [← hr] at this
      calc r * Mp ≤ ε / (2 * Mp) * Mp := this
        _ = ε / 2 := by field_simp
    linarith
  have hexp : cexp (s₁ * w j) ≠ 0 := Complex.exp_ne_zero _
  have : a j * cexp (s₁ * w j) = 0 := hbj0
  exact (mul_eq_zero.mp this).resolve_right hexp

end GaloisForLFunctions.HTGeometry.LocallyFiniteExponentialSumRigidity
