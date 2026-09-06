import GaloisForLFunctions.RHTower.WeilLagFunctionSingleBase
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The shadow law for single-base lag sequences

For an integer base `b ≥ 2` write `z_q = b^{ρ_q − ½}` for the node of a zero copy.  The lag
sequence `a_{b^m} = Σ_q w_q z_q^m` is the coefficient sequence of the node series
`Σ_q w_q/(1 − z_q t)`, which converges near `t = 0` and has a genuine pole at every `t = 1/z_q`
with residue of positive real part (aliased copies add, they never cancel).  If the sequence is
bounded, its generating function is analytic on the whole unit disc.  Following the segment from
`0` to the pole `1/z_{q₀}` of an off-line copy, the identity theorem transports the equality of the
two functions along a convex tube, provided the tube avoids the closure of the other poles; at
the endpoint the analytic function must vanish against the pole, forcing the aliased weight to be
zero, which is impossible.  Hence a bounded single-base sequence forces, for every off-line copy
`q₀`, that the other nodes accumulate somewhere on the segment from `0` to `1/z_{q₀}`: modulo
the lattice `2πi/log b`, zeros accumulate in the upward vertical shadow of every off-line zero.
-/

open Complex Filter Topology Metric Set

namespace RHTower

noncomputable section

/-- The node `z_q = b^{ρ_q − ½}` of a zero copy for the base `b`. -/
def baseNode (b : ℕ) (q : XiZeroCopy) : ℂ := Complex.exp (((q.1 : ℂ) - 1 / 2) * Real.log b)

theorem baseNode_ne_zero (b : ℕ) (q : XiZeroCopy) : baseNode b q ≠ 0 := Complex.exp_ne_zero _

theorem baseNode_pow (b : ℕ) (q : XiZeroCopy) (m : ℕ) :
    baseNode b q ^ m = Complex.exp ((((m : ℝ) * Real.log b : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) := by
  rw [baseNode, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_baseNode (b : ℕ) (q : XiZeroCopy) :
    ‖baseNode b q‖ = Real.exp (((q.1 : ℂ).re - 1 / 2) * Real.log b) := by
  rw [baseNode, Complex.norm_exp]
  congr 1
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re]
  norm_num

/-- The uniform node bound `b^{1/2}`. -/
def nodeBound (b : ℕ) : ℝ := Real.exp (Real.log b / 2)

theorem nodeBound_pos (b : ℕ) : 0 < nodeBound b := Real.exp_pos _

theorem norm_baseNode_le {b : ℕ} (hb : 1 ≤ b) (q : XiZeroCopy) : ‖baseNode b q‖ ≤ nodeBound b := by
  rw [norm_baseNode, nodeBound]
  apply Real.exp_le_exp.mpr
  have h1 := xiZeroCopy_re_lt_one q
  have hl : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb)
  nlinarith

theorem inv_nodeBound_le_norm_baseNode {b : ℕ} (hb : 1 ≤ b) (q : XiZeroCopy) :
    (nodeBound b)⁻¹ ≤ ‖baseNode b q‖ := by
  rw [norm_baseNode, nodeBound, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have h0 := xiZeroCopy_re_pos q
  have hl : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb)
  nlinarith

/-- Off the line to the right, the node has modulus greater than one. -/
theorem one_lt_norm_baseNode {b : ℕ} (hb : 2 ≤ b) {q : XiZeroCopy} (hq : 1 / 2 < (q.1 : ℂ).re) :
    1 < ‖baseNode b q‖ := by
  rw [norm_baseNode]
  apply Real.one_lt_exp_iff.mpr
  have hl : 0 < Real.log b := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  nlinarith

/-- `a_{b^m} = Σ_q w_q z_q^m`. -/
theorem integerLag_pow_eq_tsum_baseNode (b m : ℕ) :
    (integerLag (b ^ m) : ℂ) = ∑' q : XiZeroCopy, lagWeight q * baseNode b q ^ m := by
  have h1 : (integerLag (b ^ m) : ℂ) = weilLagFunction ((m : ℝ) * Real.log b) := by
    rw [integerLag_pow]
    exact (weilLagFunction_eq_ofReal _).symm
  rw [h1, weilLagFunction_eq_tsum_lagWeight]
  exact tsum_congr fun q => by rw [baseNode_pow]

/-- The lag generating function `Σ_m a_{b^m} t^m`. -/
def lagGen (b : ℕ) (t : ℂ) : ℂ := ∑' m : ℕ, (integerLag (b ^ m) : ℂ) * t ^ m

/-- A bounded lag sequence has a generating function analytic on the unit disc. -/
theorem differentiableOn_lagGen {b : ℕ} {M : ℝ} (hM : ∀ m : ℕ, |integerLag (b ^ m)| ≤ M) :
    DifferentiableOn ℂ (lagGen b) (ball (0 : ℂ) 1) := by
  intro t ht
  have ht' : ‖t‖ < 1 := by simpa using ht
  set r : ℝ := (‖t‖ + 1) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 ≤ r := by positivity
  have htr : t ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, hr]; linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' m : ℕ, (integerLag (b ^ m) : ℂ) * w ^ m)
      (ball (0 : ℂ) r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun m => M * r ^ m)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left M) (fun m => ?_) isOpen_ball
      (fun m w hw => ?_)
    · exact (differentiableOn_const _).mul (differentiableOn_pow m)
    · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have hw' : ‖w‖ < r := by simpa using hw
      exact mul_le_mul (hM m) (pow_le_pow_left₀ (norm_nonneg _) hw'.le m) (by positivity) hM0
  exact ((hdiff t htr).differentiableAt (isOpen_ball.mem_nhds htr)).differentiableWithinAt

/-- The node series `Σ_q w_q/(1 − z_q t)`. -/
def nodeSeries (b : ℕ) (t : ℂ) : ℂ := ∑' q : XiZeroCopy, lagWeight q * (1 - baseNode b q * t)⁻¹

/-- The termwise geometric bound. -/
theorem norm_lagWeight_mul_pow_le {b : ℕ} {t : ℂ}
    (hzt : ∀ q : XiZeroCopy, ‖baseNode b q * t‖ ≤ 1 / 2) (m : ℕ) (q : XiZeroCopy) :
    ‖lagWeight q * (baseNode b q * t) ^ m‖ ≤ (1 / 2 : ℝ) ^ m * ‖lagWeight q‖ := by
  rw [norm_mul, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hzt q) m) (norm_nonneg _)

/-- The product majorant is summable. -/
theorem summable_half_pow_mul_norm_lagWeight :
    Summable fun p : ℕ × XiZeroCopy => (1 / 2 : ℝ) ^ p.1 * ‖lagWeight p.2‖ := by
  have h1 : Summable fun m : ℕ => ‖(1 / 2 : ℝ) ^ m‖ := by
    simp only [norm_pow, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h2 : Summable fun q : XiZeroCopy => ‖‖lagWeight q‖‖ := by
    simpa using summable_norm_lagWeight
  exact summable_mul_of_summable_norm (f := fun m : ℕ => (1 / 2 : ℝ) ^ m)
    (g := fun q : XiZeroCopy => ‖lagWeight q‖) h1 h2

theorem summable_lagWeight_mul_pow_prod {b : ℕ} {t : ℂ}
    (hzt : ∀ q : XiZeroCopy, ‖baseNode b q * t‖ ≤ 1 / 2) :
    Summable (fun p : ℕ × XiZeroCopy => lagWeight p.2 * (baseNode b p.2 * t) ^ p.1) :=
  Summable.of_norm_bounded summable_half_pow_mul_norm_lagWeight
    fun p => norm_lagWeight_mul_pow_le hzt p.1 p.2

/-- Interchange of the double series `Σ_m Σ_q w_q (z_q t)^m`. -/
theorem tsum_tsum_lagWeight_mul_pow {b : ℕ} {t : ℂ}
    (hzt : ∀ q : XiZeroCopy, ‖baseNode b q * t‖ ≤ 1 / 2) :
    ∑' m : ℕ, ∑' q : XiZeroCopy, lagWeight q * (baseNode b q * t) ^ m
      = ∑' q : XiZeroCopy, ∑' m : ℕ, lagWeight q * (baseNode b q * t) ^ m := by
  have hsum := summable_lagWeight_mul_pow_prod hzt
  refine (Summable.tsum_comm'
    (f := fun (m : ℕ) (q : XiZeroCopy) => lagWeight q * (baseNode b q * t) ^ m)
    hsum (fun m => hsum.prod_factor m) fun q => ?_).symm
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)
    fun m => norm_lagWeight_mul_pow_le hzt m q

/-- Near the origin the generating function is the node series. -/
theorem lagGen_eq_nodeSeries {b : ℕ} (hb : 1 ≤ b) {t : ℂ} (ht : ‖t‖ * nodeBound b ≤ 1 / 2) :
    lagGen b t = nodeSeries b t := by
  have hzt : ∀ q : XiZeroCopy, ‖baseNode b q * t‖ ≤ 1 / 2 := fun q => by
    rw [norm_mul]
    calc ‖baseNode b q‖ * ‖t‖ ≤ nodeBound b * ‖t‖ :=
          mul_le_mul_of_nonneg_right (norm_baseNode_le hb q) (norm_nonneg _)
      _ = ‖t‖ * nodeBound b := mul_comm _ _
      _ ≤ 1 / 2 := ht
  have hL : lagGen b t = ∑' m : ℕ, ∑' q : XiZeroCopy, lagWeight q * (baseNode b q * t) ^ m := by
    unfold lagGen
    refine tsum_congr fun m => ?_
    rw [integerLag_pow_eq_tsum_baseNode, ← tsum_mul_right]
    refine tsum_congr fun q => ?_
    rw [mul_pow]; ring
  have hR : nodeSeries b t = ∑' q : XiZeroCopy, ∑' m : ℕ, lagWeight q * (baseNode b q * t) ^ m := by
    unfold nodeSeries
    refine tsum_congr fun q => ?_
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (lt_of_le_of_lt (hzt q) (by norm_num))]
  rw [hL, hR]
  exact tsum_tsum_lagWeight_mul_pow hzt

/-! ## Aliased weight, regular part, and the split -/

/-- The nodes aliased with `q₀`. -/
def aliasSet (b : ℕ) (q₀ : XiZeroCopy) : Set XiZeroCopy := {q | baseNode b q = baseNode b q₀}

/-- The aliased weight `Σ_{z_q = z_{q₀}} w_q`. -/
def aliasWeight (b : ℕ) (q₀ : XiZeroCopy) : ℂ := ∑' q : aliasSet b q₀, lagWeight q

theorem aliasWeight_re_pos (b : ℕ) (q₀ : XiZeroCopy) : 0 < (aliasWeight b q₀).re := by
  have hs : Summable fun q : aliasSet b q₀ => lagWeight q := summable_norm_lagWeight.of_norm.subtype _
  rw [aliasWeight, Complex.re_tsum hs]
  have hs' := summable_lagWeight_re_subtype (aliasSet b q₀)
  have hq₀ : q₀ ∈ aliasSet b q₀ := rfl
  exact lt_of_lt_of_le (lagWeight_re_pos q₀)
    (hs'.le_tsum ⟨q₀, hq₀⟩ fun r _ => (lagWeight_re_pos r).le)

/-- The regular part `Σ_{z_q ≠ z_{q₀}} w_q/(1 − z_q t)`. -/
def regularPart (b : ℕ) (q₀ : XiZeroCopy) (t : ℂ) : ℂ :=
  ∑' q : ↑(aliasSet b q₀)ᶜ, lagWeight q * (1 - baseNode b q * t)⁻¹

/-- Where all denominators are bounded away from zero, the node series splits. -/
theorem nodeSeries_split {b : ℕ} (q₀ : XiZeroCopy) {t : ℂ} {c : ℝ} (hc : 0 < c)
    (hall : ∀ q : XiZeroCopy, c ≤ ‖1 - baseNode b q * t‖) :
    nodeSeries b t = aliasWeight b q₀ * (1 - baseNode b q₀ * t)⁻¹ + regularPart b q₀ t := by
  have hsum : Summable fun q : XiZeroCopy => lagWeight q * (1 - baseNode b q * t)⁻¹ := by
    refine Summable.of_norm_bounded (g := fun q => ‖lagWeight q‖ / c)
      (summable_norm_lagWeight.div_const c) fun q => ?_
    rw [norm_mul, norm_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hc (hall q)) (norm_nonneg _)
  rw [nodeSeries, ← hsum.tsum_subtype_add_tsum_subtype_compl (aliasSet b q₀)]
  congr 1
  rw [aliasWeight, ← tsum_mul_right]
  exact tsum_congr fun q => by rw [show baseNode b q = baseNode b q₀ from q.2]

/-- The regular part is analytic where the non-aliased denominators are bounded below. -/
theorem differentiableOn_regularPart {b : ℕ} (q₀ : XiZeroCopy) {V : Set ℂ} (hV : IsOpen V) {c : ℝ}
    (hc : 0 < c) (hall : ∀ t ∈ V, ∀ q : ↑(aliasSet b q₀)ᶜ, c ≤ ‖1 - baseNode b q * t‖) :
    DifferentiableOn ℂ (regularPart b q₀) V := by
  unfold regularPart
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun q : ↑(aliasSet b q₀)ᶜ => ‖lagWeight q‖ / c)
    ((summable_norm_lagWeight.subtype _).div_const c) (fun q => ?_) hV (fun q t ht => ?_)
  · apply (differentiableOn_const _).mul
    apply DifferentiableOn.inv
    · exact (differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)
    · intro t ht
      have := hall t ht q
      intro h; rw [h, norm_zero] at this; linarith
  · rw [norm_mul, norm_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hc (hall t ht q)) (norm_nonneg _)

/-! ## The shadow law -/

/-- The poles of the non-aliased nodes. -/
def shadowPoles (b : ℕ) (q₀ : XiZeroCopy) : Set ℂ :=
  {t | ∃ q : XiZeroCopy, baseNode b q ≠ baseNode b q₀ ∧ t = (baseNode b q)⁻¹}

/-- **A clean shadow is incompatible with a bounded single-base sequence.**  If the segment from
`0` to the pole `1/z_{q₀}` of an off-line copy avoids the closure of the other poles, then
`a_{b^m}` is not bounded. -/
theorem not_bounded_of_clean_shadow {b : ℕ} (hb : 2 ≤ b) (q₀ : XiZeroCopy)
    (hq₀ : 1 / 2 < (q₀.1 : ℂ).re)
    (hclean : ∀ t ∈ segment ℝ (0 : ℂ) (baseNode b q₀)⁻¹, t ∉ closure (shadowPoles b q₀))
    {M : ℝ} (hM : ∀ m : ℕ, |integerLag (b ^ m)| ≤ M) : False := by
  have hb1 : 1 ≤ b := by omega
  set z₀ := baseNode b q₀ with hz₀
  set t₀ := z₀⁻¹ with ht₀
  have hz₀ne : z₀ ≠ 0 := baseNode_ne_zero b q₀
  have hz₀1 : 1 < ‖z₀‖ := one_lt_norm_baseNode hb hq₀
  have ht₀1 : ‖t₀‖ < 1 := by rw [ht₀, norm_inv]; exact inv_lt_one_of_one_lt₀ hz₀1
  set S := segment ℝ (0 : ℂ) t₀ with hS
  have hSc : IsCompact S := by
    rw [hS, segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hSconv : Convex ℝ S := convex_segment _ _
  have h0S : (0 : ℂ) ∈ S := left_mem_segment ℝ _ _
  have ht₀S : t₀ ∈ S := right_mem_segment ℝ _ _
  have hSball : ∀ s ∈ S, ‖s‖ ≤ ‖t₀‖ := fun s hs => by
    have := segment_subset_closedBall_left (0 : ℂ) t₀ hs
    simpa using this
  -- distance from the segment to the other poles
  obtain ⟨δ₂, hδ₂, hdist⟩ : ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ s ∈ S, ∀ p ∈ shadowPoles b q₀, δ₂ ≤ dist s p := by
    rcases (shadowPoles b q₀).eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun s _ p hp => by rw [hemp] at hp; exact absurd hp (Set.notMem_empty p)⟩
    · obtain ⟨s₀, hs₀, hmin⟩ :=
        hSc.exists_isMinOn ⟨0, h0S⟩ (continuous_infDist_pt (shadowPoles b q₀)).continuousOn
      refine ⟨infDist s₀ (shadowPoles b q₀), ?_, fun s hs p hp => ?_⟩
      · exact (infDist_pos_iff_notMem_closure hne).mp (hclean s₀ hs₀)
      · exact ((isMinOn_iff.mp hmin) s hs).trans (infDist_le_dist_of_mem hp)
  -- the convex tube around the segment
  set δ : ℝ := min (δ₂ / 2) ((1 - ‖t₀‖) / 2) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ₂' : δ ≤ δ₂ / 2 := min_le_left _ _
  have hδ1 : δ ≤ (1 - ‖t₀‖) / 2 := min_le_right _ _
  set V := thickening δ S with hV
  have hVopen : IsOpen V := isOpen_thickening
  have hVconv : Convex ℝ V := hSconv.thickening δ
  have hSV : S ⊆ V := self_subset_thickening hδpos S
  have hVball : V ⊆ ball (0 : ℂ) 1 := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := mem_thickening_iff.mp ht
    rw [mem_ball, dist_zero_right]
    have h1 := hSball s hs
    have h2 : dist t 0 ≤ dist t s + dist s 0 := dist_triangle _ _ _
    rw [dist_zero_right, dist_zero_right] at h2
    linarith
  -- denominators on the tube
  set c : ℝ := (nodeBound b)⁻¹ * (δ₂ / 2) with hc
  have hcpos : 0 < c := mul_pos (inv_pos.mpr (nodeBound_pos b)) (by linarith)
  have hden : ∀ t ∈ V, ∀ q : ↑(aliasSet b q₀)ᶜ, c ≤ ‖1 - baseNode b q * t‖ := by
    intro t ht q
    obtain ⟨s, hs, hts⟩ := mem_thickening_iff.mp ht
    have hq : baseNode b q ≠ z₀ := q.2
    have hp : (baseNode b q)⁻¹ ∈ shadowPoles b q₀ := ⟨q, hq, rfl⟩
    have h1 := hdist s hs _ hp
    have hzq := baseNode_ne_zero b q
    have e : 1 - baseNode b q * t = baseNode b q * ((baseNode b q)⁻¹ - t) := by
      field_simp
    rw [e, norm_mul]
    have h2 : δ₂ / 2 ≤ ‖(baseNode b q)⁻¹ - t‖ := by
      have h3 : dist s (baseNode b q)⁻¹ ≤ dist s t + dist t (baseNode b q)⁻¹ := dist_triangle _ _ _
      have h4 : dist t (baseNode b q)⁻¹ = ‖(baseNode b q)⁻¹ - t‖ := by
        rw [dist_comm, dist_eq_norm]
      have h5 : dist s t < δ := by rw [dist_comm]; exact hts
      linarith
    calc c = (nodeBound b)⁻¹ * (δ₂ / 2) := rfl
      _ ≤ ‖baseNode b q‖ * ‖(baseNode b q)⁻¹ - t‖ :=
          mul_le_mul (inv_nodeBound_le_norm_baseNode hb1 q) h2 (by positivity) (norm_nonneg _)
  -- analyticity of both sides on the tube
  have hG : AnalyticOnNhd ℂ (regularPart b q₀) V :=
    (differentiableOn_regularPart q₀ hVopen hcpos hden).analyticOnNhd hVopen
  have hP : AnalyticOnNhd ℂ (lagGen b) V :=
    ((differentiableOn_lagGen hM).mono hVball).analyticOnNhd hVopen
  have hlin : AnalyticOnNhd ℂ (fun t : ℂ => 1 - z₀ * t) V :=
    fun t _ => analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hH₁ : AnalyticOnNhd ℂ (fun t => lagGen b t * (1 - z₀ * t)) V := hP.mul hlin
  have hH₂ : AnalyticOnNhd ℂ
      (fun t => aliasWeight b q₀ + regularPart b q₀ t * (1 - z₀ * t)) V :=
    fun t ht => analyticAt_const.add ((hG t ht).mul (hlin t ht))
  -- agreement near the origin
  set r₀ : ℝ := (2 * nodeBound b)⁻¹ with hr₀
  have hr₀pos : 0 < r₀ := inv_pos.mpr (by have := nodeBound_pos b; linarith)
  have hagree : ∀ t ∈ ball (0 : ℂ) r₀,
      lagGen b t * (1 - z₀ * t) = aliasWeight b q₀ + regularPart b q₀ t * (1 - z₀ * t) := by
    intro t ht
    have ht' : ‖t‖ < r₀ := by simpa using ht
    have htn : ‖t‖ * nodeBound b ≤ 1 / 2 := by
      have h1 : ‖t‖ * nodeBound b ≤ r₀ * nodeBound b :=
        mul_le_mul_of_nonneg_right ht'.le (nodeBound_pos b).le
      have h2 : r₀ * nodeBound b = 1 / 2 := by
        have hn : nodeBound b ≠ 0 := (nodeBound_pos b).ne'
        rw [hr₀]; field_simp
      linarith
    have hall : ∀ q : XiZeroCopy, (1 / 2 : ℝ) ≤ ‖1 - baseNode b q * t‖ := by
      intro q
      have h1 : ‖baseNode b q * t‖ ≤ 1 / 2 := by
        rw [norm_mul]
        calc ‖baseNode b q‖ * ‖t‖ ≤ nodeBound b * ‖t‖ :=
              mul_le_mul_of_nonneg_right (norm_baseNode_le hb1 q) (norm_nonneg _)
          _ = ‖t‖ * nodeBound b := mul_comm _ _
          _ ≤ 1 / 2 := htn
      have := norm_sub_norm_le (1 : ℂ) (baseNode b q * t)
      rw [norm_one] at this
      linarith
    rw [lagGen_eq_nodeSeries hb1 htn, nodeSeries_split q₀ (by norm_num : (0:ℝ) < 1 / 2) hall,
      ← hz₀]
    have hne : 1 - z₀ * t ≠ 0 := by
      intro h; have := hall q₀; rw [← hz₀, h, norm_zero] at this; linarith
    rw [add_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one]
  have hev : (fun t => lagGen b t * (1 - z₀ * t))
      =ᶠ[𝓝 (0 : ℂ)] (fun t => aliasWeight b q₀ + regularPart b q₀ t * (1 - z₀ * t)) :=
    Filter.eventuallyEq_of_mem (ball_mem_nhds (0 : ℂ) hr₀pos) hagree
  have h0V : (0 : ℂ) ∈ V := hSV h0S
  have heq := hH₁.eqOn_of_preconnected_of_eventuallyEq hH₂ hVconv.isPreconnected h0V hev
  have ht₀V : t₀ ∈ V := hSV ht₀S
  have hval := heq ht₀V
  simp only at hval
  rw [ht₀, mul_inv_cancel₀ hz₀ne, sub_self, mul_zero, mul_zero, add_zero] at hval
  have hre := aliasWeight_re_pos b q₀
  rw [← hval, Complex.zero_re] at hre
  exact lt_irrefl _ hre

/-- **The shadow law.**  For a bounded single-base lag sequence, the poles of the non-aliased
nodes accumulate on the segment from `0` to the pole of every off-line copy: modulo the lattice
`2πi/log b`, zeros accumulate in the upward vertical shadow of every off-line zero. -/
theorem exists_segment_mem_closure_shadowPoles {b : ℕ} (hb : 2 ≤ b) {M : ℝ}
    (hM : ∀ m : ℕ, |integerLag (b ^ m)| ≤ M) (q₀ : XiZeroCopy) (hq₀ : 1 / 2 < (q₀.1 : ℂ).re) :
    ∃ t ∈ segment ℝ (0 : ℂ) (baseNode b q₀)⁻¹, t ∈ closure (shadowPoles b q₀) := by
  by_contra h
  push Not at h
  exact not_bounded_of_clean_shadow hb q₀ hq₀ h hM

/-- If every off-line copy has a clean shadow, a bounded single-base sequence gives RH. -/
theorem riemannHypothesis_of_forall_abs_le_of_clean_shadows {b : ℕ} (hb : 2 ≤ b) {M : ℝ}
    (hM : ∀ m : ℕ, |integerLag (b ^ m)| ≤ M)
    (hclean : ∀ q₀ : XiZeroCopy, 1 / 2 < (q₀.1 : ℂ).re →
      ∀ t ∈ segment ℝ (0 : ℂ) (baseNode b q₀)⁻¹, t ∉ closure (shadowPoles b q₀)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiZeroCopy_re_eq_half
  intro q
  by_contra hq
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · have hq' : 1 / 2 < ((xiZeroCopyReflectEquiv q).1 : ℂ).re := by
      rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re]; linarith
    exact not_bounded_of_clean_shadow hb _ hq' (hclean _ hq') hM
  · exact not_bounded_of_clean_shadow hb q hgt (hclean q hgt) hM

end

end RHTower
