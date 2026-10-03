import GaloisForLFunctions.RHTower.WeilProducerSoundararajanInequality

/-!
# Gap reflection for the Weil function of a Weil-positive system

Let `lam` be full-cone Weil-positive with boundary measure `μ_lam` and Herglotz function
`H(w) = ∫ (1/(w − ir) − ir/(1 + r²)) dμ_lam(r)`, so that `Φ_lam(s) = H(s − ½) + C_lam` on
`Re s > ½`.  The integral defining `H` makes sense for every `w`, and:

* **Reflection** (`herglotzFunction_neg_conj`, `weilContinuation_one_sub_conj`).  For every `w`,
  `H(−w̄) = −conj H(w)`.  Hence the extended Weil function satisfies
  `Φ_lam(1 − s̄) = −conj Φ_lam(s)` for every `s`, and `Re C_lam = 0`.
* **Gap continuation** (`hasDerivAt_herglotzFunction_of_gap`, `differentiableOn_herglotzFunction_gap`).
  If `μ_lam(a, b) = 0`, then `H` is holomorphic on the connected open set
  `{Re w ≠ 0} ∪ {Im w ∈ (a, b)}`.  So the Weil function continues analytically from `Re s > ½`
  across the arc `½ + i(a, b)` of the critical line to `Re s < ½`, and the continuation is the
  reflected function `−conj Φ_lam(1 − s̄)`.

For `Λ`, this is the classical continuation of `ξ'/ξ` across the gaps between ordinates of zeros.
For a general producer, one gap in `supp μ_lam` already forces the log-derivative functional equation
on the whole complement of `½ + i supp μ_lam`.

**Proof.**  `herglotzKernel(−w̄, r) = −conj herglotzKernel(w, r)` termwise.  Near a point `w₀` with
`|w₀ − ir| ≥ d` for all `r ∉ (a, b)`, the kernel and its derivative are bounded by
`K(1 + r²)⁻¹` for `μ_lam`-almost every `r`.  This holds because `|w − ir| ≥ d/2` on a ball, and
`|w − ir| ≥ (|r| + 1)/2` for large `|r|`.  Dominated differentiation then applies.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real ComplexConjugate

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-! ### Reflection -/

theorem herglotzKernel_neg_conj (w : ℂ) (r : ℝ) :
    herglotzKernel (-conj w) r = -conj (herglotzKernel w r) := by
  unfold herglotzKernel
  have h1 : -(starRingEnd ℂ) w - I * (r : ℂ) = -(starRingEnd ℂ) (w - I * r) := by
    simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  have h2 : (starRingEnd ℂ) (I * r / (1 + (r : ℂ) ^ 2)) = -(I * r / (1 + (r : ℂ) ^ 2)) := by
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_add, map_one, map_pow]
    ring
  rw [h1, map_sub (starRingEnd ℂ) (1 / (w - I * r)) (I * r / (1 + (r : ℂ) ^ 2)), h2,
    map_div₀, map_one]
  simp only [one_div, inv_neg]
  ring

/-- **Reflection of the Herglotz function.**  `H(−w̄) = −conj H(w)` for every `w`. -/
theorem herglotzFunction_neg_conj {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (w : ℂ) :
    herglotzFunction hW (-conj w) = -conj (herglotzFunction hW w) := by
  unfold herglotzFunction
  simp_rw [herglotzKernel_neg_conj]
  rw [integral_neg, integral_conj]

/-- **Reflection of the Weil function.**  `Φ_lam(1 − s̄) = −conj Φ_lam(s)` for every `s`. -/
theorem weilContinuation_one_sub_conj {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (s : ℂ) :
    weilContinuation hW (1 - conj s) = -conj (weilContinuation hW s) := by
  have hC := re_weilConst hW
  have hconjC : conj (weilConst hW) = -weilConst hW := by
    apply Complex.ext <;> simp [hC]
  have e : (1 - conj s) - 1 / 2 = -conj (s - 1 / 2) := by
    simp only [map_sub, map_div₀, map_one, map_ofNat]; ring
  have hdef : ∀ z, weilContinuation hW z = herglotzFunction hW (z - 1 / 2) + weilConst hW :=
    fun z => rfl
  rw [hdef, hdef, e, herglotzFunction_neg_conj, map_add, hconjC]
  ring

/-! ### Continuation across a gap -/

theorem norm_inv_sq_le_of_dist {w : ℂ} {r R d : ℝ} (hd : 0 < d) (hwR : ‖w‖ ≤ R)
    (hwd : d ≤ ‖w - I * r‖) :
    ‖1 / (w - I * r) ^ 2‖ ≤ (4 + (1 + (2 * R + 1) ^ 2) / d ^ 2) * (1 + r ^ 2)⁻¹ := by
  have hR : 0 ≤ R := (norm_nonneg w).trans hwR
  have hpos : 0 < ‖w - I * r‖ := lt_of_lt_of_le hd hwd
  have hq : 0 < 1 + r ^ 2 := by positivity
  rw [norm_div, norm_one, norm_pow, div_le_iff₀ (by positivity)]
  have hlow : |r| - R ≤ ‖w - I * r‖ := by
    have h := norm_sub_norm_le (I * (r : ℂ)) w
    rw [norm_sub_rev, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs] at h
    linarith
  rcases le_or_gt (2 * R + 1) |r| with h | h
  · -- far: `|w − ir| ≥ (|r| + 1)/2`
    have h2 : (|r| + 1) / 2 ≤ ‖w - I * r‖ := by linarith
    have h3 : ((|r| + 1) / 2) ^ 2 ≤ ‖w - I * r‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have h4 : 1 + r ^ 2 ≤ (|r| + 1) ^ 2 := by nlinarith [sq_abs r, abs_nonneg r]
    have h5 : 0 ≤ (1 + (2 * R + 1) ^ 2) / d ^ 2 * (1 + r ^ 2)⁻¹ * ‖w - I * r‖ ^ 2 := by
      positivity
    have h6 : (1 + r ^ 2) / 4 ≤ ‖w - I * r‖ ^ 2 := by nlinarith
    have h7 : (1 + r ^ 2)⁻¹ * ((1 + r ^ 2) / 4) = 1 / 4 := by field_simp
    have h8 := mul_le_mul_of_nonneg_left h6 (inv_nonneg.mpr hq.le)
    nlinarith
  · -- near: `|w − ir| ≥ d`
    have h2 : d ^ 2 ≤ ‖w - I * r‖ ^ 2 := pow_le_pow_left₀ hd.le hwd 2
    have h3 : 1 + r ^ 2 ≤ 1 + (2 * R + 1) ^ 2 := by
      have : |r| ^ 2 ≤ (2 * R + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg r) h.le 2
      rw [sq_abs] at this; linarith
    have h4 : (1 + (2 * R + 1) ^ 2) / d ^ 2 * (1 + r ^ 2)⁻¹ * ‖w - I * r‖ ^ 2 ≥ 1 := by
      rw [ge_iff_le, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity),
        one_mul]
      have : (1 + r ^ 2)⁻¹ * (1 + r ^ 2) = 1 := inv_mul_cancel₀ hq.ne'
      have h5 : (1 + (2 * R + 1) ^ 2) * (1 + r ^ 2)⁻¹ ≥ 1 := by
        rw [ge_iff_le, ← div_eq_mul_inv, le_div_iff₀ hq, one_mul]; exact h3
      nlinarith
    have h5 : 0 ≤ 4 * (1 + r ^ 2)⁻¹ * ‖w - I * r‖ ^ 2 := by positivity
    nlinarith

theorem herglotzKernel_eq_of_ne {w : ℂ} {r : ℝ} (hw : w - I * r ≠ 0) :
    herglotzKernel w r = (1 - I * r * w) / ((w - I * r) * (1 + (r : ℂ) ^ 2)) := by
  unfold herglotzKernel
  have h2 := one_add_sq_ne_zero r
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_herglotzKernel_le_of_dist {w : ℂ} {r R d : ℝ} (hd : 0 < d) (hwR : ‖w‖ ≤ R)
    (hwd : d ≤ ‖w - I * r‖) :
    ‖herglotzKernel w r‖ ≤ (2 * (1 + R) + (1 + (2 * R + 1) * R) / d) * (1 + r ^ 2)⁻¹ := by
  have hR : 0 ≤ R := (norm_nonneg w).trans hwR
  have hpos : 0 < ‖w - I * r‖ := lt_of_lt_of_le hd hwd
  have hne : w - I * r ≠ 0 := norm_pos_iff.mp hpos
  rw [herglotzKernel_eq_of_ne hne, norm_div, norm_mul, norm_one_add_sq]
  have hnum : ‖1 - I * r * w‖ ≤ 1 + |r| * R := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    gcongr
  have hlow : |r| - R ≤ ‖w - I * r‖ := by
    have h := norm_sub_norm_le (I * (r : ℂ)) w
    rw [norm_sub_rev, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs] at h
    linarith
  have hq : 0 < 1 + r ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  have key : 1 + |r| * R ≤ (2 * (1 + R) + (1 + (2 * R + 1) * R) / d) * ‖w - I * r‖ := by
    rcases le_or_gt (2 * R + 1) |r| with h | h
    · have h2 : (|r| + 1) / 2 ≤ ‖w - I * r‖ := by linarith
      have h3 : 1 + |r| * R ≤ 2 * (1 + R) * ((|r| + 1) / 2) := by nlinarith [abs_nonneg r]
      have h4 : 0 ≤ (1 + (2 * R + 1) * R) / d * ‖w - I * r‖ := by positivity
      nlinarith
    · have h2 : 1 + |r| * R ≤ 1 + (2 * R + 1) * R := by nlinarith [abs_nonneg r]
      have h3 : (1 + (2 * R + 1) * R) / d * d ≤ (1 + (2 * R + 1) * R) / d * ‖w - I * r‖ :=
        mul_le_mul_of_nonneg_left hwd (by positivity)
      have h4 : (1 + (2 * R + 1) * R) / d * d = 1 + (2 * R + 1) * R := by field_simp
      have h5 : 0 ≤ 2 * (1 + R) * ‖w - I * r‖ := by positivity
      nlinarith
  calc ‖1 - I * r * w‖ ≤ 1 + |r| * R := hnum
    _ ≤ (2 * (1 + R) + (1 + (2 * R + 1) * R) / d) * ‖w - I * r‖ := key
    _ = (2 * (1 + R) + (1 + (2 * R + 1) * R) / d) * (1 + r ^ 2)⁻¹ *
          (‖w - I * r‖ * (1 + r ^ 2)) := by field_simp

/-- **Differentiability away from the support.**  If `μ_lam(a, b) = 0` and `|w₀ − ir| ≥ d > 0` for
every `r ∉ (a, b)`, then `H` has derivative `∫ −(w₀ − ir)⁻² dμ_lam` at `w₀`. -/
theorem hasDerivAt_herglotzFunction_of_gap {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {a b : ℝ}
    (hgap : boundaryMeasure hW (Ioo a b) = 0) {w₀ : ℂ} {d : ℝ} (hd : 0 < d)
    (hw₀ : ∀ r : ℝ, r ∉ Ioo a b → d ≤ ‖w₀ - I * r‖) :
    HasDerivAt (herglotzFunction hW)
      (∫ r, -(1 / (w₀ - I * r) ^ 2) ∂boundaryMeasure hW) w₀ := by
  set R : ℝ := ‖w₀‖ + d / 2 with hR
  have hae : ∀ᵐ r ∂boundaryMeasure hW, r ∉ Ioo a b :=
    measure_mono_null (fun r hr => by simpa using hr) hgap
  have hball : ∀ x ∈ ball w₀ (d / 2), ∀ r : ℝ, r ∉ Ioo a b →
      ‖x‖ ≤ R ∧ d / 2 ≤ ‖x - I * r‖ := by
    intro x hx r hr
    rw [mem_ball, dist_eq_norm] at hx
    constructor
    · have := norm_le_norm_add_norm_sub' x w₀
      have h2 : ‖x - w₀‖ = ‖w₀ - x‖ := norm_sub_rev _ _
      linarith
    · have h1 := hw₀ r hr
      have h2 : ‖w₀ - I * r‖ ≤ ‖x - I * r‖ + ‖w₀ - x‖ := by
        have := norm_sub_le (x - I * r) (x - w₀)
        rw [show x - I * r - (x - w₀) = w₀ - I * r by ring, norm_sub_rev x w₀] at this
        linarith
      rw [norm_sub_rev] at hx
      linarith
  set N₁ : ℝ := 2 * (1 + R) + (1 + (2 * R + 1) * R) / (d / 2) with hN₁
  set N₂ : ℝ := 4 + (1 + (2 * R + 1) ^ 2) / (d / 2) ^ 2 with hN₂
  have hd2 : 0 < d / 2 := by linarith
  have hint₀ : Integrable (herglotzKernel w₀) (boundaryMeasure hW) := by
    refine Integrable.mono' ((integrable_inv_one_add_sq hW).const_mul N₁)
      (measurable_herglotzKernel w₀).aestronglyMeasurable ?_
    filter_upwards [hae] with r hr
    obtain ⟨h1, h2⟩ := hball w₀ (mem_ball_self hd2) r hr
    exact norm_herglotzKernel_le_of_dist hd2 h1 h2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := boundaryMeasure hW)
    (F := fun x r => herglotzKernel x r) (x₀ := w₀) (s := ball w₀ (d / 2))
    (F' := fun x r => -(1 / (x - I * r) ^ 2)) (bound := fun r => N₂ * (1 + r ^ 2)⁻¹)
    (ball_mem_nhds w₀ hd2)
    (Eventually.of_forall fun x => (measurable_herglotzKernel x).aestronglyMeasurable)
    hint₀
    (by fun_prop : Measurable fun r : ℝ => -(1 / (w₀ - I * (r : ℂ)) ^ 2)).aestronglyMeasurable
    (by
      filter_upwards [hae] with r hr x hx
      obtain ⟨h1, h2⟩ := hball x hx r hr
      rw [norm_neg]
      exact norm_inv_sq_le_of_dist hd2 h1 h2)
    ((integrable_inv_one_add_sq hW).const_mul N₂)
    (by
      filter_upwards [hae] with r hr x hx
      obtain ⟨_, h2⟩ := hball x hx r hr
      have hne : x - I * r ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hd2 h2)
      have hdx : HasDerivAt (fun y : ℂ => y - I * (r : ℂ)) 1 x := (hasDerivAt_id x).sub_const _
      have hinv := (hdx.inv hne).sub_const (I * r / (1 + (r : ℂ) ^ 2))
      have e : (fun y => herglotzKernel y r) =
          fun y => (y - I * (r : ℂ))⁻¹ - I * r / (1 + (r : ℂ) ^ 2) := by
        funext y
        simp [herglotzKernel, one_div]
      rw [e, show -(1 / (x - I * (r : ℂ)) ^ 2) = -1 / (x - I * (r : ℂ)) ^ 2 by ring]
      exact hinv)
  exact key.2

/-- The domain `{Re w ≠ 0} ∪ {Im w ∈ (a, b)}`. -/
def gapDomain (a b : ℝ) : Set ℂ := {w : ℂ | w.re ≠ 0} ∪ {w : ℂ | w.im ∈ Ioo a b}

theorem isOpen_gapDomain (a b : ℝ) : IsOpen (gapDomain a b) :=
  (isOpen_ne_fun Complex.continuous_re continuous_const).union
    (isOpen_Ioo.preimage Complex.continuous_im)

/-- **Gap continuation.**  If `μ_lam(a, b) = 0`, the Herglotz function is holomorphic on
`{Re w ≠ 0} ∪ {Im w ∈ (a, b)}`. -/
theorem differentiableOn_herglotzFunction_gap {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {a b : ℝ} (hgap : boundaryMeasure hW (Ioo a b) = 0) :
    DifferentiableOn ℂ (herglotzFunction hW) (gapDomain a b) := by
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  rcases hw with hre | him
  · -- off the imaginary axis: distance `|Re w|`
    have hd : 0 < |w.re| := abs_pos.mpr hre
    refine (hasDerivAt_herglotzFunction_of_gap hW hgap hd fun r _ => ?_).differentiableAt
    have := Complex.abs_re_le_norm (w - I * r)
    simpa using this
  · -- inside the gap: distance to the ends
    rw [Set.mem_setOf_eq, mem_Ioo] at him
    set d : ℝ := min (w.im - a) (b - w.im) with hd
    have hd0 : 0 < d := lt_min (by linarith [him.1]) (by linarith [him.2])
    refine (hasDerivAt_herglotzFunction_of_gap hW hgap hd0 fun r hr => ?_).differentiableAt
    have him' := Complex.abs_im_le_norm (w - I * r)
    have himr : (w - I * (r : ℂ)).im = w.im - r := by simp
    rw [himr] at him'
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hr
    rcases hr with h | h
    · have : d ≤ w.im - a := min_le_left _ _
      have : w.im - a ≤ |w.im - r| := by rw [abs_of_nonneg (by linarith)]; linarith
      linarith
    · have : d ≤ b - w.im := min_le_right _ _
      have : b - w.im ≤ |w.im - r| := by rw [abs_of_nonpos (by linarith)]; linarith
      linarith

/-- **The Weil function continues across the gap.**  If `μ_lam(a, b) = 0`, then `Φ_lam` is
holomorphic on `½ + gapDomain a b`, a connected open set containing both half-planes
`Re s ≠ ½` and the arc `½ + i(a, b)`. -/
theorem differentiableOn_weilContinuation_gap {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {a b : ℝ} (hgap : boundaryMeasure hW (Ioo a b) = 0) :
    DifferentiableOn ℂ (weilContinuation hW) {s : ℂ | s - 1 / 2 ∈ gapDomain a b} := by
  intro s hs
  have h := (differentiableOn_herglotzFunction_gap hW hgap).differentiableAt
    ((isOpen_gapDomain a b).mem_nhds hs)
  have h2 : DifferentiableAt ℂ (fun z => herglotzFunction hW (z - 1 / 2) + weilConst hW) s :=
    (h.comp s ((differentiableAt_id).sub_const _)).add_const _
  exact h2.differentiableWithinAt

/-- **The log-derivative functional equation of a producer.**  For every `s`,
`A_lam(s) + conj A_lam(1 − s̄) = U(s) + conj U(1 − s̄)`; with a gap in `μ_lam` both sides are
holomorphic across the gap, so this is the functional equation of `−F_lam'/F_lam`. -/
theorem producerA_add_conj_one_sub_conj {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (s : ℂ) :
    producerA hW s + conj (producerA hW (1 - conj s)) = archU s + conj (archU (1 - conj s)) := by
  have hA : ∀ z, producerA hW z = archU z - weilContinuation hW z := fun z => by
    unfold producerA archU; ring
  rw [hA, hA, weilContinuation_one_sub_conj, map_sub, map_neg, Complex.conj_conj]
  ring

end RHTower.WeilSpectral

end
