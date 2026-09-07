import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.RHTower.XiWardEdgeReChannelDeposit
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Lorentzian product integral with complex shifts

For complex shifts `a, b` in the open strip `|Im| < 1`,

`∫_ℝ dt / ((1 + (t+a)²)(1 + (t+b)²)) = 2π / (4 + (a − b)²)`.

This is the pairing that turns Montgomery's Cauchy-kernel zero sum at height `t` into the
pair-correlation form over complex zeros (Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, Lemma 3).
The corpus owns the identity for real shifts (`integral_mul_lorentzianHalves`); both sides are
analytic in each shift on the strip, so the identity theorem extends it, first in `a` for real
`b`, then in `b`.  Analyticity of the integral is the Cauchy-dominated holomorphy theorem with the
explicit majorant `‖1 + (t+a)²‖ ≥ ((1 − |Im a|)²/4)(1 + (t + Re a)²)`.
-/

open Complex MeasureTheory Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The open unit strip `|Im a| < 1`. -/
def unitStrip : Set ℂ := {a : ℂ | |a.im| < 1}

theorem mem_unitStrip {a : ℂ} : a ∈ unitStrip ↔ |a.im| < 1 := Iff.rfl

theorem ofReal_mem_unitStrip (α : ℝ) : (α : ℂ) ∈ unitStrip := by
  simp [mem_unitStrip]

theorem isOpen_unitStrip : IsOpen unitStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem convex_unitStrip : Convex ℝ unitStrip := by
  intro a ha b hb x y hx hy hxy
  rw [mem_unitStrip] at ha hb ⊢
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  calc |x * a.im + y * b.im| ≤ |x * a.im| + |y * b.im| := abs_add_le _ _
    _ = x * |a.im| + y * |b.im| := by rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg hy]
    _ < x * 1 + y * 1 := by
        rcases eq_or_lt_of_le hx with hx0 | hx0
        · rw [← hx0] at hxy ⊢
          simp only [zero_mul, zero_add] at hxy ⊢
          rw [hxy, one_mul, one_mul]; exact hb
        · nlinarith
    _ = 1 := by linarith

theorem isPreconnected_unitStrip : IsPreconnected unitStrip := convex_unitStrip.isPreconnected

/-- The Lorentzian `1/(1 + (t+a)²)` with a complex shift `a`. -/
def lorentzShift (a : ℂ) (t : ℝ) : ℂ := 1 / (1 + ((t : ℂ) + a) ^ 2)

theorem one_add_sq_eq_mul (w : ℂ) : 1 + w ^ 2 = (w - I) * (w + I) := by
  ring_nf; rw [Complex.I_sq]; ring

/-- The explicit lower bound `‖1 + (t+a)²‖ ≥ ((1 − |Im a|)²/4)(1 + (t + Re a)²)`. -/
theorem norm_one_add_sq_ge {a : ℂ} (ha : a ∈ unitStrip) (t : ℝ) :
    ((1 - |a.im|) ^ 2 / 4) * (1 + (t + a.re) ^ 2) ≤ ‖1 + ((t : ℂ) + a) ^ 2‖ := by
  rw [mem_unitStrip] at ha
  obtain ⟨hal, hau⟩ := abs_lt.mp ha
  set η : ℝ := 1 - |a.im| with hη
  set u : ℝ := |t + a.re| with hu
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η ≤ 1 := by rw [hη]; linarith [abs_nonneg a.im]
  have hu0 : 0 ≤ u := abs_nonneg _
  rw [one_add_sq_eq_mul, norm_mul]
  have h1 : (η + u) / 2 ≤ ‖(t : ℂ) + a - I‖ := by
    have hi : |((t : ℂ) + a - I).im| ≤ ‖(t : ℂ) + a - I‖ := Complex.abs_im_le_norm _
    have hr : |((t : ℂ) + a - I).re| ≤ ‖(t : ℂ) + a - I‖ := Complex.abs_re_le_norm _
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add,
      Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.I_re, sub_zero] at hi hr
    have hi' : η ≤ |a.im - 1| := by
      have hab : |a.im - 1| = 1 - a.im := by
        rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      rw [hab, hη]
      linarith [le_abs_self a.im]
    linarith
  have h2 : (η + u) / 2 ≤ ‖(t : ℂ) + a + I‖ := by
    have hi : |((t : ℂ) + a + I).im| ≤ ‖(t : ℂ) + a + I‖ := Complex.abs_im_le_norm _
    have hr : |((t : ℂ) + a + I).re| ≤ ‖(t : ℂ) + a + I‖ := Complex.abs_re_le_norm _
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add,
      Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] at hi hr
    have hi' : η ≤ |a.im + 1| := by
      have hab : |a.im + 1| = a.im + 1 := abs_of_nonneg (by linarith)
      rw [hab, hη]
      linarith [neg_abs_le a.im]
    linarith
  have hprod : ((η + u) / 2) ^ 2 ≤ ‖(t : ℂ) + a - I‖ * ‖(t : ℂ) + a + I‖ := by
    calc ((η + u) / 2) ^ 2 = ((η + u) / 2) * ((η + u) / 2) := sq _
      _ ≤ _ := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
  refine le_trans ?_ hprod
  have hsq : η ^ 2 * (1 + u ^ 2) ≤ (η + u) ^ 2 := by
    have h1η : 0 ≤ 1 - η ^ 2 := by nlinarith
    nlinarith [mul_nonneg hη0.le hu0, mul_nonneg (sq_nonneg u) h1η]
  have hu2 : u ^ 2 = (t + a.re) ^ 2 := by rw [hu, sq_abs]
  rw [← hu2]
  nlinarith

theorem one_add_sq_ne_zero {a : ℂ} (ha : a ∈ unitStrip) (t : ℝ) : 1 + ((t : ℂ) + a) ^ 2 ≠ 0 := by
  intro h
  have := norm_one_add_sq_ge ha t
  rw [h, norm_zero] at this
  have hη : 0 < 1 - |a.im| := by rw [mem_unitStrip] at ha; linarith
  have : 0 < ((1 - |a.im|) ^ 2 / 4) * (1 + (t + a.re) ^ 2) := by positivity
  linarith

theorem norm_lorentzShift_le {a : ℂ} (ha : a ∈ unitStrip) (t : ℝ) :
    ‖lorentzShift a t‖ ≤ (4 / (1 - |a.im|) ^ 2) * (1 / (1 + (t + a.re) ^ 2)) := by
  unfold lorentzShift
  rw [norm_div, norm_one]
  have hη : 0 < 1 - |a.im| := by rw [mem_unitStrip] at ha; linarith
  have hlow := norm_one_add_sq_ge ha t
  have hpos : 0 < ((1 - |a.im|) ^ 2 / 4) * (1 + (t + a.re) ^ 2) := by positivity
  calc 1 / ‖1 + ((t : ℂ) + a) ^ 2‖ ≤ 1 / (((1 - |a.im|) ^ 2 / 4) * (1 + (t + a.re) ^ 2)) :=
        one_div_le_one_div_of_le hpos hlow
    _ = _ := by field_simp

theorem continuous_lorentzShift {a : ℂ} (ha : a ∈ unitStrip) : Continuous (lorentzShift a) := by
  unfold lorentzShift
  exact continuous_const.div (by fun_prop) (fun t => one_add_sq_ne_zero ha t)

theorem integrable_lorentzShift {a : ℂ} (ha : a ∈ unitStrip) : Integrable (lorentzShift a) := by
  have hη : 0 < 1 - |a.im| := by rw [mem_unitStrip] at ha; linarith
  refine ((integrable_inv_one_add_sq.comp_add_right a.re).const_mul (4 / (1 - |a.im|) ^ 2)).mono'
    (continuous_lorentzShift ha).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have := norm_lorentzShift_le ha t
  simpa [one_div] using this

/-- Local uniform bound on a small ball inside the strip. -/
theorem norm_lorentzShift_le_of_mem_ball {a₀ : ℂ} (ha₀ : a₀ ∈ unitStrip) {a : ℂ}
    (ha : a ∈ ball a₀ (min ((1 - |a₀.im|) / 2) (1 / 2))) (t : ℝ) :
    ‖lorentzShift a t‖ ≤ (64 / (1 - |a₀.im|) ^ 2) * (1 / (1 + (t + a₀.re) ^ 2)) := by
  rw [mem_unitStrip] at ha₀
  set η₀ : ℝ := (1 - |a₀.im|) / 2 with hη₀
  have hη₀0 : 0 < η₀ := by rw [hη₀]; linarith
  rw [mem_ball, dist_eq_norm] at ha
  have hlt1 : ‖a - a₀‖ < η₀ := lt_of_lt_of_le ha (min_le_left _ _)
  have hlt2 : ‖a - a₀‖ < 1 / 2 := lt_of_lt_of_le ha (min_le_right _ _)
  -- the imaginary part stays inside the strip with margin `η₀`
  have him : |a.im| ≤ |a₀.im| + ‖a - a₀‖ := by
    have := Complex.abs_im_le_norm (a - a₀)
    rw [Complex.sub_im] at this
    have := abs_sub_abs_le_abs_sub a.im a₀.im
    linarith
  have hηa : η₀ ≤ 1 - |a.im| := by linarith
  have ha' : a ∈ unitStrip := by rw [mem_unitStrip]; linarith
  -- the real part moves by less than `1/2`
  have hre : |(t + a.re) - (t + a₀.re)| < 1 / 2 := by
    have := Complex.abs_re_le_norm (a - a₀)
    rw [Complex.sub_re] at this
    rw [show (t + a.re) - (t + a₀.re) = a.re - a₀.re by ring]
    linarith
  have hden : (1 + (t + a₀.re) ^ 2) / 4 ≤ 1 + (t + a.re) ^ 2 := by
    rcases le_or_gt 1 |t + a₀.re| with h1 | h1
    · have h2 : |t + a₀.re| / 2 ≤ |t + a.re| := by
        have := abs_sub_abs_le_abs_sub (t + a₀.re) (t + a.re)
        rw [abs_sub_comm] at hre
        linarith
      have h3 := pow_le_pow_left₀ (by positivity) h2 2
      rw [div_pow, sq_abs, sq_abs] at h3
      nlinarith
    · have h2 : (t + a₀.re) ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (t + a₀.re)]
      nlinarith [sq_nonneg (t + a.re)]
  have hbound := norm_lorentzShift_le ha' t
  refine hbound.trans ?_
  have hA : 4 / (1 - |a.im|) ^ 2 ≤ 4 / η₀ ^ 2 := by
    gcongr
  have hB : 1 / (1 + (t + a.re) ^ 2) ≤ 4 / (1 + (t + a₀.re) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  calc (4 / (1 - |a.im|) ^ 2) * (1 / (1 + (t + a.re) ^ 2))
      ≤ (4 / η₀ ^ 2) * (4 / (1 + (t + a₀.re) ^ 2)) := by gcongr
    _ = (64 / (1 - |a₀.im|) ^ 2) * (1 / (1 + (t + a₀.re) ^ 2)) := by
        rw [hη₀]; field_simp; ring

theorem differentiableOn_lorentzShift (t : ℝ) :
    DifferentiableOn ℂ (fun a : ℂ => lorentzShift a t) unitStrip := by
  unfold lorentzShift
  exact (differentiableOn_const 1).div (by fun_prop) (fun a ha => one_add_sq_ne_zero ha t)

/-- The right-hand side `2π/(4 + (a−b)²)` is analytic in `a` on the strip. -/
theorem four_add_sq_ne_zero {a b : ℂ} (ha : a ∈ unitStrip) (hb : b ∈ unitStrip) :
    4 + (a - b) ^ 2 ≠ 0 := by
  intro h
  have hfac : 4 + (a - b) ^ 2 = ((a - b) - 2 * I) * ((a - b) + 2 * I) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [hfac] at h
  rw [mem_unitStrip] at ha hb
  obtain ⟨hal, hau⟩ := abs_lt.mp ha
  obtain ⟨hbl, hbu⟩ := abs_lt.mp hb
  rcases mul_eq_zero.mp h with h1 | h1
  · have := congrArg Complex.im h1
    simp at this
    linarith
  · have := congrArg Complex.im h1
    simp at this
    linarith

/-- **Identity theorem on the strip**: analytic functions agreeing on the real axis agree on the
strip. -/
theorem eqOn_unitStrip_of_forall_real {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F unitStrip)
    (hG : AnalyticOnNhd ℂ G unitStrip) (hreal : ∀ α : ℝ, F α = G α) : EqOn F G unitStrip := by
  refine hF.eqOn_of_preconnected_of_frequently_eq hG isPreconnected_unitStrip
    (ofReal_mem_unitStrip 0) ?_
  have hu : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] ((0 : ℝ) : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Filter.Eventually.of_forall fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_zero]
        exact_mod_cast (by positivity : (1 / ((n : ℝ) + 1)) ≠ 0)
  rw [Complex.ofReal_zero] at hu
  exact hu.frequently (Filter.Eventually.of_forall fun n => hreal _).frequently

/-! ## The real case, cast to `ℂ` -/

theorem lorentzProduct_real (α β : ℝ) :
    ∫ t : ℝ, lorentzShift (α : ℂ) t * lorentzShift (β : ℂ) t
      = 2 * (Real.pi : ℂ) / (4 + ((α : ℂ) - β) ^ 2) := by
  have h := integral_mul_lorentzianHalves (x := 1) one_pos α β
  have hcast : ∀ t : ℝ, lorentzShift (α : ℂ) t * lorentzShift (β : ℂ) t
      = (((1 / (1 ^ 2 + (t + α) ^ 2)) * (1 / (1 ^ 2 + (t + β) ^ 2)) : ℝ) : ℂ) := by
    intro t
    unfold lorentzShift
    push_cast
    ring
  simp_rw [hcast]
  rw [show (∫ t : ℝ, (((1 / (1 ^ 2 + (t + α) ^ 2)) * (1 / (1 ^ 2 + (t + β) ^ 2)) : ℝ) : ℂ))
      = ((∫ t : ℝ, (1 / (1 ^ 2 + (t + α) ^ 2)) * (1 / (1 ^ 2 + (t + β) ^ 2)) : ℝ) : ℂ) from by
    exact_mod_cast (integral_ofReal (𝕜 := ℂ)), h]
  push_cast
  ring

/-! ## Analyticity in each shift -/

theorem analyticOnNhd_rhs_left (b : ℂ) (hb : b ∈ unitStrip) :
    AnalyticOnNhd ℂ (fun a : ℂ => 2 * (Real.pi : ℂ) / (4 + (a - b) ^ 2)) unitStrip := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_unitStrip
  exact (differentiableOn_const _).div (by fun_prop) (fun a ha => four_add_sq_ne_zero ha hb)

theorem analyticOnNhd_rhs_right (a : ℂ) (ha : a ∈ unitStrip) :
    AnalyticOnNhd ℂ (fun b : ℂ => 2 * (Real.pi : ℂ) / (4 + (a - b) ^ 2)) unitStrip := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_unitStrip
  exact (differentiableOn_const _).div (by fun_prop) (fun b hb => four_add_sq_ne_zero ha hb)

/-- The ball of radius `min((1−|Im a₀|)/2, 1/2)` around a strip point stays in the strip. -/
theorem ball_subset_unitStrip {a₀ : ℂ} (ha₀ : a₀ ∈ unitStrip) :
    ball a₀ (min ((1 - |a₀.im|) / 2) (1 / 2)) ⊆ unitStrip := by
  intro a ha
  rw [mem_ball, dist_eq_norm] at ha
  have hlt : ‖a - a₀‖ < (1 - |a₀.im|) / 2 := lt_of_lt_of_le ha (min_le_left _ _)
  have h1 := Complex.abs_im_le_norm (a - a₀)
  rw [Complex.sub_im] at h1
  have h2 := abs_sub_abs_le_abs_sub a.im a₀.im
  rw [mem_unitStrip] at ha₀ ⊢
  linarith

theorem integrable_shiftedLorentzBound (C c : ℝ) :
    Integrable (fun t : ℝ => C * (1 / (1 + (t + c) ^ 2))) := by
  simpa [one_div] using (integrable_inv_one_add_sq.comp_add_right c).const_mul C

/-- Analyticity of the product integral in the first shift, the second shift fixed in the strip. -/
theorem analyticOnNhd_lorentzProduct_left {b : ℂ} (hb : b ∈ unitStrip) :
    AnalyticOnNhd ℂ (fun a : ℂ => ∫ t : ℝ, lorentzShift a t * lorentzShift b t) unitStrip := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_unitStrip
  intro a₀ ha₀
  have hη : 0 < (1 - |a₀.im|) / 2 := by rw [mem_unitStrip] at ha₀; linarith
  have hηb : 0 < 1 - |b.im| := by rw [mem_unitStrip] at hb; linarith
  have hr0 : 0 < min ((1 - |a₀.im|) / 2) (1 / 2) := lt_min hη one_half_pos
  have hball := ball_subset_unitStrip ha₀
  refine (differentiableAt_integral_of_cauchy_dominated
    (F := fun a t => lorentzShift a t * lorentzShift b t) (z₀ := a₀)
    (R := min ((1 - |a₀.im|) / 2) (1 / 2))
    (bound := fun t => (4 / (1 - |b.im|) ^ 2) *
      ((64 / (1 - |a₀.im|) ^ 2) * (1 / (1 + (t + a₀.re) ^ 2)))) hr0 ?_ ?_ ?_ ?_).differentiableWithinAt
  · intro a ha
    exact ((continuous_lorentzShift (hball ha)).mul
      (continuous_lorentzShift hb)).aestronglyMeasurable
  · intro t
    exact ((differentiableOn_lorentzShift t).mono hball).mul (differentiableOn_const _)
  · intro t a ha
    rw [norm_mul]
    have h1 := norm_lorentzShift_le_of_mem_ball ha₀ ha t
    have h2 : ‖lorentzShift b t‖ ≤ 4 / (1 - |b.im|) ^ 2 := by
      refine (norm_lorentzShift_le hb t).trans ?_
      have : 1 / (1 + (t + b.re) ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (t + b.re)]
      calc (4 / (1 - |b.im|) ^ 2) * (1 / (1 + (t + b.re) ^ 2)) ≤ (4 / (1 - |b.im|) ^ 2) * 1 := by
            gcongr
        _ = _ := mul_one _
    calc ‖lorentzShift a t‖ * ‖lorentzShift b t‖
        ≤ ((64 / (1 - |a₀.im|) ^ 2) * (1 / (1 + (t + a₀.re) ^ 2))) * (4 / (1 - |b.im|) ^ 2) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have := (integrable_shiftedLorentzBound (64 / (1 - |a₀.im|) ^ 2) a₀.re).const_mul
      (4 / (1 - |b.im|) ^ 2)
    exact this

/-- Analyticity in the second shift, the first fixed in the strip. -/
theorem analyticOnNhd_lorentzProduct_right {a : ℂ} (ha : a ∈ unitStrip) :
    AnalyticOnNhd ℂ (fun b : ℂ => ∫ t : ℝ, lorentzShift a t * lorentzShift b t) unitStrip := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_unitStrip
  intro b₀ hb₀
  have hη : 0 < (1 - |b₀.im|) / 2 := by rw [mem_unitStrip] at hb₀; linarith
  have hηa : 0 < 1 - |a.im| := by rw [mem_unitStrip] at ha; linarith
  have hr0 : 0 < min ((1 - |b₀.im|) / 2) (1 / 2) := lt_min hη one_half_pos
  have hball := ball_subset_unitStrip hb₀
  refine (differentiableAt_integral_of_cauchy_dominated
    (F := fun b t => lorentzShift a t * lorentzShift b t) (z₀ := b₀)
    (R := min ((1 - |b₀.im|) / 2) (1 / 2))
    (bound := fun t => (4 / (1 - |a.im|) ^ 2) *
      ((64 / (1 - |b₀.im|) ^ 2) * (1 / (1 + (t + b₀.re) ^ 2)))) hr0 ?_ ?_ ?_ ?_).differentiableWithinAt
  · intro b hb
    exact ((continuous_lorentzShift ha).mul
      (continuous_lorentzShift (hball hb))).aestronglyMeasurable
  · intro t
    exact (differentiableOn_const _).mul ((differentiableOn_lorentzShift t).mono hball)
  · intro t b hb
    rw [norm_mul]
    have h1 := norm_lorentzShift_le_of_mem_ball hb₀ hb t
    have h2 : ‖lorentzShift a t‖ ≤ 4 / (1 - |a.im|) ^ 2 := by
      refine (norm_lorentzShift_le ha t).trans ?_
      have : 1 / (1 + (t + a.re) ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (t + a.re)]
      calc (4 / (1 - |a.im|) ^ 2) * (1 / (1 + (t + a.re) ^ 2)) ≤ (4 / (1 - |a.im|) ^ 2) * 1 := by
            gcongr
        _ = _ := mul_one _
    exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
  · exact (integrable_shiftedLorentzBound (64 / (1 - |b₀.im|) ^ 2) b₀.re).const_mul
      (4 / (1 - |a.im|) ^ 2)

/-! ## The identity on the strip -/

theorem lorentzProduct_eq_of_real_right {a : ℂ} (ha : a ∈ unitStrip) (β : ℝ) :
    ∫ t : ℝ, lorentzShift a t * lorentzShift (β : ℂ) t
      = 2 * (Real.pi : ℂ) / (4 + (a - β) ^ 2) :=
  (eqOn_unitStrip_of_forall_real (analyticOnNhd_lorentzProduct_left (ofReal_mem_unitStrip β))
    (analyticOnNhd_rhs_left (β : ℂ) (ofReal_mem_unitStrip β))
    (fun α => lorentzProduct_real α β)) ha

/-- **The Lorentzian product integral with complex shifts.** -/
theorem lorentzProduct_eq {a b : ℂ} (ha : a ∈ unitStrip) (hb : b ∈ unitStrip) :
    ∫ t : ℝ, lorentzShift a t * lorentzShift b t = 2 * (Real.pi : ℂ) / (4 + (a - b) ^ 2) :=
  (eqOn_unitStrip_of_forall_real (analyticOnNhd_lorentzProduct_right ha)
    (analyticOnNhd_rhs_right a ha) (fun β => lorentzProduct_eq_of_real_right ha β)) hb

end

end RHTower
