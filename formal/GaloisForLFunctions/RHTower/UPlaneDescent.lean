/-
The u-plane descent (MWM lane, Arc B — task #121).

The global FE-descent of ξ, built with the q62 lane's Painlevé/Morera reflection engine
(`Bottcher.SchwarzReflection` — CROSS-LANE IMPORT, mathlib-only dependencies, compiles
standalone): `xiDescent w := ξ(1/2 + √w)` with the principal square root is

* analytic off the slit `(−∞, 0]` (principal branch),
* continuous ACROSS the slit because the two one-sided limits differ by the reflection
  `v ↦ −v` and ξ is even about `1/2` (`xi_one_sub`),
* hence ENTIRE by `Bottcher.differentiableOn_of_off_horizontal_line` — Painlevé turns
  continuity across the real line into holomorphy, no limiting argument.

The descent identity `xi_eq_xiDescent : ξ(s) = xiDescent((s − 1/2)²)` holds globally
with NO branch bookkeeping: the two square roots of `(s−1/2)²` differ by the reflection
that evenness absorbs.

Capstone `rh_iff_xiDescent_ne_zero_slitPlane`: **RH ⟺ the descended function has no
zeros on the slit plane.** In the u-plane the critical line IS the slit (on-line zeros
are absorbed into the boundary), the FE involution is quotiented away, and the deck
charts' local `slitPlane` geometry becomes the GLOBAL domain — the ladder turns into a
native slit-plane root question.
-/
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.Bottcher.SchwarzReflection

namespace RHTower

open Complex Filter Topology Metric Set

/-! ### The principal square root -/

/-- The principal square root `exp((1/2)·log w)`. -/
noncomputable def uSqrt (w : ℂ) : ℂ := exp (((1 / 2 : ℝ) : ℂ) * log w)

theorem uSqrt_ne_zero (w : ℂ) : uSqrt w ≠ 0 := exp_ne_zero _

theorem uSqrt_sq {w : ℂ} (hw : w ≠ 0) : uSqrt w ^ (2 : ℕ) = w := by
  simp only [uSqrt]
  rw [← exp_nat_mul]
  have h : ((2 : ℕ) : ℂ) * (((1 / 2 : ℝ) : ℂ) * log w) = log w := by
    push_cast
    ring
  rw [h, exp_log hw]

theorem norm_uSqrt_of_ne_zero {w : ℂ} (hw : w ≠ 0) : ‖uSqrt w‖ = Real.sqrt ‖w‖ := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  simp only [uSqrt]
  rw [Complex.norm_exp, Complex.re_ofReal_mul, log_re,
    show (1 / 2 : ℝ) * Real.log ‖w‖ = Real.log ‖w‖ / 2 from by ring,
    ← Real.log_sqrt hpos.le, Real.exp_log (Real.sqrt_pos.mpr hpos)]

/-- The principal square root of a slit-plane point has positive real part. -/
theorem uSqrt_re_pos {w : ℂ} (hw : w ∈ slitPlane) : 0 < (uSqrt w).re := by
  simp only [uSqrt]
  rw [exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  rw [Complex.im_ofReal_mul, log_im, Set.mem_Ioo]
  have h1 : -Real.pi < arg w := neg_pi_lt_arg w
  have h2 : arg w < Real.pi :=
    lt_of_le_of_ne (arg_le_pi w) (slitPlane_arg_ne_pi hw)
  constructor
  · linarith
  · linarith

theorem uSqrt_analyticAt {w : ℂ} (hw : w ∈ slitPlane) : AnalyticAt ℂ uSqrt w := by
  have hconst : AnalyticAt ℂ (fun _ : ℂ => ((1 / 2 : ℝ) : ℂ)) w := analyticAt_const
  have hlog : AnalyticAt ℂ (fun z : ℂ => log z) w := analyticAt_id.clog hw
  show AnalyticAt ℂ (fun z : ℂ => exp (((1 / 2 : ℝ) : ℂ) * log z)) w
  exact (hconst.mul hlog).cexp

/-! ### The descended function -/

/-- The FE-descent of ξ to the u-plane: `xiDescent w = ξ(1/2 + √w)`, patched at `0`. -/
noncomputable def xiDescent (w : ℂ) : ℂ :=
  if w = 0 then xi (1 / 2 : ℂ) else xi ((1 / 2 : ℂ) + uSqrt w)

theorem xiDescent_zero : xiDescent 0 = xi (1 / 2 : ℂ) := by simp [xiDescent]

theorem xiDescent_of_ne_zero {w : ℂ} (hw : w ≠ 0) :
    xiDescent w = xi ((1 / 2 : ℂ) + uSqrt w) := by simp [xiDescent, hw]

/-- Evenness of ξ about the center, in the form the descent consumes. -/
theorem xi_half_sub (v : ℂ) : xi ((1 / 2 : ℂ) - v) = xi ((1 / 2 : ℂ) + v) := by
  rw [show (1 / 2 : ℂ) - v = 1 - ((1 / 2 : ℂ) + v) from by ring, xi_one_sub]

/-! ### Analyticity off the slit, continuity everywhere -/

theorem xiDescent_analyticAt {w : ℂ} (hw : w ∈ slitPlane) :
    AnalyticAt ℂ xiDescent w := by
  have hxi : AnalyticAt ℂ xi ((1 / 2 : ℂ) + uSqrt w) :=
    xi_analyticOnNhd_univ _ (Set.mem_univ _)
  have hinner : AnalyticAt ℂ (fun w' : ℂ => (1 / 2 : ℂ) + uSqrt w') w :=
    analyticAt_const.add (uSqrt_analyticAt hw)
  have han : AnalyticAt ℂ (fun w' => xi ((1 / 2 : ℂ) + uSqrt w')) w :=
    AnalyticAt.comp (f := fun w' : ℂ => (1 / 2 : ℂ) + uSqrt w') hxi hinner
  refine han.congr ?_
  filter_upwards [isOpen_slitPlane.mem_nhds hw] with w' hw'
  exact (xiDescent_of_ne_zero (slitPlane_ne_zero hw')).symm

theorem xiDescent_continuousAt_zero : ContinuousAt xiDescent 0 := by
  rw [← continuousWithinAt_compl_self]
  show Tendsto xiDescent (𝓝[≠] (0 : ℂ)) (𝓝 (xiDescent 0))
  rw [xiDescent_zero]
  have hnorm : Tendsto (fun w : ℂ => ‖w‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun w : ℂ => ‖w‖) (𝓝 (0 : ℂ)) (𝓝 0) := by
      simpa using continuous_norm.tendsto (0 : ℂ)
    exact h.mono_left nhdsWithin_le_nhds
  have hsqrt : Tendsto (fun w : ℂ => Real.sqrt ‖w‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    change Tendsto ((fun x : ℝ => Real.sqrt x) ∘ fun w : ℂ => ‖w‖)
      (𝓝[≠] (0 : ℂ)) (𝓝 0)
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hnorm
  have husq : Tendsto uSqrt (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine hsqrt.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (norm_uSqrt_of_ne_zero hw).symm
  have hmap : Tendsto (fun w : ℂ => (1 / 2 : ℂ) + uSqrt w) (𝓝[≠] (0 : ℂ))
      (𝓝 (1 / 2 : ℂ)) := by
    simpa using tendsto_const_nhds.add husq
  have hxi : Tendsto (fun w : ℂ => xi ((1 / 2 : ℂ) + uSqrt w)) (𝓝[≠] (0 : ℂ))
      (𝓝 (xi (1 / 2 : ℂ))) :=
    ((xi_analyticOnNhd_univ _ (Set.mem_univ _)).continuousAt.tendsto).comp hmap
  refine hxi.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (xiDescent_of_ne_zero hw).symm

theorem xiDescent_continuousAt_neg {w : ℂ} (hre : w.re < 0) (him : w.im = 0) :
    ContinuousAt xiDescent w := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hval : xiDescent w = xi ((1 / 2 : ℂ) + uSqrt w) := xiDescent_of_ne_zero hw0
  have hne : {z : ℂ | z ≠ 0} ∈ 𝓝 w := isOpen_compl_singleton.mem_nhds hw0
  rw [← continuousWithinAt_univ]
  rw [show (univ : Set ℂ) = {z : ℂ | 0 ≤ z.im} ∪ {z : ℂ | z.im < 0} by
    ext z
    simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
    by_cases h : 0 ≤ z.im
    · exact Or.inl h
    · exact Or.inr (not_le.mp h)]
  refine ContinuousWithinAt.union ?_ ?_
  · -- closed upper half: log is one-sidedly continuous here
    have hlogc : ContinuousWithinAt log {z : ℂ | 0 ≤ z.im} w :=
      continuousWithinAt_log_of_re_neg_of_im_zero hre him
    have h1 : ContinuousWithinAt (fun z : ℂ => ((1 / 2 : ℝ) : ℂ) * log z)
        {z : ℂ | 0 ≤ z.im} w := continuousWithinAt_const.mul hlogc
    have h2 : ContinuousWithinAt (fun z : ℂ => exp (((1 / 2 : ℝ) : ℂ) * log z))
        {z : ℂ | 0 ≤ z.im} w :=
      Complex.continuous_exp.continuousAt.comp_continuousWithinAt h1
    have h3 : ContinuousWithinAt
        (fun z : ℂ => (1 / 2 : ℂ) + exp (((1 / 2 : ℝ) : ℂ) * log z))
        {z : ℂ | 0 ≤ z.im} w := continuousWithinAt_const.add h2
    have h4 : ContinuousWithinAt
        (fun z : ℂ => xi ((1 / 2 : ℂ) + exp (((1 / 2 : ℝ) : ℂ) * log z)))
        {z : ℂ | 0 ≤ z.im} w :=
      ((xi_analyticOnNhd_univ _ (Set.mem_univ _)).continuousAt).comp_continuousWithinAt h3
    refine h4.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hne] with z hz
      rw [xiDescent_of_ne_zero hz]
      rfl
    · rw [hval]
      rfl
  · -- open lower half: log tends to the reflected branch value; evenness bridges
    have hlogt : Tendsto log (𝓝[{z : ℂ | z.im < 0}] w)
        (𝓝 (Real.log ‖w‖ - Real.pi * I)) :=
      tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him
    have h1 : Tendsto (fun z : ℂ => ((1 / 2 : ℝ) : ℂ) * log z)
        (𝓝[{z : ℂ | z.im < 0}] w)
        (𝓝 (((1 / 2 : ℝ) : ℂ) * (Real.log ‖w‖ - Real.pi * I))) :=
      hlogt.const_mul _
    have h2 : Tendsto (fun z : ℂ => exp (((1 / 2 : ℝ) : ℂ) * log z))
        (𝓝[{z : ℂ | z.im < 0}] w)
        (𝓝 (exp (((1 / 2 : ℝ) : ℂ) * (Real.log ‖w‖ - Real.pi * I)))) :=
      (Complex.continuous_exp.tendsto _).comp h1
    have h3 : Tendsto
        (fun z : ℂ => (1 / 2 : ℂ) + exp (((1 / 2 : ℝ) : ℂ) * log z))
        (𝓝[{z : ℂ | z.im < 0}] w)
        (𝓝 ((1 / 2 : ℂ) + exp (((1 / 2 : ℝ) : ℂ) * (Real.log ‖w‖ - Real.pi * I)))) :=
      tendsto_const_nhds.add h2
    have h4 : Tendsto
        (fun z : ℂ => xi ((1 / 2 : ℂ) + exp (((1 / 2 : ℝ) : ℂ) * log z)))
        (𝓝[{z : ℂ | z.im < 0}] w)
        (𝓝 (xi ((1 / 2 : ℂ) + exp (((1 / 2 : ℝ) : ℂ) * (Real.log ‖w‖ - Real.pi * I))))) :=
      ((xi_analyticOnNhd_univ _ (Set.mem_univ _)).continuousAt.tendsto).comp h3
    have hlogw : log w = (Real.log ‖w‖ : ℂ) + Real.pi * I := by
      have harg : arg w = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hre, him⟩
      rw [← re_add_im (log w), log_re, log_im, harg]
    have hexp : exp (((1 / 2 : ℝ) : ℂ) * (Real.log ‖w‖ - Real.pi * I)) = -uSqrt w := by
      have hsplit : ((1 / 2 : ℝ) : ℂ) * ((Real.log ‖w‖ : ℂ) - Real.pi * I)
          = ((1 / 2 : ℝ) : ℂ) * log w + -(Real.pi * I) := by
        rw [hlogw]
        push_cast
        ring
      simp only [uSqrt]
      rw [hsplit, exp_add, exp_neg, exp_pi_mul_I]
      norm_num
    have hvalue : xi ((1 / 2 : ℂ) + exp (((1 / 2 : ℝ) : ℂ) * (Real.log ‖w‖ - Real.pi * I)))
        = xiDescent w := by
      rw [hexp, show (1 / 2 : ℂ) + -uSqrt w = (1 / 2 : ℂ) - uSqrt w from by ring,
        xi_half_sub, hval]
    show Tendsto xiDescent (𝓝[{z : ℂ | z.im < 0}] w) (𝓝 (xiDescent w))
    rw [← hvalue]
    refine h4.congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hne] with z hz
    rw [xiDescent_of_ne_zero hz]
    rfl

theorem xiDescent_continuous : Continuous xiDescent := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases h0 : w = 0
  · rw [h0]
    exact xiDescent_continuousAt_zero
  by_cases hs : w ∈ slitPlane
  · exact (xiDescent_analyticAt hs).continuousAt
  · rw [Complex.mem_slitPlane_iff, not_or] at hs
    obtain ⟨h1, h2⟩ := hs
    rw [not_lt] at h1
    rw [ne_eq, not_not] at h2
    have hre : w.re < 0 := by
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact absurd (by apply Complex.ext <;> simp [← h, h2]) h0
    exact xiDescent_continuousAt_neg hre h2

/-! ### Painlevé: entire -/

/-- **The descent is entire** — continuity across the slit plus holomorphy off the real
line, upgraded by the q62 lane's Painlevé/Morera engine. -/
theorem xiDescent_differentiable : Differentiable ℂ xiDescent := by
  rw [← differentiableOn_univ]
  refine Bottcher.differentiableOn_of_off_horizontal_line (a := (0 : ℝ)) isOpen_univ
    xiDescent_continuous.continuousOn ?_
  intro w hw
  have hs : w ∈ slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hw.2)
  exact (xiDescent_analyticAt hs).differentiableAt.differentiableWithinAt

theorem xiDescent_analyticOnNhd_univ : AnalyticOnNhd ℂ xiDescent Set.univ :=
  xiDescent_differentiable.differentiableOn.analyticOnNhd isOpen_univ

/-! ### The descent identity and the capstone -/

/-- **The global descent identity**: `ξ(s) = xiDescent((s − 1/2)²)`, with no branch
bookkeeping — evenness absorbs the sign of the square root. -/
theorem xi_eq_xiDescent (s : ℂ) : xi s = xiDescent ((s - 1 / 2) ^ (2 : ℕ)) := by
  by_cases hv : s - 1 / 2 = 0
  · have hs : s = 1 / 2 := by
      have h := sub_eq_zero.mp hv
      simpa using h
    rw [hs, show ((1 / 2 : ℂ) - 1 / 2) ^ (2 : ℕ) = 0 from by ring, xiDescent_zero]
  · have hw : (s - 1 / 2) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hv
    rw [xiDescent_of_ne_zero hw]
    have hfac : (uSqrt ((s - 1 / 2) ^ (2 : ℕ)) - (s - 1 / 2)) *
        (uSqrt ((s - 1 / 2) ^ (2 : ℕ)) + (s - 1 / 2)) = 0 := by
      linear_combination uSqrt_sq hw
    rcases mul_eq_zero.mp hfac with h | h
    · rw [sub_eq_zero.mp h, show (1 / 2 : ℂ) + (s - 1 / 2) = s from by ring]
    · rw [eq_neg_of_add_eq_zero_left h,
        show (1 / 2 : ℂ) + -(s - 1 / 2) = (1 / 2 : ℂ) - (s - 1 / 2) from by ring,
        xi_half_sub, show (1 / 2 : ℂ) + (s - 1 / 2) = s from by ring]

/-- The square of a point with positive real part lies in the slit plane. -/
theorem sq_mem_slitPlane_of_re_pos {v : ℂ} (hv : 0 < v.re) : v ^ (2 : ℕ) ∈ slitPlane := by
  by_contra hns
  rw [Complex.mem_slitPlane_iff, not_or] at hns
  obtain ⟨h1, h2⟩ := hns
  rw [not_lt] at h1
  rw [ne_eq, not_not] at h2
  rw [sq, Complex.mul_im] at h2
  rw [sq, Complex.mul_re] at h1
  have hvim : v.im = 0 := by
    have h4 : v.re * v.im = 0 := by linarith
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h hv.ne'
    · exact h
  rw [hvim] at h1
  nlinarith

/-- **RH in the u-plane**: the Riemann Hypothesis is equivalent to the descended
function having no zeros on the slit plane. The critical line is the slit; the FE
involution is quotiented away; the deck calculus's local slit-chart geometry is now the
global domain. -/
theorem rh_iff_xiDescent_ne_zero_slitPlane :
    RiemannHypothesis ↔ ∀ w ∈ slitPlane, xiDescent w ≠ 0 := by
  rw [rh_iff_xi_ne_zero_right]
  have hcast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  constructor
  · intro hxi w hw
    rw [xiDescent_of_ne_zero (slitPlane_ne_zero hw)]
    refine hxi _ ?_
    rw [mem_rightHalf, Complex.add_re, hcast, Complex.ofReal_re]
    have hpos := uSqrt_re_pos hw
    linarith
  · intro hF s hs
    have hv : 0 < (s - 1 / 2).re := by
      rw [Complex.sub_re, hcast, Complex.ofReal_re]
      have h := mem_rightHalf.mp hs
      linarith
    rw [xi_eq_xiDescent s]
    exact hF _ (sq_mem_slitPlane_of_re_pos hv)

end RHTower

namespace RHTower

open Complex

/-- Right-half zeros of ξ are exactly slit-plane zeros of the u-plane descent.  This is
zero-set transport under the constraint map `w = (s - 1/2)^(2 : ℕ)`, not a new flow. -/
theorem exists_xi_zero_rightHalf_iff_exists_xiDescent_zero_slitPlane :
    (∃ s ∈ rightHalf, xi s = 0) ↔ ∃ w ∈ slitPlane, xiDescent w = 0 := by
  constructor
  · rintro ⟨s, hs, hs0⟩
    refine ⟨(s - 1 / 2) ^ (2 : ℕ), ?_, ?_⟩
    · refine sq_mem_slitPlane_of_re_pos ?_
      have hcast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
      rw [Complex.sub_re, hcast, Complex.ofReal_re]
      have h := mem_rightHalf.mp hs
      linarith
    · rw [← xi_eq_xiDescent s]
      exact hs0
  · rintro ⟨w, hw, hw0⟩
    refine ⟨(1 / 2 : ℂ) + uSqrt w, ?_, ?_⟩
    · have hcast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
      rw [mem_rightHalf, Complex.add_re, hcast, Complex.ofReal_re]
      have hpos := uSqrt_re_pos hw
      linarith
    · rw [← xiDescent_of_ne_zero (slitPlane_ne_zero hw)]
      exact hw0

end RHTower

namespace RHTower

open Complex Filter

/-- The u-plane square descent preserves local zero order away from the critical line.  On
`rightHalf`, the constraint map `s ↦ (s - 1/2)^(2 : ℕ)` has nonzero derivative, so the descended
zero at the slit-plane image has exactly the original ξ multiplicity. -/
theorem analyticOrderAt_xiDescent_center_sq {s : ℂ} (hs : s ∈ rightHalf) :
    analyticOrderAt xiDescent ((s - (1 / 2 : ℂ)) ^ (2 : ℕ)) = analyticOrderAt xi s := by
  let φ : ℂ → ℂ := fun z => (z - (1 / 2 : ℂ)) ^ (2 : ℕ)
  have hφ : AnalyticAt ℂ φ s := (analyticAt_id.sub analyticAt_const).pow 2
  have hsne : s - (1 / 2 : ℂ) ≠ 0 := by
    intro h
    have hs_eq : s = (1 / 2 : ℂ) := sub_eq_zero.mp h
    have hright := mem_rightHalf.mp hs
    rw [hs_eq] at hright
    norm_num at hright
  have hbase : HasDerivAt (fun z : ℂ => z - (1 / 2 : ℂ)) 1 s := by
    exact (hasDerivAt_id s).sub_const (1 / 2 : ℂ)
  have hderiv_at : HasDerivAt φ (2 * (s - (1 / 2 : ℂ))) s := by
    dsimp [φ]
    simpa using hbase.fun_pow 2
  have hφ' : deriv φ s ≠ 0 := by
    rw [hderiv_at.deriv]
    exact mul_ne_zero two_ne_zero hsne
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := xiDescent) hφ hφ'
  have hxi_ev : xi =ᶠ[nhds s] xiDescent ∘ φ := by
    filter_upwards with z
    exact xi_eq_xiDescent z
  rw [analyticOrderAt_congr hxi_ev]
  simpa [φ, Function.comp] using hcomp.symm

end RHTower

namespace RHTower

open Complex Filter

/-- Level `k` of the RH ladder is exactly divisibility of the descended divisor on the
slit plane.  The u-plane constraint transports both zeros and multiplicities, so the
right-half ladder can be read directly as a slit-plane divisor condition for `xiDescent`. -/
theorem rhLadder_iff_xiDescent_order_dvd_slitPlane (k : ℕ) :
    RHLadder k ↔
      ∀ w ∈ slitPlane, xiDescent w = 0 →
        ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xiDescent w := by
  constructor
  · intro hlad w hw hw0
    let s : ℂ := (1 / 2 : ℂ) + uSqrt w
    have hs : s ∈ rightHalf := by
      rw [mem_rightHalf, Complex.add_re]
      have hcast : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
      rw [hcast]
      have hpos := uSqrt_re_pos hw
      linarith
    have hxi0 : xi s = 0 := by
      rw [← xiDescent_of_ne_zero (slitPlane_ne_zero hw)]
      exact hw0
    have hord : analyticOrderAt xiDescent w = analyticOrderAt xi s := by
      have hsquare : (s - (1 / 2 : ℂ)) ^ (2 : ℕ) = w := by
        dsimp [s]
        rw [add_sub_cancel_left]
        exact uSqrt_sq (slitPlane_ne_zero hw)
      rw [← hsquare]
      exact analyticOrderAt_xiDescent_center_sq hs
    rw [hord]
    exact hlad s hs hxi0
  · intro hdiv ρ hρ hρ0
    have hw : (ρ - (1 / 2 : ℂ)) ^ (2 : ℕ) ∈ slitPlane := by
      refine sq_mem_slitPlane_of_re_pos ?_
      rw [Complex.sub_re]
      have hcast : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
      rw [hcast]
      linarith [mem_rightHalf.mp hρ]
    have hw0 : xiDescent ((ρ - (1 / 2 : ℂ)) ^ (2 : ℕ)) = 0 := by
      rw [← xi_eq_xiDescent ρ]
      exact hρ0
    have hord := analyticOrderAt_xiDescent_center_sq hρ
    rw [← hord]
    exact hdiv _ hw hw0

end RHTower
