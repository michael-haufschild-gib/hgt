import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The real analysis of a hyperbolic reflection flow

Two real traces with `u² − v² = 2K > 0` have reflection `r = v/u ∈ (−1,1)`. In the variable
`L = artanh r` the mass and drift of the trace pair are `cosh 2L` and `sinh 2L`.

A flow `L′ = q − s` whose drift `s` has the sign of `L` is restoring: `|L|` grows at most by the
total variation of `q`. An absolutely continuous function with `n′ ≤ g′ n` satisfies the integrating
factor bound `n(b) e^{−g(b)} ≤ n(a) e^{−g(a)}`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- Two real traces with positive energy difference have a reflection in `(−1,1)`, with mass and
drift as rational functions of the reflection. -/
theorem traceReflection_algebra {u v K : ℝ} (hK : 0 < K) (h : u ^ 2 - v ^ 2 = 2 * K) :
    u ≠ 0 ∧ v / u ∈ Ioo (-1 : ℝ) 1 ∧
      (u ^ 2 + v ^ 2) / (2 * K) = (1 + (v / u) ^ 2) / (1 - (v / u) ^ 2) ∧
      u * v / K = 2 * (v / u) / (1 - (v / u) ^ 2) ∧
      (u + v) ^ 2 / (2 * K) = (1 + v / u) / (1 - v / u) ∧
      (u - v) ^ 2 / (2 * K) = (1 - v / u) / (1 + v / u) := by
  have hu : u ≠ 0 := by
    rintro rfl
    nlinarith only [h, hK, sq_nonneg v]
  have hD : u ^ 2 - v ^ 2 ≠ 0 := by rw [h]; positivity
  have hm : u - v ≠ 0 := fun h0 => hD (by rw [sq_sub_sq, h0, mul_zero])
  have hp : u + v ≠ 0 := fun h0 => hD (by rw [sq_sub_sq, h0, zero_mul])
  have hK' : K = (u ^ 2 - v ^ 2) / 2 := by rw [h]; ring
  have h1 : 1 - (v / u) ^ 2 = (u ^ 2 - v ^ 2) / u ^ 2 := by field_simp
  have hmem : v / u ∈ Ioo (-1 : ℝ) 1 := by
    have hlt : (v / u) ^ 2 < 1 := by
      have hpos : 0 < (u ^ 2 - v ^ 2) / u ^ 2 := by
        rw [h]; positivity
      linarith only [h1, hpos]
    exact abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hlt)
  have h2 : 1 - v / u = (u - v) / u := by field_simp
  have h3 : 1 + v / u = (u + v) / u := by field_simp
  refine ⟨hu, hmem, ?_, ?_, ?_, ?_⟩
  · rw [h1, hK']
    field_simp
  · rw [h1, hK']
    field_simp
  · rw [h2, h3, hK']
    field_simp
    ring
  · rw [h2, h3, hK']
    field_simp
    ring

/-- The exponential of `2 artanh r` is the Möbius ratio of `r`. -/
theorem exp_two_mul_artanh {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    Real.exp (2 * Real.artanh r) = (1 + r) / (1 - r) := by
  have hpos : 0 ≤ (1 + r) / (1 - r) := div_nonneg (by linarith only [hr.1]) (by linarith only [hr.2])
  rw [show 2 * Real.artanh r = Real.artanh r + Real.artanh r by ring, Real.exp_add,
    Real.exp_artanh hr]
  exact Real.mul_self_sqrt hpos

/-- `cosh 2L` is the mass ratio of `r = tanh L`. -/
theorem cosh_two_mul_artanh {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    Real.cosh (2 * Real.artanh r) = (1 + r ^ 2) / (1 - r ^ 2) := by
  have h1 : 1 - r ≠ 0 := by linarith only [hr.2]
  have h2 : 1 + r ≠ 0 := by linarith only [hr.1]
  have h3 : 1 - r ^ 2 ≠ 0 := by
    rw [show 1 - r ^ 2 = (1 - r) * (1 + r) by ring]
    exact mul_ne_zero h1 h2
  rw [Real.cosh_eq, Real.exp_neg, exp_two_mul_artanh hr, inv_div]
  field_simp
  ring

/-- `sinh 2L` is the drift of `r = tanh L`. -/
theorem sinh_two_mul_artanh {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    Real.sinh (2 * Real.artanh r) = 2 * r / (1 - r ^ 2) := by
  have h1 : 1 - r ≠ 0 := by linarith only [hr.2]
  have h2 : 1 + r ≠ 0 := by linarith only [hr.1]
  have h3 : 1 - r ^ 2 ≠ 0 := by
    rw [show 1 - r ^ 2 = (1 - r) * (1 + r) by ring]
    exact mul_ne_zero h1 h2
  rw [Real.sinh_eq, Real.exp_neg, exp_two_mul_artanh hr, inv_div]
  field_simp
  ring

/-- The derivative of the hyperbolic tangent in the form used by the Riccati equation. -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have hf : Real.tanh = fun y => Real.sinh y / Real.cosh y :=
    funext Real.tanh_eq_sinh_div_cosh
  have h' : HasDerivAt Real.tanh ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) /
      Real.cosh x ^ 2) x := by
    rw [hf]
    exact h
  exact h'.congr_deriv (by rw [Real.tanh_eq_sinh_div_cosh]; field_simp)

/-- The derivative of `artanh` on `(−1,1)`. -/
theorem hasDerivAt_artanh {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - r ^ 2)) r := by
  have h1 : 1 - r ≠ 0 := by linarith only [hr.2]
  have h2 : 1 + r ≠ 0 := by linarith only [hr.1]
  have hd : HasDerivAt (fun y : ℝ => 1 / 2 * (Real.log (1 + y) - Real.log (1 - y)))
      (1 / 2 * (1 / (1 + r) - (-1) / (1 - r))) r := by
    have ha : HasDerivAt (fun y : ℝ => 1 + y) 1 r := (hasDerivAt_id r).const_add 1
    have hb : HasDerivAt (fun y : ℝ => 1 - y) (-1) r := (hasDerivAt_id r).const_sub 1
    exact ((ha.log h2).sub (hb.log h1)).const_mul _
  have he : (fun y : ℝ => 1 / 2 * (Real.log (1 + y) - Real.log (1 - y))) =ᶠ[𝓝 r] Real.artanh := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with y hy
    rw [Real.artanh_eq_half_log (Ioo_subset_Icc_self hy),
      Real.log_div (by linarith only [hy.1]) (by linarith only [hy.2])]
  have h3 : 1 - r ^ 2 ≠ 0 := by
    rw [show 1 - r ^ 2 = (1 - r) * (1 + r) by ring]
    exact mul_ne_zero h1 h2
  exact (hd.congr_of_eventuallyEq he.symm).congr_deriv (by field_simp; ring)

private theorem le_of_restoring {L q s : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hL : ContinuousOn L (Icc a b)) (hq : IntervalIntegrable q volume a b)
    (hs : IntervalIntegrable s volume a b)
    (heq : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → L y - L x = ∫ t in x..y, (q t - s t))
    (hpos : ∀ x ∈ Icc a b, 0 < L x → 0 ≤ s x) :
    L b ≤ |L a| + ∫ t in a..b, |q t| := by
  have hqa : 0 ≤ ∫ t in a..b, |q t| :=
    intervalIntegral.integral_nonneg hab fun _ _ => abs_nonneg _
  by_cases hb : L b ≤ 0
  · linarith only [hb, abs_nonneg (L a), hqa]
  push Not at hb
  -- The last point where `L` is nonpositive, or the left endpoint when there is none.
  obtain ⟨x₀, hx₀, hx₀L, hx₀pos⟩ : ∃ x₀ ∈ Icc a b, L x₀ ≤ |L a| ∧ ∀ x ∈ Ioc x₀ b, 0 < L x := by
    let A := Icc a b ∩ {x | L x ≤ 0}
    have hA : IsClosed (Icc a b ∩ L ⁻¹' Iic 0) := hL.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    by_cases hne : A.Nonempty
    · obtain ⟨x₀, hx₀, hg⟩ := (isCompact_Icc.of_isClosed_subset hA inter_subset_left).exists_isGreatest hne
      refine ⟨x₀, hx₀.1, (show L x₀ ≤ 0 from hx₀.2).trans (abs_nonneg _), fun x hx => ?_⟩
      by_contra hn
      have hmem : x ∈ A := ⟨⟨hx₀.1.1.trans hx.1.le, hx.2⟩, not_lt.mp hn⟩
      exact absurd (hg hmem) (not_le.mpr hx.1)
    · refine ⟨a, left_mem_Icc.mpr hab, le_abs_self _, fun x hx => ?_⟩
      by_contra hn
      exact hne ⟨x, ⟨hx.1.le, hx.2⟩, not_lt.mp hn⟩
  have hbmem : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hsub : uIcc x₀ b ⊆ uIcc a b := by
    rw [uIcc_of_le hx₀.2, uIcc_of_le hab]
    exact Icc_subset_Icc hx₀.1 le_rfl
  have hqs : IntervalIntegrable q volume x₀ b := hq.mono_set hsub
  have hss : IntervalIntegrable s volume x₀ b := hs.mono_set hsub
  have hdiff := heq x₀ hx₀ b hbmem hx₀.2
  rw [intervalIntegral.integral_sub hqs hss] at hdiff
  have hsnn : 0 ≤ ∫ t in x₀..b, s t := by
    rw [intervalIntegral.integral_of_le hx₀.2]
    exact setIntegral_nonneg measurableSet_Ioc fun x hx =>
      hpos x ⟨hx₀.1.trans hx.1.le, hx.2⟩ (hx₀pos x hx)
  have hqle : ∫ t in x₀..b, q t ≤ ∫ t in x₀..b, |q t| :=
    (le_abs_self _).trans (intervalIntegral.abs_integral_le_integral_abs hx₀.2)
  have hmono : ∫ t in x₀..b, |q t| ≤ ∫ t in a..b, |q t| :=
    intervalIntegral.integral_mono_interval hx₀.1 hx₀.2 le_rfl
      (Eventually.of_forall fun _ => abs_nonneg _) hq.abs
  linarith only [hdiff, hsnn, hqle, hmono, hx₀L]

/-- **The restoring bound.** If `L′ = q − s` in integrated form and the drift `s` has the sign of
`L`, then `|L|` grows at most by the total variation of `q`. -/
theorem abs_le_of_restoring {L q s : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hL : ContinuousOn L (Icc a b)) (hq : IntervalIntegrable q volume a b)
    (hs : IntervalIntegrable s volume a b)
    (heq : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → L y - L x = ∫ t in x..y, (q t - s t))
    (hpos : ∀ x ∈ Icc a b, 0 < L x → 0 ≤ s x) (hneg : ∀ x ∈ Icc a b, L x < 0 → s x ≤ 0) :
    |L b| ≤ |L a| + ∫ t in a..b, |q t| := by
  apply abs_le.mpr
  constructor
  · have h := le_of_restoring (L := fun x => -L x) (q := fun x => -q x) (s := fun x => -s x) hab
      hL.neg hq.neg hs.neg ?_ ?_
    · simp only [abs_neg] at h
      linarith only [h]
    · intro x hx y hy hxy
      have hc : (∫ t in x..y, (-q t - -s t)) = -∫ t in x..y, (q t - s t) := by
        rw [← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr fun t _ => by ring
      rw [hc, ← heq x hx y hy hxy]
      ring
    · intro x hx hLx
      have := hneg x hx (by linarith only [hLx])
      linarith only [this]
  · exact le_of_restoring hab hL hq hs heq hpos

/-- Composition of an absolutely continuous function with the exponential. -/
theorem absolutelyContinuousOnInterval_exp {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (f x)) a b := by
  obtain ⟨M, hM⟩ := hf.exists_bound
  obtain ⟨K, hK⟩ := ((Real.contDiff_exp (n := 1)).contDiffOn (s := Icc (-M) M)).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hmem : ∀ x ∈ uIcc a b, f x ∈ Icc (-M) M := fun x hx =>
    abs_le.mp (by simpa only [Real.norm_eq_abs] using hM x hx)
  have hKpos : 0 < (K : ℝ) + 1 := add_pos_of_nonneg_of_pos K.coe_nonneg zero_lt_one
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hf (ε / ((K : ℝ) + 1)) (div_pos hε hKpos)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  calc
    (∑ i ∈ Finset.range E.1, dist (Real.exp (f (E.2 i).1)) (Real.exp (f (E.2 i).2))) ≤
        (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi =>
        hK.dist_le_mul _ (hmem _ (hE.1 i hi).1) _ (hmem _ (hE.1 i hi).2)
    _ ≤ ((K : ℝ) + 1) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Finset.sum_nonneg fun _ _ => dist_nonneg)
    _ < ((K : ℝ) + 1) * (ε / ((K : ℝ) + 1)) := mul_lt_mul_of_pos_left (hb E hE hlen) hKpos
    _ = ε := by field_simp

/-- A function dominated in distance by an absolutely continuous function is absolutely
continuous. -/
theorem absolutelyContinuousOnInterval_of_dist_le {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {g : ℝ → ℂ} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ x y, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hg ε hε
  exact ⟨δ, hδ, fun E hE hlen =>
    (Finset.sum_le_sum fun i _ => h _ _).trans_lt (hb E hE hlen)⟩

/-- The squared norm of an absolutely continuous complex function is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_norm_sq {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => ‖f x‖ ^ 2) a b := by
  have hre : AbsolutelyContinuousOnInterval (fun x => (f x).re) a b :=
    absolutelyContinuousOnInterval_of_dist_le hf fun x y => by
      rw [Real.dist_eq, Complex.dist_eq, ← Complex.sub_re]
      exact Complex.abs_re_le_norm _
  have him : AbsolutelyContinuousOnInterval (fun x => (f x).im) a b :=
    absolutelyContinuousOnInterval_of_dist_le hf fun x y => by
      rw [Real.dist_eq, Complex.dist_eq, ← Complex.sub_im]
      exact Complex.abs_im_le_norm _
  have h := (hre.fun_mul hre).add (him.fun_mul him)
  have he : (fun x => ‖f x‖ ^ 2) =
      (fun x => (f x).re * (f x).re) + (fun x => (f x).im * (f x).im) := by
    funext x
    simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_apply]
  rw [he]
  exact h

/-- The derivative of a squared complex norm. -/
theorem hasDerivAt_norm_sq {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => ‖f t‖ ^ 2) (2 * ((starRingEnd ℂ) (f x) * f').re) x := by
  have hre : HasDerivAt (fun t => (f t).re) f'.re x := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have him : HasDerivAt (fun t => (f t).im) f'.im x := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf
  have h := (hre.mul hre).add (him.mul him)
  have he : (fun t => ‖f t‖ ^ 2) = (fun t => (f t).re) * (fun t => (f t).re) +
      (fun t => (f t).im) * (fun t => (f t).im) := by
    funext t
    simp only [Pi.add_apply, Pi.mul_apply, Complex.sq_norm, Complex.normSq_apply]
  rw [he]
  exact h.congr_deriv (by simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring)

/-- **The integrating factor bound.** An absolutely continuous function with `n′ ≤ g′ n` almost
everywhere satisfies `n(b) e^{−g(b)} ≤ n(a) e^{−g(a)}`. -/
theorem mul_exp_neg_le_of_ae_deriv_le {n g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hn : AbsolutelyContinuousOnInterval n a b) (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ᵐ x : ℝ, x ∈ Ioo a b → ∃ n' g' : ℝ, HasDerivAt n n' x ∧ HasDerivAt g g' x ∧
      n' ≤ g' * n x) :
    n b * Real.exp (-g b) ≤ n a * Real.exp (-g a) := by
  have hF := hn.fun_mul (absolutelyContinuousOnInterval_exp hg.neg)
  have hint := hF.integral_deriv_eq_sub
  have hnonpos : ∫ x in a..b, deriv (fun x => n x * Real.exp ((-g) x)) x ≤ 0 := by
    rw [intervalIntegral.integral_of_le hab]
    apply integral_nonpos_of_ae
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h, volume.ae_ne b] with x hx hxb hxI
    obtain ⟨n', g', hn', hg', hle⟩ := hx ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
    have hd := hn'.mul hg'.neg.exp
    have hdv : deriv (fun x => n x * Real.exp ((-g) x)) x =
        n' * Real.exp ((-g) x) + n x * (Real.exp ((-g) x) * -g') := hd.deriv
    change deriv (fun x => n x * Real.exp ((-g) x)) x ≤ 0
    rw [hdv]
    have hprod : Real.exp ((-g) x) * (n' - g' * n x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hle)
    nlinarith only [hprod]
  simp only [Pi.neg_apply] at hint hnonpos
  linarith only [hint, hnonpos]


/-! ### Scaling at a finite-order singularity -/

private theorem integral_one_div_sub {c l h : ℝ} (hl : 0 < l) (hlh : l ≤ h) :
    ∫ t in (c - h)..(c - l), 1 / (c - t) = Real.log (h / l) := by
  have h1 := intervalIntegral.integral_comp_sub_left (a := c - h) (b := c - l)
    (fun u : ℝ => 1 / u) c
  have h2 : c - (c - l) = l := by ring
  have h3 : c - (c - h) = h := by ring
  rw [h2, h3] at h1
  rw [h1, integral_one_div_of_pos hl (hl.trans_le hlh)]

/-- If `(c−x) f(x) → ℓ` as `x ↑ c`, then `f` integrates to `ℓ log(1/λ)` over each dyadic-type
block `[c−d, c−λd]` as `d ↓ 0`. -/
theorem tendsto_integral_block_of_mul_tendsto {f : ℝ → ℝ} {b c ℓ lam : ℝ} (hbc : b < c)
    (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hi : ∀ x ∈ Ico b c, ∀ y ∈ Ico b c, IntervalIntegrable f volume x y)
    (hf : Tendsto (fun x => (c - x) * f x) (𝓝[<] c) (𝓝 ℓ)) :
    Tendsto (fun d => ∫ t in (c - d)..(c - lam * d), f t) (𝓝[>] (0 : ℝ))
      (𝓝 (ℓ * Real.log (1 / lam))) := by
  have hlog : 0 < Real.log (1 / lam) := Real.log_pos ((one_lt_div hlam.1).mpr hlam.2)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (Real.log (1 / lam) + 1) := div_pos hε (by linarith only [hlog])
  have hev := (Metric.tendsto_nhds.mp hf) _ hε'
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hbc).mp hev
  have hd0 : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), 0 < d ∧ d < c - u := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (sub_pos.mpr (mem_Iio.mp hu))).filter_mono nhdsWithin_le_nhds]
      with d hd hdu using ⟨hd, hdu⟩
  have hub : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), d < c - b :=
    (eventually_lt_nhds (sub_pos.mpr hbc)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hd0, hub] with d hd hdb
  obtain ⟨hdpos, hdu⟩ := hd
  have hl : 0 < lam * d := mul_pos hlam.1 hdpos
  have hld : lam * d ≤ d := by nlinarith only [hlam.2, hdpos]
  have hmem {t : ℝ} (ht : t ∈ Icc (c - d) (c - lam * d)) : t ∈ Ioo u c ∧ t ∈ Ico b c :=
    ⟨⟨by linarith only [ht.1, hdu], by linarith only [ht.2, hl]⟩,
      by linarith only [ht.1, hdb], by linarith only [ht.2, hl]⟩
  have hab : c - d ≤ c - lam * d := by linarith only [hld]
  have hL : c - d ∈ Ico b c := ⟨by linarith only [hdb], by linarith only [hdpos]⟩
  have hR : c - lam * d ∈ Ico b c := ⟨by linarith only [hdb, hld], by linarith only [hl]⟩
  have hfi := hi _ hL _ hR
  have hkernel : ContinuousOn (fun t : ℝ => 1 / (c - t)) (uIcc (c - d) (c - lam * d)) := by
    rw [uIcc_of_le hab]
    refine continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun t ht => ?_
    have := ht.2
    exact (by linarith only [this, hl] : (0 : ℝ) < c - t).ne'
  have hki := hkernel.intervalIntegrable (μ := volume)
  have hval := integral_one_div_sub (c := c) hl hld
  have hratio : d / (lam * d) = 1 / lam := by field_simp
  rw [hratio] at hval
  have hsplit : (∫ t in (c - d)..(c - lam * d), f t) - ℓ * Real.log (1 / lam) =
      ∫ t in (c - d)..(c - lam * d), (f t - ℓ * (1 / (c - t))) := by
    rw [intervalIntegral.integral_sub hfi (hki.const_mul ℓ), intervalIntegral.integral_const_mul,
      hval]
  have hbound : ‖∫ t in (c - d)..(c - lam * d), (f t - ℓ * (1 / (c - t)))‖ ≤
      ∫ t in (c - d)..(c - lam * d), ε / (Real.log (1 / lam) + 1) * (1 / (c - t)) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · refine Eventually.of_forall fun t ht => ?_
      have ht' : t ∈ Icc (c - d) (c - lam * d) := ⟨ht.1.le, ht.2⟩
      obtain ⟨htu, -⟩ := hmem ht'
      have hpos : 0 < c - t := sub_pos.mpr htu.2
      have hd1 := hsub htu
      simp only [mem_setOf_eq, Real.dist_eq] at hd1
      have hrew : f t - ℓ * (1 / (c - t)) = ((c - t) * f t - ℓ) * (1 / (c - t)) := by
        field_simp
      rw [hrew, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hpos)]
      exact mul_le_mul_of_nonneg_right hd1.le (one_div_pos.mpr hpos).le
    · exact hki.const_mul _
  rw [intervalIntegral.integral_const_mul, hval] at hbound
  rw [Real.dist_eq, ← Real.norm_eq_abs, hsplit]
  refine hbound.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith only [hlog])]
  nlinarith only [hε, hlog]

/-- The scale law of a reflection at a finite-order singularity: if `(c−x)m(x) → γ/2` and
`r → σ = ±1`, then `(c−x)/(1−r²) → γ/4`, the mass and drift integrate on blocks to `(γ/2)log(1/λ)`
and `σ(γ/2)log(1/λ)`, and `artanh r` moves by `σ(1/2)log(1/λ)`. -/
theorem reflection_scaling {r : ℝ → ℝ} {b c γ σ lam : ℝ} (hbc : b < c) (hγ : 0 < γ)
    (hσ : σ ^ 2 = 1) (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hr : ∀ x ∈ Ico b c, r x ∈ Ioo (-1 : ℝ) 1)
    (hmi : ∀ x ∈ Ico b c, ∀ y ∈ Ico b c,
      IntervalIntegrable (fun t => (1 + r t ^ 2) / (1 - r t ^ 2)) volume x y)
    (hsi : ∀ x ∈ Ico b c, ∀ y ∈ Ico b c,
      IntervalIntegrable (fun t => 2 * r t / (1 - r t ^ 2)) volume x y)
    (hm : Tendsto (fun x => (c - x) * ((1 + r x ^ 2) / (1 - r x ^ 2))) (𝓝[<] c) (𝓝 (γ / 2)))
    (hlim : Tendsto r (𝓝[<] c) (𝓝 σ)) :
    Tendsto (fun x => (c - x) / (1 - r x ^ 2)) (𝓝[<] c) (𝓝 (γ / 4)) ∧
    Tendsto (fun d => ∫ t in (c - d)..(c - lam * d), (1 + r t ^ 2) / (1 - r t ^ 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (γ / 2 * Real.log (1 / lam))) ∧
    Tendsto (fun d => ∫ t in (c - d)..(c - lam * d), 2 * r t / (1 - r t ^ 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (σ * (γ / 2) * Real.log (1 / lam))) ∧
    Tendsto (fun d => Real.artanh (r (c - lam * d)) - Real.artanh (r (c - d))) (𝓝[>] (0 : ℝ))
      (𝓝 (σ * (1 / 2) * Real.log (1 / lam))) := by
  have hnear : ∀ᶠ x in 𝓝[<] c, x ∈ Ico b c := Ico_mem_nhdsLT hbc
  have hcx : Tendsto (fun x => c - x) (𝓝[<] c) (𝓝 0) := by
    have h : Tendsto (fun x => c - x) (𝓝 c) (𝓝 (c - c)) := tendsto_const_nhds.sub tendsto_id
    simpa only [sub_self] using h.mono_left nhdsWithin_le_nhds
  have hone : Tendsto (fun x => (c - x) / (1 - r x ^ 2)) (𝓝[<] c) (𝓝 (γ / 4)) := by
    have ht := (hm.add hcx).div_const 2
    have hv : (γ / 2 + 0) / 2 = γ / 4 := by ring
    rw [hv] at ht
    refine ht.congr' ?_
    filter_upwards [hnear] with x hx
    have hne : 1 - r x ^ 2 ≠ 0 := by
      have h := hr x hx
      nlinarith only [h.1, h.2]
    field_simp
    ring
  have hratio : Tendsto (fun x => 2 * r x / (1 + r x ^ 2)) (𝓝[<] c) (𝓝 σ) := by
    have hn := (hlim.const_mul 2).div (tendsto_const_nhds.add (hlim.pow 2))
      (by rw [hσ]; norm_num : (1 : ℝ) + σ ^ 2 ≠ 0)
    have hv : 2 * σ / (1 + σ ^ 2) = σ := by rw [hσ]; ring
    rw [hv] at hn
    exact hn
  have hdrift : Tendsto (fun x => (c - x) * (2 * r x / (1 - r x ^ 2))) (𝓝[<] c)
      (𝓝 (σ * (γ / 2))) := by
    have ht := hratio.mul hm
    refine ht.congr' ?_
    filter_upwards [hnear] with x hx
    have hne : 1 - r x ^ 2 ≠ 0 := by
      have h := hr x hx
      nlinarith only [h.1, h.2]
    have hne' : 1 + r x ^ 2 ≠ 0 := by positivity
    field_simp
  refine ⟨hone, tendsto_integral_block_of_mul_tendsto hbc hlam hmi hm,
    tendsto_integral_block_of_mul_tendsto hbc hlam hsi hdrift, ?_⟩
  -- The two arguments of the block approach `c` from the left.
  have hx₀ : Tendsto (fun d : ℝ => c - d) (𝓝[>] (0 : ℝ)) (𝓝[<] c) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun d : ℝ => c - d) (𝓝 0) (𝓝 (c - 0)) := tendsto_const_nhds.sub tendsto_id
      simpa only [sub_zero] using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with d hd
      exact sub_lt_self c hd
  have hx₁ : Tendsto (fun d : ℝ => c - lam * d) (𝓝[>] (0 : ℝ)) (𝓝[<] c) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun d : ℝ => c - lam * d) (𝓝 0) (𝓝 (c - lam * 0)) :=
        tendsto_const_nhds.sub (tendsto_id.const_mul lam)
      simpa only [mul_zero, sub_zero] using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with d hd
      exact sub_lt_self c (mul_pos hlam.1 hd)
  have hσne : σ ≠ 0 := by
    rintro rfl
    norm_num at hσ
  have hplus : Tendsto (fun x => 1 + σ * r x) (𝓝[<] c) (𝓝 2) := by
    have h := (hlim.const_mul σ).const_add 1
    have hv : 1 + σ * σ = 2 := by nlinarith only [hσ]
    rwa [hv] at h
  -- `(c−x)/(1−σ r)` has the limit `γ/2`.
  have hminus : Tendsto (fun x => (c - x) / (1 - σ * r x)) (𝓝[<] c) (𝓝 (γ / 2)) := by
    have ht := hplus.mul hone
    have hv : 2 * (γ / 4) = γ / 2 := by ring
    rw [hv] at ht
    refine ht.congr' ?_
    filter_upwards [hnear] with x hx
    have h := hr x hx
    have hsq : (σ * r x) ^ 2 = r x ^ 2 := by rw [mul_pow, hσ, one_mul]
    have hne : 1 - r x ^ 2 ≠ 0 := by nlinarith only [h.1, h.2]
    have hf : (1 - σ * r x) * (1 + σ * r x) = 1 - r x ^ 2 := by linear_combination -hsq
    have hne1 : 1 - σ * r x ≠ 0 := fun h0 => hne (by rw [← hf, h0, zero_mul])
    have hne2 : 1 + σ * r x ≠ 0 := fun h0 => hne (by rw [← hf, h0, mul_zero])
    rw [← hf]
    field_simp
  have hc0 := (hminus.comp hx₀)
  have hc1 := (hminus.comp hx₁)
  have hγ2 : γ / 2 ≠ 0 := by positivity
  -- The ratio of the two reflection defects tends to `λ`.
  have hdefect : Tendsto (fun d : ℝ => (1 - σ * r (c - lam * d)) / (1 - σ * r (c - d)))
      (𝓝[>] (0 : ℝ)) (𝓝 lam) := by
    have ht := (hc0.div hc1 hγ2).const_mul lam
    have hv : lam * ((γ / 2) / (γ / 2)) = lam := by rw [div_self hγ2, mul_one]
    rw [hv] at ht
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin, (hx₀.eventually hnear), (hx₁.eventually hnear)]
      with d hd h0 h1
    have hd' : 0 < d := hd
    have ha0 := hr _ h0
    have ha1 := hr _ h1
    have hnz (y : ℝ) (hy : r y ∈ Ioo (-1 : ℝ) 1) : 1 - σ * r y ≠ 0 := by
      have hsq : (σ * r y) ^ 2 = r y ^ 2 := by rw [mul_pow, hσ, one_mul]
      intro h0'
      have h' : σ * r y = 1 := by linarith only [h0']
      rw [h'] at hsq
      nlinarith only [hsq, hy.1, hy.2]
    have h1' := hnz _ ha0
    have h2' := hnz _ ha1
    have hd0 : d ≠ 0 := hd'.ne'
    have hl0 : lam ≠ 0 := hlam.1.ne'
    have e1 : c - (c - d) = d := by ring
    have e2 : c - (c - lam * d) = lam * d := by ring
    change lam * (((c - (c - d)) / (1 - σ * r (c - d))) /
      ((c - (c - lam * d)) / (1 - σ * r (c - lam * d)))) = _
    rw [e1, e2]
    field_simp
  have hplus0 := hplus.comp hx₀
  have hplus1 := hplus.comp hx₁
  have hlog : Tendsto (fun d : ℝ => σ * (1 / 2) *
      (Real.log ((1 + σ * r (c - lam * d)) / (1 + σ * r (c - d))) -
        Real.log ((1 - σ * r (c - lam * d)) / (1 - σ * r (c - d))))) (𝓝[>] (0 : ℝ))
      (𝓝 (σ * (1 / 2) * (Real.log (2 / 2) - Real.log lam))) := by
    refine ((Tendsto.log (hplus1.div hplus0 (by norm_num)) (by norm_num)).sub
      (hdefect.log hlam.1.ne')).const_mul _
  have hv : σ * (1 / 2) * (Real.log (2 / 2) - Real.log lam) = σ * (1 / 2) * Real.log (1 / lam) := by
    rw [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, Real.log_div one_ne_zero hlam.1.ne',
      Real.log_one]
  rw [hv] at hlog
  refine hlog.congr' ?_
  filter_upwards [hx₀.eventually hnear, hx₁.eventually hnear] with d h0 h1
  have ha0 := hr _ h0
  have ha1 := hr _ h1
  -- `artanh r = σ (1/2) log((1+σ r)/(1−σ r))`, on either sign of `σ`.
  have hart (y : ℝ) (hy : r y ∈ Ioo (-1 : ℝ) 1) : 0 < 1 + σ * r y ∧ 0 < 1 - σ * r y ∧
      Real.artanh (r y) = σ * (1 / 2) * (Real.log (1 + σ * r y) - Real.log (1 - σ * r y)) := by
    have hs : σ = 1 ∨ σ = -1 := by
      have : (σ - 1) * (σ + 1) = 0 := by linear_combination hσ
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (by linarith only [h])
      · exact Or.inr (by linarith only [h])
    have hbase : Real.artanh (r y) = 1 / 2 * (Real.log (1 + r y) - Real.log (1 - r y)) := by
      rw [Real.artanh_eq_half_log (Ioo_subset_Icc_self hy),
        Real.log_div (by linarith only [hy.1]) (by linarith only [hy.2])]
    rcases hs with rfl | rfl
    · refine ⟨by linarith only [hy.1], by linarith only [hy.2], ?_⟩
      rw [hbase]
      ring_nf
    · refine ⟨by linarith only [hy.2], by linarith only [hy.1], ?_⟩
      rw [hbase]
      ring_nf
  obtain ⟨p0, m0, e0⟩ := hart _ ha0
  obtain ⟨p1, m1, e1⟩ := hart _ ha1
  rw [e0, e1, Real.log_div p1.ne' p0.ne', Real.log_div m1.ne' m0.ne']
  ring

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
