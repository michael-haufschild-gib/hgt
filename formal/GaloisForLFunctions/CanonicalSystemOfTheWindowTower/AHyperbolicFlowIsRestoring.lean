import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.RCLike

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
    ring
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
  rw [hf]
  convert h using 1
  simp only
  field_simp

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
  convert hd.congr_of_eventuallyEq he.symm using 1
  field_simp
  ring

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
      have he := heq x hx y hy hxy
      have hsub : uIcc x y ⊆ uIcc a b := by
        rw [uIcc_of_le hxy, uIcc_of_le hab]
        exact Icc_subset_Icc hx.1 hy.2
      have hq' := hq.mono_set hsub
      have hs' := hs.mono_set hsub
      rw [intervalIntegral.integral_sub hq' hs'] at he
      rw [intervalIntegral.integral_sub hq'.neg hs'.neg, intervalIntegral.integral_neg,
        intervalIntegral.integral_neg]
      linarith only [he]
    · intro x hx hLx
      have := hneg x hx (by linarith only [hLx])
      linarith only [this]
  · exact le_of_restoring hab hL hq hs heq hpos

/-- Composition of an absolutely continuous function with the exponential. -/
theorem absolutelyContinuousOnInterval_exp {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (f x)) a b := by
  obtain ⟨M, hM⟩ := hf.exists_bound
  obtain ⟨K, hK⟩ := (Real.contDiff_exp.contDiffOn (s := Icc (-M) M)).exists_lipschitzOnWith
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
  convert h using 1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

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
    rw [show (fun x => n x * Real.exp ((-g) x)) = (fun x => n x) * (fun x => Real.exp (-g x)) by
      funext t; simp only [Pi.mul_apply, Pi.neg_apply]]
    rw [hd.deriv]
    have hprod : Real.exp (-g x) * (n' - g' * n x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hle)
    simp only [Pi.zero_apply]
    nlinarith only [hprod]
  simp only [Pi.neg_apply] at hint hnonpos
  linarith only [hint, hnonpos]

#print axioms traceReflection_algebra
#print axioms abs_le_of_restoring
#print axioms mul_exp_neg_le_of_ae_deriv_le

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
