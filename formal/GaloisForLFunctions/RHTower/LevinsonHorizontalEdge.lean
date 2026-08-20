import GaloisForLFunctions.RHTower.LevinsonRealTrace
import GaloisForLFunctions.HTGeometry.SegmentArgumentBound
import GaloisForLFunctions.HTGeometry.DistinctZerosLeDivisor

/-!
# The horizontal edges of a Levinson rectangle are `O(log T)`

The argument variation of `G = ζ + λζ'` across the segment `[1/2, 4]` at height `T` is at most `π`
times one more than the number of sign changes of `Re G(σ+iT)`.  Each such sign change is a real
zero of the analytic real trace, and Jensen's inequality bounds the number of those by `O(log T)`.
-/

open Complex Metric Set MeromorphicOn
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem levinsonGTrace_order_ne_top {lam T : ℝ} (hlam : |lam| ≤ 1) (hT : 6 ≤ T) {z : ℂ}
    (hz : z ∈ traceStrip) : analyticOrderAt (levinsonGTrace lam T) z ≠ ⊤ := by
  intro htop
  have hev : levinsonGTrace lam T =ᶠ[nhds z] 0 := analyticOrderAt_eq_top.mp htop
  have hzero := (analyticOnNhd_levinsonGTrace_strip (lam := lam) hT).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_traceStrip.isPreconnected) hz hev
  have h4 : (4 : ℂ) ∈ traceStrip := by
    simp [traceStrip]
  have hval := hzero h4
  have hge := norm_levinsonGTrace_center_ge (lam := lam) (T := T) hlam
  rw [show levinsonGTrace lam T 4 = 0 from hval, norm_zero] at hge
  norm_num at hge

theorem levinsonGTrace_real_zeros_finite {lam T : ℝ} (hlam : |lam| ≤ 1) (hT : 6 ≤ T) :
    {x : ℝ | (x : ℂ) ∈ closedBall (4 : ℂ) |(7 / 2 : ℝ)| ∧
      levinsonGTrace lam T (x : ℂ) = 0}.Finite := by
  have hKsub : closedBall (4 : ℂ) |(7 / 2 : ℝ)| ⊆ traceStrip :=
    closedBall_four_subset_traceStrip (by norm_num)
  have hK : AnalyticOnNhd ℂ (levinsonGTrace lam T) (closedBall (4 : ℂ) |(7 / 2 : ℝ)|) :=
    (analyticOnNhd_levinsonGTrace_strip hT).mono hKsub
  have hfin := (MeromorphicOn.divisor (levinsonGTrace lam T)
    (closedBall (4 : ℂ) |(7 / 2 : ℝ)|)).finiteSupport (isCompact_closedBall ..)
  have hcplx : {u : ℂ | u ∈ closedBall (4 : ℂ) |(7 / 2 : ℝ)| ∧
      levinsonGTrace lam T u = 0}.Finite := by
    refine hfin.subset ?_
    intro u hu
    rw [Function.mem_support]
    have h1 := one_le_divisor_of_zero hK hu.1 hu.2
      (levinsonGTrace_order_ne_top hlam hT (hKsub hu.1))
    omega
  refine Set.Finite.ofFinset (hcplx.toFinset.preimage (fun x : ℝ => (x : ℂ))
    (fun a _ b _ h => Complex.ofReal_inj.mp h)) ?_
  intro x
  rw [Finset.mem_preimage, Set.Finite.mem_toFinset]
  rfl

theorem continuous_horizEdge (c : ℂ) : Continuous fun x : ℝ => (x : ℂ) + c :=
  Complex.continuous_ofReal.add continuous_const

theorem continuous_vertLine (c : ℂ) : Continuous fun t : ℝ => c + (t : ℂ) * I :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

theorem continuous_levinsonG_horizEdge (lam c : ℂ)
    (hne : ∀ x : ℝ, ((x : ℂ) + c) ≠ 1) :
    Continuous fun x : ℝ => levinsonG lam ((x : ℂ) + c) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hc : ContinuousAt ((levinsonG lam) ∘ (fun v : ℝ => (v : ℂ) + c)) x :=
    ContinuousAt.comp (analyticAt_levinsonG lam (hne x)).continuousAt
      (continuous_horizEdge c).continuousAt
  simpa [Function.comp_def] using hc

theorem continuous_deriv_levinsonG_horizEdge (lam c : ℂ)
    (hne : ∀ x : ℝ, ((x : ℂ) + c) ≠ 1) :
    Continuous fun x : ℝ => deriv (levinsonG lam) ((x : ℂ) + c) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hc : ContinuousAt ((deriv (levinsonG lam)) ∘ (fun v : ℝ => (v : ℂ) + c)) x :=
    ContinuousAt.comp ((analyticAt_levinsonG lam (hne x)).deriv).continuousAt
      (continuous_horizEdge c).continuousAt
  simpa [Function.comp_def] using hc

theorem continuous_levinsonG_vertLine (lam c : ℂ)
    (hne : ∀ t : ℝ, (c + (t : ℂ) * I) ≠ 1) :
    Continuous fun t : ℝ => levinsonG lam (c + (t : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hc : ContinuousAt ((levinsonG lam) ∘ (fun v : ℝ => c + (v : ℂ) * I)) t :=
    ContinuousAt.comp (analyticAt_levinsonG lam (hne t)).continuousAt
      (continuous_vertLine c).continuousAt
  simpa [Function.comp_def] using hc

theorem continuous_deriv_levinsonG_vertLine (lam c : ℂ)
    (hne : ∀ t : ℝ, (c + (t : ℂ) * I) ≠ 1) :
    Continuous fun t : ℝ => deriv (levinsonG lam) (c + (t : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hc : ContinuousAt ((deriv (levinsonG lam)) ∘ (fun v : ℝ => c + (v : ℂ) * I)) t :=
    ContinuousAt.comp ((analyticAt_levinsonG lam (hne t)).deriv).continuousAt
      (continuous_vertLine c).continuousAt
  simpa [Function.comp_def] using hc

theorem hasDerivAt_levinsonG_horiz (lam : ℂ) {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => levinsonG lam ((y : ℂ) + (T : ℂ) * I))
      (deriv (levinsonG lam) ((x : ℂ) + (T : ℂ) * I)) x := by
  have hne1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im] at him
    exact hT (by linarith)
  have hpath : HasDerivAt (fun y : ℝ => (y : ℂ) + (T : ℂ) * I) 1 x := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((T : ℂ) * I)
    simpa using h
  have h := ((analyticAt_levinsonG lam hne1).differentiableAt.hasDerivAt).comp x hpath
  exact h.congr_deriv (by ring)

/-- **The horizontal side of a Levinson rectangle is `O(log T)`.** -/
theorem exists_horizontal_levinsonG_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, |lam| ≤ 1 → ∀ T : ℝ, 6 ≤ T →
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) 4, levinsonG (lam : ℂ) ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in (1 / 2 : ℝ)..4,
          (logDeriv (levinsonG (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im| ≤ c * Real.log T := by
  classical
  obtain ⟨c₀, hc₀, hcount⟩ := exists_levinsonGTrace_count_bound
  refine ⟨(c₀ + 1) * Real.pi, by positivity, fun lam hlam T hT hne => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hTne : T ≠ 0 := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  set f : ℝ → ℂ := fun x => levinsonG (lam : ℂ) ((x : ℂ) + (T : ℂ) * I) with hfdef
  set f' : ℝ → ℂ := fun x => deriv (levinsonG (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I) with hf'def
  have hpathne : ∀ x : ℝ, ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im] at him
    exact hTne (by linarith)
  have hfc : Continuous f := continuous_levinsonG_horizEdge (lam : ℂ) _ hpathne
  have hf'c : Continuous f' := continuous_deriv_levinsonG_horizEdge (lam : ℂ) _ hpathne
  have hquot : ContinuousOn (fun x => f' x / f x) (Icc (1 / 2 : ℝ) 4) :=
    ContinuousOn.div hf'c.continuousOn hfc.continuousOn (fun x hx => hne x hx)
  set Z : Finset ℝ := (levinsonGTrace_real_zeros_finite hlam hT).toFinset with hZdef
  have hZmem : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 4, (f x).re = 0 → x ∈ Z := by
    intro x hx hzero
    rw [hZdef, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 2), Complex.dist_eq]
      have hval : ‖((x : ℂ) - 4)‖ = |x - 4| := by
        rw [show ((x : ℂ) - 4) = ((x - 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hval, abs_le]
      constructor <;> linarith [hx.1, hx.2]
    · rw [levinsonGTrace_ofReal]
      rw [hfdef] at hzero
      simp only at hzero
      rw [hzero]
      norm_num
  have hbound := abs_integral_im_logDeriv_le_of_finite_re_zeros
    (by norm_num : (1 / 2 : ℝ) ≤ 4) (f := f) (f' := f')
    (fun x _ => hasDerivAt_levinsonG_horiz (lam : ℂ) hTne x) hquot
    (fun x hx => hne x hx) Z hZmem
  have hcongr : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 4,
      (f' x / f x).im = (logDeriv (levinsonG (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im := by
    intro x _
    rw [hf'def, hfdef, logDeriv_apply]
  rw [intervalIntegral.integral_congr hcongr] at hbound
  refine le_trans hbound ?_
  have hcard : ((Z.filter (fun z => z ∈ Set.Ioo (1 / 2 : ℝ) 4)).card : ℝ) ≤ c₀ * Real.log T := by
    have hsub : (Z.filter (fun z => z ∈ Set.Ioo (1 / 2 : ℝ) 4)).card ≤ Z.card :=
      Finset.card_filter_le _ _
    have himg : (Z.image (fun x : ℝ => (x : ℂ))).card = Z.card :=
      Finset.card_image_of_injective _ (fun a b h => Complex.ofReal_inj.mp h)
    have hKsub : closedBall (4 : ℂ) |(7 / 2 : ℝ)| ⊆ traceStrip :=
      closedBall_four_subset_traceStrip (by norm_num)
    have hKana : AnalyticOnNhd ℂ (levinsonGTrace lam T) (closedBall (4 : ℂ) |(7 / 2 : ℝ)|) :=
      (analyticOnNhd_levinsonGTrace_strip hT).mono hKsub
    have hKord : ∀ z ∈ closedBall (4 : ℂ) |(7 / 2 : ℝ)|,
        analyticOrderAt (levinsonGTrace lam T) z ≠ ⊤ :=
      fun z hz => levinsonGTrace_order_ne_top hlam hT (hKsub hz)
    have hS : ∀ z ∈ Z.image (fun x : ℝ => (x : ℂ)),
        z ∈ closedBall (4 : ℂ) |(7 / 2 : ℝ)| ∧ levinsonGTrace lam T z = 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rw [hZdef, Set.Finite.mem_toFinset] at hx
      exact hx
    have hle := card_le_divisor_sum (isCompact_closedBall ..) hKana hKord _ hS
    rw [himg] at hle
    have hcnt := hcount lam hlam T hT
    have hcast : ((Z.card : ℤ) : ℝ) ≤ ((∑ᶠ u, MeromorphicOn.divisor (levinsonGTrace lam T)
        (closedBall (4 : ℂ) |(7 / 2 : ℝ)|) u : ℤ) : ℝ) := by exact_mod_cast hle
    have hsubcast : ((Z.filter (fun z => z ∈ Set.Ioo (1 / 2 : ℝ) 4)).card : ℝ)
        ≤ (Z.card : ℝ) := by exact_mod_cast hsub
    push_cast at hcast
    linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [hcard, hlog1, hπ]

end RHTower

end
