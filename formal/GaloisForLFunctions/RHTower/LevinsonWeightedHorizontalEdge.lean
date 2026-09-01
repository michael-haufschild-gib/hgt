import GaloisForLFunctions.RHTower.LevinsonHorizontalEdge
import GaloisForLFunctions.RHTower.WeightedSegmentArgumentBound

/-!
# The weighted horizontal edge of the detector, down to an arbitrary left abscissa

Littlewood's weighted identity for the mollified detector runs its horizontal edges from the
Levinson abscissa `σ₀ = ½ − R/log T`, which is to the *left* of `½`.  The corpus's horizontal
estimate is the unweighted one on `[½,4]`, so two things must be added: the linear weight `x − σ₀`,
and a left endpoint below `½`.

Both are obtained from the same Backlund/Jensen mechanism.  Widening the counting disc from radius
`7/2` to radius `15/4` covers every left endpoint `c ≥ ¼`; the disc is still strictly inside the
sphere of radius `4` on which the crude strip bound holds, so the count remains `O(log T)`.  The
weight is then removed by one integration by parts.
-/

open Complex Metric Set MeromorphicOn MeasureTheory intervalIntegral
open GaloisForLFunctions.HTGeometry
open scoped Interval

noncomputable section

namespace RHTower

/-- Backlund's disc count for the detector, at an arbitrary radius below the sphere. -/
theorem exists_levinsonGTrace_count_bound_radius {r : ℝ} (hr0 : 0 < r) (hr4 : r < 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, |lam| ≤ 1 → ∀ T : ℝ, 6 ≤ T →
      ((∑ᶠ u, MeromorphicOn.divisor (levinsonGTrace lam T)
          (closedBall (4 : ℂ) |r|) u : ℤ) : ℝ) ≤ c * Real.log T := by
  obtain ⟨C, N, hC1, hC⟩ := exists_bound_norm_levinsonG_strip 8
  have hC0 : (0 : ℝ) < C := by linarith
  have hlogr : (0 : ℝ) < Real.log ((4 : ℝ) / r) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hr0]
    linarith
  set A : ℝ := |Real.log (C * 16 / 7)| + (N : ℝ) * Real.log 8 + (N : ℝ) with hA
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; positivity
  refine ⟨(A + 1) / Real.log ((4 : ℝ) / r), by positivity, ?_⟩
  intro lam hlam T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hlamC : ‖(lam : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  set M : ℝ := C * (4 * T) ^ N with hM
  have hMbase : (1 : ℝ) ≤ 4 * T := by linarith
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    have : (1 : ℝ) ≤ (4 * T) ^ N := one_le_pow₀ hMbase
    nlinarith
  have hsphere : ∀ z ∈ sphere (4 : ℂ) |(4 : ℝ)|, ‖levinsonGTrace lam T z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_iff_norm, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hz
    have hre : |z.re| ≤ 8 := by
      have h := Complex.abs_re_le_norm (z - 4)
      have hrz : (z - 4).re = z.re - 4 := by simp
      rw [hrz, hz] at h
      rw [abs_le] at h ⊢
      constructor <;> linarith [h.1, h.2]
    have him : |z.im| ≤ 4 := by
      have h := Complex.abs_im_le_norm (z - 4)
      have hiz : (z - 4).im = z.im := by simp
      rw [hiz, hz] at h
      exact h
    have hbound : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
        ‖levinsonG (lam : ℂ) (z + (ε : ℂ) * (T : ℂ) * I)‖ ≤ M := by
      intro ε hε
      have hre' : |(z + (ε : ℂ) * (T : ℂ) * I).re| ≤ 8 := by
        rcases hε with h1 | h1 <;> subst h1 <;> simpa using hre
      have himval : ∀ w : ℂ, w = z + ((1 : ℝ) : ℂ) * (T : ℂ) * I ∨
          w = z + ((-1 : ℝ) : ℂ) * (T : ℂ) * I → 2 ≤ |w.im| ∧ |w.im| ≤ T + 4 := by
        intro w hw
        rcases abs_le.mp him with ⟨hz1, hz2⟩
        rcases hw with h1 | h1 <;> subst h1 <;>
          · simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, Complex.I_re, Complex.I_im]
            constructor
            · rw [le_abs]
              first
                | (left; linarith)
                | (right; linarith)
            · rw [abs_le]
              constructor <;> linarith
      have hpair := himval (z + (ε : ℂ) * (T : ℂ) * I) (by
        rcases hε with h1 | h1 <;> subst h1
        · left; norm_num
        · right; norm_num)
      have hg := hC (lam : ℂ) hlamC _ hre' hpair.1
      refine le_trans hg ?_
      rw [hM]
      have hmono : (2 * |(z + (ε : ℂ) * (T : ℂ) * I).im|) ^ N ≤ (4 * T) ^ N := by
        refine pow_le_pow_left₀ (by positivity) ?_ N
        have := hpair.2
        linarith
      exact mul_le_mul_of_nonneg_left hmono hC0.le
    have h1 := hbound 1 (Or.inl rfl)
    have h2 := hbound (-1) (Or.inr rfl)
    have hval : levinsonGTrace lam T z
        = (levinsonG (lam : ℂ) (z + ((1 : ℝ) : ℂ) * (T : ℂ) * I)
          + levinsonG (lam : ℂ) (z + ((-1 : ℝ) : ℂ) * (T : ℂ) * I)) / 2 := by
      rw [levinsonGTrace]
      push_cast
      ring_nf
    rw [hval, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hsum : ‖levinsonG (lam : ℂ) (z + ((1 : ℝ) : ℂ) * (T : ℂ) * I)
        + levinsonG (lam : ℂ) (z + ((-1 : ℝ) : ℂ) * (T : ℂ) * I)‖ ≤ 2 * M := by
      refine le_trans (norm_add_le _ _) ?_
      linarith
    linarith [hsum]
  have hjensen := sum_divisor_le_of_bounds (c := (4 : ℂ)) (r := r) (R := (4 : ℝ))
    (M := M) (m := (7 / 16 : ℝ)) (f := levinsonGTrace lam T)
    (by rwa [abs_of_pos hr0])
    (by rw [abs_of_pos hr0, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; exact hr4)
    hM1 (by norm_num)
    (analyticOnNhd_levinsonGTrace hT) (norm_levinsonGTrace_center_ge hlam) hsphere
  refine le_trans hjensen ?_
  have hnum : Real.log (M / (7 / 16 : ℝ)) ≤ A * Real.log T := by
    have hMpos : (0 : ℝ) < M := by linarith
    have hsplit : Real.log (M / (7 / 16 : ℝ))
        = Real.log (C * 16 / 7) + (N : ℝ) * Real.log (4 * T) := by
      rw [hM, show C * (4 * T) ^ N / (7 / 16 : ℝ) = (C * 16 / 7) * (4 * T) ^ N by ring,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [hsplit]
    have hlog4T : Real.log (4 * T) ≤ Real.log 8 + Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity)]
      have : Real.log 4 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
      linarith
    have hfirst : Real.log (C * 16 / 7) ≤ |Real.log (C * 16 / 7)| := le_abs_self _
    have hlog8 : (0 : ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h1 : |Real.log (C * 16 / 7)| * 1 ≤ |Real.log (C * 16 / 7)| * Real.log T :=
      mul_le_mul_of_nonneg_left hlogT (abs_nonneg _)
    have h2 : ((N : ℝ) * Real.log 8) * 1 ≤ ((N : ℝ) * Real.log 8) * Real.log T :=
      mul_le_mul_of_nonneg_left hlogT (by positivity)
    have h3 : (N : ℝ) * Real.log (4 * T) ≤ (N : ℝ) * (Real.log 8 + Real.log T) :=
      mul_le_mul_of_nonneg_left hlog4T hN
    rw [hA]
    nlinarith [h1, h2, h3, hfirst, hlogT, hN, hlog8]
  have hstep : Real.log (M / (7 / 16 : ℝ)) ≤ (A + 1) * Real.log T := by
    nlinarith [hnum, hlogT]
  have hdiv : Real.log (M / (7 / 16 : ℝ)) / Real.log ((4 : ℝ) / r)
      ≤ ((A + 1) * Real.log T) / Real.log ((4 : ℝ) / r) := by gcongr
  calc Real.log (M / (7 / 16 : ℝ)) / Real.log ((4 : ℝ) / r)
      ≤ ((A + 1) * Real.log T) / Real.log ((4 : ℝ) / r) := hdiv
    _ = ((A + 1) / Real.log ((4 : ℝ) / r)) * Real.log T := by ring

/-- Real zeros of the detector trace in a disc of radius below `4` form a finite set. -/
theorem levinsonGTrace_real_zeros_finite_radius {lam T : ℝ} (hlam : |lam| ≤ 1) (hT : 6 ≤ T)
    {r : ℝ} (hr4 : |r| ≤ 4) :
    {x : ℝ | (x : ℂ) ∈ closedBall (4 : ℂ) |r| ∧ levinsonGTrace lam T (x : ℂ) = 0}.Finite := by
  have hKsub : closedBall (4 : ℂ) |r| ⊆ traceStrip :=
    closedBall_four_subset_traceStrip hr4
  have hK : AnalyticOnNhd ℂ (levinsonGTrace lam T) (closedBall (4 : ℂ) |r|) :=
    (analyticOnNhd_levinsonGTrace_strip hT).mono hKsub
  have hfin := (MeromorphicOn.divisor (levinsonGTrace lam T)
    (closedBall (4 : ℂ) |r|)).finiteSupport (isCompact_closedBall ..)
  have hcplx : {u : ℂ | u ∈ closedBall (4 : ℂ) |r| ∧ levinsonGTrace lam T u = 0}.Finite := by
    refine hfin.subset ?_
    intro u hu
    rw [Function.mem_support]
    have h1 := one_le_divisor_of_zero hK hu.1 hu.2
      (levinsonGTrace_order_ne_top hlam hT (hKsub hu.1))
    omega
  refine Set.Finite.ofFinset (hcplx.toFinset.preimage (fun x : ℝ => (x : ℂ))
    (fun p _ q _ h => Complex.ofReal_inj.mp h)) ?_
  intro x
  rw [Finset.mem_preimage, Set.Finite.mem_toFinset]
  rfl

/-- **The weighted horizontal edge of the detector, from any left abscissa `c ≥ ¼`.** -/
theorem exists_horizontal_weighted_levinsonG_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ lam : ℝ, |lam| ≤ 1 → ∀ T : ℝ, 6 ≤ T → ∀ c : ℝ, 1 / 4 ≤ c → c < 4 →
      (∀ x ∈ Set.Icc c (4 : ℝ), levinsonG (lam : ℂ) ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in c..(4 : ℝ), (x - c) *
          (logDeriv (levinsonG (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im| ≤ K * Real.log T := by
  classical
  obtain ⟨c₀, hc₀, hcount⟩ :=
    exists_levinsonGTrace_count_bound_radius (r := (15 / 4 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨2 * (15 / 4 : ℝ) * (c₀ + 1) * Real.pi, by positivity, ?_⟩
  intro lam hlam T hT c hc1 hc4 hne
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
  set Z : Finset ℝ :=
    (levinsonGTrace_real_zeros_finite_radius hlam hT (r := (15 / 4 : ℝ))
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 15/4)]; norm_num)).toFinset with hZdef
  have hZmem : ∀ x ∈ Set.Ioo c (4 : ℝ), (f x).re = 0 → x ∈ Z := by
    intro x hx hzero
    rw [hZdef, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 15 / 4), Complex.dist_eq]
      have hval : ‖((x : ℂ) - 4)‖ = |x - 4| := by
        rw [show ((x : ℂ) - 4) = ((x - 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hval, abs_le]
      constructor <;> linarith [hx.1, hx.2, hc1]
    · rw [levinsonGTrace_ofReal]
      rw [hfdef] at hzero
      simp only at hzero
      rw [hzero]
      norm_num
  have hbound := abs_integral_weighted_im_logDeriv_le_of_finite_re_zeros hc4.le
    (f := f) (f' := f') (fun x => hasDerivAt_levinsonG_horiz (lam : ℂ) hTne x)
    hfc hf'c (fun x hx => hne x hx) Z hZmem
  have hcongr : ∀ x ∈ Set.uIcc c (4 : ℝ),
      (x - c) * (f' x / f x).im
        = (x - c) * (logDeriv (levinsonG (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im := by
    intro x _
    rw [hf'def, hfdef, logDeriv_apply]
  rw [intervalIntegral.integral_congr hcongr] at hbound
  refine le_trans hbound ?_
  have hcard : ((Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card : ℝ) ≤ c₀ * Real.log T := by
    have hsubc : (Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card ≤ Z.card :=
      Finset.card_filter_le _ _
    have himg : (Z.image (fun x : ℝ => (x : ℂ))).card = Z.card :=
      Finset.card_image_of_injective _ (fun p q h => Complex.ofReal_inj.mp h)
    have hKsub : closedBall (4 : ℂ) |(15 / 4 : ℝ)| ⊆ traceStrip :=
      closedBall_four_subset_traceStrip (by rw [abs_of_pos (by norm_num : (0:ℝ) < 15/4)]; norm_num)
    have hKana : AnalyticOnNhd ℂ (levinsonGTrace lam T) (closedBall (4 : ℂ) |(15 / 4 : ℝ)|) :=
      (analyticOnNhd_levinsonGTrace_strip hT).mono hKsub
    have hKord : ∀ z ∈ closedBall (4 : ℂ) |(15 / 4 : ℝ)|,
        analyticOrderAt (levinsonGTrace lam T) z ≠ ⊤ :=
      fun z hz => levinsonGTrace_order_ne_top hlam hT (hKsub hz)
    have hS : ∀ z ∈ Z.image (fun x : ℝ => (x : ℂ)),
        z ∈ closedBall (4 : ℂ) |(15 / 4 : ℝ)| ∧ levinsonGTrace lam T z = 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rw [hZdef, Set.Finite.mem_toFinset] at hx
      exact hx
    have hle := card_le_divisor_sum (isCompact_closedBall ..) hKana hKord _ hS
    rw [himg] at hle
    have hcnt := hcount lam hlam T hT
    have hcast : ((Z.card : ℤ) : ℝ) ≤ ((∑ᶠ u, MeromorphicOn.divisor (levinsonGTrace lam T)
        (closedBall (4 : ℂ) |(15 / 4 : ℝ)|) u : ℤ) : ℝ) := by exact_mod_cast hle
    have hsubcast : ((Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card : ℝ)
        ≤ (Z.card : ℝ) := by exact_mod_cast hsubc
    push_cast at hcast
    linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hwidth : (0 : ℝ) < 4 - c := by linarith
  have hw2 : 4 - c ≤ 15 / 4 := by linarith
  have hN1 : (((Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card : ℝ) + 1)
      ≤ (c₀ + 1) * Real.log T := by
    have hexp : (c₀ + 1) * Real.log T = c₀ * Real.log T + Real.log T := by ring
    rw [hexp]
    linarith [hcard, hlog1]
  have hstep1 : (((Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card : ℝ) + 1) * Real.pi
      ≤ ((c₀ + 1) * Real.log T) * Real.pi :=
    mul_le_mul_of_nonneg_right hN1 hπ.le
  have hstep2 : 2 * (4 - c) *
      ((((Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card : ℝ) + 1) * Real.pi)
      ≤ 2 * (15 / 4 : ℝ) * (((c₀ + 1) * Real.log T) * Real.pi) := by
    refine mul_le_mul (by linarith) hstep1 (by positivity) (by norm_num)
  calc 2 * (4 - c) *
        ((((Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card : ℝ) + 1) * Real.pi)
      ≤ 2 * (15 / 4 : ℝ) * (((c₀ + 1) * Real.log T) * Real.pi) := hstep2
    _ = 2 * (15 / 4 : ℝ) * (c₀ + 1) * Real.pi * Real.log T := by ring

end RHTower

end
