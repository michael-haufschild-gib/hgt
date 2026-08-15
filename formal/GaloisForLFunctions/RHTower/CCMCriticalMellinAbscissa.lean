import Mathlib

/-!
# The exponential abscissa of the critical Mellin defect

The card's section 3 chain `(i) → (ii) → (iii)` is formalized: from the von Koch estimate `(8)` to
the polynomial bound `(10)`, then to subexponential growth `(ii)`, then to the vanishing of the
exponential abscissa `(iii)`.

*The logarithmic integral.*  `∫_1^X (log t)²/t dt = (log X)³/3` exactly, which is the `O(h³)` term
of `(10)`.

*The two von Koch contributions.*  Under `|Ψ(X) − X| ≤ K √X (log X)²`, the endpoint term of `(9)`
is `≤ K h²` and the integral term is `≤ K h³/3`.

*Polynomial growth is subexponential.*  A bound `C(1 + h³)` is eventually below `exp(ε h)` for every
`ε > 0`.

*The abscissa vanishes.*  Subexponential growth makes `log(1+|R(h)|)/h → 0`, which is exactly
`ω_R = 0`.

The Laplace–Stieltjes continuation `(2)`, `(5)`, the zeta zero/pole interface `(6)`, the partial
summation identity `(9)` and the von Koch theorem `(8)` itself are cited parents and stay outside
the Lean statement.
-/

open Filter Topology intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The logarithmic integral -/

/-- The exact logarithmic integral behind the `h³` term of `(10)`. -/
theorem integral_log_sq_div_self {X : ℝ} (hX : 1 ≤ X) :
    (∫ t in (1 : ℝ)..X, (Real.log t) ^ 2 / t) = (Real.log X) ^ 3 / 3 := by
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) X,
      HasDerivAt (fun s : ℝ => (Real.log s) ^ 3 / 3) ((Real.log t) ^ 2 / t) t := by
    intro t ht
    have htpos : 0 < t := by
      rcases Set.mem_uIcc.mp ht with h | h
      · linarith [h.1]
      · linarith [h.1, hX]
    have hlog : HasDerivAt (fun s : ℝ => Real.log s) t⁻¹ t :=
      Real.hasDerivAt_log (ne_of_gt htpos)
    have hcube : HasDerivAt (fun s : ℝ => (Real.log s) ^ 3)
        (3 * (Real.log t) ^ 2 * t⁻¹) t := by
      simpa using hlog.fun_pow 3
    have hdiv := hcube.div_const 3
    refine hdiv.congr_deriv ?_
    field_simp
  have hne0 : ∀ t ∈ Set.uIcc (1 : ℝ) X, t ≠ 0 := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h
    · exact ne_of_gt (by linarith [h.1])
    · exact ne_of_gt (by linarith [h.1, hX])
  have hcontlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc 1 X) :=
    Real.continuousOn_log.mono (fun t ht => hne0 t ht)
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t) ^ 2 / t) (Set.uIcc 1 X) :=
    ContinuousOn.div (hcontlog.pow 2) continuousOn_id hne0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp

/-! ## The two von Koch contributions -/

/-- **Equation (9), endpoint term.**  Under the von Koch bound the endpoint contribution is
`O(h²)`. -/
theorem vonKoch_endpoint_bound {K h : ℝ} {E : ℝ → ℝ}
    (hE : |E (Real.exp h)| ≤ K * Real.sqrt (Real.exp h) * (Real.log (Real.exp h)) ^ 2) :
    Real.exp (-(h / 2)) * |E (Real.exp h)| ≤ K * h ^ 2 := by
  have hsqrt : Real.sqrt (Real.exp h) = Real.exp (h / 2) := by
    rw [show Real.exp h = (Real.exp (h / 2)) ^ 2 by
      rw [← Real.exp_nat_mul]
      norm_num
      ring_nf, Real.sqrt_sq (le_of_lt (Real.exp_pos _))]
  rw [Real.log_exp, hsqrt] at hE
  have hpos : (0 : ℝ) < Real.exp (-(h / 2)) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hE (le_of_lt hpos)
  refine le_trans hmul (le_of_eq ?_)
  rw [show Real.exp (-(h / 2)) * (K * Real.exp (h / 2) * h ^ 2)
      = K * h ^ 2 * (Real.exp (-(h / 2)) * Real.exp (h / 2)) by ring, ← Real.exp_add]
  simp

/-- **Equation (9), integral term.**  Under the von Koch bound the integral contribution is
`≤ K h³/3`. -/
theorem vonKoch_integral_bound {K h : ℝ} (hh : 0 ≤ h) {E : ℝ → ℝ}
    (hEcont : ContinuousOn (fun t : ℝ => E t * t ^ (-(3 : ℝ) / 2)) (Set.uIcc 1 (Real.exp h)))
    (hE : ∀ t ∈ Set.uIcc (1 : ℝ) (Real.exp h),
      E t * t ^ (-(3 : ℝ) / 2) ≤ K * (Real.log t) ^ 2 / t) :
    (∫ t in (1 : ℝ)..Real.exp h, E t * t ^ (-(3 : ℝ) / 2)) ≤ K * h ^ 3 / 3 := by
  have hX : (1 : ℝ) ≤ Real.exp h := Real.one_le_exp hh
  have hne0 : ∀ t ∈ Set.uIcc (1 : ℝ) (Real.exp h), t ≠ 0 := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with hmem | hmem
    · exact ne_of_gt (by linarith [hmem.1])
    · exact ne_of_gt (by linarith [hmem.1, hX])
  have hcontlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc 1 (Real.exp h)) :=
    Real.continuousOn_log.mono (fun t ht => hne0 t ht)
  have hcont2 : ContinuousOn (fun t : ℝ => K * (Real.log t) ^ 2 / t)
      (Set.uIcc 1 (Real.exp h)) :=
    ContinuousOn.div (continuousOn_const.mul (hcontlog.pow 2)) continuousOn_id hne0
  have hmono : (∫ t in (1 : ℝ)..Real.exp h, E t * t ^ (-(3 : ℝ) / 2))
      ≤ ∫ t in (1 : ℝ)..Real.exp h, K * (Real.log t) ^ 2 / t := by
    refine intervalIntegral.integral_mono_on hX hEcont.intervalIntegrable
      hcont2.intervalIntegrable ?_
    intro t ht
    exact hE t (Set.mem_uIcc_of_le ht.1 ht.2)
  refine le_trans hmono (le_of_eq ?_)
  have hrw : (∫ t in (1 : ℝ)..Real.exp h, K * (Real.log t) ^ 2 / t)
      = K * ∫ t in (1 : ℝ)..Real.exp h, (Real.log t) ^ 2 / t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hrw, integral_log_sq_div_self hX, Real.log_exp]
  ring

/-! ## Polynomial growth is subexponential -/

/-- **Equation (10) → (ii).**  A polynomial bound is eventually below every exponential. -/
theorem eventually_le_exp_of_poly_bound {R : ℝ → ℝ} {C : ℝ}
    (hR : ∀ h : ℝ, 0 ≤ h → |R h| ≤ C * (1 + h ^ 3)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in atTop, |R h| ≤ Real.exp (ε * h) := by
  have hpoly : Tendsto (fun h : ℝ => C * (1 + h ^ 3) * Real.exp (-(ε * h))) atTop (nhds 0) := by
    have hbase : Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-x)) atTop (nhds 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3
    have hscale : Tendsto (fun h : ℝ => ε * h) atTop atTop :=
      Filter.tendsto_atTop_atTop_of_monotone (fun a b hab => by nlinarith)
        (fun b => ⟨b / ε, by rw [mul_div_cancel₀ _ (ne_of_gt hε)]⟩)
    have hcomp : Tendsto (fun h : ℝ => (ε * h) ^ 3 * Real.exp (-(ε * h))) atTop (nhds 0) :=
      hbase.comp hscale
    have hexp : Tendsto (fun h : ℝ => Real.exp (-(ε * h))) atTop (nhds 0) := by
      have := Real.tendsto_exp_atBot
      exact this.comp (tendsto_neg_atBot_iff.mpr hscale)
    have hsum : Tendsto
        (fun h : ℝ => C * Real.exp (-(ε * h)) + (C / ε ^ 3) * ((ε * h) ^ 3 * Real.exp (-(ε * h))))
        atTop (nhds (C * 0 + (C / ε ^ 3) * 0)) :=
      (hexp.const_mul C).add (hcomp.const_mul (C / ε ^ 3))
    rw [mul_zero, mul_zero, add_zero] at hsum
    refine hsum.congr fun h => ?_
    field_simp
  have hev := hpoly.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with h hlt hh0
  have hexppos : (0 : ℝ) < Real.exp (ε * h) := Real.exp_pos _
  have hkey : C * (1 + h ^ 3) ≤ Real.exp (ε * h) := by
    have hne : Real.exp (-(ε * h)) = (Real.exp (ε * h))⁻¹ := by
      rw [← Real.exp_neg]
    rw [hne, ← div_eq_mul_inv] at hlt
    have hlt2 := (div_lt_one hexppos).mp hlt
    linarith
  exact le_trans (hR h hh0) hkey

/-! ## The exponential abscissa vanishes -/

/-- **(ii) → (iii).**  Subexponential growth makes the exponential abscissa zero. -/
theorem tendsto_logAbscissa_zero {R : ℝ → ℝ}
    (h : ∀ ε > 0, ∀ᶠ x in atTop, |R x| ≤ Real.exp (ε * x)) :
    Tendsto (fun x => Real.log (1 + |R x|) / x) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hlog2 : Tendsto (fun x : ℝ => Real.log 2 / x) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hsmall : ∀ᶠ x : ℝ in atTop, Real.log 2 / x < ε / 2 := by
    have := hlog2.eventually (gt_mem_nhds hhalf)
    exact this
  filter_upwards [h (ε / 2) hhalf, hsmall, eventually_gt_atTop (0 : ℝ)] with x hx hs hx0
  have hRnn : (0 : ℝ) ≤ |R x| := abs_nonneg _
  have hone : (1 : ℝ) ≤ 1 + |R x| := by linarith
  have hnn : 0 ≤ Real.log (1 + |R x|) / x :=
    div_nonneg (Real.log_nonneg hone) (le_of_lt hx0)
  have hub : 1 + |R x| ≤ 2 * Real.exp (ε / 2 * x) := by
    have hexp1 : (1 : ℝ) ≤ Real.exp (ε / 2 * x) := by
      refine Real.one_le_exp ?_
      positivity
    linarith
  have hlogub : Real.log (1 + |R x|) ≤ Real.log 2 + ε / 2 * x := by
    have := Real.log_le_log (by linarith) hub
    rwa [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at this
  have hdiv : Real.log (1 + |R x|) / x ≤ Real.log 2 / x + ε / 2 := by
    rw [div_le_iff₀ hx0]
    have hxx : (Real.log 2 / x + ε / 2) * x = Real.log 2 + ε / 2 * x := by
      field_simp
    rw [hxx]
    exact hlogub
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  linarith

end GaloisForLFunctions.RHTower

end
