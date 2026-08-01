import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Continuous characters of the line are exponentials

A continuous multiplicative map `ψ : ℝ → ℂ` of modulus one is `t ↦ e^{iλt}` for a unique real `λ`.

The proof is the classical smoothing argument.  For a small `a` the integral `A = ∫₀^a ψ` is nonzero,
and `ψ t · A = ∫_t^{t+a} ψ` exhibits `ψ` as a difference of primitives, hence differentiable with
`ψ' = c ψ` where `c = (ψ a - 1)/A`.  Therefore `ψ t = e^{ct}`, and modulus one forces `c` to be
purely imaginary.
-/

open Complex MeasureTheory intervalIntegral

namespace GaloisForLFunctions

noncomputable section

/-- **Continuous characters of the line are exponentials.** -/
theorem exists_exp_of_continuous_character {ψ : ℝ → ℂ} (hcont : Continuous ψ)
    (hmul : ∀ s t : ℝ, ψ (s + t) = ψ s * ψ t) (hnorm : ∀ t : ℝ, ‖ψ t‖ = 1) :
    ∃ lam : ℝ, ∀ t : ℝ, ψ t = Complex.exp ((lam * t : ℝ) * Complex.I) := by
  -- the value at the origin
  have hψ0 : ψ 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    have hne : ψ 0 ≠ 0 := by
      intro h0
      have := hnorm 0
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    field_simp at h
    exact h.symm
  -- a window on which the average is close to one
  obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (ε := 1 / 2) (by norm_num)
  set a : ℝ := δ / 2 with ha'
  have ha : 0 < a := by positivity
  have hclose : ∀ s ∈ Set.uIoc (0 : ℝ) a, ‖ψ s - 1‖ ≤ 1 / 2 := by
    intro s hs
    rw [Set.uIoc_of_le ha.le] at hs
    have hsd : dist s 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
      calc s ≤ a := hs.2
        _ < δ := by rw [ha']; linarith
    have := hδψ hsd
    rw [hψ0, Complex.dist_eq] at this
    exact this.le
  set A : ℂ := ∫ s in (0 : ℝ)..a, ψ s with hA'
  have hAsub : ‖A - (a : ℂ)‖ ≤ a * (1 / 2) := by
    have hint : A - (a : ℂ) = ∫ s in (0 : ℝ)..a, (ψ s - 1) := by
      rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
        (intervalIntegrable_const), hA']
      simp
    rw [hint]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1 / 2)
      (f := fun s => ψ s - 1) (a := (0 : ℝ)) (b := a) hclose
    calc ‖∫ s in (0 : ℝ)..a, (ψ s - 1)‖ ≤ 1 / 2 * |a - 0| := this
      _ = a * (1 / 2) := by rw [sub_zero, abs_of_nonneg ha.le]; ring
  have hAne : A ≠ 0 := by
    intro h0
    rw [h0] at hAsub
    have : ‖(a : ℂ)‖ ≤ a * (1 / 2) := by
      rw [zero_sub, norm_neg] at hAsub
      exact hAsub
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha.le] at this
    linarith
  -- `ψ` is a difference of primitives
  set F : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, ψ u with hF'
  have hFderiv : ∀ t : ℝ, HasDerivAt F (ψ t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hshift : ∀ t : ℝ, F (t + a) - F t = ψ t * A := by
    intro t
    have h1 : ∫ u in t..(t + a), ψ u = ∫ s in (0 : ℝ)..a, ψ (t + s) := by
      rw [intervalIntegral.integral_comp_add_left (fun u => ψ u) t]
      simp
    have h2 : ∫ s in (0 : ℝ)..a, ψ (t + s) = ψ t * A := by
      rw [hA', ← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun s _ => hmul t s
    have h3 : F t + ∫ u in t..(t + a), ψ u = F (t + a) := by
      rw [hF']
      exact intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    rw [← h3, h1, h2]
    ring
  -- hence `ψ' = c ψ`
  set c : ℂ := (ψ a - 1) / A with hc'
  have hψderiv : ∀ t : ℝ, HasDerivAt ψ (c * ψ t) t := by
    intro t
    have hid : HasDerivAt (fun s : ℝ => s + a) 1 t := by
      simpa using (hasDerivAt_id t).add_const a
    have hcomp : HasDerivAt (fun s : ℝ => F (s + a)) (ψ (t + a)) t := by
      have h2 := (hFderiv (t + a)).scomp t hid
      rw [one_smul] at h2
      exact h2
    have h0 : HasDerivAt (fun s : ℝ => F (s + a) - F s) (ψ (t + a) - ψ t) t :=
      hcomp.sub (hFderiv t)
    have hdiff : HasDerivAt (fun s : ℝ => ψ s * A) (ψ (t + a) - ψ t) t :=
      h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => (hshift s).symm)
    have hψ' : HasDerivAt ψ ((ψ (t + a) - ψ t) / A) t := by
      have h1 := hdiff.div_const A
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      field_simp
    have hval : (ψ (t + a) - ψ t) / A = c * ψ t := by
      rw [hmul t a, hc']
      field_simp
    rw [← hval]
    exact hψ'
  -- solve the differential equation
  have hgconst : ∀ t : ℝ, ψ t * Complex.exp (-(c * t)) = 1 := by
    have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ψ s * Complex.exp (-(c * (s : ℂ)))) 0 t := by
      intro t
      have hlin : HasDerivAt (fun s : ℝ => -(c * (s : ℂ))) (-c) t := by
        have h1 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
        have h2 : HasDerivAt (fun s : ℝ => c * ((s : ℝ) : ℂ)) c t := by
          have h3 := h1.const_mul c
          rw [mul_one] at h3
          exact h3
        exact h2.neg
      have h1 : HasDerivAt (fun s : ℝ => Complex.exp (-(c * (s : ℂ))))
          (Complex.exp (-(c * (t : ℂ))) * (-c)) t := hlin.cexp
      have h2 := (hψderiv t).mul h1
      have hz : c * ψ t * Complex.exp (-(c * (t : ℂ)))
          + ψ t * (Complex.exp (-(c * (t : ℂ))) * (-c)) = 0 := by ring
      rw [hz] at h2
      exact h2
    intro t
    have hconst := is_const_of_deriv_eq_zero (f := fun s : ℝ => ψ s * Complex.exp (-(c * (s : ℂ))))
      (fun x => (hg x).differentiableAt) (fun x => (hg x).deriv) t 0
    calc ψ t * Complex.exp (-(c * (t : ℂ)))
        = ψ 0 * Complex.exp (-(c * ((0 : ℝ) : ℂ))) := hconst
      _ = 1 := by simp [hψ0]
  have hexp : ∀ t : ℝ, ψ t = Complex.exp (c * t) := by
    intro t
    have h := hgconst t
    have hmulinv : Complex.exp (-(c * (t : ℂ))) * Complex.exp (c * (t : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      simp
    calc ψ t = ψ t * (Complex.exp (-(c * (t : ℂ))) * Complex.exp (c * (t : ℂ))) := by
          rw [hmulinv, mul_one]
      _ = (ψ t * Complex.exp (-(c * (t : ℂ)))) * Complex.exp (c * (t : ℂ)) := by ring
      _ = Complex.exp (c * t) := by rw [h, one_mul]
  -- modulus one forces the exponent to be imaginary
  have hre : c.re = 0 := by
    have h1 : ‖ψ 1‖ = 1 := hnorm 1
    rw [hexp 1, Complex.norm_exp] at h1
    have h2 : (c * ((1 : ℝ) : ℂ)).re = 0 := by
      rwa [Real.exp_eq_one_iff] at h1
    simpa using h2
  refine ⟨c.im, fun t => ?_⟩
  rw [hexp t]
  congr 1
  apply Complex.ext <;> simp [hre]

end

end GaloisForLFunctions
