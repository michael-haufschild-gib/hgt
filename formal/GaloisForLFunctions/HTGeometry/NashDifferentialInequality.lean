import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Nash's differential inequality

The analytic core of every ultracontractivity argument — Nash's, and after him Carlen–Kusuoka–
Stroock's, whose on-diagonal heat-kernel bound `k(t,x,x) ≤ C t^{-n}` is the input to Lemma 2.3 of
Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the Laplacian*
(arXiv:2509.06151v2) — is a single ordinary differential inequality:

```text
f' ≤ −A f^{1+p}  on (0,∞),  f > 0     ⟹     f(t) ≤ (A p t)^{−1/p} .
```

The decay rate is universal: it does not remember `f(0)`, which is exactly why the bound is a pure
power of `t`.  The proof is that `g = f^{−p}` has `g' ≥ A p`, so `g(t) ≥ g(s) + Ap(t−s)` and, `g`
being positive, `g(t) ≥ A p t`.

Mathlib has no such lemma; it is proved here in the generality needed.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

/-- **Nash's differential inequality.**

A positive solution of `f' ≤ −A f^{1+p}` on the half-line obeys the universal decay
`f(t) ≤ (A p t)^{−1/p}`. -/
theorem nash_decay {f f' : ℝ → ℝ} {A p : ℝ} (hA : 0 < A) (hp : 0 < p)
    (hpos : ∀ y, 0 < y → 0 < f y)
    (hderiv : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hineq : ∀ y, 0 < y → f' y ≤ -A * (f y) ^ (1 + p))
    {t : ℝ} (ht : 0 < t) :
    f t ≤ (A * p * t) ^ (-(1 / p)) := by
  set g : ℝ → ℝ := fun y => (f y) ^ (-p) with hgdef
  have hgderiv : ∀ y, 0 < y → HasDerivAt g (f' y * (-p) * (f y) ^ (-p - 1)) y := by
    intro y hy
    exact (hderiv y hy).rpow_const (Or.inl (ne_of_gt (hpos y hy)))
  have hgpos : ∀ y, 0 < y → 0 < g y := by
    intro y hy
    exact Real.rpow_pos_of_pos (hpos y hy) _
  have hlow : ∀ y, 0 < y → A * p ≤ f' y * (-p) * (f y) ^ (-p - 1) := by
    intro y hy
    have hfy : 0 < f y := hpos y hy
    have hc : (-p) * (f y) ^ (-p - 1) ≤ 0 := by
      have : (0 : ℝ) < (f y) ^ (-p - 1) := Real.rpow_pos_of_pos hfy _
      nlinarith [hp]
    have hstep := mul_le_mul_of_nonpos_right (hineq y hy) hc
    have hcollapse : (-A * (f y) ^ (1 + p)) * ((-p) * (f y) ^ (-p - 1)) = A * p := by
      have hsum : (f y) ^ (1 + p) * (f y) ^ (-p - 1) = 1 := by
        rw [← Real.rpow_add hfy, show (1 : ℝ) + p + (-p - 1) = 0 by ring, Real.rpow_zero]
      calc (-A * (f y) ^ (1 + p)) * ((-p) * (f y) ^ (-p - 1))
          = (A * p) * ((f y) ^ (1 + p) * (f y) ^ (-p - 1)) := by ring
        _ = A * p := by rw [hsum, mul_one]
    have hassoc : f' y * (-p) * (f y) ^ (-p - 1)
        = f' y * ((-p) * (f y) ^ (-p - 1)) := by ring
    rw [hassoc]
    rw [hcollapse] at hstep
    exact hstep
  -- the mean value estimate on `[s,t]`
  have hmvt : ∀ s, 0 < s → s < t → A * p * (t - s) ≤ g t - g s := by
    intro s hs hst
    have hsub : Icc s t ⊆ Ioi (0 : ℝ) := by
      intro y hy
      exact lt_of_lt_of_le hs hy.1
    have hdiff : DifferentiableOn ℝ g (Icc s t) := by
      intro y hy
      exact ((hgderiv y (hsub hy)).differentiableAt).differentiableWithinAt
    have hcont : ContinuousOn g (Icc s t) := hdiff.continuousOn
    have hint : DifferentiableOn ℝ g (interior (Icc s t)) :=
      hdiff.mono interior_subset
    have hderivBound : ∀ y ∈ interior (Icc s t), A * p ≤ deriv g y := by
      intro y hy
      have hy' : y ∈ Icc s t := interior_subset hy
      have hy0 : 0 < y := hsub hy'
      rw [(hgderiv y hy0).deriv]
      exact hlow y hy0
    exact (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv hcont hint hderivBound
      s (left_mem_Icc.mpr hst.le) t (right_mem_Icc.mpr hst.le) hst.le
  have hgt : A * p * t ≤ g t := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨s, hs0, hst, hsmall⟩ : ∃ s, 0 < s ∧ s < t ∧ A * p * s < ε := by
      refine ⟨min (t / 2) (ε / (A * p + 1)), ?_, ?_, ?_⟩
      · exact lt_min (by linarith) (by positivity)
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · have h1 : min (t / 2) (ε / (A * p + 1)) ≤ ε / (A * p + 1) := min_le_right _ _
        have h2 : A * p * (ε / (A * p + 1)) < ε := by
          rw [mul_div_assoc']
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [hε, hA, hp]
        calc A * p * min (t / 2) (ε / (A * p + 1))
            ≤ A * p * (ε / (A * p + 1)) := by
              exact mul_le_mul_of_nonneg_left h1 (by positivity)
          _ < ε := h2
    have h := hmvt s hs0 hst
    have hgs : 0 < g s := hgpos s hs0
    nlinarith [h, hgs, hsmall]
  -- invert the power
  have hApt : 0 < A * p * t := by positivity
  have hft : 0 < f t := hpos t ht
  have hgt' : A * p * t ≤ (f t) ^ (-p) := hgt
  have hexp : -(1 / p) ≤ 0 := by
    have : (0 : ℝ) < 1 / p := by positivity
    linarith
  have hstep : ((f t) ^ (-p)) ^ (-(1 / p)) ≤ (A * p * t) ^ (-(1 / p)) :=
    Real.rpow_le_rpow_of_nonpos hApt hgt' hexp
  have hid : ((f t) ^ (-p)) ^ (-(1 / p)) = f t := by
    rw [← Real.rpow_mul hft.le]
    have hmul : (-p) * (-(1 / p)) = 1 := by
      field_simp
    rw [hmul, Real.rpow_one]
  rw [← hid]
  exact hstep

end GaloisForLFunctions.HTGeometry
