import GaloisForLFunctions.RHTower.DeningerHarmonicMode
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniqueness of the decaying harmonic mode

At a fixed frequency the leafwise Hodge system has a two-dimensional solution space, spanned by a
decaying and a growing exponential.  The combination `a - i ε b` solves `v' = |μ| v`, so it is a
growing exponential and its modulus is bounded below by a positive constant on the whole half
line; square integrability therefore forces it to vanish.  What is left is the chirality relation
`b = -i ε a`, which turns the system into `a' = -|μ| a` and identifies the solution with a scalar
multiple of the mode.

At zero frequency both coefficients are constant, and a nonzero constant is not square integrable
on the half line, so no nonzero solution survives.

* `deningerSolution_growing_eq_zero` : square integrability kills the growing part.
* `deningerSolution_eq_smul_mode` : every square-integrable solution is a multiple of the mode.
* `deningerSolution_zeroFreq_eq_zero` : no nonzero square-integrable solution at zero frequency.
-/

namespace RHTower

open MeasureTheory Set

section Uniqueness

/-- Constancy on the open half line from a vanishing derivative. -/
private theorem deningerConst_of_derivZero {g : ℝ → ℂ}
    (hg : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt g 0 r) {r s : ℝ}
    (hr : r ∈ Ioi (0 : ℝ)) (hs : s ∈ Ioi (0 : ℝ)) : g r = g s := by
  refine (convex_Ioi (0 : ℝ)).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) ?_ ?_ hr hs
  · intro x hx
    exact (hg x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    have hf : HasFDerivAt g (0 : ℝ →L[ℝ] ℂ) x := by
      have hd := (hg x hx).hasFDerivAt
      rwa [show ContinuousLinearMap.toSpanSingleton ℝ (0 : ℂ) = 0 by ext; simp] at hd
    exact HasFDerivWithinAt.fderivWithin (HasFDerivAt.hasFDerivWithinAt hf)
      ((uniqueDiffOn_Ioi 0) x hx)

/-- A function bounded below by a positive constant is not integrable on the half line. -/
private theorem deningerNotIntegrable_of_pos_le {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : IntegrableOn f (Ioi (0 : ℝ))) (hle : ∀ r ∈ Ioi (0 : ℝ), c ≤ f r) : False := by
  have hconst : IntegrableOn (fun _ : ℝ => c) (Ioi (0 : ℝ)) := by
    refine hf.mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_eq_abs, abs_of_pos hc]
    exact hle r hr
  rw [IntegrableOn, integrable_const_iff] at hconst
  rcases hconst with h | h
  · exact absurd h (ne_of_gt hc)
  · haveI := h
    have hfin := measure_lt_top (volume.restrict (Ioi (0 : ℝ))) univ
    rw [Measure.restrict_apply_univ, Real.volume_Ioi] at hfin
    exact absurd hfin (lt_irrefl _)

variable {μ : ℝ} {a b : ℝ → ℂ}

/-- The growing combination `v = a - i ε b` of a solution. -/
private noncomputable def deningerGrowingPart (μ : ℝ) (a b : ℝ → ℂ) (r : ℝ) : ℂ :=
  a r - Complex.I * (deningerFreqSign μ : ℂ) * b r

/-- **The growing combination times the decaying profile is constant.** -/
private theorem deningerGrowingPart_const (hμ : μ ≠ 0)
    (ha : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt a (-(Complex.I * (μ : ℂ) * b r)) r)
    (hb : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt b (Complex.I * (μ : ℂ) * a r) r) {r s : ℝ}
    (hr : r ∈ Ioi (0 : ℝ)) (hs : s ∈ Ioi (0 : ℝ)) :
    deningerGrowingPart μ a b r * (deningerModeProfile μ r : ℂ)
      = deningerGrowingPart μ a b s * (deningerModeProfile μ s : ℂ) := by
  have hsq : (deningerFreqSign μ : ℂ) * (deningerFreqSign μ : ℂ) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_sq μ)
  have habs : ((|μ| : ℝ) : ℂ) = (deningerFreqSign μ : ℂ) * (μ : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_abs hμ)
  refine deningerConst_of_derivZero
    (g := fun t => deningerGrowingPart μ a b t * (deningerModeProfile μ t : ℂ))
    (fun x hx => ?_) hr hs
  have hv : HasDerivAt (deningerGrowingPart μ a b)
      (((|μ| : ℝ) : ℂ) * deningerGrowingPart μ a b x) x := by
    have h := (ha x hx).sub ((hb x hx).const_mul (Complex.I * (deningerFreqSign μ : ℂ)))
    have hval : -(Complex.I * (μ : ℂ) * b x)
        - Complex.I * (deningerFreqSign μ : ℂ) * (Complex.I * (μ : ℂ) * a x)
        = ((|μ| : ℝ) : ℂ) * deningerGrowingPart μ a b x := by
      rw [deningerGrowingPart, habs]
      linear_combination (Complex.I * (μ : ℂ) * b x) * hsq
        - ((deningerFreqSign μ : ℂ) * (μ : ℂ) * a x) * Complex.I_sq
    rw [← hval]
    exact h
  have hp : HasDerivAt (fun r => (deningerModeProfile μ r : ℂ))
      ((deningerModeProfile μ x * -|μ| : ℝ) : ℂ) x :=
    (deningerModeProfile_hasDerivAt μ x).ofReal_comp
  have hprod := hv.mul hp
  have hzero : ((|μ| : ℝ) : ℂ) * deningerGrowingPart μ a b x * (deningerModeProfile μ x : ℂ)
      + deningerGrowingPart μ a b x * ((deningerModeProfile μ x * -|μ| : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [hzero] at hprod
  exact hprod

/-- **Square integrability kills the growing part.** -/
theorem deningerSolution_growing_eq_zero (hμ : μ ≠ 0)
    (ha : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt a (-(Complex.I * (μ : ℂ) * b r)) r)
    (hb : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt b (Complex.I * (μ : ℂ) * a r) r)
    (hL2 : IntegrableOn (fun r => ‖a r‖ ^ (2 : ℕ) + ‖b r‖ ^ (2 : ℕ)) (Ioi (0 : ℝ)))
    {r : ℝ} (hr : r ∈ Ioi (0 : ℝ)) : a r = Complex.I * (deningerFreqSign μ : ℂ) * b r := by
  by_contra hne
  have hv0 : deningerGrowingPart μ a b r ≠ 0 := by
    rw [deningerGrowingPart]
    exact sub_ne_zero_of_ne hne
  set C : ℝ := ‖deningerGrowingPart μ a b r * (deningerModeProfile μ r : ℂ)‖ with hC
  have hCpos : 0 < C := by
    rw [hC, norm_pos_iff]
    exact mul_ne_zero hv0 (by
      exact_mod_cast ne_of_gt (deningerModeProfile_pos μ r))
  have hprofile_le : ∀ s ∈ Ioi (0 : ℝ), deningerModeProfile μ s ≤ 1 := by
    intro s hs
    rw [deningerModeProfile, Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ |μ| * s := mul_nonneg (abs_nonneg μ) (le_of_lt hs)
    linarith [this]
  have hlow : ∀ s ∈ Ioi (0 : ℝ), C ≤ ‖deningerGrowingPart μ a b s‖ := by
    intro s hs
    have hconst := deningerGrowingPart_const hμ ha hb hr hs
    have hnorm : C = ‖deningerGrowingPart μ a b s‖ * deningerModeProfile μ s := by
      rw [hC, hconst, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (deningerModeProfile_pos μ s)]
    rw [hnorm]
    nlinarith [norm_nonneg (deningerGrowingPart μ a b s), hprofile_le s hs,
      deningerModeProfile_pos μ s]
  refine deningerNotIntegrable_of_pos_le (c := C ^ (2 : ℕ) / 2) (by positivity) hL2 ?_
  intro s hs
  have hsign : ‖Complex.I * (deningerFreqSign μ : ℂ)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
      deningerFreqSign]
    split_ifs <;> norm_num
  have htri : ‖deningerGrowingPart μ a b s‖ ≤ ‖a s‖ + ‖b s‖ := by
    rw [deningerGrowingPart]
    calc ‖a s - Complex.I * (deningerFreqSign μ : ℂ) * b s‖
        ≤ ‖a s‖ + ‖Complex.I * (deningerFreqSign μ : ℂ) * b s‖ := norm_sub_le _ _
      _ = ‖a s‖ + ‖b s‖ := by rw [norm_mul, hsign, one_mul]
  have hCle := hlow s hs
  nlinarith [norm_nonneg (a s), norm_nonneg (b s), sq_nonneg (‖a s‖ - ‖b s‖), hCle, htri]

/-- **Every square-integrable solution is a scalar multiple of the mode.** -/
theorem deningerSolution_eq_smul_mode (hμ : μ ≠ 0)
    (ha : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt a (-(Complex.I * (μ : ℂ) * b r)) r)
    (hb : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt b (Complex.I * (μ : ℂ) * a r) r)
    (hL2 : IntegrableOn (fun r => ‖a r‖ ^ (2 : ℕ) + ‖b r‖ ^ (2 : ℕ)) (Ioi (0 : ℝ))) :
    ∃ c : ℂ, ∀ r ∈ Ioi (0 : ℝ), (a r, b r) = c • deningerMode μ r := by
  have hsq : (deningerFreqSign μ : ℂ) * (deningerFreqSign μ : ℂ) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_sq μ)
  have habs : ((|μ| : ℝ) : ℂ) = (deningerFreqSign μ : ℂ) * (μ : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_abs hμ)
  -- the chirality relation
  have hchi : ∀ r ∈ Ioi (0 : ℝ), b r = -(Complex.I * (deningerFreqSign μ : ℂ)) * a r := by
    intro r hr
    have h := deningerSolution_growing_eq_zero hμ ha hb hL2 hr
    linear_combination (Complex.I * (deningerFreqSign μ : ℂ)) * h
      + (Complex.I ^ (2 : ℕ) * b r) * hsq + (b r) * Complex.I_sq
  -- the radial equation
  have hrad : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt a (-(((|μ| : ℝ) : ℂ) * a r)) r := by
    intro r hr
    have hval : -(Complex.I * (μ : ℂ) * b r) = -(((|μ| : ℝ) : ℂ) * a r) := by
      rw [hchi r hr, habs]
      linear_combination ((deningerFreqSign μ : ℂ) * (μ : ℂ) * a r) * Complex.I_sq
    rw [← hval]
    exact ha r hr
  -- the radial profile is exhausted
  have hgrow : ∀ r ∈ Ioi (0 : ℝ), ∀ s ∈ Ioi (0 : ℝ),
      a r * ((Real.exp (|μ| * r) : ℝ) : ℂ) = a s * ((Real.exp (|μ| * s) : ℝ) : ℂ) := by
    intro r hr s hs
    refine deningerConst_of_derivZero
      (g := fun t => a t * ((Real.exp (|μ| * t) : ℝ) : ℂ)) (fun x hx => ?_) hr hs
    have hp : HasDerivAt (fun x : ℝ => ((Real.exp (|μ| * x) : ℝ) : ℂ))
        ((Real.exp (|μ| * x) * |μ| : ℝ) : ℂ) x := by
      refine HasDerivAt.ofReal_comp ?_
      simpa using ((hasDerivAt_id x).const_mul |μ|).exp
    have hprod := (hrad x hx).mul hp
    have hzero : -(((|μ| : ℝ) : ℂ) * a x) * ((Real.exp (|μ| * x) : ℝ) : ℂ)
        + a x * ((Real.exp (|μ| * x) * |μ| : ℝ) : ℂ) = 0 := by
      push_cast
      ring
    rw [hzero] at hprod
    exact hprod
  refine ⟨a 1 * ((Real.exp (|μ| * 1) : ℝ) : ℂ), fun r hr => ?_⟩
  have hone : (1 : ℝ) ∈ Ioi (0 : ℝ) := by norm_num
  have hkey := hgrow r hr 1 hone
  have hprof : ((Real.exp (|μ| * r) : ℝ) : ℂ) * (deningerModeProfile μ r : ℂ) = 1 := by
    rw [deningerModeProfile]
    rw [show ((Real.exp (|μ| * r) : ℝ) : ℂ) * ((Real.exp (-|μ| * r) : ℝ) : ℂ)
        = ((Real.exp (|μ| * r) * Real.exp (-|μ| * r) : ℝ) : ℂ) by push_cast; ring,
      ← Real.exp_add]
    norm_num
  have hfst : a r = a 1 * ((Real.exp (|μ| * 1) : ℝ) : ℂ) * (deningerModeProfile μ r : ℂ) := by
    calc a r = a r * (((Real.exp (|μ| * r) : ℝ) : ℂ) * (deningerModeProfile μ r : ℂ)) := by
          rw [hprof, mul_one]
      _ = (a r * ((Real.exp (|μ| * r) : ℝ) : ℂ)) * (deningerModeProfile μ r : ℂ) := by ring
      _ = a 1 * ((Real.exp (|μ| * 1) : ℝ) : ℂ) * (deningerModeProfile μ r : ℂ) := by rw [hkey]
  refine Prod.ext ?_ ?_
  · show a r = a 1 * ((Real.exp (|μ| * 1) : ℝ) : ℂ) * (deningerMode μ r).1
    rw [deningerMode_fst]
    exact hfst
  · show b r = a 1 * ((Real.exp (|μ| * 1) : ℝ) : ℂ) * (deningerMode μ r).2
    rw [deningerMode_snd, hchi r hr, hfst]
    ring

/-- **No nonzero square-integrable solution at zero frequency.** -/
theorem deningerSolution_zeroFreq_eq_zero
    (ha : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt a 0 r) (hb : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt b 0 r)
    (hL2 : IntegrableOn (fun r => ‖a r‖ ^ (2 : ℕ) + ‖b r‖ ^ (2 : ℕ)) (Ioi (0 : ℝ)))
    {r : ℝ} (hr : r ∈ Ioi (0 : ℝ)) : a r = 0 ∧ b r = 0 := by
  by_contra hcon
  have hpos : 0 < ‖a r‖ ^ (2 : ℕ) + ‖b r‖ ^ (2 : ℕ) := by
    rcases not_and_or.mp hcon with h | h
    · have : 0 < ‖a r‖ := norm_pos_iff.mpr h
      nlinarith [norm_nonneg (b r)]
    · have : 0 < ‖b r‖ := norm_pos_iff.mpr h
      nlinarith [norm_nonneg (a r)]
  refine deningerNotIntegrable_of_pos_le hpos hL2 ?_
  intro s hs
  have hasr : a s = a r := deningerConst_of_derivZero ha hs hr
  have hbsr : b s = b r := deningerConst_of_derivZero hb hs hr
  rw [hasr, hbsr]

end Uniqueness

end RHTower
