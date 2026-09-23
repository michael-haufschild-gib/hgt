import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Strict log-concavity of the Bose-log law

For `a > 0` the Bose measure `t^a/(exp t - 1) dt` on the positive half line, read in the
logarithmic coordinate `X = log t`, has density proportional to

`exp ((a+1) X) / (exp (exp X) - 1)`.

Its log-density is `(a+1) X - log (exp (exp X) - 1)`, whose first derivative is `(a+1) - g (exp X)`
for the growth factor

`g t = t / (1 - exp (-t))`,

and whose second derivative is therefore `-t * g' t` at `t = exp X`.  The single inequality
`exp t > 1 + t` makes `g' t > 0` for every `t > 0`, so the score is strictly decreasing and the
log-density is strictly concave for every shift `a`.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Bose growth factor `g t = t / (1 - exp (-t))`. -/
def boseGrowth (t : ℝ) : ℝ := t / (1 - Real.exp (-t))

/-- The derivative of the Bose growth factor, in closed form. -/
def boseGrowthDeriv (t : ℝ) : ℝ :=
  (1 - (1 + t) * Real.exp (-t)) / (1 - Real.exp (-t)) ^ (2 : ℕ)

theorem one_sub_exp_neg_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem hasDerivAt_boseGrowth {t : ℝ} (ht : 0 < t) :
    HasDerivAt boseGrowth (boseGrowthDeriv t) t := by
  have hden : (1 : ℝ) - Real.exp (-t) ≠ 0 := ne_of_gt (one_sub_exp_neg_pos ht)
  have hnum : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t) * (-1)) t :=
    HasDerivAt.exp ((hasDerivAt_id t).neg)
  have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (Real.exp (-t)) t := by
    have hraw : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x))
        (-(Real.exp (-t) * (-1 : ℝ))) t := h1.const_sub 1
    rw [show -(Real.exp (-t) * (-1 : ℝ)) = Real.exp (-t) from by ring] at hraw
    exact hraw
  have h := hnum.div hd hden
  have hval : (1 * (1 - Real.exp (-t)) - t * Real.exp (-t)) / (1 - Real.exp (-t)) ^ (2 : ℕ)
      = boseGrowthDeriv t := by
    rw [boseGrowthDeriv]
    congr 1
    ring
  rw [← hval]
  exact h

/-- **The growth factor is strictly increasing.**  The numerator of `g'` is
`1 - (1+t) exp (-t)`, which is positive exactly because `exp t > 1 + t`. -/
theorem boseGrowthDeriv_pos {t : ℝ} (ht : 0 < t) : 0 < boseGrowthDeriv t := by
  have hden : 0 < (1 - Real.exp (-t)) ^ (2 : ℕ) := pow_pos (one_sub_exp_neg_pos ht) 2
  have hkey : (1 + t) * Real.exp (-t) < 1 := by
    have h := Real.add_one_lt_exp (x := t) (ne_of_gt ht)
    have hpos : (0:ℝ) < Real.exp (-t) := Real.exp_pos _
    have hmul : (t + 1) * Real.exp (-t) < Real.exp t * Real.exp (-t) :=
      mul_lt_mul_of_pos_right h hpos
    rw [← Real.exp_add] at hmul
    simp only [add_neg_cancel, Real.exp_zero] at hmul
    linarith
  rw [boseGrowthDeriv]
  exact div_pos (by linarith) hden

theorem strictMonoOn_boseGrowth : StrictMonoOn boseGrowth (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro t ht
    exact ((hasDerivAt_boseGrowth ht).continuousAt).continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    rw [(hasDerivAt_boseGrowth ht).deriv]
    exact boseGrowthDeriv_pos ht

/-! ### The Bose-log density -/

/-- The log-density of the Bose-log law in the logarithmic coordinate `X = log t`, up to the
normalizing constant. -/
def boseLogDensity (a X : ℝ) : ℝ :=
  (a + 1) * X - Real.log (Real.exp (Real.exp X) - 1)

/-- The score of the Bose-log law. -/
def boseLogScore (a X : ℝ) : ℝ := (a + 1) - boseGrowth (Real.exp X)

theorem exp_exp_sub_one_ne_zero (X : ℝ) : Real.exp (Real.exp X) - 1 ≠ 0 := by
  have ht : (0:ℝ) < Real.exp X := Real.exp_pos X
  have h1 : (1:ℝ) < Real.exp (Real.exp X) := by
    have := Real.add_one_lt_exp (x := Real.exp X) (ne_of_gt ht)
    linarith
  linarith

theorem hasDerivAt_boseLogDensity (a X : ℝ) :
    HasDerivAt (boseLogDensity a) (boseLogScore a X) X := by
  have hden := exp_exp_sub_one_ne_zero X
  have h2 : HasDerivAt (fun Y : ℝ => Real.exp (Real.exp Y))
      (Real.exp (Real.exp X) * Real.exp X) X := HasDerivAt.exp (Real.hasDerivAt_exp X)
  have hu : HasDerivAt (fun Y : ℝ => Real.exp (Real.exp Y) - 1)
      (Real.exp (Real.exp X) * Real.exp X) X := h2.sub_const 1
  have hlog := hu.log hden
  have hlin : HasDerivAt (fun Y : ℝ => (a + 1) * Y) (a + 1) X := by
    simpa using (hasDerivAt_id X).const_mul (a + 1)
  have h := hlin.sub hlog
  have hval : (a + 1) - Real.exp (Real.exp X) * Real.exp X / (Real.exp (Real.exp X) - 1)
      = boseLogScore a X := by
    rw [boseLogScore, boseGrowth, Real.exp_neg]
    have hne : Real.exp (Real.exp X) ≠ 0 := (Real.exp_pos _).ne'
    congr 1
    field_simp
  rw [← hval]
  exact h

theorem deriv_boseLogDensity (a X : ℝ) :
    deriv (boseLogDensity a) X = boseLogScore a X :=
  (hasDerivAt_boseLogDensity a X).deriv

/-- **Exact second derivative.**  The Bose-log curvature is `-t g' t` at `t = exp X`. -/
theorem hasDerivAt_boseLogScore (a X : ℝ) :
    HasDerivAt (boseLogScore a) (-(Real.exp X * boseGrowthDeriv (Real.exp X))) X := by
  have hg := (hasDerivAt_boseGrowth (t := Real.exp X) (Real.exp_pos X)).comp X
    (Real.hasDerivAt_exp X)
  have hres : HasDerivAt (boseLogScore a)
      (0 - boseGrowthDeriv (Real.exp X) * Real.exp X) X := (hasDerivAt_const X (a + 1)).sub hg
  rw [show (0 : ℝ) - boseGrowthDeriv (Real.exp X) * Real.exp X
      = -(Real.exp X * boseGrowthDeriv (Real.exp X)) from by ring] at hres
  exact hres

theorem boseLogCurvature_neg (X : ℝ) :
    -(Real.exp X * boseGrowthDeriv (Real.exp X)) < 0 := by
  have h := boseGrowthDeriv_pos (t := Real.exp X) (Real.exp_pos X)
  have hx : (0:ℝ) < Real.exp X := Real.exp_pos X
  nlinarith

theorem strictAnti_boseLogScore (a : ℝ) : StrictAnti (boseLogScore a) := by
  intro x y hxy
  have hx : Real.exp x ∈ Ioi (0:ℝ) := Real.exp_pos x
  have hy : Real.exp y ∈ Ioi (0:ℝ) := Real.exp_pos y
  have h := strictMonoOn_boseGrowth hx hy (Real.exp_lt_exp.mpr hxy)
  rw [boseLogScore, boseLogScore]
  linarith

/-- **Strict log-concavity of the Bose-log law.**  Its log-density is strictly concave on the whole
real line, for every shift `a`. -/
theorem strictConcaveOn_boseLogDensity (a : ℝ) :
    StrictConcaveOn ℝ univ (boseLogDensity a) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv convex_univ ?_ ?_
  · intro X _
    exact ((hasDerivAt_boseLogDensity a X).continuousAt).continuousWithinAt
  · rw [interior_univ]
    have hderiv : deriv (boseLogDensity a) = boseLogScore a := by
      funext X
      exact deriv_boseLogDensity a X
    rw [hderiv]
    exact (strictAnti_boseLogScore a).strictAntiOn univ

end

end GaloisForLFunctions.HTGeometry
