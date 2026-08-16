import GaloisForLFunctions.RHTower.BurnolGlasserIntegral

/-!
# The positive subordination kernel of the massive half-wave

The square-root Laplace identity turns the massive half-wave factor `e^{2a²t}e^{-2at√(a²+w)}` into
the Laplace transform of an explicit positive kernel concentrated at `s = t`:

`K_{a,t}(s) = (at/√π) s^{-3/2} exp(-a²(s-t)²/s)`,  `K_{a,t} ≥ 0`,  `∫₀^∞ K_{a,t} = 1`.

So the massive propagation has the Gaussian heat semigroup as its parabolic tangent, and the mass
jet of a heat test is an average of the test against a probability kernel.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- The subordination kernel of the massive half-wave. -/
def massSubordinationKernel (a t s : ℝ) : ℝ :=
  a * t / Real.sqrt Real.pi * s ^ (-(3 : ℝ) / 2) * Real.exp (-(a ^ 2 * (s - t) ^ 2 / s))

theorem massSubordinationKernel_nonneg {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) {s : ℝ}
    (hs : 0 < s) : 0 ≤ massSubordinationKernel a t s := by
  rw [massSubordinationKernel]
  have h1 : (0 : ℝ) ≤ s ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hs.le _
  have h2 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have h3 : (0 : ℝ) ≤ a * t / Real.sqrt Real.pi := by positivity
  positivity

/-- **(24.110) The exact subordination law.** -/
theorem massSubordinationKernel_laplace {a t w : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hlam : 0 < a ^ 2 + w) :
    Real.exp (2 * a ^ 2 * t) * Real.exp (-(2 * a * t * Real.sqrt (a ^ 2 + w)))
      = ∫ s in Ioi (0 : ℝ), massSubordinationKernel a t s * Real.exp (-(s * w)) := by
  have hy : (0 : ℝ) < 2 * a * t := by positivity
  have hcorpus := burnolPoissonSubordination (y := 2 * a * t) (lam := a ^ 2 + w) hy hlam
  have hpull : Real.exp (2 * a ^ 2 * t) * (2 * a * t / (2 * Real.sqrt Real.pi)
      * ∫ s in Ioi (0 : ℝ), burnolSubordinationIntegrand (2 * a * t) (a ^ 2 + w) s)
      = ∫ s in Ioi (0 : ℝ), (Real.exp (2 * a ^ 2 * t) * (2 * a * t / (2 * Real.sqrt Real.pi)))
          * burnolSubordinationIntegrand (2 * a * t) (a ^ 2 + w) s := by
    rw [MeasureTheory.integral_const_mul]
    ring
  rw [hcorpus, hpull]
  refine setIntegral_congr_fun (measurableSet_Ioi (a := (0:ℝ))) fun s hs => ?_
  have hspos : (0 : ℝ) < s := hs
  rw [massSubordinationKernel, burnolSubordinationIntegrand]
  have hexp : Real.exp (2 * a ^ 2 * t) * Real.exp (-((2 * a * t) ^ 2 / (4 * s)))
      * Real.exp (-(s * (a ^ 2 + w)))
      = Real.exp (-(a ^ 2 * (s - t) ^ 2 / s)) * Real.exp (-(s * w)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  calc Real.exp (2 * a ^ 2 * t) * (2 * a * t / (2 * Real.sqrt Real.pi))
        * (s ^ (-(3 : ℝ) / 2) * Real.exp (-((2 * a * t) ^ 2 / (4 * s)))
            * Real.exp (-(s * (a ^ 2 + w))))
      = a * t / Real.sqrt Real.pi * s ^ (-(3 : ℝ) / 2)
          * (Real.exp (2 * a ^ 2 * t) * Real.exp (-((2 * a * t) ^ 2 / (4 * s)))
            * Real.exp (-(s * (a ^ 2 + w)))) := by
        have hpi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
        field_simp
    _ = a * t / Real.sqrt Real.pi * s ^ (-(3 : ℝ) / 2)
          * (Real.exp (-(a ^ 2 * (s - t) ^ 2 / s)) * Real.exp (-(s * w))) := by rw [hexp]
    _ = a * t / Real.sqrt Real.pi * s ^ (-(3 : ℝ) / 2)
          * Real.exp (-(a ^ 2 * (s - t) ^ 2 / s)) * Real.exp (-(s * w)) := by ring

/-- **(24.111) The kernel is a probability density.** -/
theorem massSubordinationKernel_integral_one {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (∫ s in Ioi (0 : ℝ), massSubordinationKernel a t s) = 1 := by
  have hlam : (0 : ℝ) < a ^ 2 + 0 := by positivity
  have h := massSubordinationKernel_laplace ha ht hlam
  have hsqrt : Real.sqrt (a ^ 2 + 0) = a := by
    rw [add_zero, Real.sqrt_sq ha.le]
  rw [hsqrt] at h
  have hone : Real.exp (2 * a ^ 2 * t) * Real.exp (-(2 * a * t * a)) = 1 := by
    rw [← Real.exp_add]
    have : 2 * a ^ 2 * t + -(2 * a * t * a) = 0 := by ring
    rw [this, Real.exp_zero]
  rw [hone] at h
  have hid : (∫ s in Ioi (0 : ℝ), massSubordinationKernel a t s * Real.exp (-(s * 0)))
      = ∫ s in Ioi (0 : ℝ), massSubordinationKernel a t s := by
    refine setIntegral_congr_fun (measurableSet_Ioi (a := (0:ℝ))) fun s _ => ?_
    simp
  rw [hid] at h
  exact h.symm

end

end RHTower
