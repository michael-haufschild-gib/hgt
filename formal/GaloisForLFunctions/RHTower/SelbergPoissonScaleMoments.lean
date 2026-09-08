import GaloisForLFunctions.HTGeometry.FrullaniIntegral
import GaloisForLFunctions.RHTower.DeningerMultiplier

/-!
# Scale moments of a dyadic Poisson response

For logarithmic rate `s`, the positive rate is `exp s`. The actual dyadic
response `exp(-t*exp s)-exp(-2*t*exp s)` has squared integral `log(9/8)` in the
measure `dt/t`, independent of the rate. Its squared integral in `dt` is
`1/(12*exp s)`, which determines the rate and ranges over all positive reals.

Integrability and both set-integral evaluations are proved. The response is
also identified with the existing diagonal Poisson multiplier. These results
separate a scale-invariant norm detector from a rate-sensitive moment; neither
provides an arithmetic bound on the latter or a congruence Maass spectral gap.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower.SelbergPoissonScaleMoments
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- Dyadic difference of two real exponential semigroup multipliers. -/
def difference (r t : ℝ) : ℝ := Real.exp (-(r * t)) - Real.exp (-(2 * r * t))

/-- Squared response at logarithmic rate `s`, integrated in logarithmic scale. -/
def logScaleEnergy (s : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), difference (Real.exp s) t ^ 2 / t

/-- Squared response at logarithmic rate `s`, integrated in ordinary scale. -/
def ordinaryScaleEnergy (s : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), difference (Real.exp s) t ^ 2

private def realFrullani (a b t : ℝ) : ℝ :=
  (Real.exp (-(a * t)) - Real.exp (-(b * t))) / t

private theorem realFrullani_eq_re (a b t : ℝ) :
    realFrullani a b t =
      ((Complex.exp (-((a : ℂ) * t)) - Complex.exp (-((b : ℂ) * t))) / (t : ℂ)).re := by
  simp [realFrullani, Complex.exp_re]

private theorem realFrullani_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (realFrullani a b) (Ioi (0 : ℝ)) := by
  have h := (integrableOn_frullani (a := (a : ℂ)) (b := (b : ℂ))
    (by simpa using ha) (by simpa using hb)).re
  change Integrable (realFrullani a b) (volume.restrict (Ioi (0 : ℝ)))
  convert h using 1
  funext t
  exact realFrullani_eq_re a b t

private theorem integral_realFrullani {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), realFrullani a b t) = Real.log b - Real.log a := by
  have hc := integrableOn_frullani (a := (a : ℂ)) (b := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have he := integral_frullani (a := (a : ℂ)) (b := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  simp_rw [realFrullani_eq_re]
  calc
    _ = ((∫ t in Ioi (0 : ℝ),
        (Complex.exp (-((a : ℂ) * t)) - Complex.exp (-((b : ℂ) * t))) / (t : ℂ)) : ℂ).re := by
      convert integral_re hc using 1 <;> rfl
    _ = _ := by
      rw [he]
      simp [Complex.log_re, abs_of_pos ha, abs_of_pos hb]

/-- Exact three-exponential expansion of the squared dyadic response. -/
theorem difference_sq (r t : ℝ) :
    difference r t ^ 2 =
      Real.exp (-(2 * r * t)) - 2 * Real.exp (-(3 * r * t)) +
        Real.exp (-(4 * r * t)) := by
  have h₂ : Real.exp (-(2 * r * t)) = Real.exp (-(r * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h₃ : Real.exp (-(3 * r * t)) =
      Real.exp (-(r * t)) * Real.exp (-(2 * r * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₄ : Real.exp (-(4 * r * t)) = Real.exp (-(2 * r * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h₃, h₄, h₂]
  unfold difference
  rw [h₂]
  ring

private theorem logScale_split (r : ℝ) :
    (fun t => difference r t ^ 2 / t) =
      (fun t => realFrullani (2 * r) (3 * r) t + realFrullani (4 * r) (3 * r) t) := by
  funext t
  rw [difference_sq]
  unfold realFrullani
  ring

/-- The logarithmic-scale integrand is integrable on the positive ray. -/
theorem logScale_integrable (s : ℝ) :
    IntegrableOn (fun t => difference (Real.exp s) t ^ 2 / t) (Ioi (0 : ℝ)) := by
  rw [logScale_split]
  exact (realFrullani_integrable (by positivity) (by positivity)).add
    (realFrullani_integrable (by positivity) (by positivity))

/-- Every positive rate has exactly the same logarithmic-scale energy. -/
theorem logScaleEnergy_eq (s : ℝ) : logScaleEnergy s = Real.log (9 / 8 : ℝ) := by
  unfold logScaleEnergy
  rw [logScale_split, integral_add
    (realFrullani_integrable (by positivity) (by positivity))
    (realFrullani_integrable (by positivity) (by positivity)),
    integral_realFrullani (by positivity) (by positivity),
    integral_realFrullani (by positivity) (by positivity)]
  rw [← Real.log_div (by positivity) (by positivity),
    ← Real.log_div (by positivity) (by positivity),
    ← Real.log_mul (by positivity) (by positivity)]
  congr 1
  field_simp [(Real.exp_pos s).ne']
  ring

private theorem expRate_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t => Real.exp (-(r * t))) (Ioi (0 : ℝ)) := by
  simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hr

private theorem integral_expRate {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(r * t))) = 1 / r := by
  simpa only [neg_mul, mul_zero, Real.exp_zero, neg_div_neg_eq] using
    integral_exp_mul_Ioi (a := -r) (by linarith) 0

/-- The ordinary-scale squared response is integrable on the positive ray. -/
theorem ordinaryScale_integrable (s : ℝ) :
    IntegrableOn (fun t => difference (Real.exp s) t ^ 2) (Ioi (0 : ℝ)) := by
  simp_rw [difference_sq]
  exact ((expRate_integrable (by positivity)).sub
    ((expRate_integrable (by positivity)).const_mul 2)).add
    (expRate_integrable (by positivity))

/-- The ordinary-scale moment is exactly the reciprocal rate divided by twelve. -/
theorem ordinaryScaleEnergy_eq (s : ℝ) : ordinaryScaleEnergy s = 1 / (12 * Real.exp s) := by
  unfold ordinaryScaleEnergy
  simp_rw [difference_sq]
  have h₂ := expRate_integrable (r := 2 * Real.exp s) (by positivity)
  have h₃ := expRate_integrable (r := 3 * Real.exp s) (by positivity)
  have h₄ := expRate_integrable (r := 4 * Real.exp s) (by positivity)
  have hadd := integral_add (h₂.sub (h₃.const_mul 2)) h₄
  have hsub := integral_sub h₂ (h₃.const_mul 2)
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul,
    integral_expRate (by positivity), integral_expRate (by positivity),
    integral_expRate (by positivity)]
  field_simp [(Real.exp_pos s).ne']
  ring

/-- The ordinary-scale moment recovers the positive rate exactly. -/
theorem ordinaryScale_rate_recovery (s : ℝ) :
    Real.exp s * ordinaryScaleEnergy s = 1 / 12 := by
  rw [ordinaryScaleEnergy_eq]
  field_simp [(Real.exp_pos s).ne']

/-- Distinct logarithmic rates have distinct ordinary-scale moments. -/
theorem ordinaryScaleEnergy_injective : Function.Injective ordinaryScaleEnergy := by
  intro s t h
  rw [ordinaryScaleEnergy_eq, ordinaryScaleEnergy_eq] at h
  have he : Real.exp s = Real.exp t := by
    field_simp [(Real.exp_pos s).ne', (Real.exp_pos t).ne'] at h
    linarith
  exact Real.exp_injective he

/-- Logarithmic-scale integration erases all positive-rate information. -/
theorem logScaleEnergy_same (s t : ℝ) : logScaleEnergy s = logScaleEnergy t := by
  rw [logScaleEnergy_eq, logScaleEnergy_eq]

/-- The logarithmic-scale moment cannot separate logarithmic rates. -/
theorem logScaleEnergy_not_injective : ¬ Function.Injective logScaleEnergy := by
  intro h
  exact zero_ne_one (h (logScaleEnergy_same 0 1))

/-- The ordinary-scale moment is strictly positive. -/
theorem ordinaryScaleEnergy_pos (s : ℝ) : 0 < ordinaryScaleEnergy s := by
  rw [ordinaryScaleEnergy_eq]
  positivity

/-- An explicit parameter produces every exponential moment value. -/
theorem ordinaryScaleEnergy_reparametrize (s : ℝ) :
    ordinaryScaleEnergy (-(s + Real.log 12)) = Real.exp s := by
  rw [ordinaryScaleEnergy_eq, Real.exp_neg, Real.exp_add, Real.exp_log (by positivity)]
  field_simp [(Real.exp_pos s).ne']

/-- The ordinary-scale moment ranges over exactly the positive real numbers. -/
theorem range_ordinaryScaleEnergy : Set.range ordinaryScaleEnergy = Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ordinaryScaleEnergy_pos s
  · intro hy
    refine ⟨-(Real.log y + Real.log 12), ?_⟩
    rw [ordinaryScaleEnergy_reparametrize, Real.exp_log hy]

/-- No uniform upper bound holds over unrestricted positive semigroup rates. -/
theorem ordinaryScaleEnergy_no_uniform_bound :
    ¬ ∃ b : ℝ, ∀ s : ℝ, ordinaryScaleEnergy s ≤ b := by
  rintro ⟨b, hb⟩
  have hmem : b ^ 2 + 1 ∈ Set.range ordinaryScaleEnergy := by
    rw [range_ordinaryScaleEnergy]
    exact show 0 < b ^ 2 + 1 by positivity
  obtain ⟨s, hs⟩ := hmem
  have h := hb s
  rw [hs] at h
  nlinarith [sq_nonneg (b - 1 / 2)]

/-- The response is the actual dyadic difference of the corpus Poisson multiplier. -/
theorem difference_eq_poissonMultiplier (s t : ℝ) :
    (difference (Real.exp s) t : ℂ) =
      _root_.RHTower.deningerPoissonMultiplier (fun _ : Unit => Real.exp s) t () -
        _root_.RHTower.deningerPoissonMultiplier (fun _ : Unit => Real.exp s) (2 * t) () := by
  simp only [difference, _root_.RHTower.deningerPoissonMultiplier,
    abs_of_pos (Real.exp_pos s)]
  push_cast
  congr 2 <;> ring

end
end GaloisForLFunctions.RHTower.SelbergPoissonScaleMoments
