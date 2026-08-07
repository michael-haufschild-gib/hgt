import GaloisForLFunctions.RHTower.Sieve.LorentzianLSeriesLine
/-!
# The truncated mean square in the two frequency variables

The Perron passage delivers its integral in `y`, where the frequency is `n^{−iy}`; the corpus's truncated mean
value theorem is stated in `w`, where it is `n^{2πiw}`.  On a symmetric interval the substitution `y = −2πw`
carries one to the other exactly:

`∫_{|y| ≤ T} ‖L(a,σ+iy)‖² dy = 2π ∫_{|w| ≤ T/2π} ‖logPoly (a_n n^{−σ}) s w‖² dw`,

the reflection being absorbed by the symmetry of the interval and the scaling costing the Jacobian `2π`.  This
is the truncated counterpart of the reflection-and-rescaling used for the Lorentzian weight, and it is what
lets the truncated route use the corpus's window mean value theorem.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The truncated mean square in the two frequency variables.**  The substitution `y = −2πw` carries the
Perron variable to the Gallagher variable, the symmetric interval `|y| ≤ T` to `|w| ≤ T/2π`, and costs the
Jacobian `2π`. -/
theorem integral_Icc_normSq_LSeries_eq {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      = 2 * Real.pi * ∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
          ‖logPoly (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s w‖ ^ 2 := by
  classical
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set c : ℕ → ℂ := fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ) with hc
  set G : ℝ → ℝ := fun w => ‖logPoly c s w‖ ^ 2 with hG
  have hTT : -T ≤ T := by linarith
  have hTT' : -(T / (2 * Real.pi)) ≤ T / (2 * Real.pi) := by
    have : (0 : ℝ) ≤ T / (2 * Real.pi) := by positivity
    linarith
  -- the integrand in the Perron variable
  have hpt : ∀ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 = G (-y / (2 * Real.pi)) := by
    intro y
    rw [hG, LSeries_eq_logPoly_of_support hs0 hsupp σ y]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hTT,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hTT']
  rw [intervalIntegral.integral_congr (g := fun y => G (-y / (2 * Real.pi)))
    (fun y _ => hpt y)]
  have hcongr2 : (∫ y in (-T)..T, G (-y / (2 * Real.pi)))
      = ∫ y in (-T)..T, G (-(y / (2 * Real.pi))) := by
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [neg_div]
  rw [hcongr2, intervalIntegral.integral_comp_div (fun u => G (-u)) hpi.ne',
    intervalIntegral.integral_comp_neg G, smul_eq_mul]
  have hend : -(-T / (2 * Real.pi)) = T / (2 * Real.pi) := by ring
  rw [hend]

end RHTower.Sieve
end
