import GaloisForLFunctions.RHTower.Sieve.LorentzianMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly

/-!
# The Lorentzian mean value theorem in the Dirichlet frequency variable

The Gallagher polynomial `logPoly a (Icc 1 N) w = ∑_{n ≤ N} a_n n^{2πiw}` is the Dirichlet polynomial
`dirPoly N a' (2πw)`, so the parameter-free Lorentzian mean value theorem transfers to the frequency
variable in which every vertical-line estimate of the corpus is stated:

`∫_ℝ ‖∑_{n ≤ N} a_n n^{it}‖² dt/(1+t²) ≤ 25π² ∑_{n ≤ N} ‖a_n‖² · #{m ≤ N : |log n - log m| < 1/(2π)}`.

The substitution `t = 2πw` costs the factor `2π`, and the weight improves rather than degrades:
`1 + 4π²w² ≥ 1 + w²`.  This is the form the sharp Perron kernel `1/s` consumes on the line, and the
right-hand side is sharp for a sparse support — for the primes the neighbour count is `O(1)` at unit
scale, while the classical mean value theorem's error term `O(N ∑‖a_n‖²)` is blind to the support.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Set Finset

/-- **The Lorentzian mean value theorem, Dirichlet form.** -/
theorem integral_lorentz_normSq_dirPoly_le_count (a : ℕ → ℂ) (N : ℕ) :
    (∫ t : ℝ, ‖dirPoly N (fun n : Fin N => a ((n : ℕ) + 1)) t‖ ^ (2 : ℕ) / (1 + t ^ (2 : ℕ)))
      ≤ 25 * Real.pi ^ (2 : ℕ)
          * ∑ n ∈ Finset.Icc 1 N,
              (logNeighbourCount (Finset.Icc 1 N) (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set c : Fin N → ℂ := fun n : Fin N => a ((n : ℕ) + 1) with hc
  set g : ℝ → ℝ := fun t => ‖dirPoly N c t‖ ^ (2 : ℕ) / (1 + t ^ (2 : ℕ)) with hg
  set L : ℝ → ℝ := fun w => ‖logPoly a (Finset.Icc 1 N) w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)) with hL
  have hLint : Integrable L := integrable_lorentz_normSq_logPoly a (Finset.Icc 1 N)
  -- the substitution `t = 2πw`
  have hsubst : (∫ t : ℝ, g t) = 2 * Real.pi * ∫ w : ℝ, g (2 * Real.pi * w) := by
    have h := MeasureTheory.Measure.integral_comp_mul_left g (2 * Real.pi)
    rw [smul_eq_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
    rw [h]
    field_simp
  -- pointwise the scaled integrand is dominated by the Gallagher integrand
  have hpoint : ∀ w : ℝ, g (2 * Real.pi * w) ≤ L w := by
    intro w
    have hpoly : dirPoly N c (2 * Real.pi * w) = logPoly a (Finset.Icc 1 N) w :=
      (logPoly_eq_dirPoly a N w).symm
    have hnum : (0 : ℝ) ≤ ‖logPoly a (Finset.Icc 1 N) w‖ ^ (2 : ℕ) := by positivity
    have hd1 : (0 : ℝ) < 1 + w ^ (2 : ℕ) := by positivity
    have hd2 : (0 : ℝ) < 1 + (2 * Real.pi * w) ^ (2 : ℕ) := by positivity
    have hcmp : 1 + w ^ (2 : ℕ) ≤ 1 + (2 * Real.pi * w) ^ (2 : ℕ) := by
      have hpi3 : (3 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      have hsq : (1 : ℝ) ≤ (2 * Real.pi) ^ (2 : ℕ) := by nlinarith [hpi3]
      have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg w)
      rw [one_mul] at hmul
      have hexp : (2 * Real.pi * w) ^ (2 : ℕ) = (2 * Real.pi) ^ (2 : ℕ) * w ^ (2 : ℕ) := by ring
      rw [hexp]
      linarith [hmul]
    rw [hg, hL]
    simp only [hpoly]
    exact div_le_div_of_nonneg_left hnum hd1 hcmp
  -- the scaled integrand is integrable
  have hgint : Integrable fun w : ℝ => g (2 * Real.pi * w) := by
    refine Integrable.mono' hLint ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      refine Continuous.div ?_ (by fun_prop) fun w => by positivity
      exact (((continuous_dirPoly N c).norm).pow 2).comp (by fun_prop)
    · filter_upwards with w
      have h0 : (0 : ℝ) ≤ g (2 * Real.pi * w) := by
        rw [hg]
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hpoint w
  have hmono : (∫ w : ℝ, g (2 * Real.pi * w)) ≤ ∫ w : ℝ, L w :=
    integral_mono hgint hLint hpoint
  have hmain := integral_lorentz_normSq_logPoly_le_count a (Finset.Icc 1 N)
  have hCnn : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N,
      (logNeighbourCount (Finset.Icc 1 N) (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun n _ => by positivity
  rw [hsubst]
  have hstep : 2 * Real.pi * ∫ w : ℝ, g (2 * Real.pi * w)
      ≤ 2 * Real.pi * ((25 * Real.pi / 2)
          * ∑ n ∈ Finset.Icc 1 N,
              (logNeighbourCount (Finset.Icc 1 N) (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ)) := by
    refine mul_le_mul_of_nonneg_left (hmono.trans ?_) (by positivity)
    exact hmain
  refine hstep.trans (le_of_eq ?_)
  ring

end RHTower.Sieve

end
