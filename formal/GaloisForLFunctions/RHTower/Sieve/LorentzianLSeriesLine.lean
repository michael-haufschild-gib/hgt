import GaloisForLFunctions.RHTower.Sieve.LorentzianPrimeSupport
import GaloisForLFunctions.RHTower.Sieve.DistanceAbscissaBridge
import Mathlib.NumberTheory.LSeries.Basic

/-!
# The mean square of a Dirichlet series on a vertical line

A Dirichlet series with finite support is a Dirichlet polynomial: on the line `Re s = σ`,

`L(a, σ+iy) = ∑_{n ∈ s} a_n n^{-σ} · n^{-iy}`,

which is the Gallagher polynomial of the damped coefficients at frequency `-y/2π`.  The reflection and
rescaling `y = -2πw` carries the Lorentzian weight `1/(1+y²)` to `2π/(1+4π²w²)`, dominated by
`2π/(1+w²)`, so the parameter-free Lorentzian mean value theorem transfers to the frequency variable of
the Perron integral:

`∫_ℝ ‖L(a, σ+iy)‖² dy/(1+y²) ≤ 25π² ∑_{n ∈ s} #{m ∈ s : |log n − log m| < 1/2π} · ‖a_n n^{-σ}‖²`,

and for coefficients supported on primes the neighbour count is a short-interval prime count, discharged by
the Selberg sieve.  This is GHS Lemma 1 in the variable in which the Perron passage delivers its integral.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Finset

/-- One term of a Dirichlet series on a vertical line, split into modulus and phase: the polar split of
`DistanceAbscissaBridge`, written in the frequency convention of the Gallagher polynomial. -/
theorem natCast_cpow_neg_eq {n : ℕ} (hn : 1 ≤ n) (σ y : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I))
      = ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)
          * Complex.exp (((2 * Real.pi * ((-y / (2 * Real.pi)) * Real.log n) : ℝ) : ℂ) * I) := by
  have hn0 : 0 < n := by omega
  have hre : ((σ : ℂ) + (y : ℝ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (y : ℝ) * I).im = y := by simp
  have hsplit := natCast_cpow_neg_eq_mul ((σ : ℂ) + (y : ℝ) * I) hn0
  rw [hre, him, conj_charFn] at hsplit
  rw [hsplit]
  congr 2
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

/-- **A finitely supported Dirichlet series is a Dirichlet polynomial.**  On the line `Re s = σ` the
series is the Gallagher polynomial of the damped coefficients `a_n n^{-σ}` at frequency `-y/2π`. -/
theorem LSeries_eq_logPoly_of_support {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ y : ℝ) :
    LSeries a ((σ : ℂ) + (y : ℝ) * I)
      = logPoly (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s (-y / (2 * Real.pi)) := by
  classical
  rw [LSeries]
  have hzero : ∀ n : ℕ, n ∉ s → LSeries.term a ((σ : ℂ) + (y : ℝ) * I) n = 0 := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [LSeries.term_def, if_pos rfl]
    · have ha : a n = 0 := by
        by_contra hne
        exact hn (hsupp n hne)
      rw [LSeries.term_def, if_neg hn0, ha, zero_div]
  rw [tsum_eq_sum hzero, logPoly]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := fun h => hs0 (h ▸ hn)
  have hn1 : 1 ≤ n := by omega
  rw [LSeries.term_def, if_neg hn0, div_eq_mul_inv, ← Complex.cpow_neg,
    natCast_cpow_neg_eq hn1 σ y]
  ring

/-- **The Lorentzian integral in a reflected and rescaled frequency.**  Substituting `y = -2πw` turns the
weight `1/(1+y²)` into `2π/(1+4π²w²)`, which the weight `1/(1+w²)` dominates. -/
theorem integral_lorentz_comp_neg_div_le {F : ℝ → ℝ} (hFnn : ∀ w, 0 ≤ F w) (hFc : Continuous F)
    (hFint : Integrable fun w : ℝ => F w / (1 + w ^ 2)) :
    (∫ y : ℝ, F (-y / (2 * Real.pi)) / (1 + y ^ 2))
      ≤ 2 * Real.pi * ∫ w : ℝ, F w / (1 + w ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set G : ℝ → ℝ := fun y => F (-y / (2 * Real.pi)) / (1 + y ^ 2) with hG
  have hcomp : ∀ w : ℝ, G (-(2 * Real.pi) * w) = F w / (1 + 4 * Real.pi ^ 2 * w ^ 2) := by
    intro w
    rw [hG]
    dsimp only
    have harg : -(-(2 * Real.pi) * w) / (2 * Real.pi) = w := by
      field_simp
    have hden : (1 : ℝ) + (-(2 * Real.pi) * w) ^ 2 = 1 + 4 * Real.pi ^ 2 * w ^ 2 := by ring
    rw [harg, hden]
  have hchange : (∫ y : ℝ, G y) = 2 * Real.pi * ∫ w : ℝ, G (-(2 * Real.pi) * w) := by
    have h := MeasureTheory.Measure.integral_comp_mul_left G (-(2 * Real.pi))
    rw [smul_eq_mul, abs_inv, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
    rw [h]
    field_simp
  have hdom : ∀ w : ℝ, F w / (1 + 4 * Real.pi ^ 2 * w ^ 2) ≤ F w / (1 + w ^ 2) := by
    intro w
    have hpi3 : (3 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hsq : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [hpi3]
    have hmul : w ^ 2 ≤ 4 * Real.pi ^ 2 * w ^ 2 := by nlinarith [sq_nonneg w]
    exact div_le_div_of_nonneg_left (hFnn w) (by positivity) (by linarith)
  have hint2 : Integrable fun w : ℝ => F w / (1 + 4 * Real.pi ^ 2 * w ^ 2) := by
    refine Integrable.mono' hFint ?_ ?_
    · exact (hFc.div (by fun_prop) fun w => by positivity).aestronglyMeasurable
    · filter_upwards with w
      have h0 : (0 : ℝ) ≤ F w / (1 + 4 * Real.pi ^ 2 * w ^ 2) := by
        have := hFnn w
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hdom w
  have hmono : (∫ w : ℝ, F w / (1 + 4 * Real.pi ^ 2 * w ^ 2)) ≤ ∫ w : ℝ, F w / (1 + w ^ 2) :=
    MeasureTheory.integral_mono hint2 hFint hdom
  rw [hG] at hchange ⊢
  rw [hchange]
  have hcongr : (∫ w : ℝ, (fun y => F (-y / (2 * Real.pi)) / (1 + y ^ 2)) (-(2 * Real.pi) * w))
      = ∫ w : ℝ, F w / (1 + 4 * Real.pi ^ 2 * w ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    exact hcomp w
  rw [hcongr]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **The mean square of a finitely supported Dirichlet series on a vertical line.**  In the frequency
variable of the Perron integral, with the Lorentzian weight, against the almost-diagonal count of the
damped coefficients. -/
theorem integral_lorentz_normSq_LSeries_le_count {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ : ℝ) :
    (∫ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 / (1 + y ^ 2))
      ≤ 25 * Real.pi ^ 2 * ∑ n ∈ s,
          (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ)
            * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 := by
  classical
  set c : ℕ → ℂ := fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ) with hc
  set F : ℝ → ℝ := fun w => ‖logPoly c s w‖ ^ 2 with hF
  have hcongr : ∀ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 / (1 + y ^ 2)
      = F (-y / (2 * Real.pi)) / (1 + y ^ 2) := by
    intro y
    rw [hF, LSeries_eq_logPoly_of_support hs0 hsupp σ y]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)]
  have hstep := integral_lorentz_comp_neg_div_le (F := F) (fun w => by rw [hF]; positivity)
    (continuous_normSq_logPoly c s) (integrable_lorentz_normSq_logPoly c s)
  refine hstep.trans ?_
  have hmain := integral_lorentz_normSq_logPoly_le_count c s
  have h2 : 2 * Real.pi * ∫ w : ℝ, F w / (1 + w ^ 2)
      ≤ 2 * Real.pi * ((25 * Real.pi / 2)
          * ∑ n ∈ s, (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) * ‖c n‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hmain (by positivity)
  refine h2.trans (le_of_eq ?_)
  rw [hc]
  ring

/-- **GHS Lemma 1 on the Perron line.**  For a prime-supported finite coefficient sequence the mean square
of the Dirichlet series along the line `Re s = σ`, weighted by the Lorentzian kernel, is bounded by the
damped coefficients weighted by a short-interval prime count. -/
theorem integral_lorentz_normSq_LSeries_le_prime_sieve {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (hprime : ∀ n ∈ s, a n ≠ 0 → n.Prime) (σ : ℝ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    (∫ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 / (1 + y ^ 2))
      ≤ 25 * Real.pi ^ 2 * ∑ n ∈ s,
          (2 * ((n : ℝ) * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
              / Real.log Y
            + selbergFibreError z Y + (z : ℝ))
            * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 := by
  classical
  set c : ℕ → ℂ := fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ) with hc
  set F : ℝ → ℝ := fun w => ‖logPoly c s w‖ ^ 2 with hF
  have hcongr : ∀ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 / (1 + y ^ 2)
      = F (-y / (2 * Real.pi)) / (1 + y ^ 2) := by
    intro y
    rw [hF, LSeries_eq_logPoly_of_support hs0 hsupp σ y]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)]
  have hstep := integral_lorentz_comp_neg_div_le (F := F) (fun w => by rw [hF]; positivity)
    (continuous_normSq_logPoly c s) (integrable_lorentz_normSq_logPoly c s)
  refine hstep.trans ?_
  have hcprime : ∀ n ∈ s, c n ≠ 0 → n.Prime := by
    intro n hn hcn
    refine hprime n hn ?_
    intro han
    rw [hc] at hcn
    simp only [han, zero_mul] at hcn
    exact hcn rfl
  have hmain := integral_lorentz_normSq_logPoly_le_prime_sieve c s hcprime z Y hY hYz hz hlog
  have h2 : 2 * Real.pi * ∫ w : ℝ, F w / (1 + w ^ 2)
      ≤ 2 * Real.pi * ((25 * Real.pi / 2) * ∑ n ∈ s,
          (2 * ((n : ℝ) * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
              / Real.log Y
            + selbergFibreError z Y + (z : ℝ)) * ‖c n‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hmain (by positivity)
  refine h2.trans (le_of_eq ?_)
  rw [hc]
  ring

end RHTower.Sieve
end
