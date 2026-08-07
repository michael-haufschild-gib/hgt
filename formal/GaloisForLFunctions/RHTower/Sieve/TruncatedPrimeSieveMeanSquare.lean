import GaloisForLFunctions.RHTower.Sieve.TruncatedMeanSquareChange
import GaloisForLFunctions.RHTower.Sieve.LorentzianPrimeSupport
/-!
# The truncated mean square of a prime-supported series, on the Perron line

Transported to the Gallagher variable and cut down to the primes, the truncated mean square is the corpus's
window mean value theorem at the neighbour scale the truncation forces:

`∫_{|y| ≤ T} ‖L(a,σ+iy)‖² dy ≤ 2π·(5T/4)·∑_{n} (2(n(e^{1/T} − e^{−1/T}) + 1)/log Y + E + z)·‖a_n n^{−σ}‖²`.

The scale is sharp: the window theorem's hypothesis `2πδW ≤ 1` at `W = T/2π` is an *equality* when `δ = 1/T`,
so the height of the truncation and the width of the multiplicative window are reciprocal.  Two consequences
worth noting.  The factor `5T/4` in front is cancelled by the `e^{1/T} − e^{−1/T} ≍ 2/T` inside, so the leading
term `≍ ∑_n n‖a_n n^{−σ}‖²/log Y` is *independent of `T`*; and what does grow with `T` is only the additive
part `(5T/4)(E + z)∑‖a_n n^{−σ}‖²`, so `T` may be taken large as long as `T(E+z)` stays below the leading term.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Finset

/-- **The truncated mean square of a prime-supported Dirichlet series on the Perron line.**  The window mean
value theorem at the neighbour scale `δ = 1/T` forced by the truncation height, with its count discharged by
the Selberg sieve.  The scale is the sharp one: `2πδW ≤ 1` with `W = T/2π` is an equality at `δ = 1/T`, so a
high truncation gives a narrow multiplicative window. -/
theorem integral_Icc_normSq_LSeries_le_prime_sieve {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (hprime : ∀ n ∈ s, a n ≠ 0 → n.Prime) (σ : ℝ)
    {T : ℝ} (hT : 0 < T) (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z)
    (hlog : 0 < Real.log Y) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ 2 * Real.pi * ((5 * T / 4) * ∑ n ∈ s,
          (2 * ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) + 1) / Real.log Y
            + selbergFibreError z Y + (z : ℝ))
              * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) := by
  classical
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set c : ℕ → ℂ := fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ) with hc
  set s' : Finset ℕ := {n ∈ s | c n ≠ 0} with hs'
  have hδ : (0 : ℝ) < 1 / T := by positivity
  have hWδ : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) ≤ 1 := by
    rw [show 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) = 1 by field_simp]
  have hprime' : ∀ m ∈ s', m.Prime := by
    intro m hm
    rw [hs', Finset.mem_filter] at hm
    refine hprime m hm.1 ?_
    intro hane
    rw [hc] at hm
    simp only [hane, zero_mul] at hm
    exact hm.2 rfl
  -- move to the Gallagher variable and drop the vanishing coefficients
  rw [integral_Icc_normSq_LSeries_eq hs0 hsupp σ hT.le]
  have hcongr : ∀ w : ℝ, ‖logPoly c s w‖ ^ 2 = ‖logPoly c s' w‖ ^ 2 := by
    intro w
    rw [hs', logPoly_eq_logPoly_filter c s w]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)]
  refine mul_le_mul_of_nonneg_left ?_ hpi.le
  refine le_trans (integral_Icc_normSq_logPoly_le_prime_sieve c s' hprime' hδ hWδ z Y hY hYz hz
    hlog) ?_
  have hfac : (5 : ℝ) / (4 * (1 / T)) = 5 * T / 4 := by
    field_simp
  rw [hfac]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsub : s' ⊆ s := by
    rw [hs']
    exact Finset.filter_subset _ _
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
  have herr : 0 ≤ selbergFibreError z Y := selbergFibreError_nonneg hz Y
  have hzR : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  have hS : Real.exp (-(1 / T)) ≤ Real.exp (1 / T) := Real.exp_le_exp.2 (by linarith)
  have hnum : (0 : ℝ) ≤ 2 * ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) + 1) := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : (0 : ℝ) ≤ (n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) :=
      mul_nonneg hnn (by linarith)
    linarith
  have hcount : (0 : ℝ) ≤ 2 * ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) + 1)
      / Real.log Y + selbergFibreError z Y + (z : ℝ) := by
    have := div_nonneg hnum hlog.le
    linarith
  positivity

end RHTower.Sieve
end
