import Mathlib.Analysis.Real.Pi.Wallis

/-!
# Wallis surplus of the paired-eta logarithmic support

In cell `n`, the eta support occupies `(log(2n+1), log(2n+2)]` and the
following gap occupies `(log(2n+2), log(2n+3)]`.  Half the difference of
their log-lengths is the discrepancy of eta occupation from half-density.
The cumulative discrepancy is exactly half the logarithm of the Wallis
product.  This is a real source invariant; it does not orient the complex
Fourier correlation needed for the RG-ETA source inequality.
-/

open Filter Topology

namespace RiemannGaussian

noncomputable def etaCellSurplus (n : ℕ) : ℝ :=
  (Real.log (((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) -
   Real.log (((2 * n + 3 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ))) / 2

noncomputable def etaCumulativeSurplus (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, etaCellSurplus n

private theorem etaCellSurplus_eq (n : ℕ) :
    etaCellSurplus n =
      Real.log ((((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) *
        (((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ))) / 2 := by
  unfold etaCellSurplus
  rw [Real.log_mul (by positivity :
    (((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) ≠ 0)
    (by positivity :
      (((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) ≠ 0)]
  rw [Real.log_div (by positivity : (((2 * n + 3 : ℕ) : ℝ)) ≠ 0)
    (by positivity : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0)]
  rw [Real.log_div (by positivity : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0)
    (by positivity : (((2 * n + 3 : ℕ) : ℝ)) ≠ 0)]
  ring

theorem etaCumulativeSurplus_eq_wallis (N : ℕ) :
    etaCumulativeSurplus N = Real.log (Real.Wallis.W N) / 2 := by
  unfold etaCumulativeSurplus Real.Wallis.W
  rw [Real.log_prod]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    rw [etaCellSurplus_eq]
    push_cast
    ring
  · intro n hn
    positivity

theorem etaCellSurplus_pos (n : ℕ) : 0 < etaCellSurplus n := by
  rw [etaCellSurplus_eq]
  apply div_pos _ (by norm_num)
  apply Real.log_pos
  have ha : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hb : (0 : ℝ) < ((2 * n + 3 : ℕ) : ℝ) := by positivity
  rw [div_mul_div_comm, one_lt_div₀ (mul_pos ha hb)]
  push_cast
  nlinarith

theorem etaCumulativeSurplus_strictMono : StrictMono etaCumulativeSurplus := by
  apply strictMono_nat_of_lt_succ
  intro N
  unfold etaCumulativeSurplus
  rw [Finset.sum_range_succ]
  exact lt_add_of_pos_right _ (etaCellSurplus_pos N)

theorem etaCumulativeSurplus_pos {N : ℕ} (hN : 0 < N) :
    0 < etaCumulativeSurplus N := by
  have h := etaCumulativeSurplus_strictMono (show 0 < N from hN)
  simpa [etaCumulativeSurplus] using h

theorem etaCumulativeSurplus_tendsto :
    Tendsto etaCumulativeSurplus atTop (nhds (Real.log (Real.pi / 2) / 2)) := by
  have h := Real.Wallis.tendsto_W_nhds_pi_div_two
  have hlog := (Real.continuousAt_log (by positivity : Real.pi / 2 ≠ 0)).tendsto.comp h
  have hhalf := hlog.div_const 2
  exact hhalf.congr' (Filter.Eventually.of_forall (fun N => (etaCumulativeSurplus_eq_wallis N).symm))

end RiemannGaussian
