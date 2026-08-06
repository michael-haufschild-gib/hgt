import GaloisForLFunctions.HTGeometry.LatticeExpSumDichotomy
import GaloisForLFunctions.HTGeometry.ShiftSpectrumSpacing
import Mathlib.Analysis.PSeries

/-!
# The degree-one standard twist converges off its spectrum

Off the lattice the additive character sums stay bounded, so Dirichlet's test
applies to the twisted Dirichlet series `∑ n^{-σ} e(αn)`: it converges for every
`σ > 0`, far to the left of the abscissa `σ > 1` of absolute convergence.

On the lattice the character is one and the same series is the real
`p`-series `∑ (n+1)^{-σ}`, which diverges for `σ ≤ 1`.  This is the analytic form
of the degree-one dichotomy: the standard twist extends past `Re w = 1` exactly
off the spectrum, and carries the pole of the underlying `L`-function exactly
on it.
-/

open Filter Topology Finset
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section Weight

/-- The real weight of the twisted series. -/
noncomputable def twistWeight (σ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-σ)

theorem antitone_twistWeight {σ : ℝ} (hσ : 0 < σ) : Antitone (twistWeight σ) := by
  intro m n hmn
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
  have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  linarith

theorem tendsto_twistWeight {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (twistWeight σ) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_neg_nhds_zero (by linarith : -σ < 0)).comp hbase

end Weight

section Convergence

/-- **The degree-one standard twist converges off the lattice.**  For every
positive real spectral parameter the twisted series has Cauchy partial sums. -/
theorem cauchySeq_latticeTwist {α σ : ℝ} (hα : ∀ m : ℤ, α ≠ (m : ℝ)) (hσ : 0 < σ) :
    CauchySeq fun N : ℕ =>
      ∑ n ∈ range N, twistWeight σ n • (latticeChar α) ^ n := by
  refine (antitone_twistWeight hσ).cauchySeq_series_mul_of_tendsto_zero_of_bounded
    (tendsto_twistWeight hσ) (b := 2 / ‖latticeChar α - 1‖) fun N => ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [range_zero, Finset.sum_empty, norm_zero]
    have hden : (0 : ℝ) < ‖latticeChar α - 1‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero_of_ne (latticeChar_ne_one hα)
    positivity
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
    exact norm_latticeExpSum_le hα M

/-- **The twisted series converges off the lattice.** -/
theorem exists_tendsto_latticeTwist {α σ : ℝ} (hα : ∀ m : ℤ, α ≠ (m : ℝ))
    (hσ : 0 < σ) :
    ∃ L : ℂ, Tendsto
      (fun N : ℕ => ∑ n ∈ range N, twistWeight σ n • (latticeChar α) ^ n)
      atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (cauchySeq_latticeTwist hα hσ)

/-- **On the lattice the twisted series is the real `p`-series.**  The character
is one, so no cancellation is available and the series carries the pole of the
underlying `L`-function. -/
theorem latticeTwist_at_integer (m : ℤ) (σ : ℝ) (N : ℕ) :
    (∑ n ∈ range N, twistWeight σ n • (latticeChar ((m : ℤ) : ℝ)) ^ n)
      = ((∑ n ∈ range N, twistWeight σ n : ℝ) : ℂ) := by
  have hone : latticeChar ((m : ℤ) : ℝ) = 1 := by
    rw [latticeChar_eq]
    refine Complex.exp_eq_one_iff.mpr ⟨m, ?_⟩
    push_cast
    ring
  rw [hone]
  push_cast
  simp

/-- The lattice-point series diverges below the abscissa: the real `p`-series
with exponent at most one is not summable. -/
theorem not_summable_twistWeight {σ : ℝ} (hσ : σ ≤ 1) :
    ¬ Summable (twistWeight σ) := by
  intro hsum
  have hshift : Summable fun n : ℕ => ((n : ℝ)) ^ (-σ) := by
    refine (summable_nat_add_iff 1).mp ?_
    refine hsum.congr fun n => ?_
    rw [twistWeight]
    push_cast
    ring_nf
  have hps : Summable fun n : ℕ => 1 / ((n : ℝ)) ^ σ := by
    refine hshift.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  rw [Real.summable_one_div_nat_rpow] at hps
  linarith

end Convergence

end GaloisForLFunctions.HTGeometry
