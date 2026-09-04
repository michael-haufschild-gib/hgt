import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Signed convolution transfer for Selberg--Delange asymptotics

The summatory function of a Dirichlet convolution is an exact hyperbola sum.  After normalization,
Tannery's theorem transfers a pointwise asymptotic for the inner summatory function through a
signed or complex outer coefficient system, provided one summable majorant controls the moving
hyperbola array.

This is the signed step in the concrete squarefree-half Selberg--Delange argument.  Positivity is
needed only for the base Tauberian theorem; no sign hypothesis is imposed on the correction.
-/

open ArithmeticFunction Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Summatory function of a complex arithmetic function over the positive integers up to `N`. -/
def arithmeticSummatory (f : ArithmeticFunction ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, f n

/-- Exact hyperbola identity in summatory-function notation. -/
theorem arithmeticSummatory_mul (f g : ArithmeticFunction ℂ) (N : ℕ) :
    arithmeticSummatory (f * g) N =
      ∑ d ∈ Finset.Icc 1 N, f d * arithmeticSummatory g (N / d) := by
  exact sum_Icc_mul_apply f g N

/-- The termwise convolution-transfer constant is the correction's `L`-value at one. -/
theorem tsum_corr_mul_div_eq_mul_LSeries_one (corr : ArithmeticFunction ℂ) (A : ℂ) :
    (∑' d : ℕ, if d = 0 then 0 else corr d * (A / (d : ℂ))) =
      A * LSeries corr (1 : ℂ) := by
  rw [LSeries]
  calc
    (∑' d : ℕ, if d = 0 then 0 else corr d * (A / (d : ℂ))) =
        ∑' d : ℕ, A * LSeries.term corr (1 : ℂ) d := by
      apply tsum_congr
      intro d
      by_cases hd : d = 0
      · subst d
        simp
      · rw [if_neg hd, LSeries.term_of_ne_zero hd]
        simp only [Complex.cpow_one]
        ring
    _ = A * ∑' d : ℕ, LSeries.term corr (1 : ℂ) d := tsum_mul_left

/-- **Signed Selberg--Delange convolution transfer.**

Suppose the normalized summatory function of `base` has, after every fixed integral dilation,
the expected limit `A / d`.  If the moving hyperbola summands obtained by convolving with `corr`
have a single summable majorant, then the normalized convolution summatory function tends to the
termwise sum.  The correction may be signed or genuinely complex.

The explicit `d = 0` branch matches the convention that arithmetic functions vanish at zero and
keeps the theorem independent of any division-by-zero simplification.
-/
theorem tendsto_arithmeticSummatory_mul_div_of_dominated
    (corr base : ArithmeticFunction ℂ) (scale : ℕ → ℂ) (A : ℂ)
    (bound : ℕ → ℝ)
    (hboundNonneg : ∀ d, 0 ≤ bound d)
    (hboundSummable : Summable bound)
    (hbase : ∀ d : ℕ, d ≠ 0 →
      Tendsto (fun N ↦ arithmeticSummatory base (N / d) / scale N) atTop
        (𝓝 (A / (d : ℂ))))
    (hdominated : ∀ N d : ℕ, d ∈ Finset.Icc 1 N →
      ‖corr d * arithmeticSummatory base (N / d) / scale N‖ ≤ bound d) :
    Tendsto (fun N ↦ arithmeticSummatory (corr * base) N / scale N) atTop
      (𝓝 (∑' d : ℕ, if d = 0 then 0 else corr d * (A / (d : ℂ)))) := by
  let row : ℕ → ℕ → ℂ := fun N d ↦
    if d ∈ Finset.Icc 1 N then
      corr d * arithmeticSummatory base (N / d) / scale N
    else 0
  let limit : ℕ → ℂ := fun d ↦
    if d = 0 then 0 else corr d * (A / (d : ℂ))
  have hrowLimit : ∀ d : ℕ, Tendsto (fun N ↦ row N d) atTop (𝓝 (limit d)) := by
    intro d
    by_cases hd : d = 0
    · subst d
      simp [row, limit]
    · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
      have hmain :
          Tendsto
            (fun N ↦ corr d * arithmeticSummatory base (N / d) / scale N)
            atTop (𝓝 (corr d * (A / (d : ℂ)))) := by
        simpa only [mul_div_assoc] using tendsto_const_nhds.mul (hbase d hd)
      have heq :
          (fun N ↦ corr d * arithmeticSummatory base (N / d) / scale N) =ᶠ[atTop]
            (fun N ↦ row N d) := by
        filter_upwards [eventually_ge_atTop d] with N hN
        have hmem : d ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hd1, hN⟩
        simp only [row, hmem, if_true]
      simpa only [limit, hd, if_false] using hmain.congr' heq
  have hrowBound : ∀ᶠ N in atTop, ∀ d, ‖row N d‖ ≤ bound d := by
    filter_upwards with N d
    by_cases hd : d ∈ Finset.Icc 1 N
    · simp only [row, hd, if_true]
      exact hdominated N d hd
    · simp only [row, hd, if_false, norm_zero]
      exact hboundNonneg d
  have htannery :
      Tendsto (fun N ↦ ∑' d, row N d) atTop (𝓝 (∑' d, limit d)) :=
    tendsto_tsum_of_dominated_convergence hboundSummable hrowLimit hrowBound
  apply htannery.congr'
  filter_upwards with N
  have hrowFinite : (∑' d, row N d) = ∑ d ∈ Finset.Icc 1 N,
      corr d * arithmeticSummatory base (N / d) / scale N := by
    rw [tsum_eq_sum (s := Finset.Icc 1 N)]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [row, hd, if_true]
    · intro d hd
      simp only [row, hd, if_false]
  rw [hrowFinite, arithmeticSummatory_mul]
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- `L`-value form of the signed convolution-transfer theorem. -/
theorem tendsto_arithmeticSummatory_mul_div_of_dominated_LSeries
    (corr base : ArithmeticFunction ℂ) (scale : ℕ → ℂ) (A : ℂ)
    (bound : ℕ → ℝ)
    (hboundNonneg : ∀ d, 0 ≤ bound d)
    (hboundSummable : Summable bound)
    (hbase : ∀ d : ℕ, d ≠ 0 →
      Tendsto (fun N ↦ arithmeticSummatory base (N / d) / scale N) atTop
        (𝓝 (A / (d : ℂ))))
    (hdominated : ∀ N d : ℕ, d ∈ Finset.Icc 1 N →
      ‖corr d * arithmeticSummatory base (N / d) / scale N‖ ≤ bound d) :
    Tendsto (fun N ↦ arithmeticSummatory (corr * base) N / scale N) atTop
      (𝓝 (A * LSeries corr (1 : ℂ))) := by
  simpa only [tsum_corr_mul_div_eq_mul_LSeries_one] using
    tendsto_arithmeticSummatory_mul_div_of_dominated corr base scale A bound
      hboundNonneg hboundSummable hbase hdominated

end RHTower
