import GaloisForLFunctions.RHTower.SummableDivisorHarmonicMean
import GaloisForLFunctions.RHTower.Sieve.SquarefreeTotientResidueKernel

open Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Exact harmonic-divisor representation of the squarefree reciprocal-totient sum. -/
theorem sum_sqfreeTotientInv_eq_residueHarmonic (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, sqfreeTotientInv n) =
      ∑ d ∈ Finset.Icc 1 N,
        squarefreeTotientHarmonicResidue d * (harmonic (N / d) : ℝ) := by
  have hswap := RHTower.RegularizedDivisorHarmonic.divisorSummatory_reciprocal_harmonic
    N (fun d => squarefreeTotientResidue d)
  calc
    (∑ n ∈ Finset.Icc 1 N, sqfreeTotientInv n) =
        ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ *
          ∑ d ∈ n.divisors, squarefreeTotientResidue d := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sum_divisors_squarefreeTotientResidue, scaledSqfreeTotientInv_apply]
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
      field_simp
    _ = ∑ d ∈ Finset.Icc 1 N,
        squarefreeTotientResidue d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ) :=
      hswap.symm
    _ = ∑ d ∈ Finset.Icc 1 N,
        squarefreeTotientHarmonicResidue d * (harmonic (N / d) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [squarefreeTotientHarmonicResidue_apply
        (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)]
      ring

/-- The squarefree reciprocal-totient weight has exact logarithmic mean `1`. -/
theorem tendsto_sum_sqfreeTotientInv_div_log_one :
    Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, sqfreeTotientInv n) / Real.log N)
      atTop (𝓝 1) := by
  have hmean := RHTower.tendsto_summableDivisorHarmonicMean
    (fun d : ℕ => squarefreeTotientHarmonicResidue d)
    squarefreeTotientHarmonicResidue_zero
    summable_abs_squarefreeTotientHarmonicResidue
  rw [tsum_squarefreeTotientHarmonicResidue] at hmean
  exact hmean.congr' (Filter.Eventually.of_forall fun N => by
    symm
    change (∑ n ∈ Finset.Icc 1 N, sqfreeTotientInv n) / Real.log N = _
    rw [sum_sqfreeTotientInv_eq_residueHarmonic, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    ring)

end

end RHTower.Sieve
