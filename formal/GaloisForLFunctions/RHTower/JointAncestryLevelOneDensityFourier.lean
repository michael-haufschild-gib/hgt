import GaloisForLFunctions.RHTower.JointAncestryLevelOneDensityL2
import GaloisForLFunctions.HTGeometry.TorusFourierL2

/-! # Exact Fourier recovery for the signed level-one JAS density -/

namespace RHTower

open MeasureTheory Filter GaloisForLFunctions.HTGeometry
open scoped BigOperators Topology ComplexConjugate

noncomputable section

theorem eventually_subset_jasPrimePrefix (P : Finset Nat.Primes) :
    ∀ᶠ N in atTop, P ⊆ jasPrimePrefix N := by
  classical
  refine eventually_atTop.2 ⟨P.sup (fun p => (p : ℕ)) + 1, fun N hN p hp => ?_⟩
  rw [mem_jasPrimePrefix]
  exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup hp)) hN

theorem torusFourierL2_jasLevelOneSectorLp (q : XiZeroCopy) (P : Finset Nat.Primes)
    {n : Nat.Primes →₀ ℤ} (hn : n.support ⊆ P) :
    torusFourierL2 n (jasLevelOneSectorLp q P) =
      jasDressedCoeff ((q.1 : ℂ) + (1 / 2 : ℝ)) ((q.1 : ℂ) - (1 / 2 : ℝ)) n := by
  rw [jasLevelOneSectorLp, torusFourierL2_torusFiniteProduct _ _ hn,
    jasDressedCoeff, Finsupp.prod_of_support_subset _ hn _
      (fun i _ => by simp [jasDressedLocalCoeff])]
  apply Finset.prod_congr rfl
  intro p _
  simp only [← fourier_neg]
  exact integral_fourier_neg_mul_jasHoloCircle
    (norm_jasHoloA_dressed_lt_one (by linarith [xiZeroCopy_re_pos q]) p)
    (norm_jasHoloB_dressed_lt_one (by linarith [xiZeroCopy_re_lt_one q]) p) (n p)

theorem torusFourierL2_jasLevelOneSectorLimit (q : XiZeroCopy) (n : Nat.Primes →₀ ℤ) :
    torusFourierL2 n (jasLevelOneSectorLimit q) =
      jasDressedCoeff ((q.1 : ℂ) + (1 / 2 : ℝ)) ((q.1 : ℂ) - (1 / 2 : ℝ)) n := by
  have hlim := (torusFourierL2 n).continuous.tendsto _ |>.comp (tendsto_jasLevelOneSectorLp q)
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_subset_jasPrimePrefix n.support] with N hN
  exact (torusFourierL2_jasLevelOneSectorLp q _ hN).symm

theorem torusFourierL2_jasLevelOneDensity (n : Nat.Primes →₀ ℤ) :
    torusFourierL2 n jasLevelOneDensity = jasDressedLagAggregate 1 n := by
  rw [jasLevelOneDensity, (torusFourierL2 n).map_tsum
    summable_norm_lagWeight_smul_jasLevelOneSectorLimit.of_norm,
    jasDressedLagAggregate_eq_tsum]
  apply tsum_congr
  intro q
  rw [map_smul, torusFourierL2_jasLevelOneSectorLimit]
  simp only [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring,
    lagWeight, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm]

theorem integral_jasLevelOneDensity :
    ∫ x, jasLevelOneDensity x ∂torusHaar Nat.Primes = (poleSharpConstant : ℂ) := by
  have h := torusFourierL2_jasLevelOneDensity 0
  simpa only [torusFourierL2_apply, torusCharacter_zero, map_one, one_mul,
    jasDressedLagAggregate_zero] using h

end

end RHTower
