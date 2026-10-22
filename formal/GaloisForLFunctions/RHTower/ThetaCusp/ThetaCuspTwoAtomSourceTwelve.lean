import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspDeepTailCoolingTwelve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTwoAtomSourceApproximation

/-! # Quantitative complete-source approximation through derivative twelve -/
namespace RHTower
noncomputable section

/-- Every first-atom derivative remains exact in the finite complete-tail error bound. -/
def thetaCuspTwoAtomSourceErrorBoundTwelve (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
    |iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x| *
    thetaCuspDeepDerivativeBoundTwelve (n-i) x

/-- Every derivative through twelve is linked to the literal two atoms by a complete error bar. -/
theorem abs_thetaCuspFullSource_derivative_sub_two_le_twelve {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspFullSource x-iteratedDeriv n thetaCuspTwoAtomSource x| ≤
      thetaCuspTwoAtomSourceErrorBoundTwelve n x := by
  rw [thetaCuspFullSource_derivative_sub_two_eq n (thetaCusp_pos_of_thirtySevenTenths_le hq)]
  unfold thetaCuspTwoAtomSourceErrorBoundTwelve
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hn' : n-i ≤ 12 := (Nat.sub_le n i).trans hn
  have hb := abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le_hybrid hn' hq
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (n.choose i : ℝ)*|iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x| by positivity)
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
  exact hm

end
end RHTower
