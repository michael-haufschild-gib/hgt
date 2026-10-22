import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEffectiveLikelihoodCooling
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEffectiveFirstAtomJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomAllOrderApproximation

/-!
# Quantitative all-order first-atom approximation of the complete theta source

The exact source Leibniz decomposition combines the Gaussian and calibrated
likelihood bounds. The binomial theorem gives the explicit factor 3(12q)^n
epsilon at the concrete threshold q >= n+6.
-/

namespace RHTower
noncomputable section

/-- Complete source derivatives have a calibrated first-atom error at every order. -/
theorem abs_thetaCuspFullSource_derivative_sub_first_le_effective
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hq : (n : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspFullSource x -
      iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤
      3*(12*thetaCuspSingleAtomReflectionScale 1 x)^n *
        regimeOneLikelihoodScale x * thetaCuspSourceTerm x 1 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let ε := regimeOneLikelihoodScale x
  have hq0 : 0 ≤ q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hf0 : 0 ≤ f := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).le
  have he0 : 0 ≤ ε := (regimeOneLikelihoodScale_pos x).le
  rw [thetaCuspFullSource_derivative_sub_first_eq n hx]
  calc
    |∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x *
          iteratedDeriv (n-i) thetaCuspLikelihoodSourceRemainder x| ≤
        ∑ i ∈ Finset.range (n+1), |(n.choose i : ℝ) *
          iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x *
            iteratedDeriv (n-i) thetaCuspLikelihoodSourceRemainder x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        (3*(4*q)^i*f) * ((8*q)^(n-i)*ε) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
      have hir : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hin
      have hsub : ((n-i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.sub_le n i)
      have hfirst := abs_iteratedDeriv_firstAtom_le_effective i (x := x) (by linarith)
      have hrem := abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_explicitScale
        (n-i) hx (by linarith)
      have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
      simp only [abs_mul, abs_of_nonneg hc]
      have hm := mul_le_mul hfirst hrem (abs_nonneg _) (by positivity)
      have hh := mul_le_mul_of_nonneg_left hm hc
      dsimp [q, f, ε]
      simpa only [mul_assoc] using hh
    _ = 3*(4*q+8*q)^n*ε*f := by
      rw [add_pow]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 3*(12*thetaCuspSingleAtomReflectionScale 1 x)^n *
        regimeOneLikelihoodScale x * thetaCuspSourceTerm x 1 := by
      rw [show 4*q+8*q = 12*q by ring]

/-- The literal first-atom relative error has an explicit exponential majorant. -/
theorem abs_thetaCuspFullSource_derivative_relative_error_le_effective
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hq : (n : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |(iteratedDeriv n thetaCuspFullSource x -
      iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) x) /
        thetaCuspSourceTerm x 1| ≤
      3*(12*thetaCuspSingleAtomReflectionScale 1 x)^n * regimeOneLikelihoodScale x := by
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  rw [abs_div, abs_of_pos hf]
  exact (div_le_iff₀ hf).mpr (abs_thetaCuspFullSource_derivative_sub_first_le_effective n hx hq)

end
end RHTower
