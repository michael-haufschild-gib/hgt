import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAllOrderLikelihoodCooling
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5RegimeOneCurvatureSigns

/-!
# Quantitative all-order cooling of the literal likelihood remainder

The calibrated positive spectral measure gives an explicit error scale.
The triangular moment recurrence retains that scale at every derivative order,
with the concrete threshold q >= m+n+6 and majorant (8q)^n (3q)^m epsilon.
-/

namespace RHTower
noncomputable section

/-- The unnormalized literal spectral moments retain the calibrated exponential bound. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_le_explicitScale
    (m : ℕ) {x : ℝ}
    (hm : (m : ℝ) / 3 ≤ thetaCuspSingleAtomReflectionScale 1 x - Real.pi) :
    thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) m ≤
      3^m * regimeOneLikelihoodScale x := by
  have hδ : (m : ℝ) / 3 ≤ thetaCuspLikelihoodCoordinate x - thetaCuspLikelihoodCoordinate 0 := by
    rwa [thetaCuspLikelihoodCoordinate_sub_zero]
  have hcmp := thetaCuspHigherLikelihoodSpectralMoment_le_three_pow_mul_exp_support_comparison
    m (thetaCuspLikelihoodCoordinate_pos (le_refl 0)) hδ
  rw [thetaCuspLikelihoodCoordinate_sub_zero] at hcmp
  have hcal := thetaCuspHigherLikelihoodSpectralMoment_zero_coordinate_zero_lt
  have hm0 : 0 ≤ 3^m * Real.exp (-(3*(thetaCuspSingleAtomReflectionScale 1 x-Real.pi))) :=
    by positivity
  have h := hcmp.trans (mul_le_mul_of_nonneg_left hcal.le hm0)
  calc
    thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) m ≤
        3^m * Real.exp (-(3*(thetaCuspSingleAtomReflectionScale 1 x-Real.pi))) * (1/399) := h
    _ = 3^m * regimeOneLikelihoodScale x := by unfold regimeOneLikelihoodScale; ring

/-- Every finite cooling jet has an explicit majorant at a concrete source scale. -/
theorem abs_thetaCuspCoolingJet_le_explicitScale
    (n m : ℕ) {x : ℝ}
    (hq : ((m+n : ℕ) : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspCoolingJet n m x| ≤
      (8*thetaCuspSingleAtomReflectionScale 1 x)^n *
        (3*thetaCuspSingleAtomReflectionScale 1 x)^m * regimeOneLikelihoodScale x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 ≤ q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have he0 : 0 ≤ regimeOneLikelihoodScale x := (regimeOneLikelihoodScale_pos x).le
  change ((m+n : ℕ) : ℝ)+6 ≤ q at hq
  change |thetaCuspCoolingJet n m x| ≤ (8*q)^n*(3*q)^m*regimeOneLikelihoodScale x
  induction n generalizing m with
  | zero =>
    have hmq : (m : ℝ)/3 ≤ q-Real.pi := by
      simp only [Nat.add_zero] at hq
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith [Real.pi_lt_four]
    have hm := thetaCuspHigherLikelihoodSpectralMoment_le_explicitScale m hmq
    have hn := thetaCuspC5FarTail_moment_nonneg (thetaCuspLikelihoodCoordinate x) m
    change |q^m * thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) m| ≤
      (8*q)^(0 : ℕ)*(3*q)^m*regimeOneLikelihoodScale x
    rw [pow_zero, one_mul, abs_mul, abs_of_nonneg (pow_nonneg hq0 m), abs_of_nonneg hn]
    calc
      q^m * thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) m ≤
          q^m*(3^m*regimeOneLikelihoodScale x) :=
        mul_le_mul_of_nonneg_left hm (pow_nonneg hq0 m)
      _ = (3*q)^m*regimeOneLikelihoodScale x := by rw [mul_pow]; ring
  | succ n ih =>
    have h0 := ih m (by push_cast at hq ⊢; linarith)
    have h1 := ih (m+1) (by push_cast at hq ⊢; linarith)
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmq : (m : ℝ) ≤ q := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast at hq
      linarith
    have hb : 0 ≤ (8*q)^n*(3*q)^m*regimeOneLikelihoodScale x := by positivity
    calc
      |thetaCuspCoolingJet (n+1) m x| ≤
          |2*(m : ℝ)*thetaCuspCoolingJet n m x| +
            |2*thetaCuspCoolingJet n (m+1) x| := by
        simpa only [thetaCuspCoolingJet, sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (2*(m : ℝ)*thetaCuspCoolingJet n m x) 0
            (2*thetaCuspCoolingJet n (m+1) x))
      _ = 2*(m : ℝ)*|thetaCuspCoolingJet n m x| +
          2*|thetaCuspCoolingJet n (m+1) x| := by
        simp only [abs_mul, abs_of_nonneg hm0,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2*(m : ℝ)*((8*q)^n*(3*q)^m*regimeOneLikelihoodScale x) +
          2*((8*q)^n*(3*q)^(m+1)*regimeOneLikelihoodScale x) :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity))
          (mul_le_mul_of_nonneg_left h1 (by norm_num))
      _ = (2*(m : ℝ)+6*q)*((8*q)^n*(3*q)^m*regimeOneLikelihoodScale x) := by
        rw [pow_succ]
        ring
      _ ≤ (8*q)*((8*q)^n*(3*q)^m*regimeOneLikelihoodScale x) :=
        mul_le_mul_of_nonneg_right (by linarith) hb
      _ = (8*q)^(n+1)*(3*q)^m*regimeOneLikelihoodScale x := by ring

/-- Explicit all-order derivative error for the literal higher-source partition. -/
theorem abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_explicitScale
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hq : (n : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspLikelihoodSourceRemainder x| ≤
      (8*thetaCuspSingleAtomReflectionScale 1 x)^n * regimeOneLikelihoodScale x := by
  rw [iteratedDeriv_thetaCuspLikelihoodSourceRemainder n hx]
  simpa only [Nat.zero_add, pow_zero, mul_one] using
    abs_thetaCuspCoolingJet_le_explicitScale n 0 (x := x) (by simpa only [Nat.zero_add] using hq)

end
end RHTower
