import GaloisForLFunctions.RHTower.ThetaCuspFactoredReflectionError

/-! # Sharp reflected likelihood bounds on physical scale at least seven -/
namespace RHTower
noncomputable section

/-- The reflected relative error costs two linear tails and one quadratic tail. -/
theorem abs_thetaCuspLikelihoodReflectionErrorJet_le {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodReflectionErrorJet n x| ≤
      2*(6*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x +
        (12*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x^2 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let ε := regimeOneLikelihoodScale x
  let R := thetaCuspLikelihoodSourceRemainder
  have hqp : 0 ≤ q := by dsimp [q]; linarith
  have he : 0 ≤ ε := (regimeOneLikelihoodScale_pos x).le
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hb := abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_six_scale hn hq
  have hp : |1+(-1 : ℝ)^n| ≤ 2 := by
    have h := abs_add_le (1 : ℝ) ((-1 : ℝ)^n)
    norm_num [abs_pow] at h ⊢
    exact h
  have hlin : |(1+(-1 : ℝ)^n)*iteratedDeriv n R x| ≤ 2*(6*q)^n*ε := by
    rw [abs_mul]
    have hm := mul_le_mul hp hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    change |1+(-1 : ℝ)^n| * |iteratedDeriv n R x| ≤ 2*((6*q)^n*ε) at hm
    nlinarith only [hm]
  have hs : |∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i R x *
      ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) R x)| ≤ (12*q)^n*ε^2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n+1), |(n.choose i : ℝ)*iteratedDeriv i R x *
          ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) R x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*((6*q)^i*ε)*((6*q)^(n-i)*ε) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
        have h1 := abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_six_scale (hi'.trans hn) hq
        have h2 := abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_six_scale
          ((Nat.sub_le n i).trans hn) hq
        simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (show (0 : ℝ) ≤ (n.choose i : ℝ) from Nat.cast_nonneg _)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
          (abs_nonneg _) (by positivity)
      _ = (12*q)^n*ε^2 := by
        rw [show 12*q = 6*q+6*q by ring, add_pow, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [thetaCuspLikelihoodReflectionErrorJet_eq n hx]
  have ht := abs_add_le ((1+(-1 : ℝ)^n)*iteratedDeriv n R x)
    (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i R x *
      ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) R x))
  change |(1+(-1 : ℝ)^n)*iteratedDeriv n R x +
    ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i R x *
      ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) R x)| ≤ 2*(6*q)^n*ε+(12*q)^n*ε^2
  linarith only [ht, hlin, hs]

/-- The complete finite reflection error retains the exact first-atom reflected jets in its majorant. -/
theorem abs_thetaCuspNativeReflectionJet_sub_first_le_factored
    {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeReflectionJet n x-thetaCuspFirstAtomReflectionJet n x| ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*|thetaCuspFirstAtomReflectionJet i x| *
        (2*(6*thetaCuspSingleAtomReflectionScale 1 x)^(n-i)*regimeOneLikelihoodScale x +
          (12*thetaCuspSingleAtomReflectionScale 1 x)^(n-i)*regimeOneLikelihoodScale x^2) := by
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  rw [thetaCuspNativeReflectionJet_sub_first_eq_factored n hx]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hb := abs_thetaCuspLikelihoodReflectionErrorJet_le ((Nat.sub_le n i).trans hn) hq
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n.choose i : ℝ) from Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left hb (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

end
end RHTower
