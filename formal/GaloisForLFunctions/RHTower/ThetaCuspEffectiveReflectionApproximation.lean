import GaloisForLFunctions.RHTower.ThetaCuspEffectiveSourceApproximation
import GaloisForLFunctions.RHTower.ThetaCuspNativeJetFirstAtomApproximation

/-!
# Quantitative all-order reflected first-atom approximation

The full reflected Leibniz sum retains both linear source errors and their
product. Its two binomial convolutions give explicit constants and preserve
the same calibrated exponential scale.
-/

namespace RHTower
noncomputable section

private theorem product_error_bound (a b c d : ℝ) :
    |a*b-c*d| ≤ |c| * |b-d| + |a-c| * |d| + |a-c| * |b-d| := by
  rw [show a*b-c*d = c*(b-d)+(a-c)*d+(a-c)*(b-d) by ring]
  calc
    |c*(b-d)+(a-c)*d+(a-c)*(b-d)| ≤
        |c*(b-d)+(a-c)*d| + |(a-c)*(b-d)| := abs_add_le _ _
    _ ≤ (|c*(b-d)| + |(a-c)*d|)+|(a-c)*(b-d)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |c| * |b-d| + |a-c| * |d| + |a-c| * |b-d| := by simp only [abs_mul]

/-- Exact quantitative reflected-jet error, retaining both linear errors and their product. -/
theorem abs_thetaCuspNativeReflectionJet_sub_first_le_effective
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hq : (n : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeReflectionJet n x-thetaCuspFirstAtomReflectionJet n x| ≤
      (18*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x +
        9*(24*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x^(2 : ℕ)) *
          thetaCuspSourceTerm x 1^(2 : ℕ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let φ := thetaCuspSourceTerm x 1
  let ε := regimeOneLikelihoodScale x
  let f (k : ℕ) := iteratedDeriv k (fun y : ℝ => thetaCuspSourceTerm y 1) x
  let F (k : ℕ) := iteratedDeriv k thetaCuspFullSource x
  have hq0 : 0 ≤ q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hφ0 : 0 ≤ φ := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).le
  have hε0 : 0 ≤ ε := (regimeOneLikelihoodScale_pos x).le
  have hf (k : ℕ) (hk : k ≤ n) : |f k| ≤ 3*(4*q)^k*φ := by
    have hkr : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    exact abs_iteratedDeriv_firstAtom_le_effective k (x := x) (by linarith)
  have he (k : ℕ) (hk : k ≤ n) : |F k-f k| ≤ 3*(12*q)^k*ε*φ := by
    have hkr : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    exact abs_thetaCuspFullSource_derivative_sub_first_le_effective k hx (by linarith)
  have hprod (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
      |F i*F j-f i*f j| ≤ 9*φ^(2 : ℕ) *
        ((4*q)^i*(12*q)^j*ε + (12*q)^i*(4*q)^j*ε + (12*q)^i*(12*q)^j*ε^(2 : ℕ)) := by
    calc
      |F i*F j-f i*f j| ≤ |f i| * |F j-f j| + |F i-f i| * |f j| + |F i-f i| * |F j-f j| :=
        product_error_bound _ _ _ _
      _ ≤ (3*(4*q)^i*φ)*(3*(12*q)^j*ε*φ) +
          (3*(12*q)^i*ε*φ)*(3*(4*q)^j*φ) +
          (3*(12*q)^i*ε*φ)*(3*(12*q)^j*ε*φ) :=
        add_le_add (add_le_add
          (mul_le_mul (hf i hi) (he j hj) (abs_nonneg _) (by positivity))
          (mul_le_mul (he i hi) (hf j hj) (abs_nonneg _) (by positivity)))
          (mul_le_mul (he i hi) (he j hj) (abs_nonneg _) (by positivity))
      _ = 9*φ^(2 : ℕ) *
          ((4*q)^i*(12*q)^j*ε + (12*q)^i*(4*q)^j*ε + (12*q)^i*(12*q)^j*ε^(2 : ℕ)) := by ring
  have hid : thetaCuspNativeReflectionJet n x-thetaCuspFirstAtomReflectionJet n x =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*(-1 : ℝ)^(n-i)*
        (F i*F (n-i)-f i*f (n-i)) := by
    rw [thetaCuspNativeReflectionJet_eq, thetaCuspFirstAtomReflectionJet_eq,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f, F]
    ring
  rw [hid]
  calc
    |∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*(-1 : ℝ)^(n-i)*
        (F i*F (n-i)-f i*f (n-i))| ≤
        ∑ i ∈ Finset.range (n+1), |(n.choose i : ℝ)*(-1 : ℝ)^(n-i)*
          (F i*F (n-i)-f i*f (n-i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*(9*φ^(2 : ℕ) *
        ((4*q)^i*(12*q)^(n-i)*ε + (12*q)^i*(4*q)^(n-i)*ε +
          (12*q)^i*(12*q)^(n-i)*ε^(2 : ℕ))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
      have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (hprod i (n-i) hin (Nat.sub_le _ _)) hc
    _ = 9*((4*q+12*q)^n*ε+(12*q+4*q)^n*ε+(12*q+12*q)^n*ε^(2 : ℕ))*φ^(2 : ℕ) := by
      rw [add_pow, add_pow, add_pow]
      simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (18*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x +
        9*(24*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x^(2 : ℕ)) *
          thetaCuspSourceTerm x 1^(2 : ℕ) := by
      rw [show 4*q+12*q = 16*q by ring, show 12*q+4*q = 16*q by ring,
        show 12*q+12*q = 24*q by ring]
      dsimp [q, φ, ε]
      ring

/-- Explicit mass-normalized reflected error at every order. -/
theorem abs_thetaCuspNativeReflectionJet_relative_error_le_effective
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hq : (n : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |(thetaCuspNativeReflectionJet n x-thetaCuspFirstAtomReflectionJet n x) /
      thetaCuspSourceTerm x 1^(2 : ℕ)| ≤
      18*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x +
        9*(24*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x^(2 : ℕ) := by
  have hf := pow_pos (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))) 2
  rw [abs_div, abs_of_pos hf]
  exact (div_le_iff₀ hf).mpr (abs_thetaCuspNativeReflectionJet_sub_first_le_effective n hx hq)

/-- One exponential majorant controls the entire normalized reflected-jet error. -/
theorem abs_thetaCuspNativeReflectionJet_relative_error_le_singleScale
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hq : (n : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |(thetaCuspNativeReflectionJet n x-thetaCuspFirstAtomReflectionJet n x) /
      thetaCuspSourceTerm x 1^(2 : ℕ)| ≤
      27*(24*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have he0 := (regimeOneLikelihoodScale_pos x).le
  have he1 : regimeOneLikelihoodScale x ≤ 1 := by
    have h := regimeOneLikelihoodScale_le_of_six_le (x := x) (by linarith)
    linarith
  have hs : regimeOneLikelihoodScale x^(2 : ℕ) ≤ regimeOneLikelihoodScale x := by nlinarith
  have hp : (16*thetaCuspSingleAtomReflectionScale 1 x)^n ≤
      (24*thetaCuspSingleAtomReflectionScale 1 x)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  have h1 := mul_le_mul_of_nonneg_right hp he0
  have h2 := mul_le_mul_of_nonneg_left hs
    (pow_nonneg (show 0 ≤ 24*thetaCuspSingleAtomReflectionScale 1 x by positivity) n)
  have hb := abs_thetaCuspNativeReflectionJet_relative_error_le_effective n hx hq
  nlinarith only [h1, h2, hb]

end
end RHTower
