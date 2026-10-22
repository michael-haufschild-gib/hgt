import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEffectiveReflectionApproximation
/-!
# Support-sensitive complete-source reflection bounds

The cooling recurrence only needs `m+n <= q` and `(m+n)/3 <= q-pi`.
Combining this with the Gaussian source jets gives the complete derivative
and reflection bounds under `6 <= q` and `n+3 <= q`. Both linear errors
and their quadratic product remain in the reflected estimate.
-/
namespace RHTower
noncomputable section
/-- Every finite cooling jet has an explicit majorant at a concrete source scale. -/
theorem abs_thetaCuspCoolingJet_le_supportScale
    (n m : ℕ) {x : ℝ}
    (hq : ((m+n : ℕ) : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hs : ((m+n : ℕ) : ℝ)/3 ≤ thetaCuspSingleAtomReflectionScale 1 x-Real.pi) :
    |thetaCuspCoolingJet n m x| ≤
      (8*thetaCuspSingleAtomReflectionScale 1 x)^n *
        (3*thetaCuspSingleAtomReflectionScale 1 x)^m * regimeOneLikelihoodScale x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 ≤ q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have he0 : 0 ≤ regimeOneLikelihoodScale x := (regimeOneLikelihoodScale_pos x).le
  change ((m+n : ℕ) : ℝ) ≤ q at hq
  change ((m+n : ℕ) : ℝ)/3 ≤ q-Real.pi at hs
  change |thetaCuspCoolingJet n m x| ≤ (8*q)^n*(3*q)^m*regimeOneLikelihoodScale x
  induction n generalizing m with
  | zero =>
    have hmq : (m : ℝ)/3 ≤ q-Real.pi := by simpa only [Nat.add_zero] using hs
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
    have h0 := ih m (by push_cast at hq ⊢; linarith) (by push_cast at hs ⊢; linarith)
    have h1 := ih (m+1) (by push_cast at hq ⊢; linarith) (by push_cast at hs ⊢; linarith)
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
theorem abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_supportScale
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hq : (n : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hs : (n : ℝ)/3 ≤ thetaCuspSingleAtomReflectionScale 1 x-Real.pi) :
    |iteratedDeriv n thetaCuspLikelihoodSourceRemainder x| ≤
      (8*thetaCuspSingleAtomReflectionScale 1 x)^n * regimeOneLikelihoodScale x := by
  rw [iteratedDeriv_thetaCuspLikelihoodSourceRemainder n hx]
  simpa only [Nat.zero_add, pow_zero, mul_one] using
    abs_thetaCuspCoolingJet_le_supportScale n 0 (x := x) (by simpa only [Nat.zero_add] using hq) (by simpa only [Nat.zero_add] using hs)


/-- Complete source derivatives have a calibrated first-atom error at every order. -/
theorem abs_thetaCuspFullSource_derivative_sub_first_le_supportScale
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (h6 : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq : (n : ℝ)+3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
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
      have hrem := abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_supportScale
        (n-i) hx (by linarith) (by linarith [Real.pi_lt_four])
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
theorem abs_thetaCuspFullSource_derivative_relative_error_le_supportScale
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (h6 : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq : (n : ℝ)+3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |(iteratedDeriv n thetaCuspFullSource x -
      iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) x) /
        thetaCuspSourceTerm x 1| ≤
      3*(12*thetaCuspSingleAtomReflectionScale 1 x)^n * regimeOneLikelihoodScale x := by
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  rw [abs_div, abs_of_pos hf]
  exact (div_le_iff₀ hf).mpr (abs_thetaCuspFullSource_derivative_sub_first_le_supportScale n hx h6 hq)


private theorem support_product_error_bound (a b c d : ℝ) :
    |a*b-c*d| ≤ |c| * |b-d| + |a-c| * |d| + |a-c| * |b-d| := by
  rw [show a*b-c*d = c*(b-d)+(a-c)*d+(a-c)*(b-d) by ring]
  calc
    |c*(b-d)+(a-c)*d+(a-c)*(b-d)| ≤
        |c*(b-d)+(a-c)*d| + |(a-c)*(b-d)| := abs_add_le _ _
    _ ≤ (|c*(b-d)| + |(a-c)*d|)+|(a-c)*(b-d)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |c| * |b-d| + |a-c| * |d| + |a-c| * |b-d| := by simp only [abs_mul]

/-- Exact quantitative reflected-jet error, retaining both linear errors and their product. -/
theorem abs_thetaCuspNativeReflectionJet_sub_first_le_supportScale
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (h6 : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq : (n : ℝ)+3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
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
    exact abs_thetaCuspFullSource_derivative_sub_first_le_supportScale k hx h6 (by linarith)
  have hprod (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
      |F i*F j-f i*f j| ≤ 9*φ^(2 : ℕ) *
        ((4*q)^i*(12*q)^j*ε + (12*q)^i*(4*q)^j*ε + (12*q)^i*(12*q)^j*ε^(2 : ℕ)) := by
    calc
      |F i*F j-f i*f j| ≤ |f i| * |F j-f j| + |F i-f i| * |f j| + |F i-f i| * |F j-f j| :=
        support_product_error_bound _ _ _ _
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
theorem abs_thetaCuspNativeReflectionJet_relative_error_le_supportScale
    (n : ℕ) {x : ℝ} (hx : 0 < x)
    (h6 : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq : (n : ℝ)+3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |(thetaCuspNativeReflectionJet n x-thetaCuspFirstAtomReflectionJet n x) /
      thetaCuspSourceTerm x 1^(2 : ℕ)| ≤
      18*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x +
        9*(24*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x^(2 : ℕ) := by
  have hf := pow_pos (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))) 2
  rw [abs_div, abs_of_pos hf]
  exact (div_le_iff₀ hf).mpr (abs_thetaCuspNativeReflectionJet_sub_first_le_supportScale n hx h6 hq)


end
end RHTower
