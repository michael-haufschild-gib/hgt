import GaloisForLFunctions.SelbergClass.Primon.KestenGaussianNoise

/-!
# A Gaussian process with the prime Green covariance

The causal filter `X_n = ∑_{k≤n} q^(n-k) ε_k` turns the independent
Gaussian innovations into an actual Gaussian process. Its covariance is
the previously constructed Green kernel. The recursion
`X_(n+1) = q X_n + ε_(n+1)` recovers the original independent noise.
-/

open _root_.RHTower MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The prime autoregression, on the countable innovation probability space. -/
def kestenGaussianProcess (p : Nat.Primes) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), primeReciprocal p ^ (n - k) * ω k

theorem kestenGaussianProcess_zero (p : Nat.Primes) (ω : ℕ → ℝ) :
    kestenGaussianProcess p 0 ω = ω 0 := by
  simp [kestenGaussianProcess]

/-- Each new site is its propagated predecessor plus one fresh Gaussian coordinate. -/
theorem kestenGaussianProcess_succ (p : Nat.Primes) (n : ℕ) (ω : ℕ → ℝ) :
    kestenGaussianProcess p (n + 1) ω = primeReciprocal p * kestenGaussianProcess p n ω + ω (n + 1) := by
  rw [kestenGaussianProcess, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, one_mul]
  rw [kestenGaussianProcess, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

/-- Causal differencing recovers the innovation pointwise, not merely almost everywhere. -/
theorem kestenGaussianProcess_innovation (p : Nat.Primes) (n : ℕ) (ω : ℕ → ℝ) :
    kestenGaussianProcess p (n + 1) ω - primeReciprocal p * kestenGaussianProcess p n ω = ω (n + 1) := by
  rw [kestenGaussianProcess_succ]
  ring

private def causalFunctional (p : Nat.Primes) (n : ℕ) :
    (Finset.range (n + 1) → ℝ) →L[ℝ] ℝ :=
  ∑ k : Finset.range (n + 1), primeReciprocal p ^ (n - k.val) • ContinuousLinearMap.proj k

/-- All finite sections of the filtered process are jointly Gaussian. -/
theorem isGaussianProcess_kestenGaussianProcess (p : Nat.Primes) :
    IsGaussianProcess (kestenGaussianProcess p) (kestenGaussianNoiseMeasure p) := by
  apply (isGaussianProcess_kestenGaussianNoise p).of_isGaussianProcess
  intro n
  refine ⟨Finset.range (n + 1), causalFunctional p n, fun ω => ?_⟩
  simp only [causalFunctional, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Finset.restrict_def]
  exact (Finset.sum_attach (Finset.range (n + 1))
    (fun k => primeReciprocal p ^ (n - k) * ω k)).symm

theorem memLp_kestenGaussianProcess (p : Nat.Primes) (n : ℕ) :
    MemLp (kestenGaussianProcess p n) 2 (kestenGaussianNoiseMeasure p) :=
  ((isGaussianProcess_kestenGaussianProcess p).hasGaussianLaw_eval n).memLp_two

/-- The actual Gaussian field is centered. -/
theorem integral_kestenGaussianProcess (p : Nat.Primes) (n : ℕ) :
    (∫ ω, kestenGaussianProcess p n ω ∂kestenGaussianNoiseMeasure p) = 0 := by
  unfold kestenGaussianProcess
  rw [integral_finsetSum _ (fun k _ =>
    (hasLaw_kestenGaussianNoise p k).hasGaussianLaw.integrable.const_mul _)]
  simp only [integral_const_mul, integral_kestenGaussianNoise, mul_zero, Finset.sum_const_zero]

/-- The covariance with an innovation records precisely its causal contribution. -/
theorem covariance_kestenGaussianProcess_noise (p : Nat.Primes) (n m : ℕ) :
    cov[kestenGaussianProcess p n, fun ω => ω m; kestenGaussianNoiseMeasure p] =
      if m ≤ n then primeReciprocal p ^ (n - m) * (kestenGaussianNoiseVariance p m : ℝ) else 0 := by
  unfold kestenGaussianProcess
  rw [covariance_fun_sum_left'
    (fun k _ => (memLp_kestenGaussianNoise p k).const_mul
      (primeReciprocal p ^ (n - k))) (memLp_kestenGaussianNoise p m)]
  simp only [covariance_const_mul_left, covariance_kestenGaussianNoise, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]

private theorem covariance_succ_right (p : Nat.Primes) (n m : ℕ) :
    cov[kestenGaussianProcess p n, kestenGaussianProcess p (m + 1); kestenGaussianNoiseMeasure p] =
      primeReciprocal p * cov[kestenGaussianProcess p n, kestenGaussianProcess p m; kestenGaussianNoiseMeasure p] +
        if m + 1 ≤ n then primeReciprocal p ^ (n - (m + 1)) * primeReciprocal p else 0 := by
  have h : kestenGaussianProcess p (m + 1) = primeReciprocal p • kestenGaussianProcess p m +
      (fun ω : ℕ → ℝ => ω (m + 1)) := funext (kestenGaussianProcess_succ p m)
  have hm : MemLp (primeReciprocal p • kestenGaussianProcess p m) 2
      (kestenGaussianNoiseMeasure p) := (memLp_kestenGaussianProcess p m).const_mul (primeReciprocal p)
  rw [h, covariance_add_right (memLp_kestenGaussianProcess p n)
    hm (memLp_kestenGaussianNoise p (m + 1)),
    covariance_smul_right, covariance_kestenGaussianProcess_noise, kestenGaussianNoiseVariance_succ]

private theorem covariance_step_of_le (p : Nat.Primes) (n m : ℕ) (hnm : n ≤ m) :
    cov[kestenGaussianProcess p n, kestenGaussianProcess p (m + 1); kestenGaussianNoiseMeasure p] =
      primeReciprocal p * cov[kestenGaussianProcess p n, kestenGaussianProcess p m; kestenGaussianNoiseMeasure p] := by
  rw [covariance_succ_right, if_neg (by omega), add_zero]

private theorem green_zero (p : Nat.Primes) :
    kestenGreenEntry p 0 0 = primeReciprocal p / (1 + primeReciprocal p) := by
  rw [kestenGreenEntry_diagonal]
  simp only [Nat.mul_zero, zero_add, pow_one]
  have hgap : 1 - primeReciprocal p ^ 2 ≠ 0 :=
    (sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide))).ne'
  have hplus : 1 + primeReciprocal p ≠ 0 := by have := primeReciprocal_pos p; positivity
  field_simp [hgap, hplus]
  ring

/-- The diagonal covariance follows exactly the Green variance recursion. -/
theorem covariance_kestenGaussianProcess_self (p : Nat.Primes) (n : ℕ) :
    cov[kestenGaussianProcess p n, kestenGaussianProcess p n; kestenGaussianNoiseMeasure p] =
      kestenGreenEntry p n n := by
  induction n with
  | zero =>
      have h : kestenGaussianProcess p 0 = fun ω : ℕ → ℝ => ω 0 := funext (kestenGaussianProcess_zero p)
      rw [h, covariance_kestenGaussianNoise, if_pos rfl, kestenGaussianNoiseVariance_zero, green_zero]
  | succ n ih =>
      rw [covariance_succ_right, if_pos le_rfl, Nat.sub_self, pow_zero, one_mul,
        covariance_comm (kestenGaussianProcess p (n + 1)) (kestenGaussianProcess p n),
        covariance_step_of_le p n n le_rfl, ih, kestenGreenEntry_variance_recursion]
      ring

private theorem covariance_ordered (p : Nat.Primes) (n k : ℕ) :
    cov[kestenGaussianProcess p n, kestenGaussianProcess p (n + k); kestenGaussianNoiseMeasure p] =
      kestenGreenEntry p n (n + k) := by
  induction k with
  | zero => simpa only [Nat.add_zero] using covariance_kestenGaussianProcess_self p n
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by omega,
        covariance_step_of_le p n (n + k) (by omega), ih,
        kestenGreenEntry_propagation, show n + k + 1 = n + (k + 1) by omega,
        kestenGreenEntry_propagation, pow_succ]
      ring

/-- The actual process covariance is the Green entry, at every pair of depths. -/
theorem covariance_kestenGaussianProcess (p : Nat.Primes) (n m : ℕ) :
    cov[kestenGaussianProcess p n, kestenGaussianProcess p m; kestenGaussianNoiseMeasure p] =
      kestenGreenEntry p n m := by
  rcases le_total n m with h | h
  · simpa only [Nat.add_sub_of_le h] using covariance_ordered p n (m - n)
  · rw [covariance_comm, kestenGreenEntry_symm p n m]
    simpa only [Nat.add_sub_of_le h] using covariance_ordered p m (n - m)

theorem variance_kestenGaussianProcess (p : Nat.Primes) (n : ℕ) :
    Var[kestenGaussianProcess p n; kestenGaussianNoiseMeasure p] = kestenGreenEntry p n n := by
  rw [← covariance_self ((isGaussianProcess_kestenGaussianProcess p).aemeasurable n),
    covariance_kestenGaussianProcess]

/-- Every coordinate has the centered Gaussian law with its Green diagonal variance. -/
theorem hasLaw_kestenGaussianProcess (p : Nat.Primes) (n : ℕ) :
    HasLaw (kestenGaussianProcess p n)
      (gaussianReal 0 (kestenGreenEntry p n n).toNNReal) (kestenGaussianNoiseMeasure p) where
  aemeasurable := (isGaussianProcess_kestenGaussianProcess p).aemeasurable n
  map_eq := by
    rw [((isGaussianProcess_kestenGaussianProcess p).hasGaussianLaw_eval n).map_eq_gaussianReal,
      integral_kestenGaussianProcess, variance_kestenGaussianProcess]

end
end GaloisForLFunctions.SelbergClass.Primon
