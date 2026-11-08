import GaloisForLFunctions.SelbergClass.Primon.KestenGaussianProcess

/-!
# Independent terminal regression of the prime Gaussian process

Subtracting the terminal linear predictor leaves a centered Gaussian
process independent of the terminal value. Its covariance is the exact
Schur complement of the terminal Green diagonal.
-/

open _root_.RHTower MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The residual after predicting each site from one terminal value. -/
def kestenGaussianResidual (p : Nat.Primes) (t n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  kestenGaussianProcess p n ω -
    (kestenGreenEntry p n t / kestenGreenEntry p t t) * kestenGaussianProcess p t ω

/-- The residual field and the terminal variable are jointly Gaussian. -/
theorem isGaussianProcess_kestenGaussianResidual_joint (p : Nat.Primes) (t : ℕ) :
    IsGaussianProcess (Sum.elim (kestenGaussianResidual p t)
      (fun _ : Unit => kestenGaussianProcess p t)) (kestenGaussianNoiseMeasure p) := by
  apply (isGaussianProcess_kestenGaussianProcess p).of_isGaussianProcess
  intro s
  cases s with
  | inl n =>
      refine ⟨{n, t},
        { toFun x := x ⟨n, by simp⟩ -
            (kestenGreenEntry p n t / kestenGreenEntry p t t) * x ⟨t, by simp⟩
          map_add' x y := by simp only [Pi.add_apply]; ring
          map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }, ?_⟩
      intro ω
      rfl
  | inr u =>
      refine ⟨{t}, ContinuousLinearMap.proj ⟨t, by simp⟩, ?_⟩
      intro ω
      rfl

theorem isGaussianProcess_kestenGaussianResidual (p : Nat.Primes) (t : ℕ) :
    IsGaussianProcess (kestenGaussianResidual p t) (kestenGaussianNoiseMeasure p) :=
  (isGaussianProcess_kestenGaussianResidual_joint p t).comp_right Sum.inl

theorem memLp_kestenGaussianResidual (p : Nat.Primes) (t n : ℕ) :
    MemLp (kestenGaussianResidual p t n) 2 (kestenGaussianNoiseMeasure p) :=
  ((isGaussianProcess_kestenGaussianResidual p t).hasGaussianLaw_eval n).memLp_two

theorem integral_kestenGaussianResidual (p : Nat.Primes) (t n : ℕ) :
    (∫ ω, kestenGaussianResidual p t n ω ∂kestenGaussianNoiseMeasure p) = 0 := by
  unfold kestenGaussianResidual
  rw [integral_sub
    ((isGaussianProcess_kestenGaussianProcess p).hasGaussianLaw_eval n).integrable
    (((isGaussianProcess_kestenGaussianProcess p).hasGaussianLaw_eval t).integrable.const_mul _),
    integral_const_mul, integral_kestenGaussianProcess, integral_kestenGaussianProcess,
    mul_zero, sub_zero]

/-- Regression removes every covariance with the terminal coordinate. -/
theorem covariance_kestenGaussianResidual_terminal (p : Nat.Primes) (t n : ℕ) :
    cov[kestenGaussianResidual p t n, kestenGaussianProcess p t;
      kestenGaussianNoiseMeasure p] = 0 := by
  change cov[kestenGaussianProcess p n -
    (kestenGreenEntry p n t / kestenGreenEntry p t t) • kestenGaussianProcess p t,
    kestenGaussianProcess p t; kestenGaussianNoiseMeasure p] = 0
  rw [covariance_sub_left (memLp_kestenGaussianProcess p n)
    ((memLp_kestenGaussianProcess p t).const_smul _) (memLp_kestenGaussianProcess p t),
    covariance_smul_left, covariance_kestenGaussianProcess, covariance_kestenGaussianProcess]
  field_simp [(kestenGreenEntry_pos p t t).ne']
  ring

/-- The whole countable residual field is independent of the terminal value. -/
theorem indepFun_kestenGaussianResidual_terminal (p : Nat.Primes) (t : ℕ) :
    IndepFun (fun ω n => kestenGaussianResidual p t n ω)
      (kestenGaussianProcess p t) (kestenGaussianNoiseMeasure p) := by
  have h := (isGaussianProcess_kestenGaussianResidual_joint p t).indepFun_of_covariance_eq_zero
    (fun n => (isGaussianProcess_kestenGaussianResidual p t).aemeasurable n)
    (fun _ => (isGaussianProcess_kestenGaussianProcess p).aemeasurable t)
    (fun n _ => covariance_kestenGaussianResidual_terminal p t n)
  exact h.comp measurable_id (measurable_pi_apply ())

/-- The residual covariance is the terminal Schur complement at arbitrary sites. -/
theorem covariance_kestenGaussianResidual (p : Nat.Primes) (t n m : ℕ) :
    cov[kestenGaussianResidual p t n, kestenGaussianResidual p t m;
      kestenGaussianNoiseMeasure p] =
      kestenGreenEntry p n m -
        kestenGreenEntry p n t * kestenGreenEntry p t m / kestenGreenEntry p t t := by
  have h : kestenGaussianResidual p t m = kestenGaussianProcess p m -
      (kestenGreenEntry p m t / kestenGreenEntry p t t) • kestenGaussianProcess p t := rfl
  rw [h, covariance_sub_right (memLp_kestenGaussianResidual p t n)
    (memLp_kestenGaussianProcess p m) ((memLp_kestenGaussianProcess p t).const_smul _),
    covariance_smul_right, covariance_kestenGaussianResidual_terminal, mul_zero, sub_zero]
  change cov[kestenGaussianProcess p n -
    (kestenGreenEntry p n t / kestenGreenEntry p t t) • kestenGaussianProcess p t,
    kestenGaussianProcess p m; kestenGaussianNoiseMeasure p] = _
  rw [covariance_sub_left (memLp_kestenGaussianProcess p n)
    ((memLp_kestenGaussianProcess p t).const_smul _) (memLp_kestenGaussianProcess p m),
    covariance_smul_left, covariance_kestenGaussianProcess, covariance_kestenGaussianProcess]
  ring

theorem kestenGaussianResidual_terminal (p : Nat.Primes) (t : ℕ) (ω : ℕ → ℝ) :
    kestenGaussianResidual p t t ω = 0 := by
  rw [kestenGaussianResidual, div_self (kestenGreenEntry_pos p t t).ne', one_mul, sub_self]

/-- Terminal prediction and independent residual reconstruct the field pointwise. -/
theorem kestenGaussianProcess_eq_residual_add_prediction (p : Nat.Primes) (t n : ℕ) (ω : ℕ → ℝ) :
    kestenGaussianProcess p n ω = kestenGaussianResidual p t n ω +
      (kestenGreenEntry p n t / kestenGreenEntry p t t) * kestenGaussianProcess p t ω := by
  rw [kestenGaussianResidual, sub_add_cancel]

end
end GaloisForLFunctions.SelbergClass.Primon
