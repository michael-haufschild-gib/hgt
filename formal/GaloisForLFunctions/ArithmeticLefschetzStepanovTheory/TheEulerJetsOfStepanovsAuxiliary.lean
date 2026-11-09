import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.StepanovJetTransfer
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.StepanovsConstructionOnTheTorsion

/-!
# Exact Euler jets of the Stepanov auxiliary

Euler differentiation scales by the Adams degree under power substitution.
At a fixed point, the binomial transfer expresses every jet through the
polynomial moments of the first factors. No smallness condition enters the
identity.
-/

open MvPolynomial Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {σ : Type*}

/-- The integral coordinate Euler derivation `X_j ∂_j`. -/
def integralEuler (j : σ) : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ) :=
  (X j : MvPolynomial σ ℤ) • pderiv j

theorem integralEuler_apply (j : σ) (F : MvPolynomial σ ℤ) :
    integralEuler j F = X j * pderiv j F := rfl

theorem adams_X (q : ℕ) (j : σ) : adams q (X j) = (X j : MvPolynomial σ ℤ) ^ q :=
  aeval_X _ _

theorem integralEuler_X_self (j : σ) : integralEuler j (X j) = X j := by
  rw [integralEuler_apply, pderiv_X_self, mul_one]

theorem integralEuler_X_of_ne {j i : σ} (hi : i ≠ j) : integralEuler j (X i) = 0 := by
  rw [integralEuler_apply, pderiv_X_of_ne hi, mul_zero]

private theorem integralEuler_adams_X (q : ℕ) (j i : σ) :
    integralEuler j (adams q (X i)) = (q : ℤ) • adams q (integralEuler j (X i)) := by
  classical
  by_cases hi : i = j
  · subst i
    rw [integralEuler_X_self]
    simp only [adams_X]
    cases q with
    | zero => simp only [pow_zero, Derivation.map_one_eq_zero, Nat.cast_zero, zero_smul]
    | succ q =>
      rw [Derivation.leibniz_pow, integralEuler_X_self]
      simp only [Nat.succ_sub_one, smul_eq_mul, nsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
      simp only [pow_succ, mul_assoc]
  · rw [integralEuler_X_of_ne hi, map_zero, smul_zero, adams_X,
      Derivation.leibniz_pow, integralEuler_X_of_ne hi, smul_zero, smul_zero]

/-- Euler differentiation scales exactly by the Adams degree, over the integers. -/
theorem integralEuler_adams (q : ℕ) (j : σ) (F : MvPolynomial σ ℤ) :
    integralEuler j (adams q F) = (q : ℤ) • adams q (integralEuler j F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    simp only [adams, aeval_C, MvPolynomial.algebraMap_eq, integralEuler_apply,
      pderiv_C, mul_zero, map_zero, smul_zero]
  | add F G hF hG => simp only [map_add, hF, hG, smul_add]
  | mul_X F i hF =>
    rw [map_mul, Derivation.leibniz, integralEuler_adams_X, hF, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, zsmul_eq_mul]
    ring

/-- Evaluation at an Adams fixed point removes the substitution. -/
theorem aeval_adams_fixed (q : ℕ) (u : σ → ℂ) (hu : ∀ j, u j ^ q = u j)
    (F : MvPolynomial σ ℤ) : aeval u (adams q F) = aeval u F := by
  rw [aeval_adams, show (fun i => u i ^ q) = u from funext hu]

/-- The concrete Euler product recurrence agrees with the binomial transfer at fixed points. -/
theorem aeval_euler_pow_mul_adams (q n : ℕ) (j : σ) (u : σ → ℂ)
    (hu : ∀ i, u i ^ q = u i) (f g : MvPolynomial σ ℤ) :
    aeval u (((integralEuler j).toLinearMap ^ n) (f * adams q g)) =
      aeval u (((stepanovJetTransfer (q : ℤ) (integralEuler j).toLinearMap ^ n)
        (LinearMap.mulRight ℤ g)) f) := by
  induction n generalizing f g with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, LinearMap.mulRight_apply, map_mul,
      aeval_adams_fixed q u hu]
  | succ n ih =>
    have hp : integralEuler j (f * adams q g) =
        integralEuler j f * adams q g + (q : ℤ) • (f * adams q (integralEuler j g)) := by
      rw [Derivation.leibniz, integralEuler_adams]
      simp only [smul_eq_mul, zsmul_eq_mul]
      ring
    rw [pow_succ, Module.End.mul_apply]
    change aeval u (((integralEuler j).toLinearMap ^ n) (integralEuler j (f * adams q g))) = _
    rw [hp, map_add, map_zsmul, map_add, map_zsmul, ih, ih,
      stepanovJetTransfer_succ_mulRight, map_add, map_zsmul]
    rfl

/-- The `k`th polynomial moment differentiates only the first factors. -/
def stepanovEulerMoment {m : ℕ} (j : σ) (k : ℕ) (f g : Fin m → MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ := ∑ i, ((integralEuler j).toLinearMap ^ k) (f i) * g i

/-- Exact all-order Euler jets, with no vanishing or norm-smallness premise. -/
theorem aeval_euler_pow_stepanov (q n : ℕ) (j : σ) (u : σ → ℂ)
    (hu : ∀ i, u i ^ q = u i) {m : ℕ} (f g : Fin m → MvPolynomial σ ℤ) :
    aeval u (((integralEuler j).toLinearMap ^ n) (stepanovAux q f g)) =
      ∑ ab ∈ antidiagonal n, n.choose ab.1 •
        (((q : ℤ) ^ ab.2 * (1 - (q : ℤ)) ^ ab.1) •
          aeval u (((integralEuler j).toLinearMap ^ ab.2) (stepanovEulerMoment j ab.1 f g))) := by
  rw [stepanovAux, map_sum, map_sum]
  simp_rw [aeval_euler_pow_mul_adams q n j u hu, stepanovJetTransfer_pow]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.mulRight_apply, map_sum, map_nsmul, map_zsmul]
  rw [sum_comm]
  apply sum_congr rfl
  intro ab _
  simp only [stepanovEulerMoment, map_sum, smul_sum]

/-- The first surviving polynomial moment gives the first surviving Euler jet exactly. -/
theorem aeval_euler_pow_stepanov_of_lowerMoments (q n : ℕ) (j : σ) (u : σ → ℂ)
    (hu : ∀ i, u i ^ q = u i) {m : ℕ} (f g : Fin m → MvPolynomial σ ℤ)
    (hlow : ∀ k < n, stepanovEulerMoment j k f g = 0) :
    aeval u (((integralEuler j).toLinearMap ^ n) (stepanovAux q f g)) =
      (1 - (q : ℤ)) ^ n • aeval u (stepanovEulerMoment j n f g) := by
  rw [aeval_euler_pow_stepanov q n j u hu, sum_eq_single (n, 0)]
  · simp only [Nat.choose_self, one_smul, pow_zero, one_mul, Module.End.one_apply]
  · rintro ⟨a, b⟩ hab hne
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have ha : a < n := by
      by_contra h
      apply hne
      apply Prod.ext <;> omega
    rw [hlow a ha, map_zero, map_zero, smul_zero, smul_zero]
  · intro h
    exact (h (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_zero n))).elim

theorem stepanovEulerMoment_zero {m : ℕ} (j : σ) (f g : Fin m → MvPolynomial σ ℤ) :
    stepanovEulerMoment j 0 f g = ∑ i, f i * g i := rfl

theorem stepanovEulerMoment_one {m : ℕ} (j : σ) (f g : Fin m → MvPolynomial σ ℤ) :
    stepanovEulerMoment j 1 f g = X j * ∑ i, pderiv j (f i) * g i := by
  simp only [stepanovEulerMoment, pow_one]
  change (∑ i, (X j * pderiv j (f i)) * g i) = X j * ∑ i, pderiv j (f i) * g i
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  exact mul_assoc _ _ _

/-- Two polynomial syzygies force the first derivative exactly; no norm bound is needed. -/
theorem aeval_pderiv_stepanov_eq_zero_of_syzygies (q : ℕ) (j : σ) (u : σ → ℂ)
    (hu : ∀ i, u i ^ q = u i) (hunit : u j ≠ 0) {m : ℕ}
    (f g : Fin m → MvPolynomial σ ℤ) (hfg : ∑ i, f i * g i = 0)
    (hdf : ∑ i, pderiv j (f i) * g i = 0) :
    aeval u (pderiv j (stepanovAux q f g)) = 0 := by
  have hlow : ∀ k < 1, stepanovEulerMoment j k f g = 0 := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rw [stepanovEulerMoment_zero, hfg]
  have he := aeval_euler_pow_stepanov_of_lowerMoments q 1 j u hu f g hlow
  rw [stepanovEulerMoment_one, hdf, mul_zero, map_zero, smul_zero, pow_one] at he
  change aeval u (integralEuler j (stepanovAux q f g)) = 0 at he
  rw [integralEuler_apply, map_mul, aeval_X] at he
  exact (mul_eq_zero.mp he).resolve_left hunit

#print axioms integralEuler_adams
#print axioms aeval_euler_pow_stepanov
#print axioms aeval_pderiv_stepanov_eq_zero_of_syzygies

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
