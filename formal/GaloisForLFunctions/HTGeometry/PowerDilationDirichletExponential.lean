import GaloisForLFunctions.HTGeometry.ArithmeticPowerDilation
import GaloisForLFunctions.HTGeometry.DirichletConvolutionExponential

/-!
Power completion commutes with the coefficientwise Dirichlet exponential.
The exponential at index `n` is a finite sum, so these identities need no
convergence assumption. Completely multiplicative weights may vanish.
This applies the power-completion mechanism of paper2, Section 5, to the
corpus's arithmetic generating functions at every positive power, not only cubes.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open _root_.RHTower

theorem dirichletConvPow_coe {R : Type*} [Semiring R]
    (f : ArithmeticFunction R) (k : ℕ) : dirichletConvPow f k = ⇑(f ^ k) := by
  induction k with
  | zero => ext n; simp [dirichletConvPow_zero_apply, ArithmeticFunction.one_apply]
  | succ k ih =>
    rw [dirichletConvPow_succ, ih, ArithmeticFunction.coe_mul, pow_succ']

/-- Every convolution power retains the original coefficient, including its weight. -/
theorem dirichletConvPow_powerTwistedDilation
    (m : ℕ) (w : ℕ →* ℂ) (f : ArithmeticFunction ℂ) (k n : ℕ) :
    dirichletConvPow (powerTwistedDilation m w f) k (n ^ (m + 1)) =
      w n * dirichletConvPow f k n := by
  rw [dirichletConvPow_coe, dirichletConvPow_coe, ← map_pow,
    powerTwistedDilation_apply_pow]

/-- Exponentiation introduces no coefficients away from the completion powers. -/
theorem dirichletExp_powerTwistedDilation_off_powers
    (m : ℕ) (w : ℕ →* ℂ) (f : ArithmeticFunction ℂ) {n : ℕ}
    (hn : ∀ k, k ^ (m + 1) ≠ n) :
    dirichletExp (powerTwistedDilation m w f) n = 0 := by
  unfold dirichletExp
  apply Finset.sum_eq_zero
  intro k _
  rw [dirichletConvPow_coe, ← map_pow]
  change mPart (m + 1) (arithmeticTwistRingHom w (f ^ k)) n / _ = 0
  rw [mPart_apply_of_forall_pow_ne _ _ hn, zero_div]

/-- Power completion and the Dirichlet exponential commute at every supported index. -/
theorem dirichletExp_powerTwistedDilation_apply_pow
    (m : ℕ) (w : ℕ →* ℂ) (f : ArithmeticFunction ℂ) (hf : f 1 = 0) (n : ℕ) :
    dirichletExp (powerTwistedDilation m w f) (n ^ (m + 1)) =
      w n * dirichletExp f n := by
  have h1 : powerTwistedDilation m w f 1 = 0 := by
    simpa [hf] using powerTwistedDilation_apply_pow m w f 1
  rw [dirichletExp_eq_tsum (ArithmeticFunction.map_zero) h1,
    dirichletExp_eq_tsum (ArithmeticFunction.map_zero) hf, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [dirichletConvPow_powerTwistedDilation, mul_div_assoc]

/-- The finite coefficient exponential packaged in the convolution algebra. -/
def arithmeticDirichletExp (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨dirichletExp f, dirichletExp_zero⟩

theorem arithmeticDirichletExp_powerTwistedDilation
    (m : ℕ) (w : ℕ →* ℂ) (f : ArithmeticFunction ℂ) (hf : f 1 = 0) :
    arithmeticDirichletExp (powerTwistedDilation m w f) =
      powerTwistedDilation m w (arithmeticDirichletExp f) := by
  ext n
  by_cases hn : ∃ k, k ^ (m + 1) = n
  · obtain ⟨k, rfl⟩ := hn
    exact (dirichletExp_powerTwistedDilation_apply_pow m w f hf k).trans
      (powerTwistedDilation_apply_pow m w (arithmeticDirichletExp f) k).symm
  · have hn' : ∀ k, k ^ (m + 1) ≠ n := fun k hk => hn ⟨k, hk⟩
    change dirichletExp (powerTwistedDilation m w f) n =
      mPart (m + 1) (arithmeticTwistRingHom w (arithmeticDirichletExp f)) n
    rw [dirichletExp_powerTwistedDilation_off_powers _ _ _ hn',
      mPart_apply_of_forall_pow_ne _ _ hn']

/-- Exact analytic clock transport, with no summability premise. -/
theorem LSeries_dirichletExp_powerDilation
    (m : ℕ) (f : ArithmeticFunction ℂ) (hf : f 1 = 0) (s : ℂ) :
    LSeries (dirichletExp (mPart (m + 1) f)) s =
      LSeries (dirichletExp f) (((m + 1 : ℕ) : ℂ) * s) := by
  have hone (g : ArithmeticFunction ℂ) :
      powerTwistedDilation m (1 : ℕ →* ℂ) g = mPart (m + 1) g := by
    change mPart (m + 1) (arithmeticTwistRingHom 1 g) = _
    congr 1
    ext n
    change (1 : ℂ) * g n = g n
    exact one_mul _
  have h := arithmeticDirichletExp_powerTwistedDilation m 1 f hf
  rw [hone, hone] at h
  change LSeries (arithmeticDirichletExp (mPart (m + 1) f)) s = _
  rw [h, LSeries_mPart (Nat.succ_ne_zero m)]
  rfl

end GaloisForLFunctions.HTGeometry
