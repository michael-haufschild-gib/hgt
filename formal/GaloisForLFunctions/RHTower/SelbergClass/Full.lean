import GaloisForLFunctions.RHTower.SelbergClass.Basic

/-!
# Exact Selberg class

The full Selberg carrier extends `ExtendedSelbergClass` by normalization, the Ramanujan coefficient
bound, and a concrete Euler-log Dirichlet series supported on prime powers.  The Euler identity is
stated after exponentiation, so it does not confuse the analytic logarithm with the principal branch
of `Complex.log`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact Selberg class: `S♯` plus normalization, Ramanujan, and Euler product. -/
structure SelbergClass extends ExtendedSelbergClass where
  coeff_one : coeff 1 = 1
  ramanujan : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, n ≠ 0 → ‖coeff n‖ ≤ C * (n : ℝ) ^ ε
  eulerLogCoeff : ArithmeticFunction ℂ
  eulerLogCoeff_primePower : ∀ {n : ℕ}, eulerLogCoeff n ≠ 0 →
    ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k
  eulerTheta : ℝ
  eulerTheta_lt_half : eulerTheta < 1 / 2
  eulerLogBound : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
    ‖eulerLogCoeff n‖ ≤ C * (n : ℝ) ^ eulerTheta
  eulerLogSummable : ∀ s : ℂ, 1 < s.re → LSeriesSummable eulerLogCoeff s
  eulerProduct : ∀ s : ℂ, 1 < s.re →
    Complex.exp (LSeries eulerLogCoeff s) = continuation.value s

instance : Coe SelbergClass ExtendedSelbergClass := ⟨SelbergClass.toExtendedSelbergClass⟩

/-- Represented meromorphic function of a full Selberg-class carrier. -/
def SelbergClass.value (F : SelbergClass) : ℂ → ℂ :=
  F.toExtendedSelbergClass.value

instance : CoeFun SelbergClass (fun _ ↦ ℂ → ℂ) := ⟨SelbergClass.value⟩

/-- Every full Selberg-class carrier represents a meromorphic function. -/
theorem SelbergClass.meromorphic_value (F : SelbergClass) : Meromorphic F :=
  F.toExtendedSelbergClass.meromorphic_value

end


end RHTower
