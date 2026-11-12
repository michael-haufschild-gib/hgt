import GaloisForLFunctions.MatomakiRadziwill.ParsevalMeanSquare
import GaloisForLFunctions.MatomakiRadziwill.LiouvilleMeanSquare

/-!
# Matomäki–Radziwiłł for `λ` in additive short windows

Parseval (`exists_short_sum_mean_square_of`) applied to the mean square of `λ`
(`exists_mean_square_liouville_le`): for every `ε > 0` there is `h₀` such that for `h ≥ h₀` there is
`X₀` with `Σ_{X ≤ m < 2X} |Σ_{m < n ≤ m + h} λ(n)|² ≤ ε h² X` for `X ≥ X₀`
(`exists_short_sum_mean_square_liouville_le`).
-/

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- **Matomäki–Radziwiłł for `λ` in additive short windows.** -/
theorem exists_short_sum_mean_square_liouville_le {ε : ℝ} (hε : 0 < ε) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ k ∈ Finset.range X,
          ‖∑ n ∈ Finset.Ioc (X + k) (X + k + h), (ArithmeticFunction.liouville n : ℂ)‖ ^ 2
        ≤ ε * (h : ℝ) ^ 2 * X := by
  have h := exists_short_sum_mean_square_of (norm_twLiouville_le (1 : DirichletCharacter ℂ 1))
    (fun _ hε' => exists_mean_square_liouville_le hε') hε
  simpa only [twLiouville_trivial] using h

end

end GaloisForLFunctions.MatomakiRadziwill
