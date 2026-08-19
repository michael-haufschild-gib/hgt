import GaloisForLFunctions.HTGeometry.FlatMultiplier
import GaloisForLFunctions.HTGeometry.PeriodizationNormalization

/-!
# The damping multiplier

Normalizing an invariant profile at a point and feeding it to `flatMultiplier` produces a multiplier
that is invariant, is the identity on every jet of order below `m` at that point, and inherits the
profile's decay.  Applied to a periodized Gaussian, this is Abe's damping multiplier.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The profile normalized to one at a point. -/
def normalizedProfile {d : ℕ} (Θ : MultivariateEntire d) (p : Fin d → ℂ) : MultivariateEntire d :=
  (Θ.1 p)⁻¹ • Θ

theorem normalizedProfile_apply {d : ℕ} (Θ : MultivariateEntire d) (p x : Fin d → ℂ) :
    (normalizedProfile Θ p).1 x = (Θ.1 p)⁻¹ * Θ.1 x := rfl

theorem normalizedProfile_self {d : ℕ} (Θ : MultivariateEntire d) {p : Fin d → ℂ}
    (hp : Θ.1 p ≠ 0) : (normalizedProfile Θ p).1 p = 1 := by
  rw [normalizedProfile_apply, inv_mul_cancel₀ hp]

theorem normalizedProfile_invariant {d : ℕ} (Θ : MultivariateEntire d) (p : Fin d → ℂ)
    {ΓH : AddSubgroup (Fin d → ℂ)} (hΘ : ∀ η ∈ ΓH, ∀ x, Θ.1 (x + η) = Θ.1 x) :
    ∀ η ∈ ΓH, ∀ x, (normalizedProfile Θ p).1 (x + η) = (normalizedProfile Θ p).1 x := by
  intro η hη x
  rw [normalizedProfile_apply, normalizedProfile_apply, hΘ η hη x]

theorem norm_normalizedProfile {d : ℕ} (Θ : MultivariateEntire d) (p x : Fin d → ℂ) :
    ‖(normalizedProfile Θ p).1 x‖ = ‖Θ.1 p‖⁻¹ * ‖Θ.1 x‖ := by
  rw [normalizedProfile_apply, norm_mul, norm_inv]

/-- **The damping multiplier of a profile at a point.** -/
def dampingMultiplier {d : ℕ} (Θ : MultivariateEntire d) (p : Fin d → ℂ) (m : ℕ) :
    MultivariateEntire d :=
  flatMultiplier (normalizedProfile Θ p) m

/-- **The damping multiplier is invariant.** -/
theorem dampingMultiplier_invariant {d : ℕ} (Θ : MultivariateEntire d) (p : Fin d → ℂ) (m : ℕ)
    {ΓH : AddSubgroup (Fin d → ℂ)} (hΘ : ∀ η ∈ ΓH, ∀ x, Θ.1 (x + η) = Θ.1 x) :
    ∀ η ∈ ΓH, ∀ x, (dampingMultiplier Θ p m).1 (x + η) = (dampingMultiplier Θ p m).1 x :=
  flatMultiplier_invariant (normalizedProfile Θ p) m (normalizedProfile_invariant Θ p hΘ)

/-- **The damping multiplier is the identity on the jets below `m` at the normalization point.** -/
theorem multiIndexJetEvalCLM_dampingMultiplier_mul {d m : ℕ} (Θ f : MultivariateEntire d)
    {p : Fin d → ℂ} (hp : Θ.1 p ≠ 0) (a : Fin d →₀ ℕ) (ha : Finsupp.degree a < m) :
    multiIndexJetEvalCLM p a (multivariateEntireMul (dampingMultiplier Θ p m) f)
      = multiIndexJetEvalCLM p a f :=
  multiIndexJetEvalCLM_flatMultiplier_mul (normalizedProfile Θ p) f
    (normalizedProfile_self Θ hp) a ha

end

end GaloisForLFunctions.HTGeometry
