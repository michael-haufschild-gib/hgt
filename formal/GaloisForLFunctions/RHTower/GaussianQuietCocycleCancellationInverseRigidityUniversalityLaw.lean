import GaloisForLFunctions.RHTower.GaussianQuietMultiplicativeCarrierRigidityUniversalityLaw
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Gaussian-quiet cocycle cancellation forces inverse carriers

Pointwise cancellation of two intrinsic reflection cocycles makes the product carrier
reflection-symmetric and nowhere zero. Dirichlet convolution makes that product another
multiplicative L-series carrier. If the product also obeys the all-scale Gaussian quiet budget,
Gaussian quiet rigidity forces the two original carriers to be pointwise inverses globally.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open ArithmeticFunction

/-- **Gaussian-quiet cocycle-cancellation inverse-rigidity universality law.** Two entire
multiplicative Dirichlet carriers with pointwise cancelling intrinsic reflection cocycles and a
joint all-scale Gaussian quiet budget multiply to one on the whole complex plane. Cocycle
cancellation itself supplies both symmetry and nonvanishing of the product carrier. -/
theorem gaussianQuiet_cancellingReflectionCocycles_pointwiseInverse
    {F G : ℂ → ℂ} {a b : ArithmeticFunction ℂ} {c : ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hmulA : a.IsMultiplicative) (hmulB : b.IsMultiplicative)
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hsumA : LSeriesSummable (fun n => a n) c)
    (hsumB : LSeriesSummable (fun n => b n) c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries (fun n => a n) s)
    (hGeq : ∀ s : ℂ, c ≤ s.re → G s = LSeries (fun n => b n) s)
    (hcocycle : ∀ s : ℂ, reflCocycle F s * reflCocycle G s = 1)
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ),
      Filter.Tendsto T Filter.atTop Filter.atTop ∧ (∀ k, 0 < T k) ∧
      (∀ lam : ℝ, 0 < lam →
        Filter.Tendsto (fun k => q k * Real.exp (-(T k) ^ 2 / lam))
          Filter.atTop (nhds 0)) ∧
      ∀ k, ∀ sigma : ℝ, 1 - c ≤ sigma → sigma ≤ c →
        ‖F (sigma + (T k) * Complex.I) * G (sigma + (T k) * Complex.I)‖ ≤ q k ∧
          ‖F (sigma - (T k) * Complex.I) * G (sigma - (T k) * Complex.I)‖ ≤ q k) :
    ∀ s : ℂ, F s * G s = 1 := by
  let C : ℂ → ℂ := fun s => F s * G s
  have hmulC : (a * b).IsMultiplicative := hmulA.mul hmulB
  have hCdiff : Differentiable ℂ C := hF.mul hG
  have hsumC : LSeriesSummable (fun n => (a * b) n) c :=
    ArithmeticFunction.LSeriesSummable_mul hsumA hsumB
  have hCeq : ∀ s : ℂ, c ≤ s.re →
      C s = LSeries (fun n => (a * b) n) s := by
    intro s hs
    rw [show C s = F s * G s by rfl, hFeq s hs, hGeq s hs]
    symm
    exact ArithmeticFunction.LSeries_mul'
      (hsumA.of_re_le_re (by exact_mod_cast hs))
      (hsumB.of_re_le_re (by exact_mod_cast hs))
  have hsym : ∀ s : ℂ, C s = C (1 - s) := by
    intro s
    have hcocycleC : reflCocycle C s = 1 := by
      rw [show C = fun z => F z * G z by rfl, reflCocycle_mul]
      exact hcocycle s
    exact (reflCocycle_eq_one_iff.mp hcocycleC).2.symm
  have hquietC : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ),
      Filter.Tendsto T Filter.atTop Filter.atTop ∧ (∀ k, 0 < T k) ∧
      (∀ lam : ℝ, 0 < lam →
        Filter.Tendsto (fun k => q k * Real.exp (-(T k) ^ 2 / lam))
          Filter.atTop (nhds 0)) ∧
      ∀ k, ∀ sigma : ℝ, 1 - c ≤ sigma → sigma ≤ c →
        ‖C (sigma + (T k) * Complex.I)‖ ≤ q k ∧
          ‖C (sigma - (T k) * Complex.I)‖ ≤ q k := by
    simpa only [C] using hquiet
  exact gaussianQuiet_symmetricMultiplicativeCarrier_eq_one
    hc hc0 hmulC hCdiff hsumC hCeq hsym hquietC

end

end RHTower
