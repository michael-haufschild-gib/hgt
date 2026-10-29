import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic

/-!
# The positive–negative Eisenstein pair is a receiver

For cuspidal loop Eisenstein series the positive series `E` is entire (Garland–Miller–Patnaik;
finite sums over function fields by Braverman–Kazhdan), but its constant term carries no
nontrivial `L`-function. The `L`-functions sit in the factor `Ξ` of the functional equation
`E = Ξ · E⁻` with the negative series `E⁻`.

This module records the exact consequence, for any meromorphic germs. If `E = Ξ · F` near `ν`
and `E` is holomorphic and nonzero at `ν`, then both orders are finite and opposite
(`meromorphicOrderAt_eq_neg_of_mul`): a pole of `Ξ` (a zero of its denominator `L`-function) is
exactly a zero of `F` (`pole_iff_zero_of_mul`), and `Ξ` is holomorphic and nonzero at `ν` iff `F`
is (`order_zero_iff_of_mul`). Entirety of `E` therefore certifies nothing about the zeros in `Ξ`;
zero-freeness is equivalent to holomorphy and nonvanishing of the negative series.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower.InfiniteSymmetry

variable {E Ξ F : ℂ → ℂ} {ν : ℂ}

/-- If `E = Ξ · F` near `ν` with `E` holomorphic and nonzero at `ν`, both orders are finite
integers summing to zero. -/
theorem exists_orders_of_mul (hΞ : MeromorphicAt Ξ ν) (hF : MeromorphicAt F ν)
    (hE : AnalyticAt ℂ E ν) (hE0 : E ν ≠ 0) (h : E =ᶠ[𝓝[≠] ν] Ξ * F) :
    ∃ a b : ℤ, meromorphicOrderAt Ξ ν = a ∧ meromorphicOrderAt F ν = b ∧ a + b = 0 := by
  have hE' : meromorphicOrderAt E ν = 0 := by
    rw [hE.meromorphicOrderAt_eq, hE.analyticOrderAt_eq_zero.mpr hE0]
    rfl
  have hsum : meromorphicOrderAt Ξ ν + meromorphicOrderAt F ν = 0 := by
    rw [← meromorphicOrderAt_mul hΞ hF, ← meromorphicOrderAt_congr h, hE']
  have hΞt : meromorphicOrderAt Ξ ν ≠ ⊤ := fun ht => by simp [ht] at hsum
  have hFt : meromorphicOrderAt F ν ≠ ⊤ := fun ht => by simp [ht] at hsum
  lift meromorphicOrderAt Ξ ν to ℤ using hΞt with a ha
  lift meromorphicOrderAt F ν to ℤ using hFt with b hb
  exact ⟨a, b, rfl, rfl, by exact_mod_cast hsum⟩

/-- The orders of `Ξ` and `F` are opposite. -/
theorem meromorphicOrderAt_eq_neg_of_mul (hΞ : MeromorphicAt Ξ ν) (hF : MeromorphicAt F ν)
    (hE : AnalyticAt ℂ E ν) (hE0 : E ν ≠ 0) (h : E =ᶠ[𝓝[≠] ν] Ξ * F) :
    meromorphicOrderAt Ξ ν = -meromorphicOrderAt F ν := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_orders_of_mul hΞ hF hE hE0 h
  rw [ha, hb, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
  exact congrArg _ (by omega)

/-- **A pole of `Ξ` is exactly a zero of `F`.** -/
theorem pole_iff_zero_of_mul (hΞ : MeromorphicAt Ξ ν) (hF : MeromorphicAt F ν)
    (hE : AnalyticAt ℂ E ν) (hE0 : E ν ≠ 0) (h : E =ᶠ[𝓝[≠] ν] Ξ * F) :
    meromorphicOrderAt Ξ ν < 0 ↔ 0 < meromorphicOrderAt F ν := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_orders_of_mul hΞ hF hE hE0 h
  rw [ha, hb]
  constructor <;> intro hlt
  · have : a < 0 := by exact_mod_cast hlt
    exact_mod_cast (show (0 : ℤ) < b by omega)
  · have : 0 < b := by exact_mod_cast hlt
    exact_mod_cast (show a < (0 : ℤ) by omega)

/-- **The receiver.** `Ξ` is holomorphic and nonzero at `ν` (order zero) iff `F` is. -/
theorem order_zero_iff_of_mul (hΞ : MeromorphicAt Ξ ν) (hF : MeromorphicAt F ν)
    (hE : AnalyticAt ℂ E ν) (hE0 : E ν ≠ 0) (h : E =ᶠ[𝓝[≠] ν] Ξ * F) :
    meromorphicOrderAt Ξ ν = 0 ↔ meromorphicOrderAt F ν = 0 := by
  rw [meromorphicOrderAt_eq_neg_of_mul hΞ hF hE hE0 h, neg_eq_zero]

end GaloisForLFunctions.RHTower.InfiniteSymmetry
