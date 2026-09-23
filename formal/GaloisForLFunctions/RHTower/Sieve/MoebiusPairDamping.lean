import GaloisForLFunctions.RHTower.Sieve.MoebiusDistance
import GaloisForLFunctions.RHTower.Sieve.HalaszDichotomy

/-!
# The Möbius smooth sums at `t` and `2t` cannot both be large

Every damping estimate in this folder that survives its own architecture has to see the *sign* of the
coefficients, not only their moduli: a majorisation through `‖f(p)‖ ≤ 1` cannot separate `μ` from `1`.
The one sign-sensitive tool available is the elementary identity

`3 + 4cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`,

which for `f(p) = −1` gives `2∑_{p ∈ P}1/p ≤ 4𝔻(f,n^{it})² + 𝔻(f,n^{2it})²`, hence
`(2/5)∑_{p ∈ P}1/p ≤ max(𝔻(f,n^{it})², 𝔻(f,n^{2it})²)`.  Feeding that maximum into the damped Euler
bound at whichever of the two frequencies attains it, and the trivial bound at the other, gives

`‖S(t)‖·‖S(2t)‖ ≤ exp(2∑_p 1/p + 2∑_p 1/p² − (2/5)∑_p 1/p)`

for the smooth multiplicative sums `S`.  Since `∑_{p ≤ z}1/p = logLog z + O(1)`, the trivial product
bound is `≍ (log z)²` and this is `≍ (log z)^{8/5}`: an unconditional saving of `(log z)^{-2/5}` that
uses no zero-free region and no distance hypothesis, only `μ(p) = −1`.  It is the sign of the
coefficients doing the work — exactly what the majorised architectures throw away.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- **The product of the two smooth sums is damped.**  Sign-sensitive and unconditional. -/
theorem norm_smoothMulSum_mul_norm_smoothMulSum_two_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hneg : ∀ p ∈ P, f p = -1) (t : ℝ) :
    ‖smoothMulSum f P t‖ * ‖smoothMulSum f P (2 * t)‖
      ≤ Real.exp (2 * (∑ p ∈ P, 1 / (p : ℝ)) + 2 * (∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ))
          - 2 * (∑ p ∈ P, 1 / (p : ℝ)) / 5) := by
  classical
  have hPpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  set A : ℝ := ∑ p ∈ P, 1 / (p : ℝ) with hA
  set B : ℝ := ∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ) with hB
  set δ : ℝ := Real.sqrt (2 * A / 5) with hδdef
  have hAnn : (0 : ℝ) ≤ A := Finset.sum_nonneg fun p hp => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hPpos p hp
    positivity
  have hδ0 : (0 : ℝ) ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ ^ (2 : ℕ) = 2 * A / 5 := Real.sq_sqrt (by positivity)
  -- the sign-sensitive maximum
  have hmax := two_mul_sum_inv_div_five_le_max hneg hPpos t
  -- the trivial and damped bounds, both stated on the smooth sum
  have htriv : ∀ u : ℝ, ‖smoothMulSum f P u‖ ≤ Real.exp (A + B) := by
    intro u
    rw [smoothMulSum]
    refine le_trans (norm_sum_smooth_le_exp hf hmul h1 u hP) (Real.exp_le_exp.mpr ?_)
    have hnn : 0 ≤ mulDistSq f u P := by
      rw [mulDistSq_eq_pair]
      exact mulDistSqPair_nonneg_disc (fun p _ => hf p) (fun p _ => (norm_charFn u p).le) hPpos
    linarith
  have hdamp : ∀ u : ℝ, δ ≤ Real.sqrt (mulDistSqPair f (charFn u) P) →
      ‖smoothMulSum f P u‖ ≤ Real.exp (A + B - δ ^ (2 : ℕ)) := by
    intro u hfar
    rw [smoothMulSum]
    exact norm_sum_smooth_le_exp_of_far hf hmul h1 u hP hδ0 hfar
  -- the maximum is attained at `t` or at `2t`
  have hsplit : δ ≤ Real.sqrt (mulDistSqPair f (charFn t) P)
      ∨ δ ≤ Real.sqrt (mulDistSqPair f (charFn (2 * t)) P) := by
    rcases le_total (mulDistSqPair f (charFn (2 * t)) P) (mulDistSqPair f (charFn t) P) with h | h
    · refine Or.inl (Real.sqrt_le_sqrt ?_)
      rw [max_eq_left h] at hmax
      rw [hA]
      linarith [hmax]
    · refine Or.inr (Real.sqrt_le_sqrt ?_)
      rw [max_eq_right h] at hmax
      rw [hA]
      linarith [hmax]
  have hprodval : Real.exp (A + B - δ ^ (2 : ℕ)) * Real.exp (A + B)
      = Real.exp (2 * A + 2 * B - 2 * A / 5) := by
    rw [← Real.exp_add, hδsq]
    congr 1
    ring
  have hnn1 : (0 : ℝ) ≤ ‖smoothMulSum f P t‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖smoothMulSum f P (2 * t)‖ := norm_nonneg _
  rcases hsplit with h | h
  · calc ‖smoothMulSum f P t‖ * ‖smoothMulSum f P (2 * t)‖
        ≤ Real.exp (A + B - δ ^ (2 : ℕ)) * Real.exp (A + B) :=
          mul_le_mul (hdamp t h) (htriv (2 * t)) hnn2 (Real.exp_pos _).le
      _ = Real.exp (2 * A + 2 * B - 2 * A / 5) := hprodval
  · calc ‖smoothMulSum f P t‖ * ‖smoothMulSum f P (2 * t)‖
        ≤ Real.exp (A + B) * Real.exp (A + B - δ ^ (2 : ℕ)) :=
          mul_le_mul (htriv t) (hdamp (2 * t) h) hnn2 (Real.exp_pos _).le
      _ = Real.exp (A + B - δ ^ (2 : ℕ)) * Real.exp (A + B) := by ring
      _ = Real.exp (2 * A + 2 * B - 2 * A / 5) := hprodval

/-- **At least one of the two frequencies is damped.**  The minimum form of the pair bound. -/
theorem min_norm_smoothMulSum_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hneg : ∀ p ∈ P, f p = -1) (t : ℝ) :
    min ‖smoothMulSum f P t‖ ‖smoothMulSum f P (2 * t)‖
      ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ))
          - 2 * (∑ p ∈ P, 1 / (p : ℝ)) / 5) := by
  classical
  have hPpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  set A : ℝ := ∑ p ∈ P, 1 / (p : ℝ) with hA
  set B : ℝ := ∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ) with hB
  set δ : ℝ := Real.sqrt (2 * A / 5) with hδdef
  have hAnn : (0 : ℝ) ≤ A := Finset.sum_nonneg fun p hp => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hPpos p hp
    positivity
  have hδ0 : (0 : ℝ) ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ ^ (2 : ℕ) = 2 * A / 5 := Real.sq_sqrt (by positivity)
  have hmax := two_mul_sum_inv_div_five_le_max hneg hPpos t
  have hdamp : ∀ u : ℝ, δ ≤ Real.sqrt (mulDistSqPair f (charFn u) P) →
      ‖smoothMulSum f P u‖ ≤ Real.exp (A + B - 2 * A / 5) := by
    intro u hfar
    rw [smoothMulSum]
    have h := norm_sum_smooth_le_exp_of_far hf hmul h1 u hP hδ0 hfar
    rwa [hδsq] at h
  rcases le_total (mulDistSqPair f (charFn (2 * t)) P) (mulDistSqPair f (charFn t) P) with h | h
  · refine le_trans (min_le_left _ _) (hdamp t (Real.sqrt_le_sqrt ?_))
    rw [max_eq_left h] at hmax
    rw [hA]
    linarith [hmax]
  · refine le_trans (min_le_right _ _) (hdamp (2 * t) (Real.sqrt_le_sqrt ?_))
    rw [max_eq_right h] at hmax
    rw [hA]
    linarith [hmax]

end RHTower.Sieve
end
