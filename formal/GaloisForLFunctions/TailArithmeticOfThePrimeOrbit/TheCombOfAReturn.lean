import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheFirstReturn
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheJetOfTheLogarithm
import GaloisForLFunctions.PrimeTorusTheory.TheMassOfMisalignedPrimes
import GaloisForLFunctions.HTGeometry.LogFrequencySeparation

/-!
# The comb of a return

The phase `n ↦ t log n/2π` is a homomorphism from the multiplicative monoid to `ℝ/ℤ`. Its level sets
`L(t, δ) = {n : dist(t log n/2π, ℤ) ≤ δ}` are multiplicative Bohr sets.

* **A multiplicative approximate group** (`dist01_mul_le`). `L(t, δ) · L(t, δ') ⊆ L(t, δ + δ')`.
* **A return is a comb** (`dist01_le_of_isReturn`). If `t` returns the primes of `P` to precision `η`, every integer whose
  prime factors lie in `P` and which has `Ω(n) = k` prime factors has phase within `k √(η/8)` of an integer: the
  `P`-smooth integers lie on the comb `exp((2π/t)ℤ)`, with teeth of relative width `k√(η/8)`.
* **Past the height the comb is thin** (`card_comb_le`). On `[X, X + H]` the phase increases by at least
  `t/(2π(X+H+1))` per step and by `t log((X+H)/X)/2π` in all, so the level set at `δ` has at most
  `(t log((X+H)/X)/2π + 2)(4πδ(X+H+1)/t + 1)` elements: density `O(δ)` once `X ≫ t`.
* **The comb inequality** (`comb_inequality`). If every integer of `[X, X+H]` is `P`-smooth with at most `k` prime
  factors and `t` returns `P` to precision `η`, then `H + 1 ≤ (t log((X+H)/X)/2π + 2)(4πk√(η/8)(X+H+1)/t + 1)`.

This is the sum–product mechanism of the height orbit, and its reach: the level set is a multiplicative approximate group
and, past `X ≍ t`, locally a union of intervals, so a block of consecutive smooth integers cannot lie on it. It needs
`X ≳ t` and precision `≲ 1/k`; it gives first returns polynomial in the length, far below Vinogradov. The comb has both
structures, additive and multiplicative, so no sum–product inequality excludes it by itself: below `X ≍ t` the level
set is not an additive Bohr set, and the problem is the dark range.
-/

open Real Finset

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

open PrimeTorusTheory (dist01)

/-- Distance to the nearest integer is subadditive. -/
theorem dist01_add_le (x y : ℝ) : dist01 (x + y) ≤ dist01 x + dist01 y := by
  unfold dist01
  calc |x + y - round (x + y)| ≤ |x + y - ((round x + round y : ℤ) : ℝ)| := round_le (x + y) (round x + round y)
    _ = |(x - round x) + (y - round y)| := by push_cast; ring_nf
    _ ≤ |x - round x| + |y - round y| := abs_add_le _ _

theorem dist01_zero : dist01 0 = 0 := by simp [dist01]

/-- The phase of `n`. -/
def phaseOf (t : ℝ) (n : ℕ) : ℝ := t * Real.log n / (2 * π)

/-- **A multiplicative approximate group.** -/
theorem dist01_mul_le (t : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    dist01 (phaseOf t (m * n)) ≤ dist01 (phaseOf t m) + dist01 (phaseOf t n) := by
  have e : phaseOf t (m * n) = phaseOf t m + phaseOf t n := by
    unfold phaseOf
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
    ring
  rw [e]
  exact dist01_add_le _ _

/-- A return to precision `η` puts each prime within `√(η/8)` of an integer. -/
theorem dist01_le_of_one_sub_cos_le {t η : ℝ} {p : ℕ} (h : 1 - cos (t * Real.log p) ≤ η) :
    dist01 (phaseOf t p) ≤ √(η / 8) := by
  have h8 := PrimeTorusTheory.eight_mul_sq_le_one_sub_cos (phaseOf t p)
  have e : 2 * π * phaseOf t p = t * Real.log p := by
    unfold phaseOf
    field_simp
  rw [e] at h8
  have h0 : 0 ≤ dist01 (phaseOf t p) := abs_nonneg _
  refine Real.le_sqrt_of_sq_le ?_
  linarith

/-- **A return is a comb.** -/
theorem dist01_le_of_isReturn {P : Finset ℕ} {η t : ℝ} (hret : IsReturn P logStep η t) :
    ∀ n : ℕ, n ≠ 0 → (∀ p, p.Prime → p ∣ n → p ∈ P) →
      dist01 (phaseOf t n) ≤ (ArithmeticFunction.cardFactors n : ℝ) * √(η / 8) := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; simp [phaseOf, dist01_zero]
  | prime p hp =>
    intro _ hP
    rw [ArithmeticFunction.cardFactors_apply_prime hp, Nat.cast_one, one_mul]
    exact dist01_le_of_one_sub_cos_le (hret p (hP p hp dvd_rfl))
  | mul a b iha ihb =>
    intro hab hP
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    have h1 := iha ha fun p hp hpa => hP p hp (Dvd.dvd.mul_right hpa b)
    have h2 := ihb hb fun p hp hpb => hP p hp (Dvd.dvd.mul_left hpb a)
    rw [ArithmeticFunction.cardFactors_mul ha hb]
    push_cast
    linarith [dist01_mul_le t ha hb]

open Classical in
/-- **Past the height the comb is thin.** -/
theorem card_comb_le {t : ℝ} (ht : 0 < t) {X H : ℕ} (hX : 1 ≤ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    (((Icc X (X + H)).filter fun n => dist01 (phaseOf t n) ≤ δ).card : ℝ) ≤
      (t * (Real.log (X + H : ℕ) - Real.log X) / (2 * π) + 2) * (4 * π * δ * (X + H + 1) / t + 1) := by
  set f : ℕ → ℝ := fun n => -phaseOf t n with hf
  set μ : ℝ := t / (2 * π * (X + H + 1)) with hμ
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hstep : ∀ n, X ≤ n → n < X + H → μ ≤ f n - f (n + 1) := by
    intro n hn hnH
    have hn0 : 0 < n := by omega
    have hgap := HTGeometry.inv_max_le_abs_log_sub_log (by omega : 0 < n + 1) hn0 (by omega)
    rw [max_eq_left (by omega)] at hgap
    have hlog : Real.log n ≤ Real.log (n + 1 : ℕ) :=
      Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast (by omega : n ≤ n + 1))
    rw [abs_of_nonneg (by linarith)] at hgap
    have hfd : f n - f (n + 1) = t * (Real.log (n + 1 : ℕ) - Real.log n) / (2 * π) := by
      simp only [hf, phaseOf]
      ring
    rw [hfd, hμ, div_le_div_iff₀ (by positivity) (by positivity)]
    have hN : ((n + 1 : ℕ) : ℝ) ≤ (X : ℝ) + H + 1 := by
      push_cast
      have : (n : ℝ) ≤ X + H := by exact_mod_cast hnH.le
      linarith
    have h1 : 1 ≤ ((X : ℝ) + H + 1) * (Real.log (n + 1 : ℕ) - Real.log n) := by
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      calc (1 : ℝ) = ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ := by field_simp
        _ ≤ ((X : ℝ) + H + 1) * (Real.log (n + 1 : ℕ) - Real.log n) :=
            mul_le_mul hN hgap (by positivity) (by positivity)
    have htp : 0 ≤ t * (2 * π) := by positivity
    calc t * (2 * π) = (t * (2 * π)) * 1 := by ring
      _ ≤ (t * (2 * π)) * (((X : ℝ) + H + 1) * (Real.log (n + 1 : ℕ) - Real.log n)) :=
          mul_le_mul_of_nonneg_left h1 htp
      _ = t * (Real.log (n + 1 : ℕ) - Real.log n) * (2 * π * (X + H + 1)) := by ring
  have h := card_near_lattice_le (f := f) (by omega : X ≤ X + H) hμ0 hδ hstep 0
  have hsub : (Icc X (X + H)).filter (fun n => dist01 (phaseOf t n) ≤ δ) ⊆
      (Icc X (X + H)).filter (fun n => ∃ m : ℤ, |f n - 0 - m| ≤ δ) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨hn1, -round (phaseOf t n), ?_⟩
    simp only [hf, sub_zero, Int.cast_neg]
    rw [show -phaseOf t n - -(round (phaseOf t n) : ℝ) = -(phaseOf t n - round (phaseOf t n)) by ring, abs_neg]
    exact hn2
  have hfab : f X - f (X + H) = t * (Real.log (X + H : ℕ) - Real.log X) / (2 * π) := by
    simp only [hf, phaseOf]
    ring
  have hdiv : 2 * δ / μ = 4 * π * δ * (X + H + 1) / t := by
    rw [hμ]
    field_simp
    ring
  rw [hfab, hdiv] at h
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans h

/-- **The comb inequality.** -/
theorem comb_inequality {P : Finset ℕ} {η t : ℝ} (ht : 0 < t) (hret : IsReturn P logStep η t)
    {X H k : ℕ} (hX : 1 ≤ X)
    (hsmooth : ∀ n ∈ Icc X (X + H), (∀ p, p.Prime → p ∣ n → p ∈ P) ∧ ArithmeticFunction.cardFactors n ≤ k) :
    (H + 1 : ℝ) ≤
      (t * (Real.log (X + H : ℕ) - Real.log X) / (2 * π) + 2) * (4 * π * (k * √(η / 8)) * (X + H + 1) / t + 1) := by
  classical
  have hδ : 0 ≤ (k : ℝ) * √(η / 8) := by positivity
  have hall : (Icc X (X + H)).filter (fun n => dist01 (phaseOf t n) ≤ (k : ℝ) * √(η / 8)) = Icc X (X + H) := by
    refine Finset.filter_true_of_mem fun n hn => ?_
    obtain ⟨hP, hk⟩ := hsmooth n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have h1 := dist01_le_of_isReturn hret n hn0 hP
    have h2 : (ArithmeticFunction.cardFactors n : ℝ) * √(η / 8) ≤ (k : ℝ) * √(η / 8) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (Real.sqrt_nonneg _)
    linarith
  have h := card_comb_le (H := H) ht hX hδ
  rw [hall, Nat.card_Icc] at h
  have e : ((X + H + 1 - X : ℕ) : ℝ) = (H : ℝ) + 1 := by
    rw [show X + H + 1 - X = H + 1 by omega]
    push_cast
    ring
  rw [e] at h
  exact h

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
