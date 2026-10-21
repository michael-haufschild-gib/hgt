import GaloisForLFunctions.BezoutValuationIncidence.OneNumeratorClustersAreShortIntervalSums

/-!
# Twisted short-interval cancellation gives window dispersion

Combine the numerator split with the cluster form of the one-numerator energies. Let `c` be a prime
packet on `S ⊆ (P, 2P]`, `1 ≤ a₀ ≤ P/2`, `2P ≤ N`, `M = N!`, and choose an arc length `L` with
`4KL ≤ M` and `4PL ≤ M`. Suppose that for every numerator `a ≤ a₀` the twisted sums of
`u(p, a) ω_p^{aX}` over primes in intervals of length `16P²L/(aM)` are at most `B_a`. Then

`Σ_{X ≤ m < X+K} F_c(m)²/(m(m+1)) ≤ (2/X²) (2 h_{a₀} Σ_{a ≤ a₀} a · 2(4M/L²)(a(M/(2P)) + L) B_a²
  + (K + 2N² - 1) Σ_p c(p)²/(8a₀))`.

With `L = M/(4K)` (arc length `1/(4K)`), the intervals have length `4P²/(aK)`. The factor is
`2(4M/L²)(a(M/(2P)) + L) = 64K²a/P + 32K`. The bound reads

`E_{[X,X+K)} ≲ X^{-2} (h_{a₀} Σ_{a ≤ a₀} (K²a²/P + Ka) B_a² + (K + N²) Σ c²/a₀)`.

Since `|u(p, a)| ≤ |c(p)|/(4a)`, twisted square-root cancellation `B_a ≤ η √(4P²/(aK)) |c|_∞/(4a)` for
`a ≤ a₀ = P²/(εX)` gives, on `[X, 2X)`, a window energy within `≍ (η² log² + ε) log P` of the
diagonal `Σ_p c(p)²/X`, at every window `P ≤ X ≤ P²`, i.e. for every exponent `1 ≤ θ ≤ 2`. With the
Type-II no-go of the coherent blocks, which have `B_a ≍ |I_a|`, this identifies the replacement
hypothesis exactly: twisted square-root cancellation of the packet over the intervals of length
`P²/(aX)` determined by the first `P²/X` numerators.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- **Twisted short-interval cancellation gives window dispersion.** -/
theorem window_energy_le_twisted_short_sums {N P a₀ X K L : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ P < p ∧ p ≤ 2 * P) (hP : 1 ≤ P) (hPN : 2 * P ≤ N) (ha₀ : 1 ≤ a₀)
    (ha₀P : 2 * a₀ ≤ P) (hX : 1 ≤ X) (hL : 1 ≤ L) (hKL : 4 * K * L ≤ N.factorial)
    (hPL : 4 * P * L ≤ N.factorial) {c : ℕ → ℝ} (hsupp : ∀ n, c n ≠ 0 → n ∈ S) (B : ℕ → ℝ)
    (hB : ∀ a ∈ Ico 1 (a₀ + 1), ∀ t₁ t₂ : ℝ, t₂ - t₁ ≤ 16 * (P : ℝ) ^ 2 * L / (a * N.factorial) →
      ‖∑ p ∈ S.filter (fun p : ℕ => t₁ < (p : ℝ) ∧ (p : ℝ) ≤ t₂),
        fareyCoeff c p a * (stdRoot p ^ a) ^ X‖ ≤ B a) :
    ∑ j ∈ range K, rowFluct N c (X + j) ^ 2 / (pronicSeq (X + j) : ℝ) ≤
      2 / (X : ℝ) ^ 2 * (2 * (∑ a ∈ Ico 1 (a₀ + 1), 1 / (a : ℝ)) *
          ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) * (2 * (4 * N.factorial / (L : ℝ) ^ 2 *
            ((a * (N.factorial / (2 * P)) : ℕ) + L) * B a ^ 2)) +
        ((K : ℝ) + 2 * (N : ℝ) ^ 2 - 1) * ∑ p ∈ S, c p ^ 2 / (8 * a₀)) := by
  have hS' : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ 2 * a₀ < p := fun p hp =>
    ⟨(hS p hp).1, by have := (hS p hp).2.2; omega, by have := (hS p hp).2.1; omega⟩
  have hsplit := window_energy_le_numerator_split hS' (by omega) ha₀ hX hsupp (K := K)
  refine hsplit.trans ?_
  have hh : 0 ≤ ∑ a ∈ Ico 1 (a₀ + 1), 1 / (a : ℝ) := sum_nonneg fun _ _ => by positivity
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (by positivity)
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun a ha => ?_) (by positivity)
  have ha' := mem_Ico.mp ha
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hconj : ∀ j, ‖conjNumeratorSum S c a (X + j)‖ = ‖numeratorSum S c a (X + j)‖ := fun j =>
    norm_conjNumeratorSum (fun p hp => ⟨(hS p hp).1.pos, by have := (hS p hp).2.1; omega⟩) c _
  rw [sum_congr rfl fun j _ => by rw [hconj j]]
  have hone := sum_numeratorSum_sq_le hS hP hPN ha'.1 (by omega) hL hKL
    (by nlinarith) c (X := X) (hB a ha)
  have htwo : ∑ j ∈ range K, (‖numeratorSum S c a (X + j)‖ ^ 2 + ‖numeratorSum S c a (X + j)‖ ^ 2) =
      2 * ∑ j ∈ range K, ‖numeratorSum S c a (X + j)‖ ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  rw [htwo]
  exact mul_le_mul_of_nonneg_left hone (by norm_num)

end

end GaloisForLFunctions.BezoutValuationIncidence
