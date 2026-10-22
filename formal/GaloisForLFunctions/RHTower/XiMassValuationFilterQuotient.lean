import GaloisForLFunctions.RHTower.XiMassValuationOnePrimeQuotient

/-!
# Valuation filters of the mass prime source and RH

A valuation filter `b : ℕ → ℂ` reweights the centered mass atom at each prime power `p^r` by
`b r`, giving the filtered layer `b 1 · (prime layer) + b 2 · (prime-square layer) +
∑_{p, k} b (k+3) · atom(p^{k+3})`. For a bounded filter, everything except the valuation-one part
is bounded on every positive vertical line. Hence a filter with `b 1 = 0` always yields a bounded
layer, while for `b 1 ≠ 0` the filtered layer is bounded on `Re τ = σ` iff the prime layer is,
which is equivalent to the Riemann Hypothesis.

## Main results

- `norm_xiMassValuationFilteredHighTail_vertical_le`: the filtered high tail is bounded by
  `L · (∑_{p, k} log p · p^{-(k+3)/2}) · ∫ e^{-σ|x|} dx` on `Re τ = σ`.
- `xiMassValuationFilteredLineBound_of_depthOne_eq_zero`: if `b 1 = 0`, the filtered layer is
  bounded on the line.
- `xiMassValuationFilteredLineBound_iff_valuationOne`: if `b 1 ≠ 0`, filtered boundedness is
  equivalent to prime-layer boundedness.
- `riemannHypothesis_iff_xiMassValuationFilteredLineBound`: for bounded `b` with `b 1 ≠ 0`,
  RH is equivalent to boundedness of the filtered layer on one vertical line.

## Hypotheses

All results are unconditional. The filter is assumed bounded, `‖b r‖ ≤ L` for all `r` with
`0 ≤ L`; the equivalences additionally assume `b 1 ≠ 0`. Parameter ranges are `0 < a`, `0 < σ`
and, for the RH criterion, `1/2 < c < a`. The line-bound predicates occur only as sides of the
equivalences or as conclusions.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Filtered high tail `∑_{p, k} b (k+3) · atom(p^{k+3})` over prime powers of exponent `≥ 3`. -/
def xiMassValuationFilteredHighTail
    (b : ℕ → ℂ) (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' pk : Nat.Primes × ℕ,
    b (pk.2 + 3) *
      xiMassCenteredPrimeAtom a τ ((pk.1 : ℕ) ^ (pk.2 + 3))

/-- The valuation-filtered layer: each prime-power atom `p^r` is weighted by `b r`. -/
def xiMassValuationFilteredLayer
    (b : ℕ → ℂ) (a : ℝ) (τ : ℂ) : ℂ :=
  b 1 * xiMassValuationOnePrimeLayer a τ +
  b 2 * xiMassPrimeSquareLayer a τ +
  xiMassValuationFilteredHighTail b a τ

/-- The filtered layer is bounded along the vertical line `τ = σ + iu`, `u ∈ ℝ`. -/
def XiMassValuationFilteredLineBound
    (b : ℕ → ℂ) (a σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiMassValuationFilteredLayer b a ((σ : ℂ) + u * I)‖ ≤ C

theorem summable_norm_xiMassValuationFilteredHighAtom
    {b : ℕ → ℂ} {L a σ : ℝ}
    (_hL : 0 ≤ L) (hb : ∀ r : ℕ, ‖b r‖ ≤ L)
    (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ‖b (pk.2 + 3) *
        xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
          ((pk.1 : ℕ) ^ (pk.2 + 3))‖) := by
  have hatom := summable_norm_xiMassHighPrimePowerAtom ha hσ u
  exact (hatom.mul_left L).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun pk => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))

theorem summable_xiMassValuationFilteredHighAtom
    {b : ℕ → ℂ} {L a σ : ℝ}
    (hL : 0 ≤ L) (hb : ∀ r : ℕ, ‖b r‖ ≤ L)
    (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun pk : Nat.Primes × ℕ =>
      b (pk.2 + 3) *
        xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
          ((pk.1 : ℕ) ^ (pk.2 + 3))) :=
  summable_norm_iff.mp
    (summable_norm_xiMassValuationFilteredHighAtom hL hb ha hσ u)

/-- Assuming `‖b r‖ ≤ L` for all `r`, and `a, σ > 0`, the filtered high tail on `Re τ = σ` is
bounded by `L · (∑_{p, k} log p · p^{-(k+3)/2}) · ∫ e^{-σ|x|} dx`. -/
theorem norm_xiMassValuationFilteredHighTail_vertical_le
    {b : ℕ → ℂ} {L a σ : ℝ}
    (hL : 0 ≤ L) (hb : ∀ r : ℕ, ‖b r‖ ≤ L)
    (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    ‖xiMassValuationFilteredHighTail b a ((σ : ℂ) + u * I)‖ ≤
      L * ((∑' pk : Nat.Primes × ℕ,
        xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2)) *
          (∫ x : ℝ, Real.exp (-σ * |x|))) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-σ * |x|)
  have hmajor : Summable (fun pk : Nat.Primes × ℕ =>
      L * (xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2) * J)) :=
    (summable_xiMassPrimePowerCriticalWeight_high.mul_right J).mul_left L
  have hnorm := summable_norm_xiMassValuationFilteredHighAtom hL hb ha hσ u
  calc
    ‖xiMassValuationFilteredHighTail b a ((σ : ℂ) + u * I)‖ ≤
        ∑' pk : Nat.Primes × ℕ,
          ‖b (pk.2 + 3) *
            xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
              ((pk.1 : ℕ) ^ (pk.2 + 3))‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' pk : Nat.Primes × ℕ,
        L * (xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2) * J) := by
      apply hnorm.tsum_le_tsum
      · rintro ⟨p, k⟩
        rw [norm_mul]
        have hatom := norm_xiMassCenteredPrimeAtom_primePower_le
          ha hσ u p (k + 2)
        have hk : k + 2 + 1 = k + 3 := by omega
        calc
          ‖b (k + 3)‖ *
              ‖xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
                ((p : ℕ) ^ (k + 3))‖ ≤
            L * ‖xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
                ((p : ℕ) ^ (k + 3))‖ :=
              mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
          _ ≤ L * (xiMassPrimePowerCriticalWeight p (k + 2) * J) :=
              mul_le_mul_of_nonneg_left (by
                simpa only [J, hk, neg_mul] using hatom) hL
      · exact hmajor
    _ = L * ((∑' pk : Nat.Primes × ℕ,
        xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2)) * J) := by
      rw [tsum_mul_left, tsum_mul_right]
    _ = _ := by rfl

/-- For a bounded filter and `a, σ > 0`, the non-primitive part `b 2 · (square layer) +
(filtered high tail)` is bounded on the vertical line `Re τ = σ`. -/
theorem exists_norm_xiMassValuationFilteredNonPrimitive_vertical_bound
    {b : ℕ → ℂ} {L a σ : ℝ}
    (hL : 0 ≤ L) (hb : ∀ r : ℕ, ‖b r‖ ≤ L)
    (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖b 2 * xiMassPrimeSquareLayer a ((σ : ℂ) + u * I) +
        xiMassValuationFilteredHighTail b a ((σ : ℂ) + u * I)‖ ≤ B := by
  obtain ⟨B₂, hB₂⟩ := exists_norm_xiMassPrimeSquareLayer_vertical_bound ha hσ
  let Bₕ : ℝ :=
    L * ((∑' pk : Nat.Primes × ℕ,
      xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2)) *
        (∫ x : ℝ, Real.exp (-σ * |x|)))
  refine ⟨L * B₂ + Bₕ, fun u => ?_⟩
  calc
    ‖b 2 * xiMassPrimeSquareLayer a ((σ : ℂ) + u * I) +
        xiMassValuationFilteredHighTail b a ((σ : ℂ) + u * I)‖ ≤
      ‖b 2 * xiMassPrimeSquareLayer a ((σ : ℂ) + u * I)‖ +
        ‖xiMassValuationFilteredHighTail b a ((σ : ℂ) + u * I)‖ :=
          norm_add_le _ _
    _ ≤ L * B₂ + Bₕ := by
      apply add_le_add
      · rw [norm_mul]
        exact (mul_le_mul (hb 2) (hB₂ u) (norm_nonneg _) hL)
      · exact norm_xiMassValuationFilteredHighTail_vertical_le hL hb ha hσ u

/-- A bounded filter that kills valuation one (`b 1 = 0`) gives a filtered layer bounded on every
positive vertical line, unconditionally. -/
theorem xiMassValuationFilteredLineBound_of_depthOne_eq_zero
    {b : ℕ → ℂ} {L a σ : ℝ}
    (hL : 0 ≤ L) (hb : ∀ r : ℕ, ‖b r‖ ≤ L)
    (hb1 : b 1 = 0) (ha : 0 < a) (hσ : 0 < σ) :
    XiMassValuationFilteredLineBound b a σ := by
  obtain ⟨B, hB⟩ :=
    exists_norm_xiMassValuationFilteredNonPrimitive_vertical_bound hL hb ha hσ
  refine ⟨B, fun u => ?_⟩
  simpa [xiMassValuationFilteredLayer, hb1] using hB u

/-- For a bounded filter with `b 1 ≠ 0` and `a, σ > 0`, the filtered layer is bounded on
`Re τ = σ` iff the valuation-one prime layer is. -/
theorem xiMassValuationFilteredLineBound_iff_valuationOne
    {b : ℕ → ℂ} {L a σ : ℝ}
    (hL : 0 ≤ L) (hb : ∀ r : ℕ, ‖b r‖ ≤ L)
    (hb1 : b 1 ≠ 0) (ha : 0 < a) (hσ : 0 < σ) :
    XiMassValuationFilteredLineBound b a σ ↔
      XiMassValuationOnePrimeLineBound a σ := by
  obtain ⟨B, hB⟩ :=
    exists_norm_xiMassValuationFilteredNonPrimitive_vertical_bound hL hb ha hσ
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖(b 1)⁻¹‖ * (C + B), fun u => ?_⟩
    let R : ℂ :=
      b 2 * xiMassPrimeSquareLayer a ((σ : ℂ) + u * I) +
        xiMassValuationFilteredHighTail b a ((σ : ℂ) + u * I)
    have heq :
        xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I) =
          (b 1)⁻¹ *
            (xiMassValuationFilteredLayer b a ((σ : ℂ) + u * I) - R) := by
      rw [xiMassValuationFilteredLayer]
      dsimp only [R]
      field_simp
      ring
    rw [heq, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((norm_sub_le _ _).trans (add_le_add (hC u) (hB u))) (norm_nonneg _)
  · rintro ⟨C, hC⟩
    refine ⟨‖b 1‖ * C + B, fun u => ?_⟩
    let R : ℂ :=
      b 2 * xiMassPrimeSquareLayer a ((σ : ℂ) + u * I) +
        xiMassValuationFilteredHighTail b a ((σ : ℂ) + u * I)
    have heq :
        xiMassValuationFilteredLayer b a ((σ : ℂ) + u * I) =
          b 1 * xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I) + R := by
      simp only [xiMassValuationFilteredLayer, R, add_assoc]
    rw [heq]
    exact (norm_add_le _ _).trans
      (add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _))
        (hB u))

/-- RH criterion: for a bounded filter with `b 1 ≠ 0`, `1/2 < c < a` and `0 < σ`, the Riemann
Hypothesis is equivalent to boundedness of the filtered layer on the vertical line `Re τ = σ`. -/
theorem riemannHypothesis_iff_xiMassValuationFilteredLineBound
    {b : ℕ → ℂ} {L a c σ : ℝ}
    (hL : 0 ≤ L) (hb : ∀ r : ℕ, ‖b r‖ ≤ L)
    (hb1 : b 1 ≠ 0)
    (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 0 < σ) :
    RiemannHypothesis ↔ XiMassValuationFilteredLineBound b a σ := by
  have ha : 0 < a := by linarith
  exact (riemannHypothesis_iff_xiMassValuationOnePrimeLineBound hhalf hca hσ).trans
    (xiMassValuationFilteredLineBound_iff_valuationOne hL hb hb1 ha hσ).symm

end

end RHTower
