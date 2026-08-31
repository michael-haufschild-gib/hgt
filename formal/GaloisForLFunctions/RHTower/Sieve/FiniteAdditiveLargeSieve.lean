import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumFourier

/-!
# Exact finite additive large sieve

Additive-character orthogonality gives an exact Parseval identity for any injective family of
frequencies in `ZMod q`.  This weighted form is the finite large-sieve layer used by the
Kloosterman transform.
-/

open scoped BigOperators ComplexConjugate

namespace RHTower.Sieve

noncomputable section

/-- Exact weighted additive-character Parseval identity along an injective frequency family. -/
theorem sum_normSq_weighted_stdAddChar_mul_of_injective
    {ι : Type*} [Fintype ι]
    (q : ℕ) [NeZero q] (f : ι → ZMod q) (hf : Function.Injective f)
    (a : ι → ℂ) :
    ∑ n : ZMod q, Complex.normSq
        (∑ i : ι, a i * ZMod.stdAddChar (n * f i)) =
      (q : ℝ) * ∑ i : ι, Complex.normSq (a i) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  let K : ι → ι → ZMod q → ℂ := fun i j n =>
    star (a i * ZMod.stdAddChar (n * f i)) *
      (a j * ZMod.stdAddChar (n * f j))
  change (∑ n : ZMod q, ∑ j : ι, ∑ i : ι, K i j n) =
    ∑ i : ι, (q : ℂ) * ((starRingEnd ℂ) (a i) * a i)
  calc
    (∑ n : ZMod q, ∑ j : ι, ∑ i : ι, K i j n) =
        ∑ n : ZMod q, ∑ i : ι, ∑ j : ι, K i j n := by
      apply Finset.sum_congr rfl
      intro n _
      exact Finset.sum_comm
    _ = ∑ i : ι, ∑ n : ZMod q, ∑ j : ι, K i j n := Finset.sum_comm
    _ = ∑ i : ι, ∑ j : ι, ∑ n : ZMod q, K i j n := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ i : ι, ∑ j : ι, ((starRingEnd ℂ) (a i) * a j) *
          ∑ n : ZMod q, ZMod.stdAddChar (n * (f j - f i)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      dsimp only [K]
      rw [star_mul]
      change (starRingEnd ℂ) (ZMod.stdAddChar (n * f i)) *
          (starRingEnd ℂ) (a i) *
          (a j * ZMod.stdAddChar (n * f j)) = _
      rw [← AddChar.map_neg_eq_conj]
      calc
        ZMod.stdAddChar (-(n * f i)) * (starRingEnd ℂ) (a i) *
            (a j * ZMod.stdAddChar (n * f j)) =
            ((starRingEnd ℂ) (a i) * a j) *
              (ZMod.stdAddChar (-(n * f i)) * ZMod.stdAddChar (n * f j)) := by ring
        _ = ((starRingEnd ℂ) (a i) * a j) *
              ZMod.stdAddChar (-(n * f i) + n * f j) := by
          rw [AddChar.map_add_eq_mul]
        _ = _ := by
          congr 2
          ring
    _ = ∑ i : ι, ∑ j : ι, ((starRingEnd ℂ) (a i) * a j) *
          (if f j = f i then (q : ℂ) else 0) := by
      simp_rw [sum_stdAddChar_mul, sub_eq_zero]
      push_cast
      rfl
    _ = ∑ i : ι, (q : ℂ) * ((starRingEnd ℂ) (a i) * a i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp
        ring
      · intro j _ hji
        have hne : f j ≠ f i := fun h => hji (hf h)
        simp [hne]
      · simp

end

end RHTower.Sieve
