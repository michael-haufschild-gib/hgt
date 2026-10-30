import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingCoreObstruction
import GaloisForLFunctions.RHTower.MobiusDivisorUniformSuccessorTransport
import GaloisForLFunctions.RHTower.Sieve.InverseSquareTail

/-!
# Terminal leaf energy on the fourth-power mesh

The square of a prime singleton fibre is at most `9 M³ / (25 p²)`, uniformly in the
processed core. At a square cutoff `M = N²`, every prime outside the canonical
square-root core exceeds `N`. Summing the inverse-square tail bounds all nonempty
retained energy by `9 N⁵ / 25`. Its normalized fourth-power mesh prefix is cubic.
The head square is kept separate throughout this estimate.
-/

noncomputable section
open Finset
namespace RHTower

private theorem inverse_square_finset_tail (N : ℕ) (hN : 1 ≤ N) (S : Finset ℕ)
    (hS : ∀ p ∈ S, N < p) :
    (∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + N + 1) ^ 2
  have he (p : ℕ) (hp : p ∈ S) : f (p - (N + 1)) = 1 / (p : ℝ) ^ 2 := by
    have hid : p - (N + 1) + (N + 1) = p := Nat.sub_add_cancel (hS p hp)
    have hcast : ((p - (N + 1) : ℕ) : ℝ) + N + 1 = (p : ℝ) := by
      exact_mod_cast hid
    dsimp [f]
    rw [hcast]
  have hinj : Set.InjOn (fun p : ℕ => p - (N + 1)) (↑S) := by
    intro p hp q hq heq
    have hpN := hS p hp
    have hqN := hS q hq
    change p - (N + 1) = q - (N + 1) at heq
    omega
  calc
    _ = ∑ p ∈ S, f (p - (N + 1)) := sum_congr rfl (fun p hp => (he p hp).symm)
    _ = ∑ n ∈ S.image (fun p => p - (N + 1)), f n := (sum_image hinj).symm
    _ ≤ ∑' n : ℕ, f n :=
      (Sieve.summable_inv_sq_shift N).sum_le_tsum _ (fun _ _ => by positivity)
    _ ≤ 1 / (N : ℝ) := Sieve.tsum_inv_sq_shift_le hN

/-- The full prime-containing quotient budget bounds each singleton, without a condition on
the processed core or the signs of its coefficients. -/
theorem mobiusDivisorSelectionFibre_singleton_sq_le (M : ℕ) (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) :
    mobiusDivisorSelectionFibre M P {p} ^ 2 ≤ (9 / 25 : ℝ) * M ^ 3 / (p : ℝ) ^ 2 := by
  have hs := single_le_sum
    (fun R (_ : R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset) =>
      sq_nonneg (mobiusDivisorSelectionFibre M P (insert p R)))
    (mem_powerset.mpr (empty_subset _))
  simp only [insert_empty_eq] at hs
  have hq : ((M / p : ℕ) : ℝ) ^ 2 ≤ ((M : ℝ) / p) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr Nat.cast_div_le
  calc
    _ ≤ (9 / 25 : ℝ) * M * ((M / p : ℕ) : ℝ) ^ 2 :=
      hs.trans (sum_mobiusDivisorPrimeFibre_sq_le_quotient M P hp)
    _ ≤ (9 / 25 : ℝ) * M * ((M : ℝ) / p) ^ 2 :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by rw [div_pow]; ring

/-- Retaining only primes above `N` bounds their total singleton energy by an inverse-square tail. -/
theorem sum_mobiusDivisorSingleton_sq_le_tail (M N : ℕ) (P : Finset ℕ) (hN : 1 ≤ N)
    (hfront : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P, N < p) :
    (∑ p ∈ mobiusDivisorSelectionPrimes M \ P, mobiusDivisorSelectionFibre M P {p} ^ 2)
      ≤ (9 / 25 : ℝ) * M ^ 3 / N := by
  calc
    _ ≤ ∑ p ∈ mobiusDivisorSelectionPrimes M \ P, (9 / 25 : ℝ) * M ^ 3 / (p : ℝ) ^ 2 :=
      sum_le_sum (fun p hp => mobiusDivisorSelectionFibre_singleton_sq_le M P
        (mem_filter.mp (mem_sdiff.mp hp).1).2)
    _ = (9 / 25 : ℝ) * M ^ 3 *
        ∑ p ∈ mobiusDivisorSelectionPrimes M \ P, (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ (9 / 25 : ℝ) * M ^ 3 * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (inverse_square_finset_tail N hN _ hfront) (by positivity)
    _ = _ := by ring

/-- At `M = N²`, all nonempty fibres of the canonical core have total energy at most `9 N⁵ / 25`. -/
theorem criticalMovingSquareCore_leafEnergy_le (N : ℕ) :
    (∑ p ∈ mobiusDivisorSelectionPrimes (N ^ 2) \ criticalMovingSquareCore (N ^ 2),
      mobiusDivisorSelectionFibre (N ^ 2) (criticalMovingSquareCore (N ^ 2)) {p} ^ 2)
      ≤ (9 / 25 : ℝ) * (N : ℝ) ^ 5 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [mobiusDivisorSelectionPrimes]
  have hfront : ∀ p ∈ mobiusDivisorSelectionPrimes (N ^ 2) \ criticalMovingSquareCore (N ^ 2),
      N < p := by
    intro p hp
    obtain ⟨hpA, hpC⟩ := mem_sdiff.mp hp
    by_contra hn
    have hpN : p ≤ N := by omega
    apply hpC
    exact mem_filter.mpr ⟨hpA, by simpa only [pow_two] using Nat.pow_le_pow_left hpN 2⟩
  have hb := sum_mobiusDivisorSingleton_sq_le_tail (N ^ 2) N (criticalMovingSquareCore (N ^ 2))
    hN hfront
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have he : (9 / 25 : ℝ) * ((N ^ 2 : ℕ) : ℝ) ^ 3 / N = (9 / 25 : ℝ) * (N : ℝ) ^ 5 := by
    push_cast
    field_simp
  rwa [he] at hb

/-- The only part of canonical retained energy outside the `N⁵` bound is its head square. -/
theorem criticalMovingSquareCore_energy_sub_head_sq_le (N : ℕ) :
    mobiusDivisorSelectionEnergy (N ^ 2) (criticalMovingSquareCore (N ^ 2)) -
      mobiusDivisorSelectionFibre (N ^ 2) (criticalMovingSquareCore (N ^ 2)) ∅ ^ 2
      ≤ (9 / 25 : ℝ) * (N : ℝ) ^ 5 := by
  have hterminal : mobiusDivisorSmallSelectionPrimes (N ^ 2) ⊆ criticalMovingSquareCore (N ^ 2) := by
    intro p hp
    obtain ⟨hp, hsq⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp, hsq.le⟩
  rw [mobiusDivisorSelectionEnergy_terminal _ _ hterminal, add_sub_cancel_left]
  exact criticalMovingSquareCore_leafEnergy_le N

/-- On the fourth-power mesh, normalized nonempty retained energy has a quadratic pointwise bound. -/
theorem criticalMovingSquareCore_fourthMesh_leafEnergy_le (j : ℕ) :
    (∑ p ∈ mobiusDivisorSelectionPrimes (j ^ 4) \ criticalMovingSquareCore (j ^ 4),
      mobiusDivisorSelectionFibre (j ^ 4) (criticalMovingSquareCore (j ^ 4)) {p} ^ 2) /
        (j : ℝ) ^ 8 ≤ (9 / 25 : ℝ) * (j : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · norm_num
  have hb := criticalMovingSquareCore_leafEnergy_le (j ^ 2)
  rw [← pow_mul] at hb
  norm_num only [Nat.cast_pow, ← pow_mul] at hb
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) ^ 8)).mpr
  calc
    _ ≤ (9 / 25 : ℝ) * (j : ℝ) ^ 10 := hb
    _ = _ := by ring

/-- The complete normalized terminal-leaf prefix fits the cubic fourth-power mesh scale. -/
theorem criticalMovingSquareCore_fourthMesh_leafPrefix_le (J : ℕ) :
    (∑ j ∈ Icc 1 J,
      (∑ p ∈ mobiusDivisorSelectionPrimes (j ^ 4) \ criticalMovingSquareCore (j ^ 4),
        mobiusDivisorSelectionFibre (j ^ 4) (criticalMovingSquareCore (j ^ 4)) {p} ^ 2) /
          (j : ℝ) ^ 8) ≤ (9 / 25 : ℝ) * (J : ℝ) ^ 3 := by
  calc
    _ ≤ ∑ j ∈ Icc 1 J, (9 / 25 : ℝ) * (j : ℝ) ^ 2 :=
      sum_le_sum (fun j _ => criticalMovingSquareCore_fourthMesh_leafEnergy_le j)
    _ ≤ ∑ _j ∈ Icc 1 J, (9 / 25 : ℝ) * (J : ℝ) ^ 2 := by
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
      exact_mod_cast (mem_Icc.mp hj).2
    _ = _ := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring

end RHTower
