import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitPairEnergy
import GaloisForLFunctions.RHTower.CCM.CCMPrimeEntryProductKernel
import GaloisForLFunctions.RHTower.LocalizedHalfDensityCurvature

/-!
# The actual critical prime-pair energy on multiplicative product layers

The finite square of prime entries is reindexed by nm. The exact ratio
kernel already vanishes beyond the terminal cutoff, so no spurious factors
are added when passing to the complete divisor antidiagonal. This connects
the full energy to the existing localized von Mangoldt product fibres.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

private theorem sum_square_by_product (F : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, F n m) =
      ∑ R ∈ Finset.Icc 1 (N * N), ∑ x ∈ R.divisorsAntidiagonal,
        if x.1 ≤ N ∧ x.2 ≤ N then F x.1 x.2 else 0 := by
  classical
  let S := (Finset.Icc 1 N).product (Finset.Icc 1 N)
  have hmap (x : ℕ × ℕ) (hx : x ∈ S) : x.1 * x.2 ∈ Finset.Icc 1 (N * N) := by
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
    obtain ⟨hx10, hx1N⟩ := Finset.mem_Icc.mp hx1
    obtain ⟨hx20, hx2N⟩ := Finset.mem_Icc.mp hx2
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hx10 hx20, Nat.mul_le_mul hx1N hx2N⟩
  have hset (R : ℕ) (hR : R ∈ Finset.Icc 1 (N * N)) :
      S.filter (fun x => x.1 * x.2 = R) =
        R.divisorsAntidiagonal.filter (fun x => x.1 ≤ N ∧ x.2 ≤ N) := by
    have hR0 : R ≠ 0 := Nat.ne_zero_of_lt (Finset.mem_Icc.mp hR).1
    ext x
    rcases x with ⟨n, m⟩
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨hx, hprod⟩
      obtain ⟨hn, hm⟩ := Finset.mem_product.mp hx
      exact ⟨⟨hprod, hR0⟩, (Finset.mem_Icc.mp hn).2, (Finset.mem_Icc.mp hm).2⟩
    · rintro ⟨⟨hprod, _⟩, hx1N, hx2N⟩
      have hx10 : n ≠ 0 := by
        intro h
        rw [h, zero_mul] at hprod
        exact hR0 hprod.symm
      have hx20 : m ≠ 0 := by
        intro h
        rw [h, mul_zero] at hprod
        exact hR0 hprod.symm
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hx1N⟩,
        Finset.mem_Icc.mpr ⟨by omega, hx2N⟩⟩, hprod⟩
  calc
    _ = ∑ x ∈ S, F x.1 x.2 := (Finset.sum_product _ _ _).symm
    _ = ∑ R ∈ Finset.Icc 1 (N * N), ∑ x ∈ S with x.1 * x.2 = R, F x.1 x.2 :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun x => F x.1 x.2)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [hset R hR, Finset.sum_filter]

/-- Exact descent of the actual finite pair energy to existing arithmetic
product fibres, retaining the product-dependent terminal ratio kernel. -/
theorem ccmPrimeEntryPairPrefix_eq_product_layers {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeEntryPairPrefix T ⌊Real.exp T⌋₊ =
      ∑ R ∈ Finset.Icc 1 (⌊Real.exp T⌋₊ * ⌊Real.exp T⌋₊),
        localizedVonMangoldtPair (ccmPrimeEntryProductKernel T R) R := by
  classical
  rw [ccmPrimeEntryPairPrefix, sum_square_by_product]
  apply Finset.sum_congr rfl
  intro R _
  unfold localizedVonMangoldtPair
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hprod, hR0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hx10 : 0 < x.1 := by
    by_contra h
    have hx1 : x.1 = 0 := by omega
    rw [hx1, zero_mul] at hprod
    exact hR0 hprod.symm
  have hx20 : 0 < x.2 := by
    by_contra h
    have hx2 : x.2 = 0 := by omega
    rw [hx2, mul_zero] at hprod
    exact hR0 hprod.symm
  rw [← hprod, ccmPrimeEntryProductKernel_log_ratio T hx10 hx20]
  split_ifs with hcut
  · rfl
  · have hlarge {n : ℕ} (hn : 0 < n) (hnot : ¬n ≤ ⌊Real.exp T⌋₊) : T < Real.log n := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      apply (Real.lt_log_iff_exp_lt hnR).mpr
      exact lt_of_not_ge fun h => hnot ((Nat.le_floor_iff (Real.exp_pos T).le).mpr h)
    rcases not_and_or.mp hcut with h1 | h2
    · rw [ccmPrimeEntryOverlap_eq_zero_of_left_ge hT (hlarge hx10 h1).le, mul_zero]
    · rw [ccmPrimeEntryOverlap_eq_zero_of_right_ge hT (hlarge hx20 h2).le, mul_zero]

/-- The centered full deficit energy, now on multiplicative product layers.
The continuous background and the signed mixed work are unchanged. -/
theorem ccmPrimeDeficitCriticalEnergy_integral_eq_product_layers {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
      Real.exp T - Real.exp (-T) - 2 * T -
        2 * ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ +
          ∑ R ∈ Finset.Icc 1 (⌊Real.exp T⌋₊ * ⌊Real.exp T⌋₊),
            localizedVonMangoldtPair (ccmPrimeEntryProductKernel T R) R := by
  rw [ccmPrimeDeficitCriticalEnergy_integral_eq_pair hT,
    ccmPrimeEntryPairPrefix_eq_product_layers hT]

/-- On a genuine two-prime product the two orientations reinforce. Any
cancellation estimate must still include the signed background/mixed work. -/
theorem localizedVonMangoldtPair_ccmPrimeEntryProductKernel_two_prime (T : ℝ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    localizedVonMangoldtPair (ccmPrimeEntryProductKernel T (p ^ a * q ^ b)) (p ^ a * q ^ b) =
      2 * Real.log p * Real.log q * ccmPrimeEntryProductKernel T (p ^ a * q ^ b)
        ((a : ℝ) * Real.log p - (b : ℝ) * Real.log q) :=
  localizedVonMangoldtPair_two_prime _ (ccmPrimeEntryProductKernel_even T _) hp hq hpq ha hb

end RHTower
