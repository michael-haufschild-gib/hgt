import GaloisForLFunctions.RHTower.MobiusCofactorAmplifiedToken

/-!
# Cofactor parity balance without a signed Möbius estimate

Both Möbius parity classes of band-avoiding cofactors carry the same harmonic mass, and this needs
no cancellation estimate for a signed Möbius sum.  The reason is the elementary pairing
`s ↔ 2s`: if the fixed prime `2` lies below the excluded band, then doubling an odd band-avoiding
squarefree cofactor stays band-avoiding, stays squarefree, and reverses the Möbius sign.  So each
odd source cofactor supplies exactly one member of the requested parity class, at the cost of a
factor two in its reciprocal.

This is the structural half of the card's `(7)` and `(9)`.  The classical unsigned squarefree
harmonic estimate, which turns the resulting lower bound into `≍ √T` and `≍ log T`, is a separate
input.
-/

open Finset

namespace RHTower

namespace CofactorParity

variable (Band : ℕ → Prop) [DecidablePred Band]

/-- The cofactors below `T` of one Möbius parity class that avoid a band of primes. -/
def parityClass (σ : ℤ) (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter fun t =>
    ArithmeticFunction.moebius t = σ ∧ ∀ p ∈ t.primeFactors, ¬ Band p

/-- The odd squarefree band-avoiding cofactors below `T/2`, the source of the pairing. -/
def oddBase (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (T / 2)).filter fun s =>
    Squarefree s ∧ ¬ (2 ∣ s) ∧ ∀ p ∈ s.primeFactors, ¬ Band p

variable {Band}

/-- The pairing map: keep `s` when it already carries the target parity, otherwise double it. -/
def pairMap (σ : ℤ) (s : ℕ) : ℕ :=
  if ArithmeticFunction.moebius s = σ then s else 2 * s

theorem moebius_eq_one_or_neg_one {n : ℕ} (hn : Squarefree n) :
    ArithmeticFunction.moebius n = 1 ∨ ArithmeticFunction.moebius n = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn]
  rcases Nat.even_or_odd (ArithmeticFunction.cardFactors n) with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

theorem coprime_two_of_not_dvd {s : ℕ} (hs : ¬ (2 ∣ s)) : Nat.Coprime 2 s :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hs

/-- Doubling an odd cofactor reverses the Möbius sign. -/
theorem moebius_two_mul {s : ℕ} (hs : ¬ (2 ∣ s)) :
    ArithmeticFunction.moebius (2 * s) = -ArithmeticFunction.moebius s := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (coprime_two_of_not_dvd hs),
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

theorem mem_oddBase_iff {T s : ℕ} :
    s ∈ oddBase Band T ↔
      (1 ≤ s ∧ s ≤ T / 2) ∧ Squarefree s ∧ ¬ (2 ∣ s) ∧ ∀ p ∈ s.primeFactors, ¬ Band p := by
  rw [oddBase, Finset.mem_filter, Finset.mem_Icc]

theorem mem_parityClass_iff {σ : ℤ} {T t : ℕ} :
    t ∈ parityClass Band σ T ↔
      (1 ≤ t ∧ t ≤ T) ∧ ArithmeticFunction.moebius t = σ ∧ ∀ p ∈ t.primeFactors, ¬ Band p := by
  rw [parityClass, Finset.mem_filter, Finset.mem_Icc]

/-- The pairing lands in the requested parity class. -/
theorem pairMap_mem (hband : ¬ Band 2) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {T s : ℕ}
    (hs : s ∈ oddBase Band T) : pairMap σ s ∈ parityClass Band σ T := by
  rw [mem_oddBase_iff] at hs
  obtain ⟨⟨hs1, hsT⟩, hsq, hodd, hbandfree⟩ := hs
  have hs0 : s ≠ 0 := by omega
  rw [mem_parityClass_iff, pairMap]
  by_cases hpar : ArithmeticFunction.moebius s = σ
  · rw [if_pos hpar]
    exact ⟨⟨hs1, le_trans hsT (Nat.div_le_self T 2)⟩, hpar, hbandfree⟩
  · rw [if_neg hpar]
    have hle : 2 * s ≤ T := by
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hsT
      omega
    have hmu : ArithmeticFunction.moebius (2 * s) = σ := by
      rw [moebius_two_mul hodd]
      rcases moebius_eq_one_or_neg_one hsq with h | h <;> rcases hσ with hs' | hs' <;>
        simp_all
    refine ⟨⟨by omega, hle⟩, hmu, ?_⟩
    intro p hp
    rw [Nat.primeFactors_mul (by norm_num) hs0] at hp
    rcases Finset.mem_union.mp hp with h | h
    · rw [Nat.Prime.primeFactors Nat.prime_two, Finset.mem_singleton] at h
      rw [h]
      exact hband
    · exact hbandfree p h

theorem pairMap_le {σ : ℤ} {s : ℕ} : pairMap σ s ≤ 2 * s := by
  rw [pairMap]
  split_ifs
  · omega
  · omega

theorem one_le_pairMap {σ : ℤ} {s : ℕ} (hs : 1 ≤ s) : 1 ≤ pairMap σ s := by
  rw [pairMap]
  split_ifs <;> omega

theorem odd_of_mem_oddBase {T s : ℕ} (hs : s ∈ oddBase Band T) : ¬ (2 ∣ s) :=
  ((mem_oddBase_iff).mp hs).2.2.1

/-- The pairing is injective: an odd cofactor is never the double of another. -/
theorem pairMap_injOn {σ : ℤ} {T : ℕ} : Set.InjOn (pairMap σ) (oddBase Band T) := by
  intro a ha b hb hab
  have hoa : ¬ (2 ∣ a) := odd_of_mem_oddBase ha
  have hob : ¬ (2 ∣ b) := odd_of_mem_oddBase hb
  rw [pairMap, pairMap] at hab
  by_cases hA : ArithmeticFunction.moebius a = σ <;> by_cases hB :
      ArithmeticFunction.moebius b = σ
  · rwa [if_pos hA, if_pos hB] at hab
  · rw [if_pos hA, if_neg hB] at hab
    exact absurd ⟨b, hab⟩ hoa
  · rw [if_neg hA, if_pos hB] at hab
    exact absurd ⟨a, hab.symm⟩ hob
  · rw [if_neg hA, if_neg hB] at hab
    omega

/-- **The parity-balance inequality.**  Each parity class of band-avoiding cofactors carries at
least half the harmonic mass of the odd band-avoiding squarefree cofactors below `T/2`.  No signed
Möbius estimate is used: the pairing `s ↔ 2s` supplies the class directly. -/
theorem half_sum_oddBase_le_sum_parityClass (hband : ¬ Band 2) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (T : ℕ) :
    (1 / 2 : ℝ) * ∑ s ∈ oddBase Band T, ((s : ℝ))⁻¹
      ≤ ∑ t ∈ parityClass Band σ T, ((t : ℝ))⁻¹ := by
  classical
  have hsub : (oddBase Band T).image (pairMap σ) ⊆ parityClass Band σ T := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    exact pairMap_mem hband hσ hs
  have himg : ∑ q ∈ (oddBase Band T).image (pairMap σ), ((q : ℝ))⁻¹
      = ∑ s ∈ oddBase Band T, ((pairMap σ s : ℝ))⁻¹ :=
    Finset.sum_image (f := fun q : ℕ => ((q : ℝ))⁻¹) pairMap_injOn
  have hterm : ∀ s ∈ oddBase Band T, (1 / 2 : ℝ) * ((s : ℝ))⁻¹ ≤ ((pairMap σ s : ℝ))⁻¹ := by
    intro s hs
    have hs1 : 1 ≤ s := ((mem_oddBase_iff).mp hs).1.1
    have hp1 : 1 ≤ pairMap σ s := one_le_pairMap hs1
    have hple : (pairMap σ s : ℝ) ≤ 2 * (s : ℝ) := by
      have := pairMap_le (σ := σ) (s := s)
      exact_mod_cast this
    have hppos : (0 : ℝ) < (pairMap σ s : ℝ) := by exact_mod_cast hp1
    have hstep : 1 / (2 * (s : ℝ)) ≤ 1 / (pairMap σ s : ℝ) :=
      one_div_le_one_div_of_le hppos hple
    have hrw : (1 / 2 : ℝ) * ((s : ℝ))⁻¹ = 1 / (2 * (s : ℝ)) := by
      rw [one_div, ← mul_inv]
      norm_num
    rw [hrw, ← one_div]
    exact hstep
  calc (1 / 2 : ℝ) * ∑ s ∈ oddBase Band T, ((s : ℝ))⁻¹
      = ∑ s ∈ oddBase Band T, (1 / 2 : ℝ) * ((s : ℝ))⁻¹ := by rw [Finset.mul_sum]
    _ ≤ ∑ s ∈ oddBase Band T, ((pairMap σ s : ℝ))⁻¹ := Finset.sum_le_sum hterm
    _ = ∑ q ∈ (oddBase Band T).image (pairMap σ), ((q : ℝ))⁻¹ := himg.symm
    _ ≤ ∑ t ∈ parityClass Band σ T, ((t : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity

/-! ## The dyadic slice count -/

theorem dyadic_mem_iff {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (k : ℤ) :
    (A ≤ (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k ≤ B)
      ↔ Real.log A / Real.log 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ Real.log B / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hpow : Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := Real.log_zpow 2 k
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hl2, ← hpow]
      exact (Real.log_le_log_iff hA hkpos).mpr h1
    · rw [le_div_iff₀ hl2, ← hpow]
      exact (Real.log_le_log_iff hkpos hB).mpr h2
  · rintro ⟨h1, h2⟩
    rw [div_le_iff₀ hl2, ← hpow] at h1
    rw [le_div_iff₀ hl2, ← hpow] at h2
    exact ⟨(Real.log_le_log_iff hA hkpos).mp h1, (Real.log_le_log_iff hkpos hB).mp h2⟩

theorem mem_dyadicSlices {A B : ℝ} (k : ℤ) :
    k ∈ Finset.Icc ⌈Real.log A / Real.log 2⌉ ⌊Real.log B / Real.log 2⌋
      ↔ Real.log A / Real.log 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ Real.log B / Real.log 2 := by
  rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor]

/-- **(6a).**  The dyadic slices inside `[A, B]` number at least `log(B/A)/log 2 - 1`.  Applied to
`A = L^{a₀}`, `B = 2 L^{a₁}` this is the `≍ (a₁-a₀) log log U` slice count. -/
theorem le_card_dyadicSlices {A B : ℝ} :
    (Real.log B - Real.log A) / Real.log 2 - 1
      ≤ ((Finset.Icc ⌈Real.log A / Real.log 2⌉ ⌊Real.log B / Real.log 2⌋).card : ℝ) := by
  set α : ℝ := Real.log A / Real.log 2 with hα
  set β : ℝ := Real.log B / Real.log 2 with hβ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiff : (Real.log B - Real.log A) / Real.log 2 = β - α := by
    rw [hα, hβ]
    ring
  have h1 : β - 1 < (⌊β⌋ : ℝ) := Int.sub_one_lt_floor β
  have h2 : (⌈α⌉ : ℝ) < α + 1 := Int.ceil_lt_add_one α
  rw [hdiff, Int.card_Icc]
  rcases le_or_gt (0 : ℤ) (⌊β⌋ + 1 - ⌈α⌉) with h | h
  · have hcast : (((⌊β⌋ + 1 - ⌈α⌉).toNat : ℕ) : ℝ) = (⌊β⌋ : ℝ) + 1 - (⌈α⌉ : ℝ) := by
      have hz := Int.toNat_of_nonneg h
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) hz
    rw [hcast]
    linarith
  · have hz : ((⌊β⌋ + 1 - ⌈α⌉ : ℤ) : ℝ) < 0 := by exact_mod_cast h
    push_cast at hz
    have : (((⌊β⌋ + 1 - ⌈α⌉).toNat : ℕ) : ℝ) = 0 := by
      have : (⌊β⌋ + 1 - ⌈α⌉).toNat = 0 := Int.toNat_of_nonpos (by omega)
      rw [this]
      norm_num
    rw [this]
    linarith

end CofactorParity

end RHTower
