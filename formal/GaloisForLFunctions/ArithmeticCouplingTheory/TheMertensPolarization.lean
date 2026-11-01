import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# The Mertens polarization of the prime dilation form

On narrow atoms at the positions `log n`, `1 ≤ n ≤ N`, with amplitudes `F(n)/√n`, the prime part of
Weil's form only pairs `n` with its dilates `kn`. Its value is the **prime dilation form**

  `P_N(F) = Σ_{kn ≤ N} (Λ(k)/k) · 2F(n)F(kn)/n`.

Polarizing `2F(n)F(kn) = F(n)² + F(kn)² − (F(kn) − F(n))²` splits it into a diagonal and the
**dilation jump energy** `J_N(F) = Σ_{kn ≤ N} (Λ(k)/k)(F(kn) − F(n))²/n ≥ 0`. In the diagonal the two
halves collapse exactly:

* `Σ_{kn ≤ N} (Λ(k)/k) F(n)²/n = Σ_{n ≤ N} F(n)²/n · ψ₁(⌊N/n⌋)`, with the Mertens sum
  `ψ₁(M) = Σ_{k ≤ M} Λ(k)/k` (`sum_dilation_source_eq`);
* `Σ_{kn ≤ N} (Λ(k)/k) F(kn)²/n = Σ_{m ≤ N} F(m)² log m / m`, since `Σ_{k | m} Λ(k) = log m`
  (`sum_dilation_target_eq`).

**Mertens polarization** (`primeDilationForm_eq`): for every `F` and `N`,

  `P_N(F) = Σ_{n ≤ N} F(n)²/n · (ψ₁(⌊N/n⌋) + log n) − J_N(F)`.

The `log n` growth of the Mertens sum is cancelled exactly by the divisor identity; what remains is
`log N` (the running counterterm), the Mertens defect `ψ₁(M) − log M → −γ`, and a floor term.

On the **coherent prime sector** — prime-incidence packets `F_b(n) = Σ_{p ∈ P} b_p([p ∣ n] − 1/p)` —
every jump is an event (`incidencePacket_dilation_jump`): for a prime power `k = q^j`,
`F_b(kn) − F_b(n) = b_q [q ∈ P][q ∤ n]`. So `J_N(F_b)` is a weighted count of nondivisibility events
(`jumpEnergy_incidencePacket`), and the prime form on the coherent sector is a sum of incidence
squares minus an exact Mertens term (`primeDilationForm_incidencePacket`).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- The dilation pairs `(k, n)`, `k, n ≥ 1`, `kn ≤ N`. -/
def dilationPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 N ×ˢ Icc 1 N).filter fun p => p.1 * p.2 ≤ N

/-- The Mertens sum `ψ₁(M) = Σ_{k ≤ M} Λ(k)/k`. -/
def mertensSum (M : ℕ) : ℝ := ∑ k ∈ Icc 1 M, Λ k / k

/-- The prime dilation form `P_N(F) = Σ_{kn ≤ N} (Λ(k)/k) · 2F(n)F(kn)/n`. -/
def primeDilationForm (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ p ∈ dilationPairs N, Λ p.1 / p.1 * (2 * F p.2 * F (p.1 * p.2) / p.2)

/-- The dilation jump energy `J_N(F) = Σ_{kn ≤ N} (Λ(k)/k)(F(kn) − F(n))²/n`. -/
def jumpEnergy (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ p ∈ dilationPairs N, Λ p.1 / p.1 * ((F (p.1 * p.2) - F p.2) ^ 2 / p.2)

/-- The Mertens diagonal `Σ_{n ≤ N} F(n)²/n · (ψ₁(⌊N/n⌋) + log n)`. -/
def mertensDiagonal (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, F n ^ 2 / n * (mertensSum (N / n) + Real.log n)

theorem jumpEnergy_nonneg (N : ℕ) (F : ℕ → ℝ) : 0 ≤ jumpEnergy N F :=
  sum_nonneg fun _ _ => mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

theorem mem_dilationPairs {N : ℕ} {p : ℕ × ℕ} :
    p ∈ dilationPairs N ↔ 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 * p.2 ≤ N := by
  simp only [dilationPairs, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, h2, -⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨⟨h1, ?_⟩, h2, ?_⟩, h3⟩
    · exact (Nat.le_mul_of_pos_right _ h2).trans h3
    · exact (Nat.le_mul_of_pos_left _ h1).trans h3

/-- Dilation pairs are fibred over the base point: `(k, n)` with `k ≤ ⌊N/n⌋`. -/
theorem sum_dilationPairs_eq (N : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ p ∈ dilationPairs N, g p.1 p.2 = ∑ n ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / n), g k n := by
  have hset : dilationPairs N = (Icc 1 N).sigma (fun n => Icc 1 (N / n)) |>.map
      ⟨fun x => (x.2, x.1), fun x y h => by
        simp only [Prod.mk.injEq] at h; exact Sigma.ext h.2 (heq_of_eq h.1)⟩ := by
    ext ⟨k, n⟩
    simp only [mem_dilationPairs, mem_map, mem_sigma, mem_Icc, Function.Embedding.coeFn_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hk, hn, hkn⟩
      refine ⟨⟨n, k⟩, ⟨⟨hn, (Nat.le_mul_of_pos_left _ hk).trans hkn⟩, hk,
        (Nat.le_div_iff_mul_le hn).mpr hkn⟩, rfl, rfl⟩
    · rintro ⟨⟨n', k'⟩, ⟨⟨hn, -⟩, hk, hkN⟩, rfl, rfl⟩
      exact ⟨hk, hn, (Nat.le_div_iff_mul_le hn).mp hkN⟩
  rw [hset, sum_map, sum_sigma]
  rfl

/-- The source half of the diagonal: summing over `k ≤ ⌊N/n⌋` gives the Mertens sum. -/
theorem sum_dilation_source_eq (N : ℕ) (G : ℕ → ℝ) :
    ∑ p ∈ dilationPairs N, Λ p.1 / p.1 * G p.2 = ∑ n ∈ Icc 1 N, G n * mertensSum (N / n) := by
  rw [sum_dilationPairs_eq N (fun k n => Λ k / k * G n)]
  refine sum_congr rfl fun n _ => ?_
  simp only [mertensSum, mul_sum]
  exact sum_congr rfl fun k _ => by ring

/-- The target half of the diagonal: grouping `kn = m` gives `Σ_{k | m} Λ(k) = log m`. -/
theorem sum_dilation_target_eq (N : ℕ) (G : ℕ → ℝ) :
    ∑ p ∈ dilationPairs N, Λ p.1 / p.1 * (G (p.1 * p.2) / p.2) =
      ∑ m ∈ Icc 1 N, G m * Real.log m / m := by
  have hset : dilationPairs N = (Icc 1 N).biUnion Nat.divisorsAntidiagonal := by
    ext ⟨k, n⟩
    simp only [mem_dilationPairs, mem_biUnion, mem_Icc, Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨hk, hn, hkn⟩
      exact ⟨k * n, ⟨Nat.mul_pos hk hn, hkn⟩, rfl, (Nat.mul_pos hk hn).ne'⟩
    · rintro ⟨m, ⟨hm1, hmN⟩, hkn, -⟩
      have hk : k ≠ 0 := by rintro rfl; simp at hkn; omega
      have hn : n ≠ 0 := by rintro rfl; simp at hkn; omega
      exact ⟨Nat.one_le_iff_ne_zero.mpr hk, Nat.one_le_iff_ne_zero.mpr hn, hkn ▸ hmN⟩
  rw [hset, sum_biUnion]
  · refine sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := by simp only [mem_Icc] at hm; omega
    have hterm : ∀ p ∈ m.divisorsAntidiagonal,
        Λ p.1 / p.1 * (G (p.1 * p.2) / p.2) = G m / m * Λ p.1 := by
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      have h1 : (p.1 : ℝ) ≠ 0 := by
        have : p.1 ≠ 0 := fun h => by simp [h] at hp; exact hm0 hp.1.symm
        exact_mod_cast this
      have h2 : (p.2 : ℝ) ≠ 0 := by
        have : p.2 ≠ 0 := fun h => by simp [h] at hp; exact hm0 hp.1.symm
        exact_mod_cast this
      have hm : (m : ℝ) = p.1 * p.2 := by rw [← hp.1]; push_cast; ring
      rw [hp.1, hm]
      field_simp
    rw [sum_congr rfl hterm, ← mul_sum, Nat.sum_divisorsAntidiagonal (fun a _ => Λ a),
      vonMangoldt_sum]
    ring
  · intro m _ m' _ hmm'
    refine Finset.disjoint_left.mpr fun p hp hp' => hmm' ?_
    rw [Nat.mem_divisorsAntidiagonal] at hp hp'
    exact hp.1.symm.trans hp'.1

/-- **Mertens polarization.** The prime dilation form is the Mertens diagonal minus the jump
energy, exactly, for every packet `F` and horizon `N`. -/
theorem primeDilationForm_eq (N : ℕ) (F : ℕ → ℝ) :
    primeDilationForm N F = mertensDiagonal N F - jumpEnergy N F := by
  have hpol : ∀ p ∈ dilationPairs N, Λ p.1 / p.1 * (2 * F p.2 * F (p.1 * p.2) / p.2) =
      Λ p.1 / p.1 * (F p.2 ^ 2 / p.2) + Λ p.1 / p.1 * (F (p.1 * p.2) ^ 2 / p.2) -
        Λ p.1 / p.1 * ((F (p.1 * p.2) - F p.2) ^ 2 / p.2) := fun p _ => by ring
  rw [primeDilationForm, sum_congr rfl hpol, sum_sub_distrib, sum_add_distrib,
    sum_dilation_source_eq N (fun n => F n ^ 2 / n), sum_dilation_target_eq N (fun m => F m ^ 2),
    jumpEnergy, mertensDiagonal, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  ring

/-! ### The coherent prime sector -/

/-- A prime-incidence packet `F_b(n) = Σ_{p ∈ P} b_p([p ∣ n] − 1/p)`. -/
def incidencePacket (P : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, b p * ((if p ∣ n then 1 else 0) - 1 / p)

/-- For a prime power `k`, a prime divides `kn` iff it is the prime of `k` or divides `n`. -/
theorem prime_dvd_mul_iff_of_isPrimePow {k : ℕ} (hk : IsPrimePow k) {p : ℕ} (hp : p.Prime)
    (n : ℕ) : p ∣ k * n ↔ p = k.minFac ∨ p ∣ n := by
  rw [hp.dvd_mul]
  have hq : k.minFac.Prime := Nat.minFac_prime hk.ne_one
  have hkpow := hk.minFac_pow_factorization_eq
  constructor
  · rintro (h | h)
    · left
      rw [← hkpow] at h
      exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl (Nat.minFac_dvd k)
    · exact Or.inr h

/-- **Every jump of an incidence packet is an event**: for a prime power `k` with prime `q`,
`F_b(kn) − F_b(n) = b_q` if `q ∈ P` and `q ∤ n`, and `0` otherwise. -/
theorem incidencePacket_dilation_jump {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ)
    {k : ℕ} (hk : IsPrimePow k) (n : ℕ) :
    incidencePacket P b (k * n) - incidencePacket P b n =
      if k.minFac ∈ P ∧ ¬k.minFac ∣ n then b k.minFac else 0 := by
  rw [incidencePacket, incidencePacket, ← sum_sub_distrib]
  have hterm : ∀ p ∈ P, b p * ((if p ∣ k * n then 1 else 0) - 1 / p) -
      b p * ((if p ∣ n then 1 else 0) - 1 / p) =
        if p = k.minFac then (if ¬p ∣ n then b p else 0) else 0 := fun p hp => by
    rw [prime_dvd_mul_iff_of_isPrimePow hk (hP p hp)]
    by_cases h1 : p = k.minFac <;> by_cases h2 : p ∣ n <;> simp [h1, h2]
  rw [sum_congr rfl hterm, sum_ite_eq']
  by_cases hm : k.minFac ∈ P <;> by_cases hd : k.minFac ∣ n <;> simp [hm, hd]

/-- **The jump energy of an incidence packet counts nondivisibility events.** -/
theorem jumpEnergy_incidencePacket {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) (N : ℕ) :
    jumpEnergy N (incidencePacket P b) = ∑ p ∈ dilationPairs N,
      Λ p.1 / p.1 * ((if p.1.minFac ∈ P ∧ ¬p.1.minFac ∣ p.2 then b p.1.minFac ^ 2 else 0) / p.2) := by
  refine sum_congr rfl fun p _ => ?_
  by_cases hΛ : Λ p.1 = 0
  · simp [hΛ]
  · rw [incidencePacket_dilation_jump hP b (vonMangoldt_ne_zero_iff.mp hΛ)]
    split_ifs <;> simp

/-- **The prime form on the coherent sector is incidence squares minus an exact Mertens term.** -/
theorem primeDilationForm_incidencePacket {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ)
    (N : ℕ) :
    primeDilationForm N (incidencePacket P b) = mertensDiagonal N (incidencePacket P b) -
      ∑ p ∈ dilationPairs N, Λ p.1 / p.1 *
        ((if p.1.minFac ∈ P ∧ ¬p.1.minFac ∣ p.2 then b p.1.minFac ^ 2 else 0) / p.2) := by
  rw [primeDilationForm_eq, jumpEnergy_incidencePacket hP]

end GaloisForLFunctions.ArithmeticCouplingTheory
