import GaloisForLFunctions.BezoutValuationIncidence.CotangentSawtoothFormOfThePronicGram

/-!
# Vasyunin cotangent sums in the pronic Gram of primes

The sawtooth obeys Hecke's distribution relation

`Σ_{b < q} ((y + b/q)) = ((q y))`,

proved here from the `q`-periodicity of `n ↦ (((n + θ)/q))` and its value on one period. For
prime moduli the coprime residues are `1, …, p - 1`, so the inner sums of the cotangent–sawtooth
form collapse. With the Vasyunin cotangent sum

`V(h, k) = Σ_{a=1}^{k-1} cot(πa/k) ((ha/k))`  (`= Σ {ha/k} cot(πa/k)`, since `Σ cot(πa/k) = 0`),

the mean-centered pronic Gram of two primes is

`G^{mc}(p, q) = (p-1)(q-1)/4 - (π/2) (V(q, p) - V(1, p) + V(p, q) - V(1, q))`.

On the diagonal `V(p, p) = 0`, so `G^{mc}(p, p) = (p - 1)²/4 + π V(1, p)`. The pronic Gram of the
divisor theory is thereby expressed in the cotangent sums of the Nyman–Beurling Gram, and the pair
`(V(q, p), V(p, q))` is the reciprocity pair attached to `p, q`.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The Vasyunin cotangent sum `V(h, k) = Σ_{a=1}^{k-1} cot(πa/k) ((ha/k))`. -/
def vasyuninSum (h k : ℕ) : ℝ :=
  ∑ a ∈ Ico 1 k, Real.cot (Real.pi * ((a : ℝ) / k)) * sawtooth ((h : ℝ) * a / k)

/-! ## §1. The distribution relation -/

theorem sawtooth_add_intCast (x : ℝ) (n : ℤ) : sawtooth (x + n) = sawtooth x := by
  unfold sawtooth
  rw [Int.fract_add_intCast]

/-- On one period the sawtooth sums to the sawtooth of the phase. -/
theorem sum_range_sawtooth_add_div {q : ℕ} (hq : 0 < q) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∑ b ∈ range q, sawtooth (((b : ℝ) + θ) / q) = sawtooth θ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hfract : ∀ b ∈ range q, Int.fract (((b : ℝ) + θ) / q) = ((b : ℝ) + θ) / q := by
    intro b hb
    refine Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one hqR).mpr ?_⟩
    have : (b : ℝ) + 1 ≤ q := by exact_mod_cast mem_range.mp hb
    linarith
  have hid : (∑ b ∈ range q, (b : ℝ)) = (q : ℝ) * ((q : ℝ) - 1) / 2 := by
    have h := Finset.sum_range_id_mul_two q
    have hc : ((∑ i ∈ range q, i : ℕ) : ℝ) * 2 = (q : ℝ) * ((q - 1 : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub (by omega), Nat.cast_one, Nat.cast_sum] at hc
    linarith
  have hlin : ∑ b ∈ range q, (((b : ℝ) + θ) / q - 1 / 2) = θ - 1 / 2 := by
    rw [sum_sub_distrib, ← sum_div, sum_add_distrib, hid, sum_const, card_range, sum_const,
      card_range, nsmul_eq_mul, nsmul_eq_mul]
    field_simp
    ring
  -- each term is the linear sawtooth, corrected at the single zero term when `θ = 0`
  have hterm : ∀ b ∈ range q, sawtooth (((b : ℝ) + θ) / q) =
      (((b : ℝ) + θ) / q - 1 / 2) + (if b = 0 ∧ θ = 0 then 1 / 2 else 0) := by
    intro b hb
    rw [sawtooth, hfract b hb]
    by_cases h : b = 0 ∧ θ = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · have hne : ((b : ℝ) + θ) / q ≠ 0 := by
        intro h0
        have hsum : (b : ℝ) + θ = 0 := by
          rcases div_eq_zero_iff.mp h0 with h0 | h0
          · exact h0
          · exact absurd h0 hqR.ne'
        have hb0 : (b : ℝ) = 0 := by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
        exact h ⟨by exact_mod_cast hb0, by linarith⟩
      rw [if_neg hne, if_neg h]
      ring
  rw [sum_congr rfl hterm, sum_add_distrib, hlin]
  by_cases hθ : θ = 0
  · subst hθ
    have hcorr : ∑ b ∈ range q, (if b = 0 ∧ (0 : ℝ) = 0 then (1 / 2 : ℝ) else 0) = 1 / 2 := by
      simp only [and_true]
      rw [sum_ite_eq' (range q) 0 (fun _ => (1 / 2 : ℝ))]
      simp [hq]
    rw [hcorr]
    simp [sawtooth]
  · have hcorr : ∑ b ∈ range q, (if b = 0 ∧ θ = 0 then (1 / 2 : ℝ) else 0) = 0 :=
      sum_eq_zero fun b _ => by simp [hθ]
    rw [hcorr, sawtooth, Int.fract_eq_self.mpr ⟨hθ0, hθ1⟩, if_neg hθ]
    ring

/-- **Hecke's distribution relation.** `Σ_{b < q} ((y + b/q)) = ((q y))`. -/
theorem sum_range_sawtooth_add {q : ℕ} (hq : 0 < q) (y : ℝ) :
    ∑ b ∈ range q, sawtooth (y + (b : ℝ) / q) = sawtooth ((q : ℝ) * y) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set m := ⌊(q : ℝ) * y⌋
  set θ := Int.fract ((q : ℝ) * y)
  set g : ℤ → ℝ := fun n => sawtooth (((n : ℝ) + θ) / q)
  have hg : ∀ n : ℤ, g (n + q) = g n := fun n => by
    simp only [g]
    rw [show (((n + q : ℤ) : ℝ) + θ) / q = ((n : ℝ) + θ) / q + ((1 : ℤ) : ℝ) by
      push_cast; field_simp; ring, sawtooth_add_intCast]
  -- a full period of a `q`-periodic sequence has the same sum from every start
  have hshift : ∀ n : ℤ, ∑ b ∈ range q, g (n + b) = ∑ b ∈ range q, g b := by
    have hstep : ∀ n : ℤ, ∑ b ∈ range q, g (n + 1 + b) = ∑ b ∈ range q, g (n + b) := by
      intro n
      have h1 := Finset.sum_range_succ (fun b : ℕ => g (n + b)) q
      have h2 := Finset.sum_range_succ' (fun b : ℕ => g (n + b)) q
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at h1 h2
      have hq' := hg n
      have h3 : ∑ b ∈ range q, g (n + 1 + b) = ∑ b ∈ range q, g (n + (b + 1)) :=
        sum_congr rfl fun b _ => by ring_nf
      linarith
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [hstep, ih]
    | pred k ih =>
      have := hstep (-(k : ℤ) - 1)
      rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring] at this
      rw [← this, ih]
  have hy : ∀ b : ℕ, y + (b : ℝ) / q = (((m + b : ℤ) : ℝ) + θ) / q := fun b => by
    have := Int.floor_add_fract ((q : ℝ) * y)
    push_cast
    field_simp
    linarith
  have hsum := hshift m
  simp only [g] at hsum
  rw [sum_congr rfl fun b _ => by rw [hy b], hsum]
  have hbase := sum_range_sawtooth_add_div hq (Int.fract_nonneg ((q : ℝ) * y))
    (Int.fract_lt_one ((q : ℝ) * y))
  simp only [Int.cast_natCast] at hbase ⊢
  rw [hbase]
  conv_rhs => rw [← Int.floor_add_fract ((q : ℝ) * y), add_comm, sawtooth_add_intCast]

/-! ## §2. Primes -/

theorem filter_coprime_range_prime {p : ℕ} (hp : p.Prime) :
    (range p).filter (fun a => a.Coprime p) = Ico 1 p := by
  ext a
  simp only [mem_filter, mem_range, mem_Ico]
  constructor
  · rintro ⟨ha, hcop⟩
    refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, ha⟩
    rw [h0, Nat.coprime_zero_left] at hcop
    exact hp.one_lt.ne' hcop
  · rintro ⟨h1, ha⟩
    exact ⟨ha, (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (Nat.not_dvd_of_pos_of_lt h1 ha)))⟩

/-- Removing the zero residue from Hecke's relation. -/
theorem sum_Ico_sawtooth_add {q : ℕ} (hq : 0 < q) (y : ℝ) :
    ∑ b ∈ Ico 1 q, sawtooth (y + (b : ℝ) / q) = sawtooth ((q : ℝ) * y) - sawtooth y := by
  rw [← sum_range_sawtooth_add hq y, range_eq_Ico, sum_eq_sum_Ico_succ_bot hq]
  simp

/-- **The prime pronic Gram in Vasyunin sums.** -/
theorem pmRamanujanMeanCenteredGram_prime_eq_vasyunin {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    RHTower.pmRamanujanMeanCenteredGram p q =
      ((p : ℝ) - 1) * ((q : ℝ) - 1) / 4 - Real.pi / 2 *
        (vasyuninSum q p - vasyuninSum 1 p + vasyuninSum p q - vasyuninSum 1 q) := by
  have hp0 := hp.pos
  have hq0 := hq.pos
  rw [pmRamanujanMeanCenteredGram_eq_cotangent_sawtooth hp.two_le hq.two_le,
    filter_coprime_range_prime hp, filter_coprime_range_prime hq, Nat.totient_prime hp,
    Nat.totient_prime hq, Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le, Nat.cast_one]
  congr 2
  simp only [add_mul, sum_add_distrib]
  -- first family: sum over `b` at fixed `a`
  have h1 : ∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 q,
      Real.cot (Real.pi * ((a : ℝ) / p)) * sawtooth ((a : ℝ) / p + (b : ℝ) / q) =
      vasyuninSum q p - vasyuninSum 1 p := by
    rw [vasyuninSum, vasyuninSum, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← mul_sum, sum_Ico_sawtooth_add hq0, mul_sub]
    congr 2 <;> ring_nf
  -- second family: sum over `a` at fixed `b`
  have h2 : ∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 q,
      Real.cot (Real.pi * ((b : ℝ) / q)) * sawtooth ((a : ℝ) / p + (b : ℝ) / q) =
      vasyuninSum p q - vasyuninSum 1 q := by
    rw [sum_comm, vasyuninSum, vasyuninSum, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [← mul_sum]
    have h := sum_Ico_sawtooth_add hp0 ((b : ℝ) / q)
    rw [show ∑ a ∈ Ico 1 p, sawtooth ((a : ℝ) / p + (b : ℝ) / q) =
        ∑ a ∈ Ico 1 p, sawtooth ((b : ℝ) / q + (a : ℝ) / p) from
      sum_congr rfl fun a _ => by rw [add_comm], h, mul_sub]
    congr 2 <;> ring_nf
  rw [h1, h2]
  ring

/-- **The diagonal.** `G^{mc}(p, p) = (p - 1)²/4 + π V(1, p)`. -/
theorem pmRamanujanMeanCenteredGram_prime_diag {p : ℕ} (hp : p.Prime) :
    RHTower.pmRamanujanMeanCenteredGram p p =
      ((p : ℝ) - 1) ^ 2 / 4 + Real.pi * vasyuninSum 1 p := by
  have hVpp : vasyuninSum p p = 0 := by
    unfold vasyuninSum
    refine sum_eq_zero fun a _ => ?_
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [show (p : ℝ) * a / p = ((a : ℤ) : ℝ) by field_simp; push_cast; ring,
      show sawtooth ((a : ℤ) : ℝ) = 0 by simp [sawtooth], mul_zero]
  rw [pmRamanujanMeanCenteredGram_prime_eq_vasyunin hp hp, hVpp]
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence
