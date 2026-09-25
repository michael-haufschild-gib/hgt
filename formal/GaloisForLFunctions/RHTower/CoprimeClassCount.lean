import GaloisForLFunctions.RHTower.TotientMulMoebius

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-!
# Residues in a class mod `N` that are coprime to `n`

If `gcd(gcd(n,N), b) = 1` then `#{r mod nN : r ≡ b (N), (r,n) = 1} · φ(N) = φ(nN)` (`card_coprime_class_mul_totient`).
Writing `[(n,r)=1] = Σ_{e | n, e | r} μ(e)` (`coprime_indicator`) and swapping sums, the class `r ≡ b (N), e | r` has
`n/e` members when `(e,N) = 1` (Chinese remainder theorem, `card_crt`) and none otherwise (a common prime of `e` and
`N` would divide `b`, `card_crt_zero`); the result is `H_N(n) = Σ_{e | n, (e,N)=1} μ(e) n/e = φ(nN)/φ(N)`. This counts
the bottom rows `(c, d)`, `d mod |c|N`, of `Γ(N)σ` for every cusp `σ∞`.
-/

namespace GaloisForLFunctions.RHTower.CoprimeClassCount
open GaloisForLFunctions.RHTower.TotientMulMoebius

theorem coprime_indicator {n : ℕ} (hn : 0 < n) (r : ℕ) :
    (if n.Coprime r then (1 : ℤ) else 0) = ∑ e ∈ n.divisors, if e ∣ r then μ e else 0 := by
  rw [← Finset.sum_filter]
  have hg : n.divisors.filter (· ∣ r) = (n.gcd r).divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left r hn).ne'⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h1, hn.ne'⟩, h2⟩
  rw [hg, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]

theorem card_crt {n N e : ℕ} (hn : 0 < n) (hN : 0 < N) (he : e ∣ n) (hco : e.Coprime N) (b : ℕ) :
    ((Finset.range (n * N)).filter (fun r => r ≡ b [MOD N] ∧ e ∣ r)).card = n / e := by
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he hn
  obtain ⟨x, hx0, hxb⟩ := Nat.chineseRemainder hco 0 b
  have hiff : ∀ r, (r ≡ b [MOD N] ∧ e ∣ r) ↔ r ≡ x [MOD e * N] := by
    intro r
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hco, ← Nat.modEq_zero_iff_dvd]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2.trans hx0.symm, h1.trans hxb.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2.trans hxb, h1.trans hx0⟩
  simp_rw [hiff]
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (Nat.mul_pos he0 hN)]
  obtain ⟨k, rfl⟩ := he
  have : e * k * N = (e * N) * k := by ring
  rw [this, Nat.mul_mod_right, if_neg (Nat.not_lt_zero _), add_zero, Nat.mul_div_cancel_left _ (Nat.mul_pos he0 hN),
    Nat.mul_div_cancel_left _ he0]

theorem card_crt_zero {n N e : ℕ} (he : e ∣ n) (hco : ¬ e.Coprime N) {b : ℕ} (hb : (n.gcd N).Coprime b) :
    ((Finset.range (n * N)).filter (fun r => r ≡ b [MOD N] ∧ e ∣ r)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro r - ⟨h1, h2⟩
  obtain ⟨p, hp, hpe, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hco
  have hpb : p ∣ b := (h1.dvd_iff hpN).mp (hpe.trans h2)
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp
    (Nat.Coprime.coprime_dvd_left (Nat.dvd_gcd (hpe.trans he) hpN) hb) hpb

/-- **Residues in a class mod `N` coprime to `n`**: if `(gcd(n,N), b) = 1` then
`#{r mod nN : r ≡ b (N), (r,n) = 1} · φ(N) = φ(nN)`. -/
theorem card_coprime_class_mul_totient {n N : ℕ} (hn : 0 < n) (hN : 0 < N) {b : ℕ} (hb : (n.gcd N).Coprime b) :
    ((Finset.range (n * N)).filter (fun r => r ≡ b [MOD N] ∧ n.Coprime r)).card * N.totient = (n * N).totient := by
  have key : (((Finset.range (n * N)).filter (fun r => r ≡ b [MOD N] ∧ n.Coprime r)).card : ℤ) = H N n := by
    rw [Finset.natCast_card_filter]
    have h1 : ∀ r ∈ Finset.range (n * N), (if r ≡ b [MOD N] ∧ n.Coprime r then (1 : ℤ) else 0) =
        ∑ e ∈ n.divisors, if r ≡ b [MOD N] ∧ e ∣ r then μ e else 0 := by
      intro r _
      by_cases hr : r ≡ b [MOD N]
      · simp only [hr, true_and]
        rw [coprime_indicator hn]
      · simp [hr]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    unfold H
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    have hen : e ∣ n := Nat.dvd_of_mem_divisors he
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hco : e.Coprime N
    · rw [if_pos hco, card_crt hn hN hen hco b, mul_comm]
    · rw [if_neg hco, card_crt_zero hen hco hb]; simp
  have := totient_mul_eq N hN n
  rw [mul_comm N n] at this
  have h2 : ((((Finset.range (n * N)).filter (fun r => r ≡ b [MOD N] ∧ n.Coprime r)).card * N.totient : ℕ) : ℤ) =
      ((n * N).totient : ℤ) := by
    push_cast; rw [key, this]; ring
  exact_mod_cast h2

end GaloisForLFunctions.RHTower.CoprimeClassCount
