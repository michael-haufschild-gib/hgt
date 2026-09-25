import GaloisForLFunctions.RHTower.CoprimeClassRamanujan

open Complex Finset
open scoped ArithmeticFunction.Moebius

/-!
# Exact evaluation of coprime-class exponential sums

`Σ_{k<M} e(nk/M) = M [M | n]` (`geom_eq`). For `e | n'` with `(e,N) = 1`, the class `r ≡ b (N)`, `e | r` of
residues mod `n'N` is one class mod `eN`; writing its representative as `e x₁` with `x₁ ≡ b ē (N)` gives
`Σ e(nr/(n'N)) = M ψ((n/M) b ē) [M | n]`, `M = n'/e`, `ψ` the standard additive character of `ℤ/N` (`inner_eq`).
With Möbius inversion of `(r, n') = 1` (and empty classes when `(e,N) > 1`):
`Σ_{r mod n'N, r ≡ b (N), (r,n')=1} e(nr/(n'N)) = Σ_{e | n'} μ(e) [(e,N)=1] [M | n] M ψ((n/M) b ē)`
(`class_sum_eq`). These are the Ramanujan-type sums in the Fourier coefficients of the `Γ(N)` Eisenstein series.
-/

namespace GaloisForLFunctions.RHTower.CoprimeClassExact
open GaloisForLFunctions.RHTower.CoprimeClassCount GaloisForLFunctions.RHTower.CoprimeClassRamanujan

theorem geom_eq {M : ℕ} (hM : 0 < M) (n : ℤ) :
    ∑ k ∈ range M, ph n M k = if (M : ℤ) ∣ n then (M : ℂ) else 0 := by
  set w := cexp (2 * Real.pi * I * n / M)
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hk : ∀ k : ℕ, ph n M k = w ^ k := by
    intro k; unfold ph; rw [← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [hk]
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    have hw : w = 1 := by
      simp only [w]
      rw [show 2 * Real.pi * I * ((M * q : ℤ) : ℂ) / M = (q : ℂ) * (2 * Real.pi * I) by push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I q
    simp [hw]
  · have hne : w ≠ 1 := by
      intro h
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
      apply hd
      refine ⟨k, ?_⟩
      have : (n : ℂ) = k * M := by
        field_simp at hk
        linear_combination hk
      exact_mod_cast (show (n : ℂ) = ((M * k : ℤ) : ℂ) by push_cast; rw [this]; ring)
    rw [geom_sum_eq hne]
    have hwM : w ^ M = 1 := by
      rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      exact ⟨n, by field_simp⟩
    simp [hwM]

/-- **The exact inner sum**: for `e | n'`, `(e,N) = 1`, the class `r ≡ b (N)`, `e | r` contributes
`M · ψ((n/M) b ē)` if `M = n'/e` divides `n`, and `0` otherwise (`ψ` the standard additive character of `ℤ/N`). -/
theorem inner_eq {n' N e : ℕ} [NeZero N] (hn' : 0 < n') (he : e ∣ n') (hco : e.Coprime N) (b : ℕ) (n : ℤ) :
    ∑ r ∈ (range (n' * N)).filter (fun r => r ≡ b [MOD N] ∧ e ∣ r), ph n (n' * N) r =
      if ((n' / e : ℕ) : ℤ) ∣ n then ((n' / e : ℕ) : ℂ) *
        ZMod.stdAddChar (((n / (n' / e : ℕ) : ℤ) : ZMod N) * (b : ZMod N) * (e : ZMod N)⁻¹) else 0 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he hn'
  obtain ⟨x, hx0, hxb⟩ := Nat.chineseRemainder hco 0 b
  set L := e * N
  have hL : 0 < L := Nat.mul_pos he0 hN
  have hxL : x % L ≡ x [MOD e * N] := Nat.mod_modEq x L
  have hxe : x % L ≡ x [MOD e] := Nat.ModEq.of_mul_right N hxL
  have hxN : x % L ≡ x [MOD N] := Nat.ModEq.of_mul_left e hxL
  have hiff : ∀ r, (r ≡ b [MOD N] ∧ e ∣ r) ↔ r ≡ x % L [MOD L] := by
    intro r
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hco, ← Nat.modEq_zero_iff_dvd]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(h2.trans hx0.symm).trans hxe.symm, (h1.trans hxb.symm).trans hxN.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨(h2.trans hxN).trans hxb, (h1.trans hxe).trans hx0⟩
  set M := n' / e
  have hn'M : n' = e * M := (Nat.mul_div_cancel' he).symm
  have hM : 0 < M := Nat.div_pos (Nat.le_of_dvd hn' he) he0
  have hK : n' * N = M * L := by rw [hn'M]; ring
  simp_rw [hiff]
  rw [hK, sum_filter_reindex hL (Nat.mod_lt x hL)]
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hsplit : ∀ k, ph n (M * L) (x % L + L * k) = ph n (M * L) (x % L) * ph n M k := by
    intro k
    unfold ph
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  simp_rw [hsplit]
  rw [← Finset.mul_sum, geom_eq hM n]
  split_ifs with hd
  · obtain ⟨q, hq⟩ := hd
    have hqn : n / (M : ℤ) = q := by rw [hq]; exact Int.mul_ediv_cancel_left q (by exact_mod_cast hM.ne')
    rw [hqn]
    -- `x % L = e * x₁` with `e x₁ ≡ b (N)`
    have hex : e ∣ x % L := (Nat.modEq_zero_iff_dvd.mp (hxe.trans hx0))
    obtain ⟨x1, hx1⟩ := hex
    have hx1b : ((e : ZMod N) * (x1 : ZMod N)) = (b : ZMod N) := by
      have h := (ZMod.natCast_eq_natCast_iff _ _ N).mpr (hxN.trans hxb)
      rw [hx1] at h; push_cast at h; exact h
    have hu : IsUnit (e : ZMod N) := (ZMod.isUnit_iff_coprime e N).mpr hco
    have hx1' : (x1 : ZMod N) = (b : ZMod N) * (e : ZMod N)⁻¹ := by
      rw [← hx1b, mul_comm (e : ZMod N), mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one]
    have hph : ph n (M * L) (x % L) = ZMod.stdAddChar (((q * x1 : ℤ)) : ZMod N) := by
      rw [ZMod.stdAddChar_apply, ZMod.toCircle_intCast]
      unfold ph
      congr 1
      rw [hq, hx1]
      have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
      have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      simp only [L]
      push_cast
      field_simp
    rw [hph, mul_comm]
    congr 2
    push_cast
    rw [hx1', mul_assoc]
  · rw [mul_zero]

/-- The `e`-term of the exact class sum. -/
noncomputable def classTerm (N : ℕ) [NeZero N] (n' : ℕ) (b : ℕ) (n : ℤ) (e : ℕ) : ℂ :=
  if e.Coprime N ∧ ((n' / e : ℕ) : ℤ) ∣ n then
    ((n' / e : ℕ) : ℂ) * ZMod.stdAddChar (((n / (n' / e : ℕ) : ℤ) : ZMod N) * (b : ZMod N) * (e : ZMod N)⁻¹)
  else 0

/-- **Exact evaluation of a coprime-class exponential sum**:
`Σ_{r mod n'N, r ≡ b (N), (r,n')=1} e(nr/(n'N)) = Σ_{e | n', (e,N)=1, (n'/e) | n} μ(e) (n'/e) ψ((n/(n'/e)) b ē)`. -/
theorem class_sum_eq {n' N : ℕ} [NeZero N] (hn' : 0 < n') {b : ℕ} (hb : (n'.gcd N).Coprime b) (n : ℤ) :
    ∑ r ∈ (range (n' * N)).filter (fun r => r ≡ b [MOD N] ∧ n'.Coprime r), ph n (n' * N) r =
      ∑ e ∈ n'.divisors, (μ e : ℂ) * classTerm N n' b n e := by
  classical
  rw [Finset.sum_filter]
  have h1 : ∀ r ∈ range (n' * N), (if r ≡ b [MOD N] ∧ n'.Coprime r then ph n (n' * N) r else 0) =
      ∑ e ∈ n'.divisors, if r ≡ b [MOD N] ∧ e ∣ r then (μ e : ℂ) * ph n (n' * N) r else 0 := by
    intro r _
    by_cases hr : r ≡ b [MOD N]
    · simp only [hr, true_and]
      have hc := coprime_indicator hn' r
      have hc' : (if n'.Coprime r then (1 : ℂ) else 0) = ∑ e ∈ n'.divisors, if e ∣ r then (μ e : ℂ) else 0 := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hc
        push_cast at this
        exact this
      calc (if n'.Coprime r then ph n (n' * N) r else 0)
          = (if n'.Coprime r then (1 : ℂ) else 0) * ph n (n' * N) r := by split_ifs <;> simp
        _ = _ := by rw [hc', Finset.sum_mul]; apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp
    · simp [hr]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hen : e ∣ n' := Nat.dvd_of_mem_divisors he
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  unfold classTerm
  by_cases hco : e.Coprime N
  · rw [inner_eq hn' hen hco b n]
    by_cases hd : ((n' / e : ℕ) : ℤ) ∣ n
    · rw [if_pos hd, if_pos ⟨hco, hd⟩]
    · rw [if_neg hd, if_neg (fun h => hd h.2)]
  · have h0 : (range (n' * N)).filter (fun r => r ≡ b [MOD N] ∧ e ∣ r) = ∅ :=
      Finset.card_eq_zero.mp (card_crt_zero hen hco hb)
    rw [h0, Finset.sum_empty, if_neg (fun h => hco h.1)]

end GaloisForLFunctions.RHTower.CoprimeClassExact
