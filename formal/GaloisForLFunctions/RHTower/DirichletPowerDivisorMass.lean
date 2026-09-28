import GaloisForLFunctions.RHTower.BohrMoments
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment

/-!
# The mass of a convolution power of a divisor-bounded Dirichlet polynomial

Let `a` be supported on `s ⊆ [K, 2K)` with `|a k| ≤ k^{-σ} d(k)`.  The `ℓ`-th convolution power
`powConv a s ℓ` (the coefficients of `(Σ_{k ∈ s} a_k k^{-it})^ℓ`) satisfies the pointwise bound
`|powConv a s ℓ n| ≤ n^{-σ} d(n)^{2ℓ}`.  The induction step pays one factor `d(n)` for the number of
factorizations `n = pq` and one for `d(q) ≤ d(n)`.  Its support lies in `[K^ℓ, (2K-1)^ℓ]`.

Consequently, for `σ ≥ 0`, the mass `Σ_n (powConv a s ℓ n)²` is at most
`(K^ℓ)^{-2σ} (2K)^ℓ (1 + log (2K)^ℓ)^{2^{4ℓ}-1}`.  This is the fixed-moment estimate
`sum_card_divisors_pow_le_polylog` with exponent `4ℓ`, so the loss over the diagonal
`(K^ℓ)^{1-2σ}` is a fixed power of the logarithm.
-/

namespace RHTower

noncomputable section

open Finset

/-- **Pointwise divisor bound for convolution powers.** -/
theorem abs_powConv_le {a : ℕ → ℝ} {s : Finset ℕ} {σ : ℝ} (hs : ∀ k ∈ s, 1 ≤ k)
    (ha : ∀ k ∈ s, |a k| ≤ (k : ℝ) ^ (-σ) * k.divisors.card) (ℓ : ℕ) :
    ∀ n, 1 ≤ n → |powConv a s ℓ n| ≤ (n : ℝ) ^ (-σ) * (n.divisors.card : ℝ) ^ (2 * ℓ) := by
  induction ℓ with
  | zero =>
    intro n hn
    simp only [powConv, mul_zero, pow_zero, mul_one]
    split_ifs with h
    · subst h
      simp
    · simp only [abs_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  | succ ℓ ih =>
    intro n hn
    rw [powConv, dpolyConv]
    have hn0 : n ≠ 0 := by omega
    set F := (powSupport s ℓ ×ˢ s).filter (fun p => p.1 * p.2 = n) with hF
    have hcard : (F.card : ℝ) ≤ n.divisors.card := by
      have h : F.card ≤ n.divisors.card := by
        refine card_le_card_of_injOn (fun p => p.1) ?_ ?_
        · intro p hp
          rw [hF, coe_filter] at hp
          rw [mem_coe, Nat.mem_divisors]
          exact ⟨⟨p.2, hp.2.symm⟩, hn0⟩
        · intro p hp p' hp' hpp
          rw [hF, coe_filter] at hp hp'
          simp only [Set.mem_setOf_eq] at hp hp' hpp
          have hp10 : p.1 ≠ 0 := by
            intro h0
            have h2 := hp.2
            rw [h0, zero_mul] at h2
            exact hn0 h2.symm
          have h2 : p.2 = p'.2 := by
            have e : p.1 * p.2 = p.1 * p'.2 := by rw [hp.2, hpp, hp'.2]
            exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp10) e
          exact Prod.ext hpp h2
      exact_mod_cast h
    have hterm : ∀ p ∈ F, |powConv a s ℓ p.1 * a p.2|
        ≤ (n : ℝ) ^ (-σ) * (n.divisors.card : ℝ) ^ (2 * ℓ + 1) := by
      intro p hp
      rw [hF, mem_filter, mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hpn⟩ := hp
      have hp1' := one_le_of_mem_powSupport hs ℓ p.1 hp1
      have hpd : p.1 ∣ n := ⟨p.2, hpn.symm⟩
      have hqd : p.2 ∣ n := ⟨p.1, by rw [← hpn]; ring⟩
      have hdp : (p.1.divisors.card : ℝ) ≤ n.divisors.card := by
        exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hn0 hpd)
      have hdq : (p.2.divisors.card : ℝ) ≤ n.divisors.card := by
        exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hn0 hqd)
      rw [abs_mul]
      have h1 := ih p.1 hp1'
      have h2 := ha p.2 hp2
      have hmul : ((p.1 : ℝ) ^ (-σ)) * ((p.2 : ℝ) ^ (-σ)) = (n : ℝ) ^ (-σ) := by
        rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
        congr 1
        exact_mod_cast hpn
      calc |powConv a s ℓ p.1| * |a p.2|
          ≤ ((p.1 : ℝ) ^ (-σ) * (p.1.divisors.card : ℝ) ^ (2 * ℓ))
              * ((p.2 : ℝ) ^ (-σ) * p.2.divisors.card) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (n : ℝ) ^ (-σ) * ((p.1.divisors.card : ℝ) ^ (2 * ℓ) * p.2.divisors.card) := by
            rw [← hmul]
            ring
        _ ≤ (n : ℝ) ^ (-σ) * ((n.divisors.card : ℝ) ^ (2 * ℓ) * n.divisors.card) := by
            gcongr
        _ = (n : ℝ) ^ (-σ) * (n.divisors.card : ℝ) ^ (2 * ℓ + 1) := by ring
    calc |∑ p ∈ F, powConv a s ℓ p.1 * a p.2|
        ≤ ∑ p ∈ F, |powConv a s ℓ p.1 * a p.2| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ F, (n : ℝ) ^ (-σ) * (n.divisors.card : ℝ) ^ (2 * ℓ + 1) := sum_le_sum hterm
      _ = F.card * ((n : ℝ) ^ (-σ) * (n.divisors.card : ℝ) ^ (2 * ℓ + 1)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ n.divisors.card * ((n : ℝ) ^ (-σ) * (n.divisors.card : ℝ) ^ (2 * ℓ + 1)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (n : ℝ) ^ (-σ) * (n.divisors.card : ℝ) ^ (2 * (ℓ + 1)) := by ring

/-- **The support of a convolution power.**  If `s ⊆ [K, 2K-1]`, then
`powSupport s ℓ ⊆ [K^ℓ, (2K-1)^ℓ]`. -/
theorem mem_powSupport_bounds {s : Finset ℕ} {K : ℕ} (hs : ∀ k ∈ s, K ≤ k ∧ k ≤ 2 * K - 1)
    (ℓ : ℕ) : ∀ n ∈ powSupport s ℓ, K ^ ℓ ≤ n ∧ n ≤ (2 * K - 1) ^ ℓ := by
  induction ℓ with
  | zero =>
    intro n hn
    rw [powSupport, mem_singleton] at hn
    simp [hn]
  | succ ℓ ih =>
    intro n hn
    rw [powSupport, prodSupport, mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    rw [mem_product] at hp
    obtain ⟨h1, h2⟩ := ih p.1 hp.1
    obtain ⟨h3, h4⟩ := hs p.2 hp.2
    rw [pow_succ, pow_succ]
    exact ⟨Nat.mul_le_mul h1 h3, Nat.mul_le_mul h2 h4⟩

/-- **The mass of a convolution power.**  For `σ ≥ 0`, `1 ≤ K`, `ℓ ≥ 1`, `s ⊆ [K, 2K-1]` and
`|a k| ≤ k^{-σ} d(k)` on `s`:
`Σ_{n ∈ powSupport s ℓ} (powConv a s ℓ n)² ≤ (K^ℓ)^{-2σ} (2K)^ℓ (1 + log (2K)^ℓ)^{2^{4ℓ}-1}`. -/
theorem sum_sq_powConv_le {a : ℕ → ℝ} {s : Finset ℕ} {σ : ℝ} {K ℓ : ℕ} (hσ : 0 ≤ σ)
    (hK : 1 ≤ K) (hs : ∀ k ∈ s, K ≤ k ∧ k ≤ 2 * K - 1)
    (ha : ∀ k ∈ s, |a k| ≤ (k : ℝ) ^ (-σ) * k.divisors.card) :
    ∑ n ∈ powSupport s ℓ, (powConv a s ℓ n) ^ 2
      ≤ ((K : ℝ) ^ ℓ) ^ (-2 * σ) * (((2 * K) ^ ℓ : ℕ) : ℝ)
          * (1 + Real.log (((2 * K) ^ ℓ : ℕ) : ℝ)) ^ (2 ^ (4 * ℓ) - 1) := by
  have hs1 : ∀ k ∈ s, 1 ≤ k := fun k hk => le_trans hK (hs k hk).1
  have hbound := mem_powSupport_bounds hs ℓ
  have hKl : 1 ≤ K ^ ℓ := Nat.one_le_pow _ _ (by omega)
  have hL : 1 ≤ (2 * K) ^ ℓ := Nat.one_le_pow _ _ (by omega)
  have hsub : powSupport s ℓ ⊆ Icc 1 ((2 * K) ^ ℓ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := hbound n hn
    rw [mem_Icc]
    exact ⟨le_trans hKl h1, le_trans h2 (Nat.pow_le_pow_left (by omega) ℓ)⟩
  have hterm : ∀ n ∈ powSupport s ℓ, (powConv a s ℓ n) ^ 2
      ≤ ((K : ℝ) ^ ℓ) ^ (-2 * σ) * ((n.divisors.card : ℝ) ^ (4 * ℓ)) := by
    intro n hn
    obtain ⟨h1, _⟩ := hbound n hn
    have hn1 : 1 ≤ n := le_trans hKl h1
    have habs := abs_powConv_le hs1 ha ℓ n hn1
    have hsq : (powConv a s ℓ n) ^ 2 ≤ ((n : ℝ) ^ (-σ) * (n.divisors.card : ℝ) ^ (2 * ℓ)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    refine le_trans hsq ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hpow : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-2 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      push_cast
      ring
    have hmono : (n : ℝ) ^ (-2 * σ) ≤ ((K : ℝ) ^ ℓ) ^ (-2 * σ) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      exact_mod_cast h1
    rw [mul_pow, hpow, ← pow_mul]
    rw [show 2 * ℓ * 2 = 4 * ℓ by ring]
    exact mul_le_mul_of_nonneg_right hmono (by positivity)
  calc ∑ n ∈ powSupport s ℓ, (powConv a s ℓ n) ^ 2
      ≤ ∑ n ∈ powSupport s ℓ, ((K : ℝ) ^ ℓ) ^ (-2 * σ) * ((n.divisors.card : ℝ) ^ (4 * ℓ)) :=
        sum_le_sum hterm
    _ ≤ ∑ n ∈ Icc 1 ((2 * K) ^ ℓ), ((K : ℝ) ^ ℓ) ^ (-2 * σ) * ((n.divisors.card : ℝ) ^ (4 * ℓ)) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ((K : ℝ) ^ ℓ) ^ (-2 * σ) * ∑ n ∈ Icc 1 ((2 * K) ^ ℓ), (n.divisors.card : ℝ) ^ (4 * ℓ) := by
        rw [mul_sum]
    _ ≤ ((K : ℝ) ^ ℓ) ^ (-2 * σ) * ((((2 * K) ^ ℓ : ℕ) : ℝ)
          * (1 + Real.log (((2 * K) ^ ℓ : ℕ) : ℝ)) ^ (2 ^ (4 * ℓ) - 1)) :=
        mul_le_mul_of_nonneg_left (Sieve.sum_card_divisors_pow_le_polylog (4 * ℓ) _ hL) (by positivity)
    _ = _ := by ring

end

end RHTower
