import GaloisForLFunctions.RHTower.Sieve.LcmQuadraticDiagonalization

/-!
# Selberg diagonalization of the gcd-power quadratic forms

The diagonal main terms of the mollified block twisted moment are the two quadratic forms

`S₁ = Σ_{h,k} a_h a_k (h,k)^{2σ₀}/(hk)^{2σ₀}`,   `S₂ = Σ_{h,k} a_h a_k (h,k)^{2−2σ₀}/(hk)`.

Both have the shape `Σ a_h a_k (h,k)^s/(hk)`.  Writing `(h,k)^s = Σ_{e ∣ (h,k)} g_s(e)` with the
Möbius-inverted kernel `g_s = μ ∗ n^s`, the form diagonalises exactly:

`Σ_{h,k ∈ S} a_h a_k (h,k)^s/(hk) = Σ_e g_s(e) (Σ_{m ∈ S, e ∣ m} a_m/m)²`.

The kernel is multiplicative with `g_s(p^k) = p^{ks} − p^{(k−1)s} ≥ 0`, so every such form is
nonnegative for real coefficients, and an upper bound only needs the multiples-coordinates
`Σ_{e ∣ m} a_m/m`, which for the Levinson mollifier are the corpus's coprime logarithmic Möbius
sums.
-/

open Finset ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-- The power function `n ↦ n^s` as an arithmetic function. -/
def rpowArith (s : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ) ^ s, by simp⟩

theorem rpowArith_apply (s : ℝ) (n : ℕ) : rpowArith s n = if n = 0 then 0 else (n : ℝ) ^ s := rfl

theorem rpowArith_apply_of_ne_zero (s : ℝ) {n : ℕ} (hn : n ≠ 0) : rpowArith s n = (n : ℝ) ^ s := by
  rw [rpowArith_apply, if_neg hn]

theorem isMultiplicative_rpowArith (s : ℝ) : (rpowArith s).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [rpowArith_apply], fun {m n} hm hn _ => ?_⟩
  rw [rpowArith_apply_of_ne_zero s (mul_ne_zero hm hn), rpowArith_apply_of_ne_zero s hm,
    rpowArith_apply_of_ne_zero s hn, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

/-- The gcd-power kernel `g_s = μ ∗ n^s`. -/
def gcdPowKernel (s : ℝ) : ArithmeticFunction ℝ :=
  (moebius : ArithmeticFunction ℤ) * rpowArith s

theorem gcdPowKernel_apply (s : ℝ) (n : ℕ) :
    gcdPowKernel s n = ∑ x ∈ n.divisorsAntidiagonal, ((moebius x.1 : ℤ) : ℝ) * rpowArith s x.2 := by
  rw [gcdPowKernel, mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [intCoe_apply]

theorem isMultiplicative_gcdPowKernel (s : ℝ) : (gcdPowKernel s).IsMultiplicative :=
  (isMultiplicative_moebius.intCast).mul (isMultiplicative_rpowArith s)

/-- **Möbius inversion**: `Σ_{e ∣ n} g_s(e) = n^s`. -/
theorem sum_gcdPowKernel_divisors (s : ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ e ∈ n.divisors, gcdPowKernel s e = (n : ℝ) ^ s := by
  have key := (sum_eq_iff_sum_mul_moebius_eq (f := fun e => gcdPowKernel s e)
    (g := fun n => rpowArith s n)).mpr (fun n hn => by
      rw [gcdPowKernel_apply])
  rw [key n hn, rpowArith_apply_of_ne_zero s hn.ne']

/-- The kernel at a prime power: `g_s(p^k) = p^{ks} − p^{(k−1)s}`. -/
theorem gcdPowKernel_prime_pow (s : ℝ) {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    gcdPowKernel s (p ^ k) = ((p ^ k : ℕ) : ℝ) ^ s - ((p ^ (k - 1) : ℕ) : ℝ) ^ s := by
  rw [gcdPowKernel_apply, Nat.sum_divisorsAntidiagonal (fun i j => ((moebius i : ℤ) : ℝ) * rpowArith s j),
    Nat.sum_divisors_prime_pow hp]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hzero : ∀ i ∈ Finset.range k', ((moebius (p ^ (i + 1 + 1)) : ℤ) : ℝ)
      * rpowArith s (p ^ (k' + 1) / p ^ (i + 1 + 1)) = 0 := by
    intro i _
    rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [Finset.sum_eq_zero hzero]
  simp only [zero_add]
  rw [moebius_apply_prime_pow hp one_ne_zero, if_pos rfl, pow_zero, moebius_apply_one, Nat.div_one,
    Nat.pow_div (by omega) hp.pos, rpowArith_apply_of_ne_zero s (pow_ne_zero _ hp.ne_zero),
    rpowArith_apply_of_ne_zero s (pow_ne_zero _ hp.ne_zero)]
  push_cast
  ring

theorem gcdPowKernel_prime_pow_nonneg {s : ℝ} (hs : 0 ≤ s) {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    0 ≤ gcdPowKernel s (p ^ k) := by
  rw [gcdPowKernel_prime_pow s hp hk, sub_nonneg]
  apply Real.rpow_le_rpow (by positivity) _ hs
  exact_mod_cast Nat.pow_le_pow_right hp.pos (by omega)

/-- **Nonnegativity of the kernel** for `s ≥ 0`. -/
theorem gcdPowKernel_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0 ≤ gcdPowKernel s n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [IsMultiplicative.multiplicative_factorization (gcdPowKernel s) (isMultiplicative_gcdPowKernel s)
    hn.ne']
  apply Finset.prod_nonneg
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  have hk : 1 ≤ n.factorization p := Finsupp.mem_support_iff.mp hp |> Nat.pos_of_ne_zero
  exact gcdPowKernel_prime_pow_nonneg hs hpp hk

/-- `a m a n (m,n)^s/(mn) = Σ_{e ∣ (m,n)} g_s(e) (a m/m)(a n/n)`. -/
theorem gcd_rpow_div_eq_sum_gcdPowKernel (s : ℝ) (a : ℕ → ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    a m * a n * (Nat.gcd m n : ℝ) ^ s / ((m : ℝ) * n)
      = ∑ e ∈ (Nat.gcd m n).divisors, gcdPowKernel s e * ((a m / m) * (a n / n)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hgcd : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left _ hm
  rw [← Finset.sum_mul, sum_gcdPowKernel_divisors s hgcd]
  field_simp

/-- **Twisted Selberg diagonalization.** -/
theorem sum_gcd_rpow_div_eq_kernel_diagonal (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (a : ℕ → ℝ)
    (s : ℝ) :
    ∑ p ∈ S ×ˢ S, a p.1 * a p.2 * (Nat.gcd p.1 p.2 : ℝ) ^ s / ((p.1 : ℝ) * p.2)
      = ∑ e ∈ S.biUnion Nat.divisors, gcdPowKernel s e *
          (∑ m ∈ S.filter (fun m => e ∣ m), a m / (m : ℝ)) ^ 2 := by
  classical
  have hexp : ∀ p ∈ S ×ˢ S, a p.1 * a p.2 * (Nat.gcd p.1 p.2 : ℝ) ^ s / ((p.1 : ℝ) * p.2)
      = ∑ e ∈ (Nat.gcd p.1 p.2).divisors,
          gcdPowKernel s e * ((a p.1 / p.1) * (a p.2 / p.2)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact gcd_rpow_div_eq_sum_gcdPowKernel s a (hS _ hp1) (hS _ hp2)
  rw [Finset.sum_congr rfl hexp]
  have hmem : ∀ (p : ℕ × ℕ) (e : ℕ),
      p ∈ S ×ˢ S ∧ e ∈ (Nat.gcd p.1 p.2).divisors
        ↔ p ∈ (S ×ˢ S).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) ∧ e ∈ S.biUnion Nat.divisors := by
    intro p e
    constructor
    · rintro ⟨hp, he⟩
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have hgcd : e ∣ Nat.gcd p.1 p.2 := Nat.dvd_of_mem_divisors he
      have hd1 : e ∣ p.1 := dvd_trans hgcd (Nat.gcd_dvd_left _ _)
      have hd2 : e ∣ p.2 := dvd_trans hgcd (Nat.gcd_dvd_right _ _)
      refine ⟨Finset.mem_filter.mpr ⟨hp, hd1, hd2⟩, Finset.mem_biUnion.mpr ⟨p.1, hp1, ?_⟩⟩
      exact Nat.mem_divisors.mpr ⟨hd1, (hS _ hp1).ne'⟩
    · rintro ⟨hpf, -⟩
      obtain ⟨hp, hd1, hd2⟩ := Finset.mem_filter.mp hpf
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      refine ⟨hp, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hd1 hd2, ?_⟩⟩
      exact (Nat.gcd_pos_of_pos_left _ (hS _ hp1)).ne'
  rw [Finset.sum_comm' hmem]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hfilter : (S ×ˢ S).filter (fun q => e ∣ q.1 ∧ e ∣ q.2)
      = (S.filter (fun m => e ∣ m)) ×ˢ (S.filter (fun m => e ∣ m)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hfilter, ← Finset.mul_sum, sq, Finset.sum_mul_sum, Finset.sum_product]

/-- **Nonnegativity of the gcd-power forms** for real coefficients and `s ≥ 0`. -/
theorem sum_gcd_rpow_div_nonneg (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (a : ℕ → ℝ) {s : ℝ}
    (hs : 0 ≤ s) :
    0 ≤ ∑ p ∈ S ×ˢ S, a p.1 * a p.2 * (Nat.gcd p.1 p.2 : ℝ) ^ s / ((p.1 : ℝ) * p.2) := by
  rw [sum_gcd_rpow_div_eq_kernel_diagonal S hS a s]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (gcdPowKernel_nonneg hs e) (sq_nonneg _)

end

end RHTower.Sieve
