import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Int

/-!
# Products of prime-power sequences

For coefficients `f, g` supported on prime powers, the Dirichlet convolution `(f ⍟ g)(m)` only
sees factorizations `m = uv` into prime powers. Two facts govern its size:

* **Pair structure** (`eq_or_swap_of_mul_eq`): if `u, v` are prime powers whose product is not a
  prime power, the only factorizations `uv = u'v'` into prime powers are `(u, v)` and `(v, u)`.
* **Same-prime pairs are sparse**: `L = Λ ⍟ Λ` vanishes on primes and is at most `log² m`, so
  the constants `Σ_m Λ(m) L(m)/m` and `Σ_{m prime power} L(m)²/m` are finite
  (`summable_vonMangoldt_mul_LL_div`, `summable_primePow_LL_sq_div`): they run over `p^k`, `k ≥ 2`.

Sums of `(f ⍟ g)·h` regroup as sums over pairs: `Σ_m (f ⍟ g)(m) h(m) = Σ_{u,v} f(u) g(v) h(uv)`
(`hasSum_convolution_mul`).
-/

open ArithmeticFunction Filter
open scoped LSeries.notation

noncomputable section

namespace RHTower.PrimePowerPairs

/-! ### Regrouping -/

/-- `Σ_m (f ⍟ g)(m) h(m) = Σ_{u,v} f(u) g(v) h(uv)`. -/
theorem hasSum_convolution_mul {f g h : ℕ → ℝ} (hf0 : f 0 = 0) (hg0 : g 0 = 0) {S : ℝ}
    (hS : HasSum (fun p : ℕ × ℕ => f p.1 * g p.2 * h (p.1 * p.2)) S) :
    HasSum (fun m => (f ⍟ g) m * h m) S := by
  have hfib := hS.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  have hpt : ∀ m : ℕ, (f ⍟ g) m * h m =
      ∑' b : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {m}), f b.1.1 * g b.1.2 * h (b.1.1 * b.1.2) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · rw [LSeries.convolution_map_zero, zero_mul]
      symm
      refine (tsum_congr fun b => ?_).trans tsum_zero
      have hb : b.1.1 * b.1.2 = 0 := b.2
      rcases Nat.mul_eq_zero.mp hb with h0 | h0 <;> simp [h0, hf0, hg0]
    · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {m} = (m.divisorsAntidiagonal : Set (ℕ × ℕ)) by
        ext; simp [hm], Finset.tsum_subtype' m.divisorsAntidiagonal
        (fun p : ℕ × ℕ => f p.1 * g p.2 * h (p.1 * p.2)),
        congrFun (LSeries.convolution_def f g) m, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
  rw [funext hpt]
  exact hfib

/-! ### The pair structure -/

theorem coprime_of_not_isPrimePow_mul {u v : ℕ} (hu : IsPrimePow u) (hv : IsPrimePow v)
    (h : ¬IsPrimePow (u * v)) : u.Coprime v := by
  obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff u).mp hu
  obtain ⟨q, b, hq, hb, rfl⟩ := (isPrimePow_nat_iff v).mp hv
  by_cases hpq : p = q
  · subst hpq
    exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, a + b, hp, by omega, by rw [pow_add]⟩) h
  · exact Nat.Coprime.pow a b ((Nat.coprime_primes hp hq).mpr hpq)

/-- **Pair structure.** If `u, v` are prime powers and `uv` is not, every factorization
`uv = u'v'` into prime powers is `(u, v)` or `(v, u)`. -/
theorem eq_or_swap_of_mul_eq {u v u' v' : ℕ} (hu : IsPrimePow u) (hv : IsPrimePow v)
    (h : ¬IsPrimePow (u * v)) (hu' : IsPrimePow u') (hv' : IsPrimePow v')
    (he : u' * v' = u * v) : (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by
  have hc := coprime_of_not_isPrimePow_mul hu hv h
  have hu1 := hu.one_lt
  have hv1 := hv.one_lt
  have hdu' : u' ∣ u * v := ⟨v', he.symm⟩
  have hdv' : v' ∣ u * v := ⟨u', by rw [← he, mul_comm]⟩
  -- a prime power dividing `uv` divides `u` or `v`
  have hA := (Nat.Coprime.isPrimePow_dvd_mul hc hu').mp hdu'
  have hB := (Nat.Coprime.isPrimePow_dvd_mul hc hv').mp hdv'
  -- both factors cannot divide the same side
  have hsame : ∀ w : ℕ, 1 < w → ∀ z : ℕ, 1 < z → z.Coprime w → u' ∣ z → v' ∣ z →
      u' * v' = z * w → False := by
    intro w hw z hz hzw h1 h2 hzw'
    have hdiv : z * w ∣ z * z := by
      rw [← hzw']; exact mul_dvd_mul h1 h2
    have hwz : w ∣ z := (Nat.mul_dvd_mul_iff_left (by omega)).mp hdiv
    have := Nat.Coprime.eq_one_of_dvd hzw.symm hwz
    omega
  -- equal products with divisibility force equality
  have heq : ∀ a b a' b' : ℕ, 0 < a → 0 < b → a' ∣ a → b' ∣ b → a' * b' = a * b →
      a' = a ∧ b' = b := by
    intro a b a' b' ha hb ⟨k, hk⟩ ⟨l, hl⟩ hab
    have hkl : k * l = 1 := by
      have : a' * b' * (k * l) = a' * b' * 1 := by rw [mul_one]; nth_rw 2 [hab]; rw [hk, hl]; ring
      have ha' : 0 < a' * b' := by
        rw [hab]; positivity
      exact Nat.eq_of_mul_eq_mul_left ha' this
    have hk1 : k = 1 := Nat.eq_one_of_mul_eq_one_right hkl
    have hl1 : l = 1 := Nat.eq_one_of_mul_eq_one_left hkl
    exact ⟨by rw [hk, hk1, mul_one], by rw [hl, hl1, mul_one]⟩
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact (hsame v hv1 u hu1 hc hA hB he).elim
  · exact Or.inl (heq u v u' v' (by omega) (by omega) hA hB he)
  · exact Or.inr (heq v u u' v' (by omega) (by omega) hA hB (by rw [he, mul_comm]))
  · exact (hsame u hu1 v hv1 hc.symm hA hB (by rw [he, mul_comm])).elim

/-! ### `L = Λ ⍟ Λ` -/

/-- `L(m) = Σ_{uv = m} Λ(u) Λ(v)`. -/
def LL : ℕ → ℝ := (fun n => Λ n) ⍟ (fun n => Λ n)

theorem LL_apply (m : ℕ) : LL m = ∑ p ∈ m.divisorsAntidiagonal, Λ p.1 * Λ p.2 :=
  congrFun (LSeries.convolution_def _ _) m

theorem LL_nonneg (m : ℕ) : 0 ≤ LL m := by
  rw [LL_apply]
  exact Finset.sum_nonneg fun p _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

/-- `L(m) ≤ log² m`: `Σ_{uv=m} Λ(u)Λ(v) ≤ log m · Σ_{u | m} Λ(u)`. -/
theorem LL_le_log_sq (m : ℕ) : LL m ≤ Real.log m ^ 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [LL, LSeries.convolution_map_zero]
  rw [LL_apply]
  have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  calc ∑ p ∈ m.divisorsAntidiagonal, Λ p.1 * Λ p.2
      ≤ ∑ p ∈ m.divisorsAntidiagonal, Λ p.1 * Real.log m := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp' := Nat.mem_divisorsAntidiagonal.mp hp
        refine mul_le_mul_of_nonneg_left (vonMangoldt_le_log.trans ?_) vonMangoldt_nonneg
        have h2 : p.2 ∣ m := ⟨p.1, by rw [← hp'.1, mul_comm]⟩
        have hp2 : 0 < p.2 := Nat.pos_of_ne_zero (right_ne_zero_of_mul (hp'.1 ▸ hp'.2))
        exact Real.log_le_log (by exact_mod_cast hp2)
          (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h2)
    _ = (∑ i ∈ m.divisors, Λ i) * Real.log m := by
        rw [← Finset.sum_mul, Nat.sum_divisorsAntidiagonal (fun a _ => Λ a)]
    _ = Real.log m ^ 2 := by rw [vonMangoldt_sum, sq]

/-- `L(p) = 0` for a prime `p`. -/
theorem LL_prime {p : ℕ} (hp : p.Prime) : LL p = 0 := by
  rw [LL_apply]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hq' := (Nat.mem_divisorsAntidiagonal.mp hq).1
  rw [← hq'] at hp
  rcases Nat.prime_mul_iff.mp hp with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]

/-! ### The same-prime constants -/

/-- `Σ_n log^k n / n² < ∞`: `log n ≤ n^ε/ε` with `kε < 1/2`. -/
theorem summable_log_pow_div_sq (k : ℕ) : Summable fun n : ℕ => Real.log n ^ k / (n : ℝ) ^ 2 := by
  set ε : ℝ := 1 / (2 * (k + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hS : Summable fun n : ℕ => (ε⁻¹) ^ k * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left _
  refine hS.of_nonneg_of_le (fun n => div_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)
    (by positivity)) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog := Real.log_le_rpow_div hn0.le hε0
  have hlog0 := Real.log_natCast_nonneg n
  have h1 : Real.log n ^ k ≤ ((n : ℝ) ^ ε / ε) ^ k := pow_le_pow_left₀ hlog0 hlog k
  have h2 : ((n : ℝ) ^ ε / ε) ^ k = (ε⁻¹) ^ k * (n : ℝ) ^ (ε * k) := by
    rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ ε), ← Real.rpow_mul hn0.le, div_eq_mul_inv,
      mul_comm, inv_pow]
  have h3 : (n : ℝ) ^ (ε * k) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le hn' ?_
    rw [hε]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  calc Real.log n ^ k / (n : ℝ) ^ 2 ≤ (ε⁻¹) ^ k * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 := by
        gcongr
        exact h1.trans (h2.le.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
    _ = (ε⁻¹) ^ k * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        rw [mul_div_assoc]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_sub hn0, ← Real.rpow_neg hn0.le]
        norm_num

/-- The majorant over `(p, j)`: `(log^k p / p²) · ((j+2)⁴ 2^{−j})`. -/
theorem summable_primes_majorant (k : ℕ) :
    Summable fun x : Nat.Primes × ℕ =>
      Real.log (x.1 : ℕ) ^ k / ((x.1 : ℕ) : ℝ) ^ 2 * (((x.2 : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ x.2) := by
  have hP : Summable fun p : Nat.Primes => Real.log (p : ℕ) ^ k / ((p : ℕ) : ℝ) ^ 2 :=
    (summable_log_pow_div_sq k).comp_injective Subtype.val_injective
  have hG : Summable fun j : ℕ => ((j : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ j := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4
      (r := 1 / 2) (by norm_num)
    have h2 := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    refine ((h1.mul_left 8).add (h2.mul_left 128)).of_nonneg_of_le (fun j => by positivity)
      fun j => ?_
    have hj : ((j : ℝ) + 2) ^ 4 ≤ 8 * (j : ℝ) ^ 4 + 128 := by
      have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith [sq_nonneg ((j : ℝ) - 2), sq_nonneg ((j : ℝ) ^ 2 - 4), sq_nonneg (j : ℝ),
        mul_nonneg h0 (sq_nonneg ((j : ℝ) - 2))]
    have hr : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ j := by positivity
    calc ((j : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ j ≤ (8 * (j : ℝ) ^ 4 + 128) * (1 / 2 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hj hr
      _ = 8 * ((j : ℝ) ^ 4 * (1 / 2 : ℝ) ^ j) + 128 * (1 / 2 : ℝ) ^ j := by ring
  exact hP.mul_of_nonneg hG (fun p => div_nonneg (pow_nonneg (Real.log_natCast_nonneg _) k)
    (by positivity)) (fun j => by positivity)

theorem pow_add_two_injective :
    Function.Injective fun x : Nat.Primes × ℕ => (x.1 : ℕ) ^ (x.2 + 2) := by
  rintro ⟨⟨p, hp⟩, i⟩ ⟨⟨q, hq⟩, j⟩ h
  have := Nat.Prime.pow_inj hp hq (show p ^ ((i + 1) + 1) = q ^ ((j + 1) + 1) from h)
  obtain ⟨rfl, hij⟩ := this
  simp only [Prod.mk.injEq, true_and]
  omega

/-- A prime power on which `L` does not vanish is `p^{j+2}`. -/
theorem mem_range_of_LL_ne_zero {m : ℕ} (hm : IsPrimePow m) (hL : LL m ≠ 0) :
    m ∈ Set.range fun x : Nat.Primes × ℕ => (x.1 : ℕ) ^ (x.2 + 2) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hm
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    exact absurd (LL_prime (by simpa using hp)) (by simpa using hL)
  · exact ⟨(⟨p, hp⟩, k - 2), by simp only; congr 1; omega⟩

/-- The value at `p^{j+2}`: `L ≤ (j+2)² log² p` and `Λ = log p`. -/
theorem LL_pow_le (p : ℕ) (j : ℕ) :
    LL (p ^ (j + 2)) ≤ ((j : ℝ) + 2) ^ 2 * Real.log p ^ 2 := by
  refine (LL_le_log_sq _).trans (le_of_eq ?_)
  push_cast
  rw [Real.log_pow]; push_cast; ring

theorem pow_add_two_ge {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (p : ℝ) ^ 2 * 2 ^ j ≤ ((p ^ (j + 2) : ℕ) : ℝ) := by
  push_cast
  rw [pow_add, mul_comm]
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) h2 j) (by positivity)

/-- **`Σ_{m prime power} L(m)²/m < ∞`.** -/
theorem summable_primePow_LL_sq_div :
    Summable fun m : ℕ => if IsPrimePow m then LL m ^ 2 / m else 0 := by
  set F : ℕ → ℝ := fun m => if IsPrimePow m then LL m ^ 2 / m else 0
  have hsupp : ∀ m ∉ Set.range (fun x : Nat.Primes × ℕ => (x.1 : ℕ) ^ (x.2 + 2)), F m = 0 := by
    intro m hm
    simp only [F]
    split_ifs with h
    · have : LL m = 0 := by
        by_contra hL; exact hm (mem_range_of_LL_ne_zero h hL)
      simp [this]
    · rfl
  refine (pow_add_two_injective.summable_iff hsupp).mp ?_
  refine (summable_primes_majorant 4).of_nonneg_of_le (fun x => ?_) fun x => ?_
  · simp only [F, Function.comp_apply]; split_ifs <;> positivity
  · obtain ⟨⟨p, hp⟩, j⟩ := x
    simp only [F, Function.comp_apply]
    rw [if_pos ((isPrimePow_nat_iff _).mpr ⟨p, j + 2, hp, by omega, rfl⟩)]
    have hL := LL_pow_le p j
    have hL0 := LL_nonneg (p ^ (j + 2))
    have hge := pow_add_two_ge hp j
    have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 * 2 ^ j := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    have hlog := Real.log_natCast_nonneg p
    calc LL (p ^ (j + 2)) ^ 2 / ((p ^ (j + 2) : ℕ) : ℝ)
        ≤ (((j : ℝ) + 2) ^ 2 * Real.log p ^ 2) ^ 2 / ((p : ℝ) ^ 2 * 2 ^ j) :=
          div_le_div₀ (by positivity) (pow_le_pow_left₀ hL0 hL 2) hp2 hge
      _ = Real.log p ^ 4 / (p : ℝ) ^ 2 * (((j : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ j) := by
          rw [one_div_pow]
          field_simp

/-- **`Σ_m Λ(m) L(m)/m < ∞`.** -/
theorem summable_vonMangoldt_mul_LL_div : Summable fun m : ℕ => Λ m * LL m / m := by
  set F : ℕ → ℝ := fun m => Λ m * LL m / m
  have hsupp : ∀ m ∉ Set.range (fun x : Nat.Primes × ℕ => (x.1 : ℕ) ^ (x.2 + 2)), F m = 0 := by
    intro m hm
    simp only [F]
    by_cases h : IsPrimePow m
    · have : LL m = 0 := by
        by_contra hL; exact hm (mem_range_of_LL_ne_zero h hL)
      simp [this]
    · simp [vonMangoldt_eq_zero_iff.mpr h]
  refine (pow_add_two_injective.summable_iff hsupp).mp ?_
  refine (summable_primes_majorant 3).of_nonneg_of_le (fun x => ?_) fun x => ?_
  · simp only [F, Function.comp_apply]
    exact div_nonneg (mul_nonneg vonMangoldt_nonneg (LL_nonneg _)) (by positivity)
  · obtain ⟨⟨p, hp⟩, j⟩ := x
    simp only [F, Function.comp_apply]
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    have hL := LL_pow_le p j
    have hL0 := LL_nonneg (p ^ (j + 2))
    have hge := pow_add_two_ge hp j
    have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 * 2 ^ j := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    have hlog := Real.log_natCast_nonneg p
    have hj : ((j : ℝ) + 2) ^ 2 ≤ ((j : ℝ) + 2) ^ 4 := by
      have : (1 : ℝ) ≤ (j : ℝ) + 2 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      exact pow_le_pow_right₀ this (by norm_num)
    calc Real.log p * LL (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)
        ≤ Real.log p * (((j : ℝ) + 2) ^ 4 * Real.log p ^ 2) / ((p : ℝ) ^ 2 * 2 ^ j) := by
          refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hL.trans ?_) hlog)
            hp2 hge
          exact mul_le_mul_of_nonneg_right hj (by positivity)
      _ = Real.log p ^ 3 / (p : ℝ) ^ 2 * (((j : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ j) := by
          rw [one_div_pow]
          field_simp

/-! ### Convolutions of prime-power sequences -/

/-- `0 ≤ f(n) ≤ a Λ(n)/n^σ`; such an `f` lives on prime powers. -/
def PPBound (f : ℕ → ℝ) (a σ : ℝ) : Prop := ∀ n, 0 ≤ f n ∧ f n ≤ a * Λ n / (n : ℝ) ^ σ

theorem PPBound.eq_zero {f : ℕ → ℝ} {a σ : ℝ} (hf : PPBound f a σ) {n : ℕ} (hn : ¬IsPrimePow n) :
    f n = 0 := by
  have h := hf n
  rw [vonMangoldt_eq_zero_iff.mpr hn, mul_zero, zero_div] at h
  linarith [h.1, h.2]

theorem PPBound.zero {f : ℕ → ℝ} {a σ : ℝ} (hf : PPBound f a σ) : f 0 = 0 :=
  hf.eq_zero not_isPrimePow_zero

theorem PPBound.isPrimePow {f : ℕ → ℝ} {a σ : ℝ} (hf : PPBound f a σ) {n : ℕ} (hn : f n ≠ 0) :
    IsPrimePow n := by
  by_contra h; exact hn (hf.eq_zero h)

theorem conv_nonneg {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (m : ℕ) :
    0 ≤ (f ⍟ g) m := by
  rw [congrFun (LSeries.convolution_def f g) m]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hf _) (hg _)

/-- `(f ⍟ g)(m) ≤ ab L(m)/m^σ`. -/
theorem conv_le_LL {f g : ℕ → ℝ} {a b σ : ℝ} (hf : PPBound f a σ) (hg : PPBound g b σ) (m : ℕ) :
    (f ⍟ g) m ≤ a * b * LL m / (m : ℝ) ^ σ := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [LSeries.convolution_map_zero, LL]
  rw [congrFun (LSeries.convolution_def f g) m, LL_apply, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' := Nat.mem_divisorsAntidiagonal.mp hp
  have h1 : (0 : ℝ) ≤ (p.1 : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (p.2 : ℝ) := Nat.cast_nonneg _
  have hm' : ((m : ℕ) : ℝ) ^ σ = (p.1 : ℝ) ^ σ * (p.2 : ℝ) ^ σ := by
    rw [← Real.mul_rpow h1 h2, ← Nat.cast_mul, hp'.1]
  rw [hm']
  calc f p.1 * g p.2 ≤ a * Λ p.1 / (p.1 : ℝ) ^ σ * (b * Λ p.2 / (p.2 : ℝ) ^ σ) :=
        mul_le_mul (hf p.1).2 (hg p.2).2 (hg p.2).1 ((hf p.1).1.trans (hf p.1).2)
    _ = a * b * (Λ p.1 * Λ p.2) / ((p.1 : ℝ) ^ σ * (p.2 : ℝ) ^ σ) := by
        rw [div_mul_div_comm]; ring

/-- `Σ_m (F ⍟ G)(m) = Σ F · Σ G` for non-negative summable `F, G` vanishing at `0`. -/
theorem hasSum_conv {F G : ℕ → ℝ} (hF : ∀ n, 0 ≤ F n) (hG : ∀ n, 0 ≤ G n) (hF0 : F 0 = 0)
    (hG0 : G 0 = 0) (hFs : Summable F) (hGs : Summable G) :
    HasSum (F ⍟ G) ((∑' n, F n) * ∑' n, G n) := by
  have hprod : HasSum (fun p : ℕ × ℕ => F p.1 * G p.2) ((∑' n, F n) * ∑' n, G n) :=
    hFs.hasSum.mul hGs.hasSum (hFs.mul_of_nonneg hGs hF hG)
  have := hasSum_convolution_mul (h := fun _ => 1) hF0 hG0 (by simpa using hprod)
  simpa using this

/-- **Triple sums see only same-prime pairs**: for `PPBound`s with `σ = 1/2`,
`Σ_m (f ⍟ g)(m) h(m) ≤ abc Σ_m Λ(m) L(m)/m`. -/
theorem conv_mul_le {f g h : ℕ → ℝ} {a b c : ℝ} (hf : PPBound f a (1 / 2))
    (hg : PPBound g b (1 / 2)) (hh : PPBound h c (1 / 2)) :
    Summable (fun m => (f ⍟ g) m * h m) ∧
      ∑' m, (f ⍟ g) m * h m ≤ a * b * c * ∑' m : ℕ, Λ m * LL m / m := by
  have hpt : ∀ m : ℕ, (f ⍟ g) m * h m ≤ a * b * c * (Λ m * LL m / m) := fun m => by
    rcases eq_or_ne m 0 with rfl | hm
    · simp [LSeries.convolution_map_zero]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have h1 := conv_le_LL hf hg m
    have h2 := (hh m).2
    have hc0 := conv_nonneg (fun n => (hf n).1) (fun n => (hg n).1) m
    calc (f ⍟ g) m * h m ≤ a * b * LL m / (m : ℝ) ^ (1 / 2 : ℝ) *
          (c * Λ m / (m : ℝ) ^ (1 / 2 : ℝ)) := mul_le_mul h1 h2 (hh m).1 (hc0.trans h1)
      _ = a * b * c * (Λ m * LL m / ((m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ))) := by
          rw [div_mul_div_comm]; ring
      _ = a * b * c * (Λ m * LL m / m) := by
          rw [← Real.rpow_add hm0]; norm_num
  have hnn : ∀ m, 0 ≤ (f ⍟ g) m * h m := fun m =>
    mul_nonneg (conv_nonneg (fun n => (hf n).1) (fun n => (hg n).1) m) (hh m).1
  have hS := summable_vonMangoldt_mul_LL_div.mul_left (a * b * c)
  refine ⟨hS.of_nonneg_of_le hnn hpt, ?_⟩
  rw [← tsum_mul_left]
  exact (hS.of_nonneg_of_le hnn hpt).tsum_le_tsum hpt hS

theorem isPrimePow_mul_self {u : ℕ} (hu : IsPrimePow u) : IsPrimePow (u * u) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff u).mp hu
  exact (isPrimePow_nat_iff _).mpr ⟨p, k + k, hp, by omega, by rw [pow_add]⟩

/-- **The square of a convolution off prime powers**: if `m` is not a prime power, only the
factorizations `(u, v)` and `(v, u)` contribute, so
`(f ⍟ g)(m)² = (f² ⍟ g²)(m) + (fg ⍟ fg)(m)`. -/
theorem sq_conv_eq_of_not_isPrimePow {f g : ℕ → ℝ}
    (hfpp : ∀ n, f n ≠ 0 → IsPrimePow n) (hgpp : ∀ n, g n ≠ 0 → IsPrimePow n) {m : ℕ}
    (hm : ¬IsPrimePow m) :
    (f ⍟ g) m ^ 2 = ((fun n => f n ^ 2) ⍟ (fun n => g n ^ 2)) m +
      ((fun n => f n * g n) ⍟ (fun n => f n * g n)) m := by
  rw [congrFun (LSeries.convolution_def f g) m, congrFun (LSeries.convolution_def _ _) m,
    congrFun (LSeries.convolution_def _ _) m, ← Finset.sum_add_distrib, sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Nat.mem_divisorsAntidiagonal.mp hp
  by_cases hF : f p.1 * g p.2 = 0
  · rw [hF, zero_mul]
    have h1 : f p.1 ^ 2 * g p.2 ^ 2 = 0 := by rw [← mul_pow, hF]; ring
    have h2 : f p.1 * g p.1 * (f p.2 * g p.2) = 0 := by
      rw [show f p.1 * g p.1 * (f p.2 * g p.2) = (f p.1 * g p.2) * (g p.1 * f p.2) by ring, hF,
        zero_mul]
    rw [show f p.1 ^ 2 * g p.2 ^ 2 = 0 from h1, h2, add_zero]
  have hu : IsPrimePow p.1 := hfpp _ (left_ne_zero_of_mul hF)
  have hv : IsPrimePow p.2 := hgpp _ (right_ne_zero_of_mul hF)
  have hm' : ¬IsPrimePow (p.1 * p.2) := by rw [hp'.1]; exact hm
  have hsw : p.swap ∈ m.divisorsAntidiagonal := Nat.swap_mem_divisorsAntidiagonal.mpr hp
  have hne : p ≠ p.swap := by
    intro h
    have h12 : p.1 = p.2 := congrArg Prod.fst h
    exact hm' (by rw [← h12]; exact isPrimePow_mul_self hu)
  have hsum : ∑ q ∈ m.divisorsAntidiagonal, f q.1 * g q.2 = f p.1 * g p.2 + f p.2 * g p.1 := by
    refine Finset.sum_eq_add p p.swap hne (fun q hq hq' => ?_) (fun h => absurd hp h)
      (fun h => absurd hsw h)
    by_contra hq0
    have hq1 : IsPrimePow q.1 := hfpp _ (left_ne_zero_of_mul hq0)
    have hq2 : IsPrimePow q.2 := hgpp _ (right_ne_zero_of_mul hq0)
    have hqe : q.1 * q.2 = p.1 * p.2 := by
      rw [(Nat.mem_divisorsAntidiagonal.mp hq).1, hp'.1]
    rcases eq_or_swap_of_mul_eq hu hv hm' hq1 hq2 hqe with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hq'.1 (Prod.ext h1 h2)
    · exact hq'.2 (Prod.ext h1 h2)
  rw [hsum]
  ring

theorem sq_conv_le_of_not_isPrimePow {f g : ℕ → ℝ}
    (hfpp : ∀ n, f n ≠ 0 → IsPrimePow n) (hgpp : ∀ n, g n ≠ 0 → IsPrimePow n) {m : ℕ}
    (hm : ¬IsPrimePow m) :
    (f ⍟ g) m ^ 2 ≤ ((fun n => f n ^ 2) ⍟ (fun n => g n ^ 2)) m +
      ((fun n => f n * g n) ⍟ (fun n => f n * g n)) m :=
  le_of_eq (sq_conv_eq_of_not_isPrimePow hfpp hgpp hm)

/-- `(fg ⍟ fg)(m) ≤ (f ⍟ g)(m)²`: the swapped pairs are part of the square. -/
theorem conv_mul_self_le_sq {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (m : ℕ) :
    ((fun n => f n * g n) ⍟ (fun n => f n * g n)) m ≤ (f ⍟ g) m ^ 2 := by
  rw [congrFun (LSeries.convolution_def f g) m, congrFun (LSeries.convolution_def _ _) m, sq,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  have hsw : p.swap ∈ m.divisorsAntidiagonal := Nat.swap_mem_divisorsAntidiagonal.mpr hp
  have h := Finset.single_le_sum (f := fun q : ℕ × ℕ => f q.1 * g q.2)
    (fun q _ => mul_nonneg (hf _) (hg _)) hsw
  calc f p.1 * g p.1 * (f p.2 * g p.2) = f p.1 * g p.2 * (f p.swap.1 * g p.swap.2) := by
        simp only [Prod.fst_swap, Prod.snd_swap]; ring
    _ ≤ f p.1 * g p.2 * ∑ q ∈ m.divisorsAntidiagonal, f q.1 * g q.2 :=
        mul_le_mul_of_nonneg_left h (mul_nonneg (hf _) (hg _))

theorem sq_sum_ge_sum_sq {ι : Type*} (s : Finset ι) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∑ i ∈ s, x i ^ 2 ≤ (∑ i ∈ s, x i) ^ 2 := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => hx j) hi) (hx i)

/-- The `(pp)`-part weight `1_{m prime power} L(m)²/m`. -/
def ppWeight (m : ℕ) : ℝ := if IsPrimePow m then LL m ^ 2 / m else 0

theorem ppWeight_nonneg (m : ℕ) : 0 ≤ ppWeight m := by
  unfold ppWeight; split_ifs <;> positivity

theorem conv_sq_le_sq {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (m : ℕ) :
    ((fun n => f n ^ 2) ⍟ (fun n => g n ^ 2)) m ≤ (f ⍟ g) m ^ 2 := by
  rw [congrFun (LSeries.convolution_def f g) m, congrFun (LSeries.convolution_def _ _) m]
  simp_rw [← mul_pow]
  exact sq_sum_ge_sum_sq _ fun p => mul_nonneg (hf _) (hg _)

/-- On a prime power, `(f ⍟ g)(m)² ≤ a²b² L(m)²/m`. -/
theorem sq_conv_le_ppWeight {f g : ℕ → ℝ} {a b : ℝ} (hf : PPBound f a (1 / 2))
    (hg : PPBound g b (1 / 2)) {m : ℕ} (hm : IsPrimePow m) :
    (f ⍟ g) m ^ 2 ≤ a ^ 2 * b ^ 2 * ppWeight m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.one_lt.le.trans_lt' zero_lt_one
  have h1 := conv_le_LL hf hg m
  have hc := conv_nonneg (fun n => (hf n).1) (fun n => (hg n).1) m
  rw [ppWeight, if_pos hm]
  calc (f ⍟ g) m ^ 2 ≤ (a * b * LL m / (m : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ hc h1 2
    _ = a ^ 2 * b ^ 2 * (LL m ^ 2 / ((m : ℝ) ^ (1 / 2 : ℝ)) ^ 2) := by ring
    _ = a ^ 2 * b ^ 2 * (LL m ^ 2 / m) := by rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hm0.le]

/-- **The energy of a product of prime-power sequences.** For `PPBound`s with `σ = 1/2`:
`Σf² Σg² ≤ Σ_m (f ⍟ g)(m)² ≤ Σf² Σg² + (Σ fg)² + a²b² Σ_m 1_{pp} L(m)²/m`. -/
theorem sum_sq_conv {f g : ℕ → ℝ} {a b : ℝ} (hf : PPBound f a (1 / 2))
    (hg : PPBound g b (1 / 2)) (hf2 : Summable fun n => f n ^ 2)
    (hg2 : Summable fun n => g n ^ 2) (hfg : Summable fun n => f n * g n) :
    Summable (fun m => (f ⍟ g) m ^ 2) ∧
      (∑' n, f n ^ 2) * (∑' n, g n ^ 2) ≤ ∑' m, (f ⍟ g) m ^ 2 ∧
      ∑' m, (f ⍟ g) m ^ 2 ≤ (∑' n, f n ^ 2) * (∑' n, g n ^ 2) + (∑' n, f n * g n) ^ 2 +
        a ^ 2 * b ^ 2 * ∑' m, ppWeight m := by
  have hf0 := fun n => (hf n).1
  have hg0 := fun n => (hg n).1
  have hA := hasSum_conv (fun n => sq_nonneg (f n)) (fun n => sq_nonneg (g n))
    (by simp [hf.zero]) (by simp [hg.zero]) hf2 hg2
  have hB := hasSum_conv (fun n => mul_nonneg (hf0 n) (hg0 n)) (fun n => mul_nonneg (hf0 n) (hg0 n))
    (by simp [hf.zero]) (by simp [hf.zero]) hfg hfg
  have hC := summable_primePow_LL_sq_div.mul_left (a ^ 2 * b ^ 2)
  have hupper : ∀ m, (f ⍟ g) m ^ 2 ≤ ((fun n => f n ^ 2) ⍟ (fun n => g n ^ 2)) m +
      ((fun n => f n * g n) ⍟ (fun n => f n * g n)) m + a ^ 2 * b ^ 2 * ppWeight m := by
    intro m
    have hc1 := conv_nonneg (fun n => sq_nonneg (f n)) (fun n => sq_nonneg (g n)) m
    have hc2 := conv_nonneg (fun n => mul_nonneg (hf0 n) (hg0 n))
      (fun n => mul_nonneg (hf0 n) (hg0 n)) m
    by_cases hm : IsPrimePow m
    · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.one_lt.le.trans_lt' zero_lt_one
      have h1 := conv_le_LL hf hg m
      have hc := conv_nonneg hf0 hg0 m
      have : (f ⍟ g) m ^ 2 ≤ a ^ 2 * b ^ 2 * ppWeight m := by
        rw [ppWeight, if_pos hm]
        calc (f ⍟ g) m ^ 2 ≤ (a * b * LL m / (m : ℝ) ^ (1 / 2 : ℝ)) ^ 2 :=
              pow_le_pow_left₀ hc h1 2
          _ = a ^ 2 * b ^ 2 * (LL m ^ 2 / ((m : ℝ) ^ (1 / 2 : ℝ)) ^ 2) := by ring
          _ = a ^ 2 * b ^ 2 * (LL m ^ 2 / m) := by
              rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hm0.le]
      linarith
    · have := sq_conv_le_of_not_isPrimePow (fun n => hf.isPrimePow)
        (fun n => hg.isPrimePow) hm
      have h0 : a ^ 2 * b ^ 2 * ppWeight m = 0 := by rw [ppWeight, if_neg hm, mul_zero]
      linarith
  have hlower : ∀ m, ((fun n => f n ^ 2) ⍟ (fun n => g n ^ 2)) m ≤ (f ⍟ g) m ^ 2 := by
    intro m
    rw [congrFun (LSeries.convolution_def f g) m, congrFun (LSeries.convolution_def _ _) m]
    simp_rw [← mul_pow]
    exact sq_sum_ge_sum_sq _ fun p => mul_nonneg (hf0 _) (hg0 _)
  have hS : Summable fun m => ((fun n => f n ^ 2) ⍟ (fun n => g n ^ 2)) m +
      ((fun n => f n * g n) ⍟ (fun n => f n * g n)) m + a ^ 2 * b ^ 2 * ppWeight m :=
    (hA.summable.add hB.summable).add (by simpa [ppWeight] using hC)
  have hsq : Summable fun m => (f ⍟ g) m ^ 2 :=
    hS.of_nonneg_of_le (fun m => sq_nonneg _) hupper
  refine ⟨hsq, ?_, ?_⟩
  · rw [← hA.tsum_eq]
    exact hA.summable.tsum_le_tsum hlower hsq
  · refine (hsq.tsum_le_tsum hupper hS).trans (le_of_eq ?_)
    rw [(hA.summable.add hB.summable).tsum_add (by simpa [ppWeight] using hC),
      hA.summable.tsum_add hB.summable, hA.tsum_eq, hB.tsum_eq, tsum_mul_left]
    ring

/-- **The weighted energy** (the Montgomery–Vaughan error of a product): with the extra decay
`f ≤ a' Λ/n^{3/2}`, `g ≤ b' Λ/n^{3/2}`,
`Σ_m m (f ⍟ g)(m)² ≤ Σ nf² Σ ng² + (Σ n fg)² + a b a' b' Σ_m 1_{pp} L(m)²/m`. -/
theorem sum_mul_sq_conv {f g : ℕ → ℝ} {a b a' b' : ℝ} (hf : PPBound f a (1 / 2))
    (hg : PPBound g b (1 / 2)) (hf' : PPBound f a' (3 / 2)) (hg' : PPBound g b' (3 / 2))
    (hf2 : Summable fun n : ℕ => (n : ℝ) * f n ^ 2) (hg2 : Summable fun n : ℕ => (n : ℝ) * g n ^ 2)
    (hfg : Summable fun n : ℕ => (n : ℝ) * (f n * g n)) :
    Summable (fun m : ℕ => (m : ℝ) * (f ⍟ g) m ^ 2) ∧
      ∑' m : ℕ, (m : ℝ) * (f ⍟ g) m ^ 2 ≤
        (∑' n : ℕ, (n : ℝ) * f n ^ 2) * (∑' n : ℕ, (n : ℝ) * g n ^ 2) +
          (∑' n : ℕ, (n : ℝ) * (f n * g n)) ^ 2 + a * b * a' * b' * ∑' m, ppWeight m := by
  have hf0 := fun n => (hf n).1
  have hg0 := fun n => (hg n).1
  set F : ℕ → ℝ := fun n => Real.sqrt n * f n
  set G : ℕ → ℝ := fun n => Real.sqrt n * g n
  have hF0 : ∀ n, 0 ≤ F n := fun n => mul_nonneg (Real.sqrt_nonneg _) (hf0 n)
  have hG0 : ∀ n, 0 ≤ G n := fun n => mul_nonneg (Real.sqrt_nonneg _) (hg0 n)
  have hFG : ∀ m : ℕ, (F ⍟ G) m = Real.sqrt m * (f ⍟ g) m := by
    intro m
    rw [congrFun (LSeries.convolution_def F G) m, congrFun (LSeries.convolution_def f g) m,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
    simp only [F, G]
    rw [← hp', Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]; ring
  have hF2 : (fun n => F n ^ 2) = fun n : ℕ => (n : ℝ) * f n ^ 2 := by
    funext n; simp only [F]; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hG2 : (fun n => G n ^ 2) = fun n : ℕ => (n : ℝ) * g n ^ 2 := by
    funext n; simp only [G]; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hFGm : (fun n => F n * G n) = fun n : ℕ => (n : ℝ) * (f n * g n) := by
    funext n; simp only [F, G]
    rw [show Real.sqrt n * f n * (Real.sqrt n * g n) = (Real.sqrt n * Real.sqrt n) * (f n * g n)
      by ring, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hA := hasSum_conv (fun n => by positivity) (fun n => by positivity)
    (by simp [hf.zero]) (by simp [hg.zero]) hf2 hg2
  have hB := hasSum_conv (fun n => mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (hf0 n) (hg0 n)))
    (fun n => mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (hf0 n) (hg0 n)))
    (by simp) (by simp) hfg hfg
  have hC := summable_primePow_LL_sq_div.mul_left (a * b * a' * b')
  have hupper : ∀ m : ℕ, (m : ℝ) * (f ⍟ g) m ^ 2 ≤
      ((fun n : ℕ => (n : ℝ) * f n ^ 2) ⍟ (fun n : ℕ => (n : ℝ) * g n ^ 2)) m +
      ((fun n : ℕ => (n : ℝ) * (f n * g n)) ⍟ (fun n : ℕ => (n : ℝ) * (f n * g n))) m +
        a * b * a' * b' * ppWeight m := by
    intro m
    have hc1 := conv_nonneg (fun n => by positivity : ∀ n : ℕ, 0 ≤ (n : ℝ) * f n ^ 2)
      (fun n => by positivity : ∀ n : ℕ, 0 ≤ (n : ℝ) * g n ^ 2) m
    have hc2 := conv_nonneg (fun n => mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (hf0 n) (hg0 n)))
      (fun n => mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (hf0 n) (hg0 n))) m
    by_cases hm : IsPrimePow m
    · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.one_lt.le.trans_lt' zero_lt_one
      have h1 := conv_le_LL hf hg m
      have h2 := conv_le_LL hf' hg' m
      have hc := conv_nonneg hf0 hg0 m
      have hpow : (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (3 / 2 : ℝ) = (m : ℝ) ^ 2 := by
        rw [← Real.rpow_add hm0, show (1 / 2 : ℝ) + 3 / 2 = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
      have : (m : ℝ) * (f ⍟ g) m ^ 2 ≤ a * b * a' * b' * ppWeight m := by
        rw [ppWeight, if_pos hm]
        calc (m : ℝ) * (f ⍟ g) m ^ 2 = (m : ℝ) * ((f ⍟ g) m * (f ⍟ g) m) := by ring
          _ ≤ (m : ℝ) * (a * b * LL m / (m : ℝ) ^ (1 / 2 : ℝ) *
                (a' * b' * LL m / (m : ℝ) ^ (3 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 hc (hc.trans h1)) hm0.le
          _ = a * b * a' * b' * LL m ^ 2 * ((m : ℝ) /
                ((m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (3 / 2 : ℝ))) := by ring
          _ = a * b * a' * b' * (LL m ^ 2 / m) := by
              rw [hpow]; field_simp
      linarith
    · have hsq := sq_conv_le_of_not_isPrimePow (f := F) (g := G)
        (fun n hn => hf.isPrimePow (right_ne_zero_of_mul hn))
        (fun n hn => hg.isPrimePow (right_ne_zero_of_mul hn)) hm
      rw [hFG, hF2, hG2, hFGm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
      have h0 : a * b * a' * b' * ppWeight m = 0 := by rw [ppWeight, if_neg hm, mul_zero]
      linarith
  have hS : Summable fun m : ℕ =>
      ((fun n : ℕ => (n : ℝ) * f n ^ 2) ⍟ (fun n : ℕ => (n : ℝ) * g n ^ 2)) m +
      ((fun n : ℕ => (n : ℝ) * (f n * g n)) ⍟ (fun n : ℕ => (n : ℝ) * (f n * g n))) m +
        a * b * a' * b' * ppWeight m :=
    (hA.summable.add hB.summable).add (by simpa [ppWeight] using hC)
  have hsum : Summable fun m : ℕ => (m : ℝ) * (f ⍟ g) m ^ 2 :=
    hS.of_nonneg_of_le (fun m => by positivity) hupper
  refine ⟨hsum, (hsum.tsum_le_tsum hupper hS).trans (le_of_eq ?_)⟩
  rw [(hA.summable.add hB.summable).tsum_add (by simpa [ppWeight] using hC),
    hA.summable.tsum_add hB.summable, hA.tsum_eq, hB.tsum_eq, tsum_mul_left, sq]

/-- **The matching lower bound**: `Σ (f ⍟ g)² ≥ Σf² Σg² + (Σ fg)² − 2a²b² Σ_{pp} L(m)²/m`. -/
theorem sum_sq_conv_ge {f g : ℕ → ℝ} {a b : ℝ} (hf : PPBound f a (1 / 2))
    (hg : PPBound g b (1 / 2)) (hf2 : Summable fun n => f n ^ 2)
    (hg2 : Summable fun n => g n ^ 2) (hfg : Summable fun n => f n * g n) :
    (∑' n, f n ^ 2) * (∑' n, g n ^ 2) + (∑' n, f n * g n) ^ 2 -
        2 * (a ^ 2 * b ^ 2) * ∑' m, ppWeight m ≤ ∑' m, (f ⍟ g) m ^ 2 := by
  have hf0 := fun n => (hf n).1
  have hg0 := fun n => (hg n).1
  have hA := hasSum_conv (fun n => sq_nonneg (f n)) (fun n => sq_nonneg (g n))
    (by simp [hf.zero]) (by simp [hg.zero]) hf2 hg2
  have hB := hasSum_conv (fun n => mul_nonneg (hf0 n) (hg0 n)) (fun n => mul_nonneg (hf0 n) (hg0 n))
    (by simp [hf.zero]) (by simp [hf.zero]) hfg hfg
  have hW : Summable ppWeight := summable_primePow_LL_sq_div
  have hC : Summable fun m => 2 * (a ^ 2 * b ^ 2) * ppWeight m := hW.mul_left _
  obtain ⟨hsq, -, -⟩ := sum_sq_conv hf hg hf2 hg2 hfg
  have hpt : ∀ m, ((fun n => f n ^ 2) ⍟ (fun n => g n ^ 2)) m +
      ((fun n => f n * g n) ⍟ (fun n => f n * g n)) m - 2 * (a ^ 2 * b ^ 2) * ppWeight m ≤
      (f ⍟ g) m ^ 2 := by
    intro m
    by_cases hm : IsPrimePow m
    · have h1 := conv_sq_le_sq hf0 hg0 m
      have h2 := conv_mul_self_le_sq hf0 hg0 m
      have h3 := sq_conv_le_ppWeight hf hg hm
      nlinarith [sq_nonneg ((f ⍟ g) m)]
    · rw [sq_conv_eq_of_not_isPrimePow (fun n => hf.isPrimePow) (fun n => hg.isPrimePow) hm,
        ppWeight, if_neg hm]
      linarith
  have hS : Summable fun m => ((fun n => f n ^ 2) ⍟ (fun n => g n ^ 2)) m +
      ((fun n => f n * g n) ⍟ (fun n => f n * g n)) m - 2 * (a ^ 2 * b ^ 2) * ppWeight m :=
    (hA.summable.add hB.summable).sub hC
  refine le_of_eq_of_le ?_ (hS.tsum_le_tsum hpt hsq)
  rw [(hA.summable.add hB.summable).tsum_sub hC, hA.summable.tsum_add hB.summable, hA.tsum_eq,
    hB.tsum_eq, tsum_mul_left]
  ring

end RHTower.PrimePowerPairs
