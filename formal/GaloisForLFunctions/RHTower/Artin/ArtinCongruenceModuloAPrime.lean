import GaloisForLFunctions.RHTower.Artin.ArtinCyclicIntegralSpan
import Mathlib.Data.Nat.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integer-valued combinations of characters are congruent on `p`-regular parts

Let `𝓞` be the algebraic integers of `ℂ`, `p` a prime and `f` an `𝓞`-combination of characters
of a finite group `G`. If `y` is a power of `x` with `x^{p^k} = y^{p^k}` (for instance `y` the
`p`-regular part of `x`) and `f(x)`, `f(y)` are integers, then `f(x) ≡ f(y) (mod p)`
(`int_dvd_sub_of_pow_eq`).

On the cyclic group of `x` the function `f` is an `𝓞`-combination `Σ a_i χ_i` of linear
characters (`restrict_mem_linearIntSpan`), and `χ_i(x)^q = χ_i(x^q) = χ_i(y)^q` for `q = p^k`.
Modulo `p𝓞` the `q`-th power is additive (`add_pow_prime_pow_sub_mem`), so
`f(x)^q ≡ Σ a_i^q χ_i(x)^q = Σ a_i^q χ_i(y)^q ≡ f(y)^q` (`linearIntSpan_pow_congr`). An integer in
`p𝓞` is divisible by `p` (`int_dvd_of_mem_primeMultiples`), and `n^q ≡ n (mod p)`.
-/

open scoped Classical BigOperators

noncomputable section

universe u

namespace GaloisForLFunctions

/-! ### Multiples of a prime by algebraic integers -/

theorem isIntegral_intCast_complex (n : ℤ) : IsIntegral ℤ (n : ℂ) := by
  have h : IsIntegral ℤ (algebraMap ℤ ℂ n) := isIntegral_algebraMap
  rwa [eq_intCast] at h

theorem isIntegral_natCast_complex (n : ℕ) : IsIntegral ℤ (n : ℂ) := by
  have h := isIntegral_intCast_complex (n : ℤ)
  rwa [Int.cast_natCast] at h

/-- The multiples of `p` by algebraic integers: the ideal `p𝓞`. -/
def primeMultiples (p : ℕ) : AddSubgroup ℂ where
  carrier := {z | ∃ c : ℂ, IsIntegral ℤ c ∧ z = p * c}
  zero_mem' := ⟨0, isIntegral_zero, (mul_zero _).symm⟩
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, hc.add hd, (mul_add _ _ _).symm⟩
  neg_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨-c, hc.neg, (mul_neg _ _).symm⟩

theorem mul_mem_primeMultiples {p : ℕ} {a z : ℂ} (ha : IsIntegral ℤ a)
    (hz : z ∈ primeMultiples p) : a * z ∈ primeMultiples p := by
  obtain ⟨c, hc, rfl⟩ := hz
  exact ⟨a * c, ha.mul hc, by ring⟩

/-- **Modulo `p𝓞` the `p^k`-th power is additive.** -/
theorem add_pow_prime_pow_sub_mem {p : ℕ} (hp : p.Prime) (k : ℕ) {u v : ℂ}
    (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v) :
    (u + v) ^ p ^ k - (u ^ p ^ k + v ^ p ^ k) ∈ primeMultiples p := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = p ^ k := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact pow_ne_zero _ hp.ne_zero
  have hsum : u ^ q + v ^ q = ∑ m ∈ Finset.range (q + 1),
      ((if m = q then u ^ q else 0) + if m = 0 then v ^ q else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr (Nat.lt_succ_self q)),
      if_pos (Finset.mem_range.mpr (Nat.succ_pos q))]
  rw [add_pow, hsum, ← Finset.sum_sub_distrib]
  refine AddSubgroup.sum_mem _ fun m _ => ?_
  by_cases hm0 : m = 0
  · rw [hm0, if_neg (Ne.symm hq0), if_pos rfl]
    have e : u ^ 0 * v ^ (q - 0) * ((q.choose 0 : ℕ) : ℂ) - (0 + v ^ q) = 0 := by simp
    rw [e]
    exact zero_mem _
  · by_cases hmq : m = q
    · rw [hmq, if_pos rfl, if_neg hq0]
      have e : u ^ q * v ^ (q - q) * ((q.choose q : ℕ) : ℂ) - (u ^ q + 0) = 0 := by simp
      rw [e]
      exact zero_mem _
    · rw [if_neg hmq, if_neg hm0, add_zero, sub_zero]
      obtain ⟨d, hd⟩ : p ∣ q.choose m := by
        rw [hq]
        exact hp.dvd_choose_pow hm0 (hq ▸ hmq)
      refine ⟨u ^ m * v ^ (q - m) * d,
        ((hu.pow m).mul (hv.pow _)).mul (isIntegral_natCast_complex d), ?_⟩
      rw [hd]
      push_cast
      ring

/-- An integer that is `p` times an algebraic integer is divisible by `p`. -/
theorem int_dvd_of_mem_primeMultiples {p : ℕ} (hp : p ≠ 0) {m : ℤ}
    (h : (m : ℂ) ∈ primeMultiples p) : (p : ℤ) ∣ m := by
  obtain ⟨c, hc, hmc⟩ := h
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hr : algebraMap ℚ ℂ ((m : ℚ) / p) = c := by
    rw [eq_ratCast]
    push_cast
    rw [hmc]
    exact mul_div_cancel_left₀ c hp'
  rw [← hr] at hc
  have hq : IsIntegral ℤ ((m : ℚ) / p) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hc
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  rw [eq_intCast] at hy
  have h2 : (m : ℚ) = (p : ℚ) * (y : ℚ) := by
    rw [hy]
    field_simp
  exact ⟨y, by exact_mod_cast h2⟩

/-- `n^{p^k} ≡ n (mod p)`. -/
theorem int_dvd_pow_prime_pow_sub {p : ℕ} (hp : p.Prime) (k : ℕ) (n : ℤ) :
    (p : ℤ) ∣ n ^ p ^ k - n := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card_pow, sub_self]

/-! ### Combinations of linear characters -/

/-- The span over the algebraic integers of the linear characters of a group. -/
def linearIntSpan (A : Type u) [Group A] : AddSubgroup (A → ℂ) :=
  AddSubgroup.closure {f | ∃ a : ℂ, IsIntegral ℤ a ∧ ∃ χ : LinearCharacter A,
    f = fun c => a * ((χ c : ℂˣ) : ℂ)}

/-- **On an `𝓞`-combination of linear characters, `x^q = y^q` gives `φ(x)^q ≡ φ(y)^q` modulo
`p𝓞`**, `q = p^k`; the two values are algebraic integers. -/
theorem linearIntSpan_pow_congr {A : Type u} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    (k : ℕ) {x y : A} (hxy : x ^ p ^ k = y ^ p ^ k) {φ : A → ℂ} (hφ : φ ∈ linearIntSpan A) :
    IsIntegral ℤ (φ x) ∧ IsIntegral ℤ (φ y) ∧
      φ x ^ p ^ k - φ y ^ p ^ k ∈ primeMultiples p := by
  refine AddSubgroup.closure_induction (p := fun φ _ => IsIntegral ℤ (φ x) ∧ IsIntegral ℤ (φ y) ∧
    φ x ^ p ^ k - φ y ^ p ^ k ∈ primeMultiples p) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨a, ha, χ, rfl⟩
    refine ⟨ha.mul (isIntegral_linearCharacter χ x), ha.mul (isIntegral_linearCharacter χ y), ?_⟩
    have e : (a * ((χ x : ℂˣ) : ℂ)) ^ p ^ k - (a * ((χ y : ℂˣ) : ℂ)) ^ p ^ k = 0 := by
      rw [mul_pow, mul_pow, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow,
        ← map_pow, hxy, sub_self]
    rw [e]
    exact zero_mem _
  · refine ⟨isIntegral_zero, isIntegral_zero, ?_⟩
    simp only [Pi.zero_apply, sub_self]
    exact zero_mem _
  · rintro φ₁ φ₂ _ _ ⟨h1x, h1y, h1⟩ ⟨h2x, h2y, h2⟩
    refine ⟨h1x.add h2x, h1y.add h2y, ?_⟩
    have e : (φ₁ + φ₂) x ^ p ^ k - (φ₁ + φ₂) y ^ p ^ k =
        ((φ₁ x + φ₂ x) ^ p ^ k - (φ₁ x ^ p ^ k + φ₂ x ^ p ^ k)) -
          ((φ₁ y + φ₂ y) ^ p ^ k - (φ₁ y ^ p ^ k + φ₂ y ^ p ^ k)) +
          (φ₁ x ^ p ^ k - φ₁ y ^ p ^ k) + (φ₂ x ^ p ^ k - φ₂ y ^ p ^ k) := by
      simp only [Pi.add_apply]
      ring
    rw [e]
    exact add_mem (add_mem (sub_mem (add_pow_prime_pow_sub_mem hp k h1x h2x)
      (add_pow_prime_pow_sub_mem hp k h1y h2y)) h1) h2
  · rintro φ _ ⟨hx, hy, h⟩
    refine ⟨hx.neg, hy.neg, ?_⟩
    have e : (-φ) x ^ p ^ k - (-φ) y ^ p ^ k =
        (-1) ^ p ^ k * (φ x ^ p ^ k - φ y ^ p ^ k) := by
      simp only [Pi.neg_apply]
      rw [neg_pow (φ x), neg_pow (φ y)]
      ring
    rw [e]
    exact mul_mem_primeMultiples (isIntegral_one.neg.pow _) h

variable {G : Type u} [Group G] [Fintype G]

/-- **On a cyclic subgroup an `𝓞`-combination of characters is an `𝓞`-combination of linear
characters.** -/
theorem restrict_mem_linearIntSpan {f : G → ℂ} (hf : f ∈ virtualIntGroup G) (x : G) :
    (fun c : Subgroup.zpowers x => f c) ∈ linearIntSpan (Subgroup.zpowers x) := by
  letI : CommGroup (Subgroup.zpowers x) := IsCyclic.commGroup
  refine AddSubgroup.closure_induction
    (p := fun f _ => (fun c : Subgroup.zpowers x => f c) ∈ linearIntSpan (Subgroup.zpowers x))
    ?_ ?_ ?_ ?_ hf
  · rintro f ⟨a, ha, χ, hχ, rfl⟩
    -- the restriction of a character to an abelian group is a sum of linear characters
    have hres : (fun c : Subgroup.zpowers x => χ c) ∈
        finiteAbelianLinearVirtualCharacterGroup (Subgroup.zpowers x) := by
      rw [← finiteAbelian_virtualCharacterGroup_eq_linear]
      exact AddSubgroup.subset_closure (restrict_mem_fdCharacterSet (Subgroup.zpowers x) hχ)
    refine AddSubgroup.closure_induction
      (p := fun θ _ => (fun c : Subgroup.zpowers x => a * θ c) ∈
        linearIntSpan (Subgroup.zpowers x)) ?_ ?_ ?_ ?_ hres
    · rintro θ ⟨χ', rfl⟩
      exact AddSubgroup.subset_closure ⟨a, ha, χ', funext fun c =>
        congrArg (a * ·) (linearVirtualCharacter_apply (Subgroup.zpowers x) χ' c)⟩
    · simp only [Pi.zero_apply, mul_zero]
      exact zero_mem _
    · intro u v _ _ hu hv
      have e : (fun c : Subgroup.zpowers x => a * (u + v) c) =
          (fun c => a * u c) + fun c => a * v c := funext fun c => mul_add _ _ _
      rw [e]
      exact add_mem hu hv
    · intro u _ hu
      have e : (fun c : Subgroup.zpowers x => a * (-u) c) = -fun c => a * u c :=
        funext fun c => mul_neg _ _
      rw [e]
      exact neg_mem hu
  · exact zero_mem _
  · intro u v _ _ hu hv
    exact add_mem hu hv
  · intro u _ hu
    exact neg_mem hu

/-- **Congruence on `p`-regular parts.** Let `f` be an `𝓞`-combination of characters and `y` a
power of `x` with `x^{p^k} = y^{p^k}`. If `f(x)` and `f(y)` are integers, they are congruent
modulo `p`. -/
theorem int_dvd_sub_of_pow_eq {f : G → ℂ} (hf : f ∈ virtualIntGroup G) {p : ℕ} (hp : p.Prime)
    (k : ℕ) {x y : G} (hy : y ∈ Subgroup.zpowers x) (hxy : x ^ p ^ k = y ^ p ^ k) {n n' : ℤ}
    (hn : f x = n) (hn' : f y = n') : (p : ℤ) ∣ n - n' := by
  have hres := restrict_mem_linearIntSpan hf x
  have h := (linearIntSpan_pow_congr hp k (x := ⟨x, Subgroup.mem_zpowers x⟩) (y := ⟨y, hy⟩)
    (Subtype.ext (by simpa using hxy)) hres).2.2
  have hmem : ((n ^ p ^ k - n' ^ p ^ k : ℤ) : ℂ) ∈ primeMultiples p := by
    push_cast
    rw [← hn, ← hn']
    exact h
  have h1 := int_dvd_of_mem_primeMultiples hp.ne_zero hmem
  have h2 := int_dvd_pow_prime_pow_sub hp k n
  have h3 := int_dvd_pow_prime_pow_sub hp k n'
  have e : n - n' = (n ^ p ^ k - n' ^ p ^ k) - (n ^ p ^ k - n) + (n' ^ p ^ k - n') := by ring
  rw [e]
  exact dvd_add (dvd_sub h1 h2) h3

end GaloisForLFunctions
