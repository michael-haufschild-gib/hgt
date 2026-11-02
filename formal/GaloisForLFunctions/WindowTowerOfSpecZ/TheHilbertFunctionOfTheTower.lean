import GaloisForLFunctions.WindowTowerOfSpecZ.TheTowerOfSmallExtensions
import Mathlib.NumberTheory.AlmostPrime

/-!
# The Hilbert function of the tower

The window algebra `D_N = R/I_N` is local Artinian with maximal ideal `m = {f : f(1) = 0}`. Its
`m`-adic filtration is read off the number of prime factors `Ω(n)`:

* **The powers of the maximal ideal** (`mem_pow_sup_truncIdeal_iff`): `f ∈ m^k + I_N` iff `f(n) = 0`
  for every `n ≤ N` with fewer than `k` prime factors (counted with multiplicity). A product of `k`
  folds starts at an integer with at least `k` prime factors; conversely `δ_n = δ_p * δ_{n/p}` peels
  off one prime at a time (`single_mem_pow_truncIdeal_one`).
* **The associated graded algebra** (`sub_restrictTo_almostPrime_mem`, `restrictTo_almostPrime_mem_iff`):
  `m^k/(m^{k+1} + I_N)` has basis the `k`-almost primes `n ≤ N`. The Hilbert function of the window
  algebra is Landau's count `π_k(N) = #{n ≤ N : Ω(n) = k}`: the cotangent space (`k = 1`) counts the
  primes, the Loewy length is the largest `Ω` below `N`, `⌊log₂ N⌋ + 1`.
* **The socle** (`mul_mem_truncIdeal_forall_iff`): `f · m ⊆ I_N` iff `f(n) = 0` for `2n ≤ N`. The
  socle of `D_N` is spanned by the integers of `(N/2, N]`; its dimension (the type of the local ring)
  is `⌈N/2⌉`.
* **Gorenstein exactly before the second prime** (`socle_principal_iff`): the socle of `D_N` is
  principal — the window algebra is Gorenstein, i.e. carries a perfect pairing `(f, g) ↦ (f * g)(N)` —
  iff `N ≤ 2`, i.e. iff the window is shorter than `log 3`.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open scoped ArithmeticFunction.Omega

variable {R : Type*} [CommRing R]

/-! ### The `Ω`-filtration -/

/-- Functions vanishing at every `n` with fewer than `k` prime factors. -/
def omegaVanishing (k : ℕ) : Ideal (ArithmeticFunction R) where
  carrier := {f | ∀ n, n ≠ 0 → Ω n < k → f n = 0}
  add_mem' {f g} hf hg n hn hk := by rw [ArithmeticFunction.add_apply, hf n hn hk, hg n hn hk,
    add_zero]
  zero_mem' _ _ _ := rfl
  smul_mem' c f hf n hn hk := by
    rw [smul_eq_mul, ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have h1 : x.1 ≠ 0 := fun h => hn (by rw [← hxn, h, zero_mul])
    have h2 : x.2 ≠ 0 := fun h => hn (by rw [← hxn, h, mul_zero])
    have := ArithmeticFunction.cardFactors_mul h1 h2
    rw [hxn] at this
    rw [hf x.2 h2 (by omega), mul_zero]

/-- **A product of `k` folds starts at an integer with at least `k` prime factors**: `m^k` vanishes
below `Ω = k`. -/
theorem pow_truncIdeal_one_le_omegaVanishing (k : ℕ) :
    (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ k ≤ omegaVanishing k := by
  induction k with
  | zero => intro f _ n _ hk; omega
  | succ k ih =>
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun f hf g hg n hn hk => ?_
    rw [ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have h1 : x.1 ≠ 0 := fun h => hn (by rw [← hxn, h, zero_mul])
    have h2 : x.2 ≠ 0 := fun h => hn (by rw [← hxn, h, mul_zero])
    have hΩ := ArithmeticFunction.cardFactors_mul h1 h2
    rw [hxn] at hΩ
    by_cases hx2 : x.2 = 1
    · rw [hx2, mem_truncIdeal_one.mp hg, mul_zero]
    · have : 0 < Ω x.2 := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)
      rw [ih hf x.1 h1 (by omega), zero_mul]

/-- **Peeling off primes**: `δ_n ∈ m^k` whenever `n` has at least `k` prime factors. -/
theorem single_mem_pow_truncIdeal_one {k n : ℕ} (hn : n ≠ 0) (hk : k ≤ Ω n) (c : R) :
    single n c ∈ (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ k := by
  induction k generalizing n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ k ih =>
    have h1 : 1 < n := ArithmeticFunction.cardFactors_pos_iff_one_lt.mp (by omega)
    set p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hm0 : m ≠ 0 := fun h => hn (by rw [hm, h, mul_zero])
    have hΩ := ArithmeticFunction.cardFactors_mul hp.ne_zero hm0
    rw [← hm, ArithmeticFunction.cardFactors_apply_prime hp] at hΩ
    rw [hm, ← one_mul c, ← single_mul_single hp.ne_zero hm0, pow_succ']
    refine Ideal.mul_mem_mul (mem_truncIdeal_one.mpr ?_) (ih hm0 (by omega))
    rw [single_apply, if_neg fun h => hp.one_lt.ne h.1]

/-- Functions supported on integers with at least `k` prime factors lie in `m^k`. -/
theorem restrictTo_mem_pow {k : ℕ} {C : Finset ℕ} (hC : ∀ n ∈ C, n ≠ 0 → k ≤ Ω n)
    (f : ArithmeticFunction R) :
    restrictTo C f ∈ (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ k := by
  induction C using Finset.induction_on with
  | empty =>
    have : restrictTo (∅ : Finset ℕ) f = 0 := by ext n; simp [restrictTo_apply]
    rw [this]; exact Submodule.zero_mem _
  | insert n C hnC ih =>
    have hsplit : restrictTo (insert n C) f =
        restrictTo {n} f + restrictTo C f := by
      ext j
      rw [ArithmeticFunction.add_apply, restrictTo_apply, restrictTo_apply, restrictTo_apply]
      by_cases hj : j = n
      · subst hj; simp [hnC]
      · simp [hj]
    rw [hsplit]
    refine Submodule.add_mem _ ?_ (ih fun m hm => hC m (Finset.mem_insert_of_mem hm))
    by_cases hn : n = 0
    · have : restrictTo {n} f = 0 := by ext j; simp [restrictTo_apply, hn]
      rw [this]; exact Submodule.zero_mem _
    · have : restrictTo {n} f = single n (f n) := by
        ext j
        rw [restrictTo_apply, single_apply]
        by_cases hj : j = n
        · subst hj; simp [hn]
        · simp [hj]
      rw [this]
      exact single_mem_pow_truncIdeal_one hn (hC n (Finset.mem_insert_self n C) hn) _

/-- The integers `≤ N` with at least `k` prime factors. -/
def omegaAtLeast (k N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter fun n => k ≤ Ω n

theorem mem_omegaAtLeast {k N n : ℕ} : n ∈ omegaAtLeast k N ↔ n ∈ Finset.Icc 1 N ∧ k ≤ Ω n :=
  Finset.mem_filter

/-- **The powers of the maximal ideal of the window algebra**: `f ∈ m^k + I_N` iff `f(n) = 0` for every
`n ≤ N` with fewer than `k` prime factors. -/
theorem mem_pow_sup_truncIdeal_iff {k N : ℕ} {f : ArithmeticFunction R} :
    f ∈ (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ k ⊔ truncIdeal N ↔
      ∀ n, 1 ≤ n → n ≤ N → Ω n < k → f n = 0 := by
  constructor
  · intro h n h1 hN hk
    obtain ⟨g, hg, t, ht, rfl⟩ := Submodule.mem_sup.mp h
    rw [ArithmeticFunction.add_apply, pow_truncIdeal_one_le_omegaVanishing k hg n (by omega) hk,
      ht n h1 hN, add_zero]
  · intro h
    refine Submodule.mem_sup.mpr ⟨restrictTo (omegaAtLeast k N) f,
      restrictTo_mem_pow (fun n hn _ => (mem_omegaAtLeast.mp hn).2) f,
      f - restrictTo (omegaAtLeast k N) f, fun n h1 hn => ?_, add_sub_cancel _ _⟩
    rw [sub_apply', restrictTo_apply]
    by_cases hk : k ≤ Ω n
    · rw [if_pos ⟨mem_omegaAtLeast.mpr ⟨Finset.mem_Icc.mpr ⟨h1, hn⟩, hk⟩, by omega⟩, sub_self]
    · rw [if_neg fun h' => hk (mem_omegaAtLeast.mp h'.1).2, sub_zero]
      exact h n h1 hn (by omega)

/-! ### The associated graded algebra: almost primes -/

/-- The `k`-almost primes `≤ N`. -/
def almostPrimesUpTo (k N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter fun n => Ω n = k

theorem mem_almostPrimesUpTo {k N n : ℕ} :
    n ∈ almostPrimesUpTo k N ↔ n ∈ Finset.Icc 1 N ∧ Ω n = k :=
  Finset.mem_filter

/-- **The `k`-almost primes span `gr_k`**: every `f ∈ m^k + I_N` is congruent modulo `m^{k+1} + I_N`
to its restriction to the `k`-almost primes `≤ N`. -/
theorem sub_restrictTo_almostPrime_mem {k N : ℕ} {f : ArithmeticFunction R}
    (hf : f ∈ (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ k ⊔ truncIdeal N) :
    f - restrictTo (almostPrimesUpTo k N) f ∈
      (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ (k + 1) ⊔ truncIdeal N := by
  have hf' := mem_pow_sup_truncIdeal_iff.mp hf
  refine mem_pow_sup_truncIdeal_iff.mpr fun n h1 hN hk => ?_
  rw [sub_apply', restrictTo_apply]
  by_cases hnk : Ω n = k
  · rw [if_pos ⟨mem_almostPrimesUpTo.mpr ⟨Finset.mem_Icc.mpr ⟨h1, hN⟩, hnk⟩, by omega⟩, sub_self]
  · rw [if_neg fun h' => hnk (mem_almostPrimesUpTo.mp h'.1).2, sub_zero]
    exact hf' n h1 hN (by omega)

/-- **The `k`-almost primes are independent in `gr_k`**: a function supported on the `k`-almost primes
`≤ N` lies in `m^{k+1} + I_N` only if it vanishes there. The Hilbert function of the window algebra is
`π_k(N) = #{n ≤ N : Ω(n) = k}`. -/
theorem restrictTo_almostPrime_mem_iff {k N : ℕ} {f : ArithmeticFunction R} :
    restrictTo (almostPrimesUpTo k N) f ∈
        (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ (k + 1) ⊔ truncIdeal N ↔
      ∀ n ∈ almostPrimesUpTo k N, f n = 0 := by
  rw [mem_pow_sup_truncIdeal_iff]
  constructor
  · intro h n hn
    obtain ⟨hn1, hnk⟩ := mem_almostPrimesUpTo.mp hn
    obtain ⟨h1, hN⟩ := Finset.mem_Icc.mp hn1
    have := h n h1 hN (by omega)
    rwa [restrictTo_apply, if_pos ⟨hn, by omega⟩] at this
  · intro h n _ _ _
    rw [restrictTo_apply]
    split_ifs with hn
    · exact h n hn.1
    · rfl

/-! ### The socle -/

theorem mul_single_two_apply (f : ArithmeticFunction R) (n : ℕ) :
    (f * single 2 (1 : R)) (2 * n) = f n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply, Finset.sum_eq_single (n, 2)]
  · rw [single_apply_self two_ne_zero, mul_one]
  · intro x hx hxn
    obtain ⟨hx2, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    rw [single_apply]
    split_ifs with h
    · exfalso
      refine hxn (Prod.ext ?_ h.1)
      rw [h.1] at hx2
      change x.1 = n
      omega
    · rw [mul_zero]
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_comm n 2, by omega⟩) h

/-- **The socle of the window algebra**: `f · m ⊆ I_N` iff `f` vanishes on `1 ≤ n ≤ N/2`. -/
theorem mul_mem_truncIdeal_forall_iff {N : ℕ} {f : ArithmeticFunction R} :
    (∀ g ∈ (truncIdeal 1 : Ideal (ArithmeticFunction R)), f * g ∈ truncIdeal N) ↔
      ∀ n, 1 ≤ n → 2 * n ≤ N → f n = 0 := by
  constructor
  · intro h n h1 hn
    have hg : single 2 (1 : R) ∈ (truncIdeal 1 : Ideal (ArithmeticFunction R)) :=
      mem_truncIdeal_one.mpr (by
      rw [single_apply, if_neg fun h => by omega])
    have := h _ hg (2 * n) (by omega) hn
    rwa [mul_single_two_apply] at this
  · intro h g hg
    have hf : f ∈ truncIdeal (N / 2) := fun n h1 hn => h n h1 (by omega)
    exact truncIdeal_anti (by omega) (mul_mem_truncIdeal hf hg)

variable {K : Type*} [Field K]

/-- **The window algebra is Gorenstein exactly before the second prime**: its socle is principal
modulo `I_N` iff `N ≤ 2`. -/
theorem socle_principal_iff (N : ℕ) :
    (∃ s : ArithmeticFunction K, ∀ f : ArithmeticFunction K,
        (∀ g ∈ (truncIdeal 1 : Ideal (ArithmeticFunction K)), f * g ∈ truncIdeal N) →
          ∃ c : K, f - single 1 c * s ∈ truncIdeal N) ↔ N ≤ 2 := by
  have hsoc : ∀ n, n ≤ N → N < 2 * n → ∀ g ∈ (truncIdeal 1 : Ideal (ArithmeticFunction K)),
      single n (1 : K) * g ∈ truncIdeal N := fun n hnN hn =>
    mul_mem_truncIdeal_forall_iff.mpr fun j h1 hj => by
      rw [single_apply, if_neg fun h => by omega]
  have hsc : ∀ (c : K) (s : ArithmeticFunction K) (n : ℕ), (single 1 c * s) n = c * s n := by
    intro c s n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [ArithmeticFunction.mul_apply, Finset.sum_eq_single (1, n)]
    · rw [single_apply_self one_ne_zero]
    · intro x hx hx1
      rw [single_apply, if_neg, zero_mul]
      rintro ⟨h1, -⟩
      obtain ⟨hxn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      exact hx1 (Prod.ext h1 (by rw [h1, one_mul] at hxn; exact hxn))
    · intro h; exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, by omega⟩) h
  constructor
  · rintro ⟨s, hs⟩
    by_contra hN
    push Not at hN
    -- `δ_N` and `δ_{N−1}` both lie in the socle and are independent
    obtain ⟨c₁, h₁⟩ := hs _ (hsoc N le_rfl (by omega))
    obtain ⟨c₂, h₂⟩ := hs _ (hsoc (N - 1) (by omega) (by omega))
    have e₁ := h₁ N (by omega) le_rfl
    have e₁' := h₁ (N - 1) (by omega) (by omega)
    have e₂ := h₂ N (by omega) le_rfl
    have e₂' := h₂ (N - 1) (by omega) (by omega)
    simp only [sub_apply', hsc, single_apply_self (show N ≠ 0 by omega),
      single_apply_self (show N - 1 ≠ 0 by omega)] at e₁ e₁' e₂ e₂'
    rw [single_apply, if_neg fun h => by omega] at e₁' e₂
    -- `1 = c₁ s(N)`, `0 = c₁ s(N−1)`, `0 = c₂ s(N)`, `1 = c₂ s(N−1)`
    have ha : c₁ * s N = 1 := by linear_combination -e₁
    have hb : c₂ * s (N - 1) = 1 := by linear_combination -e₂'
    have hc : c₁ * s (N - 1) = 0 := by linear_combination -e₁'
    have hc₁ : c₁ ≠ 0 := left_ne_zero_of_mul_eq_one ha
    have hs1 : s (N - 1) = 0 := (mul_eq_zero.mp hc).resolve_left hc₁
    rw [hs1, mul_zero] at hb
    exact zero_ne_one hb
  · intro hN
    refine ⟨single N 1, fun f hf => ⟨f N, fun n h1 hn => ?_⟩⟩
    rw [sub_apply', hsc, single_apply]
    by_cases hnN : n = N
    · subst hnN; simp [show n ≠ 0 by omega]
    · rw [if_neg fun h => hnN h.1, mul_zero, sub_zero]
      exact mul_mem_truncIdeal_forall_iff.mp hf n h1 (by omega)

end GaloisForLFunctions.WindowTowerOfSpecZ
