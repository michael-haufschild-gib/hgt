import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellRamificationPower

/-!
# Support geometry of a ramification power event

The level-`r m` shell partitions into the image of the level-`m` shell under `k ↦ k^r` and a
strict excess:

`A_{rm} = P_r(A_m) ⊔ X_{m,r}`,   `X_{m,r} = {N ∈ A_{rm} : N is not an r-th power}`.

For composable power events the excess supports satisfy the canonical partition

`X_{m,sr} = X_{rm,s} ⊔ P_s(X_{m,r})`,

because a valuation vector that is nonzero modulo `s r` is either nonzero modulo `s` or is `s`
times a vector nonzero modulo `r`.  Every element of an excess support carries at least two prime
species: a prime power `p^{rm}` is always `(p^m)^r`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open RHTower

/-! ## Composition of perfect-power predicates -/

theorem isRPow_of_isRPow_mul {s r N : ℕ} (h : IsRPow (s * r) N) : IsRPow s N := by
  obtain ⟨L, rfl⟩ := h
  exact ⟨L ^ r, by rw [← pow_mul, mul_comm r s]⟩

theorem isRPow_mul_iff_of_pow {s r K N : ℕ} (hs : s ≠ 0) (hKN : K ^ s = N) :
    IsRPow (s * r) N ↔ IsRPow r K := by
  constructor
  · rintro ⟨L, hL⟩
    have hLs : (L ^ r) ^ s = K ^ s := by
      rw [← pow_mul, mul_comm r s, hL, hKN]
    exact ⟨L, Nat.pow_left_injective hs hLs⟩
  · rintro ⟨L, rfl⟩
    exact ⟨L, by rw [← hKN, ← pow_mul, mul_comm r s]⟩

/-! ## The three supports -/

/-- The level-`m` shell support. -/
def shellSupport (m : ℕ) : Set ℕ := {n | shellIndicator m n = 1}

/-- The image of the level-`m` shell under `k ↦ k^r`. -/
def powerImageSupport (m r : ℕ) : Set ℕ := {N | shellIndicator (r * m) N = 1 ∧ IsRPow r N}

/-- The strict excess of a power event. -/
def excessSupport (m r : ℕ) : Set ℕ := {N | shellIndicator (r * m) N = 1 ∧ ¬ IsRPow r N}

theorem shellSupport_mul_eq_union (m r : ℕ) :
    shellSupport (r * m) = powerImageSupport m r ∪ excessSupport m r := by
  ext N
  by_cases h : IsRPow r N <;> simp [shellSupport, powerImageSupport, excessSupport, h]

theorem powerImageSupport_disjoint_excessSupport (m r : ℕ) :
    Disjoint (powerImageSupport m r) (excessSupport m r) := by
  rw [Set.disjoint_left]
  rintro N ⟨-, h⟩ ⟨-, h'⟩
  exact h' h

/-- **The power image is the shell image.** -/
theorem powerImageSupport_eq_image {m r : ℕ} (hr : r ≠ 0) :
    powerImageSupport m r = (fun k => k ^ r) '' shellSupport m := by
  ext N
  constructor
  · rintro ⟨hN, k, rfl⟩
    exact ⟨k, by rwa [shellSupport, Set.mem_setOf_eq, ← shellIndicator_pow hr k], rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨by rw [shellIndicator_pow hr k]; exact hk, isRPow_pow r k⟩

/-! ## The canonical excess partition -/

/-- **Canonical excess partition.**  `X_{m,sr} = X_{rm,s} ⊔ P_s(X_{m,r})`. -/
theorem excessSupport_mul_eq_union {m r s : ℕ} (hs : s ≠ 0) :
    excessSupport m (s * r) = excessSupport (r * m) s ∪ (fun k => k ^ s) '' excessSupport m r := by
  ext N
  constructor
  · rintro ⟨hN, hnot⟩
    have hshell : shellIndicator (s * (r * m)) N = 1 := by
      rwa [← mul_assoc]
    by_cases hs' : IsRPow s N
    · refine Or.inr ?_
      obtain ⟨K, rfl⟩ := hs'
      refine ⟨K, ⟨?_, ?_⟩, rfl⟩
      · rwa [← shellIndicator_pow (m := r * m) hs K]
      · exact fun hK => hnot ((isRPow_mul_iff_of_pow hs rfl).mpr hK)
    · exact Or.inl ⟨hshell, hs'⟩
  · rintro (⟨hN, hnot⟩ | ⟨K, ⟨hK, hKnot⟩, rfl⟩)
    · refine ⟨by rwa [mul_assoc], fun h => hnot (isRPow_of_isRPow_mul h)⟩
    · refine ⟨?_, ?_⟩
      · rw [mul_assoc, shellIndicator_pow hs K]
        exact hK
      · exact fun h => hKnot ((isRPow_mul_iff_of_pow hs rfl).mp h)

theorem excessSupport_disjoint_image {m r s : ℕ} :
    Disjoint (excessSupport (r * m) s) ((fun k => k ^ s) '' excessSupport m r) := by
  rw [Set.disjoint_left]
  rintro N ⟨-, hnot⟩ ⟨K, -, rfl⟩
  exact hnot (isRPow_pow s K)

/-! ## Minimal prime arity of a complement detector -/

/-- **Two prime species are necessary.**  A prime power in the level-`r m` shell is always an
`r`-th power, so every excess element has at least two distinct prime factors. -/
theorem excessSupport_not_prime_pow {m r N p : ℕ} (hm : m ≠ 0) (hr : r ≠ 0) (hp : p.Prime)
    (hN : N ∈ excessSupport m r) (e : ℕ) : N ≠ p ^ e := by
  rintro rfl
  obtain ⟨hshell, hnot⟩ := hN
  have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  obtain ⟨hfree, hnotfree⟩ := (shellIndicator_eq_one_iff (r * m) (p ^ e)).mp hshell
  have hfac : ∀ q : ℕ, q.Prime → (p ^ e).factorization q < r * m + 1 :=
    (mFree_iff_forall_factorization_lt hne).mp hfree
  have hexists : ¬ ∀ q : ℕ, q.Prime → (p ^ e).factorization q < r * m :=
    fun h => hnotfree ((mFree_iff_forall_factorization_lt hne).mpr h)
  have hpe : (p ^ e).factorization p = e := by
    rw [Nat.factorization_pow, hp.factorization]
    simp
  have hother : ∀ q : ℕ, q.Prime → q ≠ p → (p ^ e).factorization q = 0 := by
    intro q hq hqp
    rw [Nat.factorization_pow, hp.factorization]
    simp [hqp]
  have he : e = r * m := by
    by_contra hne'
    refine hexists fun q hq => ?_
    by_cases hqp : q = p
    · rw [hqp, hpe]
      have h1 := hfac p hp
      rw [hpe] at h1
      omega
    · rw [hother q hq hqp]
      exact Nat.pos_of_ne_zero (Nat.mul_ne_zero hr hm)
  exact hnot ⟨p ^ m, by rw [← pow_mul, he, mul_comm]⟩

end HTGeometry.ConstraintFrameRelativity
