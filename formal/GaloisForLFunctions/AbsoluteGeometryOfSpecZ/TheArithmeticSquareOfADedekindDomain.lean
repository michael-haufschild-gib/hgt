import Mathlib

/-!
# The arithmetic square of a Dedekind domain

For a Dedekind domain `R` the Frobenius lifts are indexed by the nonzero ideals, and the
arithmetic square in ghost coordinates is the ring of families `(x_𝔞)`, `𝔞` a nonzero ideal, with

  `x_{𝔭𝔞} ≡ x_𝔞 (mod 𝔭^{k+1})` whenever `𝔭` is prime and `𝔭^k ∣ 𝔞`.

For `R = ℤ` and `𝔞 = (n)` these are the congruences of the ghost ring of the arithmetic square.
The component `x ↦ x_𝔞` is the graph `Γ_𝔞`, the diagonal is `Γ_1`, and `(F_𝔟 x)_𝔞 = x_{𝔟𝔞}`.

* **Contacts** (`idealContact_prime_pow`, `idealContact_eq_top_of_two_primes`): the diagonal and
  `Γ_{𝔭^j}` meet in `Spec R/𝔭`; the diagonal and `Γ_𝔞` do not meet when two primes divide `𝔞`. For a
  number ring the count of the fixed scheme of `F_{𝔭^j}` is `log N𝔭`, the von Mangoldt function of
  the Dedekind zeta function (`card_quotient_idealContact_prime_pow`).
* **Gluing** (`exists_isIdealGhost_one_prime_iff`): the diagonal and `Γ_𝔭` are glued along
  `R/𝔭`.
* **Necklace coordinates** (`exists_isIdealGhost_vanishing_iff`): the values at `𝔡` of the
  elements that vanish at the proper divisors of `𝔡` are exactly the elements of the ideal `𝔡`.
  The coordinate at `𝔡` is the module `𝔡`, of the class of `𝔡` in the class group.
* **Orbits and the class group** (`exists_idealOrbit_generator_iff`): an element that vanishes
  below `𝔡` and generates the coordinate at `𝔡`, the orbit `e_𝔡 = V_𝔡 1`, exists iff `𝔡` is
  principal. Over `ℤ` every orbit exists; in general the Verschiebung exists on the principal
  ideals only.

The proofs use one fact on divisibility: if `d ∣ p·a`, `d ∤ a` and `p^k ∣ a` for a prime `p`, then
`p^{k+1} ∣ d` (`pow_succ_dvd_of_dvd_mul_of_not_dvd`); so `π·[𝔡 ∣ 𝔞]` satisfies the congruences for
every `π ∈ 𝔡`.
-/

open nonZeroDivisors

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Divisibility by a prime power -/

/-- If `d` divides `p·a` and not `a`, and `p^k` divides `a`, then `p^{k+1}` divides `d`. -/
theorem pow_succ_dvd_of_dvd_mul_of_not_dvd {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    {p : α} (hp : Prime p) :
    ∀ (k : ℕ) {d a : α}, p ^ k ∣ a → d ∣ p * a → ¬ d ∣ a → p ^ (k + 1) ∣ d := by
  intro k
  induction k with
  | zero =>
    intro d a _ hd hn
    rw [zero_add, pow_one]
    exact (hp.left_dvd_or_dvd_right_of_dvd_mul hd).resolve_right hn
  | succ k ih =>
    intro d a hk hd hn
    obtain ⟨d', rfl⟩ := (hp.left_dvd_or_dvd_right_of_dvd_mul hd).resolve_right hn
    obtain ⟨a', rfl⟩ := (dvd_pow_self p (Nat.succ_ne_zero k)).trans hk
    have hk' : p ^ k ∣ a' := by
      rw [pow_succ'] at hk
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp hk
    have hd' : d' ∣ p * a' := (mul_dvd_mul_iff_left hp.ne_zero).mp hd
    have hn' : ¬ d' ∣ a' := fun h => hn (mul_dvd_mul_left p h)
    rw [pow_succ']
    exact mul_dvd_mul_left p (ih hk' hd' hn')

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- An element that lies in `p^k` whenever `p^k` divides the nonzero ideal `E` lies in `E`: a
nonzero ideal is the intersection of the prime powers that divide it. -/
theorem mem_of_forall_prime_pow {r : R} (E : Ideal R) (hE : E ≠ ⊥)
    (h : ∀ (p : Ideal R) (k : ℕ), Prime p → p ^ k ∣ E → r ∈ p ^ k) : r ∈ E := by
  revert hE h
  refine UniqueFactorizationMonoid.induction_on_coprime
    (P := fun E : Ideal R => E ≠ ⊥ →
      (∀ (p : Ideal R) (k : ℕ), Prime p → p ^ k ∣ E → r ∈ p ^ k) → r ∈ E) E ?_ ?_ ?_ ?_
  · intro h0
    exact absurd Ideal.zero_eq_bot h0
  · intro x hx _ _
    rw [Ideal.isUnit_iff.mp hx]
    exact Submodule.mem_top
  · intro p i hp _ h
    exact h p i hp dvd_rfl
  · intro x y hxy hx hy hne h
    have hx0 : x ≠ ⊥ := fun h0 => hne (by rw [h0, Ideal.bot_mul])
    have hy0 : y ≠ ⊥ := fun h0 => hne (by rw [h0, Ideal.mul_bot])
    have hrx := hx hx0 fun p k hp hk => h p k hp (hk.mul_right y)
    have hry := hy hy0 fun p k hp hk => h p k hp (hk.mul_left x)
    have hsup : x ⊔ y = ⊤ := Ideal.isUnit_iff.mp
      (hxy (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
    rw [Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr hsup)]
    exact ⟨hrx, hry⟩

/-! ### The square -/

/-- The congruences of the arithmetic square of `R`: `x_{𝔭𝔞} ≡ x_𝔞 (mod 𝔭^{k+1})` for `𝔭` prime
and `𝔭^k ∣ 𝔞`. -/
def IsIdealGhost (x : (Ideal R)⁰ → R) : Prop :=
  ∀ (P A : (Ideal R)⁰) (k : ℕ), (P : Ideal R).IsPrime → (P : Ideal R) ^ k ∣ (A : Ideal R) →
    x (P * A) - x A ∈ (P : Ideal R) ^ (k + 1)

variable (R) in
/-- The arithmetic square of `R` in ghost coordinates. -/
def idealGhostRing : Subring ((Ideal R)⁰ → R) where
  carrier := {x | IsIdealGhost x}
  mul_mem' := by
    intro x y hx hy P A k hP hk
    have e : (x * y) (P * A) - (x * y) A =
        x (P * A) * (y (P * A) - y A) + (x (P * A) - x A) * y A := by
      simp only [Pi.mul_apply]
      ring
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ (hy P A k hP hk))
      (Ideal.mul_mem_right _ _ (hx P A k hP hk))
  one_mem' := by
    intro P A k _ _
    simp
  add_mem' := by
    intro x y hx hy P A k hP hk
    have e : (x + y) (P * A) - (x + y) A = (x (P * A) - x A) + (y (P * A) - y A) := by
      simp only [Pi.add_apply]
      ring
    rw [e]
    exact add_mem (hx P A k hP hk) (hy P A k hP hk)
  zero_mem' := by
    intro P A k _ _
    simp
  neg_mem' := by
    intro x hx P A k hP hk
    have e : (-x) (P * A) - (-x) A = -(x (P * A) - x A) := by
      simp only [Pi.neg_apply]
      ring
    rw [e]
    exact neg_mem (hx P A k hP hk)

omit [IsDedekindDomain R] in
theorem isIdealGhost_const (a : R) : IsIdealGhost fun _ : (Ideal R)⁰ => a := by
  intro P A k _ _
  simp

/-- The Frobenius `F_𝔟`: `(F_𝔟 x)_𝔞 = x_{𝔟𝔞}`. -/
def idealFrobenius (B : (Ideal R)⁰) (x : (Ideal R)⁰ → R) : (Ideal R)⁰ → R := fun A => x (B * A)

omit [IsDedekindDomain R] in
theorem IsIdealGhost.frobenius {x : (Ideal R)⁰ → R} (hx : IsIdealGhost x) (B : (Ideal R)⁰) :
    IsIdealGhost (idealFrobenius B x) := by
  intro P A k hP hk
  have h := hx P (B * A) k hP (by
    rw [Submonoid.coe_mul]
    exact hk.mul_left _)
  rw [mul_left_comm] at h
  exact h

omit [IsDedekindDomain R] in
theorem idealFrobenius_idealFrobenius (B C : (Ideal R)⁰) (x : (Ideal R)⁰ → R) :
    idealFrobenius B (idealFrobenius C x) = idealFrobenius (C * B) x := by
  funext A
  simp only [idealFrobenius, mul_assoc]

/-! ### The elements `π·[𝔡 ∣ 𝔞]` -/

open Classical in
/-- The element `π·[𝔡 ∣ 𝔞]`. -/
noncomputable def idealOrbit (D : (Ideal R)⁰) (π : R) : (Ideal R)⁰ → R :=
  fun A => if (D : Ideal R) ∣ (A : Ideal R) then π else 0

omit [IsDedekindDomain R] in
theorem idealOrbit_of_dvd {D A : (Ideal R)⁰} {π : R} (h : (D : Ideal R) ∣ (A : Ideal R)) :
    idealOrbit D π A = π :=
  if_pos h

omit [IsDedekindDomain R] in
theorem idealOrbit_of_not_dvd {D A : (Ideal R)⁰} {π : R} (h : ¬ (D : Ideal R) ∣ (A : Ideal R)) :
    idealOrbit D π A = 0 :=
  if_neg h

/-- `π·[𝔡 ∣ 𝔞]` satisfies the congruences for every `π ∈ 𝔡`: where it jumps, from `𝔞` to `𝔭𝔞`, the
ideal `𝔡` is divisible by `𝔭^{k+1}`. -/
theorem isIdealGhost_idealOrbit {D : (Ideal R)⁰} {π : R} (hπ : π ∈ (D : Ideal R)) :
    IsIdealGhost (idealOrbit D π) := by
  intro P A k hP hk
  have hPp := Ideal.prime_of_isPrime (nonZeroDivisors.coe_ne_zero P) hP
  by_cases h1 : (D : Ideal R) ∣ (A : Ideal R)
  · have h2 : (D : Ideal R) ∣ ((P * A : (Ideal R)⁰) : Ideal R) := by
      rw [Submonoid.coe_mul]
      exact dvd_mul_of_dvd_right h1 _
    rw [idealOrbit_of_dvd h2, idealOrbit_of_dvd h1, sub_self]
    exact zero_mem _
  · by_cases h2 : (D : Ideal R) ∣ ((P * A : (Ideal R)⁰) : Ideal R)
    · rw [idealOrbit_of_dvd h2, idealOrbit_of_not_dvd h1, sub_zero]
      rw [Submonoid.coe_mul] at h2
      exact Ideal.dvd_iff_le.mp (pow_succ_dvd_of_dvd_mul_of_not_dvd hPp k hk h2 h1) hπ
    · rw [idealOrbit_of_not_dvd h2, idealOrbit_of_not_dvd h1, sub_self]
      exact zero_mem _

omit [IsDedekindDomain R] in
theorem not_dvd_one_of_isPrime (P : (Ideal R)⁰) (hP : (P : Ideal R).IsPrime) :
    ¬ (P : Ideal R) ∣ ((1 : (Ideal R)⁰) : Ideal R) := by
  intro h
  rw [Submonoid.coe_one] at h
  exact hP.ne_top (Ideal.isUnit_iff.mp (isUnit_of_dvd_one h))

/-! ### Contacts -/

omit [IsDedekindDomain R] in
/-- On the graph of a prime power an element agrees with its value on the diagonal modulo the
prime. -/
theorem IsIdealGhost.sub_mem_of_prime_pow {x : (Ideal R)⁰ → R} (hx : IsIdealGhost x)
    (P : (Ideal R)⁰) (hP : (P : Ideal R).IsPrime) (j : ℕ) : x (P ^ j) - x 1 ∈ (P : Ideal R) := by
  induction j with
  | zero =>
    rw [pow_zero, sub_self]
    exact zero_mem _
  | succ j ih =>
    have h := hx P (P ^ j) j hP (dvd_of_eq (SubmonoidClass.coe_pow P j).symm)
    have e : x (P ^ (j + 1)) - x 1 = (x (P * P ^ j) - x (P ^ j)) + (x (P ^ j) - x 1) := by
      rw [pow_succ']
      ring
    rw [e]
    exact add_mem (Ideal.pow_le_self (Nat.succ_ne_zero j) h) ih

/-- The ideal of the contact of the diagonal and the graph `Γ_𝔞`: generated by `x_𝔞 − x_1`. -/
def idealContact (A : (Ideal R)⁰) : Ideal R :=
  Ideal.span {r | ∃ x : (Ideal R)⁰ → R, IsIdealGhost x ∧ r = x A - x 1}

/-- **The graphs meet in the prime ideals.** The diagonal and `Γ_{𝔭^j}` meet in `Spec R/𝔭`. -/
theorem idealContact_prime_pow (P : (Ideal R)⁰) (hP : (P : Ideal R).IsPrime) {j : ℕ}
    (hj : j ≠ 0) : idealContact (P ^ j) = (P : Ideal R) := by
  apply le_antisymm
  · rw [idealContact, Ideal.span_le]
    rintro r ⟨x, hx, rfl⟩
    exact hx.sub_mem_of_prime_pow P hP j
  · intro π hπ
    refine Ideal.subset_span ⟨idealOrbit P π, isIdealGhost_idealOrbit hπ, ?_⟩
    have h2 : (P : Ideal R) ∣ ((P ^ j : (Ideal R)⁰) : Ideal R) := by
      rw [SubmonoidClass.coe_pow]
      exact dvd_pow_self _ hj
    rw [idealOrbit_of_dvd h2, idealOrbit_of_not_dvd (not_dvd_one_of_isPrime P hP), sub_zero]

/-- The diagonal does not meet the graph of an ideal divisible by two primes. -/
theorem idealContact_eq_top_of_two_primes {A P Q : (Ideal R)⁰} (hP : (P : Ideal R).IsPrime)
    (hQ : (Q : Ideal R).IsPrime) (hPQ : (P : Ideal R) ≠ Q) (hPA : (P : Ideal R) ∣ (A : Ideal R))
    (hQA : (Q : Ideal R) ∣ (A : Ideal R)) : idealContact A = ⊤ := by
  have hsup : (P : Ideal R) ⊔ Q = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne (hP.isMaximal (nonZeroDivisors.coe_ne_zero P))
      (hQ.isMaximal (nonZeroDivisors.coe_ne_zero Q)) hPQ
  have h1 : (1 : R) ∈ (P : Ideal R) ⊔ Q := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  refine Ideal.eq_top_of_isUnit_mem _
    (Ideal.subset_span ⟨idealOrbit P a + idealOrbit Q b, ?_, ?_⟩) isUnit_one
  · exact (idealGhostRing R).add_mem (isIdealGhost_idealOrbit ha) (isIdealGhost_idealOrbit hb)
  · rw [Pi.add_apply, Pi.add_apply, idealOrbit_of_dvd hPA, idealOrbit_of_dvd hQA,
      idealOrbit_of_not_dvd (not_dvd_one_of_isPrime P hP),
      idealOrbit_of_not_dvd (not_dvd_one_of_isPrime Q hQ), hab, add_zero, sub_zero]

/-- **The count of the fixed scheme over a number ring**: the contact of the diagonal and
`Γ_{𝔭^j}` has `N𝔭` points. -/
theorem card_quotient_idealContact_prime_pow [Module.Free ℤ R] (P : (Ideal R)⁰)
    (hP : (P : Ideal R).IsPrime) {j : ℕ} (hj : j ≠ 0) :
    Nat.card (R ⧸ idealContact (P ^ j)) = Ideal.absNorm (P : Ideal R) := by
  rw [idealContact_prime_pow P hP hj, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- **The diagonal and `Γ_𝔭` are glued along `R/𝔭`.** -/
theorem exists_isIdealGhost_one_prime_iff (P : (Ideal R)⁰) (hP : (P : Ideal R).IsPrime)
    (a b : R) :
    (∃ x : (Ideal R)⁰ → R, IsIdealGhost x ∧ x 1 = a ∧ x P = b) ↔ b - a ∈ (P : Ideal R) := by
  constructor
  · rintro ⟨x, hx, rfl, rfl⟩
    have h := hx P 1 0 hP (by
      rw [pow_zero]
      exact one_dvd _)
    rwa [mul_one, zero_add, pow_one] at h
  · intro h
    refine ⟨(fun _ => a) + idealOrbit P (b - a), ?_, ?_, ?_⟩
    · exact (idealGhostRing R).add_mem (isIdealGhost_const a) (isIdealGhost_idealOrbit h)
    · rw [Pi.add_apply, idealOrbit_of_not_dvd (not_dvd_one_of_isPrime P hP), add_zero]
    · rw [Pi.add_apply, idealOrbit_of_dvd dvd_rfl]
      ring

/-! ### Necklace coordinates -/

/-- An element of the square that vanishes at the proper divisors of `𝔡` has its value at `𝔡` in
the ideal `𝔡`. -/
theorem IsIdealGhost.mem_of_vanishing {x : (Ideal R)⁰ → R} (hx : IsIdealGhost x)
    (D : (Ideal R)⁰)
    (h0 : ∀ A : (Ideal R)⁰, (A : Ideal R) ∣ (D : Ideal R) → A ≠ D → x A = 0) :
    x D ∈ (D : Ideal R) := by
  refine mem_of_forall_prime_pow _ (nonZeroDivisors.coe_ne_zero D) fun p k hp hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨D', hD'⟩ := (dvd_pow_self p (Nat.succ_ne_zero k)).trans hk
  have hD0 : (D : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero D
  have hp0 : p ≠ 0 := hp.ne_zero
  have hD'0 : D' ≠ 0 := fun h => hD0 (by rw [hD', h, mul_zero])
  have hk' : p ^ k ∣ D' := by
    rw [hD', pow_succ'] at hk
    exact (mul_dvd_mul_iff_left hp0).mp hk
  have hPD : (⟨p, mem_nonZeroDivisors_iff_ne_zero.mpr hp0⟩ : (Ideal R)⁰) *
      ⟨D', mem_nonZeroDivisors_iff_ne_zero.mpr hD'0⟩ = D := Subtype.ext hD'.symm
  have hne : (⟨D', mem_nonZeroDivisors_iff_ne_zero.mpr hD'0⟩ : (Ideal R)⁰) ≠ D := by
    intro h
    have h' : p * D' = D' := hD'.symm.trans (congrArg Subtype.val h).symm
    have hp1 : p = 1 := mul_right_cancel₀ hD'0 (by rw [h', one_mul])
    exact hp.not_unit (hp1 ▸ isUnit_one)
  have hx0 := h0 ⟨D', mem_nonZeroDivisors_iff_ne_zero.mpr hD'0⟩ (Dvd.intro_left p hD'.symm) hne
  have hg := hx ⟨p, mem_nonZeroDivisors_iff_ne_zero.mpr hp0⟩
    ⟨D', mem_nonZeroDivisors_iff_ne_zero.mpr hD'0⟩ k (Ideal.isPrime_of_prime hp) hk'
  rw [hPD, hx0, sub_zero] at hg
  exact hg

/-- **The necklace coordinate at `𝔡` is the ideal `𝔡`.** The values at `𝔡` of the elements of the
square that vanish at the proper divisors of `𝔡` are exactly the elements of `𝔡`. -/
theorem exists_isIdealGhost_vanishing_iff (D : (Ideal R)⁰) (r : R) :
    (∃ x : (Ideal R)⁰ → R, IsIdealGhost x ∧
        (∀ A : (Ideal R)⁰, (A : Ideal R) ∣ (D : Ideal R) → A ≠ D → x A = 0) ∧ x D = r) ↔
      r ∈ (D : Ideal R) := by
  constructor
  · rintro ⟨x, hx, h0, rfl⟩
    exact hx.mem_of_vanishing D h0
  · intro hr
    exact ⟨idealOrbit D r, isIdealGhost_idealOrbit hr, fun A hA hne =>
      idealOrbit_of_not_dvd fun h => hne (Subtype.ext (dvd_antisymm hA h)),
      idealOrbit_of_dvd dvd_rfl⟩

/-- **An orbit exists iff the ideal is principal.** An element of the square that vanishes at the
proper divisors of `𝔡` and whose value at `𝔡` generates the coordinate exists iff `𝔡` is
principal. -/
theorem exists_idealOrbit_generator_iff (D : (Ideal R)⁰) :
    (∃ x : (Ideal R)⁰ → R, IsIdealGhost x ∧
        (∀ A : (Ideal R)⁰, (A : Ideal R) ∣ (D : Ideal R) → A ≠ D → x A = 0) ∧
        Ideal.span {x D} = (D : Ideal R)) ↔ (D : Ideal R).IsPrincipal := by
  constructor
  · rintro ⟨x, -, -, h⟩
    exact ⟨⟨x D, h.symm⟩⟩
  · rintro ⟨⟨π, hπ⟩⟩
    have hmem : π ∈ (D : Ideal R) := by
      rw [hπ]
      exact Submodule.mem_span_singleton_self π
    refine ⟨idealOrbit D π, isIdealGhost_idealOrbit hmem, fun A hA hne =>
      idealOrbit_of_not_dvd fun h => hne (Subtype.ext (dvd_antisymm hA h)), ?_⟩
    rw [idealOrbit_of_dvd dvd_rfl]
    exact hπ.symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
