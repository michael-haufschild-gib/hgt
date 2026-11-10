import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheArithmeticSquareIsCofree

/-!
# A finite fibre forces contacts

In the arithmetic square the graphs `Γ_m`, `Γ_n` meet at a prime `p` only if `n/m` is a power of
`p`. So the graphs of degree prime to `p` have pairwise distinct reductions modulo `p`: the fibre
of the square over `p` has infinitely many rational points. An object of finite type has finitely
many, and a count of sections that is bilinear in two degrees is a count of polynomials in
finitely many functions. This file proves that the two are incompatible.

* **The fibre of the square** (`graphIdeal_not_le_span_of_not_dvd`,
  `infinite_ringHom_ghostRing_zmod`): for `m ≠ n` prime to `p` the contact ideal `J(m, n)` is not
  contained in `(p)`, and `𝒢` has infinitely many ring homomorphisms to `𝔽_p`.
* **Pigeonhole** (`exists_ne_forall_dvd_sub_of_finite`, `exists_ne_forall_dvd_sub_of_card_lt`):
  if a ring `R` has finitely many `𝔽_p`-points, then among infinitely many `ℤ`-points of `R`, or
  among more of them than `R` has `𝔽_p`-points, two agree modulo `p` on all of `R`.
* **No object with a finite fibre carries the contacts of the square**
  (`FrobeniusLifts.exists_contact_not_in_square`): a ring with Frobenius lifts, a `ℤ`-point and
  finitely many `𝔽_p`-points has two graphs of distinct degrees prime to `p` that meet at `p`. In
  the square these two graphs do not meet at `p`.
* **Finite type** (`finite_ringHom_mvPolynomial_zmod`, `card_ringHom_mvPolynomial_zmod_le`,
  `finite_ringHom_zmod_of_surjective`): a quotient of `ℤ[u_1, …, u_k]` has at most `p^k` points
  over `𝔽_p`.

So an object that carries the contacts of the square has an infinite fibre over every prime; it is
not of finite type. On every object of finite type, the toric surface of a base among them, the
graphs have contacts at every prime beyond those of the square, among any `p^k + 1` of them.
-/

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The fibre of the square over a prime -/

/-- The reduction modulo `p` of a `ℤ`-point. -/
def reduce (p : ℕ) {R : Type*} [CommRing R] (r : R →+* ℤ) : R →+* ZMod p :=
  (Int.castRingHom (ZMod p)).comp r

theorem reduce_eq_iff (p : ℕ) {R : Type*} [CommRing R] (r s : R →+* ℤ) :
    reduce p r = reduce p s ↔ ∀ x : R, (p : ℤ) ∣ r x - s x := by
  constructor
  · intro h x
    have hx : ((s x : ℤ) : ZMod p) = ((r x : ℤ) : ZMod p) := (RingHom.congr_fun h x).symm
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hx
  · intro h
    ext x
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h x)).symm

/-- **Graphs of distinct degrees prime to `p` do not meet at `p`.** -/
theorem graphIdeal_not_le_span_of_not_dvd {m n : ℕ+} (hmn : m ≠ n) {p : ℕ} (hp : p.Prime)
    (hm : ¬ p ∣ (m : ℕ)) (hn : ¬ p ∣ (n : ℕ)) : ¬ graphIdeal m n ≤ Ideal.span {(p : ℤ)} := by
  intro hle
  obtain ⟨r, hr, hne⟩ := exists_prime_factorization_ne hmn
  obtain ⟨a, ha⟩ := exists_prime_pow_mem_graphIdeal hr hne
  have hpr : p ≠ r := by
    rintro rfl
    rw [Nat.factorization_eq_zero_of_not_dvd hm, Nat.factorization_eq_zero_of_not_dvd hn] at hne
    exact hne rfl
  have hmem := hle ha
  rw [Ideal.mem_span_singleton] at hmem
  have h1 : p ∣ r ^ a := by exact_mod_cast hmem
  exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h1))

theorem not_dvd_mul_add_one {p : ℕ} (hp : p.Prime) (k : ℕ) : ¬ p ∣ p * k + 1 := fun h =>
  hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right p k)).mp h))

/-- **The fibre of the arithmetic square over `p` has infinitely many rational points.** -/
theorem infinite_ringHom_ghostRing_zmod {p : ℕ} (hp : p.Prime) :
    Infinite (ghostRing →+* ZMod p) := by
  refine Infinite.of_injective
    (fun k : ℕ => reduce p (ghostComponent (Nat.succPNat (p * k)))) fun k l hkl => ?_
  by_contra hne
  have hmn : Nat.succPNat (p * k) ≠ Nat.succPNat (p * l) := fun h =>
    hne (Nat.eq_of_mul_eq_mul_left hp.pos (Nat.succPNat_injective h))
  refine graphIdeal_not_le_span_of_not_dvd hmn hp (not_dvd_mul_add_one hp k)
    (not_dvd_mul_add_one hp l) ?_
  rw [graphIdeal, Ideal.span_le]
  rintro _ ⟨x, rfl⟩
  exact Ideal.mem_span_singleton.mpr ((reduce_eq_iff p _ _).mp hkl x)

/-! ### Pigeonhole on a finite fibre -/

/-- Among infinitely many `ℤ`-points of a ring with finitely many `𝔽_p`-points, two agree
modulo `p`. -/
theorem exists_ne_forall_dvd_sub_of_finite {R : Type*} [CommRing R] (p : ℕ)
    [Finite (R →+* ZMod p)] {ι : Type*} [Infinite ι] (r : ι → (R →+* ℤ)) :
    ∃ i j : ι, i ≠ j ∧ ∀ x : R, (p : ℤ) ∣ r i x - r j x := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite fun i => reduce p (r i)
  exact ⟨i, j, hij, (reduce_eq_iff p _ _).mp h⟩

/-- Among more `ℤ`-points than the ring has `𝔽_p`-points, two agree modulo `p`. -/
theorem exists_ne_forall_dvd_sub_of_card_lt {R : Type*} [CommRing R] (p : ℕ)
    [Finite (R →+* ZMod p)] {ι : Type*} [Finite ι] (r : ι → (R →+* ℤ))
    (h : Nat.card (R →+* ZMod p) < Nat.card ι) :
    ∃ i j : ι, i ≠ j ∧ ∀ x : R, (p : ℤ) ∣ r i x - r j x := by
  haveI := Fintype.ofFinite ι
  haveI := Fintype.ofFinite (R →+* ZMod p)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  obtain ⟨i, j, hij, hr⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => reduce p (r i)) h
  exact ⟨i, j, hij, (reduce_eq_iff p _ _).mp hr⟩

/-- **No object with a finite fibre carries the contacts of the square.** A ring with Frobenius
lifts, a `ℤ`-point and finitely many `𝔽_p`-points has two graphs of distinct degrees that meet at
`p`, while the corresponding graphs of the arithmetic square do not. -/
theorem FrobeniusLifts.exists_contact_not_in_square {A : Type*} [CommRing A]
    (L : FrobeniusLifts A) (f : A →+* ℤ) {p : ℕ} (hp : p.Prime) [Finite (A →+* ZMod p)] :
    ∃ m n : ℕ+, m ≠ n ∧ (∀ a : A, (p : ℤ) ∣ f (L.ψ m a) - f (L.ψ n a)) ∧
      ¬ graphIdeal m n ≤ Ideal.span {(p : ℤ)} := by
  obtain ⟨k, l, hkl, h⟩ := exists_ne_forall_dvd_sub_of_finite p
    fun k : ℕ => f.comp (L.ψ (Nat.succPNat (p * k)))
  have hmn : Nat.succPNat (p * k) ≠ Nat.succPNat (p * l) := fun he =>
    hkl (Nat.eq_of_mul_eq_mul_left hp.pos (Nat.succPNat_injective he))
  exact ⟨Nat.succPNat (p * k), Nat.succPNat (p * l), hmn, h,
    graphIdeal_not_le_span_of_not_dvd hmn hp (not_dvd_mul_add_one hp k)
      (not_dvd_mul_add_one hp l)⟩

/-! ### Objects of finite type -/

/-- A point of affine space over `𝔽_p` is determined by its coordinates. -/
theorem ringHom_mvPolynomial_zmod_injective (σ : Type*) (p : ℕ) :
    Function.Injective fun (g : MvPolynomial σ ℤ →+* ZMod p) (i : σ) => g (MvPolynomial.X i) := by
  intro g h hgh
  refine MvPolynomial.ringHom_ext (fun z => ?_) fun i => congrFun hgh i
  exact RingHom.congr_fun (RingHom.ext_int (g.comp MvPolynomial.C) (h.comp MvPolynomial.C)) z

/-- Affine space of finite dimension has finitely many points over `𝔽_p`. -/
instance finite_ringHom_mvPolynomial_zmod (σ : Type*) [Finite σ] (p : ℕ) [NeZero p] :
    Finite (MvPolynomial σ ℤ →+* ZMod p) :=
  Finite.of_injective _ (ringHom_mvPolynomial_zmod_injective σ p)

/-- Affine space of dimension `k` has at most `p^k` points over `𝔽_p`. -/
theorem card_ringHom_mvPolynomial_zmod_le (k p : ℕ) [NeZero p] :
    Nat.card (MvPolynomial (Fin k) ℤ →+* ZMod p) ≤ p ^ k := by
  have h := Nat.card_le_card_of_injective _ (ringHom_mvPolynomial_zmod_injective (Fin k) p)
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h

/-- A quotient has no more points than the ring it is a quotient of. -/
theorem finite_ringHom_zmod_of_surjective {A B : Type*} [CommRing A] [CommRing B] (π : A →+* B)
    (hπ : Function.Surjective π) (p : ℕ) [Finite (A →+* ZMod p)] : Finite (B →+* ZMod p) :=
  Finite.of_injective (fun g : B →+* ZMod p => g.comp π) fun _ _ h =>
    (RingHom.cancel_right hπ).mp h

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
