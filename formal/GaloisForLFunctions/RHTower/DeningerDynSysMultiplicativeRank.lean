/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 4.3 (`t3`).

The dimension input for Lemma 4.3: for an algebraically closed field `C` with `C^× ≠ μ(C)` one has
`#C ≤ dim_ℚ (C^× / μ(C))`.

The mechanism is uniform in the characteristic.  A family of pairwise non-associate primes of a
subring of `C` is multiplicatively independent modulo roots of unity, because a relation between
their images, raised to the order of the root of unity it produces, descends to an equality of two
products of prime powers inside the subring.  Infinitely many such primes are available:

* in characteristic zero the rational primes, inside `ℤ ⊆ C`;
* in characteristic `p` the monic irreducible polynomials of `𝔽_p[X]`, evaluated at a unit which is
  not a root of unity — such a unit is transcendental over the prime field, since an element
  algebraic over `𝔽_p` generates a finite field and is therefore a root of unity.

Euclid's argument for the infinitude of monic irreducible polynomials over an arbitrary field is
proved here as well; it does not seem to be in mathlib.
-/
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Rat.Denumerable
import GaloisForLFunctions.RHTower.DeningerDynSysUnitClassSpace

namespace RHTower

open Cardinal IntermediateField

/-! ### Non-associate primes -/

/-- Two products of powers of pairwise non-associate primes agree only if the exponents do. -/
theorem deningerPrimePow_inj {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (π : ι → R) (hp : ∀ i, Prime (π i)) (hne : ∀ i j, i ≠ j → ¬ Associated (π i) (π j))
    (s : Finset ι) (a b : ι → ℕ)
    (h : ∏ i ∈ s, π i ^ a i = ∏ i ∈ s, π i ^ b i) : ∀ i ∈ s, a i = b i := by
  classical
  have key : ∀ (c : ι → ℕ) (j : ι), j ∈ s → ¬ (π j ^ (c j + 1) ∣ ∏ i ∈ s, π i ^ c i) := by
    intro c j hj hdvd
    rw [← Finset.prod_erase_mul s (fun i => π i ^ c i) hj] at hdvd
    rw [pow_succ] at hdvd
    have hdvd' : π j ^ c j * π j ∣ π j ^ c j * ∏ i ∈ s.erase j, π i ^ c i := by
      rw [mul_comm (π j ^ c j) (∏ i ∈ s.erase j, π i ^ c i)]
      exact hdvd
    have hne0 : (π j ^ c j) ≠ 0 := pow_ne_zero _ (hp j).ne_zero
    have hdj : π j ∣ ∏ i ∈ s.erase j, π i ^ c i :=
      (mul_dvd_mul_iff_left hne0).1 hdvd'
    obtain ⟨i, hi, hdi⟩ := ((hp j).dvd_finsetProd_iff _).1 hdj
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    exact hne j i (Ne.symm hij) ((hp j).associated_of_dvd (hp i) ((hp j).dvd_of_dvd_pow hdi))
  intro j hj
  by_contra hab
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · refine key a j hj ?_
    rw [h]
    exact dvd_trans (pow_dvd_pow (π j) hlt) (Finset.dvd_prod_of_mem (fun i => π i ^ b i) hj)
  · refine key b j hj ?_
    rw [← h]
    exact dvd_trans (pow_dvd_pow (π j) hlt) (Finset.dvd_prod_of_mem (fun i => π i ^ a i) hj)

/-- **Multiplicative independence modulo roots of unity.**  The images in a field of pairwise
non-associate primes of a subring have no nontrivial multiplicative relation modulo roots of
unity. -/
theorem deningerPrimeImage_independent {C : Type*} [Field C] {R : Type*} [CommRing R] [IsDomain R]
    (φ : R →+* C) (hφ : Function.Injective φ) {ι : Type*}
    (π : ι → R) (hp : ∀ i, Prime (π i)) (hne : ∀ i j, i ≠ j → ¬ Associated (π i) (π j))
    (u : ι → Cˣ) (hu : ∀ i, (u i : C) = φ (π i)) :
    ∀ (s : Finset ι) (n : ι → ℤ), (∏ i ∈ s, u i ^ n i) ∈ CommGroup.torsion Cˣ →
      ∀ i ∈ s, n i = 0 := by
  classical
  intro s n hmem i hi
  obtain ⟨N, hN, hNpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion _).1 hmem)
  set m : ι → ℤ := fun j => n j * (N : ℤ) with hm
  have hprod : ∏ j ∈ s, u j ^ m j = 1 := by
    have hstep : ∀ j ∈ s, u j ^ m j = (u j ^ n j) ^ N := by
      intro j _
      show u j ^ (n j * (N : ℤ)) = (u j ^ n j) ^ N
      rw [zpow_mul, zpow_natCast]
    rw [Finset.prod_congr rfl hstep, Finset.prod_pow, hNpow]
  set a : ι → ℕ := fun j => (m j).toNat with ha
  set b : ι → ℕ := fun j => (-(m j)).toNat with hb
  have hab : ∀ j, (a j : ℤ) - (b j : ℤ) = m j := by
    intro j
    show ((m j).toNat : ℤ) - ((-(m j)).toNat : ℤ) = m j
    omega
  have hsplit : (∏ j ∈ s, u j ^ a j) = (∏ j ∈ s, u j ^ b j) := by
    rw [← div_eq_one, ← Finset.prod_div_distrib, ← hprod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hab j, zpow_sub, zpow_natCast, zpow_natCast]
    exact (div_eq_mul_inv _ _).symm
  have hval : ∀ c : ι → ℕ, ((∏ j ∈ s, u j ^ c j : Cˣ) : C) = φ (∏ j ∈ s, π j ^ c j) := by
    intro c
    have h1 : ((∏ j ∈ s, u j ^ c j : Cˣ) : C) = ∏ j ∈ s, ((u j : C) ^ c j) := by
      simp
    rw [h1, map_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [map_pow, hu j]
  have hR : (∏ j ∈ s, π j ^ a j) = ∏ j ∈ s, π j ^ b j := by
    apply hφ
    rw [← hval a, ← hval b, hsplit]
  have hfin := deningerPrimePow_inj π hp hne s a b hR i hi
  have hmi : m i = 0 := by
    have h1 := hab i
    rw [hfin] at h1
    omega
  have hzero : n i * (N : ℤ) = 0 := hmi
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  exact (mul_eq_zero.1 hzero).resolve_right hN0

/-- An infinite family of pairwise non-associate primes of a subring forces the rational vector
space `(C^× / μ(C)) ⊗ ℚ` to be infinite dimensional. -/
theorem deningerRankAleph0_of_primes {C : Type*} [Field C] {R : Type*} [CommRing R] [IsDomain R]
    (φ : R →+* C) (hφ : Function.Injective φ) (π : ℕ → R) (hp : ∀ i, Prime (π i))
    (hne : ∀ i j, i ≠ j → ¬ Associated (π i) (π j)) :
    Cardinal.aleph0 ≤ Module.rank ℚ (DeningerUnitSpace C) := by
  have hu0 : ∀ i, φ (π i) ≠ 0 := by
    intro i h
    exact (hp i).ne_zero (hφ (by rw [h, map_zero]))
  have hind := deningerUnitVec_linearIndependent (fun i => Units.mk0 (φ (π i)) (hu0 i))
    (deningerPrimeImage_independent φ hφ π hp hne _ (fun _ => rfl))
  exact hind.aleph0_le_rank

/-! ### The rational primes -/

/-- **Characteristic zero.**  The rational primes give an infinite rationally independent family
of unit classes. -/
theorem deningerRankAleph0_charZero (C : Type*) [Field C] [CharZero C] :
    ℵ₀ ≤ Module.rank ℚ (DeningerUnitSpace C) := by
  classical
  have hP := Nat.infinite_setOf_prime
  set e := hP.natEmbedding with he
  refine deningerRankAleph0_of_primes (Int.castRingHom C) Int.cast_injective
    (fun n => (((e n : ℕ)) : ℤ))
    (fun n => Nat.prime_iff_prime_int.mp (e n).2) ?_
  intro i j hij hassoc
  have hinj : ((e i : ℕ)) ≠ ((e j : ℕ)) := fun hE => hij (e.injective (Subtype.ext hE))
  have h2 : 2 ≤ (e i : ℕ) := (e i).2.two_le
  have h3 : 2 ≤ (e j : ℕ) := (e j).2.two_le
  rcases Int.associated_iff.1 hassoc with hE | hE
  · exact hinj (by exact_mod_cast hE)
  · omega

/-! ### Monic irreducible polynomials -/

/-- **Euclid's argument for polynomials.**  Over any field there are infinitely many monic
irreducible polynomials. -/
theorem deningerMonicIrreducible_infinite (F : Type*) [Field F] :
    {f : Polynomial F | f.Monic ∧ Irreducible f}.Infinite := by
  classical
  intro hfin
  obtain ⟨t, ht⟩ := hfin.exists_finset_coe
  have hmem : ∀ f ∈ t, f.Monic ∧ Irreducible f := by
    intro f hf
    have : f ∈ ({f : Polynomial F | f.Monic ∧ Irreducible f}) := ht ▸ hf
    exact this
  have hprodmonic : (∏ f ∈ t, f).Monic :=
    Polynomial.monic_prod_of_monic t (fun f => f) fun f hf => (hmem f hf).1
  set P : Polynomial F := Polynomial.X * ∏ f ∈ t, f with hP
  have hPmonic : P.Monic := Polynomial.monic_X.mul hprodmonic
  have hPdeg : 0 < P.natDegree := by
    rw [hP, Polynomial.Monic.natDegree_mul Polynomial.monic_X hprodmonic, Polynomial.natDegree_X]
    omega
  have hdeg : 0 < (P + 1).natDegree := by
    have : (P + Polynomial.C (1 : F)).natDegree = P.natDegree := Polynomial.natDegree_add_C
    rw [Polynomial.C_1] at this
    rw [this]
    exact hPdeg
  obtain ⟨q, hqm, hqi, hqd⟩ :=
    Polynomial.exists_monic_irreducible_factor (P + 1)
      (Polynomial.not_isUnit_of_natDegree_pos _ hdeg)
  have hqt : q ∈ t := by
    have : q ∈ ({f : Polynomial F | f.Monic ∧ Irreducible f}) := ⟨hqm, hqi⟩
    rw [← ht] at this
    exact this
  have hqP : q ∣ P := by
    rw [hP]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun f => f) hqt) Polynomial.X
  have hq1 : q ∣ 1 := by
    have := dvd_sub hqd hqP
    simpa using this
  exact hqi.not_isUnit (isUnit_of_dvd_one hq1)

/-- **Positive characteristic.**  A transcendental element supplies an infinite rationally
independent family of unit classes, indexed by the monic irreducible polynomials of the base
field. -/
theorem deningerRankAleph0_of_transcendental {C : Type*} [Field C] {F : Type*} [Field F]
    (f : F →+* C) (t : C) (hinj : Function.Injective (Polynomial.eval₂RingHom f t)) :
    ℵ₀ ≤ Module.rank ℚ (DeningerUnitSpace C) := by
  classical
  have hS := deningerMonicIrreducible_infinite F
  set e := hS.natEmbedding with he
  refine deningerRankAleph0_of_primes (Polynomial.eval₂RingHom f t) hinj
    (fun n => ((e n : Polynomial F))) (fun n => Irreducible.prime (e n).2.2) ?_
  intro i j hij hassoc
  exact hij (e.injective (Subtype.ext
    (Polynomial.eq_of_monic_of_associated (e i).2.1 (e j).2.1 hassoc)))

/-! ### Transcendence in positive characteristic -/

/-- In positive characteristic a unit that is not a root of unity is transcendental over the
prime field. -/
theorem deningerTranscendental_of_notMem_torsion {C : Type*} [Field C] (p : ℕ) [Fact p.Prime]
    [CharP C p] (x : Cˣ) (hx : x ∉ CommGroup.torsion Cˣ) :
    Function.Injective (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl p) C) (x : C)) := by
  letI : Algebra (ZMod p) C := (ZMod.castHom (dvd_refl p) C).toAlgebra
  have halg : Transcendental (ZMod p) (x : C) := by
    intro hAlg
    have hint : IsIntegral (ZMod p) (x : C) := hAlg.isIntegral
    haveI : FiniteDimensional (ZMod p) (ZMod p)⟮(x : C)⟯ :=
      IntermediateField.adjoin.finiteDimensional hint
    haveI : Finite ((ZMod p)⟮(x : C)⟯) := Module.finite_of_finite (ZMod p)
    haveI : Fintype ((ZMod p)⟮(x : C)⟯) := Fintype.ofFinite _
    set y : (ZMod p)⟮(x : C)⟯ := ⟨(x : C), IntermediateField.mem_adjoin_simple_self _ _⟩ with hy
    have hy0 : y ≠ 0 := by
      intro h
      have hx0 : (x : C) = 0 := by
        have hz := congrArg (fun z : (ZMod p)⟮(x : C)⟯ => (z : C)) h
        simp only [hy] at hz
        exact hz
      exact x.ne_zero hx0
    have hpow := FiniteField.pow_card_sub_one_eq_one y hy0
    have hcard : 1 < Fintype.card ((ZMod p)⟮(x : C)⟯) := Fintype.one_lt_card
    refine hx ((CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨Fintype.card ((ZMod p)⟮(x : C)⟯) - 1, by omega, ?_⟩))
    apply Units.ext
    have hv : ((y ^ (Fintype.card ((ZMod p)⟮(x : C)⟯) - 1) : (ZMod p)⟮(x : C)⟯) : C) = 1 := by
      rw [hpow]
      rfl
    push_cast [hy] at hv
    simpa using hv
  have hinj := transcendental_iff_injective.mp halg
  exact fun a b hab => hinj (by
    simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hab)

/-! ### The dimension of `(C^× / μ(C)) ⊗ ℚ` -/

/-- **The rational vector space `(C^× / μ(C)) ⊗ ℚ` is infinite dimensional** whenever `C` is
algebraically closed and not the algebraic closure of a finite field. -/
theorem deningerAleph0_le_rank (C : Type*) [Field C] [IsAlgClosed C]
    (h : ∃ x : Cˣ, x ∉ CommGroup.torsion Cˣ) :
    ℵ₀ ≤ Module.rank ℚ (DeningerUnitSpace C) := by
  obtain ⟨p, hp⟩ := CharP.exists C
  haveI := hp
  rcases CharP.char_is_prime_or_zero C p with hprime | hzero
  · haveI : Fact p.Prime := ⟨hprime⟩
    obtain ⟨x, hx⟩ := h
    exact deningerRankAleph0_of_transcendental (ZMod.castHom (dvd_refl p) C) (x : C)
      (deningerTranscendental_of_notMem_torsion p x hx)
  · subst hzero
    haveI : CharZero C := CharP.charP_to_charZero C
    exact deningerRankAleph0_charZero C

/-- **Deninger, Lemma 4.3, dimension input.**  For an algebraically closed field `C` which is not
the algebraic closure of a finite field, `dim_ℚ (C^× / μ(C)) = #C`; only the inequality
`#C ≤ dim_ℚ (C^× / μ(C))` is recorded here, the reverse one being
`deningerRank_unitSpace_le`. -/
theorem deningerMk_le_rank (C : Type*) [Field C] [IsAlgClosed C]
    (h : ∃ x : Cˣ, x ∉ CommGroup.torsion Cˣ) :
    #C ≤ Module.rank ℚ (DeningerUnitSpace C) := by
  have hr := deningerAleph0_le_rank C h
  have hrle : Module.rank ℚ (DeningerUnitSpace C) ≤ #(DeningerUnitSpace C) :=
    deningerRank_le_mk ℚ _
  have hmkW : #(DeningerUnitSpace C) = #(DeningerUnitClass C) := deningerMk_unitSpace C
  have hW : ℵ₀ ≤ #(DeningerUnitSpace C) := hr.trans hrle
  have hM : ℵ₀ ≤ #(DeningerUnitClass C) := hmkW ▸ hW
  have hCM : #C ≤ #(DeningerUnitClass C) := deningerMk_le_unitClass C hM
  rcases lt_or_eq_of_le hW with hlt | heq
  · have hrank := Module.Free.rank_eq_mk_of_infinite_lt ℚ (DeningerUnitSpace C) (by
      rw [Cardinal.mk_denumerable ℚ, Cardinal.lift_aleph0, Cardinal.lift_uzero]
      exact hlt)
    rw [hrank, hmkW]
    exact hCM
  · calc #C ≤ #(DeningerUnitClass C) := hCM
      _ = #(DeningerUnitSpace C) := hmkW.symm
      _ = ℵ₀ := heq.symm
      _ ≤ Module.rank ℚ (DeningerUnitSpace C) := hr

end RHTower
