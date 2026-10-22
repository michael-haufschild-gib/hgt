/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 4.3 (`t3`),
last assertion, mixed characteristic.

`deningerRootsOfUnity_embed` already embeds `μ(k)` into an algebraically closed `C` whenever `k`
and `C` share a subfield.  The remaining case of the source — `char k = p > 0` and `char C = 0` —
is settled here by the classical reduction isomorphism

  `μ_{p'}(C) ≅ (𝒪 / 𝔪)^×`,   `𝒪 = integralClosure ℤ C`,   `𝔪` a maximal ideal above `p`.

Three facts are proved for that, none of which seem to be in mathlib:

* a root of unity of order prime to `p` congruent to `1` modulo `𝔪` is `1` (a two-line geometric
  sum argument inside the domain `𝒪`);
* the residue field `𝒪 / 𝔪` is algebraically closed — a monic polynomial over it lifts to `𝒪`,
  its roots in `C` are integral over `𝒪` hence lie in `𝒪`, and they reduce to roots downstairs;
* a unit of a field of characteristic `p` which is integral over `ℤ` has finite order, and that
  order may be taken prime to `p`.

Counting `#μ_n` on both sides then turns the injective reduction into a bijection, and its inverse
composed with the equal-characteristic embedding into `𝒪 / 𝔪` gives `μ(k) ↪ C^×`.

The file closes with the last assertion of Lemma 4.3 in the exact generality of the source:
`char C = 0` or `char k = char C`.
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Basic
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCharacterExtension
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysPointedMultiplicativeRoot

namespace RHTower

open Cardinal IntermediateField

/-- **Roots of unity of order invertible modulo `𝔪` reduce injectively.**  In a domain, a root of
unity of order `n` congruent to `1` modulo an ideal not containing `n` is equal to `1`. -/
theorem deningerRootOfUnity_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] {m : Ideal R}
    {n : ℕ} (hn : (n : R) ∉ m) {ζ : R} (hζ : ζ ^ n = 1) (h1 : ζ - 1 ∈ m) : ζ = 1 := by
  classical
  have hgeom : (∑ i ∈ Finset.range n, ζ ^ i) * (ζ - 1) = ζ ^ n - 1 := geom_sum_mul ζ n
  rw [hζ, sub_self] at hgeom
  have hstep : ∀ i : ℕ, ζ ^ i - 1 ∈ m := by
    intro i
    obtain ⟨c, hc⟩ : (ζ - 1) ∣ (ζ ^ i - 1 ^ i) := sub_dvd_pow_sub_pow ζ 1 i
    rw [one_pow] at hc
    rw [hc]
    exact Ideal.mul_mem_right c m h1
  have hS : (∑ i ∈ Finset.range n, ζ ^ i) - (n : R) ∈ m := by
    have hrw : (∑ i ∈ Finset.range n, ζ ^ i) - (n : R)
        = ∑ i ∈ Finset.range n, (ζ ^ i - 1) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [hrw]
    exact Ideal.sum_mem m fun i _ => hstep i
  have hSne : (∑ i ∈ Finset.range n, ζ ^ i) ≠ 0 := by
    intro h
    rw [h, zero_sub] at hS
    exact hn (by simpa using m.neg_mem hS)
  rcases mul_eq_zero.1 hgeom with h | h
  · exact absurd h hSne
  · exact sub_eq_zero.1 h

/-! ### The algebraic integers of an algebraically closed field -/

section AlgInt

variable {C : Type*} [Field C] [IsAlgClosed C]

/-- A root of a monic polynomial over the algebraic integers is an algebraic integer. -/
theorem deningerAlgInt_exists_root (F : Polynomial (integralClosure ℤ C)) (hFmonic : F.Monic)
    (hdeg : F.degree ≠ 0) : ∃ a : integralClosure ℤ C, F.eval a = 0 := by
  have hdeg' : (F.map (algebraMap (integralClosure ℤ C) C)).degree ≠ 0 := by
    rw [hFmonic.degree_map]
    exact hdeg
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg'
  have hint : IsIntegral (integralClosure ℤ C) α := by
    refine ⟨F, hFmonic, ?_⟩
    have := hα
    rw [Polynomial.IsRoot, Polynomial.eval_map] at this
    exact this
  have hintZ : IsIntegral ℤ α := isIntegral_trans α hint
  refine ⟨⟨α, hintZ⟩, Subtype.ext ?_⟩
  have hmapval : (algebraMap (integralClosure ℤ C) C) (F.eval ⟨α, hintZ⟩)
      = Polynomial.eval₂ (algebraMap (integralClosure ℤ C) C) α F := by
    rw [← Polynomial.eval₂_at_apply]
    rfl
  have hzero : Polynomial.eval₂ (algebraMap (integralClosure ℤ C) C) α F = 0 := by
    have := hα
    rw [Polynomial.IsRoot, Polynomial.eval_map] at this
    exact this
  simpa [hzero] using hmapval

/-- **The residue field of the algebraic integers at a maximal ideal is algebraically closed.** -/
theorem deningerAlgInt_isAlgClosed_quotient (m : Ideal (integralClosure ℤ C)) [m.IsMaximal] :
    letI := Ideal.Quotient.field m
    IsAlgClosed ((integralClosure ℤ C) ⧸ m) := by
  classical
  letI := Ideal.Quotient.field m
  refine IsAlgClosed.of_exists_root _ fun f hmonic hirr => ?_
  obtain ⟨F, hFmap, hFdeg, hFmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective f) hmonic
  have hfdeg : f.degree ≠ 0 := fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨a, ha⟩ := deningerAlgInt_exists_root F hFmonic (by rw [hFdeg]; exact hfdeg)
  refine ⟨Ideal.Quotient.mk m a, ?_⟩
  rw [← hFmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]

end AlgInt

/-! ### Units of a field algebraic over its prime field -/

section FinOrder

variable {L : Type*} [Field L]

/-- An element of a field of characteristic `p` which is integral over `ℤ` is algebraic over the
prime field. -/
theorem deningerIsAlgebraic_zmod_of_isIntegral (p : ℕ) [Fact p.Prime] [CharP L p]
    (y : L) (h : IsIntegral ℤ y) :
    letI : Algebra (ZMod p) L := (ZMod.castHom (dvd_refl p) L).toAlgebra
    IsAlgebraic (ZMod p) y := by
  letI : Algebra (ZMod p) L := (ZMod.castHom (dvd_refl p) L).toAlgebra
  obtain ⟨F, hFmonic, hFeval⟩ := h
  refine ⟨F.map (Int.castRingHom (ZMod p)), ?_, ?_⟩
  · exact (hFmonic.map _).ne_zero
  · have hcomp : (algebraMap (ZMod p) L).comp (Int.castRingHom (ZMod p))
        = Int.castRingHom L := by
      ext z
      simp
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
    exact hFeval

/-- A unit of a field of characteristic `p` which is integral over `ℤ` has finite order. -/
theorem deningerIsOfFinOrder_of_isIntegral (p : ℕ) [Fact p.Prime] [CharP L p] (u : Lˣ)
    (h : IsIntegral ℤ ((u : L))) : IsOfFinOrder u := by
  letI : Algebra (ZMod p) L := (ZMod.castHom (dvd_refl p) L).toAlgebra
  have halg : IsAlgebraic (ZMod p) (u : L) := deningerIsAlgebraic_zmod_of_isIntegral p (u : L) h
  have hint : IsIntegral (ZMod p) (u : L) := halg.isIntegral
  haveI : FiniteDimensional (ZMod p) (ZMod p)⟮(u : L)⟯ :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite ((ZMod p)⟮(u : L)⟯) := Module.finite_of_finite (ZMod p)
  haveI : Fintype ((ZMod p)⟮(u : L)⟯) := Fintype.ofFinite _
  set y : (ZMod p)⟮(u : L)⟯ := ⟨(u : L), IntermediateField.mem_adjoin_simple_self _ _⟩ with hy
  have hy0 : y ≠ 0 := by
    intro hz
    have hu0 : (u : L) = 0 := by
      have hz' := congrArg (fun z : (ZMod p)⟮(u : L)⟯ => (z : L)) hz
      simp only [hy] at hz'
      exact hz'
    exact u.ne_zero hu0
  have hpow := FiniteField.pow_card_sub_one_eq_one y hy0
  have hcard : 1 < Fintype.card ((ZMod p)⟮(u : L)⟯) := Fintype.one_lt_card
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨Fintype.card ((ZMod p)⟮(u : L)⟯) - 1, by omega, ?_⟩
  apply Units.ext
  have hv : ((y ^ (Fintype.card ((ZMod p)⟮(u : L)⟯) - 1) : (ZMod p)⟮(u : L)⟯) : L) = 1 := by
    rw [hpow]
    rfl
  push_cast [hy] at hv
  simpa using hv

/-- In characteristic `p` a torsion unit has an annihilating exponent prime to `p`. -/
theorem deningerExists_primeToP_pow (p : ℕ) [Fact p.Prime] [CharP L p] (u : Lˣ)
    (h : IsOfFinOrder u) :
    ∃ n : ℕ, n ≠ 0 ∧ ¬ p ∣ n ∧ u ^ n = 1 := by
  haveI : ExpChar L p := ExpChar.prime (Fact.out)
  have hp : p.Prime := Fact.out
  set n₀ := orderOf u with hn₀
  have hn₀pos : 0 < n₀ := h.orderOf_pos
  refine ⟨ordCompl[p] n₀, (Nat.ordCompl_pos p (by omega)).ne', Nat.not_dvd_ordCompl hp (by omega),
    ?_⟩
  have hsplit : ordProj[p] n₀ * ordCompl[p] n₀ = n₀ := Nat.ordProj_mul_ordCompl_eq_self n₀ p
  have hbig : (u ^ ordCompl[p] n₀) ^ ordProj[p] n₀ = 1 := by
    rw [← pow_mul, mul_comm, hsplit, hn₀, pow_orderOf_eq_one]
  apply Units.ext
  have hval : (((u ^ ordCompl[p] n₀ : Lˣ) : L)) ^ (p ^ (n₀.factorization p)) = 1 := by
    have := congrArg (fun v : Lˣ => (v : L)) hbig
    simpa using this
  have hsub : ((((u ^ ordCompl[p] n₀ : Lˣ) : L)) - 1) ^ (p ^ (n₀.factorization p)) = 0 := by
    rw [sub_pow_char_pow, hval, one_pow, sub_self]
  have hne : p ^ (n₀.factorization p) ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have := (pow_eq_zero_iff hne).1 hsub
  have hfin : (((u ^ ordCompl[p] n₀ : Lˣ) : L)) = 1 := by
    have h2 := sub_eq_zero.1 this
    exact h2
  simpa using hfin

end FinOrder

/-! ### Reduction of roots of unity of order prime to `p` -/

section Reduction

variable {C : Type*} [Field C] (p : ℕ) [Fact p.Prime]

/-- The group of roots of unity of `C` whose order is prime to `p`. -/
def deningerPrimeToPUnits : Subgroup Cˣ where
  carrier := {x : Cˣ | ∃ n : ℕ, n ≠ 0 ∧ ¬ p ∣ n ∧ x ^ n = 1}
  one_mem' := ⟨1, one_ne_zero, (Fact.out : p.Prime).not_dvd_one, one_pow 1⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hpn, han⟩ ⟨k, hk, hpk, hbk⟩
    refine ⟨n * k, Nat.mul_ne_zero hn hk, ?_, ?_⟩
    · intro h
      rcases (Nat.Prime.dvd_mul (Fact.out)).1 h with h' | h'
      · exact hpn h'
      · exact hpk h'
    · have h1 : a ^ (n * k) = 1 := by rw [pow_mul, han, one_pow]
      have h2 : b ^ (n * k) = 1 := by rw [mul_comm, pow_mul, hbk, one_pow]
      rw [mul_pow, h1, h2, one_mul]
  inv_mem' := by
    rintro a ⟨n, hn, hpn, han⟩
    exact ⟨n, hn, hpn, by rw [inv_pow, han, inv_one]⟩

variable {p}

theorem deningerMem_primeToPUnits_iff {x : Cˣ} :
    x ∈ deningerPrimeToPUnits (C := C) p ↔ ∃ n : ℕ, n ≠ 0 ∧ ¬ p ∣ n ∧ x ^ n = 1 := Iff.rfl

/-- A root of unity is an algebraic integer. -/
theorem deningerIsIntegral_of_primeToP {x : Cˣ} (hx : x ∈ deningerPrimeToPUnits (C := C) p) :
    IsIntegral ℤ ((x : Cˣ) : C) := by
  obtain ⟨n, hn, -, hxn⟩ := hx
  refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
  · have := Polynomial.monic_X_pow_sub_C (1 : ℤ) hn
    rwa [Polynomial.C_1] at this
  · have hval : ((x : Cˣ) : C) ^ n = 1 := by
      have := congrArg (fun u : Cˣ => (u : C)) hxn
      simpa using this
    simp [hval]

variable (p)

/-- The tautological multiplicative map from the prime-to-`p` roots of unity to the algebraic
integers. -/
def deningerPrimeToPAlgInt : deningerPrimeToPUnits (C := C) p →* integralClosure ℤ C where
  toFun x := ⟨((x : Cˣ) : C), deningerIsIntegral_of_primeToP x.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- The reduction of the prime-to-`p` roots of unity modulo a maximal ideal of the algebraic
integers. -/
def deningerReduceUnits (m : Ideal (integralClosure ℤ C)) :
    deningerPrimeToPUnits (C := C) p →* ((integralClosure ℤ C) ⧸ m)ˣ :=
  MonoidHom.toHomUnits
    (((Ideal.Quotient.mk m : integralClosure ℤ C →+* _) : integralClosure ℤ C →* _).comp
      (deningerPrimeToPAlgInt p))

theorem deningerReduceUnits_val (m : Ideal (integralClosure ℤ C))
    (x : deningerPrimeToPUnits (C := C) p) :
    ((deningerReduceUnits p m x : ((integralClosure ℤ C) ⧸ m)ˣ) : (integralClosure ℤ C) ⧸ m)
      = Ideal.Quotient.mk m (deningerPrimeToPAlgInt p x) := rfl

variable {p}

/-- An integer prime to `p` is invertible modulo a maximal ideal containing `p`. -/
theorem deningerNatCast_notMem {m : Ideal (integralClosure ℤ C)} [m.IsMaximal]
    (hm : ((p : ℕ) : integralClosure ℤ C) ∈ m) {n : ℕ} (hpn : ¬ p ∣ n) :
    ((n : ℕ) : integralClosure ℤ C) ∉ m := by
  intro hn
  haveI : Nontrivial ((integralClosure ℤ C) ⧸ m) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top ‹m.IsMaximal›)
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 hpn
  obtain ⟨a, b, hab⟩ : IsCoprime ((p : ℕ) : ℤ) ((n : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hzero : (1 : (integralClosure ℤ C) ⧸ m) = 0 := by
    have hp0 : (Ideal.Quotient.mk m) ((p : ℕ) : integralClosure ℤ C) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hm
    have hn0 : (Ideal.Quotient.mk m) ((n : ℕ) : integralClosure ℤ C) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hn
    have := congrArg (fun z : ℤ => (Ideal.Quotient.mk m) ((z : integralClosure ℤ C))) hab
    simpa [hp0, hn0] using this.symm
  exact one_ne_zero hzero

/-- **The reduction of the prime-to-`p` roots of unity is injective.** -/
theorem deningerReduceUnits_injective {m : Ideal (integralClosure ℤ C)} [m.IsMaximal]
    (hm : ((p : ℕ) : integralClosure ℤ C) ∈ m) :
    Function.Injective (deningerReduceUnits p m) := by
  rw [injective_iff_map_eq_one]
  intro ζ hζ
  obtain ⟨n, hn, hpn, hζn⟩ := ζ.2
  have hsub : (deningerPrimeToPAlgInt p ζ) - 1 ∈ m := by
    have hval : Ideal.Quotient.mk m (deningerPrimeToPAlgInt p ζ) = Ideal.Quotient.mk m 1 := by
      rw [map_one, ← deningerReduceUnits_val p m ζ, hζ, Units.val_one]
    exact (Ideal.Quotient.eq).1 hval
  have hpow : (deningerPrimeToPAlgInt p ζ) ^ n = 1 := by
    rw [← map_pow]
    have : (ζ : deningerPrimeToPUnits (C := C) p) ^ n = 1 := Subtype.ext (by
      exact_mod_cast hζn)
    rw [this, map_one]
  have h1 := deningerRootOfUnity_eq_one_of_sub_mem (deningerNatCast_notMem hm hpn) hpow hsub
  have h2 : (((ζ : Cˣ)) : C) = 1 := congrArg Subtype.val h1
  exact Subtype.ext (Units.ext h2)

/-! ### The residue field at a maximal ideal above `p` -/

section Residue

variable {C : Type*} [Field C] [IsAlgClosed C] [CharZero C] {p : ℕ} [Fact p.Prime]

omit [IsAlgClosed C] [CharZero C] in
/-- The residue field of the algebraic integers at a maximal ideal containing `p` has
characteristic `p`. -/
theorem deningerCharP_quotient {m : Ideal (integralClosure ℤ C)} [m.IsMaximal]
    (hm : ((p : ℕ) : integralClosure ℤ C) ∈ m) :
    CharP ((integralClosure ℤ C) ⧸ m) p := by
  letI := Ideal.Quotient.field m
  obtain ⟨q, hq⟩ := CharP.exists ((integralClosure ℤ C) ⧸ m)
  haveI := hq
  have hp0 : ((p : ℕ) : (integralClosure ℤ C) ⧸ m) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk m) p]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hm
  have hpq : q ∣ p := (CharP.cast_eq_zero_iff _ q p).1 hp0
  rcases CharP.char_is_prime_or_zero ((integralClosure ℤ C) ⧸ m) q with hqp | hq0
  · exact ((Nat.prime_dvd_prime_iff_eq hqp Fact.out).1 hpq) ▸ hq
  · subst hq0
    exact absurd (Nat.eq_zero_of_zero_dvd hpq) (Fact.out : p.Prime).ne_zero

omit [IsAlgClosed C] [CharZero C] in
/-- Every element of the residue field is integral over `ℤ`. -/
theorem deningerIsIntegral_quotient (m : Ideal (integralClosure ℤ C))
    (a : integralClosure ℤ C) : IsIntegral ℤ (Ideal.Quotient.mk m a) := by
  obtain ⟨F, hFmonic, hFeval⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) a
  refine ⟨F, hFmonic, ?_⟩
  have hcomp : (Ideal.Quotient.mk m).comp (algebraMap ℤ (integralClosure ℤ C))
      = algebraMap ℤ ((integralClosure ℤ C) ⧸ m) := by
    ext z
    simp
  have hstep := Polynomial.hom_eval₂ F (algebraMap ℤ (integralClosure ℤ C))
    (Ideal.Quotient.mk m) a
  rw [hcomp] at hstep
  rw [← hstep, hFeval, map_zero]

/-- **The reduction of the prime-to-`p` roots of unity is surjective.** -/
theorem deningerReduceUnits_surjective {m : Ideal (integralClosure ℤ C)} [m.IsMaximal]
    (hm : ((p : ℕ) : integralClosure ℤ C) ∈ m) :
    Function.Surjective (deningerReduceUnits p m) := by
  classical
  haveI := deningerCharP_quotient hm
  letI := Ideal.Quotient.field m
  haveI : IsAlgClosed ((integralClosure ℤ C) ⧸ m) := deningerAlgInt_isAlgClosed_quotient m
  intro u
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : (integralClosure ℤ C) ⧸ m)
  have hint : IsIntegral ℤ ((u : (integralClosure ℤ C) ⧸ m)) := by
    rw [← ha]
    exact deningerIsIntegral_quotient m a
  obtain ⟨n, hn, hpn, hun⟩ :=
    deningerExists_primeToP_pow p u (deningerIsOfFinOrder_of_isIntegral p u hint)
  haveI : NeZero n := ⟨hn⟩
  haveI : Fintype (rootsOfUnity n C) := Fintype.ofFinite _
  haveI : Fintype (rootsOfUnity n ((integralClosure ℤ C) ⧸ m)) := Fintype.ofFinite _
  have hcardA : Fintype.card (rootsOfUnity n C) = n := by
    rw [← Nat.card_eq_fintype_card]
    exact deningerCard_rootsOfUnity_charZero hn
  have hcardB : Fintype.card (rootsOfUnity n ((integralClosure ℤ C) ⧸ m)) = n := by
    rw [← Nat.card_eq_fintype_card, deningerCard_rootsOfUnity_charP (p := p) hn]
    simp [Nat.factorization_eq_zero_of_not_dvd hpn]
  have hmemT : ∀ x : rootsOfUnity n C, (x : Cˣ) ∈ deningerPrimeToPUnits (C := C) p := by
    intro x
    exact ⟨n, hn, hpn, (mem_rootsOfUnity n (x : Cˣ)).1 x.2⟩
  have hmemB : ∀ x : rootsOfUnity n C,
      deningerReduceUnits p m ⟨(x : Cˣ), hmemT x⟩
        ∈ rootsOfUnity n ((integralClosure ℤ C) ⧸ m) := by
    intro x
    refine (mem_rootsOfUnity n _).2 ?_
    rw [← map_pow]
    have hxval : ((x : Cˣ)) ^ n = 1 := (mem_rootsOfUnity n (x : Cˣ)).1 x.2
    have hx : (⟨(x : Cˣ), hmemT x⟩ : deningerPrimeToPUnits (C := C) p) ^ n = 1 :=
      Subtype.ext (by simpa using hxval)
    rw [hx, map_one]
  set Ψ : rootsOfUnity n C → rootsOfUnity n ((integralClosure ℤ C) ⧸ m) :=
    fun x => ⟨deningerReduceUnits p m ⟨(x : Cˣ), hmemT x⟩, hmemB x⟩ with hΨ
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    have h1 : deningerReduceUnits p m ⟨(x : Cˣ), hmemT x⟩
        = deningerReduceUnits p m ⟨(y : Cˣ), hmemT y⟩ :=
      congrArg (fun z : rootsOfUnity n ((integralClosure ℤ C) ⧸ m) =>
        (z : ((integralClosure ℤ C) ⧸ m)ˣ)) hxy
    have h2 := deningerReduceUnits_injective hm h1
    have h3 : ((x : Cˣ)) = ((y : Cˣ)) :=
      congrArg (fun z : deningerPrimeToPUnits (C := C) p => (z : Cˣ)) h2
    exact Subtype.ext h3
  have hbij : Function.Bijective Ψ :=
    (Fintype.bijective_iff_injective_and_card Ψ).2 ⟨hΨinj, by rw [hcardA, hcardB]⟩
  have humem : u ∈ rootsOfUnity n ((integralClosure ℤ C) ⧸ m) := (mem_rootsOfUnity n u).2 hun
  obtain ⟨x, hx⟩ := hbij.2 ⟨u, humem⟩
  exact ⟨⟨(x : Cˣ), hmemT x⟩, congrArg Subtype.val hx⟩

end Residue

end Reduction

/-! ### The mixed-characteristic embedding of roots of unity -/

universe u v

/-- **Roots of unity of a field of characteristic `p` embed into an algebraically closed field of
characteristic zero.**  The bridge is the residue field of the algebraic integers of `C` at a
maximal ideal above `p`: it is algebraically closed of characteristic `p`, and the prime-to-`p`
roots of unity of `C` reduce bijectively onto its unit group. -/
theorem deningerRootsOfUnity_embed_mixed {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {C : Type*} [Field C] [IsAlgClosed C] [CharZero C] :
    ∃ χμ : CommGroup.torsion kˣ →* Cˣ, Function.Injective χμ := by
  classical
  haveI hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).irreducible
  obtain ⟨m, hmmax, hcomap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (R := ℤ) (S := integralClosure ℤ C)
      (Ideal.span {(p : ℤ)})
      (by
        have : RingHom.ker (algebraMap ℤ (integralClosure ℤ C)) = ⊥ :=
          (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
        rw [this]
        exact bot_le)
  haveI := hmmax
  have hm : ((p : ℕ) : integralClosure ℤ C) ∈ m := by
    have hmem : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (integralClosure ℤ C)) m := by
      rw [hcomap]
      exact Ideal.mem_span_singleton_self _
    have := hmem
    rw [Ideal.mem_comap] at this
    have hcast : (algebraMap ℤ (integralClosure ℤ C)) (p : ℤ)
        = ((p : ℕ) : integralClosure ℤ C) := by push_cast; rfl
    rwa [hcast] at this
  haveI := deningerCharP_quotient (p := p) hm
  letI := Ideal.Quotient.field m
  haveI : IsAlgClosed ((integralClosure ℤ C) ⧸ m) := deningerAlgInt_isAlgClosed_quotient m
  letI : Algebra (ZMod p) k := (ZMod.castHom (dvd_refl p) k).toAlgebra
  letI : Algebra (ZMod p) ((integralClosure ℤ C) ⧸ m) :=
    (ZMod.castHom (dvd_refl p) _).toAlgebra
  obtain ⟨f, hf⟩ :=
    deningerRootsOfUnity_embed (ZMod p) (k := k) (C := (integralClosure ℤ C) ⧸ m)
  have hbij : Function.Bijective (deningerReduceUnits p m) :=
    ⟨deningerReduceUnits_injective hm, deningerReduceUnits_surjective hm⟩
  set e := MulEquiv.ofBijective (deningerReduceUnits p m) hbij with he
  refine ⟨((deningerPrimeToPUnits (C := C) p).subtype).comp
    ((e.symm : ((integralClosure ℤ C) ⧸ m)ˣ →* deningerPrimeToPUnits (C := C) p).comp f), ?_⟩
  intro a b hab
  exact hf (e.symm.injective (Subtype.val_injective hab))

/-- **Deninger, Lemma 4.3 (`t3`), last assertion, mixed characteristic.** -/
theorem deningerInjectiveCharacter_mixed {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {C : Type v} [Field C] [IsAlgClosed C] [CharZero C]
    (hcard : Cardinal.lift.{v} #k ≤ Cardinal.lift.{u} #C) :
    ∃ χ : kˣ →* Cˣ, Function.Injective χ := by
  obtain ⟨χμ, hχμ⟩ := deningerRootsOfUnity_embed_mixed (k := k) p (C := C)
  obtain ⟨χ, hext, hker⟩ :=
    deningerCharacterExtension (deningerExists_notMem_torsion_charZero C) hcard χμ
  refine ⟨χ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨hmem, hzero⟩ := (hker x).1 hx
  have h1 : (⟨x, hmem⟩ : CommGroup.torsion kˣ) = 1 := hχμ (by rw [hzero, map_one])
  exact congrArg (fun y : CommGroup.torsion kˣ => (y : kˣ)) h1

/-- **Deninger, Lemma 4.3 (`t3`), last assertion, in full.**  If `C` is algebraically closed with
`C^× ≠ μ(C)`, `#k ≤ #C`, and either `char C = 0` or `char k = char C`, then `k^×` embeds into
`C^×`. -/
theorem deningerInjectiveCharacter_of_char {k : Type u} [Field k] {C : Type v} [Field C]
    [IsAlgClosed C] (hne : ∃ x : Cˣ, x ∉ CommGroup.torsion Cˣ)
    (hcard : Cardinal.lift.{v} #k ≤ Cardinal.lift.{u} #C)
    (hchar : ringChar C = 0 ∨ ringChar k = ringChar C) :
    ∃ χ : kˣ →* Cˣ, Function.Injective χ := by
  haveI hCk : CharP C (ringChar C) := ringChar.charP C
  haveI hkk : CharP k (ringChar k) := ringChar.charP k
  rcases hchar with hC0 | heq
  · haveI : CharP C 0 := hC0 ▸ hCk
    haveI : CharZero C := CharP.charP_to_charZero C
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hkp | hk0
    · haveI : Fact (ringChar k).Prime := ⟨hkp⟩
      exact deningerInjectiveCharacter_mixed (ringChar k) hcard
    · haveI : CharP k 0 := hk0 ▸ hkk
      haveI : CharZero k := CharP.charP_to_charZero k
      exact deningerInjectiveCharacter_charZero hcard
  · rcases CharP.char_is_prime_or_zero C (ringChar C) with hCp | hC0
    · haveI : Fact (ringChar C).Prime := ⟨hCp⟩
      haveI : CharP k (ringChar C) := heq ▸ hkk
      exact deningerInjectiveCharacter_charP hne hcard
    · haveI : CharP C 0 := hC0 ▸ hCk
      haveI : CharZero C := CharP.charP_to_charZero C
      haveI : CharP k 0 := (heq.trans hC0) ▸ hkk
      haveI : CharZero k := CharP.charP_to_charZero k
      exact deningerInjectiveCharacter_charZero hcard

end RHTower
