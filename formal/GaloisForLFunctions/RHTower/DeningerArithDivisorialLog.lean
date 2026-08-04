import GaloisForLFunctions.RHTower.DeningerArithStructureRing
import GaloisForLFunctions.RHTower.DeningerLogStructure
import GaloisForLFunctions.RHTower.DeningerSUnitEndpointPage

/-!
# The divisorial log structure of a finite set of primes

Fix a finite set `P` of rational primes and an open set `U` of the arithmetic curve.  The rational
units that are regular on `U` and invertible away from `P` form the divisorial log structure of the
divisor cut out by `P`: it is a log structure over the ring of regular functions, and its
characteristic monoid is the free commutative monoid on the primes of `P` lying in `U`.

Surjectivity of the characteristic map is unique factorization — every exponent vector is realized
by the corresponding product of prime powers — and its fibres are the orbits of the units, because
two sections with the same valuations differ by a rational with vanishing valuations.

* `deningerLogSub` : the divisorial log structure on an open set.
* `deningerArithPreLog`, `deningerArithIsLog` : it is a log structure over the structure ring.
* `deningerArithLogChar` : its characteristic monoid is `⊕_{p ∈ P, p ∈ U} ℕ`.
-/

namespace RHTower

open TopologicalSpace

/-- The divisorial log structure of the primes in `P`, on an open set of the arithmetic curve:
rational units that are regular on the open set and invertible away from `P`. -/
def deningerLogSub (P : Finset Nat.Primes) (U : Opens deningerArithBase) : Submonoid ℚˣ where
  carrier := {q : ℚˣ | ∀ p : Nat.Primes, deningerClosedPt p ∈ U →
    0 ≤ padicValRat ((p : ℕ)) ((q : ℚ)) ∧ (p ∉ P → padicValRat ((p : ℕ)) ((q : ℚ)) = 0)}
  one_mem' := by
    intro p _
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [Units.val_one, padicValRat.one]
    exact ⟨le_rfl, fun _ => rfl⟩
  mul_mem' := by
    intro a b ha hb p hp
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [Units.val_mul, padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]
    exact ⟨add_nonneg (ha p hp).1 (hb p hp).1, fun hP => by
      rw [(ha p hp).2 hP, (hb p hp).2 hP, add_zero]⟩

theorem deningerLogSub_mem_iff {P : Finset Nat.Primes} {U : Opens deningerArithBase} {q : ℚˣ} :
    q ∈ deningerLogSub P U ↔ ∀ p : Nat.Primes, deningerClosedPt p ∈ U →
      0 ≤ padicValRat ((p : ℕ)) ((q : ℚ)) ∧ (p ∉ P → padicValRat ((p : ℕ)) ((q : ℚ)) = 0) :=
  Iff.rfl

/-- The structure map of the divisorial log structure. -/
def deningerLogHom (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    deningerLogSub P U →* deningerArithRing U where
  toFun q := ⟨((q : ℚˣ) : ℚ), fun p hp => (q.2 p hp).1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[simp]
theorem deningerLogHom_val (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (q : deningerLogSub P U) : ((deningerLogHom P U q : deningerArithRing U) : ℚ) =
      ((q : ℚˣ) : ℚ) := rfl

/-- **The divisorial log structure**, as a prelog structure over the ring of regular functions. -/
def deningerArithPreLog (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    DeningerPreLog (deningerArithRing U) where
  M := deningerLogSub P U
  hom := deningerLogHom P U

theorem deningerLogHom_injective (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    Function.Injective (deningerLogHom P U) := by
  intro m n h
  have h' : ((m : ℚˣ) : ℚ) = ((n : ℚˣ) : ℚ) :=
    congrArg (fun z : deningerArithRing U => (z : ℚ)) h
  exact Subtype.ext (Units.ext h')

/-- **It is a log structure**: the sections lying over units are exactly the units. -/
theorem deningerArithIsLog (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    DeningerIsLog (deningerArithPreLog P U) where
  injOn := fun _ _ _ _ h => deningerLogHom_injective P U h
  surjOn := by
    intro r hr
    obtain ⟨hr0, hval⟩ := (deningerArithRing_isUnit_iff U r).1 hr
    refine ⟨(⟨Units.mk0 ((r : ℚ)) hr0, fun p hp => ?_⟩ : deningerLogSub P U), ?_⟩
    · rw [show ((Units.mk0 ((r : ℚ)) hr0 : ℚˣ) : ℚ) = (r : ℚ) from rfl, hval p hp]
      exact ⟨le_rfl, fun _ => rfl⟩
    · exact Subtype.ext rfl

/-- The primes of `P` that lie in the open set: the support of the characteristic monoid. -/
abbrev deningerLogIdx (P : Finset Nat.Primes) (U : Opens deningerArithBase) : Type :=
  {p : Nat.Primes // p ∈ P ∧ deningerClosedPt p ∈ U}

instance deningerLogIdx_finite (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    Finite (deningerLogIdx P U) :=
  Finite.of_injective (fun x : deningerLogIdx P U => (⟨x.1, x.2.1⟩ : {p : Nat.Primes // p ∈ P}))
    (fun _ _ h => Subtype.ext
      (congrArg (fun z : {p : Nat.Primes // p ∈ P} => (z : Nat.Primes)) h))

/-- The characteristic map of the divisorial log structure: the valuations along `P`. -/
def deningerLogOrdFun (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (q : deningerLogSub P U) : deningerLogIdx P U → ℕ :=
  fun p => (padicValRat (((p : Nat.Primes) : ℕ)) ((q : ℚˣ) : ℚ)).toNat

theorem deningerLogOrdFun_coe (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (q : deningerLogSub P U) (p : deningerLogIdx P U) :
    ((deningerLogOrdFun P U q p : ℕ) : ℤ) =
      padicValRat (((p : Nat.Primes) : ℕ)) ((q : ℚˣ) : ℚ) :=
  Int.toNat_of_nonneg (q.2 (p : Nat.Primes) p.2.2).1

/-- The characteristic map, as a monoid homomorphism. -/
def deningerLogOrd (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    deningerLogSub P U →* Multiplicative (deningerLogIdx P U → ℕ) where
  toFun q := Multiplicative.ofAdd (deningerLogOrdFun P U q)
  map_one' := by
    refine congrArg Multiplicative.ofAdd ?_
    funext p
    haveI : Fact (((p : Nat.Primes) : ℕ)).Prime := ⟨(p : Nat.Primes).2⟩
    have : padicValRat (((p : Nat.Primes) : ℕ)) (((1 : deningerLogSub P U) : ℚˣ) : ℚ) = 0 := by
      rw [show (((1 : deningerLogSub P U) : ℚˣ) : ℚ) = 1 from rfl, padicValRat.one]
    show (padicValRat _ _).toNat = 0
    rw [this]
    rfl
  map_mul' a b := by
    refine congrArg Multiplicative.ofAdd ?_
    funext p
    haveI : Fact (((p : Nat.Primes) : ℕ)).Prime := ⟨(p : Nat.Primes).2⟩
    have hz : ((deningerLogOrdFun P U (a * b) p : ℕ) : ℤ) =
        ((deningerLogOrdFun P U a p : ℕ) : ℤ) + ((deningerLogOrdFun P U b p : ℕ) : ℤ) := by
      rw [deningerLogOrdFun_coe, deningerLogOrdFun_coe, deningerLogOrdFun_coe,
        show (((a * b : deningerLogSub P U) : ℚˣ) : ℚ) = ((a : ℚˣ) : ℚ) * ((b : ℚˣ) : ℚ) from rfl,
        padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]
    exact_mod_cast hz

@[simp]
theorem deningerLogOrd_apply (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (q : deningerLogSub P U) :
    deningerLogOrd P U q = Multiplicative.ofAdd (deningerLogOrdFun P U q) := rfl

theorem deningerLogOrd_eq_one_iff (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (q : deningerLogSub P U) :
    deningerLogOrd P U q = 1 ↔
      ∀ p : Nat.Primes, deningerClosedPt p ∈ U → padicValRat ((p : ℕ)) ((q : ℚˣ) : ℚ) = 0 := by
  constructor
  · intro h p hp
    by_cases hP : p ∈ P
    · have h0 : deningerLogOrdFun P U q ⟨p, hP, hp⟩ = 0 := by
        have := congrArg (fun t : Multiplicative (deningerLogIdx P U → ℕ) =>
          Multiplicative.toAdd t ⟨p, hP, hp⟩) h
        simpa using this
      have := deningerLogOrdFun_coe P U q ⟨p, hP, hp⟩
      rw [h0] at this
      exact this.symm.trans rfl
    · exact (q.2 p hp).2 hP
  · intro h
    refine congrArg Multiplicative.ofAdd ?_
    funext p
    have hz : ((deningerLogOrdFun P U q p : ℕ) : ℤ) = 0 := by
      rw [deningerLogOrdFun_coe]
      exact h (p : Nat.Primes) p.2.2
    exact_mod_cast hz

/-- **Unique factorization**: every exponent vector along `P` is realized. -/
theorem deningerLogOrd_surjective (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    Function.Surjective (deningerLogOrd P U) := by
  classical
  intro N
  set n : deningerLogIdx P U → ℕ := Multiplicative.toAdd N with hn
  set n' : {x : Nat.Primes // x ∈ P} → ℤ := fun x =>
    if h : deningerClosedPt ((x : Nat.Primes)) ∈ U then ((n ⟨(x : Nat.Primes), x.2, h⟩ : ℕ) : ℤ)
    else 0 with hn'
  set q : ℚˣ := deningerSUnitProduct P n' with hq
  have hval : ∀ p : Nat.Primes, padicValRat ((p : ℕ)) ((q : ℚ)) =
      if hp : p ∈ P then n' ⟨p, hp⟩ else 0 := fun p => deningerSUnitProduct_val P n' p
  have hmem : q ∈ deningerLogSub P U := by
    intro p hp
    rw [hval p]
    by_cases hP : p ∈ P
    · rw [dif_pos hP, hn']
      simp only [dif_pos hp]
      exact ⟨Int.natCast_nonneg _, fun h => absurd hP h⟩
    · rw [dif_neg hP]
      exact ⟨le_rfl, fun _ => rfl⟩
  refine ⟨(⟨q, hmem⟩ : deningerLogSub P U), ?_⟩
  have hfun : deningerLogOrdFun P U ⟨q, hmem⟩ = n := by
    funext p
    have hz : ((deningerLogOrdFun P U ⟨q, hmem⟩ p : ℕ) : ℤ) = ((n p : ℕ) : ℤ) := by
      rw [deningerLogOrdFun_coe]
      show padicValRat _ ((q : ℚ)) = _
      rw [hval (p : Nat.Primes), dif_pos p.2.1, hn']
      simp only [dif_pos p.2.2]
    exact_mod_cast hz
  show Multiplicative.ofAdd (deningerLogOrdFun P U ⟨q, hmem⟩) = N
  rw [hfun, hn]
  rfl

/-- **The kernel of the characteristic map** is the group of units. -/
theorem deningerArithLog_ker (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (m : deningerLogSub P U) :
    deningerLogOrd P U m = 1 ↔ IsUnit (deningerLogHom P U m) := by
  rw [deningerLogOrd_eq_one_iff, deningerArithRing_isUnit_iff]
  exact ⟨fun h => ⟨Units.ne_zero _, h⟩, fun h => h.2⟩

/-- **The fibres of the characteristic map are the orbits of the units**: this is the unique
decomposition `u p^n` of a section of the divisorial log structure. -/
theorem deningerArithLog_orbit (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (m n : deningerLogSub P U) (h : deningerLogOrd P U m = deningerLogOrd P U n) :
    ∃ w : deningerLogSub P U, IsUnit (deningerLogHom P U w) ∧ m = n * w := by
  have hval : ∀ p : Nat.Primes, deningerClosedPt p ∈ U →
      padicValRat ((p : ℕ)) ((m : ℚˣ) : ℚ) = padicValRat ((p : ℕ)) ((n : ℚˣ) : ℚ) := by
    intro p hp
    by_cases hP : p ∈ P
    · have h0 : deningerLogOrdFun P U m ⟨p, hP, hp⟩ = deningerLogOrdFun P U n ⟨p, hP, hp⟩ :=
        congrArg (fun t : Multiplicative (deningerLogIdx P U → ℕ) =>
          Multiplicative.toAdd t ⟨p, hP, hp⟩) h
      have h1 := deningerLogOrdFun_coe P U m ⟨p, hP, hp⟩
      have h2 := deningerLogOrdFun_coe P U n ⟨p, hP, hp⟩
      rw [h0] at h1
      exact h1.symm.trans h2
    · rw [(m.2 p hp).2 hP, (n.2 p hp).2 hP]
  have hzero : ∀ p : Nat.Primes, deningerClosedPt p ∈ U →
      padicValRat ((p : ℕ)) ((((n : ℚˣ)⁻¹ * (m : ℚˣ) : ℚˣ)) : ℚ) = 0 := by
    intro p hp
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [Units.val_mul, padicValRat.mul (Units.ne_zero _) (Units.ne_zero _),
      Units.val_inv_eq_inv_val, padicValRat.inv, hval p hp, neg_add_cancel]
  have hwmem : ((n : ℚˣ)⁻¹ * (m : ℚˣ)) ∈ deningerLogSub P U := by
    intro p hp
    rw [hzero p hp]
    exact ⟨le_rfl, fun _ => rfl⟩
  refine ⟨(⟨(n : ℚˣ)⁻¹ * (m : ℚˣ), hwmem⟩ : deningerLogSub P U), ?_, ?_⟩
  · refine (deningerArithRing_isUnit_iff U _).2 ⟨?_, hzero⟩
    exact Units.ne_zero ((n : ℚˣ)⁻¹ * (m : ℚˣ))
  · refine Subtype.ext ?_
    show (m : ℚˣ) = (n : ℚˣ) * ((n : ℚˣ)⁻¹ * (m : ℚˣ))
    rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- **The characteristic monoid of the divisorial log structure** is the free commutative monoid on
the primes of `P` lying in the open set. -/
noncomputable def deningerArithLogChar (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    DeningerLogChar (deningerArithPreLog P U) (Multiplicative (deningerLogIdx P U → ℕ)) where
  ord := deningerLogOrd P U
  surj := deningerLogOrd_surjective P U
  ker := fun m => deningerArithLog_ker P U m
  orbit := fun m n h => deningerArithLog_orbit P U m n h

end RHTower
