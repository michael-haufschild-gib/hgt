import GaloisForLFunctions.RHTower.Deninger.DeningerLogCharacteristicSheaf

/-!
# The groupified Kummer sequence of the divisorial log structure

Groupifying the divisorial log structure gives the rational units that are invertible away from
`P`.  Over every open set of the arithmetic curve the valuations along `P` fit into a short exact
sequence

`0 → 𝒪ˣ(U) → M_P^{gp}(U) → ⨁_{p ∈ P, p ∈ U} ℤ → 0`,

with injectivity because the first map is an inclusion of sections, exactness in the middle because
a section whose valuations along `P` vanish has all valuations zero, and surjectivity because every
exponent vector is realized by the corresponding product of prime powers.

* `deningerLogGpAddCond`, `deningerUnitAddCond` : the pointwise conditions.
* `deningerGpResidueHom` : the valuation map on sections.
* `deningerGpResidue_surjective`, `deningerGpResidue_eq_zero_iff` : exactness.
-/

namespace RHTower

open TopologicalSpace CategoryTheory Opposite TopCat

/-- The pointwise condition defining the sheaf of units, additively. -/
def deningerUnitAddCond : DeningerAddCond deningerArithBase (Additive ℚˣ) where
  cond x a := ∀ p : Nat.Primes, x = deningerClosedPt p →
    padicValRat ((p : ℕ)) (((Additive.toMul a : ℚˣ)) : ℚ) = 0
  zero_mem := by
    intro x p _
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [show ((Additive.toMul (0 : Additive ℚˣ) : ℚˣ) : ℚ) = 1 from rfl, padicValRat.one]
  add_mem := by
    intro x a b ha hb p hxp
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [show ((Additive.toMul (a + b) : ℚˣ) : ℚ) =
      ((Additive.toMul a : ℚˣ) : ℚ) * ((Additive.toMul b : ℚˣ) : ℚ) from rfl,
      padicValRat.mul (Units.ne_zero _) (Units.ne_zero _), ha p hxp, hb p hxp, add_zero]
  neg_mem := by
    intro x a ha p hxp
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [show (Additive.toMul (-a) : ℚˣ) = (Additive.toMul a : ℚˣ)⁻¹ from rfl,
      Units.val_inv_eq_inv_val, padicValRat.inv, ha p hxp, neg_zero]

/-- The pointwise condition defining the groupified divisorial log structure of `P`: rational units
invertible away from `P`. -/
def deningerLogGpAddCond (P : Finset Nat.Primes) :
    DeningerAddCond deningerArithBase (Additive ℚˣ) where
  cond x a := ∀ p : Nat.Primes, x = deningerClosedPt p → p ∉ P →
    padicValRat ((p : ℕ)) (((Additive.toMul a : ℚˣ)) : ℚ) = 0
  zero_mem := by
    intro x p _ _
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [show ((Additive.toMul (0 : Additive ℚˣ) : ℚˣ) : ℚ) = 1 from rfl, padicValRat.one]
  add_mem := by
    intro x a b ha hb p hxp hP
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [show ((Additive.toMul (a + b) : ℚˣ) : ℚ) =
      ((Additive.toMul a : ℚˣ) : ℚ) * ((Additive.toMul b : ℚˣ) : ℚ) from rfl,
      padicValRat.mul (Units.ne_zero _) (Units.ne_zero _), ha p hxp hP, hb p hxp hP, add_zero]
  neg_mem := by
    intro x a ha p hxp hP
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [show (Additive.toMul (-a) : ℚˣ) = (Additive.toMul a : ℚˣ)⁻¹ from rfl,
      Units.val_inv_eq_inv_val, padicValRat.inv, ha p hxp hP, neg_zero]

/-- **The sheaf of units, as a sheaf of abelian groups.** -/
def deningerUnitAddSheaf : TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase :=
  deningerUnitAddCond.sheaf deningerGenericPt_isGeneric

/-- **The groupified divisorial log structure, as a sheaf of abelian groups.** -/
def deningerLogGpSheaf (P : Finset Nat.Primes) :
    TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase :=
  (deningerLogGpAddCond P).sheaf deningerGenericPt_isGeneric

variable {P : Finset Nat.Primes} {U : Opens deningerArithBase}

/-- **A unit section is a section of the groupified log structure.** -/
theorem deningerUnitAddSub_le_gpSub (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    deningerUnitAddCond.sub U ≤ (deningerLogGpAddCond P).sub U := by
  rintro f ⟨hconst, hcond⟩
  exact ⟨hconst, fun x p hxp _ => hcond x p hxp⟩

/-- The valuations along `P` of a section of the groupified log structure. -/
def deningerGpResidueFun (s : (deningerLogGpAddCond P).sub U) :
    deningerLogIdx P U → ℤ :=
  fun i => padicValRat (((i : Nat.Primes) : ℕ))
    ((Additive.toMul ((s : ↥U → Additive ℚˣ)
      ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩) : ℚˣ) : ℚ)

/-- The valuations along `P`, as a group homomorphism on sections. -/
def deningerGpResidueHom (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    (deningerLogGpAddCond P).sub U →+ (deningerLogIdx P U → ℤ) where
  toFun := deningerGpResidueFun
  map_zero' := by
    funext i
    haveI : Fact (((i : Nat.Primes) : ℕ)).Prime := ⟨(i : Nat.Primes).2⟩
    show padicValRat (((i : Nat.Primes) : ℕ)) ((1 : ℚˣ) : ℚ) = 0
    rw [Units.val_one, padicValRat.one]
  map_add' a b := by
    funext i
    haveI : Fact (((i : Nat.Primes) : ℕ)).Prime := ⟨(i : Nat.Primes).2⟩
    show padicValRat _ ((Additive.toMul
        (((a : ↥U → Additive ℚˣ) + (b : ↥U → Additive ℚˣ)) _) : ℚˣ) : ℚ) = _
    rw [show ((Additive.toMul (((a : ↥U → Additive ℚˣ) + (b : ↥U → Additive ℚˣ))
        ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩) : ℚˣ) : ℚ) =
      ((Additive.toMul ((a : ↥U → Additive ℚˣ)
        ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩) : ℚˣ) : ℚ) *
      ((Additive.toMul ((b : ↥U → Additive ℚˣ)
        ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩) : ℚˣ) : ℚ) from rfl,
      padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]
    rfl

@[simp]
theorem deningerGpResidueHom_apply (s : (deningerLogGpAddCond P).sub U) :
    deningerGpResidueHom P U s = deningerGpResidueFun s := rfl

/-- **Exactness in the middle**: a section whose valuations along `P` vanish is a unit section. -/
theorem deningerGpResidue_eq_zero_iff (s : (deningerLogGpAddCond P).sub U) :
    deningerGpResidueHom P U s = 0 ↔
      ((s : ↥U → Additive ℚˣ)) ∈ deningerUnitAddCond.sub U := by
  constructor
  · intro h
    refine ⟨s.2.1, fun x p hxp => ?_⟩
    have hp : deningerClosedPt p ∈ U := hxp ▸ x.2
    have hconst : (s : ↥U → Additive ℚˣ) x =
        (s : ↥U → Additive ℚˣ) ⟨deningerClosedPt p, hp⟩ := s.2.1 x _
    rw [hconst]
    by_cases hP : p ∈ P
    · exact congrFun h ⟨p, hP, hp⟩
    · exact s.2.2 ⟨deningerClosedPt p, hp⟩ p rfl hP
  · intro h
    funext i
    exact h.2 ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩ (i : Nat.Primes) rfl

/-- **Surjectivity**: every exponent vector along `P` is the divisor of a rational unit invertible
away from `P`. -/
theorem deningerGpResidue_surjective (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    Function.Surjective (deningerGpResidueHom P U) := by
  classical
  intro n
  set n' : {x : Nat.Primes // x ∈ P} → ℤ := fun x =>
    if h : deningerClosedPt ((x : Nat.Primes)) ∈ U then n ⟨(x : Nat.Primes), x.2, h⟩ else 0
    with hn'
  set q : ℚˣ := deningerSUnitProduct P n' with hq
  have hval : ∀ p : Nat.Primes, padicValRat ((p : ℕ)) ((q : ℚ)) =
      if hp : p ∈ P then n' ⟨p, hp⟩ else 0 := fun p => deningerSUnitProduct_val P n' p
  have hmem : (fun _ : ↥U => (Additive.ofMul q)) ∈ (deningerLogGpAddCond P).sub U := by
    refine ⟨fun _ _ => rfl, fun x p _ hP => ?_⟩
    show padicValRat ((p : ℕ)) ((q : ℚ)) = 0
    rw [hval p, dif_neg hP]
  refine ⟨⟨fun _ => Additive.ofMul q, hmem⟩, ?_⟩
  funext i
  show padicValRat (((i : Nat.Primes) : ℕ)) ((q : ℚ)) = n i
  rw [hval (i : Nat.Primes), dif_pos i.2.1, hn']
  simp only [dif_pos i.2.2]

end RHTower
