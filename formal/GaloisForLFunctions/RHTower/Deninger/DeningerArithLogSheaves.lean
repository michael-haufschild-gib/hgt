import GaloisForLFunctions.RHTower.Deninger.DeningerArithDivisorialLog

/-!
# The divisorial log structure as a sheaf on the arithmetic curve

The divisorial log structure of a finite set of primes and the sheaf of units are sheaves of
commutative monoids on the arithmetic curve: their sections over an open set are the constant
rational units subject to the pointwise valuation conditions, and constants glue because the generic
point lies in every nonempty open set.

* `deningerLogMulCond`, `deningerUnitMulCond` : the pointwise conditions.
* `deningerLogSheaf`, `deningerUnitSheaf` : the sheaves.
* `deningerLogSection_mem` : a section is a constant lying in the divisorial log structure.
-/

namespace RHTower

open TopologicalSpace CategoryTheory

/-- The pointwise condition defining the sheaf of units: all valuations vanish. -/
def deningerUnitMulCond : DeningerMulCond deningerArithBase ℚˣ where
  cond x q := ∀ p : Nat.Primes, x = deningerClosedPt p → padicValRat ((p : ℕ)) ((q : ℚ)) = 0
  one_mem := by
    intro x p _
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [Units.val_one, padicValRat.one]
  mul_mem := by
    intro x a b ha hb p hxp
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [Units.val_mul, padicValRat.mul (Units.ne_zero _) (Units.ne_zero _), ha p hxp, hb p hxp,
      add_zero]

/-- The pointwise condition defining the divisorial log structure of `P`. -/
def deningerLogMulCond (P : Finset Nat.Primes) : DeningerMulCond deningerArithBase ℚˣ where
  cond x q := ∀ p : Nat.Primes, x = deningerClosedPt p →
    0 ≤ padicValRat ((p : ℕ)) ((q : ℚ)) ∧ (p ∉ P → padicValRat ((p : ℕ)) ((q : ℚ)) = 0)
  one_mem := by
    intro x p _
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [Units.val_one, padicValRat.one]
    exact ⟨le_rfl, fun _ => rfl⟩
  mul_mem := by
    intro x a b ha hb p hxp
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [Units.val_mul, padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]
    exact ⟨add_nonneg (ha p hxp).1 (hb p hxp).1, fun hP => by
      rw [(ha p hxp).2 hP, (hb p hxp).2 hP, add_zero]⟩

/-- **The sheaf of units of the arithmetic curve.** -/
def deningerUnitSheaf : TopCat.Sheaf CommMonCat.{0} deningerArithBase :=
  deningerUnitMulCond.sheaf deningerGenericPt_isGeneric

/-- **The divisorial log structure of `P`, as a sheaf of commutative monoids.** -/
def deningerLogSheaf (P : Finset Nat.Primes) : TopCat.Sheaf CommMonCat.{0} deningerArithBase :=
  (deningerLogMulCond P).sheaf deningerGenericPt_isGeneric

/-- The value of a section at a point of the open set. -/
def deningerLogSectionVal {P : Finset Nat.Primes} {U : Opens deningerArithBase}
    (s : (deningerLogMulCond P).sub U) (x : ↥U) : ℚˣ := (s : ↥U → ℚˣ) x

theorem deningerLogSectionVal_const {P : Finset Nat.Primes} {U : Opens deningerArithBase}
    (s : (deningerLogMulCond P).sub U) (x y : ↥U) :
    deningerLogSectionVal s x = deningerLogSectionVal s y := s.2.1 x y

/-- **A section of the divisorial log structure is a constant lying in it.** -/
theorem deningerLogSection_mem {P : Finset Nat.Primes} {U : Opens deningerArithBase}
    (s : (deningerLogMulCond P).sub U) (x : ↥U) :
    deningerLogSectionVal s x ∈ deningerLogSub P U := by
  intro p hp
  have hcond := s.2.2 ⟨deningerClosedPt p, hp⟩ p rfl
  have hval : (s : ↥U → ℚˣ) ⟨deningerClosedPt p, hp⟩ = deningerLogSectionVal s x := s.2.1 _ x
  rw [hval] at hcond
  exact hcond

theorem deningerUnitSection_mem {U : Opens deningerArithBase}
    (s : deningerUnitMulCond.sub U) (x : ↥U) (p : Nat.Primes) (hp : deningerClosedPt p ∈ U) :
    padicValRat ((p : ℕ)) (((s : ↥U → ℚˣ) x : ℚˣ) : ℚ) = 0 := by
  have hcond := s.2.2 ⟨deningerClosedPt p, hp⟩ p rfl
  have hval : (s : ↥U → ℚˣ) ⟨deningerClosedPt p, hp⟩ = (s : ↥U → ℚˣ) x := s.2.1 _ x
  rw [hval] at hcond
  exact hcond

/-- The constant section attached to an element of the divisorial log structure. -/
def deningerLogConstSection {P : Finset Nat.Primes} {U : Opens deningerArithBase}
    (q : deningerLogSub P U) : (deningerLogMulCond P).sub U :=
  ⟨fun _ => (q : ℚˣ), fun _ _ => rfl, fun x p hxp => by
    have hp : deningerClosedPt p ∈ U := hxp ▸ x.2
    exact q.2 p hp⟩

@[simp]
theorem deningerLogConstSection_val {P : Finset Nat.Primes} {U : Opens deningerArithBase}
    (q : deningerLogSub P U) (x : ↥U) :
    deningerLogSectionVal (deningerLogConstSection q) x = (q : ℚˣ) := rfl

/-- **Sections of the divisorial log structure are exactly its elements**, on a nonempty open
set. -/
theorem deningerLogSection_ext {P : Finset Nat.Primes} {U : Opens deningerArithBase}
    (s t : (deningerLogMulCond P).sub U)
    (h : ∀ x : ↥U, deningerLogSectionVal s x = deningerLogSectionVal t x) : s = t :=
  Subtype.ext (funext h)

end RHTower
