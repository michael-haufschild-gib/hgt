import GaloisForLFunctions.HTGeometry.BoundedGaugeGenericity
import Mathlib.Tactic.DeriveCountable

/-!
# Countable differential-pattern geometry for prime-log HT sources

For a countable shift palette, every finite differential-algebraic possibility can be described by
a countable rectangular code: a finite injective shift packet, a finite jet-order vector, a finite
injective list of jet monomials, and a polynomial coefficient-degree bound.  The complex
coefficient vectors are deliberately absent from the code.  One determinant rank condition handles
all of them simultaneously.

This module chooses the noncolliding upper evaluation packet supplied by bounded-gauge genericity
for every code, then applies Baire category over the countable code type.  The resulting bounded
prime-log gauge has full actual-differential evaluation rank for every finite pattern at once.
-/

namespace GaloisForLFunctions.HTGeometry

open Topology

/-- Data of a finite rectangular differential pattern before injectivity conditions are imposed. -/
structure RawFiniteDifferentialPattern (Γ : Type*) where
  shiftCount : ℕ
  shiftCode : Fin shiftCount → Γ
  orders : Fin shiftCount → ℕ
  monomialCount : ℕ
  jetExponent : Fin monomialCount → ((Σ i, Fin (orders i)) →₀ ℕ)
  coefficientDegree : ℕ
  deriving Countable

/-- A finite differential pattern has distinct shifts and distinct jet monomials.  Repetitions are
combined before a polynomial relation is encoded, so these are the canonical finite supports. -/
structure FiniteDifferentialPattern (Γ : Type*) extends RawFiniteDifferentialPattern Γ where
  shiftCode_injective : Function.Injective shiftCode
  jetExponent_injective : Function.Injective jetExponent

/-- Finite differential patterns over a countable shift palette form a countable type.  Notice that
no complex coefficient vector occurs in the code. -/
noncomputable instance [Countable Γ] : Countable (FiniteDifferentialPattern Γ) := by
  have h : Function.Injective (FiniteDifferentialPattern.toRawFiniteDifferentialPattern :
      FiniteDifferentialPattern Γ → RawFiniteDifferentialPattern Γ) := by
    intro p q hpq
    cases p
    cases q
    simp_all
  exact h.countable

/-- Column labels: one distinct jet monomial and one coefficient power. -/
abbrev PatternShape {Γ : Type*} (p : FiniteDifferentialPattern Γ) :=
  Fin p.monomialCount × Fin (p.coefficientDegree + 1)

/-- Square evaluation-row type for a finite pattern. -/
abbrev PatternRow {Γ : Type*} (p : FiniteDifferentialPattern Γ) :=
  Fin (Fintype.card (PatternShape p))

/-- Polynomial coefficient degree belonging to an expanded pattern column. -/
noncomputable def patternDegree {Γ : Type*} (p : FiniteDifferentialPattern Γ) :
    PatternRow p → ℕ :=
  fun b ↦ ((Fintype.equivFin (PatternShape p)).symm b).2.val

/-- Jet-monomial exponent belonging to an expanded pattern column. -/
noncomputable def patternExponent {Γ : Type*} (p : FiniteDifferentialPattern Γ) :
    PatternRow p → ((Σ i, Fin (p.orders i)) →₀ ℕ) :=
  fun b ↦ p.jetExponent ((Fintype.equivFin (PatternShape p)).symm b).1

/-- Row-by-shift evaluation nodes belonging to a chosen base packet. -/
def patternNodes {Γ : Type*} (shiftValue : Γ → ℂ)
    (p : FiniteDifferentialPattern Γ) (base : PatternRow p → ℂ) :
    PatternRow p × Fin p.shiftCount → ℂ :=
  fun x ↦ base x.1 + shiftValue (p.shiftCode x.2)

/-- A witness consists of one noncolliding upper evaluation packet and its closed nowhere-dense
actual-differential rank-defect stratum. -/
def PatternWitness {Γ : Type*} (shiftValue : Γ → ℂ)
    (p : FiniteDifferentialPattern Γ) :=
  {base : PatternRow p → ℂ //
    Function.Injective (patternNodes shiftValue p base) ∧
    (∀ x, 0 < (patternNodes shiftValue p base x).im) ∧
    IsClosed (actualCoefficientPatternRankDefect
      (patternNodes shiftValue p base) p.orders base
      (patternDegree p) (patternExponent p)) ∧
    IsNowhereDense (actualCoefficientPatternRankDefect
      (patternNodes shiftValue p base) p.orders base
      (patternDegree p) (patternExponent p))}

theorem patternWitness_nonempty {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) : Nonempty (PatternWitness shiftValue p) := by
  have hshift : Function.Injective (fun i ↦ shiftValue (p.shiftCode i)) :=
    hshiftValue.comp p.shiftCode_injective
  obtain ⟨base, hnodes, hupper, hclosed, hnowhere⟩ :=
    exists_primeLog_actualCoefficientPattern_closed_nowhereDense
      p.coefficientDegree (fun i ↦ shiftValue (p.shiftCode i)) hshift
      p.orders p.jetExponent p.jetExponent_injective
  exact ⟨⟨base, hnodes, hupper, hclosed, hnowhere⟩⟩

/-- A simultaneous choice of one admissible evaluation packet for each finite code. -/
noncomputable def patternWitness {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) : PatternWitness shiftValue p :=
  Classical.choice (patternWitness_nonempty shiftValue hshiftValue p)

noncomputable def patternBase {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) : PatternRow p → ℂ :=
  (patternWitness shiftValue hshiftValue p).val

/-- The actual-differential rank-defect stratum selected for one finite code. -/
noncomputable def patternDefect {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) : Set PrimeLogBoundedGauge :=
  actualCoefficientPatternRankDefect
    (patternNodes shiftValue p (patternBase shiftValue hshiftValue p)) p.orders
    (patternBase shiftValue hshiftValue p) (patternDegree p) (patternExponent p)

theorem patternDefect_isClosed {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) :
    IsClosed (patternDefect shiftValue hshiftValue p) := by
  simpa [patternDefect, patternBase] using
    (patternWitness shiftValue hshiftValue p).property.2.2.1

theorem patternDefect_isNowhereDense {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) :
    IsNowhereDense (patternDefect shiftValue hshiftValue p) := by
  simpa [patternDefect, patternBase] using
    (patternWitness shiftValue hshiftValue p).property.2.2.2

theorem patternDefect_compl_isOpen_dense {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) :
    IsOpen (patternDefect shiftValue hshiftValue p)ᶜ ∧
      Dense (patternDefect shiftValue hshiftValue p)ᶜ := by
  rw [← isClosed_isNowhereDense_iff_compl]
  exact ⟨patternDefect_isClosed shiftValue hshiftValue p,
    patternDefect_isNowhereDense shiftValue hshiftValue p⟩

/-- Avoiding the selected defect is exactly full rank of its actual-differential expanded matrix. -/
theorem not_mem_patternDefect_iff_fullRank
    {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) (u : PrimeLogBoundedGauge) :
    u ∉ patternDefect shiftValue hshiftValue p ↔
      IsUnit (Matrix.of fun a b ↦
        patternBase shiftValue hshiftValue p a ^ patternDegree p b *
          (patternExponent p b).prod (fun i e ↦
            actualRowJetPacket
              (patternNodes shiftValue p (patternBase shiftValue hshiftValue p))
              p.orders u (a, i) ^ e) :
        Matrix (PatternRow p) (PatternRow p) ℂ) := by
  simp [patternDefect, actualCoefficientPatternRankDefect,
    coefficientPatternRankDefect]

/-- **Countable simultaneous differential fullness.** For every countable injective complex shift
palette, the bounded prime-log gauges avoiding every finite differential-pattern defect form a
dense residual set. -/
theorem universalPatternFullness_dense_residual
    {Γ : Type*} [Countable Γ] (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue) :
    Dense {u : PrimeLogBoundedGauge |
      ∀ p : FiniteDifferentialPattern Γ,
        u ∉ patternDefect shiftValue hshiftValue p} ∧
    {u : PrimeLogBoundedGauge |
      ∀ p : FiniteDifferentialPattern Γ,
        u ∉ patternDefect shiftValue hshiftValue p} ∈ residual PrimeLogBoundedGauge := by
  let D : FiniteDifferentialPattern Γ → Set PrimeLogBoundedGauge :=
    patternDefect shiftValue hshiftValue
  have hopen : ∀ p, IsOpen (D p)ᶜ := fun p ↦
    (patternDefect_isClosed shiftValue hshiftValue p).isOpen_compl
  have hdense : ∀ p, Dense (D p)ᶜ := fun p ↦
    (patternDefect_compl_isOpen_dense shiftValue hshiftValue p).2
  have hset : {u : PrimeLogBoundedGauge |
      ∀ p : FiniteDifferentialPattern Γ,
        u ∉ patternDefect shiftValue hshiftValue p} = ⋂ p, (D p)ᶜ := by
    ext u
    simp [D]
  rw [hset]
  exact ⟨dense_iInter_of_isOpen hopen hdense,
    countable_iInter_mem.mpr
      (fun p ↦ residual_of_dense_open (hopen p) (hdense p))⟩

theorem exists_universalPatternFullGauge
    {Γ : Type*} [Countable Γ] (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue) :
    ∃ u : PrimeLogBoundedGauge,
      ∀ p : FiniteDifferentialPattern Γ,
        u ∉ patternDefect shiftValue hshiftValue p :=
  (universalPatternFullness_dense_residual shiftValue hshiftValue).1.nonempty

/-- A single bounded gauge whose actual differential expanded matrix has full rank for every
finite pattern on the countable shift palette. -/
theorem exists_universalPatternFullRankGauge
    {Γ : Type*} [Countable Γ] (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue) :
    ∃ u : PrimeLogBoundedGauge,
      ∀ p : FiniteDifferentialPattern Γ,
        IsUnit (Matrix.of fun a b ↦
          patternBase shiftValue hshiftValue p a ^ patternDegree p b *
            (patternExponent p b).prod (fun i e ↦
              actualRowJetPacket
                (patternNodes shiftValue p (patternBase shiftValue hshiftValue p))
                p.orders u (a, i) ^ e) :
          Matrix (PatternRow p) (PatternRow p) ℂ) := by
  obtain ⟨u, hu⟩ := exists_universalPatternFullGauge shiftValue hshiftValue
  exact ⟨u, fun p ↦
    (not_mem_patternDefect_iff_fullRank shiftValue hshiftValue p u).mp (hu p)⟩

/-- Value of one expanded differential monomial at an arbitrary common evaluation base. -/
noncomputable def patternExpandedValue
    {Γ : Type*} (shiftValue : Γ → ℂ)
    (p : FiniteDifferentialPattern Γ) (u : PrimeLogBoundedGauge)
    (z : ℂ) (b : PatternRow p) : ℂ :=
  z ^ patternDegree p b *
    (patternExponent p b).prod (fun s e ↦
      (primeLogDifferentialJetPacket (fun q ↦ u q)
        (fun i ↦ z + shiftValue (p.shiftCode i)) p.orders s) ^ e)

theorem patternExpandedValue_at_patternBase
    {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) (u : PrimeLogBoundedGauge)
    (a b : PatternRow p) :
    patternExpandedValue shiftValue p u
      (patternBase shiftValue hshiftValue p a) b =
      patternBase shiftValue hshiftValue p a ^ patternDegree p b *
        (patternExponent p b).prod (fun i e ↦
          actualRowJetPacket
            (patternNodes shiftValue p (patternBase shiftValue hshiftValue p))
            p.orders u (a, i) ^ e) := by
  rfl

/-- Full rank forces every coefficient of an expanded finite differential pattern to vanish. -/
theorem patternCoefficients_eq_zero_of_fullRank
    {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) (u : PrimeLogBoundedGauge)
    (hfull : u ∉ patternDefect shiftValue hshiftValue p)
    (c : PatternRow p → ℂ)
    (hvanish : ∀ a : PatternRow p,
      ∑ b, c b * patternExpandedValue shiftValue p u
        (patternBase shiftValue hshiftValue p a) b = 0) :
    ∀ b, c b = 0 := by
  let f : PatternRow p → PatternRow p → ℂ := fun b z ↦
    patternExpandedValue shiftValue p u
      (patternBase shiftValue hshiftValue p z) b
  apply coefficients_eq_zero_of_fullRank_evaluation_packet f id
    ((not_mem_patternDefect_iff_fullRank shiftValue hshiftValue p u).mp hfull)
    c
  intro a
  simpa [f] using hvanish a

/-- A polynomial-coefficient differential relation carried by one finite rectangle and valid on
its common upper domain. -/
def PatternRelationHolds
    {Γ : Type*} (shiftValue : Γ → ℂ)
    (p : FiniteDifferentialPattern Γ) (u : PrimeLogBoundedGauge)
    (c : PatternRow p → ℂ) : Prop :=
  ∀ z : ℂ, (∀ i : Fin p.shiftCount,
    0 < (z + shiftValue (p.shiftCode i)).im) →
      ∑ b, c b * patternExpandedValue shiftValue p u z b = 0

/-- **Finite-pattern relation rigidity.** Outside the selected defect, every functional
polynomial-coefficient differential relation on the encoded translate rectangle is the zero
relation. -/
theorem patternRelation_coefficients_eq_zero
    {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue)
    (p : FiniteDifferentialPattern Γ) (u : PrimeLogBoundedGauge)
    (hfull : u ∉ patternDefect shiftValue hshiftValue p)
    (c : PatternRow p → ℂ)
    (hrelation : PatternRelationHolds shiftValue p u c) :
    ∀ b, c b = 0 := by
  apply patternCoefficients_eq_zero_of_fullRank
    shiftValue hshiftValue p u hfull c
  intro a
  apply hrelation
  intro i
  simpa [patternBase, patternNodes] using
    (patternWitness shiftValue hshiftValue p).property.2.1 (a, i)

/-- Polynomial-coefficient differential freeness on every finite rectangle cut from a shift
palette.  This is the functional constraint-side predicate delivered directly by the determinant
geometry; no individual complex coefficient relation is enumerated. -/
def CountableShiftPolynomialDifferentialFree
    {Γ : Type*} (shiftValue : Γ → ℂ) (u : PrimeLogBoundedGauge) : Prop :=
  ∀ (p : FiniteDifferentialPattern Γ) (c : PatternRow p → ℂ),
    PatternRelationHolds shiftValue p u c → ∀ b, c b = 0

theorem countableShiftPolynomialDifferentialFree_of_avoidsPatterns
    {Γ : Type*} (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue) (u : PrimeLogBoundedGauge)
    (hu : ∀ p : FiniteDifferentialPattern Γ,
      u ∉ patternDefect shiftValue hshiftValue p) :
    CountableShiftPolynomialDifferentialFree shiftValue u := by
  intro p c hrelation
  exact patternRelation_coefficients_eq_zero
    shiftValue hshiftValue p u (hu p) c hrelation

/-- **Countable-shift polynomial differential freeness law.** For every countable injective
complex shift palette, the bounded gauges whose prime-log sources satisfy no nonzero finite
polynomial-coefficient differential relation on that palette form a dense residual set. -/
theorem countableShiftPolynomialDifferentialFree_dense_residual
    {Γ : Type*} [Countable Γ] (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue) :
    Dense {u : PrimeLogBoundedGauge |
      CountableShiftPolynomialDifferentialFree shiftValue u} ∧
    {u : PrimeLogBoundedGauge |
      CountableShiftPolynomialDifferentialFree shiftValue u} ∈
        residual PrimeLogBoundedGauge := by
  let U : Set PrimeLogBoundedGauge := {u |
    ∀ p : FiniteDifferentialPattern Γ,
      u ∉ patternDefect shiftValue hshiftValue p}
  let F : Set PrimeLogBoundedGauge := {u |
    CountableShiftPolynomialDifferentialFree shiftValue u}
  have hUF : U ⊆ F := by
    intro u hu
    exact countableShiftPolynomialDifferentialFree_of_avoidsPatterns
      shiftValue hshiftValue u hu
  have hU := universalPatternFullness_dense_residual shiftValue hshiftValue
  exact ⟨hU.1.mono hUF, Filter.mem_of_superset hU.2 hUF⟩

theorem exists_countableShiftPolynomialDifferentialFree
    {Γ : Type*} [Countable Γ] (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue) :
    ∃ u : PrimeLogBoundedGauge,
      CountableShiftPolynomialDifferentialFree shiftValue u :=
  (countableShiftPolynomialDifferentialFree_dense_residual
    shiftValue hshiftValue).1.nonempty

end GaloisForLFunctions.HTGeometry
