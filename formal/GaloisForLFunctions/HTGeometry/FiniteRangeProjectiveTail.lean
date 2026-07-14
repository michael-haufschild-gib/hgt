import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern
import GaloisForLFunctions.HTGeometry.FiniteEvaluationPacket

/-!
# Finite-range projective-tail differential matroids

This module removes the Boolean-sign restriction from the prime-Dirichlet tail algebra.  For a
finite family of arbitrary complex coefficient functions with finite joint range, tail
independence is exactly spanning by the joint values that recur infinitely often.  The same
recurring-value condition propagates through every finite shift--jet rectangle as soon as the
underlying shift--clock functions are rigid on infinite fibres.

The latter rigidity is deliberately an explicit boundary: in the Dirichlet-series application it
is supplied by the classical uniqueness theorem for finite exponential-polynomial sums with
distinct real shift parts.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The joint coefficient value displayed by a finite source family at one coordinate. -/
def coefficientPattern {J P : Type*} (c : J → P → ℂ) (p : P) : J → ℂ :=
  fun j => c j p

/-- The joint values that occur infinitely often span the complete coefficient space.  The
annihilator formulation avoids a basis choice and is valid over an arbitrary finite index type. -/
def RecurringCoefficientPatternsSpan {J P : Type*} [Fintype J]
    (c : J → P → ℂ) : Prop :=
  ∀ a : J → ℂ,
    (∀ b : J → ℂ,
      {p | coefficientPattern c p = b}.Infinite →
        ∑ j, a j * b j = 0) →
    a = 0

/-- **Finite-range tail law.**  For a finite source family whose joint coefficient function has
finite range, independence modulo finite support is equivalent to spanning by the joint values
that recur infinitely often. -/
theorem tailCoefficientIndependent_iff_recurringPatternsSpan_of_finiteRange
    {J P : Type*} [Fintype J] (c : J → P → ℂ)
    (hrange : (Set.range (coefficientPattern c)).Finite) :
    TailCoefficientIndependent c ↔ RecurringCoefficientPatternsSpan c := by
  classical
  constructor
  · intro htail a hrec
    let bad : Set (J → ℂ) := {b | ∑ j, a j * b j ≠ 0}
    have hbad : (Set.range (coefficientPattern c) ∩ bad).Finite :=
      hrange.inter_of_left bad
    have hfibre : ∀ b ∈ Set.range (coefficientPattern c) ∩ bad,
        {p | coefficientPattern c p = b}.Finite := by
      intro b hb
      have hninf : ¬ {p | coefficientPattern c p = b}.Infinite := by
        intro hinf
        exact hb.2 (hrec b hinf)
      simpa only [Set.not_infinite] using hninf
    have hunion :
        (⋃ b ∈ Set.range (coefficientPattern c) ∩ bad,
          {p | coefficientPattern c p = b}).Finite :=
      hbad.biUnion hfibre
    apply htail a
    apply hunion.subset
    intro p hp
    have hrangeP : coefficientPattern c p ∈ Set.range (coefficientPattern c) :=
      ⟨p, rfl⟩
    have hbadP : coefficientPattern c p ∈ bad := by
      simpa only [bad, Set.mem_setOf_eq, coefficientPattern] using hp
    refine Set.mem_iUnion₂.mpr
      ⟨coefficientPattern c p, ⟨hrangeP, hbadP⟩, ?_⟩
    simp
  · intro hspan a hsupp
    apply hspan a
    intro b hinf
    by_contra hne
    have hsub : {p | coefficientPattern c p = b} ⊆
        {p | ∑ j, a j * c j p ≠ 0} := by
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      have hpoint : ∀ j, c j p = b j := fun j => congrFun hp j
      simpa only [hpoint] using hne
    exact (hinf.mono hsub) hsupp

/-- Rigidity of an arbitrary finite family of shift factors and clock powers on every infinite
coordinate fibre.  For `factor a p = exp (-shift a * log p)`, this is the classical uniqueness of
finite exponential-polynomial sums when the real parts of the shifts are distinct. -/
def FactorClockFiberIndependent {A P : Type*} [Fintype A]
    (factor : A → P → ℂ) (clock : P → ℂ) (m : ℕ) : Prop :=
  ∀ U : Set P, U.Infinite → ∀ d : A × Fin (m + 1) → ℂ,
    {p | p ∈ U ∧
      ∑ ak, d ak * factor ak.1 p * clock p ^ (ak.2 : ℕ) ≠ 0}.Finite →
    d = 0

/-- The coefficient column carrying a source coordinate, a shift factor, and a logarithmic jet
order. -/
def coefficientShiftJet {J A P : Type*}
    (c : J → P → ℂ) (factor : A → P → ℂ) (clock : P → ℂ) (m : ℕ)
    (jak : J × (A × Fin (m + 1))) (p : P) : ℂ :=
  c jak.1 p * factor jak.2.1 p * clock p ^ (jak.2.2 : ℕ)

/-- Tail independence is stronger than ordinary linear independence of the coefficient
functions. -/
theorem TailCoefficientIndependent.linearIndependent
    {I P : Type*} [Fintype I] (a : I → P → ℂ)
    (h : TailCoefficientIndependent a) :
    LinearIndependent ℂ a := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro q hq
  have hzero : ∀ p, ∑ i, q i * a i p = 0 := by
    intro p
    have hp := congrFun hq p
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hp
  have hfinite : {p | ∑ i, q i * a i p ≠ 0}.Finite := by
    simp only [hzero, ne_eq, not_true_eq_false, Set.setOf_false]
    exact Set.finite_empty
  have hq0 := h q hfinite
  exact fun i => congrFun hq0 i

/-- **Finite Jacobian probe.**  A tail-independent coefficient family admits a square packet of
coordinates whose evaluation matrix is a unit.  This is the finite linear-algebra input required
by the Shapiro--Sparer arithmetic-function Jacobian criterion. -/
theorem TailCoefficientIndependent.exists_fullRank_evaluation_packet
    {I P : Type*} [Fintype I] [DecidableEq I]
    (a : I → P → ℂ) (h : TailCoefficientIndependent a) :
    ∃ points : I → P,
      IsUnit (Matrix.of fun row i => a i (points row) : Matrix I I ℂ) :=
  GaloisForLFunctions.HTGeometry.exists_fullRank_evaluation_packet a
    (h.linearIndependent a)

/-- **Finite-range shift--jet law.**  Recurring joint coefficient values and rigidity of the
shift--clock functions force full tail rank for the complete source--shift--jet rectangle. -/
theorem coefficientShiftJet_tailIndependent_of_recurringPatternsSpan
    {J A P : Type*} [Fintype J] [Fintype A]
    (c : J → P → ℂ) (factor : A → P → ℂ) (clock : P → ℂ)
    (hspan : RecurringCoefficientPatternsSpan c)
    (m : ℕ) (hrigid : FactorClockFiberIndependent factor clock m) :
    TailCoefficientIndependent (coefficientShiftJet c factor clock m) := by
  classical
  intro q hsupp
  have hcolumn : ∀ ak : A × Fin (m + 1), (fun j => q (j, ak)) = 0 := by
    intro ak
    apply hspan (fun j => q (j, ak))
    intro b hb
    let U : Set P := {p | coefficientPattern c p = b}
    let d : A × Fin (m + 1) → ℂ := fun rk => ∑ j, q (j, rk) * b j
    have hd : d = 0 := by
      apply hrigid U hb d
      apply hsupp.subset
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      rcases hp with ⟨hpPattern, hpne⟩
      have hpoint : ∀ j, c j p = b j := fun j => congrFun hpPattern j
      intro hzero
      apply hpne
      calc
        ∑ rk : A × Fin (m + 1),
              (∑ j, q (j, rk) * b j) * factor rk.1 p * clock p ^ (rk.2 : ℕ) =
            ∑ jak, q jak * coefficientShiftJet c factor clock m jak p := by
              conv_rhs =>
                rw [Fintype.sum_prod_type]
                rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro rk _
              rw [Finset.sum_mul, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              simp only [coefficientShiftJet]
              rw [hpoint j]
              ring
        _ = 0 := hzero
    have hak := congrFun hd ak
    simpa only [d, Pi.zero_apply] using hak
  funext jak
  have hjak := congrFun (hcolumn jak.2) jak.1
  simpa using hjak

/-- The finite-range criterion in its direct form: tail independence of the source coefficients
implies full shift--jet tail independence under the classical fibre-rigidity input. -/
theorem coefficientShiftJet_tailIndependent_of_finiteRange
    {J A P : Type*} [Fintype J] [Fintype A]
    (c : J → P → ℂ) (factor : A → P → ℂ) (clock : P → ℂ)
    (hrange : (Set.range (coefficientPattern c)).Finite)
    (htail : TailCoefficientIndependent c)
    (m : ℕ) (hrigid : FactorClockFiberIndependent factor clock m) :
    TailCoefficientIndependent (coefficientShiftJet c factor clock m) :=
  coefficientShiftJet_tailIndependent_of_recurringPatternsSpan c factor clock
    ((tailCoefficientIndependent_iff_recurringPatternsSpan_of_finiteRange c hrange).mp htail)
    m hrigid

/-- A finite shift palette contains a factor that vanishes at no coordinate. -/
def HasNowhereZeroFactor {A P : Type*} (factor : A → P → ℂ) : Prop :=
  ∃ a₀ : A, ∀ p, factor a₀ p ≠ 0

/-- Full rank of a shift--jet rectangle containing one nowhere-zero shift factor already forces
tail independence of the original coefficient family. -/
theorem tailCoefficientIndependent_of_coefficientShiftJet
    {J A P : Type*} [Fintype J] [Fintype A] [Nonempty A]
    (c : J → P → ℂ) (factor : A → P → ℂ) (clock : P → ℂ)
    (m : ℕ) (hnz : HasNowhereZeroFactor factor)
    (hfull : TailCoefficientIndependent (coefficientShiftJet c factor clock m)) :
    TailCoefficientIndependent c := by
  classical
  obtain ⟨a₀, ha₀⟩ := hnz
  intro q hsupp
  let q' : J × (A × Fin (m + 1)) → ℂ := fun jak =>
    if jak.2 = (a₀, 0) then q jak.1 else 0
  have hsupport :
      {p | ∑ jak, q' jak * coefficientShiftJet c factor clock m jak p ≠ 0}.Finite := by
    apply hsupp.subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    intro hbase
    apply hp
    rw [Fintype.sum_prod_type]
    simp only [q', coefficientShiftJet]
    simp
    calc
      ∑ j, q j * (c j p * factor a₀ p) =
          ∑ j, (q j * c j p) * factor a₀ p := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j, q j * c j p) * factor a₀ p := by rw [Finset.sum_mul]
      _ = 0 := by rw [hbase, zero_mul]
  have hq' := hfull q' hsupport
  funext j
  have hzero := congrFun hq' (j, a₀, 0)
  simpa only [q', if_pos rfl, Pi.zero_apply] using hzero

/-- **Exact finite-range projective-tail shift--jet criterion.**  When one nowhere-zero shift factor
is present, the complete finite shift--jet rectangle is tail-independent exactly when the original
finite-range coefficient family is tail-independent. -/
theorem coefficientShiftJet_tailIndependent_iff_of_finiteRange
    {J A P : Type*} [Fintype J] [Fintype A] [Nonempty A]
    (c : J → P → ℂ) (factor : A → P → ℂ) (clock : P → ℂ)
    (hrange : (Set.range (coefficientPattern c)).Finite)
    (hnz : HasNowhereZeroFactor factor)
    (m : ℕ) (hrigid : FactorClockFiberIndependent factor clock m) :
    TailCoefficientIndependent (coefficientShiftJet c factor clock m) ↔
      TailCoefficientIndependent c := by
  constructor
  · exact tailCoefficientIndependent_of_coefficientShiftJet c factor clock m hnz
  · intro htail
    exact coefficientShiftJet_tailIndependent_of_finiteRange c factor clock
      hrange htail m hrigid

/-- The complete operator-tail condition: every finite shift--jet rectangle has full tail rank. -/
def CompleteShiftJetTailIndependent
    {J A P : Type*} [Fintype J] [Fintype A]
    (c : J → P → ℂ) (factor : A → P → ℂ) (clock : P → ℂ) : Prop :=
  ∀ m : ℕ, TailCoefficientIndependent (coefficientShiftJet c factor clock m)

/-- **Complete finite-range collapse law.**  If every finite shift--clock system is rigid on
infinite fibres and one shift factor is nowhere zero, then the complete operator-tail condition
collapses exactly to scalar tail independence of the finite-range source coefficients. -/
theorem completeShiftJetTailIndependent_iff_of_finiteRange
    {J A P : Type*} [Fintype J] [Fintype A] [Nonempty A]
    (c : J → P → ℂ) (factor : A → P → ℂ) (clock : P → ℂ)
    (hrange : (Set.range (coefficientPattern c)).Finite)
    (hnz : HasNowhereZeroFactor factor)
    (hrigid : ∀ m : ℕ, FactorClockFiberIndependent factor clock m) :
    CompleteShiftJetTailIndependent c factor clock ↔ TailCoefficientIndependent c := by
  constructor
  · intro hcomplete
    exact tailCoefficientIndependent_of_coefficientShiftJet c factor clock 0 hnz
      (hcomplete 0)
  · intro htail m
    exact coefficientShiftJet_tailIndependent_of_finiteRange c factor clock
      hrange htail m (hrigid m)

end

end GaloisForLFunctions.HTGeometry
