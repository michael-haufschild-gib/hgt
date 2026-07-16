import GaloisForLFunctions.HTGeometry.DifferentialPolynomial
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Tactic

/-!
# Generic finite-jet birationality under a time change

Let `D` be a derivation, let `D w = 1`, and put `δ = aD`.  This module proves that the finite
source packet

`w, D^r a (r < m), D^r fᵢ (r ≤ m)`

and the time-changed target packet

`δ^r w (r ≤ m), δ^r fᵢ (r ≤ m)`

are related by an injective polynomial substitution.  The proof constructs the rational inverse
over the universal target fraction field using `D = (δ w)⁻¹δ`, then descends every jet of order at
most `m` to the exact finite source polynomial ring.  Consequently algebraic independence of the
source packet implies algebraic independence of the target packet, for an arbitrary observable
index type.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

abbrev TimeChangeSourceIndex (ι : Type*) :=
  Sum PUnit (Sum ℕ (ι × ℕ))

abbrev TimeChangeTargetIndex (ι : Type*) :=
  (Sum PUnit ι) × ℕ

abbrev TimeChangeSourcePolynomial (K ι : Type*) [CommRing K] :=
  MvPolynomial (TimeChangeSourceIndex ι) K

abbrev TimeChangeTargetPolynomial (K ι : Type*) [CommRing K] :=
  MvPolynomial (TimeChangeTargetIndex ι) K

def timeChangeSourceClockIndex {ι : Type*} : TimeChangeSourceIndex ι :=
  Sum.inl PUnit.unit

def timeChangeSourceScaleIndex {ι : Type*} (n : ℕ) : TimeChangeSourceIndex ι :=
  Sum.inr (Sum.inl n)

def timeChangeSourceObservableIndex {ι : Type*} (i : ι) (n : ℕ) :
    TimeChangeSourceIndex ι :=
  Sum.inr (Sum.inr (i, n))

def timeChangeTargetClockIndex {ι : Type*} (n : ℕ) : TimeChangeTargetIndex ι :=
  (Sum.inl PUnit.unit, n)

def timeChangeTargetObservableIndex {ι : Type*} (i : ι) (n : ℕ) :
    TimeChangeTargetIndex ι :=
  (Sum.inr i, n)

def timeChangeSourceShift
    {K ι : Type*} [CommRing K] (p : TimeChangeSourceIndex ι) :
    TimeChangeSourcePolynomial K ι :=
  match p with
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl n) => MvPolynomial.X (timeChangeSourceScaleIndex (n + 1))
  | Sum.inr (Sum.inr (i, n)) =>
      MvPolynomial.X (timeChangeSourceObservableIndex i (n + 1))

def timeChangeSourceDerivation
    (K ι : Type*) [CommRing K] :
    Derivation K (TimeChangeSourcePolynomial K ι)
      (TimeChangeSourcePolynomial K ι) :=
  MvPolynomial.mkDerivation K (timeChangeSourceShift (K := K))

@[simp] theorem timeChangeSourceDerivation_clock
    {K ι : Type*} [CommRing K] :
    timeChangeSourceDerivation K ι
      (MvPolynomial.X timeChangeSourceClockIndex) = 1 := by
  simp [timeChangeSourceDerivation, timeChangeSourceShift,
    timeChangeSourceClockIndex]

@[simp] theorem timeChangeSourceDerivation_scale
    {K ι : Type*} [CommRing K] (n : ℕ) :
    timeChangeSourceDerivation K ι
      (MvPolynomial.X (timeChangeSourceScaleIndex n)) =
        MvPolynomial.X (timeChangeSourceScaleIndex (n + 1)) := by
  simp [timeChangeSourceDerivation, timeChangeSourceShift,
    timeChangeSourceScaleIndex]

@[simp] theorem timeChangeSourceDerivation_observable
    {K ι : Type*} [CommRing K] (i : ι) (n : ℕ) :
    timeChangeSourceDerivation K ι
      (MvPolynomial.X (timeChangeSourceObservableIndex i n)) =
        MvPolynomial.X (timeChangeSourceObservableIndex i (n + 1)) := by
  simp [timeChangeSourceDerivation, timeChangeSourceShift,
    timeChangeSourceObservableIndex]

def timeChangeSourceScaleVariable
    {K ι : Type*} [CommRing K] : TimeChangeSourcePolynomial K ι :=
  MvPolynomial.X (timeChangeSourceScaleIndex 0)

def timeChangeSourceTimeDerivation
    (K ι : Type*) [CommRing K] :
    Derivation K (TimeChangeSourcePolynomial K ι)
      (TimeChangeSourcePolynomial K ι) :=
  (timeChangeSourceScaleVariable (K := K) (ι := ι)) •
    timeChangeSourceDerivation K ι

def timeChangeSourceSeedVariable
    {K ι : Type*} [CommRing K] (b : Sum PUnit ι) :
    TimeChangeSourcePolynomial K ι :=
  match b with
  | Sum.inl _ => MvPolynomial.X timeChangeSourceClockIndex
  | Sum.inr i => MvPolynomial.X (timeChangeSourceObservableIndex i 0)

def universalTimeChangeJet
    {K ι : Type*} [CommRing K] (b : Sum PUnit ι) (n : ℕ) :
    TimeChangeSourcePolynomial K ι :=
  (timeChangeSourceTimeDerivation K ι)^[n]
    (timeChangeSourceSeedVariable (K := K) b)

theorem universalTimeChangeJet_succ
    {K ι : Type*} [CommRing K] (b : Sum PUnit ι) (n : ℕ) :
    universalTimeChangeJet (K := K) b (n + 1) =
      timeChangeSourceTimeDerivation K ι
        (universalTimeChangeJet (K := K) b n) := by
  simp [universalTimeChangeJet, Function.iterate_succ_apply']

def universalTimeChangeAlgHom
    (K ι : Type*) [CommRing K] :
    TimeChangeTargetPolynomial K ι →ₐ[K] TimeChangeSourcePolynomial K ι :=
  MvPolynomial.aeval fun p => universalTimeChangeJet (K := K) p.1 p.2

@[simp] theorem universalTimeChangeAlgHom_X
    {K ι : Type*} [CommRing K] (p : TimeChangeTargetIndex ι) :
    universalTimeChangeAlgHom K ι (MvPolynomial.X p) =
      universalTimeChangeJet (K := K) p.1 p.2 := by
  simp [universalTimeChangeAlgHom]

abbrev TimeChangeTargetFractionField (K ι : Type*) [Field K] :=
  FractionRing (TimeChangeTargetPolynomial K ι)

def timeChangeTargetEmbedding
    {K ι : Type*} [Field K] :
    TimeChangeTargetPolynomial K ι →ₐ[K] TimeChangeTargetFractionField K ι :=
  IsScalarTower.toAlgHom K (TimeChangeTargetPolynomial K ι)
    (TimeChangeTargetFractionField K ι)

theorem timeChangeTargetEmbedding_injective
    {K ι : Type*} [Field K] :
    Function.Injective (timeChangeTargetEmbedding (K := K) (ι := ι)) :=
  IsFractionRing.injective (TimeChangeTargetPolynomial K ι)
    (TimeChangeTargetFractionField K ι)

@[simp] theorem timeChangeTargetEmbedding_apply
    {K ι : Type*} [Field K] (P : TimeChangeTargetPolynomial K ι) :
    timeChangeTargetEmbedding (K := K) (ι := ι) P =
      algebraMap (TimeChangeTargetPolynomial K ι)
        (TimeChangeTargetFractionField K ι) P := rfl

def timeChangeTargetJet
    {K ι : Type*} [Field K] (b : Sum PUnit ι) (n : ℕ) :
    TimeChangeTargetFractionField K ι :=
  timeChangeTargetEmbedding (K := K) (ι := ι)
    (MvPolynomial.X (b, n))

def timeChangeTargetPolynomialDerivation
    (K ι : Type*) [Field K] :
    Derivation K (TimeChangeTargetPolynomial K ι)
      (TimeChangeTargetFractionField K ι) :=
  MvPolynomial.mkDerivation K fun p =>
    timeChangeTargetJet (K := K) p.1 (p.2 + 1)

def timeChangeTargetDerivation
    (K ι : Type*) [Field K] :
    Derivation K (TimeChangeTargetFractionField K ι)
      (TimeChangeTargetFractionField K ι) :=
  fractionRingDerivation (timeChangeTargetPolynomialDerivation K ι)

@[simp] theorem timeChangeTargetDerivation_jet
    {K ι : Type*} [Field K] (b : Sum PUnit ι) (n : ℕ) :
    timeChangeTargetDerivation K ι (timeChangeTargetJet (K := K) b n) =
      timeChangeTargetJet (K := K) b (n + 1) := by
  rw [timeChangeTargetDerivation, timeChangeTargetJet,
    timeChangeTargetEmbedding_apply, fractionRingDerivation_algebraMap]
  simp [timeChangeTargetPolynomialDerivation]

def timeChangeTargetScale
    {K ι : Type*} [Field K] : TimeChangeTargetFractionField K ι :=
  timeChangeTargetJet (K := K) (Sum.inl PUnit.unit) 1

theorem timeChangeTargetScale_ne_zero
    {K ι : Type*} [Field K] :
    timeChangeTargetScale (K := K) (ι := ι) ≠ 0 := by
  exact (map_ne_zero_iff _
    (timeChangeTargetEmbedding_injective (K := K) (ι := ι))).mpr
      (MvPolynomial.X_ne_zero (R := K)
        (timeChangeTargetClockIndex (ι := ι) 1))

def timeChangeTargetInverseDerivation
    (K ι : Type*) [Field K] :
    Derivation K (TimeChangeTargetFractionField K ι)
      (TimeChangeTargetFractionField K ι) :=
  (timeChangeTargetScale (K := K) (ι := ι))⁻¹ •
    timeChangeTargetDerivation K ι

def timeChangeInverseSourceVariable
    {K ι : Type*} [Field K] (p : TimeChangeSourceIndex ι) :
    TimeChangeTargetFractionField K ι :=
  match p with
  | Sum.inl _ => timeChangeTargetJet (K := K) (Sum.inl PUnit.unit) 0
  | Sum.inr (Sum.inl n) =>
      (timeChangeTargetInverseDerivation K ι)^[n]
        (timeChangeTargetScale (K := K) (ι := ι))
  | Sum.inr (Sum.inr (i, n)) =>
      (timeChangeTargetInverseDerivation K ι)^[n]
        (timeChangeTargetJet (K := K) (Sum.inr i) 0)

def timeChangeInverseAlgHom
    (K ι : Type*) [Field K] :
    TimeChangeSourcePolynomial K ι →ₐ[K] TimeChangeTargetFractionField K ι :=
  MvPolynomial.aeval (timeChangeInverseSourceVariable (K := K))

@[simp] theorem timeChangeInverseAlgHom_X
    {K ι : Type*} [Field K] (p : TimeChangeSourceIndex ι) :
    timeChangeInverseAlgHom K ι (MvPolynomial.X p) =
      timeChangeInverseSourceVariable (K := K) p := by
  simp [timeChangeInverseAlgHom]

@[simp] theorem timeChangeTargetInverseDerivation_clock_zero
    {K ι : Type*} [Field K] :
    timeChangeTargetInverseDerivation K ι
      (timeChangeTargetJet (K := K) (Sum.inl PUnit.unit) 0) = 1 := by
  change (timeChangeTargetScale (K := K) (ι := ι))⁻¹ *
      timeChangeTargetDerivation K ι
        (timeChangeTargetJet (K := K) (Sum.inl PUnit.unit) 0) = 1
  rw [timeChangeTargetDerivation_jet]
  exact inv_mul_cancel₀ (timeChangeTargetScale_ne_zero (K := K) (ι := ι))

@[simp] theorem timeChangeTargetInverseDerivation_inverseVariable
    {K ι : Type*} [Field K] (p : TimeChangeSourceIndex ι) :
    timeChangeTargetInverseDerivation K ι
      (timeChangeInverseSourceVariable (K := K) p) =
    timeChangeInverseAlgHom K ι (timeChangeSourceShift (K := K) p) := by
  rcases p with h | h
  · cases h
    simp [timeChangeInverseSourceVariable, timeChangeSourceShift]
  · rcases h with n | q
    · simp only [timeChangeInverseSourceVariable, timeChangeSourceShift,
        timeChangeSourceScaleIndex, timeChangeInverseAlgHom_X]
      rw [Function.iterate_succ_apply']
    · rcases q with ⟨i, n⟩
      simp only [timeChangeInverseSourceVariable, timeChangeSourceShift,
        timeChangeSourceObservableIndex, timeChangeInverseAlgHom_X]
      rw [Function.iterate_succ_apply']

theorem timeChangeInverseAlgHom_sourceDerivation
    {K ι : Type*} [Field K] (P : TimeChangeSourcePolynomial K ι) :
    timeChangeInverseAlgHom K ι (timeChangeSourceDerivation K ι P) =
      timeChangeTargetInverseDerivation K ι (timeChangeInverseAlgHom K ι P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [timeChangeSourceDerivation, timeChangeInverseAlgHom]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P p hP =>
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul, hP,
        timeChangeInverseAlgHom_X,
        timeChangeTargetInverseDerivation_inverseVariable]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [timeChangeSourceDerivation, MvPolynomial.mkDerivation_X,
        timeChangeTargetInverseDerivation_inverseVariable]

theorem timeChangeInverseAlgHom_sourceTimeDerivation
    {K ι : Type*} [Field K] (P : TimeChangeSourcePolynomial K ι) :
    timeChangeInverseAlgHom K ι (timeChangeSourceTimeDerivation K ι P) =
      timeChangeTargetDerivation K ι (timeChangeInverseAlgHom K ι P) := by
  change timeChangeInverseAlgHom K ι
      ((timeChangeSourceScaleVariable (K := K) (ι := ι)) *
        timeChangeSourceDerivation K ι P) = _
  rw [map_mul, timeChangeInverseAlgHom_sourceDerivation]
  have hscale : timeChangeInverseAlgHom K ι
      (timeChangeSourceScaleVariable (K := K) (ι := ι)) =
      timeChangeTargetScale (K := K) (ι := ι) := by
    simp [timeChangeSourceScaleVariable, timeChangeSourceScaleIndex,
      timeChangeInverseSourceVariable, timeChangeTargetScale]
  rw [hscale]
  unfold timeChangeTargetInverseDerivation
  change (timeChangeTargetScale (K := K) (ι := ι)) *
      ((timeChangeTargetScale (K := K) (ι := ι))⁻¹ *
        timeChangeTargetDerivation K ι (timeChangeInverseAlgHom K ι P)) = _
  rw [← mul_assoc, mul_inv_cancel₀
    (timeChangeTargetScale_ne_zero (K := K) (ι := ι)), one_mul]

theorem timeChangeInverseAlgHom_universalTimeChangeJet
    {K ι : Type*} [Field K] (b : Sum PUnit ι) :
    ∀ n : ℕ,
      timeChangeInverseAlgHom K ι (universalTimeChangeJet (K := K) b n) =
        timeChangeTargetJet (K := K) b n := by
  intro n
  induction n with
  | zero =>
      rcases b with h | i
      · cases h
        change timeChangeInverseAlgHom K ι
            (MvPolynomial.X (timeChangeSourceClockIndex (ι := ι))) =
          timeChangeTargetJet (K := K) (Sum.inl PUnit.unit) 0
        rw [timeChangeInverseAlgHom_X]
        rfl
      · change timeChangeInverseAlgHom K ι
            (MvPolynomial.X (timeChangeSourceObservableIndex i 0)) =
          timeChangeTargetJet (K := K) (Sum.inr i) 0
        rw [timeChangeInverseAlgHom_X]
        rfl
  | succ n ih =>
      rw [universalTimeChangeJet_succ,
        timeChangeInverseAlgHom_sourceTimeDerivation]
      rw [ih, timeChangeTargetDerivation_jet]

theorem timeChangeInverseAlgHom_universalTimeChangeAlgHom
    {K ι : Type*} [Field K] (P : TimeChangeTargetPolynomial K ι) :
    timeChangeInverseAlgHom K ι (universalTimeChangeAlgHom K ι P) =
      timeChangeTargetEmbedding (K := K) (ι := ι) P := by
  let lhs : TimeChangeTargetPolynomial K ι →ₐ[K]
      TimeChangeTargetFractionField K ι :=
    (timeChangeInverseAlgHom K ι).comp (universalTimeChangeAlgHom K ι)
  have hlhs : lhs = timeChangeTargetEmbedding (K := K) (ι := ι) := by
    ext p
    simp [lhs, timeChangeInverseAlgHom_universalTimeChangeJet,
      timeChangeTargetJet]
  exact DFunLike.congr_fun hlhs P

theorem universalTimeChangeAlgHom_injective
    {K ι : Type*} [Field K] :
    Function.Injective (universalTimeChangeAlgHom K ι) := by
  intro P Q hPQ
  apply timeChangeTargetEmbedding_injective (K := K) (ι := ι)
  rw [← timeChangeInverseAlgHom_universalTimeChangeAlgHom P,
    ← timeChangeInverseAlgHom_universalTimeChangeAlgHom Q, hPQ]

def timeChangeSourceValue
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E) :
    TimeChangeSourceIndex ι → E
  | Sum.inl _ => w
  | Sum.inr (Sum.inl n) => D^[n] a
  | Sum.inr (Sum.inr (i, n)) => D^[n] (f i)

def timeChangeSourceEval
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E) :
    TimeChangeSourcePolynomial K ι →ₐ[K] E :=
  MvPolynomial.aeval (timeChangeSourceValue D w a f)

@[simp] theorem timeChangeSourceEval_X
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E)
    (p : TimeChangeSourceIndex ι) :
    timeChangeSourceEval D w a f (MvPolynomial.X p) =
      timeChangeSourceValue D w a f p := by
  simp [timeChangeSourceEval]

theorem timeChangeSourceEval_shift
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E)
    (hclock : D w = 1) (p : TimeChangeSourceIndex ι) :
    timeChangeSourceEval D w a f (timeChangeSourceShift (K := K) p) =
      D (timeChangeSourceValue D w a f p) := by
  rcases p with h | h
  · cases h
    simpa [timeChangeSourceShift, timeChangeSourceValue] using hclock.symm
  · rcases h with n | q
    · simp [timeChangeSourceShift, timeChangeSourceValue,
        timeChangeSourceScaleIndex, Function.iterate_succ_apply']
    · rcases q with ⟨i, n⟩
      simp [timeChangeSourceShift, timeChangeSourceValue,
        timeChangeSourceObservableIndex, Function.iterate_succ_apply']

theorem timeChangeSourceEval_derivation
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E)
    (hclock : D w = 1) (P : TimeChangeSourcePolynomial K ι) :
    timeChangeSourceEval D w a f (timeChangeSourceDerivation K ι P) =
      D (timeChangeSourceEval D w a f P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [timeChangeSourceDerivation, timeChangeSourceEval]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P p hP =>
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul, hP, timeChangeSourceEval_X]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [timeChangeSourceDerivation, MvPolynomial.mkDerivation_X,
        timeChangeSourceEval_shift D w a f hclock p]

def actualTimeChangeDerivation
    {K E : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (a : E) : Derivation K E E :=
  a • D

def actualTimeChangeJet
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E)
    (b : Sum PUnit ι) (n : ℕ) : E :=
  (actualTimeChangeDerivation D a)^[n]
    (match b with
    | Sum.inl _ => w
    | Sum.inr i => f i)

theorem timeChangeSourceEval_timeDerivation
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E)
    (hclock : D w = 1) (P : TimeChangeSourcePolynomial K ι) :
    timeChangeSourceEval D w a f (timeChangeSourceTimeDerivation K ι P) =
      actualTimeChangeDerivation D a (timeChangeSourceEval D w a f P) := by
  change timeChangeSourceEval D w a f
      ((timeChangeSourceScaleVariable (K := K) (ι := ι)) *
        timeChangeSourceDerivation K ι P) = _
  rw [map_mul, timeChangeSourceEval_derivation D w a f hclock]
  simp [timeChangeSourceScaleVariable, timeChangeSourceScaleIndex,
    timeChangeSourceValue, actualTimeChangeDerivation, smul_eq_mul]

theorem timeChangeSourceEval_universalTimeChangeJet
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E)
    (hclock : D w = 1) (b : Sum PUnit ι) :
    ∀ n : ℕ,
      timeChangeSourceEval D w a f (universalTimeChangeJet (K := K) b n) =
        actualTimeChangeJet D w a f b n := by
  intro n
  induction n with
  | zero =>
      rcases b with h | i
      · cases h
        simp [universalTimeChangeJet, timeChangeSourceSeedVariable,
          actualTimeChangeJet, timeChangeSourceValue,
          timeChangeSourceClockIndex]
      · simp [universalTimeChangeJet, timeChangeSourceSeedVariable,
          actualTimeChangeJet, timeChangeSourceValue,
          timeChangeSourceObservableIndex]
  | succ n ih =>
      rw [universalTimeChangeJet_succ,
        timeChangeSourceEval_timeDerivation D w a f hclock, ih]
      simp [actualTimeChangeJet, Function.iterate_succ_apply']

/-- The common finite coordinate set.  Its first block is interpreted as
`w, a, Da, ..., D^(m-1)a` on the source and as `w, δw, ..., δ^m w` on the target. -/
abbrev TimeChangeFiniteIndex (ι : Type*) (m : ℕ) :=
  Sum (Fin (m + 1)) (ι × Fin (m + 1))

abbrev TimeChangeFiniteSourceIndex (ι : Type*) (m : ℕ) :=
  TimeChangeFiniteIndex ι m

abbrev TimeChangeFiniteTargetIndex (ι : Type*) (m : ℕ) :=
  TimeChangeFiniteIndex ι m

abbrev TimeChangeFiniteSourcePolynomial
    (K ι : Type*) [CommRing K] (m : ℕ) :=
  MvPolynomial (TimeChangeFiniteIndex ι m) K

abbrev TimeChangeFiniteTargetPolynomial
    (K ι : Type*) [CommRing K] (m : ℕ) :=
  MvPolynomial (TimeChangeFiniteIndex ι m) K

def timeChangeFiniteSourceIndexEmbedding
    {ι : Type*} {m : ℕ} :
    TimeChangeFiniteIndex ι m → TimeChangeSourceIndex ι
  | Sum.inl r => Fin.cases timeChangeSourceClockIndex
      (fun n => timeChangeSourceScaleIndex n) r
  | Sum.inr (i, r) => timeChangeSourceObservableIndex i r

def timeChangeFiniteSourceEmbedding
    {K ι : Type*} [CommRing K] {m : ℕ} :
    TimeChangeFiniteSourcePolynomial K ι m →ₐ[K]
      TimeChangeSourcePolynomial K ι :=
  MvPolynomial.rename timeChangeFiniteSourceIndexEmbedding

def timeChangeFiniteSourceStepIndex
    {ι : Type*} {m : ℕ} :
    TimeChangeFiniteIndex ι m → TimeChangeFiniteIndex ι (m + 1)
  | Sum.inl r => Sum.inl r.castSucc
  | Sum.inr (i, r) => Sum.inr (i, r.castSucc)

def timeChangeFiniteSourceStepEmbedding
    {K ι : Type*} [CommRing K] {m : ℕ} :
    TimeChangeFiniteSourcePolynomial K ι m →ₐ[K]
      TimeChangeFiniteSourcePolynomial K ι (m + 1) :=
  MvPolynomial.rename timeChangeFiniteSourceStepIndex

noncomputable instance timeChangeFiniteSourcePolynomialAlgebraSucc
    {K ι : Type*} [CommRing K] {m : ℕ} :
    Algebra (TimeChangeFiniteSourcePolynomial K ι m)
      (TimeChangeFiniteSourcePolynomial K ι (m + 1)) :=
  (timeChangeFiniteSourceStepEmbedding (K := K) (ι := ι) (m := m)).toRingHom.toAlgebra

def timeChangeFiniteSourceStepShift
    {K ι : Type*} [CommRing K] {m : ℕ}
    (p : TimeChangeFiniteIndex ι m) :
    TimeChangeFiniteSourcePolynomial K ι (m + 1) :=
  match p with
  | Sum.inl r => Fin.cases 1
      (fun n => MvPolynomial.X (Sum.inl n.succ.succ)) r
  | Sum.inr (i, r) => MvPolynomial.X (Sum.inr (i, r.succ))

def timeChangeFiniteSourceStepDerivation
    (K ι : Type*) [CommRing K] (m : ℕ) :
    Derivation K (TimeChangeFiniteSourcePolynomial K ι m)
      (TimeChangeFiniteSourcePolynomial K ι (m + 1)) :=
  MvPolynomial.mkDerivation K timeChangeFiniteSourceStepShift

theorem timeChangeFiniteSourceEmbedding_stepEmbedding
    {K ι : Type*} [CommRing K] {m : ℕ}
    (P : TimeChangeFiniteSourcePolynomial K ι m) :
    timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m + 1)
        (timeChangeFiniteSourceStepEmbedding (K := K) (ι := ι) (m := m) P) =
      timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m) P := by
  rw [timeChangeFiniteSourceEmbedding, timeChangeFiniteSourceStepEmbedding,
    MvPolynomial.rename_rename]
  congr 1
  funext p
  rcases p with r | ⟨i, r⟩
  · refine Fin.cases ?_ (fun n => ?_) r <;> rfl
  · rfl

theorem timeChangeFiniteSourceEmbedding_stepShift
    {K ι : Type*} [CommRing K] {m : ℕ}
    (p : TimeChangeFiniteIndex ι m) :
    timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m + 1)
        (timeChangeFiniteSourceStepShift (K := K) p) =
      timeChangeSourceShift (K := K)
        (timeChangeFiniteSourceIndexEmbedding p) := by
  rcases p with r | ⟨i, r⟩
  · refine Fin.cases ?_ (fun n => ?_) r
    · simp [timeChangeFiniteSourceStepShift, timeChangeFiniteSourceIndexEmbedding,
        timeChangeSourceShift]
    · simp [timeChangeFiniteSourceStepShift, timeChangeFiniteSourceIndexEmbedding,
        timeChangeSourceShift, timeChangeFiniteSourceEmbedding,
        timeChangeSourceScaleIndex]
  · simp [timeChangeFiniteSourceStepShift, timeChangeFiniteSourceIndexEmbedding,
      timeChangeSourceShift, timeChangeSourceObservableIndex,
      timeChangeFiniteSourceEmbedding]

theorem timeChangeFiniteSourceEmbedding_stepDerivation
    {K ι : Type*} [CommRing K] {m : ℕ}
    (P : TimeChangeFiniteSourcePolynomial K ι m) :
    timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m + 1)
        (timeChangeFiniteSourceStepDerivation K ι m P) =
      timeChangeSourceDerivation K ι
        (timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [timeChangeFiniteSourceStepDerivation, timeChangeSourceDerivation]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P p hP =>
      rw [Derivation.leibniz]
      simp only [Algebra.smul_def, map_add, map_mul]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [hP, timeChangeFiniteSourceEmbedding_stepEmbedding,
        timeChangeFiniteSourceStepDerivation, MvPolynomial.mkDerivation_X,
        timeChangeFiniteSourceEmbedding_stepShift,
        timeChangeSourceDerivation, MvPolynomial.mkDerivation_X]

def timeChangeFiniteSourceScaleVariable
    {K ι : Type*} [CommRing K] (m : ℕ) :
    TimeChangeFiniteSourcePolynomial K ι (m + 1) :=
  MvPolynomial.X (Sum.inl
    ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ m)⟩)

@[simp] theorem timeChangeFiniteSourceEmbedding_scaleVariable
    {K ι : Type*} [CommRing K] (m : ℕ) :
    timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m + 1)
      (timeChangeFiniteSourceScaleVariable (K := K) (ι := ι) m) =
        timeChangeSourceScaleVariable (K := K) (ι := ι) := by
  simp [timeChangeFiniteSourceScaleVariable, timeChangeFiniteSourceEmbedding,
    timeChangeFiniteSourceIndexEmbedding, timeChangeSourceScaleVariable,
    timeChangeSourceScaleIndex]

theorem exists_timeChangeFiniteSourcePolynomial_universalJet
    {K ι : Type*} [CommRing K] (b : Sum PUnit ι) :
    ∀ n : ℕ, ∃ P : TimeChangeFiniteSourcePolynomial K ι n,
      timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := n) P =
        universalTimeChangeJet (K := K) b n := by
  intro n
  induction n with
  | zero =>
      rcases b with h | i
      · cases h
        exact ⟨MvPolynomial.X (Sum.inl 0), rfl⟩
      · exact ⟨MvPolynomial.X (Sum.inr (i, 0)), rfl⟩
  | succ n ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨timeChangeFiniteSourceScaleVariable (K := K) (ι := ι) n *
          timeChangeFiniteSourceStepDerivation K ι n P, ?_⟩
      rw [map_mul, timeChangeFiniteSourceEmbedding_scaleVariable,
        timeChangeFiniteSourceEmbedding_stepDerivation, hP,
        universalTimeChangeJet_succ]
      rfl

def timeChangeFiniteSourceIndexCast
    {ι : Type*} {n m : ℕ} (h : n ≤ m) :
    TimeChangeFiniteIndex ι n → TimeChangeFiniteIndex ι m
  | Sum.inl r => Sum.inl (Fin.castLE (Nat.succ_le_succ h) r)
  | Sum.inr (i, r) => Sum.inr (i, Fin.castLE (Nat.succ_le_succ h) r)

def timeChangeFiniteSourceCast
    {K ι : Type*} [CommRing K] {n m : ℕ} (h : n ≤ m) :
    TimeChangeFiniteSourcePolynomial K ι n →ₐ[K]
      TimeChangeFiniteSourcePolynomial K ι m :=
  MvPolynomial.rename (timeChangeFiniteSourceIndexCast h)

theorem timeChangeFiniteSourceEmbedding_cast
    {K ι : Type*} [CommRing K] {n m : ℕ} (h : n ≤ m)
    (P : TimeChangeFiniteSourcePolynomial K ι n) :
    timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m)
        (timeChangeFiniteSourceCast (K := K) (ι := ι) h P) =
      timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := n) P := by
  rw [timeChangeFiniteSourceEmbedding, timeChangeFiniteSourceCast,
    MvPolynomial.rename_rename]
  congr 1
  funext p
  rcases p with r | ⟨i, r⟩
  · refine Fin.cases ?_ (fun j => ?_) r <;> rfl
  · rfl

theorem exists_timeChangeFiniteSourcePolynomial_universalJet_of_le
    {K ι : Type*} [CommRing K] {n m : ℕ} (h : n ≤ m)
    (b : Sum PUnit ι) :
    ∃ P : TimeChangeFiniteSourcePolynomial K ι m,
      timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m) P =
        universalTimeChangeJet (K := K) b n := by
  obtain ⟨P, hP⟩ :=
    exists_timeChangeFiniteSourcePolynomial_universalJet (K := K) b n
  exact ⟨timeChangeFiniteSourceCast (K := K) (ι := ι) h P,
    (timeChangeFiniteSourceEmbedding_cast h P).trans hP⟩

def timeChangeFiniteTargetIndexEmbedding
    {ι : Type*} {m : ℕ} :
    TimeChangeFiniteIndex ι m → TimeChangeTargetIndex ι
  | Sum.inl n => timeChangeTargetClockIndex n
  | Sum.inr (i, n) => timeChangeTargetObservableIndex i n

theorem timeChangeFiniteTargetIndexEmbedding_injective
    {ι : Type*} {m : ℕ} :
    Function.Injective (timeChangeFiniteTargetIndexEmbedding (ι := ι) (m := m)) := by
  rintro (n | q) (n' | q') heq
  · exact Sum.inl_injective (Fin.ext (congrArg Prod.snd heq))
  · rcases q' with ⟨i', n'⟩
    simp [timeChangeFiniteTargetIndexEmbedding, timeChangeTargetClockIndex,
      timeChangeTargetObservableIndex] at heq
  · rcases q with ⟨i, n⟩
    simp [timeChangeFiniteTargetIndexEmbedding, timeChangeTargetClockIndex,
      timeChangeTargetObservableIndex] at heq
  · rcases q with ⟨i, n⟩
    rcases q' with ⟨i', n'⟩
    have hp : (i, (n : ℕ)) = (i', (n' : ℕ)) := by
      simpa [timeChangeFiniteTargetIndexEmbedding,
        timeChangeTargetObservableIndex] using heq
    cases hp
    rfl

def timeChangeFiniteTargetEmbedding
    {K ι : Type*} [CommRing K] {m : ℕ} :
    TimeChangeFiniteTargetPolynomial K ι m →ₐ[K]
      TimeChangeTargetPolynomial K ι :=
  MvPolynomial.rename timeChangeFiniteTargetIndexEmbedding

theorem timeChangeFiniteTargetEmbedding_injective
    {K ι : Type*} [CommRing K] {m : ℕ} :
    Function.Injective (timeChangeFiniteTargetEmbedding (K := K) (ι := ι) (m := m)) :=
  MvPolynomial.rename_injective _
    (timeChangeFiniteTargetIndexEmbedding_injective (ι := ι) (m := m))

def finiteUniversalTimeChangeJet
    {K ι : Type*} [CommRing K] (m : ℕ)
    (p : TimeChangeFiniteIndex ι m) :
    TimeChangeFiniteSourcePolynomial K ι m :=
  Classical.choose <| match p with
  | Sum.inl n => exists_timeChangeFiniteSourcePolynomial_universalJet_of_le
      (K := K) (Nat.lt_succ_iff.mp n.isLt) (Sum.inl PUnit.unit)
  | Sum.inr (i, n) => exists_timeChangeFiniteSourcePolynomial_universalJet_of_le
      (K := K) (Nat.lt_succ_iff.mp n.isLt) (Sum.inr i)

theorem finiteUniversalTimeChangeJet_embedding
    {K ι : Type*} [CommRing K] (m : ℕ)
    (p : TimeChangeFiniteIndex ι m) :
    timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m)
        (finiteUniversalTimeChangeJet (K := K) m p) =
      universalTimeChangeJet (K := K)
        (timeChangeFiniteTargetIndexEmbedding p).1
        (timeChangeFiniteTargetIndexEmbedding p).2 := by
  rcases p with n | ⟨i, n⟩
  · exact Classical.choose_spec <|
      exists_timeChangeFiniteSourcePolynomial_universalJet_of_le
        (K := K) (Nat.lt_succ_iff.mp n.isLt) (Sum.inl PUnit.unit)
  · exact Classical.choose_spec <|
      exists_timeChangeFiniteSourcePolynomial_universalJet_of_le
        (K := K) (Nat.lt_succ_iff.mp n.isLt) (Sum.inr i)

def finiteUniversalTimeChangeAlgHom
    (K ι : Type*) [CommRing K] (m : ℕ) :
    TimeChangeFiniteTargetPolynomial K ι m →ₐ[K]
      TimeChangeFiniteSourcePolynomial K ι m :=
  MvPolynomial.aeval (finiteUniversalTimeChangeJet (K := K) m)

theorem finiteUniversalTimeChangeAlgHom_embedding
    {K ι : Type*} [CommRing K] (m : ℕ)
    (P : TimeChangeFiniteTargetPolynomial K ι m) :
    timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m)
        (finiteUniversalTimeChangeAlgHom K ι m P) =
      universalTimeChangeAlgHom K ι
        (timeChangeFiniteTargetEmbedding (K := K) (ι := ι) (m := m) P) := by
  let lhs : TimeChangeFiniteTargetPolynomial K ι m →ₐ[K]
      TimeChangeSourcePolynomial K ι :=
    (timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m)).comp
      (finiteUniversalTimeChangeAlgHom K ι m)
  let rhs : TimeChangeFiniteTargetPolynomial K ι m →ₐ[K]
      TimeChangeSourcePolynomial K ι :=
    (universalTimeChangeAlgHom K ι).comp
      (timeChangeFiniteTargetEmbedding (K := K) (ι := ι) (m := m))
  have heq : lhs = rhs := by
    ext p
    simp [lhs, rhs, finiteUniversalTimeChangeAlgHom,
      finiteUniversalTimeChangeJet_embedding,
      timeChangeFiniteTargetEmbedding,
      universalTimeChangeAlgHom, universalTimeChangeJet]
  exact DFunLike.congr_fun heq P

theorem finiteUniversalTimeChangeAlgHom_injective
    {K ι : Type*} [Field K] (m : ℕ) :
    Function.Injective (finiteUniversalTimeChangeAlgHom K ι m) := by
  intro P Q hPQ
  apply timeChangeFiniteTargetEmbedding_injective (K := K) (ι := ι) (m := m)
  apply universalTimeChangeAlgHom_injective (K := K) (ι := ι)
  rw [← finiteUniversalTimeChangeAlgHom_embedding m P,
    ← finiteUniversalTimeChangeAlgHom_embedding m Q, hPQ]

def timeChangeFiniteSourceValue
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E) {m : ℕ} :
    TimeChangeFiniteIndex ι m → E :=
  timeChangeSourceValue D w a f ∘ timeChangeFiniteSourceIndexEmbedding

@[simp] theorem timeChangeFiniteSourceValue_clock
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E) (m : ℕ) :
    timeChangeFiniteSourceValue D w a f
      (Sum.inl (0 : Fin (m + 1))) = w := by
  rfl

@[simp] theorem timeChangeFiniteSourceValue_scale
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E)
    {m : ℕ} (r : Fin m) :
    timeChangeFiniteSourceValue D w a f
      (Sum.inl r.succ) = D^[r] a := by
  rfl

@[simp] theorem timeChangeFiniteSourceValue_observable
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E)
    {m : ℕ} (i : ι) (r : Fin (m + 1)) :
    timeChangeFiniteSourceValue D w a f
      (Sum.inr (i, r)) = D^[r] (f i) := by
  rfl

def timeChangeFiniteSourceEval
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E) (m : ℕ) :
    TimeChangeFiniteSourcePolynomial K ι m →ₐ[K] E :=
  MvPolynomial.aeval (timeChangeFiniteSourceValue D w a f)

theorem timeChangeFiniteSourceEval_eq_comp
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E) (m : ℕ) :
    timeChangeFiniteSourceEval D w a f m =
      (timeChangeSourceEval D w a f).comp
        (timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m)) := by
  ext p
  rfl

def timeChangeFiniteTargetValue
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E) {m : ℕ} :
    TimeChangeFiniteIndex ι m → E
  | Sum.inl n => actualTimeChangeJet D w a f (Sum.inl PUnit.unit) n
  | Sum.inr (i, n) => actualTimeChangeJet D w a f (Sum.inr i) n

def timeChangeFiniteTargetEval
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E) (m : ℕ) :
    TimeChangeFiniteTargetPolynomial K ι m →ₐ[K] E :=
  MvPolynomial.aeval (timeChangeFiniteTargetValue D w a f)

theorem timeChangeFiniteEval_forward
    {K E ι : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E)
    (hclock : D w = 1) (m : ℕ)
    (P : TimeChangeFiniteTargetPolynomial K ι m) :
    timeChangeFiniteSourceEval D w a f m
        (finiteUniversalTimeChangeAlgHom K ι m P) =
      timeChangeFiniteTargetEval D w a f m P := by
  let lhs : TimeChangeFiniteTargetPolynomial K ι m →ₐ[K] E :=
    (timeChangeFiniteSourceEval D w a f m).comp
      (finiteUniversalTimeChangeAlgHom K ι m)
  have heq : lhs = timeChangeFiniteTargetEval D w a f m := by
    ext p
    rw [show lhs (MvPolynomial.X p) =
        timeChangeSourceEval D w a f
          (timeChangeFiniteSourceEmbedding (K := K) (ι := ι) (m := m)
            (finiteUniversalTimeChangeJet (K := K) m p)) by
      simp [lhs, timeChangeFiniteSourceEval_eq_comp,
        finiteUniversalTimeChangeAlgHom]]
    rw [finiteUniversalTimeChangeJet_embedding,
      timeChangeSourceEval_universalTimeChangeJet D w a f hclock]
    rcases p with n | ⟨i, n⟩ <;> rfl
  exact DFunLike.congr_fun heq P

/-- A finite time change `δ = aD` preserves the complete jet-coordinate count when `Dw = 1`:
the scale jets replace exactly the clock coordinate lost after the zeroth jet. -/
theorem algebraicIndependent_timeChangeFiniteTargetValue
    {K E ι : Type*} [Field K] [Field E] [Algebra K E]
    (D : Derivation K E E) (w a : E) (f : ι → E)
    (hclock : D w = 1) (m : ℕ)
    (hsource : AlgebraicIndependent K
      (timeChangeFiniteSourceValue D w a f (m := m))) :
    AlgebraicIndependent K
      (timeChangeFiniteTargetValue D w a f (m := m)) := by
  rw [algebraicIndependent_iff_injective_aeval] at hsource ⊢
  intro P Q hPQ
  apply finiteUniversalTimeChangeAlgHom_injective m
  apply hsource
  rw [timeChangeFiniteEval_forward D w a f hclock m,
    timeChangeFiniteEval_forward D w a f hclock m, hPQ]

end

end GaloisForLFunctions
