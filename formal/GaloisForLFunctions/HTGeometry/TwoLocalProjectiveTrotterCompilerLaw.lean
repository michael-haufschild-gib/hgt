import GaloisForLFunctions.HTGeometry.PauliCommutatorGramStableRankFloor
import GaloisForLFunctions.HTGeometry.NearestNeighborPathSpectrumRealRelationEscape
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich
import GaloisForLFunctions.HTGeometry.HaferkampTerminalPauliCoordinate
import GaloisForLFunctions.HTGeometry.HaferkampSpecialUnitaryPhase
import GaloisForLFunctions.HTGeometry.SiteSupportedEvolutionFactorization
import GaloisForLFunctions.HTGeometry.HaferkampEntrywiseLiftDerivative
import GaloisForLFunctions.HTGeometry.HaferkampContinuousCircuitImageCompactness
import GaloisForLFunctions.HTGeometry.HaferkampFlattenedCoordinateDerivative
import GaloisForLFunctions.HTGeometry.QuantitativeLieProductFormula

open Matrix
open scoped Matrix.Norms.L2Operator Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance matrixCStarAlgebraQubit (n : ℕ) :
    CStarAlgebra (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) where

theorem PauliTracelessLabel.exists_distinct_covering_pair
    {n : ℕ} (hn : 2 ≤ n) (P : PauliTracelessLabel n 2) :
    ∃ a b : Fin n, a ≠ b ∧
      ∀ q : Fin n, q ≠ a → q ≠ b → P.1 q = none := by
  have hcard : (pauliSupport P.1).card ≤ 2 := by
    rw [← pauliWeight_eq_card_pauliSupport]
    exact P.property.1
  have hcardpos : 0 < (pauliSupport P.1).card := by
    by_contra hnot
    have hzero : pauliWeight P.1 = 0 := by
      rw [pauliWeight_eq_card_pauliSupport]
      omega
    exact P.2.2 ((pauliWeight_eq_zero_iff_eq_identity P.1).mp hzero)
  have hcases : (pauliSupport P.1).card = 1 ∨
      (pauliSupport P.1).card = 2 := by omega
  rcases hcases with hone | htwo
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
    have hcardFin : 1 < Fintype.card (Fin n) := by
      simp only [Fintype.card_fin]
      omega
    obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card hcardFin a
    refine ⟨a, b, hba.symm, ?_⟩
    intro q hqa hqb
    have hqnot : q ∉ pauliSupport P.1 := by
      rw [ha]
      simpa using hqa
    by_contra hne
    exact hqnot (mem_pauliSupport.mpr hne)
  · obtain ⟨a, b, hab, hpairs⟩ := Finset.card_eq_two.mp htwo
    refine ⟨a, b, hab, ?_⟩
    intro q hqa hqb
    have hqnot : q ∉ pauliSupport P.1 := by
      rw [hpairs]
      simp [hqa, hqb]
    by_contra hne
    exact hqnot (mem_pauliSupport.mpr hne)

def PauliTracelessLabel.coveringPair
    {n : ℕ} (hn : 2 ≤ n) (P : PauliTracelessLabel n 2) : Fin n × Fin n :=
  ⟨Classical.choose (P.exists_distinct_covering_pair hn),
    Classical.choose (Classical.choose_spec
      (P.exists_distinct_covering_pair hn))⟩

theorem PauliTracelessLabel.coveringPair_distinct
    {n : ℕ} (hn : 2 ≤ n) (P : PauliTracelessLabel n 2) :
    (P.coveringPair hn).1 ≠ (P.coveringPair hn).2 :=
  (Classical.choose_spec (Classical.choose_spec
    (P.exists_distinct_covering_pair hn))).1

theorem PauliTracelessLabel.eq_none_outside_coveringPair
    {n : ℕ} (hn : 2 ≤ n) (P : PauliTracelessLabel n 2)
    (q : Fin n) (hqa : q ≠ (P.coveringPair hn).1)
    (hqb : q ≠ (P.coveringPair hn).2) :
    P.1 q = none :=
  (Classical.choose_spec (Classical.choose_spec
    (P.exists_distinct_covering_pair hn))).2 q hqa hqb

theorem finitePauliMatrix_eq_twoQubitLiftMatrix_coveringPair
    {n : ℕ} (hn : 2 ≤ n) (P : PauliTracelessLabel n 2) :
    finitePauliMatrix P.1 =
      twoQubitLiftMatrix (P.coveringPair hn).1 (P.coveringPair hn).2
        (P.coveringPair_distinct hn)
        (boolTwoQubitPauli
          (P.1 (P.coveringPair hn).1)
          (P.1 (P.coveringPair hn).2)) := by
  let a := (P.coveringPair hn).1
  let b := (P.coveringPair hn).2
  let hab := P.coveringPair_distinct hn
  change finitePauliMatrix P.1 =
    twoQubitLiftMatrix a b hab
      (boolTwoQubitPauli (P.1 a) (P.1 b))
  apply (Matrix.reindexAlgEquiv ℂ ℂ (splitTwoQubitConfig a b hab)).injective
  change Matrix.reindex (splitTwoQubitConfig a b hab)
      (splitTwoQubitConfig a b hab) (finitePauliMatrix P.1) =
    Matrix.reindex (splitTwoQubitConfig a b hab)
      (splitTwoQubitConfig a b hab)
      (twoQubitLiftMatrix a b hab
        (boolTwoQubitPauli (P.1 a) (P.1 b)))
  rw [reindex_splitTwoQubitConfig_finitePauliMatrix]
  change Matrix.kronecker (boolTwoQubitPauli (P.1 a) (P.1 b))
      (finitePauliMatrix (twoQubitRestPauliLabel P.1 a b)) =
    Matrix.reindex (splitTwoQubitConfig a b hab)
      (splitTwoQubitConfig a b hab)
      (twoQubitLiftMatrix a b hab
        (boolTwoQubitPauli (P.1 a) (P.1 b)))
  rw [show Matrix.reindex (splitTwoQubitConfig a b hab)
      (splitTwoQubitConfig a b hab)
      (twoQubitLiftMatrix a b hab
        (boolTwoQubitPauli (P.1 a) (P.1 b))) =
      Matrix.kronecker (boolTwoQubitPauli (P.1 a) (P.1 b)) 1 by
        simp [twoQubitLiftMatrix]]
  congr 1
  have hrest : twoQubitRestPauliLabel P.1 a b =
      (fun _ : {q : Fin n // q ≠ a ∧ q ≠ b} => none) := by
    funext q
    exact P.eq_none_outside_coveringPair hn q.1 q.2.1 q.2.2
  rw [hrest]
  ext x y
  rw [Matrix.one_apply]
  by_cases hxy : x = y
  · subst y
    simp [finitePauliMatrix, boolPauliOptionEntry, boolPauliOption]
  · rw [if_neg hxy]
    obtain ⟨q, hq⟩ : ∃ q, x q ≠ y q := by
      simpa only [Function.ne_iff] using hxy
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    simp [boolPauliOptionEntry, boolPauliOption, hq]

theorem unitaryEvolution_twoQubitLiftMatrix
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (B : Matrix (Bool × Bool) (Bool × Bool) ℂ) (t : ℝ) :
    unitaryEvolution (twoQubitLiftMatrix a b hab B) t =
      twoQubitLiftMatrix a b hab (unitaryEvolution B t) := by
  letI : NormedAlgebra ℚ (Matrix (Q → Bool) (Q → Bool) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  letI : NormedAlgebra ℚ
      (Matrix ((Bool × Bool) × ({q : Q // q ≠ a ∧ q ≠ b} → Bool))
        ((Bool × Bool) × ({q : Q // q ≠ a ∧ q ≠ b} → Bool)) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let e := splitTwoQubitConfig a b hab
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ e
  apply Φ.injective
  have hcont : Continuous Φ := Φ.toLinearEquiv.continuous_of_finiteDimensional
  have hmap := NormedSpace.map_exp Φ.toRingEquiv.toRingHom hcont
      (t • ((-Complex.I) • twoQubitLiftMatrix a b hab B))
  rw [unitaryEvolution, unitaryEvolution]
  rw [show Φ (NormedSpace.exp
      (t • ((-Complex.I) • twoQubitLiftMatrix a b hab B))) =
      NormedSpace.exp (Φ
        (t • ((-Complex.I) • twoQubitLiftMatrix a b hab B))) by exact hmap]
  have hlift (C : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
      Φ (twoQubitLiftMatrix a b hab C) =
      Matrix.kronecker C
        (1 : Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
          ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ) := by
    simp [Φ, e, twoQubitLiftMatrix]
  have hgen : Φ (t • ((-Complex.I) • twoQubitLiftMatrix a b hab B)) =
      t • ((-Complex.I) • Φ (twoQubitLiftMatrix a b hab B)) := by
    calc
      Φ (t • ((-Complex.I) • twoQubitLiftMatrix a b hab B)) =
          t • Φ ((-Complex.I) • twoQubitLiftMatrix a b hab B) :=
        Φ.toLinearMap.map_smul_of_tower t _
      _ = t • ((-Complex.I) • Φ (twoQubitLiftMatrix a b hab B)) := by
        rw [map_smul]
  rw [hgen, hlift B,
    hlift (NormedSpace.exp (t • ((-Complex.I) • B)))]
  let Irest : Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
      ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ := 1
  have hscalar :
      t • ((-Complex.I) • Matrix.kronecker B Irest) =
        Matrix.kronecker (t • ((-Complex.I) • B)) Irest := by
    ext x y
    simp [Matrix.kronecker, Matrix.smul_apply]
    ring
  rw [hscalar]
  dsimp [Irest]
  rw [exp_kronecker_one]

def realPauliCoefficient
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : Fin n → Option (Fin 3)) : ℝ :=
  (finitePauliSelfAdjointBasis (Fin n)).repr H P

def twoLocalSkewGenerator
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) :
    Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ :=
  (-Complex.I) • ((realPauliCoefficient H P.1 : ℂ) •
    finitePauliMatrix P.1)

def twoLocalPauliMatrix
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (realPauliCoefficient H P.1 : ℂ) •
    boolTwoQubitPauli
      (P.1 (P.coveringPair hn).1)
      (P.1 (P.coveringPair hn).2)

theorem boolTwoQubitPauli_isHermitian (p q : Option (Fin 3)) :
    (boolTwoQubitPauli p q).IsHermitian := by
  rw [Matrix.IsHermitian, boolTwoQubitPauli]
  calc
    (boolPauliOption p ⊗ₖ boolPauliOption q)ᴴ =
        (boolPauliOption p)ᴴ ⊗ₖ (boolPauliOption q)ᴴ :=
      Matrix.conjTranspose_kronecker _ _
    _ = boolPauliOption p ⊗ₖ boolPauliOption q := by
      rw [boolPauliOption_isHermitian p, boolPauliOption_isHermitian q]

theorem twoLocalPauliMatrix_isHermitian
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) :
    (twoLocalPauliMatrix hn H P).IsHermitian := by
  rw [Matrix.IsHermitian, twoLocalPauliMatrix,
    Matrix.conjTranspose_smul]
  rw [boolTwoQubitPauli_isHermitian]
  simp

theorem smul_finitePauliMatrix_eq_twoQubitLiftMatrix
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) :
    (realPauliCoefficient H P.1 : ℂ) • finitePauliMatrix P.1 =
      twoQubitLiftMatrix (P.coveringPair hn).1 (P.coveringPair hn).2
        (P.coveringPair_distinct hn) (twoLocalPauliMatrix hn H P) := by
  rw [finitePauliMatrix_eq_twoQubitLiftMatrix_coveringPair hn P]
  rw [twoLocalPauliMatrix, twoQubitLiftMatrix_smul]

theorem exp_twoLocalSkewGenerator_eq_localEvolutionLift
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) (t : ℝ) :
    NormedSpace.exp (t • twoLocalSkewGenerator H P) =
      twoQubitLiftMatrix (P.coveringPair hn).1 (P.coveringPair hn).2
        (P.coveringPair_distinct hn)
        (unitaryEvolution (twoLocalPauliMatrix hn H P) t) := by
  rw [twoLocalSkewGenerator]
  change unitaryEvolution
      ((realPauliCoefficient H P.1 : ℂ) • finitePauliMatrix P.1) t = _
  rw [smul_finitePauliMatrix_eq_twoQubitLiftMatrix hn H P]
  exact unitaryEvolution_twoQubitLiftMatrix _ _ _ _ _

/-- Every elementary two-local Lie factor is, up to a unit scalar phase,
one lifted `SU(4)` gate on its certified covering pair. -/
theorem exists_projective_twoQubitGate_eq_exp_twoLocalSkewGenerator
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) (t : ℝ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ∃ G : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
        NormedSpace.exp (t • twoLocalSkewGenerator H P) =
          c • (twoQubitLift (P.coveringPair hn).1 (P.coveringPair hn).2
            (P.coveringPair_distinct hn) G :
              Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ) := by
  let localH := twoLocalPauliMatrix hn H P
  have hlocalH : localH.IsHermitian := twoLocalPauliMatrix_isHermitian hn H P
  let Ulocal : Matrix.unitaryGroup (Bool × Bool) ℂ :=
    ⟨unitaryEvolution localH t,
      unitaryEvolution_mem_unitary
        (Matrix.isHermitian_iff_isSelfAdjoint.mp hlocalH) t⟩
  let z := scalarSpecialUnitaryPhase Ulocal
  let G := scalarSpecialUnitaryRepresentative Ulocal
  have hzunit : star z * z = 1 := scalarSpecialUnitaryPhase_unitary Ulocal
  have hznorm : ‖star z‖ = 1 := by
    have hnorm := congrArg norm hzunit
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
    have hsq : ‖z‖ * ‖z‖ = 1 := by simpa [norm_mul] using hnorm
    have hz : ‖z‖ = 1 := by nlinarith [sq_nonneg (‖z‖ - 1)]
    simpa using hz
  refine ⟨star z, hznorm, G, ?_⟩
  have hgate :
      (twoQubitLift (P.coveringPair hn).1 (P.coveringPair hn).2
          (P.coveringPair_distinct hn) G :
        Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) =
        z • twoQubitLiftMatrix
          (P.coveringPair hn).1 (P.coveringPair hn).2
          (P.coveringPair_distinct hn) (unitaryEvolution localH t) := by
    ext x y
    simp [G, z, Ulocal, twoQubitLift, twoQubitLiftMatrix,
      specialUnitaryAsUnitary, scalarSpecialUnitaryRepresentative_coe,
      unitaryGroupReindex_coe, Quantum.tensorGate_val,
      Matrix.reindex_apply, Matrix.kronecker, Matrix.smul_apply]
    ring
  rw [hgate, smul_smul, hzunit, one_smul]
  exact exp_twoLocalSkewGenerator_eq_localEvolutionLift hn H P t

def twoLocalProjectivePhase
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) (t : ℝ) : ℂ :=
  Classical.choose
    (exists_projective_twoQubitGate_eq_exp_twoLocalSkewGenerator hn H P t)

def twoLocalProjectiveGate
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) (t : ℝ) :
    Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  Classical.choose (Classical.choose_spec
    (exists_projective_twoQubitGate_eq_exp_twoLocalSkewGenerator hn H P t)).2

theorem twoLocalProjectivePhase_norm
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) (t : ℝ) :
    ‖twoLocalProjectivePhase hn H P t‖ = 1 :=
  (Classical.choose_spec
    (exists_projective_twoQubitGate_eq_exp_twoLocalSkewGenerator hn H P t)).1

theorem exp_twoLocalSkewGenerator_eq_projectiveGate
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) (t : ℝ) :
    NormedSpace.exp (t • twoLocalSkewGenerator H P) =
      twoLocalProjectivePhase hn H P t •
        (twoQubitLift (P.coveringPair hn).1 (P.coveringPair hn).2
          (P.coveringPair_distinct hn)
          (twoLocalProjectiveGate hn H P t) :
            Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) :=
  Classical.choose_spec (Classical.choose_spec
    (exists_projective_twoQubitGate_eq_exp_twoLocalSkewGenerator hn H P t)).2

def twoLocalActiveLabelAt (n : ℕ)
    (i : Fin (Fintype.card (PauliTracelessLabel n 2))) :
    PauliTracelessLabel n 2 :=
  (Fintype.equivFin (PauliTracelessLabel n 2)).symm i

def twoLocalTrotterStepCircuit
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (t : ℝ) : TwoQubitCircuit n where
  gateCount := Fintype.card (PauliTracelessLabel n 2)
  architecture :=
    { sites := fun r =>
        (twoLocalActiveLabelAt n (Fin.rev r)).coveringPair hn
      distinct := fun r =>
        (twoLocalActiveLabelAt n (Fin.rev r)).coveringPair_distinct hn }
  gates := fun r => twoLocalProjectiveGate hn H
    (twoLocalActiveLabelAt n (Fin.rev r)) t

theorem twoLocalTrotterStepCircuit_gateCount
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)) (t : ℝ) :
    (twoLocalTrotterStepCircuit hn H t).gateCount =
      Fintype.card (PauliTracelessLabel n 2) := rfl

theorem twoLocalTrotterStepCircuit_eval_coe
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)) (t : ℝ) :
    ((twoLocalTrotterStepCircuit hn H t).eval :
      Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) =
      (List.ofFn fun i : Fin (Fintype.card (PauliTracelessLabel n 2)) =>
        (twoQubitLift
          ((twoLocalActiveLabelAt n i).coveringPair hn).1
          ((twoLocalActiveLabelAt n i).coveringPair hn).2
          ((twoLocalActiveLabelAt n i).coveringPair_distinct hn)
          (twoLocalProjectiveGate hn H (twoLocalActiveLabelAt n i) t) :
            Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)).prod := by
  unfold TwoQubitCircuit.eval TwoQubitArchitecture.contraction
  rw [← List.map_coe_unitary_reverse_prod]
  rw [List.map_ofFn]
  let lifted : Fin (Fintype.card (PauliTracelessLabel n 2)) →
      Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ := fun i =>
    (twoQubitLift
      ((twoLocalActiveLabelAt n i).coveringPair hn).1
      ((twoLocalActiveLabelAt n i).coveringPair hn).2
      ((twoLocalActiveLabelAt n i).coveringPair_distinct hn)
      (twoLocalProjectiveGate hn H (twoLocalActiveLabelAt n i) t) :
        Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)
  change (List.ofFn (fun r => lifted (Fin.rev r))).reverse.prod =
    (List.ofFn lifted).prod
  rw [ofFn_comp_finRev, List.reverse_reverse]

theorem list_prod_exp_twoLocalSkewGenerator_eq_projectiveGates
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (t : ℝ) (l : List (PauliTracelessLabel n 2)) :
    (l.map fun P => NormedSpace.exp (t • twoLocalSkewGenerator H P)).prod =
      (l.map fun P => twoLocalProjectivePhase hn H P t).prod •
        (l.map fun P =>
          (twoQubitLift (P.coveringPair hn).1 (P.coveringPair hn).2
            (P.coveringPair_distinct hn)
            (twoLocalProjectiveGate hn H P t) :
              Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)).prod := by
  induction l with
  | nil => simp
  | cons P l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [exp_twoLocalSkewGenerator_eq_projectiveGate hn H P t, ih]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      module

theorem pauliCoeff_eq_realPauliCoefficient
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : Fin n → Option (Fin 3)) :
    pauliCoeff (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) P =
      (realPauliCoefficient H P : ℂ) := by
  classical
  have h := (finitePauliSelfAdjointBasis (Fin n)).sum_repr H
  have hcoe := congrArg
    (fun X : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) =>
      (X : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)) h
  have hmatrix :
      (∑ Q, (realPauliCoefficient H Q : ℂ) • finitePauliMatrix Q) =
        (H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) := by
    ext x y
    have hxy := congrFun (congrFun hcoe x) y
    simpa [realPauliCoefficient, finitePauliSelfAdjointBasis_apply,
      finitePauliSelfAdjoint, Finset.sum_apply] using hxy
  have hzero :
      (∑ Q, ((realPauliCoefficient H Q : ℂ) -
          pauliCoeff (H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) Q) •
          finitePauliMatrix Q) = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib]
    rw [hmatrix, sum_pauliCoeff_smul]
    simp
  have hcoord := Fintype.linearIndependent_iff.mp
    (finitePauliMatrix_linearIndependent (σ := Fin n))
    (fun Q => (realPauliCoefficient H Q : ℂ) -
      pauliCoeff (H : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) Q) hzero P
  exact (sub_eq_zero.mp hcoord).symm

theorem selfAdjoint_eq_identity_add_traceless_twoLocal
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (hlocal : HasPauliWeightAtMost (Fin n) 2 H) :
    (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) =
      (realPauliCoefficient H (pauliIdentityLabel n) : ℂ) •
        finitePauliMatrix (pauliIdentityLabel n) +
      ∑ P : PauliTracelessLabel n 2,
        (realPauliCoefficient H P.1 : ℂ) • finitePauliMatrix P.1 := by
  classical
  let f : (Fin n → Option (Fin 3)) →
      Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ :=
    fun P => (realPauliCoefficient H P : ℂ) • finitePauliMatrix P
  have hfull : (H : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) = ∑ P, f P := by
    have h := (finitePauliSelfAdjointBasis (Fin n)).sum_repr H
    have hcoe := congrArg
      (fun X : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) =>
        (X : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)) h
    simpa [f, realPauliCoefficient, finitePauliSelfAdjointBasis_apply,
      finitePauliSelfAdjoint] using hcoe.symm
  rw [hfull]
  have hterm (P : Fin n → Option (Fin 3)) :
      f P =
        (if P = pauliIdentityLabel n then f P else 0) +
        (if pauliWeight P ≤ 2 ∧ P ≠ pauliIdentityLabel n then f P else 0) := by
    by_cases hid : P = pauliIdentityLabel n
    · simp [hid]
    · by_cases hw : pauliWeight P ≤ 2
      · simp [hid, hw]
      · have hweight : 2 < finitePauliWeight P := by
          simpa [finitePauliWeight, pauliWeight] using (show 2 < pauliWeight P by omega)
        have hc : realPauliCoefficient H P = 0 := hlocal P hweight
        simp [hid, hw, f, hc]
  rw [Finset.sum_congr rfl (fun P _ => hterm P), Finset.sum_add_distrib]
  have hidSum :
      (∑ P : Fin n → Option (Fin 3),
          if P = pauliIdentityLabel n then f P else 0) =
        f (pauliIdentityLabel n) := by simp
  rw [hidSum]
  congr 1
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    (Finset.univ.filter fun P : Fin n → Option (Fin 3) =>
      pauliWeight P ≤ 2 ∧ P ≠ pauliIdentityLabel n)
    (by simp) f

theorem abs_realPauliCoefficient_le_norm
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : Fin n → Option (Fin 3)) :
    |realPauliCoefficient H P| ≤
      ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)‖ := by
  classical
  let A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ := H
  have hlower := le_opNorm_pauliCombination (pauliCoeff A)
  rw [sum_pauliCoeff_smul] at hlower
  have hsingle : ‖pauliCoeff A P‖ ^ (2 : ℕ) ≤
      ∑ Q, ‖pauliCoeff A Q‖ ^ (2 : ℕ) := by
    exact Finset.single_le_sum (fun Q _ => sq_nonneg ‖pauliCoeff A Q‖)
      (Finset.mem_univ P)
  have hsqrt : ‖pauliCoeff A P‖ ≤
      Real.sqrt (∑ Q, ‖pauliCoeff A Q‖ ^ (2 : ℕ)) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hsingle
  calc
    |realPauliCoefficient H P| = ‖(realPauliCoefficient H P : ℂ)‖ := by simp
    _ = ‖pauliCoeff A P‖ := by
      rw [pauliCoeff_eq_realPauliCoefficient]
    _ ≤ Real.sqrt (∑ Q, ‖pauliCoeff A Q‖ ^ (2 : ℕ)) := hsqrt
    _ ≤ ‖A‖ := hlower

def twoLocalSkewGeneratorList
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)) :
    List (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) :=
  List.ofFn fun i : Fin (Fintype.card (PauliTracelessLabel n 2)) =>
    twoLocalSkewGenerator H
      ((Fintype.equivFin (PauliTracelessLabel n 2)).symm i)

theorem twoLocalSkewGenerator_mem_skewAdjoint
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) :
    twoLocalSkewGenerator H P ∈ skewAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) := by
  rw [skewAdjoint.mem_iff]
  change star ((-Complex.I) •
      ((realPauliCoefficient H P.1 : ℂ) • finitePauliMatrix P.1)) =
    -((-Complex.I) •
      ((realPauliCoefficient H P.1 : ℂ) • finitePauliMatrix P.1))
  have hPstar : star (finitePauliMatrix P.1) = finitePauliMatrix P.1 :=
    finitePauliMatrix_isHermitian P.1
  rw [star_smul, star_smul, hPstar]
  simp

theorem twoLocalSkewGenerator_norm
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (P : PauliTracelessLabel n 2) :
    ‖twoLocalSkewGenerator H P‖ = |realPauliCoefficient H P.1| := by
  simp [twoLocalSkewGenerator, norm_smul, norm_finitePauliMatrix]

theorem twoLocalSkewGeneratorList_all_skewAdjoint
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)) :
    ∀ x ∈ twoLocalSkewGeneratorList H,
      x ∈ skewAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) := by
  intro x hx
  rw [twoLocalSkewGeneratorList, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact twoLocalSkewGenerator_mem_skewAdjoint H _

theorem twoLocalSkewGeneratorList_length
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)) :
    (twoLocalSkewGeneratorList H).length =
      Fintype.card (PauliTracelessLabel n 2) := by
  simp [twoLocalSkewGeneratorList]

theorem twoLocalTrotterStep_product_eq_phase_smul_eval
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)) (t : ℝ) :
    ((twoLocalSkewGeneratorList H).map
      fun x => NormedSpace.exp (t • x)).prod =
      (List.ofFn fun i : Fin (Fintype.card (PauliTracelessLabel n 2)) =>
        twoLocalProjectivePhase hn H (twoLocalActiveLabelAt n i) t).prod •
      ((twoLocalTrotterStepCircuit hn H t).eval :
        Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) := by
  let labels := List.ofFn (twoLocalActiveLabelAt n)
  have hmain := list_prod_exp_twoLocalSkewGenerator_eq_projectiveGates
    hn H t labels
  rw [twoLocalTrotterStepCircuit_eval_coe hn H t]
  simpa [twoLocalSkewGeneratorList, labels, List.map_ofFn,
    Function.comp_def, twoLocalActiveLabelAt] using hmain

theorem twoLocalTrotterStep_product_pow_eq_phase_smul_eval_pow
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)) (t : ℝ) (r : ℕ) :
    (((twoLocalSkewGeneratorList H).map
      fun x => NormedSpace.exp (t • x)).prod) ^ r =
      ((List.ofFn fun i : Fin (Fintype.card (PauliTracelessLabel n 2)) =>
        twoLocalProjectivePhase hn H (twoLocalActiveLabelAt n i) t).prod) ^ r •
      (((twoLocalTrotterStepCircuit hn H t).eval :
        Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) ^ r) := by
  rw [twoLocalTrotterStep_product_eq_phase_smul_eval hn H t, smul_pow]

theorem twoLocalSkewGeneratorList_norm_sum_le
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)) :
    ((twoLocalSkewGeneratorList H).map norm).sum ≤
      Fintype.card (PauliTracelessLabel n 2) *
        ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖ := by
  let B := ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
    (FiniteQubitConfiguration (Fin n)) ℂ)‖
  have hlist : ∀ x ∈ (twoLocalSkewGeneratorList H).map norm, x ≤ B := by
    intro x hx
    simp only [twoLocalSkewGeneratorList, List.map_ofFn,
      Function.comp_apply, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [twoLocalSkewGenerator_norm]
    exact abs_realPauliCoefficient_le_norm H _
  have hgeneral : ∀ l : List ℝ, (∀ x ∈ l, x ≤ B) →
      l.sum ≤ l.length * B := by
    intro l hl
    induction l with
    | nil => simp
    | cons x l ih =>
        simp only [List.sum_cons, List.length_cons]
        have hx := hl x (by simp)
        have htail : ∀ y ∈ l, y ≤ B := by
          intro y hy
          exact hl y (by simp [hy])
        have hi := ih htail
        push_cast
        linarith
  simpa [twoLocalSkewGeneratorList_length, B] using
    hgeneral ((twoLocalSkewGeneratorList H).map norm) hlist

theorem twoLocalSkewGeneratorList_sum
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (hlocal : HasPauliWeightAtMost (Fin n) 2 H) :
    (twoLocalSkewGeneratorList H).sum =
      (-Complex.I) •
        ((H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) -
        (realPauliCoefficient H (pauliIdentityLabel n) : ℂ) • 1) := by
  classical
  have henum :
      (∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
          twoLocalSkewGenerator H
            ((Fintype.equivFin (PauliTracelessLabel n 2)).symm i)) =
        ∑ P : PauliTracelessLabel n 2,
          twoLocalSkewGenerator H P := by
    exact Fintype.sum_equiv
      (Fintype.equivFin (PauliTracelessLabel n 2)).symm _ _ (fun _ => rfl)
  have hdecomp := selfAdjoint_eq_identity_add_traceless_twoLocal H hlocal
  have hid : finitePauliMatrix (pauliIdentityLabel n) =
      (1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) := by
    ext x y
    exact finitePauliMatrix_pauliIdentityLabel x y
  rw [hid] at hdecomp
  have hactive :
      (∑ P : PauliTracelessLabel n 2,
        (realPauliCoefficient H P.1 : ℂ) • finitePauliMatrix P.1) =
      (H : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) -
        (realPauliCoefficient H (pauliIdentityLabel n) : ℂ) • 1 := by
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    exact hdecomp.symm
  calc
    (twoLocalSkewGeneratorList H).sum =
        ∑ P : PauliTracelessLabel n 2, twoLocalSkewGenerator H P := by
          rw [twoLocalSkewGeneratorList, List.sum_ofFn, henum]
    _ = ∑ P : PauliTracelessLabel n 2,
        (-Complex.I) • ((realPauliCoefficient H P.1 : ℂ) •
          finitePauliMatrix P.1) := rfl
    _ = (-Complex.I) • (∑ P : PauliTracelessLabel n 2,
        (realPauliCoefficient H P.1 : ℂ) • finitePauliMatrix P.1) := by
          rw [Finset.smul_sum]
    _ = (-Complex.I) •
        ((H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) -
        (realPauliCoefficient H (pauliIdentityLabel n) : ℂ) • 1) := by
          rw [hactive]

theorem exp_complex_smul_one_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ℂ) :
    NormedSpace.exp (z • (1 : Matrix ι ι ℂ)) =
      Complex.exp z • (1 : Matrix ι ι ℂ) := by
  rw [show z • (1 : Matrix ι ι ℂ) =
      Matrix.diagonal (fun _ : ι => z) by
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]]
  rw [Matrix.exp_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
    exact (congrFun Complex.exp_eq_exp_ℂ _).symm
  · simp [hij]

/-- Removing the identity Pauli coefficient changes Schrödinger evolution
only by a unit-modulus global phase. -/
theorem unitaryEvolution_eq_phase_smul_exp_twoLocalSkewGeneratorList_sum
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (hlocal : HasPauliWeightAtMost (Fin n) 2 H) (t : ℝ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      unitaryEvolution H t = c •
        NormedSpace.exp (t • (twoLocalSkewGeneratorList H).sum) := by
  let a : ℝ := realPauliCoefficient H (pauliIdentityLabel n)
  let z : ℂ := (t : ℂ) * (-Complex.I) * (a : ℂ)
  refine ⟨Complex.exp z, ?_, ?_⟩
  · rw [Complex.norm_exp]
    simp [z]
  · rw [unitaryEvolution]
    let _ : NormedAlgebra ℚ
        (Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) :=
      NormedAlgebra.restrictScalars ℚ ℂ _
    have hsplit :
        t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)) =
        z • (1 : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) +
        t • (twoLocalSkewGeneratorList H).sum := by
      rw [twoLocalSkewGeneratorList_sum H hlocal]
      ext i j
      simp [z, a, Matrix.smul_apply]
      ring
    rw [hsplit, NormedSpace.exp_add_of_commute]
    · rw [exp_complex_smul_one_matrix]
      simp
    · change (z • (1 : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)) *
          (t • (twoLocalSkewGeneratorList H).sum) =
        (t • (twoLocalSkewGeneratorList H).sum) * (z • 1)
      ext i j
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
      ring

namespace TwoQubitArchitecture

/-- Concatenation of two ordered two-qubit architectures. -/
def append {n R S : ℕ} (A : TwoQubitArchitecture n R)
    (B : TwoQubitArchitecture n S) : TwoQubitArchitecture n (R + S) where
  sites := Fin.append A.sites B.sites
  distinct := by
    intro i
    refine Fin.addCases (fun r => ?_) (fun s => ?_) i
    · simpa using A.distinct r
    · simpa using B.distinct s

/-- Concatenating location lists composes contractions in time order. -/
theorem append_contraction {n R S : ℕ} (A : TwoQubitArchitecture n R)
    (B : TwoQubitArchitecture n S)
    (g : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (h : Fin S → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    (A.append B).contraction (Fin.append g h) =
      B.contraction h * A.contraction g := by
  unfold contraction
  have hlift :
      (fun i => (A.append B).gateLift i (Fin.append g h i)) =
        Fin.append (fun r => A.gateLift r (g r))
          (fun s => B.gateLift s (h s)) := by
    funext i
    refine Fin.addCases (fun r => ?_) (fun s => ?_) i
    · simp [append, gateLift]
    · simp [append, gateLift]
  rw [hlift, List.ofFn_fin_append, List.reverse_append, List.prod_append]

end TwoQubitArchitecture

namespace TwoQubitCircuit

/-- Circuit product whose endpoint is `C.eval * D.eval`. -/
def mul {n : ℕ} (C D : TwoQubitCircuit n) : TwoQubitCircuit n where
  gateCount := D.gateCount + C.gateCount
  architecture := D.architecture.append C.architecture
  gates := Fin.append D.gates C.gates

theorem mul_gateCount {n : ℕ} (C D : TwoQubitCircuit n) :
    (C.mul D).gateCount = D.gateCount + C.gateCount := rfl

theorem mul_eval {n : ℕ} (C D : TwoQubitCircuit n) :
    (C.mul D).eval = C.eval * D.eval := by
  exact TwoQubitArchitecture.append_contraction
    D.architecture C.architecture D.gates C.gates

/-- Empty two-qubit circuit. -/
def one (n : ℕ) : TwoQubitCircuit n where
  gateCount := 0
  architecture :=
    { sites := Fin.elim0
      distinct := fun r => Fin.elim0 r }
  gates := Fin.elim0

theorem one_eval (n : ℕ) : (one n).eval = 1 := by
  apply Subtype.ext
  simp [one, eval, TwoQubitArchitecture.contraction]

/-- Repetition of one concrete circuit. -/
def pow {n : ℕ} (C : TwoQubitCircuit n) : ℕ → TwoQubitCircuit n
  | 0 => one n
  | r + 1 => (pow C r).mul C

theorem pow_gateCount {n : ℕ} (C : TwoQubitCircuit n) (r : ℕ) :
    (C.pow r).gateCount = r * C.gateCount := by
  induction r with
  | zero => simp [pow, one]
  | succ r ih =>
      simp [pow, mul_gateCount, ih, Nat.succ_mul, Nat.add_comm]

theorem pow_eval {n : ℕ} (C : TwoQubitCircuit n) (r : ℕ) :
    (C.pow r).eval = C.eval ^ r := by
  induction r with
  | zero => exact one_eval n
  | succ r ih =>
      rw [pow, mul_eval, ih, pow_succ]

theorem pow_eval_coe {n : ℕ} (C : TwoQubitCircuit n) (r : ℕ) :
    ((C.pow r).eval : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) =
      ((C.eval : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) ^ r) := by
  exact congrArg Subtype.val (pow_eval C r)

end TwoQubitCircuit

def twoLocalTrotterCircuit
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (t : ℝ) (r : ℕ) : TwoQubitCircuit n :=
  (twoLocalTrotterStepCircuit hn H (t / (r : ℝ))).pow r

theorem twoLocalTrotterCircuit_gateCount
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (t : ℝ) (r : ℕ) :
    (twoLocalTrotterCircuit hn H t r).gateCount =
      r * Fintype.card (PauliTracelessLabel n 2) := by
  rw [twoLocalTrotterCircuit, TwoQubitCircuit.pow_gateCount,
    twoLocalTrotterStepCircuit_gateCount]

theorem norm_twoLocalProjectivePhaseList_prod
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)) (t : ℝ)
    (l : List (PauliTracelessLabel n 2)) :
    ‖(l.map fun P => twoLocalProjectivePhase hn H P t).prod‖ = 1 := by
  induction l with
  | nil => simp
  | cons P l ih =>
      simp only [List.map_cons, List.prod_cons, norm_mul,
        twoLocalProjectivePhase_norm hn H P t, ih, one_mul]

/-- Quantitative projective product-formula compiler for every two-local
self-adjoint qubit Hamiltonian. It returns a concrete continuous `SU(4)`
circuit, exact gate count, norm-one phase, and finite-repetition error. -/
theorem exists_twoLocal_projectiveTrotterCircuit
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (hlocal : HasPauliWeightAtMost (Fin n) 2 H)
    (t : ℝ) (r : ℕ) (hr : 0 < r)
    (hsmall : |t / (r : ℝ)| *
      ((twoLocalSkewGeneratorList H).map norm).sum ≤ 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
      C.gateCount = r * Fintype.card (PauliTracelessLabel n 2) ∧
      ‖unitaryEvolution H t - c •
        (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖ ≤
        3 * (twoLocalSkewGeneratorList H).length *
          ((twoLocalSkewGeneratorList H).map norm).sum ^ (2 : ℕ) * |t| ^ (2 : ℕ) / r := by
  obtain ⟨c₀, hc₀, hfull⟩ :=
    unitaryEvolution_eq_phase_smul_exp_twoLocalSkewGeneratorList_sum
      H hlocal t
  let phaseList := List.ofFn fun i :
      Fin (Fintype.card (PauliTracelessLabel n 2)) =>
    twoLocalProjectivePhase hn H (twoLocalActiveLabelAt n i)
      (t / (r : ℝ))
  let p : ℂ := phaseList.prod
  let C := twoLocalTrotterCircuit hn H t r
  have hp : ‖p‖ = 1 := by
    have h := norm_twoLocalProjectivePhaseList_prod hn H
      (t / (r : ℝ))
      (List.ofFn (twoLocalActiveLabelAt n))
    simpa [p, phaseList, List.map_ofFn, Function.comp_def] using h
  have hproduct :
      (((twoLocalSkewGeneratorList H).map fun x =>
        NormedSpace.exp ((t / (r : ℝ)) • x)).prod) ^ r =
      p ^ r •
        (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) := by
    rw [twoLocalTrotterStep_product_pow_eq_phase_smul_eval_pow
      hn H (t / (r : ℝ)) r]
    dsimp [p, phaseList, C, twoLocalTrotterCircuit]
    rw [TwoQubitCircuit.pow_eval_coe]
  have happrox := norm_list_exp_product_pow_sub_exp_sum_le
    (twoLocalSkewGeneratorList H)
    (twoLocalSkewGeneratorList_all_skewAdjoint H) t r hr hsmall
  refine ⟨c₀ * p ^ r, ?_, C,
    twoLocalTrotterCircuit_gateCount hn H t r, ?_⟩
  · rw [norm_mul, hc₀, norm_pow, hp, one_pow, one_mul]
  · calc
      ‖unitaryEvolution H t - (c₀ * p ^ r) •
          (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)‖ =
        ‖c₀ • (NormedSpace.exp (t • (twoLocalSkewGeneratorList H).sum) -
          p ^ r • (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ))‖ := by
              rw [hfull]
              rw [smul_sub, mul_smul]
      _ = ‖NormedSpace.exp (t • (twoLocalSkewGeneratorList H).sum) -
          p ^ r • (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)‖ := by
              rw [norm_smul, hc₀, one_mul]
      _ = ‖((twoLocalSkewGeneratorList H).map fun x =>
          NormedSpace.exp ((t / (r : ℝ)) • x)).prod ^ r -
          NormedSpace.exp (t • (twoLocalSkewGeneratorList H).sum)‖ := by
              rw [← hproduct, norm_sub_rev]
      _ ≤ 3 * (twoLocalSkewGeneratorList H).length *
          ((twoLocalSkewGeneratorList H).map norm).sum ^ (2 : ℕ) * |t| ^ (2 : ℕ) / r :=
            happrox

/-- Closed input-level form of the compiler bound: only register size,
Hamiltonian norm, time, and repetition count remain. -/
theorem exists_twoLocal_projectiveTrotterCircuit_normBound
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (hlocal : HasPauliWeightAtMost (Fin n) 2 H)
    (t : ℝ) (r : ℕ) (hr : 0 < r)
    (hsmall : |t / (r : ℝ)| *
      (Fintype.card (PauliTracelessLabel n 2) : ℝ) *
      ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)‖ ≤ 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
      C.gateCount = r * Fintype.card (PauliTracelessLabel n 2) ∧
      ‖unitaryEvolution H t - c •
        (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖ ≤
        3 * (Fintype.card (PauliTracelessLabel n 2) : ℝ) ^ (3 : ℕ) *
          ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) * |t| ^ (2 : ℕ) / r := by
  have hsum := twoLocalSkewGeneratorList_norm_sum_le H
  have habs : 0 ≤ |t / (r : ℝ)| := abs_nonneg _
  have hsmall' : |t / (r : ℝ)| *
      ((twoLocalSkewGeneratorList H).map norm).sum ≤ 1 := by
    calc
      |t / (r : ℝ)| * ((twoLocalSkewGeneratorList H).map norm).sum ≤
          |t / (r : ℝ)| *
            ((Fintype.card (PauliTracelessLabel n 2) : ℝ) *
              ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)‖) := by gcongr
      _ ≤ 1 := by
        simpa [mul_assoc] using hsmall
  obtain ⟨c, hc, C, hCcount, hCerror⟩ :=
    exists_twoLocal_projectiveTrotterCircuit hn H hlocal t r hr hsmall'
  refine ⟨c, hc, C, hCcount, hCerror.trans ?_⟩
  rw [twoLocalSkewGeneratorList_length]
  have hsum0 : 0 ≤ ((twoLocalSkewGeneratorList H).map norm).sum :=
    List.sum_nonneg (by simp)
  have hbound0 : 0 ≤ (Fintype.card (PauliTracelessLabel n 2) : ℝ) *
      ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)‖ := by positivity
  have hsumSq : ((twoLocalSkewGeneratorList H).map norm).sum ^ (2 : ℕ) ≤
      ((Fintype.card (PauliTracelessLabel n 2) : ℝ) *
        ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖) ^ (2 : ℕ) :=
    (sq_le_sq₀ hsum0 hbound0).2 hsum
  have hr0 : (0 : ℝ) ≤ r := by positivity
  calc
    3 * (Fintype.card (PauliTracelessLabel n 2) : ℝ) *
          ((twoLocalSkewGeneratorList H).map norm).sum ^ (2 : ℕ) * |t| ^ (2 : ℕ) / r ≤
        3 * (Fintype.card (PauliTracelessLabel n 2) : ℝ) *
          (((Fintype.card (PauliTracelessLabel n 2) : ℝ) *
            ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)‖) ^ (2 : ℕ)) * |t| ^ (2 : ℕ) / r := by
            gcongr
    _ = 3 * (Fintype.card (PauliTracelessLabel n 2) : ℝ) ^ (3 : ℕ) *
          ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) * |t| ^ (2 : ℕ) / r := by ring

end

end GaloisForLFunctions.HTGeometry
