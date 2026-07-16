import GaloisForLFunctions.HTGeometry.QuantumBinomialRootOfUnity
import GaloisForLFunctions.HTGeometry.GeneralExteriorPrincipalSymbolDecoder

/-!
# Quadratic-width quantum detector

Only grades zero, one, and two are needed to retain every coordinate bivector.  This module
constructs a truncated quantum-exterior packet on those three grades.  Its generators are
square-zero and ordered `q`-commuting, while their quadratic monomials have an exact pair-state
vacuum readout.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {M : Type v} [AddCommGroup M] [Module K M]
  {d n : ℕ} [NeZero d] [Fact (1 < d)]

/-- The three detector grades: vacuum, one-coordinate states, and increasing pairs. -/
inductive QuadraticQuantumDetectorIndex (n : ℕ)
  | root
  | single (i : Fin n)
  | pair (p : QuantumLawPair (Fin n))
  deriving DecidableEq

/-- Amplitudes on the quadratic detector grades. -/
abbrev QuadraticQuantumDetectorState (M : Type v) (n : ℕ) :=
  QuadraticQuantumDetectorIndex n → M

/-- Vacuum amplitude concentrated in grade zero. -/
def quadraticQuantumDetectorRoot (m : M) :
    QuadraticQuantumDetectorState M n :=
  Pi.single .root m

/-- One-coordinate detector amplitude. -/
def quadraticQuantumDetectorSingleState (i : Fin n) (m : M) :
    QuadraticQuantumDetectorState M n :=
  Pi.single (.single i) m

/-- Two-coordinate detector amplitude. -/
def quadraticQuantumDetectorPairState
    (p : QuantumLawPair (Fin n)) (m : M) :
    QuadraticQuantumDetectorState M n :=
  Pi.single (.pair p) m

/-- A truncated quantum-exterior generator.  It raises vacuum to grade one, grade one to grade
two with the ordered `q` phase, and kills grade two. -/
def quadraticQuantumDetectorGenerator (q : K) (i : Fin n) :
    Module.End K (QuadraticQuantumDetectorState M n) where
  toFun f
    | .root => 0
    | .single j => if j = i then f .root else 0
    | .pair p =>
        if i = p.lower then q • f (.single p.upper)
        else if i = p.upper then f (.single p.lower)
        else 0
  map_add' f g := by
    funext x
    cases x with
    | root => simp
    | single j => by_cases hji : j = i <;> simp [hji]
    | pair p =>
        have hne : p.upper ≠ p.lower := ne_of_gt p.isLt
        by_cases hil : i = p.lower
        · simp [hil, smul_add]
        · by_cases hiu : i = p.upper
          · subst i
            simp [hil, hne]
          · simp [hil, hiu]
  map_smul' c f := by
    funext x
    cases x with
    | root => simp
    | single j => by_cases hji : j = i <;> simp [hji]
    | pair p =>
        have hne : p.upper ≠ p.lower := ne_of_gt p.isLt
        by_cases hil : i = p.lower
        · simp [hil, smul_smul, mul_comm]
        · by_cases hiu : i = p.upper
          · subst i
            simp [hil, hne]
          · simp [hil, hiu]

@[simp]
theorem quadraticQuantumDetectorGenerator_root
    (q : K) (i : Fin n) (m : M) :
    quadraticQuantumDetectorGenerator (M := M) q i
        (quadraticQuantumDetectorRoot (n := n) m) =
      quadraticQuantumDetectorSingleState i m := by
  classical
  funext x
  cases x with
  | root => simp [quadraticQuantumDetectorGenerator,
      quadraticQuantumDetectorRoot, quadraticQuantumDetectorSingleState]
  | single j =>
      by_cases hji : j = i
      · subst j
        simp [quadraticQuantumDetectorGenerator, quadraticQuantumDetectorRoot,
          quadraticQuantumDetectorSingleState, Pi.single_apply]
      · simp [quadraticQuantumDetectorGenerator, quadraticQuantumDetectorRoot,
          quadraticQuantumDetectorSingleState, Pi.single_apply, hji]
  | pair p =>
      simp [quadraticQuantumDetectorGenerator, quadraticQuantumDetectorRoot,
        quadraticQuantumDetectorSingleState]

/-- Applying a lower generator after a higher one records `q` times their pair state. -/
theorem quadraticQuantumDetectorGenerator_singleState_of_lt
    (q : K) {i j : Fin n} (hij : i < j) (m : M) :
    quadraticQuantumDetectorGenerator (M := M) q i
        (quadraticQuantumDetectorSingleState j m) =
      q • quadraticQuantumDetectorPairState ⟨i, j, hij⟩ m := by
  classical
  funext x
  cases x with
  | root => simp [quadraticQuantumDetectorGenerator,
      quadraticQuantumDetectorSingleState, quadraticQuantumDetectorPairState]
  | single k =>
      simp [quadraticQuantumDetectorGenerator,
        quadraticQuantumDetectorSingleState, quadraticQuantumDetectorPairState,
        Pi.single_apply]
  | pair p =>
      by_cases hp : p = ⟨i, j, hij⟩
      · subst p
        simp [quadraticQuantumDetectorGenerator,
          quadraticQuantumDetectorSingleState, quadraticQuantumDetectorPairState,
          Pi.single_apply, ne_of_lt hij]
      · have hindex :
            (QuadraticQuantumDetectorIndex.pair ⟨i, j, hij⟩ :
                QuadraticQuantumDetectorIndex n) ≠ .pair p := by
            intro h
            apply hp
            injection h with hpair
            exact hpair.symm
        rw [quadraticQuantumDetectorPairState]
        simp only [Pi.smul_apply, Pi.single_apply, if_neg hindex.symm, smul_zero]
        by_cases hil : i = p.lower
        · have hupper : p.upper ≠ j := by
            intro hu
            apply hp
            cases p
            simp_all
          simp [quadraticQuantumDetectorGenerator,
            quadraticQuantumDetectorSingleState, Pi.single_apply, hil, hupper]
        · by_cases hiu : i = p.upper
          · have hlower : p.lower ≠ j := by
              intro hl
              have hback : p.upper < p.lower := by simpa [hiu, hl] using hij
              exact (not_lt_of_ge (le_of_lt p.isLt)) hback
            have hne : p.upper ≠ p.lower := ne_of_gt p.isLt
            simp [quadraticQuantumDetectorGenerator,
              quadraticQuantumDetectorSingleState, Pi.single_apply, hil, hiu, hlower, hne]
          · simp [quadraticQuantumDetectorGenerator,
              quadraticQuantumDetectorSingleState, Pi.single_apply, hil, hiu]

/-- Applying a higher generator after a lower one records their unscaled pair state. -/
theorem quadraticQuantumDetectorGenerator_singleState_of_gt
    (q : K) {i j : Fin n} (hij : i < j) (m : M) :
    quadraticQuantumDetectorGenerator (M := M) q j
        (quadraticQuantumDetectorSingleState i m) =
      quadraticQuantumDetectorPairState ⟨i, j, hij⟩ m := by
  classical
  funext x
  cases x with
  | root => simp [quadraticQuantumDetectorGenerator,
      quadraticQuantumDetectorSingleState, quadraticQuantumDetectorPairState]
  | single k =>
      simp [quadraticQuantumDetectorGenerator,
        quadraticQuantumDetectorSingleState, quadraticQuantumDetectorPairState,
        Pi.single_apply, ne_of_lt hij]
  | pair p =>
      by_cases hp : p = ⟨i, j, hij⟩
      · subst p
        simp [quadraticQuantumDetectorGenerator,
          quadraticQuantumDetectorSingleState, quadraticQuantumDetectorPairState,
          Pi.single_apply, ne_of_lt hij, (ne_of_lt hij).symm]
      · have hindex :
            (QuadraticQuantumDetectorIndex.pair ⟨i, j, hij⟩ :
                QuadraticQuantumDetectorIndex n) ≠ .pair p := by
            intro h
            apply hp
            injection h with hpair
            exact hpair.symm
        rw [quadraticQuantumDetectorPairState]
        simp only [Pi.single_apply, if_neg hindex.symm]
        by_cases hjl : j = p.lower
        · have hupper : p.upper ≠ i := by
            intro hu
            have hback : p.upper < p.lower := by simpa [hjl, hu] using hij
            exact (not_lt_of_ge (le_of_lt p.isLt)) hback
          simp [quadraticQuantumDetectorGenerator,
            quadraticQuantumDetectorSingleState, Pi.single_apply, hjl, hupper]
        · by_cases hju : j = p.upper
          · have hlower : p.lower ≠ i := by
              intro hl
              apply hp
              cases p
              simp_all
            have hne : p.upper ≠ p.lower := ne_of_gt p.isLt
            simp [quadraticQuantumDetectorGenerator,
              quadraticQuantumDetectorSingleState, Pi.single_apply, hjl, hju, hlower, hne]
          · simp [quadraticQuantumDetectorGenerator,
              quadraticQuantumDetectorSingleState, Pi.single_apply, hjl, hju]

/-- The product of two distinct generators depends only on the vacuum coordinate. -/
theorem quadraticQuantumDetectorGenerator_mul_of_lt
    (q : K) {i j : Fin n} (hij : i < j) :
    quadraticQuantumDetectorGenerator (M := M) q i *
        quadraticQuantumDetectorGenerator (M := M) q j =
      q • (quadraticQuantumDetectorGenerator (M := M) q j *
        quadraticQuantumDetectorGenerator (M := M) q i) := by
  apply LinearMap.ext
  intro f
  have hdecompose : f = quadraticQuantumDetectorRoot (n := n) (f .root) +
      (f - quadraticQuantumDetectorRoot (n := n) (f .root)) := by abel
  rw [hdecompose]
  simp only [map_add, Module.End.mul_apply, LinearMap.smul_apply]
  rw [quadraticQuantumDetectorGenerator_root,
    quadraticQuantumDetectorGenerator_root,
    quadraticQuantumDetectorGenerator_singleState_of_lt q hij,
    quadraticQuantumDetectorGenerator_singleState_of_gt q hij]
  have hrootzero :
      (f - quadraticQuantumDetectorRoot (n := n) (f .root))
        (.root : QuadraticQuantumDetectorIndex n) = 0 := by
    classical
    simp [quadraticQuantumDetectorRoot]
  have htail (k : Fin n) :
      quadraticQuantumDetectorGenerator (M := M) q k
        (f - quadraticQuantumDetectorRoot (n := n) (f .root))
          (.root : QuadraticQuantumDetectorIndex n) = 0 := by
    simp [quadraticQuantumDetectorGenerator]
  have hdouble (a b : Fin n) :
      quadraticQuantumDetectorGenerator (M := M) q a
        (quadraticQuantumDetectorGenerator (M := M) q b
          (f - quadraticQuantumDetectorRoot (n := n) (f .root))) = 0 := by
    funext x
    cases x with
    | root => simp [quadraticQuantumDetectorGenerator]
    | single k => simp [quadraticQuantumDetectorGenerator, htail]
    | pair p =>
        simp [quadraticQuantumDetectorGenerator, quadraticQuantumDetectorRoot,
          Pi.single_apply]
  rw [hdouble i j, hdouble j i]
  simp

/-- Every quadratic detector generator is square-zero. -/
theorem quadraticQuantumDetectorGenerator_sq
    (q : K) (i : Fin n) :
    (quadraticQuantumDetectorGenerator (M := M) q i) ^ 2 = 0 := by
  apply LinearMap.ext
  intro f
  funext x
  cases x with
  | root => simp [quadraticQuantumDetectorGenerator, Module.End.mul_apply, pow_two]
  | single j =>
      by_cases hji : j = i <;>
        simp [quadraticQuantumDetectorGenerator, Module.End.mul_apply, pow_two, hji]
  | pair p =>
      have hne : p.lower ≠ p.upper := ne_of_lt p.isLt
      by_cases hil : i = p.lower
      · subst i
        simp [quadraticQuantumDetectorGenerator, Module.End.mul_apply, pow_two,
          Pi.single_apply, hne, hne.symm]
      · by_cases hiu : i = p.upper
        · subst i
          simp [quadraticQuantumDetectorGenerator, Module.End.mul_apply, pow_two,
            Pi.single_apply, hil, hne, hne.symm]
        · simp [quadraticQuantumDetectorGenerator, Module.End.mul_apply, pow_two,
            Pi.single_apply, hil, hiu, hne, hne.symm]

/-- Every generator has zero `d`th power for every `d > 1`. -/
theorem quadraticQuantumDetectorGenerator_pow_degree
    (q : K) (i : Fin n) :
    (quadraticQuantumDetectorGenerator (M := M) q i) ^ d = 0 := by
  have hd : 2 ≤ d := Nat.succ_le_iff.mpr Fact.out
  rw [show d = 2 + (d - 2) by omega, pow_add,
    quadraticQuantumDetectorGenerator_sq]
  simp

/-- The quadratic detector pencil. -/
def quadraticQuantumDetectorSymbol (q : K) :
    (Fin n → K) →ₗ[K]
      Module.End K (QuadraticQuantumDetectorState M n) :=
  quantumGeneratorSymbol
    (fun i : Fin n ↦ quadraticQuantumDetectorGenerator (M := M) q i)

/-- Every value of the quadratic detector pencil has zero `d`th power. -/
theorem quadraticQuantumDetectorSymbol_pow_degree_zero
    (q : K) (hq : IsPrimitiveRoot q d) (c : Fin n → K) :
    (quadraticQuantumDetectorSymbol (M := M) q c) ^ d = 0 := by
  rw [quadraticQuantumDetectorSymbol, quantumGeneratorSymbol,
    Fintype.linearCombination_apply,
    quantumMultinomial_fin_smul_pow_primitive hq
      (lt_trans Nat.zero_lt_one Fact.out)
      (fun i : Fin n ↦ quadraticQuantumDetectorGenerator (M := M) q i) c
      (fun i j hij ↦ quadraticQuantumDetectorGenerator_mul_of_lt q hij)]
  simp [quadraticQuantumDetectorGenerator_pow_degree]

/-- Ordered quadratic monomials send the vacuum to distinct pair states. -/
theorem quadraticQuantumDetectorPairOperator_root
    (q : K) (m : M) (p : QuantumLawPair (Fin n)) :
    quantumPairOperator
        (fun i : Fin n ↦ quadraticQuantumDetectorGenerator (M := M) q i) p
        (quadraticQuantumDetectorRoot (n := n) m) =
      quadraticQuantumDetectorPairState p m := by
  rw [quantumPairOperator, Module.End.mul_apply,
    quadraticQuantumDetectorGenerator_root,
    quadraticQuantumDetectorGenerator_singleState_of_gt q p.isLt]

/-- For a nonzero vacuum amplitude, the quadratic monomials are linearly independent. -/
theorem quadraticQuantumDetectorPairOperator_linearIndependent
    (q : K) (m : M) (hm : m ≠ 0) :
    LinearIndependent K
      (quantumPairOperator
        (fun i : Fin n ↦ quadraticQuantumDetectorGenerator (M := M) q i)) := by
  apply LinearIndependent.of_comp
    (LinearMap.applyₗ (R := K) (quadraticQuantumDetectorRoot (n := n) m))
  have hstate : ∀ p : QuantumLawPair (Fin n),
      (quadraticQuantumDetectorPairState p m :
        QuadraticQuantumDetectorState M n) ≠ 0 := by
    intro p hzero
    have hp := congrFun hzero (.pair p)
    exact hm (by simpa [quadraticQuantumDetectorPairState] using hp)
  have hsingle : LinearIndependent K
      (fun p : QuantumLawPair (Fin n) ↦
        quadraticQuantumDetectorPairState p m) := by
    have hall : LinearIndependent K
        (fun x : QuadraticQuantumDetectorIndex n ↦ Pi.single x m) :=
      Pi.linearIndependent_single_of_ne_zero (R := K) (M := M)
        (v := fun _x : QuadraticQuantumDetectorIndex n ↦ m) (fun _x ↦ hm)
    exact hall.comp (fun p : QuantumLawPair (Fin n) ↦ .pair p) (by
      intro p r hpr
      cases hpr
      rfl)
  simpa [Function.comp_def, quadraticQuantumDetectorPairOperator_root] using hsingle

/-- The three-grade zero-form detector already has a faithful full exterior commutator symbol. -/
theorem quadraticQuantumDetector_endomorphismCommutatorMap_injective
    (q : K) (hq : IsPrimitiveRoot q d) (m : M) (hm : m ≠ 0) :
    Function.Injective
      (endomorphismCommutatorMap
        (quadraticQuantumDetectorSymbol (M := M) (n := n) q)) := by
  exact quantumGenerator_endomorphismCommutatorMap_injective
    q (fun i : Fin n ↦ quadraticQuantumDetectorGenerator (M := M) q i)
    (hq.ne_one Fact.out)
    (fun i j hij ↦ quadraticQuantumDetectorGenerator_mul_of_lt q hij)
    (quadraticQuantumDetectorPairOperator_linearIndependent q m hm)

end

end GaloisForLFunctions.HTGeometry
