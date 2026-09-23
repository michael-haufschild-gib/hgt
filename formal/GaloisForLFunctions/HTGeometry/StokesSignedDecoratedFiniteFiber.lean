import GaloisForLFunctions.HTGeometry.StokesDecoratedFiniteFiber

/-!
# Finite decorated fibres with signed diagonal multiplicities

Off-diagonal Stokes edges are nonnegative, but diagonal loop multiplicities may be signed.  This
module retains the exact signed diagonal equation, proves that a negative forced local weight makes
the fibre empty, and extends the complete finite enumeration theorem to that genuine scope.
-/

namespace GaloisForLFunctions.IrregularStokes
noncomputable section

/-- Decorated Stokes diagram with signed diagonal multiplicities and nonnegative off-diagonal
edge multiplicities. -/
structure SignedDecoratedDiagram (n : ℕ) where
  diagonal : Fin n → ℤ
  edge : Fin n → Fin n → ℕ
  edge_symm : ∀ i j, edge i j = edge j i
  ramification : Fin n → ℕ
  ramification_pos : ∀ i, 0 < ramification i

namespace SignedDecoratedDiagram

def localWeight {n : ℕ} (d : SignedDecoratedDiagram n) (i : Fin n) : ℤ :=
  d.diagonal i + d.ramification i ^ (2 : ℕ) - 1

/-- Nonnegative shadow used only for off-diagonal pair data.  Its diagonal is a conservative bound
for prefix encodings; the exact signed local equation remains in `FixedSignedWeightedCharacteristic`. -/
def naturalShadow {n : ℕ} (d : SignedDecoratedDiagram n) : DecoratedDiagram n where
  B i j := if i = j then Int.toNat (d.diagonal i) else d.edge i j
  B_symm := by
    intro i j
    by_cases h : i = j
    · subst j
      simp
    · have h' : j ≠ i := Ne.symm h
      simp [h, h', d.edge_symm]
  ramification := d.ramification
  ramification_pos := d.ramification_pos

@[ext] structure FixedSignedWeightedCharacteristic (R : ℕ) (W : ℤ) where
  firstExponent : ℕ
  characteristic : Characteristic R firstExponent
  weighted_eq : (characteristic.weightedIrregularity : ℤ) = W

theorem FixedSignedWeightedCharacteristic.weight_nonneg {R : ℕ} {W : ℤ}
    (c : FixedSignedWeightedCharacteristic R W) : 0 ≤ W := by
  rw [← c.weighted_eq]
  exact_mod_cast Nat.zero_le c.characteristic.weightedIrregularity

def FixedSignedWeightedCharacteristic.toNatural {R : ℕ} {W : ℤ}
    (c : FixedSignedWeightedCharacteristic R W) :
    FixedWeightedCharacteristic R W.toNat where
  firstExponent := c.firstExponent
  characteristic := c.characteristic
  weighted_eq := by
    apply Int.ofNat_injective
    simpa [Int.toNat_of_nonneg c.weight_nonneg] using c.weighted_eq

theorem FixedSignedWeightedCharacteristic.toNatural_injective {R : ℕ} {W : ℤ} :
    Function.Injective
      (FixedSignedWeightedCharacteristic.toNatural (R := R) (W := W)) := by
  intro left right h
  cases left
  cases right
  cases h
  rfl

instance finite_fixedSignedWeightedCharacteristic (R : ℕ) (W : ℤ) :
    Finite (FixedSignedWeightedCharacteristic R W) := by
  letI : Finite (FixedWeightedCharacteristic R W.toNat) :=
    finite_fixedWeightedCharacteristic R W.toNat
  exact Finite.of_injective FixedSignedWeightedCharacteristic.toNatural
    FixedSignedWeightedCharacteristic.toNatural_injective

/-- Complete fixed-diagram code with signed local loop values. Pair data use the nonnegative edge
shadow; local data retain the exact signed diagonal equation. -/
structure RawFissionTreeCode {n : ℕ} (d : SignedDecoratedDiagram n) where
  localData : ∀ i,
    FixedSignedWeightedCharacteristic (d.ramification i) (d.localWeight i)
  pair : ∀ i j, i ≠ j → d.naturalShadow.PairFissionDatum i j

instance finite_rawFissionTreeCode {n : ℕ} (d : SignedDecoratedDiagram n) :
    Finite (RawFissionTreeCode d) := by
  let Encoding :=
    (∀ i, FixedSignedWeightedCharacteristic (d.ramification i) (d.localWeight i)) ×
      (∀ i j, i ≠ j → d.naturalShadow.PairFissionDatum i j)
  let encode : RawFissionTreeCode d → Encoding := fun code => ⟨code.localData, code.pair⟩
  haveI : Finite Encoding := inferInstance
  apply Finite.of_injective encode
  intro left right h
  cases left
  cases right
  cases h
  rfl

def LabelledFissionTree {n : ℕ} (d : SignedDecoratedDiagram n)
    (Compatible : RawFissionTreeCode d → Prop) : Type :=
  { code : RawFissionTreeCode d // Compatible code }

instance finite_labelledFissionTree {n : ℕ} (d : SignedDecoratedDiagram n)
    (Compatible : RawFissionTreeCode d → Prop) :
    Finite (LabelledFissionTree d Compatible) := by
  unfold LabelledFissionTree
  infer_instance

/-- **Signed decorated finite-fibre theorem.** Fixing signed diagonal loops, nonnegative pair edges,
and positive ramification makes every exact compatibility-filtered fission-tree fibre finite. -/
theorem decorated_fissionTree_fiber_finite {n : ℕ} (d : SignedDecoratedDiagram n)
    (Compatible : RawFissionTreeCode d → Prop) :
    Set.Finite (Set.univ : Set (LabelledFissionTree d Compatible)) := by
  exact Set.toFinite _

@[reducible] noncomputable def decoratedFissionTreeFiberFintype {n : ℕ}
    (d : SignedDecoratedDiagram n) (Compatible : RawFissionTreeCode d → Prop) :
    Fintype (LabelledFissionTree d Compatible) :=
  Fintype.ofFinite _

noncomputable def enumerateDecoratedFissionTreeFiber {n : ℕ}
    (d : SignedDecoratedDiagram n) (Compatible : RawFissionTreeCode d → Prop) :
    List (LabelledFissionTree d Compatible) := by
  letI := d.decoratedFissionTreeFiberFintype Compatible
  exact Finset.univ.toList

@[simp] theorem mem_enumerateDecoratedFissionTreeFiber {n : ℕ}
    (d : SignedDecoratedDiagram n) (Compatible : RawFissionTreeCode d → Prop)
    (tree : LabelledFissionTree d Compatible) :
    tree ∈ d.enumerateDecoratedFissionTreeFiber Compatible := by
  simp [enumerateDecoratedFissionTreeFiber]

/-- A negative forced local weight makes the signed fibre empty. -/
theorem no_tree_of_localWeight_neg {n : ℕ} (d : SignedDecoratedDiagram n)
    (Compatible : RawFissionTreeCode d → Prop) {i : Fin n}
    (hneg : d.localWeight i < 0) : IsEmpty (LabelledFissionTree d Compatible) := by
  constructor
  intro tree
  exact (not_le_of_gt hneg) (tree.1.localData i).weight_nonneg

end SignedDecoratedDiagram
end
end GaloisForLFunctions.IrregularStokes
