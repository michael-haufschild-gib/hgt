import GaloisForLFunctions.HTGeometry.AiryTowerFiniteFiber

open scoped BigOperators

namespace GaloisForLFunctions.IrregularStokes

noncomputable section

/-- Fixed labelled decorated diagram, allowing nonzero diagonal entries. -/
structure DecoratedDiagram (n : ℕ) where
  B : Fin n → Fin n → ℕ
  B_symm : ∀ i j, B i j = B j i
  ramification : Fin n → ℕ
  ramification_pos : ∀ i, 0 < ramification i

namespace DecoratedDiagram

/-- Weighted irregularity forced by the diagonal Stokes formula. -/
def localWeight {n : ℕ} (d : DecoratedDiagram n) (i : Fin n) : ℕ :=
  d.B i i + d.ramification i ^ (2 : ℕ) - 1

/-- Total on the nonnegative side of the affine pair equation. -/
def pairTotal {n : ℕ} (d : DecoratedDiagram n) (i j : Fin n) : ℕ :=
  d.B i j + d.ramification i * d.ramification j

/-- Full pair-fission datum on one combinatorial interval.  The equation is the natural-number
form of `B = C + s*g - r_i*r_j`; `g` is a positive divisor of the right ramification. -/
@[ext] structure PairFissionDatum {n : ℕ} (d : DecoratedDiagram n) (i j : Fin n) where
  commonPrefixCase : Fin ((d.localWeight i + 1) * (d.localWeight j + 1) + 1)
  siblingCase : Fin 4
  fixedPart : ℕ
  gcdFactor : ℕ
  gcdFactor_pos : 0 < gcdFactor
  gcdFactor_dvd : gcdFactor ∣ d.ramification j
  fissionNumerator : ℕ
  edgeEquation : d.pairTotal i j = fixedPart + fissionNumerator * gcdFactor

namespace PairFissionDatum

theorem fixedPart_le {n : ℕ} {d : DecoratedDiagram n} {i j : Fin n}
    (p : d.PairFissionDatum i j) : p.fixedPart ≤ d.pairTotal i j := by
  rw [p.edgeEquation]
  omega

theorem gcdFactor_le {n : ℕ} {d : DecoratedDiagram n} {i j : Fin n}
    (p : d.PairFissionDatum i j) : p.gcdFactor ≤ d.ramification j := by
  exact Nat.le_of_dvd (d.ramification_pos j) p.gcdFactor_dvd

theorem fissionNumerator_le {n : ℕ} {d : DecoratedDiagram n} {i j : Fin n}
    (p : d.PairFissionDatum i j) : p.fissionNumerator ≤ d.pairTotal i j := by
  have hmul : p.fissionNumerator ≤ p.fissionNumerator * p.gcdFactor := by
    calc
      p.fissionNumerator = p.fissionNumerator * 1 := by simp
      _ ≤ p.fissionNumerator * p.gcdFactor :=
        Nat.mul_le_mul_left _ p.gcdFactor_pos
  calc
    p.fissionNumerator ≤ p.fissionNumerator * p.gcdFactor := hmul
    _ ≤ p.fixedPart + p.fissionNumerator * p.gcdFactor := by omega
    _ = d.pairTotal i j := p.edgeEquation.symm

/-- Finite bounded encoding exposed by positivity of the affine coefficient. -/
structure Encoding {n : ℕ} (d : DecoratedDiagram n) (i j : Fin n) where
  commonPrefixCase : Fin ((d.localWeight i + 1) * (d.localWeight j + 1) + 1)
  siblingCase : Fin 4
  fixedPart : Fin (d.pairTotal i j + 1)
  gcdFactor : Fin (d.ramification j + 1)
  fissionNumerator : Fin (d.pairTotal i j + 1)
  deriving Fintype

def encode {n : ℕ} {d : DecoratedDiagram n} {i j : Fin n}
    (p : d.PairFissionDatum i j) : Encoding d i j where
  commonPrefixCase := p.commonPrefixCase
  siblingCase := p.siblingCase
  fixedPart := ⟨p.fixedPart, Nat.lt_succ_of_le p.fixedPart_le⟩
  gcdFactor := ⟨p.gcdFactor, Nat.lt_succ_of_le p.gcdFactor_le⟩
  fissionNumerator := ⟨p.fissionNumerator, Nat.lt_succ_of_le p.fissionNumerator_le⟩

theorem encode_injective {n : ℕ} {d : DecoratedDiagram n} {i j : Fin n} :
    Function.Injective (@encode n d i j) := by
  intro p q h
  apply PairFissionDatum.ext
  · exact congrArg Encoding.commonPrefixCase h
  · exact congrArg Encoding.siblingCase h
  · exact congrArg (fun x => x.fixedPart.val) h
  · exact congrArg (fun x => x.gcdFactor.val) h
  · exact congrArg (fun x => x.fissionNumerator.val) h

instance finite {n : ℕ} (d : DecoratedDiagram n) (i j : Fin n) :
    Finite (d.PairFissionDatum i j) := by
  apply Finite.of_injective encode
  exact encode_injective

/-- For fixed discrete case and fixed affine part, positive slope makes the fission numerator
unique. -/
theorem fissionNumerator_unique {n : ℕ} {d : DecoratedDiagram n} {i j : Fin n}
    (p q : d.PairFissionDatum i j) (hfixed : p.fixedPart = q.fixedPart)
    (hgcd : p.gcdFactor = q.gcdFactor) :
    p.fissionNumerator = q.fissionNumerator := by
  have hp := p.edgeEquation
  have hq := q.edgeEquation
  rw [hfixed, hgcd] at hp
  have hmul : p.fissionNumerator * q.gcdFactor =
      q.fissionNumerator * q.gcdFactor := by omega
  exact Nat.eq_of_mul_eq_mul_right q.gcdFactor_pos hmul

end PairFissionDatum

/-- Raw full data for a labelled fission tree over one decorated diagram. -/
structure RawFissionTreeCode {n : ℕ} (d : DecoratedDiagram n) where
  localData : ∀ i, FixedWeightedCharacteristic (d.ramification i) (d.localWeight i)
  pair : ∀ i j, i ≠ j → d.PairFissionDatum i j

instance finite_rawFissionTreeCode {n : ℕ} (d : DecoratedDiagram n) :
    Finite (RawFissionTreeCode d) := by
  letI localFinite (i : Fin n) :
      Finite (FixedWeightedCharacteristic (d.ramification i) (d.localWeight i)) :=
    finite_fixedWeightedCharacteristic _ _
  let Encoding :=
    (∀ i, FixedWeightedCharacteristic (d.ramification i) (d.localWeight i)) ×
      (∀ i j, i ≠ j → d.PairFissionDatum i j)
  let encode : RawFissionTreeCode d → Encoding := fun code =>
    ⟨code.localData, code.pair⟩
  haveI : Finite Encoding := inferInstance
  apply Finite.of_injective encode
  intro left right h
  cases left
  cases right
  cases h
  rfl

/-- A labelled fission tree is its complete local and pair code, filtered by all fission-tree
compatibility axioms.  Keeping the predicate explicit makes the finiteness theorem independent of
the particular equivalent axiomatisation of compatibility. -/
def LabelledFissionTree {n : ℕ} (d : DecoratedDiagram n)
    (Compatible : RawFissionTreeCode d → Prop) : Type :=
  { code : RawFissionTreeCode d // Compatible code }

instance finite_labelledFissionTree {n : ℕ} (d : DecoratedDiagram n)
    (Compatible : RawFissionTreeCode d → Prop) :
    Finite (LabelledFissionTree d Compatible) := by
  unfold LabelledFissionTree
  infer_instance

/-- **Decorated finite-fibre theorem.**  Fixing labelled core and ramification makes every exact
compatibility-filtered fission-tree fibre finite. -/
theorem decorated_fissionTree_fiber_finite {n : ℕ} (d : DecoratedDiagram n)
    (Compatible : RawFissionTreeCode d → Prop) :
    Set.Finite (Set.univ : Set (LabelledFissionTree d Compatible)) := by
  exact Set.toFinite _

/-- The finite fibre admits a complete enumeration. -/
@[reducible] noncomputable def decoratedFissionTreeFiberFintype {n : ℕ}
    (d : DecoratedDiagram n)
    (Compatible : RawFissionTreeCode d → Prop) :
    Fintype (LabelledFissionTree d Compatible) :=
  Fintype.ofFinite _

/-- Explicit complete list of the fixed decorated fibre. -/
noncomputable def enumerateDecoratedFissionTreeFiber {n : ℕ} (d : DecoratedDiagram n)
    (Compatible : RawFissionTreeCode d → Prop) :
    List (LabelledFissionTree d Compatible) := by
  letI := d.decoratedFissionTreeFiberFintype Compatible
  exact Finset.univ.toList

@[simp] theorem mem_enumerateDecoratedFissionTreeFiber {n : ℕ}
    (d : DecoratedDiagram n) (Compatible : RawFissionTreeCode d → Prop)
    (tree : LabelledFissionTree d Compatible) :
    tree ∈ d.enumerateDecoratedFissionTreeFiber Compatible := by
  simp [enumerateDecoratedFissionTreeFiber]

end DecoratedDiagram
end
end GaloisForLFunctions.IrregularStokes
