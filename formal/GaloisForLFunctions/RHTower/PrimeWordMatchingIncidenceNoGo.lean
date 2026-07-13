import GaloisForLFunctions.RHTower.PrimeWordEnsembleBoundaryTomography
import GaloisForLFunctions.RHTower.PrimeSupportMultivariateLiftMarker

/-!
# Support-cardinality jets do not determine matching incidence

Two finite two-edge word ensembles can have identical support-cardinality boundary germs while
one pair of supports is disjoint and the other pair intersects.  Thus the one-variable jet tower,
although lossless on support-cardinality strata, cannot by itself determine the matching numbers
needed by a monomer--dimer polynomial.

The positive repair is also finite: the squarefree multivariate ensemble marker separates the same
two packets.  A matching-polynomial detour must retain the multivariate incidence packet before
forming disjoint-support matching sums.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open Polynomial

def matchingEdge01 : List (Fin 4) := [0, 1]
def matchingEdge23 : List (Fin 4) := [2, 3]
def matchingEdge02 : List (Fin 4) := [0, 2]

/-- Two disjoint two-letter supports. -/
def disjointTwoEdgeEnsemble : Finset (List (Fin 4)) :=
  {matchingEdge01, matchingEdge23}

/-- Two intersecting two-letter supports. -/
def intersectingTwoEdgeEnsemble : Finset (List (Fin 4)) :=
  {matchingEdge01, matchingEdge02}

def unitWordWeight (_ : List (Fin 4)) : ℤ := 1

def wordSupportsDisjoint (u v : List (Fin 4)) : Prop :=
  Disjoint (GaloisForLFunctions.primeWordSupport u)
    (GaloisForLFunctions.primeWordSupport v)

/-- Sum of the squarefree support monomials in an ensemble. -/
noncomputable def primeWordEnsembleSquarefreeMarker
    (S : Finset (List (Fin 4))) : MvPolynomial (Fin 4) ℤ :=
  ∑ w ∈ S, primeWordSquarefreeMarker w

/-- A specialization selecting the second disjoint edge. -/
def matchingIncidenceProbe (i : Fin 4) : ℤ :=
  if i = 2 ∨ i = 3 then 1 else 0

/-- The one-variable marked deformations, hence all their boundary jets, are identical. -/
theorem disjointTwoEdgeEnsemble_deformation_eq_intersecting :
    primeWordEnsembleDeformation disjointTwoEdgeEnsemble unitWordWeight =
      primeWordEnsembleDeformation intersectingTwoEdgeEnsemble unitWordWeight := by
  simp [primeWordEnsembleDeformation, disjointTwoEdgeEnsemble,
    intersectingTwoEdgeEnsemble, unitWordWeight, matchingEdge01, matchingEdge23,
    matchingEdge02, GaloisForLFunctions.primeWordSupport,
    primeSupportMarkedDeformation]

theorem matchingEdge01_edge23_disjoint :
    wordSupportsDisjoint matchingEdge01 matchingEdge23 := by
  simp [wordSupportsDisjoint, matchingEdge01, matchingEdge23,
    GaloisForLFunctions.primeWordSupport, Finset.disjoint_left]

theorem matchingEdge01_edge02_not_disjoint :
    ¬ wordSupportsDisjoint matchingEdge01 matchingEdge02 := by
  simp [wordSupportsDisjoint, matchingEdge01, matchingEdge02,
    GaloisForLFunctions.primeWordSupport, Finset.disjoint_left]

/-- The multivariate marker retains enough incidence data to distinguish the packets. -/
theorem multivariateMarker_separates_twoEdgeMatchingIncidence :
    primeWordEnsembleSquarefreeMarker disjointTwoEdgeEnsemble ≠
      primeWordEnsembleSquarefreeMarker intersectingTwoEdgeEnsemble := by
  intro h
  have he := congrArg
    (fun P : MvPolynomial (Fin 4) ℤ => MvPolynomial.eval matchingIncidenceProbe P) h
  simp [primeWordEnsembleSquarefreeMarker, disjointTwoEdgeEnsemble,
    intersectingTwoEdgeEnsemble, eval_primeWordSquarefreeMarker,
    matchingIncidenceProbe, matchingEdge01, matchingEdge23, matchingEdge02,
    GaloisForLFunctions.primeWordSupport] at he

/-- Positive no-go capstone: all scalar boundary jets coincide while matching incidence differs,
and the multivariate support packet repairs that blindness. -/
theorem boundaryGerm_blind_to_twoEdgeMatchingIncidence :
    (∀ r : ℕ,
      ((derivative^[r])
        (primeWordEnsembleDeformation disjointTwoEdgeEnsemble unitWordWeight)).eval 1 =
      ((derivative^[r])
        (primeWordEnsembleDeformation intersectingTwoEdgeEnsemble unitWordWeight)).eval 1) ∧
      wordSupportsDisjoint matchingEdge01 matchingEdge23 ∧
      ¬ wordSupportsDisjoint matchingEdge01 matchingEdge02 ∧
      primeWordEnsembleSquarefreeMarker disjointTwoEdgeEnsemble ≠
        primeWordEnsembleSquarefreeMarker intersectingTwoEdgeEnsemble := by
  refine ⟨?_, matchingEdge01_edge23_disjoint, matchingEdge01_edge02_not_disjoint,
    multivariateMarker_separates_twoEdgeMatchingIncidence⟩
  intro r
  rw [disjointTwoEdgeEnsemble_deformation_eq_intersecting]

end GaloisForLFunctions.RHTower
