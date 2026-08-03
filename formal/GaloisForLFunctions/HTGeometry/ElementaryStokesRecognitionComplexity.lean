import GaloisForLFunctions.HTGeometry.ElementaryStokesGlobalPuiseuxRealization

namespace GaloisForLFunctions.IrregularStokes

open scoped BigOperators

namespace ElementaryDecoratedGraph

/-- Ordered pair queries used by exhaustive spectrum recognition. -/
abbrev PairRecognitionQuery (n : ℕ) := Fin n × Fin n

/-- Ordered triple queries used by exhaustive acute-isosceles recognition. -/
abbrev TriangleRecognitionQuery (n : ℕ) := Fin n × Fin n × Fin n

/-- Complete unit-cost query schedule. -/
abbrev RecognitionQuery (n : ℕ) :=
  PairRecognitionQuery n ⊕ TriangleRecognitionQuery n

/-- Exact number of pair and triangle queries in the exhaustive recognizer. -/
def recognitionComparisonBudget (n : ℕ) : ℕ := n ^ 2 + n ^ 3

theorem card_pairRecognitionQuery (n : ℕ) :
    Fintype.card (PairRecognitionQuery n) = n ^ 2 := by
  simp [PairRecognitionQuery, pow_two]

theorem card_triangleRecognitionQuery (n : ℕ) :
    Fintype.card (TriangleRecognitionQuery n) = n ^ 3 := by
  simp [TriangleRecognitionQuery, pow_succ, Nat.mul_assoc]

theorem card_recognitionQuery (n : ℕ) :
    Fintype.card (RecognitionQuery n) = recognitionComparisonBudget n := by
  simp [RecognitionQuery, recognitionComparisonBudget]
  ring

/-- Concrete cubic bound, avoiding asymptotic notation or a hidden bit-complexity model. -/
theorem recognitionComparisonBudget_le_two_cubes {n : ℕ} (hn : 0 < n) :
    recognitionComparisonBudget n ≤ 2 * n ^ 3 := by
  unfold recognitionComparisonBudget
  have hnle : n ^ 2 ≤ n ^ 3 := by
    calc
      n ^ 2 = n ^ 2 * 1 := by simp
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_left _ hn
      _ = n ^ 3 := by ring
  omega

/-- Truth value represented by one ordered pair query. -/
def pairQueryHolds {n : ℕ} (g : ElementaryDecoratedGraph n)
    (q : PairRecognitionQuery n) : Prop :=
  q.1 = q.2 ∨ InElementaryPairSpectrum
    (g.ramification q.1) (g.ramification q.2) (g.edge q.1 q.2)

/-- Truth value represented by one ordered triple query. -/
def triangleQueryHolds {n : ℕ} (g : ElementaryDecoratedGraph n)
    (q : TriangleRecognitionQuery n) : Prop :=
  g.rescaledEdge q.1 q.2.1 ≤ max (g.rescaledEdge q.1 q.2.2)
      (g.rescaledEdge q.2.1 q.2.2) ∧
  g.rescaledEdge q.1 q.2.2 ≤ max (g.rescaledEdge q.1 q.2.1)
      (g.rescaledEdge q.2.1 q.2.2) ∧
  g.rescaledEdge q.2.1 q.2.2 ≤ max (g.rescaledEdge q.1 q.2.1)
      (g.rescaledEdge q.1 q.2.2)

theorem all_pairQueries_iff {n : ℕ} (g : ElementaryDecoratedGraph n) :
    (∀ q : PairRecognitionQuery n, g.pairQueryHolds q) ↔ g.HasPairSpectra := by
  constructor
  · intro hall i j hij
    exact (hall (i, j)).resolve_left hij
  · intro hpairs q
    by_cases h : q.1 = q.2
    · exact Or.inl h
    · exact Or.inr (hpairs q.1 q.2 h)

theorem all_triangleQueries_iff {n : ℕ} (g : ElementaryDecoratedGraph n) :
    (∀ q : TriangleRecognitionQuery n, g.triangleQueryHolds q) ↔
      g.HasAcuteIsoscelesRescaling := by
  constructor
  · intro hall i j k
    exact hall (i, j, k)
  · intro hacute q
    exact hacute q.1 q.2.1 q.2.2

/-- Exact exhaustive-query characterization of elementary recognition. -/
theorem all_recognitionQueries_iff_certificate {n : ℕ}
    (g : ElementaryDecoratedGraph n) :
    ((∀ q : PairRecognitionQuery n, g.pairQueryHolds q) ∧
      ∀ q : TriangleRecognitionQuery n, g.triangleQueryHolds q) ↔
        g.HasElementaryRecognitionCertificate := by
  rw [g.all_pairQueries_iff, g.all_triangleQueries_iff]
  rfl

/-- Passing all `n²+n³` queries supplies the explicit simultaneous Puiseux reconstruction. -/
theorem globalPuiseux_reconstruction_of_all_queries {n : ℕ}
    (g : ElementaryDecoratedGraph n)
    (hqueries : (∀ q : PairRecognitionQuery n, g.pairQueryHolds q) ∧
      ∀ q : TriangleRecognitionQuery n, g.triangleQueryHolds q) :
    ∃ polynomials : Fin n → (ℚ →₀ ℂ),
      (∀ i, IsElementaryPuiseuxPolynomialOfRamification
          (g.ramification i) (polynomials i)) ∧
        ∀ i j, i ≠ j → ∃ e : ℚ,
          HasHighestDifferenceExponent
              (polynomials i) (polynomials j) e ∧
            HighestDifferenceRealizesEdge (g.ramification i) (g.ramification j)
              (g.edge i j) e := by
  exact g.globalPuiseux_realization_of_certificate
    ((g.all_recognitionQueries_iff_certificate).mp hqueries)

end ElementaryDecoratedGraph
end GaloisForLFunctions.IrregularStokes
