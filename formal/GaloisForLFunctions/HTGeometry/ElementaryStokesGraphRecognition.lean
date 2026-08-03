import GaloisForLFunctions.HTGeometry.ElementaryStokesPairSpectrum

/-!
# Decorated elementary Stokes-graph recognition

This file formalizes the finite cophenetic form of the elementary recognition theorem.  Vertices
carry ramification, edges carry diagram multiplicity, and pair contact mechanisms are the exact
presentations from `ElementaryStokesPairSpectrum`.  Global compatibility is precisely the
acute-isosceles condition on rescaled edge weights.

The resulting theorem is an if-and-only-if statement for labeled finite data.  It deliberately does
not identify graphs after forgetting ramification decoration.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- Finite labeled loopless Stokes graph with positive ramification decoration. -/
structure ElementaryDecoratedGraph (n : ℕ) where
  ramification : Fin n → ℕ
  ramification_pos : ∀ i, 0 < ramification i
  edge : Fin n → Fin n → ℕ
  edge_symm : ∀ i j, edge i j = edge j i
  loopless : ∀ i, edge i i = 0

namespace ElementaryDecoratedGraph

/-- Rescaled edge weight `Bᵢⱼ/(rᵢrⱼ)`. -/
def rescaledEdge {n : ℕ} (g : ElementaryDecoratedGraph n) (i j : Fin n) : ℚ :=
  (g.edge i j : ℚ) / ((g.ramification i * g.ramification j : ℕ) : ℚ)

theorem rescaledEdge_symm {n : ℕ} (g : ElementaryDecoratedGraph n) (i j : Fin n) :
    g.rescaledEdge i j = g.rescaledEdge j i := by
  rw [rescaledEdge, rescaledEdge, g.edge_symm]
  congr 1
  rw [Nat.mul_comm]

@[simp] theorem rescaledEdge_self {n : ℕ} (g : ElementaryDecoratedGraph n) (i : Fin n) :
    g.rescaledEdge i i = 0 := by
  simp [rescaledEdge, g.loopless]

/-- Pairwise arithmetic spectrum condition. -/
def HasPairSpectra {n : ℕ} (g : ElementaryDecoratedGraph n) : Prop :=
  ∀ i j, i ≠ j →
    InElementaryPairSpectrum (g.ramification i) (g.ramification j) (g.edge i j)

/-- Acute-isosceles condition: in every triangle, each rescaled weight is bounded by the maximum
of the other two.  Equivalently, the maximum occurs at least twice. -/
def HasAcuteIsoscelesRescaling {n : ℕ} (g : ElementaryDecoratedGraph n) : Prop :=
  ∀ i j k,
    g.rescaledEdge i j ≤ max (g.rescaledEdge i k) (g.rescaledEdge j k) ∧
    g.rescaledEdge i k ≤ max (g.rescaledEdge i j) (g.rescaledEdge j k) ∧
    g.rescaledEdge j k ≤ max (g.rescaledEdge i j) (g.rescaledEdge i k)

/-- Recognition certificate stated only in terms of graph entries. -/
def HasElementaryRecognitionCertificate {n : ℕ} (g : ElementaryDecoratedGraph n) : Prop :=
  g.HasPairSpectra ∧ g.HasAcuteIsoscelesRescaling

theorem rescaledEdge_nonneg {n : ℕ} (g : ElementaryDecoratedGraph n) (i j : Fin n) :
    0 ≤ g.rescaledEdge i j := by
  exact div_nonneg (by positivity) (by positivity)

/-- Canonical cluster partition at rescaled height `t`.  Acute isosceles is exactly what makes
threshold adjacency transitive, so these partitions are the dendrogram underlying the fission
encoding. -/
def thresholdSetoid {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (t : ℚ) (ht : 0 ≤ t) : Setoid (Fin n) where
  r i j := g.rescaledEdge i j ≤ t
  iseqv := {
    refl := fun i => by simpa using ht
    symm := fun {i j} hij => by simpa [g.rescaledEdge_symm i j] using hij
    trans := fun {i j k} hij hjk =>
      (hacute i j k).2.1.trans (max_le hij hjk) }

/-- Dendrogram partitions coarsen monotonically with threshold. -/
theorem thresholdSetoid_mono {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {s t : ℚ} (hs : 0 ≤ s) (hst : s ≤ t)
    {i j : Fin n} :
    (g.thresholdSetoid hacute s hs).r i j →
      (g.thresholdSetoid hacute t (hs.trans hst)).r i j :=
  fun hij => hij.trans hst

end ElementaryDecoratedGraph

/-- Exact finite cophenetic encoding of an elementary fission tree.

Pair presentations record which coefficient/contact mechanism realizes each edge.  The
acute-isosceles field is the cophenetic sibling compatibility condition. -/
structure ElementaryFissionEncoding {n : ℕ} (g : ElementaryDecoratedGraph n) where
  pairPresentation : ∀ i j, i ≠ j →
    ElementaryPairPresentation (g.ramification i) (g.ramification j) (g.edge i j)
  acuteIsosceles : g.HasAcuteIsoscelesRescaling

/-- **Exact elementary decorated-graph recognition.**  A finite labeled decorated graph has an
elementary fission encoding exactly when every pair lies in its exact spectrum and the rescaled
weights satisfy acute isosceles. -/
theorem nonempty_elementaryFissionEncoding_iff_certificate {n : ℕ}
    (g : ElementaryDecoratedGraph n) :
    Nonempty (ElementaryFissionEncoding g) ↔ g.HasElementaryRecognitionCertificate := by
  classical
  constructor
  · rintro ⟨encoding⟩
    refine ⟨?_, encoding.acuteIsosceles⟩
    intro i j hij
    exact (nonempty_elementaryPairPresentation_iff_spectrum _ _ _).mp
      ⟨encoding.pairPresentation i j hij⟩
  · rintro ⟨hpairs, hacute⟩
    refine ⟨{ pairPresentation := ?_, acuteIsosceles := hacute }⟩
    intro i j hij
    exact Classical.choice <|
      (nonempty_elementaryPairPresentation_iff_spectrum _ _ _).mpr (hpairs i j hij)

/-- Necessity: every elementary fission encoding satisfies both recognition tests. -/
theorem ElementaryFissionEncoding.hasCertificate {n : ℕ} {g : ElementaryDecoratedGraph n}
    (encoding : ElementaryFissionEncoding g) : g.HasElementaryRecognitionCertificate :=
  (nonempty_elementaryFissionEncoding_iff_certificate g).mp ⟨encoding⟩

/-- Sufficiency in constructive witness form. -/
noncomputable def ElementaryDecoratedGraph.fissionEncodingOfCertificate {n : ℕ}
    (g : ElementaryDecoratedGraph n) (h : g.HasElementaryRecognitionCertificate) :
    ElementaryFissionEncoding g :=
  Classical.choice ((nonempty_elementaryFissionEncoding_iff_certificate g).mpr h)

end IrregularStokes
end GaloisForLFunctions
