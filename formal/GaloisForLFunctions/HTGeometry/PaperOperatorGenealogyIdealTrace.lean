import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace
import GaloisForLFunctions.HTGeometry.OperatorCertificateCofinal

/-!
# Compact-ideal trace of completed operator genealogies

Every nonzero finite-dimensional fibre supplies escaping unit coordinate vectors. The diagonal
identity in a completed genealogy survives on each such vector. Consequently its distance from
every compact perturbation is at least one, and its compact-ideal Gram trace is infinite.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- A fixed unit vector in the nonzero certificate fibre. -/
def paperGenealogyUnitFibre (d : ℕ) : Fib (d + 1) :=
  EuclideanSpace.single 0 1

/-- A unit history escaping to progressively later coordinates. -/
def paperGenealogyEscapeVector (d n : ℕ) : FibSeq (d + 1) :=
  lp.single 2 n (paperGenealogyUnitFibre d)

@[simp] theorem norm_paperGenealogyUnitFibre (d : ℕ) :
    ‖paperGenealogyUnitFibre d‖ = 1 := by
  change ‖PiLp.single (β := fun _ : Fin (d + 1) => ℂ) 2 (0 : Fin (d + 1)) (1 : ℂ)‖ = 1
  rw [PiLp.norm_single, norm_one]

@[simp] theorem norm_paperGenealogyEscapeVector (d n : ℕ) :
    ‖paperGenealogyEscapeVector d n‖ = 1 := by
  rw [paperGenealogyEscapeVector, lp.norm_single (by positivity), norm_paperGenealogyUnitFibre]

/-- The escaping history is weakly null independently of the certificate stream. -/
theorem paperGenealogyEscapeVector_weaklyNull (d : ℕ) (z : FibSeq (d + 1)) :
    Tendsto (fun n => ⟪z, paperGenealogyEscapeVector d n⟫_ℂ) atTop (𝓝 0) := by
  apply tendsto_inner_vecSeq_of_coord (C := 1) (paperGenealogyEscapeVector d)
    zero_le_one (fun n => (norm_paperGenealogyEscapeVector d n).le) _ z
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop k] with n hn
  simp [paperGenealogyEscapeVector, lp.single_apply, ne_of_lt hn]

/-- The genealogy retains the full unit vector at the last occupied coordinate. -/
theorem paperGenealogyEscapeVector_retained (d : ℕ) (a : OpCertStream (d + 1)) (n : ℕ) :
    (a.genealogy (paperGenealogyEscapeVector d n) : ℕ → Fib (d + 1)) n =
      paperGenealogyUnitFibre d := by
  simp [OpCertStream.genealogy_apply, paperGenealogyEscapeVector, lp.single_apply]

private theorem compact_perturbation_margin
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (K : compactOperatorStarAlgebra H) (x : ℕ → H)
    (hnorm : ∀ n, ‖x n‖ = 1)
    (hweak : ∀ z, Tendsto (fun n => ⟪z, x n⟫_ℂ) atTop (𝓝 0))
    (hlower : ∀ n, 1 ≤ ‖T (x n)‖) : 1 ≤ ‖T - K.1‖ := by
  have hK := tendsto_compactOperator_of_weaklyNull_hilbert K.1 K.2 x
    (fun n => (hnorm n).le) hweak
  have hb (n : ℕ) : 1 ≤ ‖T - K.1‖ + ‖K.1 (x n)‖ := by
    have hop := (T - K.1).le_opNorm (x n)
    rw [hnorm n, mul_one] at hop
    have heq : T (x n) = (T - K.1) (x n) + K.1 (x n) := by
      rw [_root_.sub_apply, sub_add_cancel]
    calc
      1 ≤ ‖T (x n)‖ := hlower n
      _ = ‖(T - K.1) (x n) + K.1 (x n)‖ := congrArg norm heq
      _ ≤ ‖(T - K.1) (x n)‖ + ‖K.1 (x n)‖ := norm_add_le _ _
      _ ≤ ‖T - K.1‖ + ‖K.1 (x n)‖ := add_le_add hop le_rfl
  have ht : Tendsto (fun n => ‖T - K.1‖ + ‖K.1 (x n)‖) atTop (𝓝 ‖T - K.1‖) := by
    simpa using tendsto_const_nhds.add hK.norm
  exact ge_of_tendsto ht (Eventually.of_forall hb)

/-- A universal quantitative compact-perturbation margin for every completed genealogy. -/
theorem one_le_norm_genealogy_sub_compact (d : ℕ) (a : OpCertStream (d + 1))
    (K : compactOperatorStarAlgebra (FibSeq (d + 1))) :
    1 ≤ ‖a.genealogy - K.1‖ := by
  apply compact_perturbation_margin a.genealogy K (paperGenealogyEscapeVector d)
    (norm_paperGenealogyEscapeVector d) (paperGenealogyEscapeVector_weaklyNull d)
  intro n
  have h := lp.norm_apply_le_norm (by positivity : (2 : ℝ≥0∞) ≠ 0)
    (a.genealogy (paperGenealogyEscapeVector d n)) n
  rw [paperGenealogyEscapeVector_retained, norm_paperGenealogyUnitFibre] at h
  exact h

/-- The completed genealogy on a nonzero fibre is never compact. -/
theorem not_isCompactOperator_genealogy (d : ℕ) (a : OpCertStream (d + 1)) :
    ¬ IsCompactOperator a.genealogy := by
  intro h
  have hb := one_le_norm_genealogy_sub_compact d a ⟨a.genealogy, h⟩
  have hfalse : (1 : ℝ) ≤ 0 := by simpa using hb
  exact (not_le_of_gt zero_lt_one) hfalse

/-- The compact-ideal Gram trace retains an infinite obstruction for every certificate stream. -/
theorem compactOperatorTraceCost_genealogy (d : ℕ) (a : OpCertStream (d + 1)) :
    compactOperatorTraceCost (FibSeq (d + 1)) a.genealogy = ∞ :=
  (compactOperatorTraceCost_eq_top_iff _).mpr (not_isCompactOperator_genealogy d a)

/-- Compact repairs cannot change the genealogy's infinite ideal-trace cost. -/
theorem compactOperatorTraceCost_genealogy_add_compact (d : ℕ) (a : OpCertStream (d + 1))
    (K : compactOperatorStarAlgebra (FibSeq (d + 1))) :
    compactOperatorTraceCost (FibSeq (d + 1)) (a.genealogy + K.1) = ∞ := by
  rw [compactOperatorTraceCost_add_compact, compactOperatorTraceCost_genealogy]

end

end GaloisForLFunctions.HTGeometry
