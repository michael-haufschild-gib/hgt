import GaloisForLFunctions.RHTower.WeilLogShiftMomentBarycentric
import GaloisForLFunctions.RHTower.WeilLogShiftGramCoordinateObstruction

/-! The geometric Weil cluster has a canonical, fully supported moment dual. -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

def finiteWeilClusterLogNodes (r k : ℕ) (i : Fin (r + 2)) : ℝ :=
  finiteWeilCenteredLog k (k + (i : ℕ))

theorem finiteWeilClusterLogNodes_apply (r k : ℕ) (i : Fin (r + 2)) :
    finiteWeilClusterLogNodes r k i =
      Real.log (((k + 2) + (i : ℕ) : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ) := by
  dsimp [finiteWeilClusterLogNodes, finiteWeilCenteredLog]
  rw [show k + (i : ℕ) + 2 = k + 2 + (i : ℕ) by omega]

theorem finiteWeilClusterLogNodes_injective (r k : ℕ) :
    Function.Injective (finiteWeilClusterLogNodes r k) := by
  intro i j hij
  rw [finiteWeilClusterLogNodes_apply, finiteWeilClusterLogNodes_apply] at hij
  have hlog : Real.log (((k + 2) + (i : ℕ) : ℕ) : ℝ) =
      Real.log (((k + 2) + (j : ℕ) : ℕ) : ℝ) := by linarith only [hij]
  have hreal := Real.log_injOn_pos
    (show 0 < (((k + 2) + (i : ℕ) : ℕ) : ℝ) by positivity)
    (show 0 < (((k + 2) + (j : ℕ) : ℕ) : ℝ) by positivity) hlog
  have hnat : k + 2 + (i : ℕ) = k + 2 + (j : ℕ) := by exact_mod_cast hreal
  apply Fin.ext
  omega

/-- Sup-norm normalized reciprocal products of logarithmic node differences. -/
def finiteWeilCanonicalCluster (r k : ℕ) : Fin (r + 2) → ℝ :=
  finiteWeilNormalizedMomentDual (finiteWeilClusterLogNodes r k)

/-- All normalized cluster moment annihilators are the two orientations of the
explicit canonical vector; every cluster coefficient is nonzero. -/
theorem finiteWeilCanonicalCluster_spec (r k : ℕ) :
    ‖finiteWeilCanonicalCluster r k‖ = 1 ∧
    (∀ i, finiteWeilCanonicalCluster r k i ≠ 0) ∧
    (∀ p ≤ r, ∑ i, finiteWeilCanonicalCluster r k i * finiteWeilClusterLogNodes r k i ^ p = 0) ∧
    (∀ c : Fin (r + 2) → ℝ, ‖c‖ = 1 →
      (∀ p ≤ r, ∑ i, c i * finiteWeilClusterLogNodes r k i ^ p = 0) →
      c = finiteWeilCanonicalCluster r k ∨ c = -finiteWeilCanonicalCluster r k) := by
  have hinj := finiteWeilClusterLogNodes_injective r k
  refine ⟨finiteWeilNormalizedMomentDual_norm _ hinj,
    finiteWeilNormalizedMomentDual_ne_zero _ hinj, ?_, ?_⟩
  · intro p hp
    exact finiteWeilNormalizedMomentDual_moment _ hinj p (by omega)
  · intro c hc hm
    exact finiteWeilNormalizedMomentDual_classification _ hinj c hc
      (fun p hp => hm p (by omega))

/-- The explicit Weil dual reads the top coefficient of the logarithmic interpolant. -/
theorem finiteWeilCanonicalCluster_pairing (r k : ℕ) (y : Fin (r + 2) → ℝ) :
    ∑ i, y i * finiteWeilCanonicalCluster r k i =
      (Lagrange.interpolate Finset.univ (finiteWeilClusterLogNodes r k) y).coeff (r + 1) /
        ‖finiteWeilMomentWeights (finiteWeilClusterLogNodes r k)‖ :=
  finiteWeilNormalizedMomentDual_pairing _ (finiteWeilClusterLogNodes_injective r k) y

/-- The previously existential geometric envelope holds for explicit canonical
coefficients, with the same constants and every cancellation order. -/
theorem exists_pairedLogKernel_canonical_cluster_envelope :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ r k : ℕ,
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) → ∀ y : ℝ,
        |∑ i, finiteWeilCanonicalCluster r k i * pairedLogKernel y ((k + 2) + (i : ℕ))| ≤
          B * Real.exp (2 * |y|) * (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r)⁻¹ := by
  obtain ⟨B, L, hB, hL, hbound⟩ :=
    exists_pairedLogKernel_geometric_cluster_envelope_with_moments
  refine ⟨B, L, hB, hL, fun r k hwidth y => ?_⟩
  obtain ⟨c, hc, hm, hb⟩ := hbound r (k + 2) hwidth
  have hm' : ∀ p ≤ r, ∑ i, c i * finiteWeilClusterLogNodes r k i ^ p = 0 := by
    intro p hp
    simpa only [finiteWeilClusterLogNodes_apply] using hm p hp
  rcases (finiteWeilCanonicalCluster_spec r k).2.2.2 c hc hm' with heq | heq
  · simpa only [heq] using hb y
  · simpa only [heq, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, abs_neg] using hb y

/-- Actual Gram tests obey the geometric sensitivity bound for the explicit
canonical dual, whose extension is nonzero on every cluster label. -/
theorem exists_finiteWeilGram_canonical_cluster_sensitivity :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) →
      let e : Fin (r + 2) → s := fun i => ⟨k + (i : ℕ), hmem i⟩
      let d : s → ℝ := Function.extend e (finiteWeilCanonicalCluster r k) (fun _ => 0)
      ‖d‖ = 1 ∧ (∀ i, d (e i) ≠ 0) ∧ ∀ w : FiniteWeilGramTest,
        |finiteWeilGramForm s w d| * (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) ≤
          B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_pairedLogKernel_canonical_cluster_envelope
  refine ⟨B, L, hB, hL, fun r s k hmem hwidth => ?_⟩
  let e : Fin (r + 2) → s := fun i => ⟨k + (i : ℕ), hmem i⟩
  have he : Function.Injective e := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    apply Fin.ext
    dsimp [e] at hv
    omega
  obtain ⟨i, hd, _, _, hcost⟩ := exists_finiteWeilGram_cluster_dual_of_coefficients
    r s k hmem (B := B) (q := (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r))
    (by positivity) (finiteWeilCanonicalCluster r k)
    (finiteWeilCanonicalCluster_spec r k).1 (hbound r k hwidth)
  refine ⟨hd, ?_, ?_⟩
  · intro j
    rw [he.extend_apply]
    exact (finiteWeilCanonicalCluster_spec r k).2.1 j
  · intro w
    exact (hcost w).trans_eq (by
      simpa only [mul_one] using finiteWeilGramTailCost_scale B 1 w)

end RHTower
