import GaloisForLFunctions.HTGeometry.QKrawtchoukEdgeMoments
import GaloisForLFunctions.HTGeometry.ComplexSecondKind
import GaloisForLFunctions.HTGeometry.MomentIndeterminacyMaximalTotalVariationUniversalityLaw
import GaloisForLFunctions.HTGeometry.SecondKindGlobal

/-!
# Bounded kernels for the inverse-q Hermite edge

The inverse-q Hermite recurrence from arXiv:2609.24149 has a constant
diagonal. At that diagonal, both first- and second-kind polynomial
recurrences decouple into even and odd indices. Their combined squared
normalized values contract every two steps by at most `exp (-exp t)`.
This supplies the bounded-kernel input rather than assuming indeterminacy.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace HTGeometry

def inverseQHermiteCenter (u : ℝ) : ℝ := Real.exp (-u) - Real.exp u

private theorem edge_diag (t u : ℝ) (n : ℕ) :
    recurDiag (inverseQHermiteMoment t u) n = inverseQHermiteCenter u :=
  inverseQHermiteMoment_alpha t u (n + 1)

private theorem edge_off (t u : ℝ) (n : ℕ) :
    recurOff (inverseQHermiteMoment t u) n = inverseQHermiteLower t (n + 1) := by
  change monicOrthoBeta (inverseQHermiteMoment t u) (n + 1) = _
  simpa [inverseQHermiteLower] using inverseQHermiteMoment_beta t u n

private theorem edge_norm_succ (t u : ℝ) (n : ℕ) :
    monicOrthoNormSq (inverseQHermiteMoment t u) (n + 1) =
      monicOrthoNormSq (inverseQHermiteMoment t u) n *
        inverseQHermiteLower t (n + 1) := by
  rw [inverseQHermiteMoment_norm, inverseQHermiteMoment_norm, Finset.prod_range_succ]
  simp [inverseQHermiteLower]

private theorem edge_norm_pos (t u : ℝ) (n : ℕ) :
    0 < monicOrthoNormSq (inverseQHermiteMoment t u) n :=
  monicOrtho_inner_self_pos (inverseQHermiteMoment_positive t u) n

private def edgeKernelTerm (t u : ℝ) (n : ℕ) : ℝ :=
  (Complex.normSq (monicOrthoC (inverseQHermiteMoment t u) n (inverseQHermiteCenter u)) +
    Complex.normSq (secondKindC (inverseQHermiteMoment t u) n (inverseQHermiteCenter u))) /
      monicOrthoNormSq (inverseQHermiteMoment t u) n

private theorem edgeKernelTerm_nonneg (t u : ℝ) (n : ℕ) : 0 ≤ edgeKernelTerm t u n :=
  div_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (edge_norm_pos t u n).le

private theorem edgeKernelTerm_zero (t u : ℝ) : edgeKernelTerm t u 0 = 1 := by
  simp [edgeKernelTerm, monicOrthoC, inverseQHermiteMoment_norm]

private theorem edgeKernelTerm_one (t u : ℝ) :
    edgeKernelTerm t u 1 = 1 / inverseQHermiteLower t 1 := by
  simp [edgeKernelTerm, monicOrthoC, inverseQHermiteMoment_monicOrtho,
    inverseQHermiteCenter, inverseQHermiteMoment_norm, inverseQHermiteLower]

private theorem edgeKernelTerm_step (t u : ℝ) (n : ℕ) :
    edgeKernelTerm t u (n + 2) =
      (inverseQHermiteLower t (n + 1) / inverseQHermiteLower t (n + 2)) *
        edgeKernelTerm t u n := by
  have hQ := monicOrthoC_succ_succ (inverseQHermiteMoment_positive t u) n
    (inverseQHermiteCenter u)
  have hR := secondKindC_succ_succ (inverseQHermiteMoment t u) n
    (inverseQHermiteCenter u)
  rw [edge_diag, edge_off, sub_self, zero_mul, zero_sub] at hQ hR
  unfold edgeKernelTerm
  rw [hQ, hR, Complex.normSq_neg, Complex.normSq_neg,
    Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    edge_norm_succ t u (n + 1), edge_norm_succ]
  have hb := (inverseQHermiteLower_succ_pos t n).ne'
  have hc := (inverseQHermiteLower_succ_pos t (n + 1)).ne'
  have hh := (edge_norm_pos t u n).ne'
  field_simp

private def edgeDecay (t : ℝ) : ℝ := Real.exp (-Real.exp t / 2)

private theorem edgeDecay_pos (t : ℝ) : 0 < edgeDecay t := Real.exp_pos _

private theorem edgeDecay_lt_one (t : ℝ) : edgeDecay t < 1 :=
  Real.exp_lt_one_iff.mpr (by have := Real.exp_pos t; linarith)

private theorem edge_ratio_le (t : ℝ) (n : ℕ) :
    inverseQHermiteLower t (n + 1) / inverseQHermiteLower t (n + 2) ≤
      edgeDecay t ^ 2 := by
  have he : edgeDecay t ^ 2 = Real.exp (-Real.exp t) := by
    unfold edgeDecay
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hm : Real.exp (-Real.exp t) * Real.exp (Real.exp t * (n + 2)) =
      Real.exp (Real.exp t * (n + 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (div_le_iff₀ (inverseQHermiteLower_succ_pos t (n + 1))).mpr
  rw [he]
  simp only [inverseQHermiteLower, Nat.cast_add, Nat.cast_one]
  rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
  have hq : Real.exp (-Real.exp t) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos t))
  nlinarith

private def edgeBound (t : ℝ) : ℝ :=
  1 + 1 / (inverseQHermiteLower t 1 * edgeDecay t)

private theorem edgeBound_pos (t : ℝ) : 0 < edgeBound t := by
  have := inverseQHermiteLower_succ_pos t 0
  have := edgeDecay_pos t
  unfold edgeBound
  positivity

private theorem edgeKernelTerm_geometric (t u : ℝ) (n : ℕ) :
    edgeKernelTerm t u n ≤ edgeBound t * edgeDecay t ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [edgeKernelTerm_zero, pow_zero, mul_one]
      have := inverseQHermiteLower_succ_pos t 0
      have := edgeDecay_pos t
      unfold edgeBound
      apply le_add_of_nonneg_right
      positivity
  | one =>
      rw [edgeKernelTerm_one, pow_one]
      have hb := inverseQHermiteLower_succ_pos t 0
      have hr := edgeDecay_pos t
      unfold edgeBound
      field_simp
      nlinarith
  | more n hn _ =>
      rw [edgeKernelTerm_step]
      calc
        _ ≤ edgeDecay t ^ 2 * edgeKernelTerm t u n :=
          mul_le_mul_of_nonneg_right (edge_ratio_le t n) (edgeKernelTerm_nonneg t u n)
        _ ≤ edgeDecay t ^ 2 * (edgeBound t * edgeDecay t ^ n) :=
          mul_le_mul_of_nonneg_left hn (sq_nonneg _)
        _ = _ := by rw [pow_add]; ring

private theorem edgeKernelTerm_sum (t u : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, edgeKernelTerm t u j) ≤
      edgeBound t / (1 - edgeDecay t) := by
  have hgeom : (∑ j ∈ Finset.range N, edgeDecay t ^ j) ≤
      1 / (1 - edgeDecay t) := by
    apply (le_div_iff₀ (sub_pos.mpr (edgeDecay_lt_one t))).mpr
    have := geom_sum_mul (edgeDecay t) N
    nlinarith [pow_nonneg (edgeDecay_pos t).le N]
  calc
    _ ≤ ∑ j ∈ Finset.range N, edgeBound t * edgeDecay t ^ j :=
      Finset.sum_le_sum fun j _ => edgeKernelTerm_geometric t u j
    _ = edgeBound t * ∑ j ∈ Finset.range N, edgeDecay t ^ j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ edgeBound t * (1 / (1 - edgeDecay t)) :=
      mul_le_mul_of_nonneg_left hgeom (edgeBound_pos t).le
    _ = _ := by ring

/-- Both first- and second-kind kernels are bounded at the constant diagonal.
The geometric majorant is obtained directly from the paper's recurrence. -/
theorem inverseQHermiteMoment_boundedKernel_center (t u : ℝ) :
    BoundedKernel (inverseQHermiteMoment t u) (inverseQHermiteCenter u) := by
  let K := Real.sqrt (edgeBound t / (1 - edgeDecay t)) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, K, hK, hK, ?_, ?_⟩
  · intro N
    apply le_trans (Real.sqrt_le_sqrt ?_)
      (show Real.sqrt (edgeBound t / (1 - edgeDecay t)) ≤ K by dsimp [K]; linarith)
    apply le_trans (Finset.sum_le_sum ?_) (edgeKernelTerm_sum t u (N + 1))
    intro j _
    rw [Complex.sq_norm]
    change _ / monicOrthoNormSq (inverseQHermiteMoment t u) j ≤ _
    unfold edgeKernelTerm
    gcongr
    · exact (edge_norm_pos t u j).le
    · exact le_add_of_nonneg_right (Complex.normSq_nonneg _)
  · intro N
    apply le_trans (Real.sqrt_le_sqrt ?_)
      (show Real.sqrt (edgeBound t / (1 - edgeDecay t)) ≤ K by dsimp [K]; linarith)
    apply le_trans (Finset.sum_le_sum ?_) (edgeKernelTerm_sum t u (N + 1))
    intro j _
    rw [Complex.sq_norm]
    change _ / monicOrthoNormSq (inverseQHermiteMoment t u) j ≤ _
    unfold edgeKernelTerm
    gcongr
    · exact (edge_norm_pos t u j).le
    · exact le_add_of_nonneg_left (Complex.normSq_nonneg _)

/-- The edge moment sequence meets the corpus's indeterminacy criterion at
every complex point, with no boundedness premise left to discharge. -/
theorem inverseQHermiteMoment_boundedKernel (t u : ℝ) (z : ℂ) :
    BoundedKernel (inverseQHermiteMoment t u) z :=
  boundedKernel_global (inverseQHermiteMoment_positive t u)
    (inverseQHermiteMoment_boundedKernel_center t u) z

/-- The inverse-q Hermite edge has a continuum of pairwise singular
probability realizations, all with exactly the same complete moment sequence.
Every distinct pair is at maximal total-variation distance. -/
theorem inverseQHermiteMoment_maximalTV_family (t u : ℝ) :
    ∃ leaf : ℝ → ProbabilityMeasure ℝ,
      (∀ r : ℝ, GaloisForLFunctions.HTGeometry.HasHamburgerMoments
        (inverseQHermiteMoment t u) (leaf r : Measure ℝ)) ∧
      ∀ r v : ℝ, r ≠ v →
        (leaf r : Measure ℝ) ⟂ₘ (leaf v : Measure ℝ) ∧
        (((leaf r : Measure ℝ).toSignedMeasure -
          (leaf v : Measure ℝ).toSignedMeasure).totalVariation Set.univ = 2) :=
  exists_momentIdentical_pairwiseMaximalTotalVariation_family
    (inverseQHermiteMoment_positive t u) (inverseQHermiteMoment_boundedKernel t u 0)
    (inverseQHermiteMoment_zero t u)

/-- In particular the inverse-q Hermite edge supports the fully constructed
classical Nevanlinna family, not merely a formal Jacobi matrix. -/
def inverseQHermiteNevanlinnaFamily (t u : ℝ) :
    GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaExtremalFamily
      (inverseQHermiteMoment t u) :=
  nevExtremalFamily (inverseQHermiteMoment_positive t u)
    (inverseQHermiteMoment_boundedKernel t u 0) (inverseQHermiteMoment_zero t u)

/-- At every observation point the maximal possible atom bound is positive. -/
theorem inverseQHermiteMoment_christoffel_pos (t u x : ℝ) :
    0 < christoffelLimit (inverseQHermiteMoment t u) x :=
  christoffelLimit_pos_of_boundedKernel (inverseQHermiteMoment_positive t u) x
    (inverseQHermiteMoment_boundedKernel t u x)

end HTGeometry
