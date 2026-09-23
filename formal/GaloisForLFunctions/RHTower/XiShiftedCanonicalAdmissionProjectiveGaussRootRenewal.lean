import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveNextAdmissionRenewal
import GaloisForLFunctions.HTGeometry.FiniteGaussQuadrature
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Projective arithmetic work is exact Gauss-root spread

The retained account in the adaptive mixed/completed arithmetic source law has an intrinsic
polynomial interpretation.  Its lower Jacobi dispersion and accumulated Christoffel edges are
exactly the centered quadratic spread of the roots of the current monic admission polynomial.

Consequently the literal source-first adjacent-degree landing splits into the next admitted norm,
current Gauss-root spread, terminal trace mismatch, and the current Christoffel edge.  Effective
renewal can collapse only through actual root concentration together with collapse of the two
boundary accounts.
-/

open Matrix Polynomial
open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Newton's quadratic identity for a real multiset, in the exact form used by admission roots. -/
theorem multiset_sum_sq_sub_two_esymm_two (r : Multiset ℝ) :
    r.sum ^ (2 : ℕ) - 2 * r.esymm 2 = (r.map fun x => x ^ (2 : ℕ)).sum := by
  induction r using Multiset.induction_on with
  | empty => simp [Multiset.esymm]
  | @cons a r ih =>
      have hesymm : (a ::ₘ r).esymm 2 = a * r.sum + r.esymm 2 := by
        simp [Multiset.esymm, Multiset.powersetCard_cons,
          Multiset.powersetCard_one]
        rw [Multiset.sum_map_mul_left]
        have hid : (r.map fun x => x).sum = r.sum := by simp
        rw [hid]
        change r.esymm 2 + a * r.sum = a * r.sum + r.esymm 2
        ring
      rw [Multiset.sum_cons, hesymm, Multiset.map_cons, Multiset.sum_cons, ← ih]
      ring

/-- Quadratic spread of a multiset relative to an externally supplied cardinality. -/
def multisetQuadraticSpread (r : Multiset ℝ) (n : ℕ) : ℝ :=
  (r.map fun x => x ^ (2 : ℕ)).sum - r.sum ^ (2 : ℕ) / (n : ℝ)

/-- Quadratic spread is translation invariant and has weight two under dilation. -/
theorem multisetQuadraticSpread_map_affine
    (r : Multiset ℝ) (n : ℕ) (c d : ℝ)
    (hcard : r.card = n) (hn : 0 < n) :
    multisetQuadraticSpread (r.map fun x => c * x + d) n =
      c ^ (2 : ℕ) * multisetQuadraticSpread r n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsum : (r.map fun x => c * x + d).sum =
      c * r.sum + (n : ℝ) * d := by
    rw [Multiset.sum_map_add, Multiset.sum_map_mul_left]
    simp [hcard]
  have hsumsq : (r.map fun x => (c * x + d) ^ (2 : ℕ)).sum =
      c ^ (2 : ℕ) * (r.map fun x => x ^ (2 : ℕ)).sum +
        2 * c * d * r.sum + (n : ℝ) * d ^ (2 : ℕ) := by
    simp_rw [show ∀ x : ℝ, (c * x + d) ^ (2 : ℕ) =
        c ^ (2 : ℕ) * x ^ (2 : ℕ) + 2 * c * d * x + d ^ (2 : ℕ) by
      intro x
      ring]
    rw [Multiset.sum_map_add, Multiset.sum_map_add,
      Multiset.sum_map_mul_left, Multiset.sum_map_mul_left]
    simp [hcard]
  unfold multisetQuadraticSpread
  rw [hsum]
  simpa only [Multiset.map_map, Function.comp_apply] using (show
    (r.map fun x => (c * x + d) ^ (2 : ℕ)).sum -
        (c * r.sum + (n : ℝ) * d) ^ (2 : ℕ) / (n : ℝ) =
      c ^ (2 : ℕ) * ((r.map fun x => x ^ (2 : ℕ)).sum - r.sum ^ (2 : ℕ) / (n : ℝ)) by
    rw [hsumsq]
    field_simp [hn0]
    ring)

/-- The root trace of the current monic admission is the cumulative Jacobi diagonal. -/
theorem monicOrtho_roots_sum_eq_sum_alpha_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n < N) :
    (monicOrtho s n).roots.sum =
      ∑ j ∈ Finset.range n, monicOrthoAlpha s j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hsplit : (monicOrtho s (k + 1)).Splits := by
    simpa only using monicOrtho_splits_below h (n := k) hnN
  have hnext := hsplit.nextCoeff_eq_neg_sum_roots_of_monic
    (monicOrtho_monic s (k + 1))
  have hfirst := monicOrthoFirstCoeff_eq_neg_sum_below h (n := k + 1)
    (by omega : k + 1 ≤ N)
  have hcoeff : (monicOrtho s (k + 1)).nextCoeff =
      monicOrthoFirstCoeff s (k + 1) := by
    simp [Polynomial.nextCoeff, natDegree_monicOrtho_eq,
      monicOrthoFirstCoeff]
  rw [hcoeff, hfirst] at hnext
  linarith

/-- The second elementary root sum is the second subleading admission coefficient. -/
theorem monicOrtho_roots_esymm_two_eq_secondCoeff_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) :
    (monicOrtho s n).roots.esymm 2 = monicOrthoSecondCoeff s n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k = k + 2 by omega] at hnN ⊢
  have hsplit : (monicOrtho s (k + 2)).Splits := by
    have hnN' : k + 1 + 1 < N := by omega
    simpa only [show k + 2 = (k + 1) + 1 by omega] using
      monicOrtho_splits_below h (n := k + 1) hnN'
  have hv := Polynomial.coeff_eq_esymm_roots_of_splits
    (p := monicOrtho s (k + 2)) hsplit
    (k := k) (by rw [natDegree_monicOrtho_eq]; omega)
  rw [(monicOrtho_monic s (k + 2)).leadingCoeff, one_mul,
    natDegree_monicOrtho_eq] at hv
  norm_num at hv
  simpa only [monicOrthoSecondCoeff] using hv.symm

/-- Exact Frobenius/root-energy law for a finite positive monic admission. -/
theorem monicOrtho_roots_sum_sq_eq_jacobiEnergy_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) :
    ((monicOrtho s n).roots.map fun x => x ^ (2 : ℕ)).sum =
      (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
        2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) := by
  have hsum := monicOrtho_roots_sum_eq_sum_alpha_below h (by omega) hnN
  have hesymm := monicOrtho_roots_esymm_two_eq_secondCoeff_below h hn hnN
  have hjet := monicOrtho_coeffJet_energy_below h (n := n) (by omega : n ≤ N)
  have hfirst := monicOrthoFirstCoeff_eq_neg_sum_below h (n := n)
    (by omega : n ≤ N)
  rw [← multiset_sum_sq_sub_two_esymm_two, hsum, hesymm]
  rw [hfirst] at hjet
  simpa only [neg_sq] using hjet

end
end HTGeometry

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Centered quadratic spread of all roots of the current monic admission polynomial. -/
def projectiveGaussRootSpread (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  let roots := (HTGeometry.monicOrtho s n).roots
  HTGeometry.multisetQuadraticSpread roots n

/-- The current root spread in the affine hard-edge coordinate `z = 2 y X - 1`. -/
def projectiveHardEdgeGaussRootSpread (y : ℝ) (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  let roots := (HTGeometry.monicOrtho s n).roots
  HTGeometry.multisetQuadraticSpread (roots.map fun x => 2 * y * x - 1) n

/-- Root spread is exactly lower Jacobi diagonal dispersion plus all earlier Christoffel edges. -/
theorem projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) :
    projectiveGaussRootSpread s n =
      projectiveJacobiLowerAlphaDispersion s n +
        2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) := by
  rw [projectiveGaussRootSpread, HTGeometry.multisetQuadraticSpread]
  rw [HTGeometry.monicOrtho_roots_sum_eq_sum_alpha_below h (by omega) hnN,
    HTGeometry.monicOrtho_roots_sum_sq_eq_jacobiEnergy_below h hn hnN]
  unfold projectiveJacobiLowerAlphaDispersion
  ring

/-- Finite positivity makes current root spread strictly positive from degree two onward. -/
theorem projectiveGaussRootSpread_pos
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) :
    0 < projectiveGaussRootSpread s n := by
  rw [projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory h hn hnN]
  have hdisp : 0 ≤ projectiveJacobiLowerAlphaDispersion s n :=
    projectiveJacobiLowerAlphaDispersion_nonneg s (by omega)
  have hbetas : 0 < ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_pos'
    · intro j hj
      rcases j with _ | j
      · simp [HTGeometry.monicOrthoBeta]
      · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
          have hjn := Finset.mem_range.mp hj
          omega)).le
    · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
      exact HTGeometry.monicOrthoBeta_pos_below h (by omega) (by omega)
  exact add_pos_of_nonneg_of_pos hdisp (mul_pos (by norm_num) hbetas)

/-- Affine hard-edge transport multiplies root spread by exactly `4 y²`. -/
theorem projectiveHardEdgeGaussRootSpread_eq_four_mul_mass_sq_mul
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) (y : ℝ) :
    projectiveHardEdgeGaussRootSpread y s n =
      4 * y ^ (2 : ℕ) * projectiveGaussRootSpread s n := by
  have hsplit : (HTGeometry.monicOrtho s n).Splits := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (by omega : 0 < n))
    simpa only using HTGeometry.monicOrtho_splits_below h (n := k) hnN
  have hcard : (HTGeometry.monicOrtho s n).roots.card = n := by
    rw [← hsplit.natDegree_eq_card_roots]
    exact HTGeometry.natDegree_monicOrtho_eq s n
  dsimp only [projectiveHardEdgeGaussRootSpread, projectiveGaussRootSpread]
  change HTGeometry.multisetQuadraticSpread
      ((HTGeometry.monicOrtho s n).roots.map fun x => (2 * y) * x + (-1)) n = _
  rw [HTGeometry.multisetQuadraticSpread_map_affine _ n (2 * y) (-1) hcard (by omega)]
  ring

/-- **Exact retained-account classification.**  Retained arithmetic work consists of current
Gauss-root spread, terminal trace mismatch, and the current Christoffel edge, with no remainder. -/
theorem projectiveJacobiRetainedInventory_eq_rootSpread_add_mismatch_add_edge
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) :
    projectiveJacobiRetainedInventory s n =
      2 * (2 * n + 1 : ℝ) * projectiveGaussRootSpread s n +
        2 / (n : ℝ) * projectiveJacobiTerminalAlphaMismatch s n ^ (2 : ℕ) +
        2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
          HTGeometry.monicOrthoBeta s n := by
  rw [projectiveJacobiRetainedInventory,
    projectiveJacobiTraceVariance_eq_dispersion_add_mismatch s (by omega),
    projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory h hn hnN]
  ring

/-- Root spread is a controlled component of retained arithmetic inventory. -/
theorem rootSpread_part_le_projectiveJacobiRetainedInventory
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) :
    2 * (2 * n + 1 : ℝ) * projectiveGaussRootSpread s n ≤
      projectiveJacobiRetainedInventory s n := by
  rw [projectiveJacobiRetainedInventory_eq_rootSpread_add_mismatch_add_edge h hn hnN]
  have hmismatch : 0 ≤
      2 / (n : ℝ) * projectiveJacobiTerminalAlphaMismatch s n ^ (2 : ℕ) :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have hedge : 0 ≤
      2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s n :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (HTGeometry.monicOrthoBeta_pos_below h (by omega) hnN).le
  linarith

/-- **Complete projective-work classification.**  Newborn and current edges, current root spread,
and terminal trace mismatch exhaust the source-first surplus. -/
theorem xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_edges_add_rootSpread_add_mismatch
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n =
      2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
          HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) (n + 1) +
        2 * (2 * n + 1 : ℝ) *
          projectiveGaussRootSpread (xiShiftedRealMomentSequence w) n +
        2 / (n : ℝ) * projectiveJacobiTerminalAlphaMismatch
          (xiShiftedRealMomentSequence w) n ^ (2 : ℕ) +
        2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
          HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n := by
  rw [xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_nextEdge_add_retained
    hw (by omega) hH]
  rw [projectiveJacobiRetainedInventory_eq_rootSpread_add_mismatch_add_edge
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) hn (by omega)]
  ring

/-- Current-norm-scaled retained work has the same exact Gauss-root classification. -/
theorem xiShiftedCanonicalAdmissionRetainedProjectiveArithmeticWork_eq_rootSpread
    {w : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionRetainedProjectiveArithmeticWork w n =
      HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
        (2 * (2 * n + 1 : ℝ) *
            projectiveGaussRootSpread (xiShiftedRealMomentSequence w) n +
          2 / (n : ℝ) * projectiveJacobiTerminalAlphaMismatch
            (xiShiftedRealMomentSequence w) n ^ (2 : ℕ) +
          2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
            HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n) := by
  unfold xiShiftedCanonicalAdmissionRetainedProjectiveArithmeticWork
  rw [projectiveJacobiRetainedInventory_eq_rootSpread_add_mismatch_add_edge
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) hn (by omega)]

/-- **Literal source law with polynomial geometry exposed.**  Adaptive mixed amplitude and
completed arithmetic first form the producer.  Its projective work then funds the next norm and
retains exactly current Gauss-root spread, terminal mismatch, and current edge inventory. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_projectiveWork_eq_nextNorm_add_rootSpread
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    let s := xiShiftedRealMomentSequence w
    let alpha := HTGeometry.monicOrthoAlpha s n
    let F := xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n
    let h := HTGeometry.monicOrthoNormSq s n
    let source := xiShiftedAdaptiveMixedCompletedArithmeticSource w
      (HTGeometry.monicMomentAdmissionPolynomial s n)
    (2 * n + 1 : ℝ) *
        (source - h * (alpha * F + 2 * (n : ℝ) * alpha ^ (2 : ℕ))) - h * F ^ (2 : ℕ) =
      2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
          HTGeometry.monicOrthoNormSq s (n + 1) +
        h * (2 * (2 * n + 1 : ℝ) * projectiveGaussRootSpread s n +
          2 / (n : ℝ) * projectiveJacobiTerminalAlphaMismatch s n ^ (2 : ℕ) +
          2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
            HTGeometry.monicOrthoBeta s n) := by
  dsimp only
  rw [xiShiftedAdaptiveMixedCompletedArithmeticSource_projectiveWork_eq_nextNorm_add_retained
    hw (by omega) hH]
  rw [xiShiftedCanonicalAdmissionRetainedProjectiveArithmeticWork_eq_rootSpread hn hH]

end
end XiShiftedCanonicalAdmission
end RHTower
