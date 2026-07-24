import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicGlobalCarrier
import GaloisForLFunctions.RHTower.SoninApertureAreaRigidity
import GaloisForLFunctions.HTGeometry.LpCoordinateProjection
import GaloisForLFunctions.HTGeometry.RankTwoFisherCutoffWard

/-!
# Global dyadic affine projection

The squarefree-times-square factorization is lifted from an equivalence of
indices to a unitary equivalence of the full complex `ell²` source spaces.
Under this unitary, every logarithmic Euler cutoff becomes exactly the affine
joint cutoff

`log d + 2 log m < T`.

The result is operator-level: conjugation carries the complete lower
off-diagonal corner, including both summands of the pointed Fisher
connection.  No diagonal or scalar quotient is taken.
-/

open Complex Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

open ContinuousLinearMap InnerProductSpace
open GaloisForLFunctions.HTGeometry

/-- Reindexing an `ell²` space by an equivalence is unitary. -/
noncomputable def lpReindexEquiv {ι κ : Type*} (e : ι ≃ κ) :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : κ => ℂ) 2 where
  toFun x :=
    ⟨fun k => x (e.symm k), by
      apply memℓp_gen
      have hx :
          Summable (fun i : ι => ‖x i‖ ^ (2 : ENNReal).toReal) :=
        (memℓp_gen_iff (by norm_num)).mp (lp.memℓp x)
      exact e.symm.summable_iff.mpr hx⟩
  invFun y :=
    ⟨fun i => y (e i), by
      apply memℓp_gen
      have hy :
          Summable (fun k : κ => ‖y k‖ ^ (2 : ENNReal).toReal) :=
        (memℓp_gen_iff (by norm_num)).mp (lp.memℓp y)
      exact e.summable_iff.mpr hy⟩
  left_inv x := by
    apply lp.ext
    funext i
    simp
  right_inv y := by
    apply lp.ext
    funext k
    simp
  map_add' x y := by
    apply lp.ext
    funext k
    rfl
  map_smul' c x := by
    apply lp.ext
    funext k
    rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num),
      lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun i : ι => ‖x i‖ ^ (2 : ENNReal).toReal)

@[simp] theorem lpReindexEquiv_apply
    {ι κ : Type*} (e : ι ≃ κ)
    (x : lp (fun _ : ι => ℂ) 2) (k : κ) :
    lpReindexEquiv e x k = x (e.symm k) :=
  rfl

@[simp] theorem lpReindexEquiv_symm_apply
    {ι κ : Type*} (e : ι ≃ κ)
    (y : lp (fun _ : κ => ℂ) 2) (i : ι) :
    (lpReindexEquiv e).symm y i = y (e i) :=
  rfl

/-- Source Hilbert space indexed by positive Euler integers. -/
abbrev EulerPositiveL2 := lp (fun _ : ℕ+ => ℂ) 2

/-- Source Hilbert space indexed jointly by squarefree part and square residual. -/
abbrev DyadicSquarefreeL2 :=
  lp (fun _ : SquarefreePNat × ℕ+ => ℂ) 2

/-- Full unitary implementing `n = m² d`. -/
noncomputable def dyadicSquarefreeSquareUnitary :
    EulerPositiveL2 ≃ₗᵢ[ℂ] DyadicSquarefreeL2 :=
  lpReindexEquiv dyadicSquarefreeSquareEquiv

/-- Sharp logarithmic Euler cutoff. -/
def eulerPositiveLogCutoffSet (T : ℝ) : Set ℕ+ :=
  {n | Real.log (n : ℝ) < T}

/-- Affine joint cutoff after the squarefree-times-square change of variables. -/
def dyadicSquarefreeAffineCutoffSet (T : ℝ) :
    Set (SquarefreePNat × ℕ+) :=
  {q |
    Real.log (q.1.1 : ℝ) + 2 * Real.log (q.2 : ℝ) < T}

/-- The global carrier sends the sharp Euler set exactly to the affine joint set. -/
theorem dyadicSquarefreeSquareEquiv_mem_affineCutoff
    (T : ℝ) (n : ℕ+) :
    dyadicSquarefreeSquareEquiv n ∈ dyadicSquarefreeAffineCutoffSet T ↔
      n ∈ eulerPositiveLogCutoffSet T := by
  exact (dyadicSquarefreeSquareEquiv_affineCutoff T n).symm

/-- Operator-level cutoff covariance.  This is equality of vectors in the
full infinite-dimensional Hilbert spaces, not equality of scalar readouts. -/
theorem dyadicSquarefreeSquareUnitary_cutoff
    (T : ℝ) (x : EulerPositiveL2) :
    dyadicSquarefreeSquareUnitary
        (lpCoordinateProjection (eulerPositiveLogCutoffSet T) x) =
      lpCoordinateProjection (dyadicSquarefreeAffineCutoffSet T)
        (dyadicSquarefreeSquareUnitary x) := by
  apply lp.ext
  funext q
  change
    (eulerPositiveLogCutoffSet T).indicator
        (fun n => x n) (dyadicSquarefreeSquareEquiv.symm q) =
      (dyadicSquarefreeAffineCutoffSet T).indicator
        (fun q' => x (dyadicSquarefreeSquareEquiv.symm q')) q
  by_cases hq : q ∈ dyadicSquarefreeAffineCutoffSet T
  · rw [indicator_of_mem hq]
    rw [indicator_of_mem]
    simpa using
      (dyadicSquarefreeSquareEquiv_mem_affineCutoff T
        (dyadicSquarefreeSquareEquiv.symm q)).mp
        (by simpa using hq)
  · rw [indicator_of_notMem hq]
    rw [indicator_of_notMem]
    intro hn
    apply hq
    have h :=
      (dyadicSquarefreeSquareEquiv_mem_affineCutoff T
        (dyadicSquarefreeSquareEquiv.symm q)).mpr hn
    simpa using h

/-- Conjugation of a bounded operator by an `ell²` reindexing unitary. -/
noncomputable def lpReindexConjugate
    {ι κ : Type*} (e : ι ≃ κ)
    (X : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
    lp (fun _ : κ => ℂ) 2 →L[ℂ] lp (fun _ : κ => ℂ) 2 :=
  (lpReindexEquiv e).toLinearIsometry.toContinuousLinearMap ∘L
    (X ∘L
      (lpReindexEquiv e).symm.toLinearIsometry.toContinuousLinearMap)

theorem lpReindexConjugate_eq_unitaryPush
    {ι κ : Type*} (e : ι ≃ κ)
    (X : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
    lpReindexConjugate e X = unitaryPush (lpReindexEquiv e) X := by
  rfl

@[simp] theorem lpReindexConjugate_apply
    {ι κ : Type*} (e : ι ≃ κ)
    (X : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)
    (y : lp (fun _ : κ => ℂ) 2) :
    lpReindexConjugate e X y =
      lpReindexEquiv e (X ((lpReindexEquiv e).symm y)) :=
  rfl

/-- Conjugation sends a coordinate projection to the reindexed coordinate
projection whenever membership is transported by the index equivalence. -/
theorem lpReindexConjugate_coordinateProjection
    {ι κ : Type*} (e : ι ≃ κ) (S : Set ι) (T : Set κ)
    (hST : ∀ i, e i ∈ T ↔ i ∈ S) :
    lpReindexConjugate e (lpCoordinateProjection S) =
      lpCoordinateProjection T := by
  apply ContinuousLinearMap.ext
  intro y
  apply lp.ext
  funext k
  change
    S.indicator (fun i => y (e i)) (e.symm k) =
      T.indicator (fun k' => y k') k
  by_cases hk : k ∈ T
  · have hi : e.symm k ∈ S :=
      (hST (e.symm k)).mp (by simpa using hk)
    simp [indicator_of_mem hk, indicator_of_mem hi]
  · have hi : e.symm k ∉ S := by
      intro hi
      exact hk (by simpa using (hST (e.symm k)).mpr hi)
    simp [indicator_of_notMem hk, indicator_of_notMem hi]

/-- The Euler cutoff projection is unitarily equal to the affine joint
projection. -/
theorem dyadicSquarefreeSquareUnitary_conjugate_cutoff
    (T : ℝ) :
    lpReindexConjugate dyadicSquarefreeSquareEquiv
        (lpCoordinateProjection (eulerPositiveLogCutoffSet T)) =
      lpCoordinateProjection (dyadicSquarefreeAffineCutoffSet T) := by
  exact lpReindexConjugate_coordinateProjection
    dyadicSquarefreeSquareEquiv _ _
    (dyadicSquarefreeSquareEquiv_mem_affineCutoff T)

/-- Unitary conjugation preserves the complete lower cutoff corner. -/
theorem lpReindexConjugate_cutoffLowerBoundary
    {ι κ : Type*} (e : ι ≃ κ)
    (P X : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
    lpReindexConjugate e (cutoffLowerBoundary P X) =
      cutoffLowerBoundary (lpReindexConjugate e P)
        (lpReindexConjugate e X) := by
  apply ContinuousLinearMap.ext
  intro y
  simp [lpReindexConjugate, cutoffLowerBoundary]

/-- Unitary reindexing preserves a rank-one operator, with both source and
target vectors transported. -/
theorem lpReindexConjugate_rankOne
    {ι κ : Type*} (e : ι ≃ κ)
    (x y : lp (fun _ : ι => ℂ) 2) :
    lpReindexConjugate e (rankOne ℂ x y) =
      rankOne ℂ (lpReindexEquiv e x) (lpReindexEquiv e y) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [lpReindexConjugate_apply, rankOne_apply, map_smul]
  congr 1
  have h :=
    LinearIsometryEquiv.inner_map_map (lpReindexEquiv e) y
      ((lpReindexEquiv e).symm z)
  simpa using h.symm

theorem lpReindexConjugate_add
    {ι κ : Type*} (e : ι ≃ κ)
    (X Y : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
    lpReindexConjugate e (X + Y) =
      lpReindexConjugate e X + lpReindexConjugate e Y := by
  apply ContinuousLinearMap.ext
  intro z
  simp [lpReindexConjugate]

theorem lpReindexConjugate_smul
    {ι κ : Type*} (e : ι ≃ κ) (c : ℂ)
    (X : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
    lpReindexConjugate e (c • X) =
      c • lpReindexConjugate e X := by
  apply ContinuousLinearMap.ext
  intro z
  simp [lpReindexConjugate]

/-- Reindexing preserves the Hilbert--Schmidt class. -/
theorem lpReindexConjugate_isHilbertSchmidt
    {ι κ : Type*} (e : ι ≃ κ)
    {X : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2}
    (hX : IsHilbertSchmidt X) :
    IsHilbertSchmidt (lpReindexConjugate e X) := by
  rw [lpReindexConjugate_eq_unitaryPush]
  exact unitaryPush_isHilbertSchmidt hX (lpReindexEquiv e)

/-- Reindexing preserves squared Hilbert--Schmidt energy exactly. -/
theorem hsNormSq_lpReindexConjugate
    {ι κ : Type*} (e : ι ≃ κ)
    {X : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2}
    (hX : IsHilbertSchmidt X) :
    hsNormSq (lpReindexConjugate e X) = hsNormSq X := by
  rw [lpReindexConjugate_eq_unitaryPush]
  exact hsNormSq_unitaryPush hX (lpReindexEquiv e)

/-- Unitary reindexing preserves the full two-summand pointed Fisher
connection. -/
theorem lpReindexConjugate_pointedFisherConnection
    {ι κ : Type*} (e : ι ≃ κ)
    (psi chi : lp (fun _ : ι => ℂ) 2) :
    lpReindexConjugate e (pointedFisherConnection psi chi) =
      pointedFisherConnection
        (lpReindexEquiv e psi) (lpReindexEquiv e chi) := by
  rw [pointedFisherConnection, pointedFisherConnection]
  rw [lpReindexConjugate_smul, lpReindexConjugate_add,
    lpReindexConjugate_rankOne, lpReindexConjugate_rankOne]

/-- **Global affine one-corner law.**  The full lower Euler boundary of the
pointed Fisher source is exactly the affine joint lower boundary after
`n = m² d`.  Both rank-one summands survive the transport. -/
theorem dyadicSquarefreeSquareUnitary_fisherLowerBoundary
    (T : ℝ) (psi chi : EulerPositiveL2) :
    lpReindexConjugate dyadicSquarefreeSquareEquiv
        (cutoffLowerBoundary
          (lpCoordinateProjection (eulerPositiveLogCutoffSet T))
          (pointedFisherConnection psi chi)) =
      cutoffLowerBoundary
        (lpCoordinateProjection (dyadicSquarefreeAffineCutoffSet T))
        (pointedFisherConnection
          (dyadicSquarefreeSquareUnitary psi)
          (dyadicSquarefreeSquareUnitary chi)) := by
  rw [lpReindexConjugate_cutoffLowerBoundary,
    dyadicSquarefreeSquareUnitary_conjugate_cutoff,
    lpReindexConjugate_pointedFisherConnection]
  rfl

/-- The global affine one-corner law preserves the complete
Hilbert--Schmidt source energy. -/
theorem hsNormSq_dyadicSquarefreeAffine_fisherLowerBoundary
    (T : ℝ) (psi chi : EulerPositiveL2) :
    hsNormSq
        (cutoffLowerBoundary
          (lpCoordinateProjection (dyadicSquarefreeAffineCutoffSet T))
          (pointedFisherConnection
            (dyadicSquarefreeSquareUnitary psi)
            (dyadicSquarefreeSquareUnitary chi))) =
      hsNormSq
        (cutoffLowerBoundary
          (lpCoordinateProjection (eulerPositiveLogCutoffSet T))
          (pointedFisherConnection psi chi)) := by
  let P :=
    lpCoordinateProjection (eulerPositiveLogCutoffSet T)
  let X := pointedFisherConnection psi chi
  have hX : IsHilbertSchmidt X :=
    pointedFisherConnection_isHilbertSchmidt psi chi
  have hL : IsHilbertSchmidt (cutoffLowerBoundary P X) := by
    exact (hX.comp_right P).comp_left (1 - P)
  rw [← dyadicSquarefreeSquareUnitary_fisherLowerBoundary]
  exact hsNormSq_lpReindexConjugate dyadicSquarefreeSquareEquiv hL

end RHTower
