import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary

/-!
# Unilateral-shift defect of the algebraic Tate clock

The forward Ind clock and backward Pro clock already form the adjoint pair underlying the
hypertranscendental clock boundary.  This file adds their canonical partial inverses and evaluates
the failure of two-sided invertibility exactly: both failures are the one-dimensional boundary
projector at clock coordinate zero.

This is the algebraic value pattern of the Susskind--Glogower unilateral quantum phase operator.
K. Fujikawa, *Phase Operator for the Photon Field and an Index Theorem*, arXiv:hep-th/9411066,
identifies its unit index and rank-one anomalous boundary.  The formal results below use that
operator-theoretic pattern only as a source of exact relations; the Tate-clock maps remain static
Ind/Pro observability maps, not temporal evolution operators.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Backward shift on the finitely supported Ind clock. -/
def tateClockIndBackward {K : Type*} [Zero K]
    (a : ℕ →₀ K) : ℕ →₀ K :=
  Finsupp.comapDomain tateClockSucc a tateClockSucc.injective.injOn

@[simp] theorem tateClockIndBackward_apply
    {K : Type*} [Zero K] (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndBackward a n = a (n + 1) := by
  simp [tateClockIndBackward, tateClockSucc, Finsupp.comapDomain_apply]

/-- Backward observation is a left inverse of forward Ind extension. -/
theorem tateClockIndBackward_forward
    {K : Type*} [Zero K] (a : ℕ →₀ K) :
    tateClockIndBackward (tateClockIndForward a) = a := by
  ext n
  simp

/-- Rank-one boundary projector on the Ind clock. -/
def tateClockIndBoundaryProjector {K : Type*} [Zero K]
    (a : ℕ →₀ K) : ℕ →₀ K :=
  Finsupp.single 0 (a 0)

@[simp] theorem tateClockIndBoundaryProjector_apply_zero
    {K : Type*} [Zero K] (a : ℕ →₀ K) :
    tateClockIndBoundaryProjector a 0 = a 0 := by
  simp [tateClockIndBoundaryProjector]

@[simp] theorem tateClockIndBoundaryProjector_apply_succ
    {K : Type*} [Zero K] (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndBoundaryProjector a (n + 1) = 0 := by
  simp [tateClockIndBoundaryProjector]

/-- **Ind unilateral-shift defect.**  Forward after backward observation loses exactly the
boundary coordinate and no bulk observable. -/
theorem tateClockIndForward_backward_eq_sub_boundary
    {K : Type*} [AddCommGroup K] (a : ℕ →₀ K) :
    tateClockIndForward (tateClockIndBackward a) =
      a - tateClockIndBoundaryProjector a := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp

/-- Every finite clock covector splits canonically into its boundary reading and a shifted bulk
covector. -/
theorem tateClockInd_boundary_add_forward_backward
    {K : Type*} [AddCommGroup K] (a : ℕ →₀ K) :
    tateClockIndBoundaryProjector a +
        tateClockIndForward (tateClockIndBackward a) = a := by
  rw [tateClockIndForward_backward_eq_sub_boundary]
  abel

/-- Zero-extending forward shift on the linearly compact Pro clock. -/
def tateClockProForward {K : Type*} [Zero K] (p : ℕ → K) : ℕ → K
  | 0 => 0
  | n + 1 => p n

@[simp] theorem tateClockProForward_apply_zero
    {K : Type*} [Zero K] (p : ℕ → K) :
    tateClockProForward p 0 = 0 := rfl

@[simp] theorem tateClockProForward_apply_succ
    {K : Type*} [Zero K] (p : ℕ → K) (n : ℕ) :
    tateClockProForward p (n + 1) = p n := rfl

/-- Backward Pro observation is a right inverse of forward zero extension. -/
theorem tateClockProBackward_forward
    {K : Type*} [Zero K] (p : ℕ → K) :
    tateClockProBackward (tateClockProForward p) = p := by
  funext n
  rfl

/-- **Pro unilateral-shift defect.**  Forward after backward observation removes exactly the
one-dimensional Pro boundary already classified by `tateClockProBackward_eq_zero_iff_exists_boundary`. -/
theorem tateClockProForward_backward_eq_sub_boundary
    {K : Type*} [AddCommGroup K] (p : ℕ → K) :
    tateClockProForward (tateClockProBackward p) =
      p - tateClockProBoundary (p 0) := by
  funext n
  cases n with
  | zero => simp [tateClockProBoundary]
  | succ n => simp [tateClockProBackward, tateClockProBoundary]

/-- Every Pro clock state splits into its boundary line and a forward-shifted observable tail. -/
theorem tateClockPro_boundary_add_forward_backward
    {K : Type*} [AddCommGroup K] (p : ℕ → K) :
    tateClockProBoundary (p 0) +
        tateClockProForward (tateClockProBackward p) = p := by
  rw [tateClockProForward_backward_eq_sub_boundary]
  abel

/-- **Boundary-plus-bulk clock value relation.**  Every Ind/Pro observable pairing is the sum of
one boundary reading and the pairing of the two shifted tails.  This is the exact value-level
content of the unilateral-clock defect. -/
theorem tateClockPairing_boundary_add_shift
    {K : Type*} [CommRing K] (a : ℕ →₀ K) (p : ℕ → K) :
    tateClockPairing a p =
      a 0 * p 0 +
        tateClockPairing (tateClockIndBackward a) (tateClockProBackward p) := by
  nth_rewrite 1 [← tateClockInd_boundary_add_forward_backward a]
  calc
    tateClockPairing
        (tateClockIndBoundaryProjector a +
          tateClockIndForward (tateClockIndBackward a)) p =
        tateClockPairing (tateClockIndBoundaryProjector a) p +
          tateClockPairing (tateClockIndForward (tateClockIndBackward a)) p := by
            simp only [tateClockPairing]
            apply Finsupp.sum_add_index
            · intro n hn
              simp
            · intro n hn x y
              exact add_mul x y (p n)
    _ = a 0 * p 0 +
        tateClockPairing (tateClockIndBackward a) (tateClockProBackward p) := by
          rw [tateClockPairing_indForward]
          simp [tateClockPairing, tateClockIndBoundaryProjector]

end

end GaloisForLFunctions.HTGeometry
