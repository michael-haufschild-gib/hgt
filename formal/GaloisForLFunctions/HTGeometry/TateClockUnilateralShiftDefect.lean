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

open scoped BigOperators

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

/-- The `m`-fold forward extension on the finitely supported Ind clock. -/
def tateClockIndForwardN {K : Type*} [Zero K] :
    ℕ → (ℕ →₀ K) → (ℕ →₀ K)
  | 0, a => a
  | m + 1, a => tateClockIndForward (tateClockIndForwardN m a)

/-- The `m`-fold backward observation on the finitely supported Ind clock. -/
def tateClockIndBackwardN {K : Type*} [Zero K] :
    ℕ → (ℕ →₀ K) → (ℕ →₀ K)
  | 0, a => a
  | m + 1, a => tateClockIndBackwardN m (tateClockIndBackward a)

/-- The `m`-fold backward observation on the Pro clock. -/
def tateClockProBackwardN {K : Type*} :
    ℕ → (ℕ → K) → (ℕ → K)
  | 0, p => p
  | m + 1, p => tateClockProBackwardN m (tateClockProBackward p)

@[simp] theorem tateClockIndBackwardN_apply
    {K : Type*} [Zero K] (m : ℕ) (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndBackwardN m a n = a (n + m) := by
  induction m generalizing a n with
  | zero => simp [tateClockIndBackwardN]
  | succ m ih =>
      rw [tateClockIndBackwardN, ih, tateClockIndBackward_apply]
      congr 1

@[simp] theorem tateClockProBackwardN_apply
    {K : Type*} (m : ℕ) (p : ℕ → K) (n : ℕ) :
    tateClockProBackwardN m p n = p (n + m) := by
  induction m generalizing p n with
  | zero => simp [tateClockProBackwardN]
  | succ m ih =>
      rw [tateClockProBackwardN, ih]
      rfl

theorem tateClockIndForwardN_apply
    {K : Type*} [Zero K] (m : ℕ) (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndForwardN m a n = if m ≤ n then a (n - m) else 0 := by
  induction m generalizing n with
  | zero => simp [tateClockIndForwardN]
  | succ m ih =>
      cases n with
      | zero => simp [tateClockIndForwardN]
      | succ n =>
          rw [tateClockIndForwardN, tateClockIndForward_apply_succ, ih]
          simp only [Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub]

/-- Backward observation remains a left inverse after any finite number of forward extensions. -/
theorem tateClockIndBackwardN_forwardN
    {K : Type*} [Zero K] (m : ℕ) (a : ℕ →₀ K) :
    tateClockIndBackwardN m (tateClockIndForwardN m a) = a := by
  ext n
  rw [tateClockIndBackwardN_apply, tateClockIndForwardN_apply]
  have hm : m ≤ n + m := by omega
  simp [hm]

/-- The oriented boundary interval cut out by an `m`-fold unilateral shift. It retains every
sector from charge `0` through charge `m - 1`, rather than only one endpoint. -/
def tateClockIndBoundaryInterval {K : Type*} [AddCommMonoid K]
    (m : ℕ) (a : ℕ →₀ K) : ℕ →₀ K :=
  ∑ k ∈ Finset.range m, Finsupp.single k (a k)

@[simp] theorem tateClockIndBoundaryInterval_apply
    {K : Type*} [AddCommMonoid K] (m : ℕ) (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndBoundaryInterval m a n = if n < m then a n else 0 := by
  classical
  unfold tateClockIndBoundaryInterval
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  by_cases hn : n < m
  · simp [hn]
  · simp [hn]

/-- **Finite unilateral interval decomposition.** Every Ind state is exactly its first `m`
boundary sectors plus the tail recovered after `m` backward and forward shifts. -/
theorem tateClockInd_boundaryInterval_add_forwardN_backwardN
    {K : Type*} [AddCommGroup K] (m : ℕ) (a : ℕ →₀ K) :
    tateClockIndBoundaryInterval m a +
        tateClockIndForwardN m (tateClockIndBackwardN m a) = a := by
  ext n
  simp only [Finsupp.add_apply]
  rw [tateClockIndBoundaryInterval_apply, tateClockIndForwardN_apply]
  by_cases hn : n < m
  · simp [hn, Nat.not_le_of_lt hn]
  · have hmn : m ≤ n := Nat.le_of_not_gt hn
    rw [if_neg hn, if_pos hmn, tateClockIndBackwardN_apply]
    simp only [zero_add]
    rw [Nat.sub_add_cancel hmn]

/-- **Oriented interval cocycle.** The boundary interval of a composite shift is the first
interval followed by the translated second interval. This retains the order of the crossings. -/
theorem tateClockIndBoundaryInterval_add
    {K : Type*} [AddCommMonoid K] (m n : ℕ) (a : ℕ →₀ K) :
    tateClockIndBoundaryInterval (m + n) a =
      tateClockIndBoundaryInterval m a +
        tateClockIndForwardN m
          (tateClockIndBoundaryInterval n (tateClockIndBackwardN m a)) := by
  ext i
  simp only [Finsupp.add_apply]
  rw [tateClockIndBoundaryInterval_apply, tateClockIndBoundaryInterval_apply,
    tateClockIndForwardN_apply]
  by_cases hi : i < m
  · have himn : i < m + n := by omega
    simp [hi, himn, Nat.not_le_of_lt hi]
  · have hmi : m ≤ i := Nat.le_of_not_gt hi
    rw [if_neg hi, if_pos hmi, tateClockIndBoundaryInterval_apply,
      tateClockIndBackwardN_apply]
    have hsub : i - m + m = i := Nat.sub_add_cancel hmi
    by_cases himn : i < m + n
    · have hin : i - m < n := by omega
      rw [if_pos himn, if_pos hin, hsub]
      simp
    · have hin : ¬i - m < n := by omega
      simp [himn, hin]

/-- **Finite boundary-plus-bulk pairing law.** The defect of `m` unilateral shifts is the whole
oriented interval of the first `m` pairings. -/
theorem tateClockPairing_boundaryInterval_add_shift
    {K : Type*} [CommRing K] (m : ℕ) (a : ℕ →₀ K) (p : ℕ → K) :
    tateClockPairing a p =
      (∑ k ∈ Finset.range m, a k * p k) +
        tateClockPairing (tateClockIndBackwardN m a) (tateClockProBackwardN m p) := by
  induction m generalizing a p with
  | zero => simp [tateClockIndBackwardN, tateClockProBackwardN]
  | succ m ih =>
      calc
        tateClockPairing a p =
            a 0 * p 0 + tateClockPairing
              (tateClockIndBackward a) (tateClockProBackward p) :=
          tateClockPairing_boundary_add_shift a p
        _ = a 0 * p 0 +
            ((∑ k ∈ Finset.range m,
                tateClockIndBackward a k * tateClockProBackward p k) +
              tateClockPairing
                (tateClockIndBackwardN m (tateClockIndBackward a))
                (tateClockProBackwardN m (tateClockProBackward p))) := by rw [ih]
        _ = (∑ k ∈ Finset.range (m + 1), a k * p k) +
              tateClockPairing
                (tateClockIndBackwardN (m + 1) a)
                (tateClockProBackwardN (m + 1) p) := by
          rw [Finset.sum_range_succ']
          simp only [tateClockIndBackward_apply, tateClockProBackward,
            tateClockIndBackwardN, tateClockProBackwardN]
          abel

end

end GaloisForLFunctions.HTGeometry
