import Mathlib

/-!
# Exact first-loss law for pointed transports

For a pointed obstruction family, a terminal zero has only two possible
origins: the obstruction was already zero at the source, or some transport
stage killed a nonzero class.  In a serial chain the killed locus splits
disjointly according to the first lossy edge.  In a parallel record it is
the common killed radical of all channels.

This is the zero-fibre form of the observation-kernel law.  It separates a
genuine source identity from an apparent solution created by information
loss and makes the location of that loss intrinsic.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Parameters at which a transport kills a nonzero pointed class. -/
def firstLossLocus
    {V W P : Type*} [Zero V] [Zero W]
    (T : V → W) (x : P → V) : Set P :=
  {p | x p ≠ 0 ∧ T (x p) = 0}

/-- The zero locus after a zero-preserving transport is source zero locus
plus the nonzero classes lost by transport. -/
theorem mappedZeroLocus_eq_union_firstLossLocus
    {V W P : Type*} [Zero V] [Zero W]
    (T : V → W) (x : P → V) (hzero : T 0 = 0) :
    {p | T (x p) = 0} = {p | x p = 0} ∪ firstLossLocus T x := by
  ext p
  constructor
  · intro hTx
    by_cases hx : x p = 0
    · exact Or.inl hx
    · exact Or.inr ⟨hx, hTx⟩
  · rintro (hx | ⟨_, hTx⟩)
    · change x p = 0 at hx
      change T (x p) = 0
      rw [hx, hzero]
    · exact hTx

/-- Parameters first killed by the second edge of a two-stage transport. -/
def secondKilledPointedLocus
    {V W U P : Type*} [Zero V] [Zero W] [Zero U]
    (T : V → W) (S : W → U) (x : P → V) : Set P :=
  {p | x p ≠ 0 ∧ T (x p) ≠ 0 ∧ S (T (x p)) = 0}

/-- The killed locus of a composite splits into loss at the first edge and
loss at the second edge after the class survived the first. -/
theorem killedPointedLocus_comp_eq_union_first_second
    {V W U P : Type*} [Zero V] [Zero W] [Zero U]
    (T : V → W) (S : W → U) (x : P → V)
    (hSzero : S 0 = 0) :
    firstLossLocus (S ∘ T) x =
      firstLossLocus T x ∪ secondKilledPointedLocus T S x := by
  ext p
  constructor
  · rintro ⟨hx, hST⟩
    by_cases hT : T (x p) = 0
    · exact Or.inl ⟨hx, hT⟩
    · exact Or.inr ⟨hx, hT, hST⟩
  · rintro (⟨hx, hT⟩ | ⟨hx, hT, hST⟩)
    · refine ⟨hx, ?_⟩
      change S (T (x p)) = 0
      rw [hT, hSzero]
    · exact ⟨hx, hST⟩

/-- Loss at the first and second edges is disjoint. -/
theorem disjoint_firstKilled_secondKilled
    {V W U P : Type*} [Zero V] [Zero W] [Zero U]
    (T : V → W) (S : W → U) (x : P → V) :
    Disjoint (firstLossLocus T x) (secondKilledPointedLocus T S x) := by
  rw [Set.disjoint_left]
  intro p hfirst hsecond
  exact hsecond.2.1 hfirst.2

/-- **Exact two-stage first-loss law.**  The terminal zero locus is the
disjoint union of source zeros, classes first killed by the first edge, and
classes first killed by the second edge. -/
theorem terminalZeroLocus_eq_source_union_first_union_second
    {V W U P : Type*} [Zero V] [Zero W] [Zero U]
    (T : V → W) (S : W → U) (x : P → V)
    (hTzero : T 0 = 0) (hSzero : S 0 = 0) :
    {p | S (T (x p)) = 0} =
      {p | x p = 0} ∪
        (firstLossLocus T x ∪ secondKilledPointedLocus T S x) := by
  change {p | (S ∘ T) (x p) = 0} = _
  rw [mappedZeroLocus_eq_union_firstLossLocus (S ∘ T) x]
  · rw [killedPointedLocus_comp_eq_union_first_second T S x hSzero]
  · change S (T 0) = 0
    rw [hTzero, hSzero]

/-- Pointed conservativity: a transport reflects zero on the delivered
obstruction family. -/
def ConservativeOnPointedRange
    {V W P : Type*} [Zero V] [Zero W]
    (T : V → W) (x : P → V) : Prop :=
  ∀ p, T (x p) = 0 → x p = 0

/-- A serial route whose two edges are conservative on the delivered
pointed ranges has exactly the source zero locus. -/
theorem terminalZero_iff_sourceZero_of_stagewiseConservative
    {V W U P : Type*} [Zero V] [Zero W] [Zero U]
    (T : V → W) (S : W → U) (x : P → V)
    (hTzero : T 0 = 0) (hSzero : S 0 = 0)
    (hT : ConservativeOnPointedRange T x)
    (hS : ConservativeOnPointedRange S (T ∘ x))
    (p : P) :
    S (T (x p)) = 0 ↔ x p = 0 := by
  constructor
  · intro h
    exact hT p (hS p h)
  · intro h
    rw [h, hTzero, hSzero]

/-! ## Arbitrary finite serial chains -/

/-- Composite of the first `n` stages of a homogeneous transport chain. -/
def iteratedPointedTransport
    {V : Type*} (T : ℕ → V → V) : ℕ → V → V
  | 0 => id
  | n + 1 => T n ∘ iteratedPointedTransport T n

@[simp]
theorem iteratedPointedTransport_zero
    {V : Type*} (T : ℕ → V → V) (v : V) :
    iteratedPointedTransport T 0 v = v := rfl

@[simp]
theorem iteratedPointedTransport_succ
    {V : Type*} (T : ℕ → V → V) (n : ℕ) (v : V) :
    iteratedPointedTransport T (n + 1) v =
      T n (iteratedPointedTransport T n v) := rfl

/-- Once a zero-preserving chain reaches zero, every later stage remains
zero. -/
theorem iteratedPointedTransport_eq_zero_of_le
    {V : Type*} [Zero V]
    (T : ℕ → V → V) (hzero : ∀ n, T n 0 = 0)
    {m n : ℕ} (hmn : m ≤ n) {v : V}
    (hm : iteratedPointedTransport T m v = 0) :
    iteratedPointedTransport T n v = 0 := by
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ n _ ih =>
      rw [iteratedPointedTransport_succ, ih, hzero]

/-- A class is first killed at stage `k` when it is nonzero immediately
before that edge and zero immediately after it. -/
def FirstKilledAt
    {V P : Type*} [Zero V]
    (T : ℕ → V → V) (x : P → V) (k : ℕ) (p : P) : Prop :=
  iteratedPointedTransport T k (x p) ≠ 0 ∧
    iteratedPointedTransport T (k + 1) (x p) = 0

/-- Every terminal zero which was nonzero at the source has a first killing
stage. -/
theorem exists_firstKilledAt_of_terminalZero_of_source_ne
    {V P : Type*} [Zero V]
    (T : ℕ → V → V) (x : P → V) (p : P) (n : ℕ)
    (hx : x p ≠ 0)
    (hterminal : iteratedPointedTransport T n (x p) = 0) :
    ∃ k, k < n ∧ FirstKilledAt T x k p := by
  induction n with
  | zero =>
      exact (hx hterminal).elim
  | succ n ih =>
      by_cases hmid : iteratedPointedTransport T n (x p) = 0
      · obtain ⟨k, hk, hkill⟩ := ih hmid
        exact ⟨k, hk.trans_le (Nat.le_succ n), hkill⟩
      · refine ⟨n, Nat.lt_succ_self n, hmid, ?_⟩
        simpa using hterminal

/-- Zero preservation makes the first killing stage unique. -/
theorem firstKilledAt_unique
    {V P : Type*} [Zero V]
    (T : ℕ → V → V) (hzero : ∀ n, T n 0 = 0)
    (x : P → V) (p : P) {k l : ℕ}
    (hk : FirstKilledAt T x k p) (hl : FirstKilledAt T x l p) :
    k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · exfalso
    exact hl.1 (iteratedPointedTransport_eq_zero_of_le T hzero
      (Nat.succ_le_of_lt hkl) hk.2)
  · exact hkl
  · exfalso
    exact hk.1 (iteratedPointedTransport_eq_zero_of_le T hzero
      (Nat.succ_le_of_lt hlk) hl.2)

/-- **Finite serial first-loss classification.**  A terminal zero is either
already a source zero or has one unique first killing edge. -/
theorem terminalZero_iff_sourceZero_or_existsUnique_firstKilledAt
    {V P : Type*} [Zero V]
    (T : ℕ → V → V) (hzero : ∀ n, T n 0 = 0)
    (x : P → V) (p : P) (n : ℕ) :
    iteratedPointedTransport T n (x p) = 0 ↔
      x p = 0 ∨ ∃! k, k < n ∧ FirstKilledAt T x k p := by
  constructor
  · intro hterminal
    by_cases hx : x p = 0
    · exact Or.inl hx
    · right
      obtain ⟨k, hklt, hkill⟩ :=
        exists_firstKilledAt_of_terminalZero_of_source_ne T x p n hx hterminal
      refine ⟨k, ⟨hklt, hkill⟩, ?_⟩
      intro l hl
      exact (firstKilledAt_unique T hzero x p hkill hl.2).symm
  · rintro (hx | ⟨k, hk, _⟩)
    · exact iteratedPointedTransport_eq_zero_of_le T hzero
        (Nat.zero_le n) (by simpa using hx)
    · exact iteratedPointedTransport_eq_zero_of_le T hzero
        (Nat.succ_le_iff.mpr hk.1) hk.2.2

/-- Heterogeneous parallel record of pointed transports. -/
def pointedParallelRecord
    {J V : Type*} {W : J → Type*}
    (T : ∀ j, V → W j) (v : V) : ∀ j, W j :=
  fun j => T j v

/-- Nonzero pointed classes killed by every channel of a heterogeneous
parallel record. -/
def commonKilledPointedLocus
    {J V P : Type*} {W : J → Type*}
    [Zero V] [∀ j, Zero (W j)]
    (T : ∀ j, V → W j) (x : P → V) : Set P :=
  {p | x p ≠ 0 ∧ ∀ j, T j (x p) = 0}

/-- The killed locus of a parallel record is exactly the common killed
radical of all channels. -/
theorem killedPointedLocus_parallelRecord_eq_common
    {J V P : Type*} {W : J → Type*}
    [Zero V] [∀ j, Zero (W j)]
    (T : ∀ j, V → W j) (x : P → V) :
    firstLossLocus (pointedParallelRecord T) x =
      commonKilledPointedLocus T x := by
  ext p
  constructor
  · rintro ⟨hx, hrecord⟩
    exact ⟨hx, fun j => congrFun hrecord j⟩
  · rintro ⟨hx, hall⟩
    exact ⟨hx, funext hall⟩

/-- **Exact parallel first-loss law.**  The zero locus of a heterogeneous
record is the disjoint union of source zeros and the common killed radical. -/
theorem parallelRecordZeroLocus_eq_source_union_commonKilled
    {J V P : Type*} {W : J → Type*}
    [Zero V] [∀ j, Zero (W j)]
    (T : ∀ j, V → W j) (x : P → V)
    (hzero : ∀ j, T j 0 = 0) :
    {p | pointedParallelRecord T (x p) = 0} =
      {p | x p = 0} ∪ commonKilledPointedLocus T x := by
  rw [mappedZeroLocus_eq_union_firstLossLocus
    (pointedParallelRecord T) x]
  · rw [killedPointedLocus_parallelRecord_eq_common T x]
  · funext j
    exact hzero j

/-! ## Principal defect gauges -/

/-- Fibrewise multiplication by a scalar gauge. -/
def pointwiseGauge
    {R P : Type*} [Mul R]
    (g x : P → R) : P → R :=
  fun p => g p * x p

/-- A nowhere-zero scalar gauge preserves the zero of every pointed
coefficient. -/
theorem pointwiseGauge_apply_eq_zero_iff
    {R P : Type*} [Field R]
    (g x : P → R) (hg : ∀ p, g p ≠ 0) (p : P) :
    pointwiseGauge g x p = 0 ↔ x p = 0 := by
  simp [pointwiseGauge, hg p]

/-- A nowhere-zero scalar gauge is an injective transport on the complete
coefficient field. -/
theorem pointwiseGauge_injective
    {R P : Type*} [Field R]
    (g : P → R) (hg : ∀ p, g p ≠ 0) :
    Function.Injective (pointwiseGauge g) := by
  intro x y hxy
  funext p
  have hp := congrFun hxy p
  exact (mul_left_cancel₀ (hg p)) hp

/-- Unit-gauge transport has no killed pointed locus. -/
theorem killedPointedLocus_pointwiseGauge_eq_empty
    {R P Q : Type*} [Field R]
    (g : P → R) (hg : ∀ p, g p ≠ 0) (x : Q → (P → R)) :
    firstLossLocus (pointwiseGauge g) x = ∅ := by
  ext q
  constructor
  · rintro ⟨hx, hkilled⟩
    apply hx
    apply pointwiseGauge_injective g hg
    have hzero : pointwiseGauge g (0 : P → R) = 0 := by
      funext p
      simp [pointwiseGauge]
    exact hkilled.trans hzero.symm
  · simp

/-- **Principal defect family law.**  An arbitrary nonempty family of
nowhere-zero gauges of one scalar defect has exactly the zero locus of that
defect.  Parallelizing such reporters adds no new selection condition. -/
theorem principalGaugeFamily_record_eq_zero_iff
    {R P J : Type*} [Field R] [Nonempty J]
    (g : J → P → R) (defect : P → R)
    (hg : ∀ j p, g j p ≠ 0) (p : P) :
    (fun j => g j p * defect p) = 0 ↔ defect p = 0 := by
  constructor
  · intro hrecord
    let j : J := Classical.choice inferInstance
    have hj := congrFun hrecord j
    exact (mul_eq_zero.mp hj).resolve_left (hg j p)
  · intro hdefect
    funext j
    simp [hdefect]

/-- A nonzero homogeneous response on a fixed carrier is a faithful
detector of its scalar coefficient, not an independent annihilator. -/
theorem principalPowerDetector_eq_zero_iff
    {R : Type*} [Field R]
    {n : ℕ} (hn : n ≠ 0) (base coefficient : R) (hbase : base ≠ 0) :
    coefficient ^ n * base = 0 ↔ coefficient = 0 := by
  constructor
  · intro h
    by_contra hcoefficient
    exact (mul_ne_zero (pow_ne_zero n hcoefficient) hbase) h
  · intro hcoefficient
    simp [hcoefficient, hn]

/-- **Cooriented positive-cone no-shorting law.**  Nonnegative mixing of
strictly positive gauges of one real defect cannot annihilate a nonzero
defect.  After coorientation the result has the strict sign of its square. -/
theorem principalCoorientedPositiveCone_noShorting
    {J : Type*}
    (a : ℝ) (ha : a ≠ 0) (S : Finset J)
    (g w : J → ℝ)
    (hg : ∀ j ∈ S, 0 < g j)
    (hw : ∀ j ∈ S, 0 ≤ w j)
    (hwpos : ∃ j ∈ S, 0 < w j) :
    0 < a * ∑ j ∈ S, w j * (a * g j) := by
  classical
  have hsum : 0 < ∑ j ∈ S, w j * g j := by
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg (hw j hj) (hg j hj).le
    · obtain ⟨j, hj, hwj⟩ := hwpos
      exact ⟨j, hj, mul_pos hwj (hg j hj)⟩
  calc
    a * ∑ j ∈ S, w j * (a * g j) =
        a ^ 2 * ∑ j ∈ S, w j * g j := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ > 0 := mul_pos (sq_pos_of_ne_zero ha) hsum

end

end GaloisForLFunctions.HTGeometry
