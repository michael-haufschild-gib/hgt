import GaloisForLFunctions.HTGeometry.ReflectionPositiveHankel

/-!
# Conservative Hankel rigidity

A Hankel kernel transports one unit of degree from either index to the other.  If its zeroth row
vanishes, repeated transport moves every entry into that row, so the whole kernel vanishes.  For a
Hilbert Gram this says that a nonzero conservative feature tower, whose constant feature is zero,
cannot be a moment-Hankel tower.

The second part records the local curvature causing this incompatibility for monomial edge
differences.  Every nontrivial positive edge has strictly negative curvature at adjacent orders.
-/

namespace HTGeometry

noncomputable section

/-- A two-index kernel is Hankel-balanced when one unit of degree can be transported between its
indices.  This is the intrinsic shift equation for dependence on the index sum. -/
def HankelShiftBalanced {α : Type*} (K : ℕ → ℕ → α) : Prop :=
  ∀ r s, K (r + 1) s = K r (s + 1)

/-- Repeated Hankel transport moves every entry to the zeroth row. -/
theorem hankelShiftBalanced_apply_eq_zeroRow
    {α : Type*} (K : ℕ → ℕ → α) (hbal : HankelShiftBalanced K) :
    ∀ r s, K r s = K 0 (r + s) := by
  intro r
  induction r with
  | zero => simp
  | succ r ihr =>
      intro s
      rw [hbal r s]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ihr (s + 1)

/-- **Conservative--Hankel rigidity.** A Hankel-balanced kernel with zero zeroth row is the zero
kernel.  No positivity, topology, or finite-dimensional assumption is needed. -/
theorem hankelShiftBalanced_eq_zero_of_zeroRow
    {α : Type*} [Zero α] (K : ℕ → ℕ → α)
    (hzero : ∀ s, K 0 s = 0) (hbal : HankelShiftBalanced K) :
    K = 0 := by
  funext r s
  rw [hankelShiftBalanced_apply_eq_zeroRow K hbal r s, hzero]
  rfl

/-- Hankel balance for the Gram kernel of a vector tower. -/
def GramHankelBalanced
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) : Prop :=
  HankelShiftBalanced (fun r s ↦ inner ℝ (v r) (v s))

/-- A conservative Hankel-balanced Gram has all inner products equal to zero. -/
theorem inner_eq_zero_of_gramHankelBalanced
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (hzero : v 0 = 0) (hbal : GramHankelBalanced v) :
    ∀ r s, inner ℝ (v r) (v s) = 0 := by
  have hrow : ∀ s, inner ℝ (v 0) (v s) = 0 := by
    intro s
    rw [hzero, inner_zero_left]
  have hkernel := hankelShiftBalanced_eq_zero_of_zeroRow
    (fun r s ↦ inner ℝ (v r) (v s)) hrow hbal
  intro r s
  have := congrFun (congrFun hkernel r) s
  simpa using this

/-- **Hilbert-space form of conservative--Hankel rigidity.** A vector tower with zero constant
feature has a Hankel-balanced Gram exactly when every feature vanishes. -/
theorem gramHankelBalanced_iff_all_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (hzero : v 0 = 0) :
    GramHankelBalanced v ↔ ∀ r, v r = 0 := by
  constructor
  · intro hbal r
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp
      (inner_eq_zero_of_gramHankelBalanced v hzero hbal r r)
  · intro hall r s
    change inner ℝ (v (r + 1)) (v s) = inner ℝ (v r) (v (s + 1))
    rw [hall, hall, hall, hall]

/-- Exact Hankel curvature of one monomial edge. -/
theorem monomialEdge_hankelCurvature_eq
    (a b : ℝ) (r s : ℕ) :
    (a ^ (r + 1) - b ^ (r + 1)) * (a ^ s - b ^ s) -
        (a ^ r - b ^ r) * (a ^ (s + 1) - b ^ (s + 1)) =
      (a - b) * (a ^ s * b ^ r - a ^ r * b ^ s) := by
  rw [pow_succ, pow_succ]
  ring

/-- At adjacent orders, monomial edge curvature is one negative square times a positive power. -/
theorem monomialEdge_adjacent_hankelCurvature_eq
    (a b : ℝ) (s : ℕ) :
    (a ^ (s + 2) - b ^ (s + 2)) * (a ^ s - b ^ s) -
        (a ^ (s + 1) - b ^ (s + 1)) ^ (2 : ℕ) =
      -(a - b) ^ (2 : ℕ) * (a * b) ^ s := by
  rw [show s + 2 = (s + 1) + 1 by omega, pow_succ, pow_succ, mul_pow]
  ring

/-- Every nontrivial edge between positive nodes has strictly negative adjacent Hankel
curvature, at every order. -/
theorem monomialEdge_adjacent_hankelCurvature_neg
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (s : ℕ) :
    (a ^ (s + 2) - b ^ (s + 2)) * (a ^ s - b ^ s) -
        (a ^ (s + 1) - b ^ (s + 1)) ^ (2 : ℕ) < 0 := by
  rw [monomialEdge_adjacent_hankelCurvature_eq]
  calc
    -(a - b) ^ (2 : ℕ) * (a * b) ^ s = -((a - b) ^ (2 : ℕ) * (a * b) ^ s) := by ring
    _ < 0 := neg_neg_of_pos (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hab))
      (pow_pos (mul_pos ha hb) s))

end

end HTGeometry
