import Mathlib

/-!
# Cellular microlocal model of an exponential Stokes sheaf

For an ordered exponential difference of positive integral degree `k`, its boundary front has
`2k` walls.  The closed epigraph sheaf is represented on the induced one-dimensional cellular
stratification by a wall stalk and its two adjacent-arc generization maps.  A microlocal Morse
group is the cokernel of one such map.  This module computes those cokernels, proves that exactly
one oriented conormal occurs at every wall, and proves that exactly `k` of the `2k` conormals have
the directed decay orientation.  Fiber dimension is arbitrary.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes
namespace CellularMicrolocal

noncomputable section

/-- Rank-`d` coefficient fiber over the rational field. -/
abbrev Fiber (d : ℕ) := Fin d → ℚ

/-- Adjacent arc stalk as a subspace of the wall stalk.  An active closed arc has full stalk;
an inactive arc has zero stalk. -/
def arcStalk (d : ℕ) (active : Bool) : Submodule ℚ (Fiber d) :=
  if active then ⊤ else ⊥

/-- Cellular generization map from an adjacent arc stalk to the wall stalk. -/
def restriction (d : ℕ) (active : Bool) :
    arcStalk d active →ₗ[ℚ] Fiber d :=
  (arcStalk d active).subtype

/-- Microlocal Morse group: cokernel of the generization map in the chosen conormal direction. -/
abbrev microstalk (d : ℕ) (active : Bool) :=
  Fiber d ⧸ (restriction d active).range

/-- Active generization has zero cokernel; inactive generization has the full rank-`d` cokernel. -/
theorem finrank_microstalk (d : ℕ) (active : Bool) :
    Module.finrank ℚ (microstalk d active) = if active then 0 else d := by
  cases active with
  | false =>
      change Module.finrank ℚ (Fiber d ⧸ (restriction d false).range) = d
      have h := Submodule.finrank_quotient_add_finrank (restriction d false).range
      have hrange : Module.finrank ℚ (restriction d false).range = 0 := by
        change Module.finrank ℚ ↥((⊥ : Submodule ℚ (Fiber d)).subtype.range) = 0
        rw [Submodule.range_subtype]
        simp
      rw [hrange] at h
      simpa using h
  | true =>
      change Module.finrank ℚ (Fiber d ⧸ (restriction d true).range) = 0
      have h := Submodule.finrank_quotient_add_finrank (restriction d true).range
      have hrange : Module.finrank ℚ (restriction d true).range = d := by
        change Module.finrank ℚ ↥((⊤ : Submodule ℚ (Fiber d)).subtype.range) = d
        rw [Submodule.range_subtype]
        simp
      rw [hrange] at h
      simp only [Module.finrank_pi, Fintype.card_fin] at h
      omega

/-- Two conormal orientations at a point of an oriented boundary circle. -/
inductive ConormalSide
  | left
  | right
  deriving DecidableEq, Fintype

/-- The `2k` dominance walls, labelled as `k` antipodal pairs. -/
abbrev StokesWall (k : ℕ) := Fin k × Bool

/-- Whether the arc adjacent to one conormal side belongs to the closed exponential epigraph. -/
def adjacentActive {k : ℕ} (w : StokesWall k) : ConormalSide → Bool
  | .left => w.2
  | .right => !w.2

/-- Unique conormal side whose adjacent generization has nonzero cokernel. -/
def activeConormalSide {k : ℕ} (w : StokesWall k) : ConormalSide :=
  if w.2 then .right else .left

/-- Opposite conormal side, whose adjacent generization is an isomorphism onto the wall stalk. -/
def oppositeConormalSide {k : ℕ} (w : StokesWall k) : ConormalSide :=
  if w.2 then .left else .right

/-- Rank of the cellular microlocal Morse group at an oriented conormal. -/
noncomputable def microRank (d : ℕ) {k : ℕ}
    (w : StokesWall k) (s : ConormalSide) : ℕ :=
  Module.finrank ℚ (microstalk d (adjacentActive w s))

theorem microRank_eq (d : ℕ) {k : ℕ} (w : StokesWall k) (s : ConormalSide) :
    microRank d w s = if adjacentActive w s then 0 else d :=
  finrank_microstalk d (adjacentActive w s)

/-- Characteristic-cycle coefficient on the unique active conormal is the fiber rank. -/
theorem microRank_activeConormal (d : ℕ) {k : ℕ} (w : StokesWall k) :
    microRank d w (activeConormalSide w) = d := by
  rcases w with ⟨a, b⟩
  cases b <;> simp [microRank_eq, activeConormalSide, adjacentActive]

/-- Opposite conormal has zero Morse group. -/
theorem microRank_oppositeConormal (d : ℕ) {k : ℕ} (w : StokesWall k) :
    microRank d w (oppositeConormalSide w) = 0 := by
  rcases w with ⟨a, b⟩
  cases b <;> simp [microRank_eq, oppositeConormalSide, adjacentActive]

/-- Cellular definition of membership in singular support. -/
def IsInMicrosupport (d : ℕ) {k : ℕ}
    (w : StokesWall k) (s : ConormalSide) : Prop :=
  microRank d w s ≠ 0

/-- For positive-rank fibers, singular support has exactly one oriented conormal over every wall. -/
theorem isInMicrosupport_iff_active {d k : ℕ} (hd : 0 < d)
    (w : StokesWall k) (s : ConormalSide) :
    IsInMicrosupport d w s ↔ s = activeConormalSide w := by
  rcases w with ⟨a, b⟩
  cases b <;> cases s <;>
    simp [IsInMicrosupport, microRank_eq, activeConormalSide, adjacentActive,
      Nat.ne_of_gt hd]

/-- Exact dominance-wall count. -/
theorem stokesWall_card (k : ℕ) : Fintype.card (StokesWall k) = 2 * k := by
  simp [StokesWall]
  omega

/-- One of the two antipodal wall orientations is the ordered-root decay orientation. -/
def decayWall (k : ℕ) (a : Fin k) : StokesWall k := (a, false)

/-- Directed decay microstalks have total multiplicity `k d`. -/
theorem directedDecayMicroRank_sum (k d : ℕ) :
    (∑ a : Fin k, microRank d (decayWall k a)
      (activeConormalSide (decayWall k a))) = k * d := by
  simp [microRank_activeConormal]

/-- Full characteristic cycle has `2k` rays, each with coefficient `d`. -/
theorem fullCharacteristicMultiplicity_sum (k d : ℕ) :
    (∑ w : StokesWall k, microRank d w (activeConormalSide w)) = 2 * k * d := by
  simp [microRank_activeConormal, Nat.mul_comm, Nat.mul_left_comm]

end
end CellularMicrolocal
end IrregularStokes
end GaloisForLFunctions
