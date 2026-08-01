import GaloisForLFunctions.HTGeometry.BrouwerFixedPoint

/-!
# The Poincaré–Miranda theorem

A continuous vector field on the unit cube whose `j`-th component is non-positive on the face
`x j = 0` and non-negative on the opposite face `x j = 1` vanishes somewhere in the cube.  The proof
is Brouwer's fixed point theorem applied to the clamped displacement `x ↦ clamp (x - g x)`: at a
fixed point, each coordinate either lies strictly inside the interval — where the clamp is inactive
and the component must vanish — or sits on a face, where the sign hypothesis forces the same.

This is the coordinate form of the statement that the opposite faces of a cube form an essential
family: no continuous deformation can separate all of them simultaneously.
-/

open Metric Set

namespace GaloisForLFunctions

/-- The unit cube of `ℝ^r`. -/
def unitCube (r : ℕ) : Set (EuclideanSpace ℝ (Fin r)) := {x | ∀ j, x j ∈ Icc (0 : ℝ) 1}

theorem isCompact_unitCube (r : ℕ) : IsCompact (unitCube r) := by
  have himg : unitCube r = (WithLp.toLp 2) '' (Set.univ.pi fun _ : Fin r => Icc (0 : ℝ) 1) := by
    ext x
    constructor
    · intro hx
      exact ⟨WithLp.ofLp x, fun j _ => hx j, rfl⟩
    · rintro ⟨y, hy, rfl⟩ j
      exact hy j (Set.mem_univ j)
  rw [himg]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

/-- **The Poincaré–Miranda theorem.** -/
theorem poincare_miranda {r : ℕ} {g : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r)}
    (hg : ContinuousOn g (unitCube r))
    (hneg : ∀ x ∈ unitCube r, ∀ j, x j = 0 → g x j ≤ 0)
    (hpos : ∀ x ∈ unitCube r, ∀ j, x j = 1 → 0 ≤ g x j) :
    ∃ x ∈ unitCube r, ∀ j, g x j = 0 := by
  classical
  set P : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r) :=
    fun x => WithLp.toLp 2 (fun j => min 1 (max 0 (x j))) with hPdef
  have hPapply : ∀ (x : EuclideanSpace ℝ (Fin r)) (j : Fin r), P x j = min 1 (max 0 (x j)) :=
    fun x j => rfl
  have hPcont : Continuous P := by
    rw [hPdef]
    exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun j => continuous_const.min (continuous_const.max ((PiLp.continuous_apply 2 _ j))))
  have hPmem : ∀ x, P x ∈ unitCube r := by
    intro x j
    rw [hPapply]
    exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hPid : ∀ x ∈ unitCube r, P x = x := by
    intro x hx
    refine PiLp.ext fun j => ?_
    rw [hPapply, max_eq_right (hx j).1, min_eq_right (hx j).2]
  set T : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r) :=
    fun x => WithLp.toLp 2 (fun j => min 1 (max 0 (x j - g (P x) j))) with hTdef
  have hTapply : ∀ (x : EuclideanSpace ℝ (Fin r)) (j : Fin r),
      T x j = min 1 (max 0 (x j - g (P x) j)) := fun x j => rfl
  have hgP : Continuous fun x => g (P x) := hg.comp_continuous hPcont hPmem
  have hTcont : Continuous T := by
    rw [hTdef]
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact continuous_const.min (continuous_const.max
      (((PiLp.continuous_apply 2 _ j)).sub (((PiLp.continuous_apply 2 _ j)).comp hgP)))
  have hTmem : ∀ x, T x ∈ unitCube r := by
    intro x j
    rw [hTapply]
    exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  obtain ⟨x, hxcube, hxfix⟩ :=
    GaloisForLFunctions.exists_fixedPoint_of_retraction hPcont hPmem hPid
      (isCompact_unitCube r).isBounded hTcont (fun x _ => hTmem x)
  refine ⟨x, hxcube, fun j => ?_⟩
  have hPx : P x = x := hPid x hxcube
  have hcoord : min 1 (max 0 (x j - g x j)) = x j := by
    have h := congrArg (fun y : EuclideanSpace ℝ (Fin r) => y j) hxfix
    simp only [hTapply, hPx] at h
    exact h
  have h0 : (0:ℝ) ≤ x j := (hxcube j).1
  have h1 : x j ≤ 1 := (hxcube j).2
  have hle : g x j ≤ 0 := by
    by_contra hpos'
    push Not at hpos'
    have hxpos : 0 < x j := by
      rcases lt_or_eq_of_le h0 with h | h
      · exact h
      · exact absurd (hneg x hxcube j h.symm) (not_le.mpr hpos')
    have hM1 : max 0 (x j - g x j) < 1 := max_lt zero_lt_one (by linarith)
    have hMa : max 0 (x j - g x j) < x j := max_lt hxpos (by linarith)
    rw [min_eq_right hM1.le] at hcoord
    linarith [hcoord, hMa]
  have hge : 0 ≤ g x j := by
    by_contra hneg'
    push Not at hneg'
    have hxlt : x j < 1 := by
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact absurd (hpos x hxcube j h) (not_le.mpr hneg')
    have hmax : max 0 (x j - g x j) = x j - g x j := max_eq_right (by linarith)
    rw [hmax] at hcoord
    have hlt : x j - g x j < 1 := by
      by_contra hge'
      push Not at hge'
      rw [min_eq_left hge'] at hcoord
      linarith
    rw [min_eq_right hlt.le] at hcoord
    linarith
  linarith

end GaloisForLFunctions
