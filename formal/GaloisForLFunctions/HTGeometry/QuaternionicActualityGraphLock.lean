import GaloisForLFunctions.HTGeometry.HiggsCausalOrbit

/-!
# Event-selected quaternionic graph locking

A pointed unit quaternion `q` removes the arbitrary choice of diagonal subgroup in the algebraic
`Spin(4)` pair action

`(u, v) • x = u * x * star v`.

For every unit left factor `u`, the unique unit right factor that fixes `q` is

`v = star q * u * q`.

Thus `q` selects a graph-conjugate diagonal subgroup.  This subgroup fixes the radial line through
`q` and preserves its orthogonal three-plane; on the latter, its action is quaternionic
conjugation on the imaginary orbit coefficient.

These are unconditional quaternion identities.  No identification with a physical event, Higgs
field, time, space, gravity, or gauge force is assumed.
-/

open scoped Quaternion RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The graph-conjugate partner of two unit quaternions is itself unit. -/
theorem quaternionGraphPartner_unit
    (u q : EventQuaternion)
    (hu : Quaternion.normSq u = 1)
    (hq : Quaternion.normSq q = 1) :
    Quaternion.normSq (star q * u * q) = 1 := by
  rw [map_mul, map_mul, Quaternion.normSq_star, hu, hq]
  simp

/-- A pointed unit quaternion selects the graph-conjugate diagonal pair fixing it. -/
theorem spinFourPairAction_graph_fixes
    (u q : EventQuaternion)
    (hu : Quaternion.normSq u = 1)
    (hq : Quaternion.normSq q = 1) :
    spinFourPairAction u (star q * u * q) q = q := by
  simp only [spinFourPairAction, star_mul, star_star]
  calc
    u * q * (star q * (star u * q)) =
        u * (q * star q) * star u * q := by noncomm_ring
    _ = q := by
      rw [Quaternion.self_mul_star, hq]
      norm_num
      rw [Quaternion.self_mul_star, hu]
      simp

/-- Among unit pairs, fixing a pointed unit quaternion is exactly the graph diagonal. -/
theorem spinFourPairAction_fixes_iff_graph
    (u v q : EventQuaternion)
    (hu : Quaternion.normSq u = 1)
    (hv : Quaternion.normSq v = 1)
    (hq : Quaternion.normSq q = 1) :
    spinFourPairAction u v q = q ↔ v = star q * u * q := by
  constructor
  · intro hfix
    have hright := congrArg (fun x : EventQuaternion => x * v) hfix
    have huv : u * q = q * v := by
      simpa [spinFourPairAction, mul_assoc, Quaternion.star_mul_self, hv] using hright
    calc
      v = (star q * q) * v := by rw [Quaternion.star_mul_self, hq]; simp
      _ = star q * (q * v) := by rw [mul_assoc]
      _ = star q * (u * q) := by rw [huv]
      _ = star q * u * q := by rw [mul_assoc]
  · rintro rfl
    exact spinFourPairAction_graph_fixes u q hu hq

/-- The selected graph pair acts on the pointed three-plane by diagonal conjugation. -/
theorem spinFourPairAction_graph_on_orbit
    (u q a : EventQuaternion)
    (hq : Quaternion.normSq q = 1) :
    spinFourPairAction u (star q * u * q) (a * q) =
      quaternionDiagonalAction u a * q := by
  simp only [spinFourPairAction, quaternionDiagonalAction, star_mul, star_star]
  calc
    u * (a * q) * (star q * (star u * q)) =
        u * a * (q * star q) * star u * q := by noncomm_ring
    _ = u * a * star u * q := by
      rw [Quaternion.self_mul_star, hq]
      simp

/-- The selected graph pair fixes the full radial line. -/
theorem spinFourPairAction_graph_fixes_radial
    (u q : EventQuaternion)
    (hu : Quaternion.normSq u = 1)
    (hq : Quaternion.normSq q = 1)
    (r : ℝ) :
    spinFourPairAction u (star q * u * q) (r • q) = r • q := by
  calc
    spinFourPairAction u (star q * u * q) (r • q) =
        r • spinFourPairAction u (star q * u * q) q := by
          simp [spinFourPairAction, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    _ = r • q := by rw [spinFourPairAction_graph_fixes u q hu hq]

/-- The selected graph pair preserves the pointed orthogonal three-plane. -/
theorem spinFourPairAction_graph_preserves_spatial
    (u q x : EventQuaternion)
    (hq : Quaternion.normSq q = 1)
    (hx : inner ℝ q x = 0) :
    inner ℝ q (spinFourPairAction u (star q * u * q) x) = 0 := by
  have hnorm : Quaternion.normSq q ≠ 0 := by rw [hq]; norm_num
  have hq0 : q ≠ 0 := Quaternion.normSq_ne_zero.mp hnorm
  obtain ⟨a, ha, hax⟩ :=
    pointedSpatial_exists_quaternionLeftOrbitDirection q x hq0 hx
  rw [← hax, spinFourPairAction_graph_on_orbit u q a hq]
  exact quaternionLeftOrbitDirection_orthogonal q (quaternionDiagonalAction u a)
    (quaternionDiagonalAction_preserves_imaginary u a ha)

/--
Exact graph-lock `1 + 3` law: a unit quaternion selects a unit graph partner, fixes its radial
line, and preserves its orthogonal three-plane.
-/
theorem quaternionActualityGraphLock_one_plus_three
    (u q : EventQuaternion)
    (hu : Quaternion.normSq u = 1)
    (hq : Quaternion.normSq q = 1) :
    Quaternion.normSq (star q * u * q) = 1 ∧
      (∀ r : ℝ, spinFourPairAction u (star q * u * q) (r • q) = r • q) ∧
      (∀ x : EventQuaternion, inner ℝ q x = 0 →
        inner ℝ q (spinFourPairAction u (star q * u * q) x) = 0) := by
  exact ⟨quaternionGraphPartner_unit u q hu hq,
    spinFourPairAction_graph_fixes_radial u q hu hq,
    fun x hx => spinFourPairAction_graph_preserves_spatial u q x hq hx⟩

end GaloisForLFunctions.HTGeometry
