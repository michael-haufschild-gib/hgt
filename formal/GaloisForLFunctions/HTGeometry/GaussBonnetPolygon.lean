import GaloisForLFunctions.HTGeometry.GaussBonnetRadialArc

/-!
# Gauss--Bonnet for a star-shaped polygon with corners

A **star polygon** about the pole of a geodesic polar chart is a closed curve made of finitely many
radial arcs `r = R_i(θ)`, `θ ∈ [t_i, t_{i+1}]`, with `t_0 = 0` and `t_n = 2π`, consecutive arcs
meeting at the nodes.  At each node the tangent direction jumps; the jump, measured against the
common outward radial direction, is the **exterior angle** of the polygon there.

Summing the arc identity of `GaussBonnetRadialArc`,

```text
∫_{t_i}^{t_{i+1}} ∫_0^{R_i} K dA + ∫_{t_i}^{t_{i+1}} κ_g ds
  = (t_{i+1} - t_i) - ( φ_i(t_{i+1}) - φ_i(t_i) ),
```

over `i` telescopes the angle differences against the exterior angles and gives the full local
Gauss--Bonnet theorem with corners:

```text
∫∫_D K dA + ∮_{∂D} κ_g ds + Σ_i ε_i = 2π = 2π · χ(disc).
```

This contains the smooth star-shaped case (`n = 1`, one closed arc, all exterior angles zero) and,
in particular, geodesic polygons containing the pole: for those the geodesic-curvature term
vanishes and the identity becomes the angle-excess formula

```text
∫∫_D K dA = Σ_i (π - ε_i) - (n - 2)π.
```
-/

open MeasureTheory intervalIntegral
open scoped Real ContDiff BigOperators

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- A closed star-shaped polygon about the pole of a geodesic polar chart: `n` radial arcs joined
at the nodes `t_0 = 0 < t_1 < ⋯ < t_n = 2π`. -/
structure StarPolygon (C : GeodesicPolarChart) where
  /-- The number of arcs. -/
  n : ℕ
  /-- There is at least one arc. -/
  npos : 0 < n
  /-- The nodes. -/
  node : ℕ → ℝ
  /-- The first node is the angle `0`. -/
  node_zero : node 0 = 0
  /-- The last node is the angle `2π`. -/
  node_last : node n = 2 * π
  /-- The nodes are increasing. -/
  node_mono : ∀ i, i < n → node i < node (i + 1)
  /-- The arcs. -/
  arc : ℕ → RadialArc C
  /-- Consecutive arcs meet at the interior nodes. -/
  meet : ∀ i, i + 1 < n → (arc i).R (node (i + 1)) = (arc (i + 1)).R (node (i + 1))
  /-- The last arc meets the first one, closing the curve up. -/
  meetClose : (arc (n - 1)).R (node n) = (arc 0).R (node 0)

namespace StarPolygon

variable {C : GeodesicPolarChart} (P : StarPolygon C)

/-- The tangent angle of the arc *ending* at the node `t_{i+1}`. -/
noncomputable def turnOut (i : ℕ) : ℝ := (P.arc i).turn (P.node (i + 1))

/-- The tangent angle of the arc *starting* at the node `t_i`. -/
noncomputable def turnIn (i : ℕ) : ℝ := (P.arc i).turn (P.node i)

/-- The **exterior angle** of the polygon at the node ending the `i`-th arc: the jump of the
tangent direction, measured against the outward radial direction. -/
noncomputable def exteriorAngle (i : ℕ) : ℝ :=
  P.turnOut i - (if i + 1 = P.n then P.turnIn 0 else P.turnIn (i + 1))

/-- `∫∫_D K dA` over the star-shaped polygonal region. -/
noncomputable def totalCurvature : ℝ :=
  ∑ i ∈ Finset.range P.n, (P.arc i).totalCurvatureOn (P.node i) (P.node (i + 1))

/-- `∮_{∂D} κ_g ds` along the polygonal boundary. -/
noncomputable def boundaryTurning : ℝ :=
  ∑ i ∈ Finset.range P.n, (P.arc i).boundaryTurningOn (P.node i) (P.node (i + 1))

/-- The sum of the exterior angles at the corners. -/
noncomputable def totalExteriorAngle : ℝ := ∑ i ∈ Finset.range P.n, P.exteriorAngle i

/-- The telescoping of the tangent angles against the exterior angles. -/
theorem totalExteriorAngle_eq :
    P.totalExteriorAngle
      = (∑ i ∈ Finset.range P.n, P.turnOut i) - ∑ i ∈ Finset.range P.n, P.turnIn i := by
  obtain ⟨m, hm⟩ : ∃ m, P.n = m + 1 := ⟨P.n - 1, by have := P.npos; omega⟩
  have hsplit : P.totalExteriorAngle
      = (∑ i ∈ Finset.range P.n, P.turnOut i)
        - ∑ i ∈ Finset.range P.n, (if i + 1 = P.n then P.turnIn 0 else P.turnIn (i + 1)) := by
    unfold totalExteriorAngle exteriorAngle
    rw [Finset.sum_sub_distrib]
  have hin : (∑ i ∈ Finset.range P.n, (if i + 1 = P.n then P.turnIn 0 else P.turnIn (i + 1)))
      = ∑ i ∈ Finset.range P.n, P.turnIn i := by
    rw [hm, Finset.sum_range_succ, Finset.sum_range_succ' (fun i => P.turnIn i) m]
    have hlast : (if m + 1 = m + 1 then P.turnIn 0 else P.turnIn (m + 1)) = P.turnIn 0 := by
      simp
    rw [hlast]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : i + 1 ≠ m + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [if_neg hne]
  rw [hsplit, hin]

/-- The telescoping of the node angles. -/
theorem sum_node_diff :
    (∑ i ∈ Finset.range P.n, (P.node (i + 1) - P.node i)) = 2 * π := by
  rw [Finset.sum_range_sub (fun i => P.node i) P.n, P.node_last, P.node_zero, sub_zero]

/-- **Gauss--Bonnet for a star-shaped polygon.**  On an arbitrary smooth Riemannian surface,

```text
∫∫_D K dA + ∮_{∂D} κ_g ds + Σ_i ε_i = 2π = 2π·χ(disc).
```
-/
theorem gauss_bonnet_polygon :
    P.totalCurvature + P.boundaryTurning + P.totalExteriorAngle = 2 * π := by
  have harc : ∀ i ∈ Finset.range P.n,
      (P.arc i).totalCurvatureOn (P.node i) (P.node (i + 1))
        + (P.arc i).boundaryTurningOn (P.node i) (P.node (i + 1))
        = (P.node (i + 1) - P.node i) - (P.turnOut i - P.turnIn i) := fun i _ =>
    (P.arc i).arc_identity (P.node i) (P.node (i + 1))
  have hsum : P.totalCurvature + P.boundaryTurning
      = (∑ i ∈ Finset.range P.n, (P.node (i + 1) - P.node i))
        - ((∑ i ∈ Finset.range P.n, P.turnOut i) - ∑ i ∈ Finset.range P.n, P.turnIn i) := by
    unfold totalCurvature boundaryTurning
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl harc]
    simp only [Finset.sum_sub_distrib]
  rw [hsum, P.sum_node_diff, P.totalExteriorAngle_eq]
  ring

/-- The **interior angle** of the polygon at the node ending the `i`-th arc. -/
noncomputable def interiorAngle (i : ℕ) : ℝ := π - P.exteriorAngle i

/-- **The angle-excess form of Gauss--Bonnet for a geodesic polygon.**  If every side of the star
polygon is a geodesic, the total curvature of the region is the angle excess

```text
∫∫_D K dA = Σ_i α_i - (n - 2)π.
```
-/
theorem gauss_bonnet_geodesic_polygon (hgeo : P.boundaryTurning = 0) :
    P.totalCurvature = (∑ i ∈ Finset.range P.n, P.interiorAngle i) - ((P.n : ℝ) - 2) * π := by
  have h := P.gauss_bonnet_polygon
  rw [hgeo, add_zero] at h
  have hint : (∑ i ∈ Finset.range P.n, P.interiorAngle i)
      = (P.n : ℝ) * π - P.totalExteriorAngle := by
    unfold interiorAngle totalExteriorAngle
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, mul_comm]
  rw [hint]
  linarith [h]

/-- A polygon all of whose sides are geodesics has no boundary turning. -/
theorem boundaryTurning_eq_zero (hgeo : ∀ i, ∀ θ, (P.arc i).kappaDs θ = 0) :
    P.boundaryTurning = 0 := by
  unfold boundaryTurning RadialArc.boundaryTurningOn
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ _ => hgeo i θ]
  simp

end StarPolygon

/-! ### The unit circle in the flat plane -/

/-- The unit circle, as a radial arc of the flat polar chart. -/
def unitArc : RadialArc flatPolarChart where
  R := fun _ => 1
  smooth := contDiff_const
  pos := fun _ => one_pos
  regular := fun _ _r hr => hr.1

/-- The unit disc of the Euclidean plane, as a one-arc star polygon. -/
noncomputable def unitDisc : StarPolygon flatPolarChart where
  n := 1
  npos := one_pos
  node := fun i => if i = 0 then 0 else 2 * π
  node_zero := by simp
  node_last := by simp
  node_mono := by
    intro i hi
    interval_cases i
    · simpa using by positivity
  arc := fun _ => unitArc
  meet := by omega
  meetClose := rfl

theorem unitArc_R1 (θ : ℝ) : unitArc.R1 θ = 0 := by
  simp [RadialArc.R1, unitArc]

theorem unitArc_turn (θ : ℝ) : unitArc.turn θ = 0 := by
  simp [RadialArc.turn, unitArc_R1]

/-- The unit disc has no corners. -/
theorem unitDisc_exteriorAngle_zero : unitDisc.totalExteriorAngle = 0 := by
  unfold StarPolygon.totalExteriorAngle StarPolygon.exteriorAngle StarPolygon.turnOut
    StarPolygon.turnIn
  simp [unitDisc, unitArc_turn]

/-- **Gauss--Bonnet for the Euclidean unit disc**, as an instance of the polygon theorem. -/
theorem unitDisc_gauss_bonnet :
    unitDisc.totalCurvature + unitDisc.boundaryTurning = 2 * π := by
  have h := unitDisc.gauss_bonnet_polygon
  rw [unitDisc_exteriorAngle_zero, add_zero] at h
  exact h

end GaloisForLFunctions.HTGeometry.GaussBonnet
