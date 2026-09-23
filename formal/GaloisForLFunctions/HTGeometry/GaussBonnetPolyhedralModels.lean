import GaloisForLFunctions.HTGeometry.GaussBonnetPolyhedral

/-!
# Euclidean realizations of closed triangulated surfaces, and the tetrahedron

Two things are established here.

First, the Euclidean angle structure of a closed triangulated surface is never a vacuous
hypothesis: whenever every face is realized by three points of a Euclidean affine space, the
resulting corner angles automatically sum to `π`, by the classical angle-sum theorem for triangles.
This is `ClosedTriangulation.ofRealization`.

Second, the regular tetrahedron is written out completely: four vertices, four faces, six edges,
each face realized by a unit equilateral triangle in the plane `ℂ`.  Its Euler characteristic is
computed to be `2`, and the Gauss--Bonnet theorem of `GaussBonnetPolyhedral` gives its total
angular defect `4π`, the classical value for a sphere.
-/

open scoped Real
open Finset

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

namespace ClosedTriangulation

variable {V F : Type*} [DecidableEq V] [Fintype V] [Fintype F]

/-- **Euclidean realization.**  A closed triangulated surface each of whose faces is realized by
three points of a Euclidean affine space carries a Euclidean angle structure: the three corner
angles of every face sum to `π`. -/
noncomputable def ofRealization {W P : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MetricSpace P] [NormedAddTorsor W P]
    (corner : F → Fin 3 → V) (pt : F → Fin 3 → P) (hne : ∀ f, pt f 1 ≠ pt f 0)
    (hedge : ∀ e ∈ edgeSet corner,
      #{s ∈ (Finset.univ : Finset (F × Fin 3)) | sideEdge corner s = e} = 2) :
    ClosedTriangulation V F where
  corner := corner
  angle := fun f => ![EuclideanGeometry.angle (pt f 2) (pt f 0) (pt f 1),
                      EuclideanGeometry.angle (pt f 0) (pt f 1) (pt f 2),
                      EuclideanGeometry.angle (pt f 1) (pt f 2) (pt f 0)]
  angleSum := fun f => by
    have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := pt f 0) (p₂ := pt f 1) (pt f 2) (hne f)
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    linarith
  edgeIncidence := hedge

end ClosedTriangulation

/-! ### The regular tetrahedron -/

/-- The four triangles of the tetrahedron, indexed by the vertex they omit. -/
def tetraCorner : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

/-- The three vertices of a unit equilateral triangle in the plane. -/
noncomputable def equilateralPoint : Fin 3 → ℂ :=
  ![0, 1, ⟨1 / 2, Real.sqrt 3 / 2⟩]

theorem equilateralPoint_dist_01 : dist (equilateralPoint 0) (equilateralPoint 1) = 1 := by
  simp [equilateralPoint, Complex.dist_eq]

theorem equilateralPoint_dist_12 : dist (equilateralPoint 1) (equilateralPoint 2) = 1 := by
  have h3 : Real.sqrt 3 ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
  have e1 : equilateralPoint 1 = (1 : ℂ) := rfl
  have e2 : equilateralPoint 2 = (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) := rfl
  rw [e1, e2, Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq]
  rw [show ((1 : ℂ) - ⟨1 / 2, Real.sqrt 3 / 2⟩).re ^ (2 : ℕ)
      + ((1 : ℂ) - ⟨1 / 2, Real.sqrt 3 / 2⟩).im ^ (2 : ℕ)
      = (1 / 2 : ℝ) ^ (2 : ℕ) + (Real.sqrt 3 / 2) ^ (2 : ℕ) from by simp; ring]
  rw [show ((1 : ℝ) / 2) ^ (2 : ℕ) + (Real.sqrt 3 / 2) ^ (2 : ℕ) = 1 / 4 + Real.sqrt 3 ^ (2 : ℕ) / 4 from by ring, h3]
  norm_num

theorem equilateralPoint_dist_20 : dist (equilateralPoint 2) (equilateralPoint 0) = 1 := by
  have h3 : Real.sqrt 3 ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
  have e0 : equilateralPoint 0 = (0 : ℂ) := rfl
  have e2 : equilateralPoint 2 = (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) := rfl
  rw [e0, e2, Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq]
  rw [show ((⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 0).re ^ (2 : ℕ)
      + ((⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 0).im ^ (2 : ℕ)
      = (1 / 2 : ℝ) ^ (2 : ℕ) + (Real.sqrt 3 / 2) ^ (2 : ℕ) from by simp]
  rw [show ((1 : ℝ) / 2) ^ (2 : ℕ) + (Real.sqrt 3 / 2) ^ (2 : ℕ) = 1 / 4 + Real.sqrt 3 ^ (2 : ℕ) / 4 from by ring, h3]
  norm_num

/-- The regular tetrahedron as a closed triangulated surface: four faces, each an isometric copy of
the unit equilateral triangle, glued along six edges. -/
noncomputable def tetrahedron : ClosedTriangulation (Fin 4) (Fin 4) :=
  ClosedTriangulation.ofRealization (W := ℂ) (P := ℂ) tetraCorner (fun _ => equilateralPoint)
    (fun _ => by simp [equilateralPoint])
    (by decide)

theorem tetrahedron_edges_card : tetrahedron.edges.card = 6 := by decide

theorem tetrahedron_eulerChar : tetrahedron.eulerChar = 2 := by
  unfold ClosedTriangulation.eulerChar
  rw [tetrahedron_edges_card]
  simp

/-- **Gauss--Bonnet for the tetrahedron.**  Its total angular defect is `4π = 2π·χ(S²)`. -/
theorem tetrahedron_totalDefect : tetrahedron.totalDefect = 4 * π := by
  rw [ClosedTriangulation.gauss_bonnet_polyhedral, tetrahedron_eulerChar]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry.GaussBonnet
