import GaloisForLFunctions.HTGeometry.ConstitutiveQuadraticFilling
import GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantTorsion

/-!
# Derived and homotopy endpoint insufficiency for torsion and filling cost

Two lossy observers are isolated and shown to be strictly lossy.

* A **derived observer** of the based two-term complexes `C(u) : 0 → k →(·u) k → 0` sees only their
  homology.  All of them are acyclic, so every derived observer is constant on the family, while the
  determinant history `τ(C(u)) = u` is not: `torsion_not_derivedObserver`.
* An **endpoint observer** of words sees only the represented group element.  Every null word
  `w n = aⁿ bⁿ a⁻ⁿ b⁻ⁿ` represents the identity, so every endpoint observer is constant on the
  family, while the van Kampen area `n²` is not: `area_not_endpointObserver`.
* An **unweighted observer** of the minimal fillings sees only their Euler characteristic.  Every
  `n × n` grid filling has Euler characteristic one — the value of a disk — while its cell count is
  `n²`: `gridFaces_not_eulerObserver`.

Hence a universal law field cannot consist of homotopy types and matching maps alone; determinant
memory or quantitative filling weights must be carried as extra structure.
-/

namespace GaloisForLFunctions.HTGeometry

section DerivedObserver

variable {k : Type*} [Field k] {Y : Type*}

/-- An observer of the based family that factors through the derived category: it cannot separate
complexes with the same homology, that is with the same degree-one kernel and the same degree-zero
image. -/
def DerivedObserver (F : kˣ → Y) : Prop :=
  ∀ u v : kˣ,
    LinearMap.ker (torsionDifferential (u : k)) = LinearMap.ker (torsionDifferential (v : k)) →
    LinearMap.range (torsionDifferential (u : k)) = LinearMap.range (torsionDifferential (v : k)) →
    F u = F v

/-- **Every derived observer is constant on the based family**, because every member is acyclic. -/
theorem derivedObserver_constant {F : kˣ → Y} (hF : DerivedObserver F) (u v : kˣ) : F u = F v := by
  obtain ⟨hker, hrange⟩ := homology_indistinguishable (u : k) (v : k) u.ne_zero v.ne_zero
  exact hF u v hker hrange

/-- **The determinant history is not a derived observer.**  It separates the members of a family
that the derived category collapses to a single object. -/
theorem torsion_not_derivedObserver (h : ∃ u v : kˣ, u ≠ v) :
    ¬ DerivedObserver (fun u : kˣ => (u : k)) := by
  obtain ⟨u, v, huv⟩ := h
  intro hF
  exact huv (Units.ext (derivedObserver_constant hF u v))

end DerivedObserver

section EndpointObserver

variable {Y : Type*}

/-- An observer of words that factors only through the represented group element. -/
def EndpointObserver (F : FreeGroup (Fin 2) → Y) : Prop :=
  ∀ w w' : FreeGroup (Fin 2),
    (QuotientGroup.mk w :
        FreeGroup (Fin 2) ⧸ Subgroup.normalClosure ({relator} : Set (FreeGroup (Fin 2))))
      = QuotientGroup.mk w' → F w = F w'

/-- **Every endpoint observer is constant on the null words**, because they all represent the
identity. -/
theorem endpointObserver_constant {F : FreeGroup (Fin 2) → Y} (hF : EndpointObserver F)
    (n m : ℕ) : F (nullWord n) = F (nullWord m) :=
  hF _ _ (by rw [nullWord_eq_one_in_quotient, nullWord_eq_one_in_quotient])

/-- **The van Kampen area is not an endpoint observer.** -/
theorem area_not_endpointObserver : ¬ EndpointObserver area := by
  intro hF
  have h := endpointObserver_constant hF 1 2
  rw [area_nullWord, area_nullWord] at h
  omega

end EndpointObserver

section UnweightedObserver

/-- Vertices of the `n × n` grid filling. -/
def gridVertices (n : ℕ) : ℤ := ((n : ℤ) + 1) ^ 2

/-- Edges of the `n × n` grid filling. -/
def gridEdges (n : ℕ) : ℤ := 2 * (n : ℤ) * ((n : ℤ) + 1)

/-- Two-cells of the `n × n` grid filling: its cellular area. -/
def gridFaces (n : ℕ) : ℤ := (n : ℤ) ^ 2

/-- **Every grid filling has the Euler characteristic of a disk.** -/
theorem grid_euler (n : ℕ) : gridVertices n - gridEdges n + gridFaces n = 1 := by
  simp only [gridVertices, gridEdges, gridFaces]
  ring

/-- An observer of the fillings that factors only through their unweighted type, recorded by the
Euler characteristic. -/
def EulerObserver {Y : Type*} (F : ℕ → Y) : Prop :=
  ∀ n m : ℕ,
    gridVertices n - gridEdges n + gridFaces n = gridVertices m - gridEdges m + gridFaces m →
      F n = F m

/-- **Every unweighted observer is constant on the grid fillings.** -/
theorem eulerObserver_constant {Y : Type*} {F : ℕ → Y} (hF : EulerObserver F) (n m : ℕ) :
    F n = F m :=
  hF n m (by rw [grid_euler, grid_euler])

/-- **The cellular area is not an unweighted observer.** -/
theorem gridFaces_not_eulerObserver : ¬ EulerObserver gridFaces := by
  intro hF
  have h := eulerObserver_constant hF 1 2
  simp only [gridFaces] at h
  norm_num at h

/-- The grid filling of the null word really has `n²` cells. -/
theorem gridFaces_eq_area (n : ℕ) : gridFaces n = (area (nullWord n) : ℤ) := by
  rw [gridFaces, area_nullWord]
  push_cast
  ring

end UnweightedObserver

section Capstone

/-- **Endpoint insufficiency.**  On one side the derived observer of the based two-term family and
the endpoint observer of the null words are constant; on the other the determinant history, the van
Kampen area, and the cellular area of the minimal fillings are not.  Homotopy types and matching
maps alone therefore cannot carry determinant memory or filling cost. -/
theorem endpoint_insufficiency (h : ∃ u v : (ℚˣ), u ≠ v) :
    (∀ {Y : Type} (F : ℚˣ → Y), DerivedObserver F → ∀ u v : ℚˣ, F u = F v) ∧
      ¬ DerivedObserver (fun u : ℚˣ => (u : ℚ)) ∧
      (∀ {Y : Type} (F : FreeGroup (Fin 2) → Y), EndpointObserver F →
        ∀ n m : ℕ, F (nullWord n) = F (nullWord m)) ∧
      ¬ EndpointObserver area ∧
      (∀ n : ℕ, gridVertices n - gridEdges n + gridFaces n = 1) ∧
      ¬ EulerObserver gridFaces :=
  ⟨fun _F hF u v => derivedObserver_constant hF u v, torsion_not_derivedObserver h,
    fun _F hF n m => endpointObserver_constant hF n m, area_not_endpointObserver,
    grid_euler, gridFaces_not_eulerObserver⟩

end Capstone

end GaloisForLFunctions.HTGeometry
