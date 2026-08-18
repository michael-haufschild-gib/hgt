import GaloisForLFunctions.HTGeometry.LatticeMinimalVectors

/-!
# Well-rounded lattices and the finiteness of their symmetry groups

A lattice is **well-rounded** when its shortest nonzero vectors span the ambient space.  The
well-rounded lattices form the retract on which `SL_n(𝒪)` acts cocompactly, and the reason the
action has **finite** stabilizers — which is what makes the equivariant chain complex finitely
generated, hence `H_i(SL_n(𝒪), ℤ)` finitely generated — is elementary: a norm-preserving linear
automorphism carrying the lattice to itself permutes the finitely many minimal vectors, and on a
well-rounded lattice those span, so the automorphism is determined by that permutation.

* `IsLatticeMinimum` : `m` is the length of a shortest nonzero vector.
* `exists_isLatticeMinimum` : it exists.
* `latticeMinimalVectors` : the shortest vectors; finite, and nonempty at the minimum.
* `IsWellRounded` : they span.
* `mapsTo_latticeMinimalVectors` : a lattice isometry permutes them.
* `finite_latticeIsometry_of_wellRounded` : **the isometry group of a well-rounded lattice is
  finite.**
-/

namespace GaloisForLFunctions.HTGeometry

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- `m` is the length of a shortest nonzero vector of `L`. -/
def IsLatticeMinimum (L : Submodule ℤ E) (m : ℝ) : Prop :=
  (∃ v ∈ L, v ≠ (0 : E) ∧ ‖v‖ = m) ∧ ∀ w ∈ L, w ≠ (0 : E) → m ≤ ‖w‖

omit [NormedSpace ℝ E] in
theorem exists_isLatticeMinimum (L : Submodule ℤ E) [DiscreteTopology L]
    (hne : ∃ v ∈ L, v ≠ (0 : E)) : ∃ m : ℝ, IsLatticeMinimum L m := by
  obtain ⟨v, hvL, hv, hmin⟩ := exists_minimal_norm L hne
  exact ⟨‖v‖, ⟨v, hvL, hv, rfl⟩, hmin⟩

/-- The shortest nonzero vectors of `L`. -/
def latticeMinimalVectors (L : Submodule ℤ E) (m : ℝ) : Set E :=
  {v | v ∈ L ∧ v ≠ (0 : E) ∧ ‖v‖ = m}

omit [NormedSpace ℝ E] in
theorem latticeMinimalVectors_finite (L : Submodule ℤ E) [DiscreteTopology L] (m : ℝ) :
    (latticeMinimalVectors L m).Finite := by
  refine (finite_lattice_inter_of_bounded L
    (Metric.isBounded_closedBall (x := (0 : E)) (r := m))).subset ?_
  rintro v ⟨hvL, _, hnorm⟩
  refine ⟨?_, hvL⟩
  simp [Metric.mem_closedBall, dist_zero_right, hnorm]

omit [NormedSpace ℝ E] [ProperSpace E] in
theorem latticeMinimalVectors_nonempty {L : Submodule ℤ E} {m : ℝ} (hm : IsLatticeMinimum L m) :
    (latticeMinimalVectors L m).Nonempty := by
  obtain ⟨⟨v, hvL, hv, hnorm⟩, _⟩ := hm
  exact ⟨v, hvL, hv, hnorm⟩

/-- A lattice is **well-rounded** when its shortest vectors span the ambient space. -/
def IsWellRounded (L : Submodule ℤ E) (m : ℝ) : Prop :=
  Submodule.span ℝ (latticeMinimalVectors L m) = ⊤

omit [ProperSpace E] in
/-- **A norm-preserving automorphism carrying `L` into itself permutes the shortest vectors.** -/
theorem mapsTo_latticeMinimalVectors {L : Submodule ℤ E} {m : ℝ} (f : E ≃ₗ[ℝ] E)
    (hiso : ∀ v, ‖f v‖ = ‖v‖) (hL : ∀ v ∈ L, f v ∈ L) :
    Set.MapsTo f (latticeMinimalVectors L m) (latticeMinimalVectors L m) := by
  rintro v ⟨hvL, hv, hnorm⟩
  refine ⟨hL v hvL, ?_, ?_⟩
  · intro h
    exact hv (by simpa using f.injective (by rw [h, map_zero]))
  · rw [hiso, hnorm]

omit [ProperSpace E] in
/-- Two linear maps agreeing on the shortest vectors of a well-rounded lattice are equal. -/
theorem eq_of_eqOn_latticeMinimalVectors {L : Submodule ℤ E} {m : ℝ}
    (hwr : IsWellRounded L m) {f g : E →ₗ[ℝ] E}
    (h : ∀ v ∈ latticeMinimalVectors L m, f v = g v) : f = g := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ Submodule.span ℝ (latticeMinimalVectors L m) := by
    rw [hwr]
    exact Submodule.mem_top
  exact LinearMap.eqOn_span h hx

/-- **The isometry group of a well-rounded lattice is finite.**  A lattice isometry permutes the
finitely many shortest vectors, and on a well-rounded lattice those span, so the isometry is
determined by that permutation.  This is the finite-stabilizer input of the well-rounded retract. -/
theorem finite_latticeIsometry_of_wellRounded {L : Submodule ℤ E} [DiscreteTopology L] {m : ℝ}
    (hwr : IsWellRounded L m) :
    {f : E ≃ₗ[ℝ] E | (∀ v, ‖f v‖ = ‖v‖) ∧ ∀ v ∈ L, f v ∈ L}.Finite := by
  classical
  haveI : Finite (latticeMinimalVectors L m) :=
    (latticeMinimalVectors_finite L m).to_subtype
  set Φ : {f : E ≃ₗ[ℝ] E | (∀ v, ‖f v‖ = ‖v‖) ∧ ∀ v ∈ L, f v ∈ L} →
      (latticeMinimalVectors L m) → (latticeMinimalVectors L m) :=
    fun f v => ⟨(f : E ≃ₗ[ℝ] E) v,
      mapsTo_latticeMinimalVectors (f : E ≃ₗ[ℝ] E) f.2.1 f.2.2 v.2⟩ with hΦ
  have hinj : Function.Injective Φ := by
    intro f g hfg
    refine Subtype.ext (LinearEquiv.toLinearMap_injective ?_)
    refine eq_of_eqOn_latticeMinimalVectors hwr fun v hv => ?_
    have := congrArg (fun h => ((h ⟨v, hv⟩ : latticeMinimalVectors L m) : E)) hfg
    exact this
  exact Set.finite_coe_iff.1 (Finite.of_injective Φ hinj)

omit [ProperSpace E] in
/-- **A well-rounded lattice has an `ℝ`-basis of shortest vectors.**  Extracting a maximal
independent subset of the shortest vectors does not change their span, which is everything. -/
theorem exists_independent_spanning_latticeMinimalVectors {L : Submodule ℤ E} {m : ℝ}
    (hwr : IsWellRounded L m) :
    ∃ B ⊆ latticeMinimalVectors L m, LinearIndependent ℝ ((↑) : B → E) ∧
      Submodule.span ℝ B = ⊤ := by
  obtain ⟨B, hBsub, hspan, hind⟩ := exists_linearIndependent ℝ (latticeMinimalVectors L m)
  exact ⟨B, hBsub, hind, by rw [hspan]; exact hwr⟩

omit [ProperSpace E] in
/-- Such a family is finite in a finite-dimensional space. -/
theorem exists_finite_independent_spanning_latticeMinimalVectors [FiniteDimensional ℝ E]
    {L : Submodule ℤ E} {m : ℝ} (hwr : IsWellRounded L m) :
    ∃ B ⊆ latticeMinimalVectors L m, B.Finite ∧ LinearIndependent ℝ ((↑) : B → E) ∧
      Submodule.span ℝ B = ⊤ := by
  obtain ⟨B, hBsub, hind, hspan⟩ := exists_independent_spanning_latticeMinimalVectors hwr
  exact ⟨B, hBsub, hind.setFinite, hind, hspan⟩

end GaloisForLFunctions.HTGeometry
