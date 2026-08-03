import GaloisForLFunctions.HTGeometry.PhaseOrbitClosureSubtorus

/-!
# Kronecker density in an infinite product torus

A basic open set of a product torus constrains only finitely many coordinates, so density of a phase
flow is a statement about its finite coordinate projections.  For a frequency family every finite
subfamily of which is rationally independent, each projection is the dense flow of a finite
rationally independent packet, and the whole flow is therefore dense in the full product torus --
however many coordinates it has.

This is the infinite Bohr hull of an almost periodic carrier with countably many rationally
independent frequencies.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A frequency family is rationally independent when every finite subfamily is: no nonzero
finitely supported integer character annihilates it. -/
def RationallyIndependentSequence {ι : Type*} (omega : ι → ℝ) : Prop :=
  ∀ s : Finset ι, RationallyIndependentFrequency fun i : (s : Set ι) => omega i

/-- The phase flow of an arbitrary frequency family, in the product torus of its index set. -/
def clockPhasePoint {ι : Type*} (omega : ι → ℝ) (t : ℝ) : UnitAddTorus ι :=
  fun i => ((t * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle)

theorem clockPhasePoint_restrict {ι : Type*} (omega : ι → ℝ) (s : Finset ι) (t : ℝ)
    (i : (s : Set ι)) :
    finiteClockPhasePoint (fun j : (s : Set ι) => omega j) t i = clockPhasePoint omega t i := rfl

theorem finiteClockPhasePoint_eq_clockPhasePoint {d : Type*} [Fintype d] (omega : d → ℝ) (t : ℝ) :
    finiteClockPhasePoint omega t = clockPhasePoint omega t := rfl

/-- **Kronecker density in a product torus of arbitrary size.**  A rationally independent frequency
family has dense phase orbit in the full product torus. -/
theorem dense_range_clockPhasePoint {ι : Type*} (omega : ι → ℝ)
    (h : RationallyIndependentSequence omega) :
    Dense (Set.range (clockPhasePoint omega)) := by
  classical
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨f, hfU⟩ := hUne
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hUopen f hfU
  have hdense := dense_range_finiteClockPhasePoint (fun j : (I : Set ι) => omega j) (h I)
  set V : Set (UnitAddTorus (I : Set ι)) := Set.univ.pi fun i => u i.1 with hV
  have hVopen : IsOpen V := by
    refine isOpen_set_pi Set.finite_univ fun i _ => ?_
    exact (hu i.1 i.2).1
  have hVne : V.Nonempty := by
    refine ⟨fun i => f i.1, ?_⟩
    intro i _
    exact (hu i.1 i.2).2
  obtain ⟨y, hyV, hyrange⟩ := (dense_iff_inter_open.mp hdense) V hVopen hVne
  obtain ⟨t, rfl⟩ := hyrange
  refine ⟨clockPhasePoint omega t, hsub ?_, ⟨t, rfl⟩⟩
  intro i hi
  have hmem := hyV ⟨i, hi⟩ (Set.mem_univ _)
  rwa [clockPhasePoint_restrict omega I t ⟨i, hi⟩] at hmem


/-- The phase flow is additive in time. -/
theorem clockPhasePoint_add {ι : Type*} (omega : ι → ℝ) (s t : ℝ) :
    clockPhasePoint omega (s + t) = clockPhasePoint omega s + clockPhasePoint omega t := by
  funext i
  simp only [clockPhasePoint, Pi.add_apply, ← AddCircle.coe_add]
  congr 1
  ring

/-- **Density of a forward orbit reduces to its finite projections.**  A basic open set of a product
constrains finitely many coordinates, so if every finite coordinate projection of the flow has dense
forward orbit after any time, so does the whole flow. -/
theorem dense_forwardOrbit_clockPhasePoint {ι : Type*} (omega : ι → ℝ) (T₀ : ℝ)
    (hfin : ∀ s : Finset ι,
      Dense {x : UnitAddTorus (s : Set ι) |
        ∃ t : ℝ, T₀ ≤ t ∧ finiteClockPhasePoint (fun j : (s : Set ι) => omega j) t = x}) :
    Dense {x : UnitAddTorus ι | ∃ t : ℝ, T₀ ≤ t ∧ clockPhasePoint omega t = x} := by
  classical
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨f, hfU⟩ := hUne
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hUopen f hfU
  set V : Set (UnitAddTorus (I : Set ι)) := Set.univ.pi fun i => u i.1 with hV
  have hVopen : IsOpen V := by
    refine isOpen_set_pi Set.finite_univ fun i _ => ?_
    exact (hu i.1 i.2).1
  have hVne : V.Nonempty := by
    refine ⟨fun i => f i.1, ?_⟩
    intro i _
    exact (hu i.1 i.2).2
  obtain ⟨y, hyV, hyorbit⟩ := (dense_iff_inter_open.mp (hfin I)) V hVopen hVne
  obtain ⟨t, htT, rfl⟩ := hyorbit
  refine ⟨clockPhasePoint omega t, hsub ?_, ⟨t, htT, rfl⟩⟩
  intro i hi
  have hmem := hyV ⟨i, hi⟩ (Set.mem_univ _)
  rwa [clockPhasePoint_restrict omega I t ⟨i, hi⟩] at hmem

end

end GaloisForLFunctions.HTGeometry
