import GaloisForLFunctions.HTGeometry.DisjointPacketSpectrum
import GaloisForLFunctions.HTGeometry.RealAffineHermitianFamilyProjectiveGenericity

/-!
# Interaction coordinates of a site-factorized network

The admissible Hamiltonians of a finite interaction graph are the real span of
Hermitian operators supported on single sites and on interaction edges.  Fixing
a Hermitian basis of each admissible packet turns that span into an explicit
real affine family, whose coordinates are indexed by

```
Σ (admissible packet P), (basis index of the Hermitian operators on P)
```

Every vertex subset `S` reads the *same* coordinates: the block of an ambient
generator inside `S` is the generator itself when its packet lies in `S`, and
zero otherwise.  So a whole atlas of subsystems is described by one real
parameter space, which is exactly the input of the simultaneous genericity
theorem.
-/

open scoped Matrix Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-! ### Linearity of the packet lifts -/

variable {A}

theorem liftLocalMatrix_zero (S : Finset V) :
    liftLocalMatrix (A := A) (R := ℂ) S 0 = 0 := by
  ext x y
  simp [liftLocalMatrix]

theorem liftLocalMatrix_add (S : Finset V)
    (B B' : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ) :
    liftLocalMatrix S (B + B') = liftLocalMatrix S B + liftLocalMatrix S B' := by
  ext x y
  by_cases h : restrictOutsideConfiguration S x =
      restrictOutsideConfiguration S y <;>
    simp [liftLocalMatrix, h]

theorem liftLocalMatrix_smul (S : Finset V) (c : ℝ)
    (B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ) :
    liftLocalMatrix S (c • B) = c • liftLocalMatrix S B := by
  ext x y
  by_cases h : restrictOutsideConfiguration S x =
      restrictOutsideConfiguration S y <;>
    simp [liftLocalMatrix, h]

theorem conjTranspose_liftLocalMatrixToSuperset {T S : Finset V} (hTS : T ⊆ S)
    (M : Matrix (LocalConfiguration A T) (LocalConfiguration A T) ℂ) :
    (liftLocalMatrixToSuperset hTS M)ᴴ = liftLocalMatrixToSuperset hTS Mᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, liftLocalMatrixToSuperset]
  by_cases h : restrictRelativeOutsideConfiguration T S x =
      restrictRelativeOutsideConfiguration T S y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), star_zero]

theorem isHermitian_liftLocalMatrixToSuperset {T S : Finset V} (hTS : T ⊆ S)
    {M : Matrix (LocalConfiguration A T) (LocalConfiguration A T) ℂ}
    (hM : M.IsHermitian) :
    (liftLocalMatrixToSuperset hTS M).IsHermitian := by
  show (liftLocalMatrixToSuperset hTS M)ᴴ = _
  rw [conjTranspose_liftLocalMatrixToSuperset, hM]

/-! ### Canonical Hermitian basis of a packet -/

variable (A)

/-- Dimension of the real space of Hermitian operators of one site packet. -/
def packetHermitianDim (S : Finset V) : ℕ :=
  Module.finrank ℝ (selfAdjoint.submodule ℝ
    (Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ))

/-- Canonical Hermitian basis of the operator space of one site packet. -/
def packetHermitianGenerator (S : Finset V) :
    Fin (packetHermitianDim A S) →
      Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ :=
  fun i => (Module.finBasis ℝ (selfAdjoint.submodule ℝ
    (Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ)) i).1

omit [DecidableEq V] [∀ v, DecidableEq (A v)] in
theorem packetHermitianGenerator_isHermitian (S : Finset V)
    (i : Fin (packetHermitianDim A S)) :
    (packetHermitianGenerator A S i).IsHermitian :=
  (Module.finBasis ℝ (selfAdjoint.submodule ℝ
    (Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ)) i).2

omit [DecidableEq V] [∀ v, DecidableEq (A v)] in
/-- Every Hermitian packet block is a real combination of the canonical
generators. -/
theorem mem_span_packetHermitianGenerator (S : Finset V)
    {B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ}
    (hB : B.IsHermitian) :
    B ∈ Submodule.span ℝ (Set.range (packetHermitianGenerator A S)) := by
  classical
  have hx : (⟨B, hB⟩ : selfAdjoint.submodule ℝ
        (Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ)) ∈
      Submodule.span ℝ (Set.range (Module.finBasis ℝ (selfAdjoint.submodule ℝ
        (Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ)))) :=
    Module.Basis.mem_span _ _
  have himg := Submodule.mem_map_of_mem
    (f := (selfAdjoint.submodule ℝ
      (Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ)).subtype) hx
  rw [Submodule.map_span, ← Set.range_comp] at himg
  exact himg

/-! ### Admissible interaction packets -/

/-- Site packets carrying an admissible interaction term: single sites and
interaction edges. -/
def interactionPackets (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset V) :=
  Finset.univ.image (fun v : V => ({v} : Finset V)) ∪
    (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).image
      (fun p : V × V => ({p.1, p.2} : Finset V))

theorem singleton_mem_interactionPackets {G : SimpleGraph V}
    [DecidableRel G.Adj] (v : V) :
    ({v} : Finset V) ∈ interactionPackets G := by
  refine Finset.mem_union_left _ ?_
  exact Finset.mem_image_of_mem _ (Finset.mem_univ v)

theorem pair_mem_interactionPackets {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) :
    ({u, v} : Finset V) ∈ interactionPackets G := by
  refine Finset.mem_union_right _ ?_
  refine Finset.mem_image.2 ⟨(u, v), ?_, rfl⟩
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, huv⟩

/-- Real coordinates of the admissible interaction terms of a graph. -/
def InteractionCoordinate (G : SimpleGraph V) [DecidableRel G.Adj] : Type _ :=
  Σ P : {P : Finset V // P ∈ interactionPackets G},
    Fin (packetHermitianDim A P.1)

instance instFintypeInteractionCoordinate (G : SimpleGraph V)
    [DecidableRel G.Adj] : Fintype (InteractionCoordinate A G) := by
  unfold InteractionCoordinate
  infer_instance

instance instDecidableEqInteractionCoordinate (G : SimpleGraph V)
    [DecidableRel G.Adj] : DecidableEq (InteractionCoordinate A G) := by
  unfold InteractionCoordinate
  infer_instance

/-- Ambient generator of one interaction coordinate. -/
def ambientInteractionGenerator (G : SimpleGraph V) [DecidableRel G.Adj] :
    InteractionCoordinate A G → Matrix (∀ v, A v) (∀ v, A v) ℂ :=
  fun θ => liftLocalMatrix θ.1.1 (packetHermitianGenerator A θ.1.1 θ.2)

theorem ambientInteractionGenerator_isHermitian (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ : InteractionCoordinate A G) :
    (ambientInteractionGenerator A G θ).IsHermitian :=
  isHermitian_liftLocalMatrix _ (packetHermitianGenerator_isHermitian A _ _)

theorem ambientInteractionGenerator_mem (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ : InteractionCoordinate A G) :
    ambientInteractionGenerator A G θ ∈ siteFactorLocalSubmodule A G := by
  have hpacket := θ.1.2
  have hsupp : IsSiteSupported θ.1.1 (ambientInteractionGenerator A G θ) :=
    isSiteSupported_liftLocalMatrix _ _
  rcases Finset.mem_union.1 hpacket with hsingle | hpair
  · obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hsingle
    refine mem_siteFactorLocalSubmodule_of_oneSite A G
      (ambientInteractionGenerator_isHermitian A G θ) v ?_
    rw [hv]
    exact hsupp
  · obtain ⟨p, hp, hpair'⟩ := Finset.mem_image.1 hpair
    have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.1 hp).2
    refine mem_siteFactorLocalSubmodule_of_edge A G
      (ambientInteractionGenerator_isHermitian A G θ) hadj ?_
    rw [hpair']
    exact hsupp

/-- Lifting a packet block that lies in the span of the packet basis lands in
the span of the ambient interaction generators. -/
theorem liftLocalMatrix_mem_span_ambientInteractionGenerator
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (hP : P ∈ interactionPackets G)
    {B : Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ}
    (hB : B ∈ Submodule.span ℝ (Set.range (packetHermitianGenerator A P))) :
    liftLocalMatrix P B ∈
      Submodule.span ℝ (Set.range (ambientInteractionGenerator A G)) := by
  induction hB using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨i, rfl⟩ := hX
      exact Submodule.subset_span ⟨⟨⟨P, hP⟩, i⟩, rfl⟩
  | zero =>
      rw [liftLocalMatrix_zero]
      exact Submodule.zero_mem _
  | add X Y _ _ hX hY =>
      rw [liftLocalMatrix_add]
      exact Submodule.add_mem _ hX hY
  | smul c X _ hX =>
      rw [liftLocalMatrix_smul]
      exact Submodule.smul_mem _ c hX

/-- **The interaction coordinates span the local Hamiltonian space.** -/
theorem span_ambientInteractionGenerator [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Submodule.span ℝ (Set.range (ambientInteractionGenerator A G)) =
      siteFactorLocalSubmodule A G := by
  classical
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro H ⟨θ, rfl⟩
    exact ambientInteractionGenerator_mem A G θ
  · refine Submodule.span_le.2 ?_
    rintro H ⟨hHermitian, hcase⟩
    obtain ⟨P, hP, hsupp⟩ :
        ∃ P : Finset V, P ∈ interactionPackets G ∧ IsSiteSupported P H := by
      rcases hcase with ⟨v, hv⟩ | ⟨u, v, huv, hsupp⟩
      · exact ⟨{v}, singleton_mem_interactionPackets v, hv⟩
      · exact ⟨{u, v}, pair_mem_interactionPackets huv, hsupp⟩
    obtain ⟨B, hBeq⟩ := exists_liftLocalMatrix_of_isSiteSupported hsupp
    have hB : B.IsHermitian := by
      refine isHermitian_of_isHermitian_liftLocalMatrix P ?_
      rw [← hBeq]
      exact hHermitian
    rw [hBeq]
    exact liftLocalMatrix_mem_span_ambientInteractionGenerator A G P hP
      (mem_span_packetHermitianGenerator A P hB)

/-! ### Subsystem blocks in the same coordinates -/

/-- The block inside `S` of an ambient interaction generator: the generator
itself when its packet lies in `S`, and zero otherwise. -/
def restrictedInteractionGenerator (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : InteractionCoordinate A G →
      Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ :=
  fun θ =>
    if h : θ.1.1 ⊆ S then
      liftLocalMatrixToSuperset h (packetHermitianGenerator A θ.1.1 θ.2)
    else 0

theorem restrictedInteractionGenerator_isHermitian (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (θ : InteractionCoordinate A G) :
    (restrictedInteractionGenerator A G S θ).IsHermitian := by
  unfold restrictedInteractionGenerator
  by_cases h : θ.1.1 ⊆ S
  · rw [dif_pos h]
    exact isHermitian_liftLocalMatrixToSuperset h
      (packetHermitianGenerator_isHermitian A _ _)
  · rw [dif_neg h]
    exact Matrix.isHermitian_zero

/-- **The subsystem block lifts back to the ambient generator.** -/
theorem liftLocalMatrix_restrictedInteractionGenerator (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (θ : InteractionCoordinate A G)
    (h : θ.1.1 ⊆ S) :
    liftLocalMatrix S (restrictedInteractionGenerator A G S θ) =
      ambientInteractionGenerator A G θ := by
  unfold restrictedInteractionGenerator ambientInteractionGenerator
  rw [dif_pos h, liftLocalMatrix_liftLocalMatrixToSuperset]

theorem liftLocalMatrix_restrictedInteractionGenerator_of_not_subset
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (θ : InteractionCoordinate A G) (h : ¬ θ.1.1 ⊆ S) :
    liftLocalMatrix S (restrictedInteractionGenerator A G S θ) = 0 := by
  unfold restrictedInteractionGenerator
  rw [dif_neg h, liftLocalMatrix_zero]

/-! ### Enumerated coordinates and the subsystem affine families -/

/-- Number of real interaction coordinates of a graph. -/
def interactionCoordinateCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Fintype.card (InteractionCoordinate A G)

/-- Canonical enumeration of the interaction coordinates. -/
def interactionCoordinateEquiv (G : SimpleGraph V) [DecidableRel G.Adj] :
    InteractionCoordinate A G ≃ Fin (interactionCoordinateCount A G) :=
  Fintype.equivFin _

/-- Ambient interaction generators in the canonical enumeration. -/
def ambientGeneratorFin (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (interactionCoordinateCount A G) →
      Matrix (∀ v, A v) (∀ v, A v) ℂ :=
  fun i =>
    ambientInteractionGenerator A G ((interactionCoordinateEquiv A G).symm i)

/-- Subsystem blocks in the canonical enumeration. -/
def restrictedGeneratorFin (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Fin (interactionCoordinateCount A G) →
      Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ :=
  fun i =>
    restrictedInteractionGenerator A G S
      ((interactionCoordinateEquiv A G).symm i)

theorem ambientGeneratorFin_isHermitian (G : SimpleGraph V)
    [DecidableRel G.Adj] (i : Fin (interactionCoordinateCount A G)) :
    (ambientGeneratorFin A G i).IsHermitian :=
  ambientInteractionGenerator_isHermitian A G _

theorem restrictedGeneratorFin_isHermitian (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V)
    (i : Fin (interactionCoordinateCount A G)) :
    (restrictedGeneratorFin A G S i).IsHermitian :=
  restrictedInteractionGenerator_isHermitian A G S _

omit [DecidableEq V] [∀ v, DecidableEq (A v)] in
theorem realAffineMatrix_zero_base {m : ℕ} {I : Type*} [Fintype I]
    (generator : Fin m → Matrix I I ℂ) (p : Fin m → ℝ) :
    realAffineMatrix 0 generator p = ∑ t, p t • generator t := by
  ext a b
  simp [realAffineMatrix, Matrix.sum_apply]

/-- **Subsystem Hamiltonians are the ambient terms inside the subsystem.**
The block Hamiltonian read by a vertex subset lifts back to exactly the sum of
those ambient interaction terms whose packet lies inside the subset. -/
theorem liftLocalMatrix_realAffineMatrix_restricted [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (p : Fin (interactionCoordinateCount A G) → ℝ) :
    liftLocalMatrix S
        (realAffineMatrix 0 (restrictedGeneratorFin A G S) p) =
      ∑ i ∈ Finset.univ.filter
          (fun i => ((interactionCoordinateEquiv A G).symm i).1.1 ⊆ S),
        p i • ambientGeneratorFin A G i := by
  classical
  rw [realAffineMatrix_zero_base]
  have hlift : liftLocalMatrix S (∑ i, p i • restrictedGeneratorFin A G S i) =
      ∑ i, liftLocalMatrix S (p i • restrictedGeneratorFin A G S i) := by
    induction (Finset.univ : Finset (Fin (interactionCoordinateCount A G)))
      using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, liftLocalMatrix_zero]
    | insert i t hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, liftLocalMatrix_add, ih]
  rw [hlift]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ((interactionCoordinateEquiv A G).symm i).1.1 ⊆ S
  · rw [if_pos h]
    simp only [restrictedGeneratorFin, ambientGeneratorFin]
    rw [liftLocalMatrix_smul,
      liftLocalMatrix_restrictedInteractionGenerator A G S _ h]
  · rw [if_neg h]
    simp only [restrictedGeneratorFin]
    rw [liftLocalMatrix_smul,
      liftLocalMatrix_restrictedInteractionGenerator_of_not_subset A G S _ h,
      smul_zero]

/-- Parameters at which the subsystem read by a vertex subset has maximal
projective spectral rank. -/
def subsystemMaximalSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    Set (Fin (interactionCoordinateCount A G) → ℝ) :=
  realAffineHermitianMaximalSet 0 (restrictedGeneratorFin A G S)
    Matrix.isHermitian_zero (restrictedGeneratorFin_isHermitian A G S)

/-- **One subsystem is generically maximally projective.**  A single witness
parameter makes the whole subsystem locus dense, residual and of full Lebesgue
measure in the ambient interaction coordinates. -/
theorem subsystemMaximalSet_dense_residual_fullMeasure
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (p₀ : Fin (interactionCoordinateCount A G) → ℝ)
    (hmax : MaximallyProjectiveEnergy
      (realAffineMatrix_isHermitian 0 (restrictedGeneratorFin A G S)
        Matrix.isHermitian_zero
        (restrictedGeneratorFin_isHermitian A G S) p₀).eigenvalues) :
    Dense (subsystemMaximalSet A G S) ∧
      subsystemMaximalSet A G S ∈
        residual (Fin (interactionCoordinateCount A G) → ℝ) ∧
      MeasureTheory.volume (subsystemMaximalSet A G S)ᶜ = 0 :=
  realAffineHermitianMaximalSet_dense_residual_fullMeasure 0
    (restrictedGeneratorFin A G S) Matrix.isHermitian_zero
    (restrictedGeneratorFin_isHermitian A G S) p₀ hmax

/-- Parameters at which every subsystem of a supplied countable family is
maximally projective. -/
def simultaneousSubsystemMaximalSet (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} (S : ι → Finset V) :
    Set (Fin (interactionCoordinateCount A G) → ℝ) :=
  {p | ∀ a, p ∈ subsystemMaximalSet A G (S a)}

/-- **Simultaneous subsystem atlas of a finite network.**  Given one witness per
subsystem, the parameters at which *all* supplied subsystems are maximally
projective at once are dense, residual and of full Lebesgue measure in the
ambient interaction coordinates. -/
theorem simultaneousSubsystemMaximalSet_dense_residual_fullMeasure
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Countable ι] (S : ι → Finset V)
    (p₀ : ι → (Fin (interactionCoordinateCount A G) → ℝ))
    (hmax : ∀ a, MaximallyProjectiveEnergy
      (realAffineMatrix_isHermitian 0 (restrictedGeneratorFin A G (S a))
        Matrix.isHermitian_zero
        (restrictedGeneratorFin_isHermitian A G (S a)) (p₀ a)).eigenvalues) :
    Dense (simultaneousSubsystemMaximalSet A G S) ∧
      simultaneousSubsystemMaximalSet A G S ∈
        residual (Fin (interactionCoordinateCount A G) → ℝ) ∧
      MeasureTheory.volume (simultaneousSubsystemMaximalSet A G S)ᶜ = 0 := by
  have hpiece : ∀ a,
      subsystemMaximalSet A G (S a) ∈
          residual (Fin (interactionCoordinateCount A G) → ℝ) ∧
        MeasureTheory.volume (subsystemMaximalSet A G (S a))ᶜ = 0 := by
    intro a
    obtain ⟨-, hres, hnull⟩ :=
      subsystemMaximalSet_dense_residual_fullMeasure A G (S a) (p₀ a) (hmax a)
    exact ⟨hres, hnull⟩
  have hiInter : simultaneousSubsystemMaximalSet A G S =
      ⋂ a, subsystemMaximalSet A G (S a) := by
    ext p
    simp [simultaneousSubsystemMaximalSet]
  have hres : simultaneousSubsystemMaximalSet A G S ∈
      residual (Fin (interactionCoordinateCount A G) → ℝ) := by
    rw [hiInter]
    exact countable_iInter_mem.2 fun a => (hpiece a).1
  refine ⟨dense_of_mem_residual hres, hres, ?_⟩
  rw [hiInter, Set.compl_iInter]
  exact MeasureTheory.measure_iUnion_null fun a => (hpiece a).2

end

end GaloisForLFunctions.HTGeometry
