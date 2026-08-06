import GaloisForLFunctions.HTGeometry.SubsystemComponentGenericity
import GaloisForLFunctions.HTGeometry.SiteFactorSubsystemTransport
import GaloisForLFunctions.HTGeometry.ComponentScaleShiftWitness

/-!
# The transversality witness of a subsystem

Every connected component of an induced subsystem carries its own maximally
projective Hamiltonian.  Rescaling and shifting those spectra independently
makes their concatenation maximally projective, and the interaction coordinates
of distinct components are disjoint — an admissible term is nonempty and lies in
one component — so the per-component parameters glue into a single ambient
parameter.

That parameter is the one witness needed to make component transversality
generic.
-/

open scoped Matrix BigOperators
open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- A subsystem block only reads the coordinates of terms inside the
subsystem. -/
theorem subsystemBlock_congr (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (p p' : Fin (interactionCoordinateCount A G) → ℝ)
    (h : ∀ θ, ((interactionCoordinateEquiv A G).symm θ).1.1 ⊆ P →
      p θ = p' θ) :
    subsystemBlock A G P p = subsystemBlock A G P p' := by
  classical
  unfold subsystemBlock
  rw [realAffineMatrix_zero_base, realAffineMatrix_zero_base]
  refine Finset.sum_congr rfl fun θ _ => ?_
  by_cases hθ : ((interactionCoordinateEquiv A G).symm θ).1.1 ⊆ P
  · rw [h θ hθ]
  · have hzero : restrictedGeneratorFin A G P θ = 0 := by
      show restrictedInteractionGenerator A G P _ = 0
      unfold restrictedInteractionGenerator
      rw [dif_neg hθ]
    rw [hzero, smul_zero, smul_zero]

/-- The identity is an admissible term of any nonempty site packet. -/
theorem one_mem_span_restrictedGeneratorFin [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] {P : Finset V}
    (hP : P.Nonempty) :
    (1 : Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ) ∈
      Submodule.span ℝ (Set.range (restrictedGeneratorFin A G P)) := by
  classical
  obtain ⟨w, hw⟩ := hP
  refine mem_span_restrictedGeneratorFin_of_isSiteSupported G P
    (T := ({⟨w, hw⟩} : Finset {v : V // v ∈ P})) ?_ ?_ ?_
  · rw [subsystemPacketImage_singleton]
    exact singleton_mem_interactionPackets w
  · exact Matrix.isHermitian_one
  · exact IsSiteSupported.mono (Finset.empty_subset _) isSiteSupported_one

/-- A scaled and shifted subsystem block is again read by some parameter. -/
theorem exists_param_smul_add_one [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] {P : Finset V} (hP : P.Nonempty)
    (p : Fin (interactionCoordinateCount A G) → ℝ) (t s : ℝ) :
    ∃ q : Fin (interactionCoordinateCount A G) → ℝ,
      subsystemBlock A G P q =
        t • subsystemBlock A G P p +
          s • (1 : Matrix (LocalConfiguration A P)
            (LocalConfiguration A P) ℂ) := by
  classical
  have hblock : subsystemBlock A G P p ∈
      Submodule.span ℝ (Set.range (restrictedGeneratorFin A G P)) := by
    rw [subsystemBlock, realAffineMatrix_zero_base]
    exact Submodule.sum_mem _ fun θ _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨θ, rfl⟩)
  have hmem : t • subsystemBlock A G P p +
      s • (1 : Matrix (LocalConfiguration A P)
        (LocalConfiguration A P) ℂ) ∈
      Submodule.span ℝ (Set.range (restrictedGeneratorFin A G P)) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hblock)
      (Submodule.smul_mem _ _ (one_mem_span_restrictedGeneratorFin A G hP))
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  refine ⟨q, ?_⟩
  rw [subsystemBlock, realAffineMatrix_zero_base]
  exact hq

/-- The characteristic relation of a scaled and shifted Hermitian block at a
scaled and shifted eigenvalue. -/
theorem matrixCharpolyRelation_smul_add_one {I : Type*} [Fintype I]
    [DecidableEq I] {H : Matrix I I ℂ} (hH : H.IsHermitian) (t s : ℝ)
    (i : I) :
    matrixCharpolyRelation
      (t • H + s • (1 : Matrix I I ℂ),
        ((hH.eigenvalues i * t + s : ℝ) : ℂ)) = 0 := by
  classical
  have hbase : matrixCharpolyRelation (H, ((hH.eigenvalues i : ℝ) : ℂ)) = 0 :=
    hermitianEigenvalue_matrixCharpolyRelation H hH i
  show (Matrix.scalar I ((hH.eigenvalues i * t + s : ℝ) : ℂ) -
    (t • H + s • (1 : Matrix I I ℂ))).det = 0
  have hrw : Matrix.scalar I ((hH.eigenvalues i * t + s : ℝ) : ℂ) -
      (t • H + s • (1 : Matrix I I ℂ)) =
      (t : ℂ) • (Matrix.scalar I ((hH.eigenvalues i : ℝ) : ℂ) - H) := by
    rw [scalar_eq_smul_one, scalar_eq_smul_one]
    push_cast
    rw [smul_sub]
    simp only [smul_smul]
    ring_nf
    module
  rw [hrw, Matrix.det_smul]
  have hdet : (Matrix.scalar I ((hH.eigenvalues i : ℝ) : ℂ) - H).det = 0 :=
    hbase
  rw [hdet, mul_zero]

variable {A}

/-- Distinct component packets cannot both contain an admissible term. -/
theorem componentPackets_unique (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {P : Finset V} (hP : P ∈ interactionPackets G)
    {c d : {Q : Finset V // Q ∈ componentPackets G S}}
    (hc : P ⊆ c.1) (hd : P ⊆ d.1) : c = d := by
  by_contra hcd
  obtain ⟨v, hv⟩ := nonempty_of_mem_interactionPackets hP
  exact Finset.disjoint_left.1
    (componentPackets_disjoint G S c.2 d.2 (fun h => hcd (Subtype.ext h)))
    (hc hv) (hd hv)

variable (A)

/-- **Transversality witness of a subsystem.**  Some ambient interaction
parameter carries a maximally projective concatenated root packet for the
component blocks of a vertex subset. -/
theorem exists_witness_subsystemComponentGenericSet
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h2 : ∀ v, 2 ≤ Fintype.card (A v)) (S : Finset V) :
    ∃ (p₀ : Fin (interactionCoordinateCount A G) → ℝ)
      (e : ∀ c : {P : Finset V // P ∈ componentPackets G S},
        LocalConfiguration A c.1 → ℝ),
      (∀ c i, matrixCharpolyRelation
        (subsystemBlock A G c.1 p₀, ((e c i : ℝ) : ℂ)) = 0) ∧
      MaximallyProjectiveEnergy
        (fun x : Σ c : {P : Finset V // P ∈ componentPackets G S},
            LocalConfiguration A c.1 => e x.1 x.2) := by
  classical
  have hrep : ∀ c : {P : Finset V // P ∈ componentPackets G S},
      ∃ v : {x : V // x ∈ S}, sitePacketOf G S v = c.1 := by
    intro c
    obtain ⟨v, -, hv⟩ := Finset.mem_image.1 c.2
    exact ⟨v, hv⟩
  choose vrep hvrep using hrep
  have hne : ∀ c : {P : Finset V // P ∈ componentPackets G S}, c.1.Nonempty := by
    intro c
    refine ⟨(vrep c).1, ?_⟩
    rw [← hvrep c]
    exact self_mem_sitePacketOf G S (vrep c)
  have hconn : ∀ c : {P : Finset V // P ∈ componentPackets G S},
      (G.comap (Function.Embedding.subtype
        (fun x : V => x ∈ c.1))).Connected := by
    intro c
    rw [← hvrep c]
    exact connected_induce_sitePacketOf G S (vrep c)
  have hwit : ∀ c : {P : Finset V // P ∈ componentPackets G S},
      ∃ p : Fin (interactionCoordinateCount A G) → ℝ,
        MaximallyProjectiveEnergy
          (subsystemBlock_isHermitian A G c.1 p).eigenvalues := by
    intro c
    exact exists_witness_subsystemMaximalSet_of_connected G c.1 (hne c)
      (hconn c) (fun w => h2 w.1)
  choose pc hpc using hwit
  obtain ⟨q, hq⟩ := exists_scaleShift_maximallyProjective_concat
    (fun c : {P : Finset V // P ∈ componentPackets G S} =>
      (subsystemBlock_isHermitian A G c.1 (pc c)).eigenvalues) hpc
  have hparam : ∀ c : {P : Finset V // P ∈ componentPackets G S},
      ∃ r : Fin (interactionCoordinateCount A G) → ℝ,
        subsystemBlock A G c.1 r =
          q (Sum.inl c) • subsystemBlock A G c.1 (pc c) +
            q (Sum.inr c) • (1 : Matrix (LocalConfiguration A c.1)
              (LocalConfiguration A c.1) ℂ) := by
    intro c
    exact exists_param_smul_add_one A G (hne c) (pc c) _ _
  choose rc hrc using hparam
  refine ⟨fun θ =>
      if h : ∃ c : {P : Finset V // P ∈ componentPackets G S},
          ((interactionCoordinateEquiv A G).symm θ).1.1 ⊆ c.1
        then rc h.choose θ else 0,
    fun c i => (subsystemBlock_isHermitian A G c.1 (pc c)).eigenvalues i *
      q (Sum.inl c) + q (Sum.inr c), ?_, hq⟩
  intro c i
  have hglue : subsystemBlock A G c.1
      (fun θ =>
        if h : ∃ d : {P : Finset V // P ∈ componentPackets G S},
            ((interactionCoordinateEquiv A G).symm θ).1.1 ⊆ d.1
          then rc h.choose θ else 0) =
      subsystemBlock A G c.1 (rc c) := by
    refine subsystemBlock_congr A G c.1 _ _ fun θ hθ => ?_
    have hex : ∃ d : {P : Finset V // P ∈ componentPackets G S},
        ((interactionCoordinateEquiv A G).symm θ).1.1 ⊆ d.1 := ⟨c, hθ⟩
    rw [dif_pos hex]
    have hchoose := hex.choose_spec
    rw [componentPackets_unique G S
      ((interactionCoordinateEquiv A G).symm θ).1.2 hchoose hθ]
  rw [hglue, hrc c]
  exact matrixCharpolyRelation_smul_add_one
    (subsystemBlock_isHermitian A G c.1 (pc c)) _ _ i

/-- **Component transversality is generic.**  For a finite network with all
local dimensions at least two, the parameters at which the component spectra of
a vertex subset are mutually projectively independent are dense, residual and of
full Lebesgue measure. -/
theorem subsystemComponentGenericSet_dense_residual_fullMeasure_of_dim
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h2 : ∀ v, 2 ≤ Fintype.card (A v)) (S : Finset V) :
    Dense (subsystemComponentGenericSet A G S) ∧
      subsystemComponentGenericSet A G S ∈
        residual (Fin (interactionCoordinateCount A G) → ℝ) ∧
      volume (subsystemComponentGenericSet A G S)ᶜ = 0 := by
  obtain ⟨p₀, e, hroot, hmax⟩ :=
    exists_witness_subsystemComponentGenericSet A G h2 S
  exact subsystemComponentGenericSet_dense_residual_fullMeasure A G S p₀ e
    hroot hmax

/-- Parameters at which *every* vertex subset has mutually projectively
independent component spectra. -/
def allSubsystemGenericSet {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Set (Fin (interactionCoordinateCount A G) → ℝ) :=
  {p | ∀ S : Finset V, p ∈ subsystemComponentGenericSet A G S}

/-- **Simultaneous transversality.**  All vertex subsets acquire mutually
projectively independent component spectra at once, on a dense, residual,
full-measure set of interaction parameters. -/
theorem allSubsystemGenericSet_dense_residual_fullMeasure
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h2 : ∀ v, 2 ≤ Fintype.card (A v)) :
    Dense (allSubsystemGenericSet A G) ∧
      allSubsystemGenericSet A G ∈
        residual (Fin (interactionCoordinateCount A G) → ℝ) ∧
      volume (allSubsystemGenericSet A G)ᶜ = 0 := by
  classical
  have hpiece : ∀ S : Finset V,
      subsystemComponentGenericSet A G S ∈
          residual (Fin (interactionCoordinateCount A G) → ℝ) ∧
        volume (subsystemComponentGenericSet A G S)ᶜ = 0 := by
    intro S
    obtain ⟨-, hres, hnull⟩ :=
      subsystemComponentGenericSet_dense_residual_fullMeasure_of_dim A G h2 S
    exact ⟨hres, hnull⟩
  have hiInter : allSubsystemGenericSet A G =
      ⋂ S : Finset V, subsystemComponentGenericSet A G S := by
    ext p
    simp [allSubsystemGenericSet]
  have hres : allSubsystemGenericSet A G ∈
      residual (Fin (interactionCoordinateCount A G) → ℝ) := by
    rw [hiInter]
    exact countable_iInter_mem.2 fun S => (hpiece S).1
  refine ⟨dense_of_mem_residual hres, hres, ?_⟩
  rw [hiInter, Set.compl_iInter]
  exact measure_iUnion_null fun S => (hpiece S).2

theorem subsystemHamiltonian_isHermitian {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (p : Fin (interactionCoordinateCount A G) → ℝ) :
    (subsystemHamiltonian A G S p).IsHermitian :=
  isHermitian_liftLocalMatrix S (subsystemBlock_isHermitian A G S p)

/-- **Equation (5), unconditionally.**  At every parameter of the simultaneous
transversality set, the temporal rank read by every vertex subset is the sum,
over the connected components of the induced graph, of the component tensor
dimension minus one. -/
theorem anchoredTemporalRank_subsystemHamiltonian_of_generic
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : Fin (interactionCoordinateCount A G) → ℝ}
    (hp : p ∈ allSubsystemGenericSet A G) (S : Finset V) (r : ∀ v, A v) :
    anchoredTemporalRank
        (subsystemHamiltonian_isHermitian A G S p).eigenvalues r =
      ∑ c ∈ componentPackets G S,
        ((∏ v ∈ c, Fintype.card (A v)) - 1) :=
  anchoredTemporalRank_subsystemHamiltonian_components A G S p
    (componentProjectivelyIndependent_of_mem_subsystemComponentGenericSet
      A G S p (hp S))
    (subsystemHamiltonian_isHermitian A G S p) r

end

end GaloisForLFunctions.HTGeometry
