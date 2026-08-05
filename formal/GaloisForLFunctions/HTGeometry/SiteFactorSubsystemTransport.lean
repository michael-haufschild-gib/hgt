import GaloisForLFunctions.HTGeometry.SiteFactorInteractionCoordinates
import GaloisForLFunctions.HTGeometry.SiteFactorGraphWitness

/-!
# Reading a subsystem as a network in its own right

The configurations of a site packet `S` are literally the site product of the
factors indexed by `S`, so a vertex subset carries its own network structure.
This file identifies the two descriptions of an operator supported on a
sub-packet `T ⊆ S`:

* seen inside `S` it is `liftLocalMatrixToSuperset`;
* seen as an operator of the `S`-site network it is site-supported on the
  corresponding packet of `S`.

The consequence is that the whole local Hamiltonian space of the induced
network sits inside the span of the ambient interaction coordinates read within
`S`, which is what supplies the per-subsystem witness of the atlas.
-/

open scoped Matrix Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-! ### Packets of a subsystem -/

/-- Ambient sites of a packet of the subsystem `S`. -/
def subsystemPacketImage {S : Finset V} (T : Finset {v : V // v ∈ S}) :
    Finset V :=
  T.image Subtype.val

omit [Fintype V] in
theorem subsystemPacketImage_subset {S : Finset V}
    (T : Finset {v : V // v ∈ S}) : subsystemPacketImage T ⊆ S := by
  intro w hw
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hw
  exact u.2

omit [Fintype V] in
theorem mem_subsystemPacketImage_iff {S : Finset V}
    {T : Finset {v : V // v ∈ S}} {w : {v : V // v ∈ S}} :
    w.1 ∈ subsystemPacketImage T ↔ w ∈ T := by
  simp [subsystemPacketImage, Subtype.val_injective.eq_iff]

omit [Fintype V] in
theorem subsystemPacketImage_singleton {S : Finset V}
    (w : {v : V // v ∈ S}) :
    subsystemPacketImage ({w} : Finset {v : V // v ∈ S}) = {w.1} := by
  simp [subsystemPacketImage]

omit [Fintype V] in
theorem subsystemPacketImage_pair {S : Finset V}
    (w w' : {v : V // v ∈ S}) :
    subsystemPacketImage ({w, w'} : Finset {v : V // v ∈ S}) =
      {w.1, w'.1} := by
  simp [subsystemPacketImage]

/-! ### Gluing a sub-packet configuration into the subsystem -/

/-- Glue a `T`-configuration into a fixed `S`-configuration. -/
def glueSupersetConfiguration {T S : Finset V} (_hTS : T ⊆ S)
    (a : LocalConfiguration A T) (z : LocalConfiguration A S) :
    LocalConfiguration A S :=
  fun w => if h : w.1 ∈ T then a ⟨w.1, h⟩ else z w

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem glueSupersetConfiguration_mem {T S : Finset V} (hTS : T ⊆ S)
    (a : LocalConfiguration A T) (z : LocalConfiguration A S)
    {w : {v : V // v ∈ S}} (hw : w.1 ∈ T) :
    glueSupersetConfiguration hTS a z w = a ⟨w.1, hw⟩ := by
  simp [glueSupersetConfiguration, hw]

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem glueSupersetConfiguration_notMem {T S : Finset V} (hTS : T ⊆ S)
    (a : LocalConfiguration A T) (z : LocalConfiguration A S)
    {w : {v : V // v ∈ S}} (hw : w.1 ∉ T) :
    glueSupersetConfiguration hTS a z w = z w := by
  simp [glueSupersetConfiguration, hw]

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem restrictSupersetConfiguration_glue {T S : Finset V} (hTS : T ⊆ S)
    (a : LocalConfiguration A T) (z : LocalConfiguration A S) :
    restrictSupersetConfiguration hTS
      (glueSupersetConfiguration hTS a z) = a := by
  funext v
  show glueSupersetConfiguration hTS a z ⟨v.1, hTS v.2⟩ = a v
  rw [glueSupersetConfiguration_mem hTS a z (w := ⟨v.1, hTS v.2⟩) v.2]

/-- Lifting a sub-packet block into a subsystem packet is injective. -/
theorem liftLocalMatrixToSuperset_injective [∀ v, Nonempty (A v)]
    {T S : Finset V} (hTS : T ⊆ S) :
    Function.Injective
      (liftLocalMatrixToSuperset (A := A) (R := ℂ) hTS) := by
  classical
  intro M M' hMM'
  ext a b
  let z : LocalConfiguration A S := fun w => Classical.arbitrary (A w.1)
  have hrel :
      restrictRelativeOutsideConfiguration T S
          (glueSupersetConfiguration hTS a z) =
        restrictRelativeOutsideConfiguration T S
          (glueSupersetConfiguration hTS b z) := by
    funext v
    show glueSupersetConfiguration hTS a z v.1 =
      glueSupersetConfiguration hTS b z v.1
    rw [glueSupersetConfiguration_notMem hTS a z v.2,
      glueSupersetConfiguration_notMem hTS b z v.2]
  have hval := congrFun (congrFun hMM' (glueSupersetConfiguration hTS a z))
    (glueSupersetConfiguration hTS b z)
  rw [liftLocalMatrixToSuperset, liftLocalMatrixToSuperset, if_pos hrel,
    if_pos hrel, restrictSupersetConfiguration_glue,
    restrictSupersetConfiguration_glue] at hval
  exact hval

theorem isHermitian_of_isHermitian_liftLocalMatrixToSuperset
    [∀ v, Nonempty (A v)] {T S : Finset V} (hTS : T ⊆ S)
    {M : Matrix (LocalConfiguration A T) (LocalConfiguration A T) ℂ}
    (hM : (liftLocalMatrixToSuperset hTS M).IsHermitian) : M.IsHermitian := by
  refine liftLocalMatrixToSuperset_injective hTS ?_
  rw [← conjTranspose_liftLocalMatrixToSuperset]
  exact hM

/-! ### Subsystem site support is a sub-packet lift -/

/-- **Support inside a subsystem is a sub-packet lift.**  An operator of the
`S`-site network supported on a packet is the lift of an explicit block on the
corresponding ambient sub-packet. -/
theorem exists_liftLocalMatrixToSuperset_of_isSiteSupported
    [∀ v, Nonempty (A v)] {S : Finset V} {T : Finset {v : V // v ∈ S}}
    {H : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ}
    (hH : IsSiteSupported (A := fun w : {v : V // v ∈ S} => A w.1) T H) :
    ∃ M : Matrix (LocalConfiguration A (subsystemPacketImage T))
        (LocalConfiguration A (subsystemPacketImage T)) ℂ,
      H = liftLocalMatrixToSuperset (subsystemPacketImage_subset T) M := by
  classical
  set P := subsystemPacketImage T with hP
  set hPS := subsystemPacketImage_subset T with hPSdef
  let z : LocalConfiguration A S := fun w => Classical.arbitrary (A w.1)
  refine ⟨fun a b => H (glueSupersetConfiguration hPS a z)
    (glueSupersetConfiguration hPS b z), ?_⟩
  ext x y
  by_cases hrel : restrictRelativeOutsideConfiguration P S x =
      restrictRelativeOutsideConfiguration P S y
  · have hout : ∀ w : {v : V // v ∈ S}, w ∉ T → x w = y w := by
      intro w hw
      have hwP : w.1 ∉ P := fun h => hw (mem_subsystemPacketImage_iff.1 h)
      exact congrFun hrel ⟨w, hwP⟩
    have hglueOut : ∀ w : {v : V // v ∈ S}, w ∉ T →
        glueSupersetConfiguration hPS (restrictSupersetConfiguration hPS x) z w =
          glueSupersetConfiguration hPS
            (restrictSupersetConfiguration hPS y) z w := by
      intro w hw
      have hwP : w.1 ∉ P := fun h => hw (mem_subsystemPacketImage_iff.1 h)
      rw [glueSupersetConfiguration_notMem hPS _ z hwP,
        glueSupersetConfiguration_notMem hPS _ z hwP]
    have hglueIn : ∀ w : {v : V // v ∈ S}, w ∈ T →
        x w = glueSupersetConfiguration hPS
          (restrictSupersetConfiguration hPS x) z w := by
      intro w hw
      have hwP : w.1 ∈ P := mem_subsystemPacketImage_iff.2 hw
      rw [glueSupersetConfiguration_mem hPS _ z hwP]
      rfl
    have hglueIn' : ∀ w : {v : V // v ∈ S}, w ∈ T →
        y w = glueSupersetConfiguration hPS
          (restrictSupersetConfiguration hPS y) z w := by
      intro w hw
      have hwP : w.1 ∈ P := mem_subsystemPacketImage_iff.2 hw
      rw [glueSupersetConfiguration_mem hPS _ z hwP]
      rfl
    rw [liftLocalMatrixToSuperset, if_pos hrel]
    exact hH.2 x y _ _ hglueIn hglueIn' hout hglueOut
  · have hne : ∃ w : {v : V // v ∈ S}, w ∉ T ∧ x w ≠ y w := by
      by_contra hcon
      push Not at hcon
      refine hrel (funext fun v => ?_)
      exact hcon v.1 (fun h => v.2 (mem_subsystemPacketImage_iff.2 h))
    rw [liftLocalMatrixToSuperset, if_neg hrel]
    exact hH.1 x y hne

/-! ### The induced network sits in the restricted coordinates -/

theorem liftLocalMatrixToSuperset_zero {T S : Finset V} (hTS : T ⊆ S) :
    liftLocalMatrixToSuperset (A := A) (R := ℂ) hTS 0 = 0 := by
  ext x y
  simp [liftLocalMatrixToSuperset]

theorem liftLocalMatrixToSuperset_add {T S : Finset V} (hTS : T ⊆ S)
    (M M' : Matrix (LocalConfiguration A T) (LocalConfiguration A T) ℂ) :
    liftLocalMatrixToSuperset hTS (M + M') =
      liftLocalMatrixToSuperset hTS M + liftLocalMatrixToSuperset hTS M' := by
  ext x y
  by_cases h : restrictRelativeOutsideConfiguration T S x =
      restrictRelativeOutsideConfiguration T S y <;>
    simp [liftLocalMatrixToSuperset, h]

theorem liftLocalMatrixToSuperset_smul {T S : Finset V} (hTS : T ⊆ S) (c : ℝ)
    (M : Matrix (LocalConfiguration A T) (LocalConfiguration A T) ℂ) :
    liftLocalMatrixToSuperset hTS (c • M) =
      c • liftLocalMatrixToSuperset hTS M := by
  ext x y
  by_cases h : restrictRelativeOutsideConfiguration T S x =
      restrictRelativeOutsideConfiguration T S y <;>
    simp [liftLocalMatrixToSuperset, h]

/-- A sub-packet lift of a spanned block lies in the span of the restricted
interaction coordinates. -/
theorem liftLocalMatrixToSuperset_mem_span_restrictedGeneratorFin
    (G : SimpleGraph V) [DecidableRel G.Adj] (S P : Finset V)
    (hP : P ∈ interactionPackets G) (hPS : P ⊆ S)
    {M : Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ}
    (hM : M ∈ Submodule.span ℝ (Set.range (packetHermitianGenerator A P))) :
    liftLocalMatrixToSuperset hPS M ∈
      Submodule.span ℝ (Set.range (restrictedGeneratorFin A G S)) := by
  induction hM using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨i, rfl⟩ := hX
      refine Submodule.subset_span
        ⟨interactionCoordinateEquiv A G ⟨⟨P, hP⟩, i⟩, ?_⟩
      show restrictedInteractionGenerator A G S
        ((interactionCoordinateEquiv A G).symm
          (interactionCoordinateEquiv A G ⟨⟨P, hP⟩, i⟩)) = _
      rw [Equiv.symm_apply_apply]
      show (if h : P ⊆ S then
          liftLocalMatrixToSuperset h (packetHermitianGenerator A P i)
        else 0) = _
      rw [dif_pos hPS]
  | zero =>
      rw [liftLocalMatrixToSuperset_zero]
      exact Submodule.zero_mem _
  | add X Y _ _ hX hY =>
      rw [liftLocalMatrixToSuperset_add]
      exact Submodule.add_mem _ hX hY
  | smul c X _ hX =>
      rw [liftLocalMatrixToSuperset_smul]
      exact Submodule.smul_mem _ c hX

/-- A Hermitian operator of the `S`-site network supported on an admissible
packet lies in the span of the restricted interaction coordinates. -/
theorem mem_span_restrictedGeneratorFin_of_isSiteSupported
    [∀ v, Nonempty (A v)] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {T : Finset {v : V // v ∈ S}}
    (hP : subsystemPacketImage T ∈ interactionPackets G)
    {H : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ}
    (hHerm : H.IsHermitian)
    (hsupp : IsSiteSupported (A := fun w : {v : V // v ∈ S} => A w.1) T H) :
    H ∈ Submodule.span ℝ (Set.range (restrictedGeneratorFin A G S)) := by
  obtain ⟨M, hM⟩ := exists_liftLocalMatrixToSuperset_of_isSiteSupported hsupp
  have hMherm : M.IsHermitian := by
    refine isHermitian_of_isHermitian_liftLocalMatrixToSuperset
      (subsystemPacketImage_subset T) ?_
    rw [← hM]
    exact hHerm
  rw [hM]
  exact liftLocalMatrixToSuperset_mem_span_restrictedGeneratorFin G S _ hP
    (subsystemPacketImage_subset T)
    (mem_span_packetHermitianGenerator A _ hMherm)

/-- **The induced network lives in the restricted coordinates.**  The whole
local Hamiltonian space of the network induced on a vertex subset is contained
in the span of the ambient interaction coordinates read inside that subset. -/
theorem siteFactorLocalSubmodule_induced_le_span_restrictedGeneratorFin
    [∀ v, Nonempty (A v)] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    siteFactorLocalSubmodule (fun w : {v : V // v ∈ S} => A w.1)
        (G.comap (Function.Embedding.subtype (fun v : V => v ∈ S))) ≤
      Submodule.span ℝ (Set.range (restrictedGeneratorFin A G S)) := by
  refine Submodule.span_le.2 ?_
  rintro H ⟨hHerm, hcase⟩
  rcases hcase with ⟨w, hsupp⟩ | ⟨w, w', hadj, hsupp⟩
  · refine mem_span_restrictedGeneratorFin_of_isSiteSupported G S ?_ hHerm hsupp
    rw [subsystemPacketImage_singleton]
    exact singleton_mem_interactionPackets w.1
  · refine mem_span_restrictedGeneratorFin_of_isSiteSupported G S ?_ hHerm hsupp
    rw [subsystemPacketImage_pair]
    exact pair_mem_interactionPackets hadj

/-- **Subsystem witness transfer.**  A maximally projective local Hamiltonian of
the induced network supplies a witness parameter for the ambient interaction
coordinates. -/
theorem exists_witness_subsystemMaximalSet [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {H : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ}
    (hHerm : H.IsHermitian)
    (hmem : H ∈ siteFactorLocalSubmodule (fun w : {v : V // v ∈ S} => A w.1)
      (G.comap (Function.Embedding.subtype (fun v : V => v ∈ S))))
    (hmax : MaximallyProjectiveEnergy hHerm.eigenvalues) :
    ∃ p₀ : Fin (interactionCoordinateCount A G) → ℝ,
      MaximallyProjectiveEnergy
        (realAffineMatrix_isHermitian 0 (restrictedGeneratorFin A G S)
          Matrix.isHermitian_zero
          (restrictedGeneratorFin_isHermitian A G S) p₀).eigenvalues := by
  obtain ⟨p₀, hp₀⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).1
      (siteFactorLocalSubmodule_induced_le_span_restrictedGeneratorFin G S hmem)
  refine ⟨p₀, ?_⟩
  have heq : realAffineMatrix 0 (restrictedGeneratorFin A G S) p₀ = H := by
    rw [realAffineMatrix_zero_base]
    exact hp₀
  have heigen :
      (realAffineMatrix_isHermitian 0 (restrictedGeneratorFin A G S)
        Matrix.isHermitian_zero
        (restrictedGeneratorFin_isHermitian A G S) p₀).eigenvalues =
      hHerm.eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ hHerm).2
    rw [heq]
  rw [heigen]
  exact hmax

/-- **Every connected induced subsystem has a witness.**  If the network induced
on a nonempty vertex subset is connected and its local dimensions are at least
two, that subsystem is maximally projective at some ambient interaction
parameter. -/
theorem exists_witness_subsystemMaximalSet_of_connected
    {V : Type} [Fintype V] [DecidableEq V]
    {A : V → Type} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hS : S.Nonempty)
    (hconn : (G.comap
      (Function.Embedding.subtype (fun v : V => v ∈ S))).Connected)
    (h2 : ∀ w : {v : V // v ∈ S}, 2 ≤ Fintype.card (A w.1)) :
    ∃ p₀ : Fin (interactionCoordinateCount A G) → ℝ,
      MaximallyProjectiveEnergy
        (realAffineMatrix_isHermitian 0 (restrictedGeneratorFin A G S)
          Matrix.isHermitian_zero
          (restrictedGeneratorFin_isHermitian A G S) p₀).eigenvalues := by
  classical
  obtain ⟨v₀, hv₀⟩ := hS
  letI : Nonempty {v : V // v ∈ S} := ⟨⟨v₀, hv₀⟩⟩
  letI : DecidableRel (G.comap
    (Function.Embedding.subtype (fun v : V => v ∈ S))).Adj := Classical.decRel _
  obtain ⟨H, hHerm, hmem, hmax⟩ :=
    exists_maximallyProjective_mem_siteFactorLocalSubmodule
      (G.comap (Function.Embedding.subtype (fun v : V => v ∈ S))) hconn
      (fun w : {v : V // v ∈ S} => A w.1) h2
  exact exists_witness_subsystemMaximalSet G S hHerm hmem hmax

/-- **Simultaneous connected-subsystem atlas.**  For a finite interaction
network whose local dimensions are all at least two, the ambient interaction
parameters at which *every* supplied connected induced subsystem is
simultaneously maximally projective form a dense, residual, full-Lebesgue-measure
set.  No relation between the supplied subsystems is assumed, and their number
may be countably infinite. -/
theorem simultaneousConnectedSubsystemMaximalSet_dense_residual_fullMeasure
    {V : Type} [Fintype V] [DecidableEq V]
    {A : V → Type} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h2 : ∀ v, 2 ≤ Fintype.card (A v))
    {ι : Type*} [Countable ι] (S : ι → Finset V)
    (hS : ∀ a, (S a).Nonempty)
    (hconn : ∀ a, (G.comap
      (Function.Embedding.subtype (fun v : V => v ∈ S a))).Connected) :
    Dense (simultaneousSubsystemMaximalSet A G S) ∧
      simultaneousSubsystemMaximalSet A G S ∈
        residual (Fin (interactionCoordinateCount A G) → ℝ) ∧
      MeasureTheory.volume (simultaneousSubsystemMaximalSet A G S)ᶜ = 0 := by
  choose p₀ hp₀ using fun a =>
    exists_witness_subsystemMaximalSet_of_connected G (S a) (hS a) (hconn a)
      (fun w => h2 w.1)
  exact simultaneousSubsystemMaximalSet_dense_residual_fullMeasure A G S p₀ hp₀

end

end GaloisForLFunctions.HTGeometry
