import GaloisForLFunctions.HTGeometry.HypergraphComponentFactorization
import GaloisForLFunctions.HTGeometry.SiteFactorSubsystemTransport

/-!
# Maximally projective blocks on the components of a hypergraph

A two-section component of a finite interaction hypergraph is a connected
network in its own right, so the spanning-tree witness supplies a Hermitian
one-site-plus-edge Hamiltonian on it whose spectrum has maximal projective
rational rank.  Every such term is supported on a single site or on a
two-section edge, and a two-section edge lies inside a hyperedge which lies
inside that component; so the lift of the whole component-local space is a
hyperedge-local Hamiltonian space of the component packet.

The resulting block space `blockLocalSubmodule` is the exact parameter space of
one component.  It contains the identity, so component spectra can be shifted
independently, and it carries a maximally projective witness.
-/

open Set SimpleGraph MeasureTheory Topology Filter
open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-! ### Component packets are connected nonempty networks -/

theorem hypergraphComponents_nonempty {𝔥 : Finset (Finset V)} {P : Finset V}
    (hP : P ∈ hypergraphComponents 𝔥) : P.Nonempty := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hP
  exact ⟨v.1, self_mem_sitePacketOf _ _ v⟩

theorem hypergraphComponentOf_eq_of_mem {𝔥 : Finset (Finset V)} {P : Finset V}
    (hP : P ∈ hypergraphComponents 𝔥) {w : V} (hw : w ∈ P) :
    hypergraphComponentOf 𝔥 w = P := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hP
  exact sitePacketOf_eq_of_mem (twoSection 𝔥) Finset.univ
    (v := v) (w := ⟨w, Finset.mem_univ w⟩) hw

theorem connected_comap_of_mem_hypergraphComponents {𝔥 : Finset (Finset V)}
    {P : Finset V} (hP : P ∈ hypergraphComponents 𝔥) :
    ((twoSection 𝔥).comap
      (Function.Embedding.subtype (fun x : V => x ∈ P))).Connected := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hP
  exact connected_induce_sitePacketOf (twoSection 𝔥) Finset.univ v

/-! ### Sub-packet support survives the packet lift -/

/-- **Support of a lifted block.**  An operator of the `P`-site network
supported on a sub-packet lifts to an ambient operator supported on the
corresponding ambient sites. -/
theorem isSiteSupported_liftLocalMatrix_of_isSiteSupported
    {P : Finset V} {T : Finset {v : V // v ∈ P}}
    {B : Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ}
    (hB : IsSiteSupported (A := fun w : {v : V // v ∈ P} => A w.1) T B) :
    IsSiteSupported (A := A) (subsystemPacketImage T) (liftLocalMatrix P B) := by
  have hQP : subsystemPacketImage T ⊆ P := subsystemPacketImage_subset T
  constructor
  · rintro x y ⟨w, hwQ, hne⟩
    by_cases hout : restrictOutsideConfiguration P x =
        restrictOutsideConfiguration P y
    · rw [liftLocalMatrix, if_pos hout]
      have hwP : w ∈ P := by
        by_contra hwP
        exact hne (congrFun hout ⟨w, hwP⟩)
      refine hB.1 _ _ ⟨⟨w, hwP⟩, ?_, hne⟩
      exact fun h => hwQ (mem_subsystemPacketImage_iff.2 h)
    · rw [liftLocalMatrix, if_neg hout]
  · intro x y x' y' h₁ h₂ h₃ h₄
    have hout : restrictOutsideConfiguration P x =
        restrictOutsideConfiguration P y := by
      funext u
      exact h₃ u.1 (fun h => u.2 (hQP h))
    have hout' : restrictOutsideConfiguration P x' =
        restrictOutsideConfiguration P y' := by
      funext u
      exact h₄ u.1 (fun h => u.2 (hQP h))
    rw [liftLocalMatrix, if_pos hout, liftLocalMatrix, if_pos hout']
    refine hB.2 _ _ _ _ ?_ ?_ ?_ ?_
    · exact fun u hu => h₁ u.1 (mem_subsystemPacketImage_iff.2 hu)
    · exact fun u hu => h₂ u.1 (mem_subsystemPacketImage_iff.2 hu)
    · exact fun u hu => h₃ u.1 (fun h => hu (mem_subsystemPacketImage_iff.1 h))
    · exact fun u hu => h₄ u.1 (fun h => hu (mem_subsystemPacketImage_iff.1 h))

/-- The packet lift is a real-linear map. -/
def liftLocalMatrixLinear (A : V → Type*) [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] (P : Finset V) :
    Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ →ₗ[ℝ]
      Matrix (∀ v, A v) (∀ v, A v) ℂ where
  toFun := liftLocalMatrix P
  map_add' := liftLocalMatrix_add P
  map_smul' := fun c B => liftLocalMatrix_smul P c B

@[simp] theorem liftLocalMatrixLinear_apply (P : Finset V)
    (B : Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ) :
    liftLocalMatrixLinear A P B = liftLocalMatrix P B := rfl

theorem liftLocalMatrix_one (P : Finset V) :
    liftLocalMatrix (A := A) (R := ℂ) P 1 = 1 := by
  ext x y
  by_cases hout : restrictOutsideConfiguration P x =
      restrictOutsideConfiguration P y
  · rw [liftLocalMatrix, if_pos hout, Matrix.one_apply, Matrix.one_apply]
    by_cases hloc : restrictLocalConfiguration P x =
        restrictLocalConfiguration P y
    · have hxy : x = y := by
        funext w
        by_cases hw : w ∈ P
        · exact congrFun hloc ⟨w, hw⟩
        · exact congrFun hout ⟨w, hw⟩
      rw [if_pos hloc, if_pos hxy]
    · rw [if_neg hloc, if_neg]
      intro hxy
      exact hloc (by rw [hxy])
  · rw [liftLocalMatrix, if_neg hout, Matrix.one_apply, if_neg]
    intro hxy
    exact hout (by rw [hxy])

/-! ### The block-local Hamiltonian space of a component -/

variable (A)

/-- Blocks on a component packet whose lift is a hyperedge-local Hamiltonian of
that component. -/
def blockLocalSubmodule (𝔥 : Finset (Finset V)) (P : Finset V) :
    Submodule ℝ (Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ) :=
  (componentLocalSubmodule A 𝔥 P).comap (liftLocalMatrixLinear A P)

variable {A}

theorem mem_blockLocalSubmodule_iff {𝔥 : Finset (Finset V)} {P : Finset V}
    {B : Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ} :
    B ∈ blockLocalSubmodule A 𝔥 P ↔
      liftLocalMatrix P B ∈ componentLocalSubmodule A 𝔥 P := Iff.rfl

theorem blockLocalSubmodule_le_selfAdjoint [∀ v, Nonempty (A v)]
    (𝔥 : Finset (Finset V)) (P : Finset V) :
    blockLocalSubmodule A 𝔥 P ≤
      selfAdjoint.submodule ℝ
        (Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ) := by
  intro B hB
  exact isHermitian_of_isHermitian_liftLocalMatrix P
    (isHermitian_of_mem_componentLocalSubmodule A
      (mem_blockLocalSubmodule_iff.1 hB))

theorem isHermitian_of_mem_blockLocalSubmodule [∀ v, Nonempty (A v)]
    {𝔥 : Finset (Finset V)} {P : Finset V}
    {B : Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ}
    (hB : B ∈ blockLocalSubmodule A 𝔥 P) : B.IsHermitian :=
  blockLocalSubmodule_le_selfAdjoint 𝔥 P hB

/-- **The identity is a block-local Hamiltonian.**  Component spectra can
therefore be shifted independently inside the admissible space. -/
theorem one_mem_blockLocalSubmodule {𝔥 : Finset (Finset V)} {P : Finset V}
    (hP : P.Nonempty) :
    (1 : Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ) ∈
      blockLocalSubmodule A 𝔥 P := by
  obtain ⟨v, hv⟩ := hP
  refine mem_blockLocalSubmodule_iff.2 (Submodule.subset_span ⟨?_, ?_⟩)
  · rw [liftLocalMatrix_one]
    exact Matrix.isHermitian_one
  · refine Or.inl ⟨v, hv, ?_⟩
    rw [liftLocalMatrix_one]
    exact (isSiteSupported_one (B := A)).mono (Finset.empty_subset _)

/-- **A component network sits inside its block space.**  Every one-site or
two-section-edge Hermitian term of a component packet lifts to a hyperedge-local
Hamiltonian of that component. -/
theorem siteFactorLocalSubmodule_le_blockLocalSubmodule
    {𝔥 : Finset (Finset V)} {P : Finset V}
    (hP : P ∈ hypergraphComponents 𝔥) :
    siteFactorLocalSubmodule (fun w : {v : V // v ∈ P} => A w.1)
        ((twoSection 𝔥).comap
          (Function.Embedding.subtype (fun v : V => v ∈ P))) ≤
      blockLocalSubmodule A 𝔥 P := by
  refine Submodule.span_le.2 ?_
  rintro K ⟨hK, hcase⟩
  refine mem_blockLocalSubmodule_iff.2 (Submodule.subset_span
    ⟨isHermitian_liftLocalMatrix P hK, ?_⟩)
  rcases hcase with ⟨w, hsupp⟩ | ⟨w, w', hadj, hsupp⟩
  · refine Or.inl ⟨w.1, w.2, ?_⟩
    have := isSiteSupported_liftLocalMatrix_of_isSiteSupported hsupp
    rwa [subsystemPacketImage_singleton] at this
  · obtain ⟨-, X, hX, hw, hw'⟩ :=
      twoSection_adj_iff.1 (show (twoSection 𝔥).Adj w.1 w'.1 from hadj)
    have hXP : X ⊆ P := by
      have := hyperedge_subset_hypergraphComponentOf hX hw
      rwa [hypergraphComponentOf_eq_of_mem hP w.2] at this
    refine Or.inr ⟨X, hX, hXP, ?_⟩
    have hlift := isSiteSupported_liftLocalMatrix_of_isSiteSupported hsupp
    rw [subsystemPacketImage_pair] at hlift
    refine hlift.mono ?_
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hw
    · exact hw'

/-- **Component witness.**  Every two-section component of a finite interaction
hypergraph with local dimensions at least two carries a Hermitian block-local
Hamiltonian whose spectrum has maximal projective rational rank. -/
theorem exists_maximallyProjective_mem_blockLocalSubmodule
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (hA : ∀ v, 2 ≤ Fintype.card (A v))
    (𝔥 : Finset (Finset V)) {P : Finset V}
    (hP : P ∈ hypergraphComponents 𝔥) :
    ∃ K : Matrix (LocalConfiguration A P) (LocalConfiguration A P) ℂ,
      ∃ hK : K.IsHermitian,
        K ∈ blockLocalSubmodule A 𝔥 P ∧
          MaximallyProjectiveEnergy hK.eigenvalues := by
  classical
  obtain ⟨v, hv⟩ := hypergraphComponents_nonempty hP
  letI : Nonempty {x : V // x ∈ P} := ⟨⟨v, hv⟩⟩
  letI : DecidableRel ((twoSection 𝔥).comap
    (Function.Embedding.subtype (fun x : V => x ∈ P))).Adj := Classical.decRel _
  obtain ⟨K, hK, hmem, hmax⟩ :=
    exists_maximallyProjective_mem_siteFactorLocalSubmodule
      ((twoSection 𝔥).comap
        (Function.Embedding.subtype (fun x : V => x ∈ P)))
      (connected_comap_of_mem_hypergraphComponents hP)
      (fun w : {x : V // x ∈ P} => A w.1) (fun w => hA w.1)
  exact ⟨K, hK, siteFactorLocalSubmodule_le_blockLocalSubmodule hP hmem, hmax⟩

end

end GaloisForLFunctions.HTGeometry
