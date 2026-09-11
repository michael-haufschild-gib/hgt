import GaloisForLFunctions.HTGeometry.DifferentialVariationalRelativeGrowth

/-!
# Integral lattices inside an invariant subspace

The degree of a `σ`-stable subspace is the signed length of the layer between an integral lattice of
that subspace and its image.  This leaf builds the lattices and the commensurability that make that
length finite, without leaving the ambient coordinate space.

* `subspaceTraceLattice L W = L.carrier ⊓ W` is finitely generated (a submodule of a finitely
  generated module over the left Noetherian valuation ring) and spans `W` over the completed skew
  field, because every vector is pushed into the base lattice by some uniformizer power
  (`DiffOp.exists_uniformizer_smul_mem_lattice`).
* `DiffOp.exists_uniformizer_smul_mem_of_mem_span` — a vector in the skew-field span of an integral
  submodule is pushed into it by one uniformizer power.  The proof is a span induction; the scalar
  step is the regrouping `π^m a = (π^d · π^z a' π^{-z}) · π^z` together with invariance of the
  valuation ring under conjugation by uniformizer powers.
* `DiffOp.exists_uniformizer_smul_le` — **commensurability**: a finitely generated integral submodule
  inside the span of another is carried into it by a *single* uniformizer power, obtained as the
  supremum of the finitely many powers that work on generators.

Together these say that any two finitely generated integral submodules with the same skew-field span
are commensurable, which is what makes the relative length of the pair finite and the degree
well-defined.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

omit [Algebra C K] [IsConstantBase C K] in
/-- Every vector is pushed into a lattice by some uniformizer power. -/
theorem DiffOp.exists_uniformizer_smul_mem_lattice {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    ∃ k : ℕ, ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈ L.carrier := by
  obtain ⟨k, hk⟩ := DiffOp.exists_nat_carrier_le_leftScale_uniformizer L
    (DiffOp.adjoinVectorLattice L v)
  refine ⟨k, ?_⟩
  have hv := hk (DiffOp.mem_adjoinVectorLattice L v)
  obtain ⟨x, hx, hxv⟩ :=
    (DiffOp.mem_leftScaleCompletedPseudoDiffOpLattice_iff _ _ _).1 hv
  have hxv' : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(k : ℤ)) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • x = v := hxv
  have : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v = x := by
    rw [← hxv', smul_smul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, one_smul]
  rw [this]
  exact hx

set_option synthInstance.maxHeartbeats 1000000 in
/-- Trace of the base lattice on a subspace. -/
def subspaceTraceLattice {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  L.carrier ⊓ W.restrictScalars (DiffOp.CompletedPseudoDiffOpInteger (K := K))

theorem subspaceTraceLattice_le {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    subspaceTraceLattice L W ≤ L.carrier := inf_le_left

theorem subspaceTraceLattice_le_subspace {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K} (hv : v ∈ subspaceTraceLattice L W) :
    v ∈ W := hv.2

theorem subspaceTraceLattice_fg {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    (subspaceTraceLattice L W).FG :=
  L.fg.of_le (subspaceTraceLattice_le L W)

/-- The trace lattice spans its subspace over the completed skew field. -/
theorem span_subspaceTraceLattice {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    Submodule.span (DiffOp.CompletedPseudoDiffOp K)
      (subspaceTraceLattice L W : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro v hv
    exact subspaceTraceLattice_le_subspace L W hv
  · intro v hv
    obtain ⟨k, hk⟩ := DiffOp.exists_uniformizer_smul_mem_lattice L v
    have hmem : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈
        subspaceTraceLattice L W := ⟨hk, W.smul_mem _ hv⟩
    have hspan : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈
        Submodule.span (DiffOp.CompletedPseudoDiffOp K)
          (subspaceTraceLattice L W : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) :=
      Submodule.subset_span hmem
    have hback := Submodule.smul_mem _
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(k : ℤ)) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) hspan
    rwa [smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
      one_smul] at hback


set_option synthInstance.maxHeartbeats 400000 in
omit [Algebra C K] [IsConstantBase C K] in
/-- Every vector of the skew-field span of an integral submodule is pushed into it by some
uniformizer power. -/
theorem DiffOp.exists_uniformizer_smul_mem_of_mem_span {r : ℕ}
    (M : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K))
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ Submodule.span (DiffOp.CompletedPseudoDiffOp K)
      (M : Set (Fin r → DiffOp.CompletedPseudoDiffOp K))) :
    ∃ k : ℕ, ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      refine ⟨0, ?_⟩
      rw [Nat.cast_zero, zpow_zero, Units.val_one, one_smul]
      exact hx
  | zero =>
      refine ⟨0, ?_⟩
      rw [smul_zero]
      exact M.zero_mem
  | add x y _ _ ihx ihy =>
      obtain ⟨kx, hkx⟩ := ihx
      obtain ⟨ky, hky⟩ := ihy
      have hraise : ∀ (y' : Fin r → DiffOp.CompletedPseudoDiffOp K) (e : ℕ), e ≤ max kx ky →
          ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (e : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • y' ∈ M →
          ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((max kx ky : ℕ) : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • y' ∈ M := by
        intro y' e he hy'
        have hfac : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
              ((max kx ky : ℕ) : ℤ) : (DiffOp.CompletedPseudoDiffOp K)ˣ) :
              DiffOp.CompletedPseudoDiffOp K) • y' =
            ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((max kx ky - e : ℕ) : ℤ) :
              (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
              (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (e : ℤ) :
                (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • y') := by
          rw [smul_smul, ← Units.val_mul, ← zpow_add]
          congr 3
          omega
        rw [hfac]
        exact M.smul_mem ⟨_, DiffOp.uniformizer_natPow_mem_integer (K := K) (max kx ky - e)⟩ hy'
      refine ⟨max kx ky, ?_⟩
      rw [smul_add]
      exact M.add_mem (hraise x kx (le_max_left _ _) hkx) (hraise y ky (le_max_right _ _) hky)
  | smul a x _ ihx =>
      obtain ⟨z, hz⟩ := ihx
      obtain ⟨t, ht⟩ := DiffOp.exists_uniformizer_left_scale_mem_integer a
      refine ⟨((z : ℤ) + t).toNat, ?_⟩
      set d : ℕ := (((((z : ℤ) + t).toNat : ℕ) : ℤ) - ((z : ℤ) + t)).toNat with hd
      have hsum : (d : ℤ) + ((z : ℤ) + t) = ((((z : ℤ) + t).toNat : ℕ) : ℤ) := by
        simp only [hd]
        omega
      rw [smul_smul, DiffOp.uniformizer_shift_factorization (K := K) z d t _ a hsum,
        ← smul_smul]
      refine M.smul_mem ⟨_, ?_⟩ hz
      exact mul_mem (DiffOp.uniformizer_natPow_mem_integer (K := K) d)
        (DiffOp.uniformizer_conj_mem_integer (K := K) (z : ℤ) ht)

set_option synthInstance.maxHeartbeats 400000 in
omit [Algebra C K] [IsConstantBase C K] in
/-- **Commensurability of integral submodules with the same span.**  A finitely generated integral
submodule is carried into any integral submodule with the same skew-field span by one uniformizer
power. -/
theorem DiffOp.exists_uniformizer_smul_le {r : ℕ}
    (M N : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) (hN : N.FG)
    (hspan : (N : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆
      Submodule.span (DiffOp.CompletedPseudoDiffOp K)
        (M : Set (Fin r → DiffOp.CompletedPseudoDiffOp K))) :
    ∃ k : ℕ, ∀ v ∈ N,
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈ M := by
  classical
  obtain ⟨s, hs⟩ := hN
  have hgen : ∀ x ∈ s, ∃ k : ℕ,
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • x ∈ M := by
    intro x hx
    refine DiffOp.exists_uniformizer_smul_mem_of_mem_span M (hspan ?_)
    rw [← hs]
    exact Submodule.subset_span hx
  choose kf hkf using hgen
  set k : ℕ := s.attach.sup (fun x => kf x.1 x.2) with hk
  refine ⟨k, ?_⟩
  have hsub : ∀ x ∈ s,
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • x ∈ M := by
    intro x hx
    have hle : kf x hx ≤ k := by
      rw [hk]
      exact Finset.le_sup (f := fun y : {y // y ∈ s} => kf y.1 y.2) (Finset.mem_attach _ ⟨x, hx⟩)
    have hfac : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • x =
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((k - kf x hx : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
          (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((kf x hx : ℕ) : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • x) := by
      rw [smul_smul, ← Units.val_mul, ← zpow_add]
      congr 3
      omega
    rw [hfac]
    exact M.smul_mem ⟨_, DiffOp.uniformizer_natPow_mem_integer (K := K) (k - kf x hx)⟩ (hkf x hx)
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hsub x hx
  | zero => rw [smul_zero]; exact M.zero_mem
  | add x y _ _ ihx ihy => rw [smul_add]; exact M.add_mem ihx ihy
  | smul c x _ ihx =>
      have hcoe : (c : DiffOp.CompletedPseudoDiffOp K) • x = c • x := rfl
      have hscal : ((((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
              (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
            (c : DiffOp.CompletedPseudoDiffOp K)) *
            ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(k : ℤ)) :
              (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K)) *
          ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) =
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
          (c : DiffOp.CompletedPseudoDiffOp K) := by
        rw [mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
          mul_one]
      rw [← hcoe, smul_smul, ← hscal, ← smul_smul]
      exact M.smul_mem ⟨_, DiffOp.uniformizer_conj_mem_integer (K := K) (k : ℤ) c.2⟩ ihx

end

end GaloisForLFunctions.HTGeometry
