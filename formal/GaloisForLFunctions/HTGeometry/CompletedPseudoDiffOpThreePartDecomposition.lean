import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpBoundedSplitting

/-!
# The expanding, neutral and contracting parts of a semilinear automorphism

For a uniformizer-semilinear automorphism `T` of a finite-dimensional completed skew vector space
`E`, write `B(T)` for the forward-bounded subspace and `C(T)` for the backward-contracting subspace.
This leaf proves the canonical three-part decomposition

```text
E = C(T) ⊕ (B(T) ⊓ B(T⁻¹)) ⊕ C(T⁻¹)
```

together with the lattice data that make each piece quantitative:

* `DiffOp.isCompl_forwardBoundedSubspace_backwardContractingSubspace` — `E = B(T) ⊕ C(T)`.  The sum is
  the splitting theorem; the intersection vanishes because a vector with bounded forward orbit and
  backward orbit tending to zero lies, by `T`-stability of a lattice of `B(T)`, in every dilation of
  that lattice.
* `DiffOp.forwardBoundedSubspace_eq_neutral_sup` — `B(T) = (B(T) ⊓ B(T⁻¹)) ⊕ C(T⁻¹)`, by the modular law.
* `DiffOp.exists_invariant_lattice_neutral` — the neutral part `B(T) ⊓ B(T⁻¹)` carries a lattice `N`
  with `T N = N`: the vectors whose whole two-sided orbit stays in one finitely generated submodule.
* `DiffOp.exists_contracting_lattice_backwardContractingSubspace` — `T⁻¹` contracts a lattice of `C(T)`
  uniformly, because `C(T)` has no nonzero forward-bounded vector.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]

variable {T : E ≃ₗ[ℤ] E} (hT : IsUniformizerSemilinear (K := K) T)

/-- Dilation commutes with intersecting with a subspace. -/
theorem uniformizerDilate_inf_restrictScalars (k : ℤ)
    (A : Submodule (CompletedPseudoDiffOpInteger (K := K)) E)
    (W : Submodule (CompletedPseudoDiffOp K) E) :
    uniformizerDilate k (A ⊓ W.restrictScalars (CompletedPseudoDiffOpInteger (K := K))) =
      uniformizerDilate k A ⊓ W.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
  ext y
  simp only [Submodule.mem_inf, mem_uniformizerDilate, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := W.smul_mem (uniformizerZPow (K := K) k) h2
    rwa [smul_smul, uniformizerZPow_mul_neg, one_smul] at this
  · rintro ⟨h1, h2⟩
    exact ⟨h1, W.smul_mem _ h2⟩

/-- A lattice with `T N ⊆ N` has all its dilations stable under the powers of `T`. -/
theorem pow_apply_mem_uniformizerDilate_of_stable
    {N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} (hTN : semilinearImage T hT N ≤ N)
    (n : ℕ) (j : ℤ) {x : E} (hx : x ∈ uniformizerDilate j N) :
    (T ^ n) x ∈ uniformizerDilate j N := by
  induction n generalizing x with
  | zero => rwa [pow_zero, LinearEquiv.coe_one, id]
  | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply]
      have h := apply_mem_semilinearImage (hT := hT) (ih hx)
      rw [semilinearImage_uniformizerDilate] at h
      exact uniformizerDilate_mono hTN h

theorem forwardBoundedSubspace_congr {S S' : E ≃ₗ[ℤ] E} (h : S = S')
    (hS : IsUniformizerSemilinear (K := K) S) (hS' : IsUniformizerSemilinear (K := K) S') :
    forwardBoundedSubspace S hS = forwardBoundedSubspace S' hS' := by
  subst h
  rfl

theorem backwardContractingSubspace_congr {S S' : E ≃ₗ[ℤ] E} (h : S = S')
    (hS : IsUniformizerSemilinear (K := K) S) (hS' : IsUniformizerSemilinear (K := K) S') :
    backwardContractingSubspace S hS = backwardContractingSubspace S' hS' := by
  subst h
  rfl

theorem apply_mem_backwardContractingSubspace {x : E}
    (hx : x ∈ backwardContractingSubspace T hT) : T x ∈ backwardContractingSubspace T hT := by
  obtain ⟨M, hM, hMx⟩ := mem_backwardContractingSubspace.1 hx
  refine mem_backwardContractingSubspace.2 ⟨semilinearImage T hT M, semilinearImage_fg hM,
    fun k => ?_⟩
  filter_upwards [hMx k] with n hn
  have hcomm : (T⁻¹ ^ n) (T x) = T ((T⁻¹ ^ n) x) := by
    have hc : T⁻¹ ^ n * T = T * T⁻¹ ^ n := ((Commute.refl T).inv_left.pow_left n).eq
    rw [← LinearEquiv.mul_apply, hc, LinearEquiv.mul_apply]
  rw [hcomm, ← semilinearImage_uniformizerDilate]
  exact apply_mem_semilinearImage hn

theorem inv_apply_mem_backwardContractingSubspace {x : E}
    (hx : x ∈ backwardContractingSubspace T hT) : T⁻¹ x ∈ backwardContractingSubspace T hT := by
  obtain ⟨M, hM, hMx⟩ := mem_backwardContractingSubspace.1 hx
  refine mem_backwardContractingSubspace.2 ⟨M, hM, fun k => ?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (hMx k)] with n hn
  rwa [pow_succ, LinearEquiv.mul_apply] at hn

variable [FiniteDimensional (CompletedPseudoDiffOp K) E]

/-- A vector with bounded forward orbit and backward orbit tending to zero is zero. -/
theorem backwardContractingSubspace_inf_forwardBoundedSubspace_eq_bot :
    backwardContractingSubspace T hT ⊓ forwardBoundedSubspace T hT = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro x ⟨hxC, hxB⟩
  rw [Submodule.mem_bot]
  obtain ⟨N, hNfg, hNB, hTN⟩ := exists_stable_lattice_forwardBoundedSubspace hT
  obtain ⟨M, hM, hMx⟩ := mem_backwardContractingSubspace.1 hxC
  obtain ⟨e, he⟩ := exists_nat_le_uniformizerDilate_of_fg (M := N)
    (hM.of_le (inf_le_left : M ⊓ (forwardBoundedSubspace T hT).restrictScalars
      (CompletedPseudoDiffOpInteger (K := K)) ≤ M)) (by
      rw [hNB]
      exact fun y hy => hy.2)
  have hBinv : ∀ n : ℕ, (T⁻¹ ^ n) x ∈ forwardBoundedSubspace T hT :=
    fun n => pow_apply_mem_of_forall (fun y hy => inv_apply_mem_forwardBoundedSubspace hT hy) n x hxB
  refine eq_zero_of_forall_mem_uniformizerDilate hNfg fun j => ?_
  obtain ⟨n, hn⟩ := (hMx (j + e)).exists
  have h1 : (T⁻¹ ^ n) x ∈ uniformizerDilate ((j + e : ℕ) : ℤ)
      (M ⊓ (forwardBoundedSubspace T hT).restrictScalars (CompletedPseudoDiffOpInteger (K := K))) := by
    rw [uniformizerDilate_inf_restrictScalars]
    exact ⟨hn, hBinv n⟩
  have h2 := uniformizerDilate_mono (k := ((j + e : ℕ) : ℤ)) he h1
  rw [uniformizerDilate_uniformizerDilate] at h2
  have h3 := pow_apply_mem_uniformizerDilate_of_stable hT hTN n _ h2
  have hback : (T ^ n) ((T⁻¹ ^ n) x) = x := by
    rw [← LinearEquiv.mul_apply, inv_pow, mul_inv_cancel, LinearEquiv.coe_one, id]
  rw [hback] at h3
  convert h3 using 2
  push_cast
  ring

/-- **`E = B(T) ⊕ C(T)`.** -/
theorem isCompl_forwardBoundedSubspace_backwardContractingSubspace :
    IsCompl (forwardBoundedSubspace T hT) (backwardContractingSubspace T hT) := by
  constructor
  · rw [disjoint_iff, inf_comm]
    exact backwardContractingSubspace_inf_forwardBoundedSubspace_eq_bot hT
  · rw [codisjoint_iff]
    exact forwardBoundedSubspace_sup_backwardContractingSubspace_eq_top hT

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- Backward-contracting vectors are backward bounded. -/
theorem backwardContractingSubspace_le_forwardBoundedSubspace_inv :
    backwardContractingSubspace T hT ≤ forwardBoundedSubspace T⁻¹ hT.inv := fun _ hx =>
  mem_forwardBoundedSubspace_inv_of_mem_backwardContractingSubspace hT hx

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- Forward-contracting vectors are forward bounded. -/
theorem backwardContractingSubspace_inv_le_forwardBoundedSubspace :
    backwardContractingSubspace T⁻¹ hT.inv ≤ forwardBoundedSubspace T hT := by
  have h := backwardContractingSubspace_le_forwardBoundedSubspace_inv hT.inv
  rwa [forwardBoundedSubspace_congr (inv_inv T) hT.inv.inv hT] at h

/-- **The forward-bounded part splits into the neutral part and the forward-contracting part.** -/
theorem forwardBoundedSubspace_eq_neutral_sup :
    forwardBoundedSubspace T hT = (forwardBoundedSubspace T hT ⊓ forwardBoundedSubspace T⁻¹ hT.inv) ⊔
      backwardContractingSubspace T⁻¹ hT.inv := by
  have htop := forwardBoundedSubspace_sup_backwardContractingSubspace_eq_top hT.inv
  calc forwardBoundedSubspace T hT
      = forwardBoundedSubspace T hT ⊓ (forwardBoundedSubspace T⁻¹ hT.inv ⊔
          backwardContractingSubspace T⁻¹ hT.inv) := by rw [htop, inf_top_eq]
    _ = (forwardBoundedSubspace T hT ⊓ forwardBoundedSubspace T⁻¹ hT.inv) ⊔
          backwardContractingSubspace T⁻¹ hT.inv :=
        (inf_sup_assoc_of_le _ (backwardContractingSubspace_inv_le_forwardBoundedSubspace hT)).symm

theorem neutral_inf_backwardContractingSubspace_inv_eq_bot :
    (forwardBoundedSubspace T hT ⊓ forwardBoundedSubspace T⁻¹ hT.inv) ⊓
      backwardContractingSubspace T⁻¹ hT.inv = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨_, hx⟩, hx'⟩
  have := backwardContractingSubspace_inf_forwardBoundedSubspace_eq_bot hT.inv
  rw [← this]
  exact ⟨hx', hx⟩

/-- **The three-part decomposition** `E = C(T) ⊕ ((B(T) ⊓ B(T⁻¹)) ⊕ C(T⁻¹))`. -/
theorem isCompl_backwardContractingSubspace_neutral_sup :
    IsCompl (backwardContractingSubspace T hT)
      ((forwardBoundedSubspace T hT ⊓ forwardBoundedSubspace T⁻¹ hT.inv) ⊔
        backwardContractingSubspace T⁻¹ hT.inv) := by
  rw [← forwardBoundedSubspace_eq_neutral_sup hT]
  exact (isCompl_forwardBoundedSubspace_backwardContractingSubspace hT).symm

/-- `T⁻¹` contracts a lattice of the backward-contracting subspace uniformly. -/
theorem exists_contracting_lattice_backwardContractingSubspace :
    ∃ P : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, P.FG ∧
      Submodule.span (CompletedPseudoDiffOp K) (P : Set E) = backwardContractingSubspace T hT ∧
      ∃ m : ℕ, 1 ≤ m ∧ uniformizerDilate (-1) P ≤ semilinearImage (T ^ m) (hT.pow m) P :=
  exists_contracting_lattice_of_inf_forwardBoundedSubspace_eq_bot hT _ _ rfl
    (fun _ hx => apply_mem_backwardContractingSubspace hT hx)
    (fun _ hx => inv_apply_mem_backwardContractingSubspace hT hx)
    (by rw [inf_comm]; exact backwardContractingSubspace_inf_forwardBoundedSubspace_eq_bot hT)

end

end DiffOp

end GaloisForLFunctions.HTGeometry
