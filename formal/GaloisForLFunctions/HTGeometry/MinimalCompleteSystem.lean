import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Minimal and complete systems of vectors in a Hilbert space

Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*
(arXiv:math/0203120), uses throughout the following terminology.  An indexed collection `u : ι → E`
of vectors in a Hilbert space is

* **complete** when the linear span of the `u i` is dense;
* **minimal** when no `u i` lies in the closed linear span of the remaining `u j`.

To a complete and minimal system is attached a *dual* (biorthogonal) system `v : ι → E`, uniquely
determined by `⟪v i, u j⟫ = δ_{ij}`.  Burnol records that such a dual system is always minimal, but
need not be complete, and gives the example `u n = 1 - z ^ n` in the Hardy space of the unit disc,
whose dual system is `v m = - z ^ m`.

This file develops that theory in full generality and closes the example: in the Hilbert-basis
model `u n = b 0 - b (n+1)` the system is complete and minimal, its dual system is
`v n = - b (n+1)`, and the dual system is *not* complete.  Everything is unconditional; the
existence half of the biorthogonal characterisation uses the orthogonal projection onto the closed
span, so no Hahn--Banach input is required.

## Main results

* `isCompleteSystem_iff_forall_inner_eq_zero` — completeness as a vanishing test.
* `IsMinimalSystem.exists_isDualSystem` / `IsDualSystem.isMinimalSystem` — minimality is exactly
  the existence of a biorthogonal system.
* `IsDualSystem.unique_of_isCompleteSystem` — a complete system has at most one dual system.
* `IsDualSystem.isMinimalSystem_right` — a dual system is itself minimal.
* `IsMinimalSystem.of_continuousLinearMap` — minimality of a continuous linear image forces
  minimality of the source system (Burnol, proof of Prop. 6.4).
* `IsCompleteSystem.map` — completeness is pushed forward by a dense-range continuous linear map
  (Burnol, proof of Prop. 6.6).
* `exists_isCompleteSystem_isMinimalSystem_isDualSystem_not_isCompleteSystem` — a complete and
  minimal system whose dual system is not complete.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

variable (𝕜 : Type*) {E F ι κ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The closed linear span of a system of vectors with one index omitted. -/
def systemSpanOmit (u : ι → E) (i : ι) : Submodule 𝕜 E :=
  (Submodule.span 𝕜 (u '' {j | j ≠ i})).topologicalClosure

/-- A system of vectors is **complete** when its linear span is dense. -/
def IsCompleteSystem (u : ι → E) : Prop :=
  (Submodule.span 𝕜 (Set.range u)).topologicalClosure = ⊤

/-- A system of vectors is **minimal** when no member lies in the closed span of the others. -/
def IsMinimalSystem (u : ι → E) : Prop :=
  ∀ i, u i ∉ systemSpanOmit 𝕜 u i

/-- `v` is a **dual system** for `u` when the two are biorthogonal. -/
structure IsDualSystem (u v : ι → E) : Prop where
  /-- Diagonal pairings are `1`. -/
  inner_self : ∀ i, ⟪v i, u i⟫_𝕜 = 1
  /-- Off-diagonal pairings vanish. -/
  inner_ne : ∀ i j, i ≠ j → ⟪v i, u j⟫_𝕜 = 0

variable {𝕜}

theorem isClosed_systemSpanOmit (u : ι → E) (i : ι) :
    IsClosed (systemSpanOmit 𝕜 u i : Set E) :=
  Submodule.isClosed_topologicalClosure _

theorem self_mem_systemSpanOmit {u : ι → E} {i j : ι} (hij : j ≠ i) :
    u j ∈ systemSpanOmit 𝕜 u i :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j, hij, rfl⟩)

/-- Completeness of a system, tested against vectors orthogonal to every member. -/
theorem isCompleteSystem_iff_forall_inner_eq_zero [CompleteSpace E] (u : ι → E) :
    IsCompleteSystem 𝕜 u ↔ ∀ x : E, (∀ i, ⟪u i, x⟫_𝕜 = 0) → x = 0 := by
  rw [IsCompleteSystem, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  constructor
  · intro h x hx
    refine h x ?_
    rw [Submodule.mem_orthogonal]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hx i
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  · intro h x hx
    refine h x fun i => ?_
    exact (Submodule.mem_orthogonal _ _).1 hx (u i) (Submodule.subset_span ⟨i, rfl⟩)

/-- Every biorthogonal partner system certifies minimality. -/
theorem IsDualSystem.isMinimalSystem {u v : ι → E} (h : IsDualSystem 𝕜 u v) :
    IsMinimalSystem 𝕜 u := by
  intro i hi
  have hle : Submodule.span 𝕜 (u '' {j | j ≠ i}) ≤ (𝕜 ∙ v i)ᗮ := by
    rw [Submodule.span_le]
    rintro y ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact h.inner_ne i j (Ne.symm hj)
  have hclosed : systemSpanOmit 𝕜 u i ≤ (𝕜 ∙ v i)ᗮ :=
    Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
  have hzero := (Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hclosed hi)
  rw [h.inner_self i] at hzero
  exact one_ne_zero hzero

/-- A dual system is a dual system in the other direction as well. -/
theorem IsDualSystem.symm {u v : ι → E} (h : IsDualSystem 𝕜 u v) : IsDualSystem 𝕜 v u where
  inner_self i := by
    have hc := congrArg (starRingEnd 𝕜) (h.inner_self i)
    rw [inner_conj_symm, map_one] at hc
    exact hc
  inner_ne i j hij := by
    have hc := congrArg (starRingEnd 𝕜) (h.inner_ne j i (Ne.symm hij))
    rw [inner_conj_symm, map_zero] at hc
    exact hc

/-- Burnol's remark that a dual system is necessarily minimal. -/
theorem IsDualSystem.isMinimalSystem_right {u v : ι → E} (h : IsDualSystem 𝕜 u v) :
    IsMinimalSystem 𝕜 v :=
  h.symm.isMinimalSystem

/-- A minimal system admits a biorthogonal dual system. -/
theorem IsMinimalSystem.exists_isDualSystem [CompleteSpace E] {u : ι → E}
    (h : IsMinimalSystem 𝕜 u) : ∃ v : ι → E, IsDualSystem 𝕜 u v := by
  classical
  have key : ∀ i : ι, ∃ w : E, (∀ j, j ≠ i → ⟪w, u j⟫_𝕜 = 0) ∧ ⟪w, u i⟫_𝕜 = 1 := by
    intro i
    set S : Submodule 𝕜 E := systemSpanOmit 𝕜 u i with hS
    haveI hcs : CompleteSpace S := (isClosed_systemSpanOmit u i).completeSpace_coe
    haveI : S.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace S
    set w : E := u i - S.starProjection (u i) with hw
    have hwmem : w ∈ Sᗮ := S.sub_starProjection_mem_orthogonal (u i)
    have hwne : w ≠ 0 := by
      intro hzero
      refine h i ?_
      have hui : u i = S.starProjection (u i) := sub_eq_zero.1 hzero
      rw [hui]
      exact S.starProjection_apply_mem _
    have hproj : ⟪w, S.starProjection (u i)⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal' _ _).1 hwmem _ (S.starProjection_apply_mem _)
    have hsplit : u i = w + S.starProjection (u i) := by rw [hw, sub_add_cancel]
    have hwu : ⟪w, u i⟫_𝕜 = (‖w‖ : 𝕜) ^ (2 : ℕ) := by
      rw [hsplit, inner_add_right, hproj, add_zero, inner_self_eq_norm_sq_to_K]
    have hnorm : ((‖w‖ : 𝕜)) ^ (2 : ℕ) ≠ 0 := by
      refine pow_ne_zero 2 ?_
      simpa using hwne
    have hconj : (starRingEnd 𝕜) (((‖w‖ : 𝕜) ^ (2 : ℕ))⁻¹) = ((‖w‖ : 𝕜) ^ (2 : ℕ))⁻¹ := by
      rw [map_inv₀, map_pow, RCLike.conj_ofReal]
    refine ⟨((‖w‖ : 𝕜) ^ (2 : ℕ))⁻¹ • w, ?_, ?_⟩
    · intro j hj
      rw [inner_smul_left, hconj]
      have hz : ⟪w, u j⟫_𝕜 = 0 :=
        (Submodule.mem_orthogonal' _ _).1 hwmem _ (self_mem_systemSpanOmit hj)
      rw [hz, mul_zero]
    · rw [inner_smul_left, hconj, hwu, inv_mul_cancel₀ hnorm]
  choose v hv0 hv1 using key
  exact ⟨v, ⟨hv1, fun i j hij => hv0 i j (Ne.symm hij)⟩⟩

/-- Minimality is exactly the existence of a biorthogonal dual system. -/
theorem isMinimalSystem_iff_exists_isDualSystem [CompleteSpace E] (u : ι → E) :
    IsMinimalSystem 𝕜 u ↔ ∃ v : ι → E, IsDualSystem 𝕜 u v :=
  ⟨fun h => h.exists_isDualSystem, fun ⟨_, hv⟩ => hv.isMinimalSystem⟩

/-- A complete system has at most one dual system. -/
theorem IsDualSystem.unique_of_isCompleteSystem [CompleteSpace E] {u v v' : ι → E}
    (hu : IsCompleteSystem 𝕜 u) (h : IsDualSystem 𝕜 u v) (h' : IsDualSystem 𝕜 u v') :
    v = v' := by
  funext i
  have := (isCompleteSystem_iff_forall_inner_eq_zero u).1 hu (v i - v' i) ?_
  · exact sub_eq_zero.1 this
  · intro j
    have h1 : ⟪u j, v i⟫_𝕜 = ⟪u j, v' i⟫_𝕜 := by
      rcases eq_or_ne i j with rfl | hij
      · have e1 := congrArg (starRingEnd 𝕜) (h.inner_self i)
        have e2 := congrArg (starRingEnd 𝕜) (h'.inner_self i)
        rw [inner_conj_symm, map_one] at e1 e2
        rw [e1, e2]
      · have e1 := congrArg (starRingEnd 𝕜) (h.inner_ne i j hij)
        have e2 := congrArg (starRingEnd 𝕜) (h'.inner_ne i j hij)
        rw [inner_conj_symm, map_zero] at e1 e2
        rw [e1, e2]
    rw [inner_sub_right, h1, sub_self]

/-- Minimality of a continuous linear image forces minimality of the source system. -/
theorem IsMinimalSystem.of_continuousLinearMap {u : ι → E} (T : E →L[𝕜] F)
    (h : IsMinimalSystem 𝕜 fun i => T (u i)) : IsMinimalSystem 𝕜 u := by
  intro i hi
  refine h i ?_
  have hsub : systemSpanOmit 𝕜 u i ≤
      (systemSpanOmit 𝕜 (fun j => T (u j)) i).comap (T : E →ₗ[𝕜] F) := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rw [Submodule.span_le]
      rintro y ⟨j, hj, rfl⟩
      exact self_mem_systemSpanOmit (u := fun j => T (u j)) hj
    · exact (isClosed_systemSpanOmit (fun j => T (u j)) i).preimage T.continuous
  exact hsub hi

/-- Completeness is pushed forward by a dense-range continuous linear map. -/
theorem IsCompleteSystem.map {u : ι → E} (T : E →L[𝕜] F) (hT : DenseRange T)
    (h : IsCompleteSystem 𝕜 u) : IsCompleteSystem 𝕜 fun i => T (u i) := by
  set K : Submodule 𝕜 F := (Submodule.span 𝕜 (Set.range fun i => T (u i))).topologicalClosure
  have hmem : ∀ x : E, T x ∈ K := by
    intro x
    have hle : Submodule.span 𝕜 (Set.range u) ≤ K.comap (T : E →ₗ[𝕜] F) := by
      rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
    have hclosed : IsClosed ((K.comap (T : E →ₗ[𝕜] F)) : Set E) :=
      (Submodule.isClosed_topologicalClosure _).preimage T.continuous
    have := Submodule.topologicalClosure_minimal _ hle hclosed
    rw [h] at this
    exact this (Submodule.mem_top (x := x))
  have hrange : Set.range (T : E → F) ⊆ (K : Set F) := by
    rintro y ⟨x, rfl⟩; exact hmem x
  have : (⊤ : Submodule 𝕜 F) ≤ K := by
    intro y _
    have : y ∈ closure (Set.range (T : E → F)) := hT y
    exact (Submodule.isClosed_topologicalClosure _).closure_subset_iff.2 hrange this
  exact top_le_iff.1 this

/-- Minimality passes to subsystems. -/
theorem IsMinimalSystem.comp_injective {u : ι → E} (h : IsMinimalSystem 𝕜 u)
    {f : κ → ι} (hf : Function.Injective f) : IsMinimalSystem 𝕜 (u ∘ f) := by
  intro k hk
  refine h (f k) ?_
  refine Submodule.topologicalClosure_mono ?_ hk
  refine Submodule.span_mono ?_
  rintro y ⟨l, hl, rfl⟩
  exact ⟨f l, fun hc => hl (hf hc), rfl⟩


/-! ### Burnol's example: a complete and minimal system whose dual system is not complete

In the Hardy space of the unit disc the system `u n = 1 - z ^ n`, `n ≥ 1`, is complete and minimal
and its dual system is `v m = - z ^ m`, which is not complete.  The following is the same example
written in an arbitrary Hilbert basis: `1` becomes `b 0` and `z ^ n` becomes `b n`. -/

section HardyRemark

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The system `u n = b 0 - b (n + 1)`; the Hilbert-basis form of `1 - z ^ n` in `H²(𝔻)`. -/
noncomputable def hardyRemarkSystem (b : HilbertBasis ℕ 𝕜 E) (n : ℕ) : E := b 0 - b (n + 1)

/-- The dual system `v n = - b (n + 1)`; the Hilbert-basis form of `- z ^ n` in `H²(𝔻)`. -/
noncomputable def hardyRemarkDual (b : HilbertBasis ℕ 𝕜 E) (n : ℕ) : E := - b (n + 1)

theorem isDualSystem_hardyRemark (b : HilbertBasis ℕ 𝕜 E) :
    IsDualSystem 𝕜 (hardyRemarkSystem b) (hardyRemarkDual b) := by
  classical
  have hb : ∀ i j : ℕ, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 :=
    orthonormal_iff_ite.1 b.orthonormal
  constructor
  · intro i
    have h1 : ¬ (i + 1 = 0) := by omega
    simp only [hardyRemarkSystem, hardyRemarkDual, inner_neg_left, inner_sub_right, hb,
      if_neg h1]
    simp
  · intro i j hij
    have h1 : ¬ (i + 1 = 0) := by omega
    have h2 : ¬ (i + 1 = j + 1) := by omega
    simp only [hardyRemarkSystem, hardyRemarkDual, inner_neg_left, inner_sub_right, hb,
      if_neg h1, if_neg h2]
    ring

theorem isMinimalSystem_hardyRemark (b : HilbertBasis ℕ 𝕜 E) :
    IsMinimalSystem 𝕜 (hardyRemarkSystem b) :=
  (isDualSystem_hardyRemark b).isMinimalSystem

theorem isMinimalSystem_hardyRemarkDual (b : HilbertBasis ℕ 𝕜 E) :
    IsMinimalSystem 𝕜 (hardyRemarkDual b) :=
  (isDualSystem_hardyRemark b).isMinimalSystem_right

theorem isCompleteSystem_hardyRemark [CompleteSpace E] (b : HilbertBasis ℕ 𝕜 E) :
    IsCompleteSystem 𝕜 (hardyRemarkSystem b) := by
  classical
  rw [isCompleteSystem_iff_forall_inner_eq_zero]
  intro x hx
  have hc : ∀ n : ℕ, ⟪b (n + 1), x⟫_𝕜 = ⟪b 0, x⟫_𝕜 := by
    intro n
    have := hx n
    rw [hardyRemarkSystem, inner_sub_left, sub_eq_zero] at this
    exact this.symm
  have htend : Filter.Tendsto (fun i => ⟪x, b i⟫_𝕜 * ⟪b i, x⟫_𝕜) Filter.atTop (nhds 0) :=
    (b.summable_inner_mul_inner x x).tendsto_atTop_zero
  have hshift : Filter.Tendsto (fun n => ⟪x, b (n + 1)⟫_𝕜 * ⟪b (n + 1), x⟫_𝕜)
      Filter.atTop (nhds 0) := htend.comp (Filter.tendsto_add_atTop_nat 1)
  have hconst : (fun n : ℕ => ⟪x, b (n + 1)⟫_𝕜 * ⟪b (n + 1), x⟫_𝕜) =
      fun _ : ℕ => ⟪x, b 0⟫_𝕜 * ⟪b 0, x⟫_𝕜 := by
    funext n
    have h1 : ⟪x, b (n + 1)⟫_𝕜 = ⟪x, b 0⟫_𝕜 := by
      have := congrArg (starRingEnd 𝕜) (hc n)
      rw [inner_conj_symm, inner_conj_symm] at this
      exact this
    rw [h1, hc n]
  rw [hconst] at hshift
  have hzero : ⟪x, b 0⟫_𝕜 * ⟪b 0, x⟫_𝕜 = 0 :=
    (tendsto_nhds_unique hshift tendsto_const_nhds).symm
  have hb0 : ⟪b 0, x⟫_𝕜 = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · exact inner_eq_zero_symm.1 h
    · exact h
  have hall : ∀ k : ℕ, ⟪b k, x⟫_𝕜 = 0 := by
    intro k
    cases k with
    | zero => exact hb0
    | succ n => rw [hc n]; exact hb0
  have hrepr := b.hasSum_repr x
  have hz : (fun i => b.repr x i • b i) = fun _ : ℕ => (0 : E) := by
    funext i
    rw [b.repr_apply_apply, hall i, zero_smul]
  rw [hz] at hrepr
  exact (hasSum_zero.unique hrepr).symm

theorem not_isCompleteSystem_hardyRemarkDual [CompleteSpace E] (b : HilbertBasis ℕ 𝕜 E) :
    ¬ IsCompleteSystem 𝕜 (hardyRemarkDual b) := by
  classical
  rw [isCompleteSystem_iff_forall_inner_eq_zero]
  intro hcomp
  have hb : ∀ i j : ℕ, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 :=
    orthonormal_iff_ite.1 b.orthonormal
  have h0 : b 0 = 0 := by
    refine hcomp (b 0) fun n => ?_
    have h1 : ¬ (n + 1 = 0) := by omega
    simp only [hardyRemarkDual, inner_neg_left, hb, if_neg h1]
    ring
  have : ‖b 0‖ = 1 := b.orthonormal.1 0
  rw [h0, norm_zero] at this
  exact zero_ne_one this

end HardyRemark

/-- A concrete Hilbert basis of `ℓ²(ℕ, ℂ)`, the model for Burnol's Hardy-space remark. -/
noncomputable def hardyRemarkBasis : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) := default

/-- **Burnol's remark of §3, closed.**  A dual system is always minimal, but need not be complete:
the system `u n = b 0 - b (n+1)` of `ℓ²(ℕ, ℂ)` is complete and minimal, its dual system is
`v n = - b (n+1)`, and that dual system is minimal but *not* complete. -/
theorem hardyRemark_isCompleteSystem_isMinimalSystem_dual_not_isCompleteSystem :
    IsCompleteSystem ℂ (hardyRemarkSystem hardyRemarkBasis) ∧
      IsMinimalSystem ℂ (hardyRemarkSystem hardyRemarkBasis) ∧
      IsDualSystem ℂ (hardyRemarkSystem hardyRemarkBasis) (hardyRemarkDual hardyRemarkBasis) ∧
      IsMinimalSystem ℂ (hardyRemarkDual hardyRemarkBasis) ∧
      ¬ IsCompleteSystem ℂ (hardyRemarkDual hardyRemarkBasis) :=
  ⟨isCompleteSystem_hardyRemark _, isMinimalSystem_hardyRemark _, isDualSystem_hardyRemark _,
    isMinimalSystem_hardyRemarkDual _, not_isCompleteSystem_hardyRemarkDual _⟩

end GaloisForLFunctions.HTGeometry
