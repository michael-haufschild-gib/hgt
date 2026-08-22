import GaloisForLFunctions.HTGeometry.TernaryFormationDualityHodge
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Hodge coercivity on the divergence-free edge-cochain space

This file formalises §2 of Boudourides, *Hodge Coercivity and Global Dynamics in Two-Field
Edge-Cochain Systems with MHD-Type Cancellation* (arXiv:2608.19360).

Let `C⁰ → C¹ → C²` be a finite two-step cochain complex of real inner-product spaces with
coboundaries `d₀`, `d₁` and `d₁ ∘ d₀ = 0`.  The divergence-free edge space is `V = ker d₀*`, the
degree-one Hodge Laplacian is `Δ₁ = d₀ d₀* + d₁* d₁`, and the harmonic space is
`H¹ = ker Δ₁ = ker d₁ ∩ ker d₀*`.

## Main results

* `inner_hodgeLaplacian_self_of_mem_divFree` — equation (1): `⟨Δ₁ v, v⟩ = ‖d₁ v‖²` on `V`.
* `hodgeLaplacian_mem_divFree`, `starProjection_divFree_hodgeLaplacian` — Lemma 1: `V` is
  `Δ₁`-invariant and `P Δ₁ = Δ₁ P`.
* `hodge_coercive_iff_harmonic_eq_bot` — **Theorem 1**, the Hodge coercivity criterion: the
  Poincaré-type estimate `⟨Δ₁ v, v⟩ ≥ λ ‖v‖²` holds on all of `V` for some `λ > 0` if and only
  if the harmonic space is trivial.
* `exists_pos_coercive_on_divFreeComplement` — the unconditional companion: the estimate always
  holds on `V₀ = V ∩ (H¹)ᗮ`, with the sharp constant `λ₊` attained
  (`exists_attained_coercive_on_divFreeComplement`).

The compactness input is isolated as `exists_pos_forall_mem_smul_norm_sq_le`, a reusable statement
about continuous `2`-homogeneous functions that are positive off the origin of a subspace.
-/

open Set Metric
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry.HodgeEdgeCochain

/-! ## A reusable compactness lemma -/

section Homogeneous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A continuous `2`-homogeneous function vanishes at the origin. -/
theorem eq_zero_of_homogeneous {q : E → ℝ}
    (hhom : ∀ (c : ℝ) (v : E), q (c • v) = c ^ 2 * q v) : q 0 = 0 := by
  have h := hhom 0 0
  simpa using h

/-- The unit sphere of a subspace of a finite-dimensional space is compact. -/
theorem isCompact_sphere_inter_submodule (W : Submodule ℝ E) :
    IsCompact {v : E | v ∈ W ∧ ‖v‖ = 1} := by
  have hset : {v : E | v ∈ W ∧ ‖v‖ = 1} = (W : Set E) ∩ Metric.sphere (0 : E) 1 := by
    ext v
    simp
  rw [hset]
  exact (isCompact_sphere (0 : E) 1).inter_left W.closed_of_finiteDimensional

/-- **Uniform positivity from pointwise positivity.**  A continuous `2`-homogeneous function that
is strictly positive on the nonzero vectors of a subspace `W` of a finite-dimensional space
dominates a positive multiple of `‖·‖²` on all of `W`.  This is the compactness step behind the
Hodge coercivity criterion. -/
theorem exists_pos_forall_mem_smul_norm_sq_le (W : Submodule ℝ E) {q : E → ℝ}
    (hq : Continuous q) (hhom : ∀ (c : ℝ) (v : E), q (c • v) = c ^ 2 * q v)
    (hpos : ∀ v ∈ W, v ≠ 0 → 0 < q v) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v ∈ W, lam * ‖v‖ ^ 2 ≤ q v := by
  classical
  have hq0 : q 0 = 0 := eq_zero_of_homogeneous hhom
  set S : Set E := {v : E | v ∈ W ∧ ‖v‖ = 1} with hS
  have hSc : IsCompact S := isCompact_sphere_inter_submodule W
  -- Normalising a nonzero vector of `W` lands in `S`.
  have hnorm : ∀ v ∈ W, v ≠ 0 → ‖v‖⁻¹ • v ∈ S := by
    intro v hv hne
    refine ⟨W.smul_mem _ hv, ?_⟩
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
  rcases S.eq_empty_or_nonempty with hE | hNe
  · refine ⟨1, one_pos, fun v hv => ?_⟩
    have hv0 : v = 0 := by
      by_contra hne
      have := hnorm v hv hne
      rw [hE] at this
      exact this
    simp [hv0, hq0]
  · obtain ⟨v₀, hv₀S, hmin⟩ := hSc.exists_isMinOn hNe hq.continuousOn
    have hv₀ne : v₀ ≠ 0 := by
      intro h
      have : ‖v₀‖ = 1 := hv₀S.2
      rw [h] at this
      simp at this
    refine ⟨q v₀, hpos v₀ hv₀S.1 hv₀ne, fun v hv => ?_⟩
    rcases eq_or_ne v 0 with rfl | hne
    · simp [hq0]
    · have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hne
      have hmem := hnorm v hv hne
      have hle : q v₀ ≤ q (‖v‖⁻¹ • v) := hmin hmem
      rw [hhom ‖v‖⁻¹ v] at hle
      have hsq : (‖v‖⁻¹) ^ 2 = (‖v‖ ^ 2)⁻¹ := by
        rw [inv_pow]
      rw [hsq] at hle
      have h2 : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
      calc q v₀ * ‖v‖ ^ 2 ≤ ((‖v‖ ^ 2)⁻¹ * q v) * ‖v‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right hle (le_of_lt h2)
        _ = q v := by field_simp

/-- The sharp form of `exists_pos_forall_mem_smul_norm_sq_le`: on a nontrivial subspace the optimal
constant is attained on the unit sphere.  This is the variational characterisation
`λ₊ = min_{0 ≠ v ∈ W} ⟨Δ₁ v, v⟩ / ‖v‖²` of the paper. -/
theorem exists_attained_forall_mem_smul_norm_sq_le (W : Submodule ℝ E) {q : E → ℝ}
    (hq : Continuous q) (hhom : ∀ (c : ℝ) (v : E), q (c • v) = c ^ 2 * q v)
    (hpos : ∀ v ∈ W, v ≠ 0 → 0 < q v) (hW : W ≠ ⊥) :
    ∃ lam : ℝ, 0 < lam ∧ (∀ v ∈ W, lam * ‖v‖ ^ 2 ≤ q v) ∧
      ∃ v ∈ W, ‖v‖ = 1 ∧ q v = lam := by
  classical
  have hq0 : q 0 = 0 := eq_zero_of_homogeneous hhom
  set S : Set E := {v : E | v ∈ W ∧ ‖v‖ = 1} with hS
  have hSc : IsCompact S := isCompact_sphere_inter_submodule W
  have hnorm : ∀ v ∈ W, v ≠ 0 → ‖v‖⁻¹ • v ∈ S := by
    intro v hv hne
    refine ⟨W.smul_mem _ hv, ?_⟩
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
  have hNe : S.Nonempty := by
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW
    exact ⟨‖w‖⁻¹ • w, hnorm w hwW hw0⟩
  obtain ⟨v₀, hv₀S, hmin⟩ := hSc.exists_isMinOn hNe hq.continuousOn
  have hv₀ne : v₀ ≠ 0 := by
    intro h
    have : ‖v₀‖ = 1 := hv₀S.2
    rw [h] at this
    simp at this
  refine ⟨q v₀, hpos v₀ hv₀S.1 hv₀ne, fun v hv => ?_, v₀, hv₀S.1, hv₀S.2, rfl⟩
  rcases eq_or_ne v 0 with rfl | hne
  · simp [hq0]
  · have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hne
    have hmem := hnorm v hv hne
    have hle : q v₀ ≤ q (‖v‖⁻¹ • v) := hmin hmem
    rw [hhom ‖v‖⁻¹ v, inv_pow] at hle
    have h2 : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
    calc q v₀ * ‖v‖ ^ 2 ≤ ((‖v‖ ^ 2)⁻¹ * q v) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle (le_of_lt h2)
      _ = q v := by field_simp

end Homogeneous

/-! ## The edge-cochain phase space -/

section Complex

variable {C0 C1 C2 : Type*}
  [NormedAddCommGroup C0] [InnerProductSpace ℝ C0] [FiniteDimensional ℝ C0]
  [NormedAddCommGroup C1] [InnerProductSpace ℝ C1] [FiniteDimensional ℝ C1]
  [NormedAddCommGroup C2] [InnerProductSpace ℝ C2] [FiniteDimensional ℝ C2]

/-- The divergence-free edge-cochain space `V = ker d₀*`. -/
noncomputable def divFree (d0 : C0 →ₗ[ℝ] C1) : Submodule ℝ C1 := LinearMap.ker (LinearMap.adjoint d0)

theorem mem_divFree_iff (d0 : C0 →ₗ[ℝ] C1) (v : C1) :
    v ∈ divFree d0 ↔ LinearMap.adjoint d0 v = 0 := Iff.rfl

/-- `V` is the orthogonal complement of the range of `d₀`: the Hodge splitting removes exactly the
gradient component. -/
theorem divFree_eq_orthogonal_range (d0 : C0 →ₗ[ℝ] C1) :
    divFree d0 = (LinearMap.range d0)ᗮ := (LinearMap.orthogonal_range d0).symm

/-- The harmonic 1-cochains `H¹ = ker Δ₁`. -/
noncomputable def harmonic (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) : Submodule ℝ C1 :=
  LinearMap.ker (hodgeLaplacian d0 d1)

/-- Equation (2): `H¹ = ker d₁ ∩ ker d₀*`. -/
theorem harmonic_eq_inf (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    harmonic d0 d1 = LinearMap.ker d1 ⊓ divFree d0 := by
  rw [harmonic, ker_hodgeLaplacian d0 d1, divFree_eq_orthogonal_range]

theorem harmonic_le_divFree (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    harmonic d0 d1 ≤ divFree d0 := by
  rw [harmonic_eq_inf]
  exact inf_le_right

/-- The complementary divergence-free space `V₀ = V ∩ (H¹)ᗮ` of equation (2). -/
noncomputable def divFreeComplement (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) : Submodule ℝ C1 :=
  divFree d0 ⊓ (harmonic d0 d1)ᗮ

theorem divFreeComplement_le_divFree (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    divFreeComplement d0 d1 ≤ divFree d0 := inf_le_left

/-! ### The Laplacian form on `V` -/

/-- The real Laplacian quadratic form is a sum of two squares. -/
theorem inner_hodgeLaplacian_self (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (v : C1) :
    ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ = ‖LinearMap.adjoint d0 v‖ ^ 2 + ‖d1 v‖ ^ 2 := by
  have h := re_inner_hodgeLaplacian_self (𝕜 := ℝ) d0 d1 v
  simpa using h

/-- **Equation (1).**  On the divergence-free space the Laplacian form is `‖d₁ v‖²`. -/
theorem inner_hodgeLaplacian_self_of_mem_divFree (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    {v : C1} (hv : v ∈ divFree d0) :
    ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ = ‖d1 v‖ ^ 2 := by
  rw [inner_hodgeLaplacian_self, (mem_divFree_iff d0 v).mp hv]
  simp

theorem inner_hodgeLaplacian_self_nonneg (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (v : C1) :
    0 ≤ ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ := by
  rw [inner_hodgeLaplacian_self]
  positivity

/-- A divergence-free cochain with vanishing Laplacian form is harmonic. -/
theorem mem_harmonic_of_inner_eq_zero (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    {v : C1} (hv : v ∈ divFree d0) (h : ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ = 0) :
    v ∈ harmonic d0 d1 := by
  rw [inner_hodgeLaplacian_self_of_mem_divFree d0 d1 hv] at h
  have hd1 : d1 v = 0 := by
    have : ‖d1 v‖ = 0 := by nlinarith [norm_nonneg (d1 v)]
    exact norm_eq_zero.mp this
  rw [harmonic_eq_inf]
  exact ⟨hd1, hv⟩

/-! ### The divergence-free projector `P` -/

/-- `P² = P`. -/
theorem starProjection_divFree_idem (d0 : C0 →ₗ[ℝ] C1) (x : C1) :
    (divFree d0).starProjection ((divFree d0).starProjection x)
      = (divFree d0).starProjection x :=
  Submodule.starProjection_eq_self_iff.mpr ((divFree d0).starProjection_apply_mem x)

/-- `P* = P`. -/
theorem inner_starProjection_divFree (d0 : C0 →ₗ[ℝ] C1) (x y : C1) :
    ⟪(divFree d0).starProjection x, y⟫_ℝ = ⟪x, (divFree d0).starProjection y⟫_ℝ :=
  Submodule.inner_starProjection_left_eq_right _ _ _

/-- `d₀* P = 0`. -/
theorem adjoint_starProjection_divFree (d0 : C0 →ₗ[ℝ] C1) (x : C1) :
    LinearMap.adjoint d0 ((divFree d0).starProjection x) = 0 :=
  (divFree d0).starProjection_apply_mem x

/-- `Vᗮ` is exactly the gradient part `range d₀`. -/
theorem orthogonal_divFree (d0 : C0 →ₗ[ℝ] C1) : (divFree d0)ᗮ = LinearMap.range d0 := by
  rw [divFree_eq_orthogonal_range, Submodule.orthogonal_orthogonal]

/-- **The normal-equation description of `P` (§2).**  This is the content of the Moore–Penrose
formula `P = I − d₀ (d₀* d₀)† d₀*`: subtracting `d₀ y` for any solution `y` of the normal
equations produces the divergence-free projection, and the pseudo-inverse is only there to pick
one solution in the presence of a nontrivial nullspace. -/
theorem starProjection_divFree_eq_sub (d0 : C0 →ₗ[ℝ] C1) (x : C1) {y : C0}
    (hy : LinearMap.adjoint d0 (d0 y) = LinearMap.adjoint d0 x) :
    (divFree d0).starProjection x = x - d0 y := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · show LinearMap.adjoint d0 (x - d0 y) = 0
    rw [map_sub, hy, sub_self]
  · have : x - (x - d0 y) = d0 y := by abel
    rw [this, orthogonal_divFree]
    exact ⟨y, rfl⟩

/-- The normal equations are always solvable. -/
theorem exists_normalEquation (d0 : C0 →ₗ[ℝ] C1) (x : C1) :
    ∃ y : C0, LinearMap.adjoint d0 (d0 y) = LinearMap.adjoint d0 x := by
  have hmem : x - (divFree d0).starProjection x ∈ LinearMap.range d0 := by
    rw [← orthogonal_divFree]
    exact Submodule.sub_starProjection_mem_orthogonal x
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_⟩
  rw [hy, map_sub, adjoint_starProjection_divFree, sub_zero]

/-! ### Lemma 1: invariance of `V` and commutation with the projector -/

/-- The degree-one Hodge Laplacian is self-adjoint. -/
theorem adjoint_hodgeLaplacian (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    LinearMap.adjoint (hodgeLaplacian d0 d1) = hodgeLaplacian d0 d1 := by
  rw [hodgeLaplacian, map_add, LinearMap.adjoint_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, LinearMap.adjoint_adjoint]

theorem inner_hodgeLaplacian_left (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (x y : C1) :
    ⟪hodgeLaplacian d0 d1 x, y⟫_ℝ = ⟪x, hodgeLaplacian d0 d1 y⟫_ℝ := by
  conv_rhs => rw [← adjoint_hodgeLaplacian d0 d1]
  rw [LinearMap.adjoint_inner_right]

theorem hodgeLaplacian_apply (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (v : C1) :
    hodgeLaplacian d0 d1 v = d0 (LinearMap.adjoint d0 v) + LinearMap.adjoint d1 (d1 v) := rfl

/-- **Lemma 1 (invariance).**  The divergence-free space is invariant under `Δ₁`. -/
theorem hodgeLaplacian_mem_divFree (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    (hdd : d1 ∘ₗ d0 = 0) {v : C1} (hv : v ∈ divFree d0) :
    hodgeLaplacian d0 d1 v ∈ divFree d0 := by
  have hadj : LinearMap.adjoint d0 ∘ₗ LinearMap.adjoint d1 = 0 := by
    rw [← LinearMap.adjoint_comp, hdd, map_zero]
  have hv0 : LinearMap.adjoint d0 v = 0 := (mem_divFree_iff d0 v).mp hv
  have hsecond : LinearMap.adjoint d0 (LinearMap.adjoint d1 (d1 v)) = 0 := by
    have := congrArg (fun f : C2 →ₗ[ℝ] C0 => f (d1 v)) hadj
    simpa using this
  rw [mem_divFree_iff, hodgeLaplacian_apply, map_add, hv0, map_zero, map_zero, hsecond, add_zero]

/-- **Lemma 1 (invariance of the complement).**  Self-adjointness transports the invariance of `V`
to `Vᗮ`. -/
theorem hodgeLaplacian_mem_divFree_orthogonal (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    (hdd : d1 ∘ₗ d0 = 0) {w : C1} (hw : w ∈ (divFree d0)ᗮ) :
    hodgeLaplacian d0 d1 w ∈ (divFree d0)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← inner_hodgeLaplacian_left d0 d1 u w]
  exact (Submodule.mem_orthogonal _ w).mp hw _ (hodgeLaplacian_mem_divFree d0 d1 hdd hu)

/-- **Lemma 1 (commutation).**  `P Δ₁ = Δ₁ P`, where `P` is the orthogonal projector onto the
divergence-free space. -/
theorem starProjection_hodgeLaplacian (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    (hdd : d1 ∘ₗ d0 = 0) (x : C1) :
    (divFree d0).starProjection (hodgeLaplacian d0 d1 x)
      = hodgeLaplacian d0 d1 ((divFree d0).starProjection x) := by
  set p := (divFree d0).starProjection x with hp
  have hpmem : p ∈ divFree d0 := (divFree d0).starProjection_apply_mem x
  have hqmem : x - p ∈ (divFree d0)ᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hxsplit : x = p + (x - p) := by abel
  have h1 : (divFree d0).starProjection (hodgeLaplacian d0 d1 p) = hodgeLaplacian d0 d1 p :=
    Submodule.starProjection_eq_self_iff.mpr (hodgeLaplacian_mem_divFree d0 d1 hdd hpmem)
  have h2 : (divFree d0).starProjection (hodgeLaplacian d0 d1 (x - p)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (divFree d0)).mpr
      (hodgeLaplacian_mem_divFree_orthogonal d0 d1 hdd hqmem)
  conv_lhs => rw [hxsplit]
  rw [map_add, map_add, h1, h2, add_zero]

/-! ### Theorem 1: the Hodge coercivity criterion -/

theorem continuous_hodgeLaplacian_form (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    Continuous fun v : C1 => ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ := by
  have hrw : (fun v : C1 => ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ)
      = fun v : C1 => ‖LinearMap.adjoint d0 v‖ ^ 2 + ‖d1 v‖ ^ 2 :=
    funext (inner_hodgeLaplacian_self d0 d1)
  rw [hrw]
  exact (((LinearMap.adjoint d0).continuous_of_finiteDimensional.norm).pow 2).add
    ((d1.continuous_of_finiteDimensional.norm).pow 2)

theorem hodgeLaplacian_form_homogeneous (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    (c : ℝ) (v : C1) :
    ⟪hodgeLaplacian d0 d1 (c • v), c • v⟫_ℝ = c ^ 2 * ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- **Theorem 1 (Hodge coercivity criterion).**  The full divergence-free space admits the
Poincaré-type estimate needed for dissipativity if and only if its harmonic 1-cochain space is
trivial. -/
theorem hodge_coercive_iff_harmonic_eq_bot (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    harmonic d0 d1 = ⊥ ↔
      ∃ lam : ℝ, 0 < lam ∧
        ∀ v ∈ divFree d0, lam * ‖v‖ ^ 2 ≤ ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ := by
  constructor
  · intro hbot
    refine exists_pos_forall_mem_smul_norm_sq_le (divFree d0)
      (continuous_hodgeLaplacian_form d0 d1) (hodgeLaplacian_form_homogeneous d0 d1) ?_
    intro v hv hne
    rcases lt_or_eq_of_le (inner_hodgeLaplacian_self_nonneg d0 d1 v) with h | h
    · exact h
    · exfalso
      have := mem_harmonic_of_inner_eq_zero d0 d1 hv h.symm
      rw [hbot] at this
      exact hne (by simpa using this)
  · rintro ⟨lam, hlam, hb⟩
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hvV : v ∈ divFree d0 := harmonic_le_divFree d0 d1 hv
    have h0 : hodgeLaplacian d0 d1 v = 0 := hv
    have := hb v hvV
    rw [h0, inner_zero_left] at this
    have hn : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
    have : ‖v‖ = 0 := by nlinarith [norm_nonneg v, sq_nonneg ‖v‖]
    exact norm_eq_zero.mp this

/-- **Theorem 1 (complementary space).**  On `V₀ = V ∩ (H¹)ᗮ` the Poincaré-type estimate holds
unconditionally, with a strictly positive constant `λ₊`. -/
theorem exists_pos_coercive_on_divFreeComplement (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ v ∈ divFreeComplement d0 d1, lam * ‖v‖ ^ 2 ≤ ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ := by
  refine exists_pos_forall_mem_smul_norm_sq_le (divFreeComplement d0 d1)
    (continuous_hodgeLaplacian_form d0 d1) (hodgeLaplacian_form_homogeneous d0 d1) ?_
  intro v hv hne
  rcases lt_or_eq_of_le (inner_hodgeLaplacian_self_nonneg d0 d1 v) with h | h
  · exact h
  · exfalso
    have hharm := mem_harmonic_of_inner_eq_zero d0 d1 hv.1 h.symm
    have : v ∈ harmonic d0 d1 ⊓ (harmonic d0 d1)ᗮ := ⟨hharm, hv.2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at this
    exact hne (by simpa using this)

/-- **Variational characterisation of `λ₊`.**  On a nontrivial complementary space the coercivity
constant is the minimum of the Rayleigh quotient and is attained. -/
theorem exists_attained_coercive_on_divFreeComplement (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    (hne : divFreeComplement d0 d1 ≠ ⊥) :
    ∃ lam : ℝ, 0 < lam ∧
      (∀ v ∈ divFreeComplement d0 d1, lam * ‖v‖ ^ 2 ≤ ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ) ∧
      ∃ v ∈ divFreeComplement d0 d1, ‖v‖ = 1 ∧ ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ = lam := by
  refine exists_attained_forall_mem_smul_norm_sq_le (divFreeComplement d0 d1)
    (continuous_hodgeLaplacian_form d0 d1) (hodgeLaplacian_form_homogeneous d0 d1) ?_ hne
  intro v hv hv0
  rcases lt_or_eq_of_le (inner_hodgeLaplacian_self_nonneg d0 d1 v) with h | h
  · exact h
  · exfalso
    have hharm := mem_harmonic_of_inner_eq_zero d0 d1 hv.1 h.symm
    have : v ∈ harmonic d0 d1 ⊓ (harmonic d0 d1)ᗮ := ⟨hharm, hv.2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at this
    exact hv0 (by simpa using this)

/-- A nonzero harmonic cochain contradicts full-space coercivity: harmonic 1-cochains are
undamped by the Hodge Laplacian. -/
theorem not_coercive_of_harmonic_ne_bot (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    (hne : harmonic d0 d1 ≠ ⊥) :
    ¬ ∃ lam : ℝ, 0 < lam ∧
        ∀ v ∈ divFree d0, lam * ‖v‖ ^ 2 ≤ ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ :=
  fun h => hne ((hodge_coercive_iff_harmonic_eq_bot d0 d1).mpr h)

end Complex

/-! ## Modal coordinates (§2.1) -/

section Modal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Modal calibration.**  In the linear unforced limit an eigenmode of the dissipative operator
decays exponentially at the rate fixed by its eigenvalue: `u(t) = e^{-ν λ t} u(0)` solves
`u' = -ν A u`. -/
theorem hasDerivAt_eigenmode (A : E →ₗ[ℝ] E) {v : E} {lam : ℝ} (hv : A v = lam • v)
    (nu t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(nu * lam) * s) • v)
      (-(nu • A (Real.exp (-(nu * lam) * t) • v))) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(nu * lam) * s) (-(nu * lam)) t := by
    simpa using (hasDerivAt_id t).const_mul (-(nu * lam))
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(nu * lam) * s))
      (Real.exp (-(nu * lam) * t) * -(nu * lam)) t := (Real.hasDerivAt_exp _).comp t h1
  have h2 := hexp.smul_const v
  have hrhs : -(nu • A (Real.exp (-(nu * lam) * t) • v))
      = (Real.exp (-(nu * lam) * t) * -(nu * lam)) • v := by
    rw [map_smul, hv, smul_smul, smul_smul, ← neg_smul]
    congr 1
    ring
  rw [hrhs]
  exact h2

/-- **Harmonic modes are undamped.**  A kernel vector of the dissipative operator is a stationary
solution of the linear unforced equation. -/
theorem hasDerivAt_harmonicMode (A : E →ₗ[ℝ] E) {v : E} (hv : A v = 0) (nu t : ℝ) :
    HasDerivAt (fun _ : ℝ => v) (-(nu • A v)) t := by
  rw [hv, smul_zero, neg_zero]
  exact hasDerivAt_const t v

end Modal

/-! ## Non-vacuity of the criterion

Both sides of Theorem 1 occur, so the criterion is not vacuous.  The complex `ℝ → ℝ → ℝ` with
`d₀ = 0`, `d₁ = id` is coercive, and the complex with `d₀ = d₁ = 0` is not. -/

section Models

/-- A coercive model: `d₀ = 0`, `d₁ = id` gives a trivial harmonic space. -/
theorem harmonic_zero_id_eq_bot :
    harmonic (0 : ℝ →ₗ[ℝ] ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) = ⊥ := by
  rw [harmonic_eq_inf, LinearMap.ker_id, bot_inf_eq]

/-- The coercive model really is a cochain complex. -/
theorem comp_zero_id : (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ∘ₗ (0 : ℝ →ₗ[ℝ] ℝ) = 0 := by
  simp

/-- Consequently Theorem 1 yields a genuine coercivity constant on this complex. -/
theorem exists_coercivity_constant_zero_id :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v ∈ divFree (0 : ℝ →ₗ[ℝ] ℝ),
      lam * ‖v‖ ^ 2 ≤ ⟪hodgeLaplacian (0 : ℝ →ₗ[ℝ] ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) v, v⟫_ℝ :=
  (hodge_coercive_iff_harmonic_eq_bot _ _).mp harmonic_zero_id_eq_bot

/-- A noncoercive model: `d₀ = d₁ = 0` makes the whole edge space harmonic. -/
theorem harmonic_zero_zero_ne_bot :
    harmonic (0 : ℝ →ₗ[ℝ] ℝ) (0 : ℝ →ₗ[ℝ] ℝ) ≠ ⊥ := by
  intro h
  have h1 : (1 : ℝ) ∈ harmonic (0 : ℝ →ₗ[ℝ] ℝ) (0 : ℝ →ₗ[ℝ] ℝ) := by
    rw [harmonic_eq_inf]
    refine ⟨by simp, ?_⟩
    show LinearMap.adjoint (0 : ℝ →ₗ[ℝ] ℝ) (1 : ℝ) = 0
    simp
  rw [h] at h1
  simp at h1

/-- Hence full-space coercivity genuinely fails on that complex. -/
theorem not_coercive_zero_zero :
    ¬ ∃ lam : ℝ, 0 < lam ∧ ∀ v ∈ divFree (0 : ℝ →ₗ[ℝ] ℝ),
        lam * ‖v‖ ^ 2 ≤ ⟪hodgeLaplacian (0 : ℝ →ₗ[ℝ] ℝ) (0 : ℝ →ₗ[ℝ] ℝ) v, v⟫_ℝ :=
  not_coercive_of_harmonic_ne_bot _ _ harmonic_zero_zero_ne_bot

end Models

end GaloisForLFunctions.HTGeometry.HodgeEdgeCochain
