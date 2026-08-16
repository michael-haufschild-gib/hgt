import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Boundary kernel positivity and the coordinate-free rank-one Schur split

For a symmetric operator `T` on a complex inner product space and a boundary functional `β`, the
repaired form `A + t β* β` restricts to `A` on `ker β`; hence every positivity statement about the
repair transfers verbatim to the boundary kernel.

Conversely, if `A` is positive definite on `ker β`, the splitting `V = ker β ⊕ ℂ q` at any `q` with
`β q = 1` is realized coordinate-free by the kernel Riesz vector `w ∈ ker β` characterized by
`⟪k, T w⟫ = ⟪k, T q⟫` for all `k ∈ ker β`.  Completing the square in that splitting gives the exact
congruence

`(A + t β* β)(v) = A(v - (β v) • (q - w)) + ‖β v‖ ^ 2 * (A q + t - A w)`,

whose first summand runs over `ker β`.  So the repair is positive (semi)definite exactly when the
single Schur scalar `A q + t - A w` is (nonneg) positive, and `A w = Re ⟪w, T q⟫` is the energy
`l* B⁻¹ l` of the boundary channel.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The Hermitian quadratic form of a symmetric operator. -/
def hermitianForm (T : V →ₗ[ℂ] V) (v : V) : ℝ := (⟪v, T v⟫_ℂ).re

/-- The form repaired by `t` copies of the rank-one boundary square `β* β`. -/
def repairedForm (T : V →ₗ[ℂ] V) (β : V →ₗ[ℂ] ℂ) (t : ℝ) (v : V) : ℝ :=
  hermitianForm T v + t * ‖β v‖ ^ 2

theorem hermitianForm_zero (T : V →ₗ[ℂ] V) : hermitianForm T 0 = 0 := by
  simp [hermitianForm]

theorem hermitianForm_add {T : V →ₗ[ℂ] V} (hT : T.IsSymmetric) (x y : V) :
    hermitianForm T (x + y) =
      hermitianForm T x + 2 * (⟪x, T y⟫_ℂ).re + hermitianForm T y := by
  have hcross : ⟪y, T x⟫_ℂ = conj ⟪x, T y⟫_ℂ := by
    rw [← hT x y, inner_conj_symm]
  unfold hermitianForm
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hcross]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem hermitianForm_smul (T : V →ₗ[ℂ] V) (c : ℂ) (v : V) :
    hermitianForm T (c • v) = ‖c‖ ^ 2 * hermitianForm T v := by
  unfold hermitianForm
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul]
  simp [pow_two]

/-- The value of the repaired form on the boundary kernel is the base value. -/
theorem repairedForm_eq_of_mem_ker {T : V →ₗ[ℂ] V} (β : V →ₗ[ℂ] ℂ) (t : ℝ) {k : V}
    (hk : β k = 0) : repairedForm T β t k = hermitianForm T k := by
  simp [repairedForm, hk]

/-- **Kernel visibility, semidefinite form.** -/
theorem hermitianForm_nonneg_on_ker {T : V →ₗ[ℂ] V} {β : V →ₗ[ℂ] ℂ} {t : ℝ}
    (h : ∀ v : V, 0 ≤ repairedForm T β t v) {k : V} (hk : β k = 0) :
    0 ≤ hermitianForm T k := by
  rw [← repairedForm_eq_of_mem_ker (T := T) β t hk]
  exact h k

/-- **Kernel visibility, definite form.** -/
theorem hermitianForm_pos_on_ker {T : V →ₗ[ℂ] V} {β : V →ₗ[ℂ] ℂ} {t : ℝ}
    (h : ∀ v : V, v ≠ 0 → 0 < repairedForm T β t v) {k : V} (hk : β k = 0) (hk0 : k ≠ 0) :
    0 < hermitianForm T k := by
  rw [← repairedForm_eq_of_mem_ker (T := T) β t hk]
  exact h k hk0

/-! ### The coordinate-free split `V = ker β ⊕ ℂ q` -/

/-- **Existence of the kernel Riesz vector.**  If the form is positive definite on the boundary
kernel, then every ambient vector has a kernel vector with the same pairing against the kernel. -/
theorem exists_kernelRiesz [FiniteDimensional ℂ V] {T : V →ₗ[ℂ] V} (β : V →ₗ[ℂ] ℂ)
    (hB : ∀ k : V, β k = 0 → k ≠ 0 → 0 < hermitianForm T k) (q : V) :
    ∃ w : V, β w = 0 ∧ ∀ k : V, β k = 0 → ⟪k, T w⟫_ℂ = ⟪k, T q⟫_ℂ := by
  set W : Submodule ℂ V := LinearMap.ker β with hW
  set S : W →ₗ[ℂ] W :=
    (W.orthogonalProjectionOnto : V →L[ℂ] W).toLinearMap ∘ₗ T ∘ₗ W.subtype with hS
  have hpair : ∀ (k : W) (x : V), ⟪k, W.orthogonalProjectionOnto x⟫_ℂ = ⟪(k : V), x⟫_ℂ :=
    fun k x => Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left k x
  have hinj : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro k hk
    have hk0 : S k = 0 := hk
    have hval : ⟪(k : V), T (k : V)⟫_ℂ = 0 := by
      rw [← hpair k (T (k : V))]
      have : (W.orthogonalProjectionOnto (T (k : V))) = S k := rfl
      rw [this, hk0, inner_zero_right]
    have hmem : β (k : V) = 0 := k.2
    by_contra hne
    have hkne : (k : V) ≠ 0 := fun h => hne (Subtype.ext h)
    have := hB _ hmem hkne
    rw [hermitianForm, hval] at this
    simp at this
  obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.mp hinj (W.orthogonalProjectionOnto (T q))
  refine ⟨(w : V), w.2, ?_⟩
  intro k hk
  have hkW : k ∈ W := hk
  have h1 : ⟪k, T (w : V)⟫_ℂ = ⟪(⟨k, hkW⟩ : W), S w⟫_ℂ := by
    rw [← hpair ⟨k, hkW⟩ (T (w : V))]
    rfl
  rw [h1, hw, hpair ⟨k, hkW⟩ (T q)]

/-- **Exact split identity.**  With `β q = 1`, a kernel vector `w` representing the pairing of `q`
against the kernel, the repaired form is a kernel square plus the scalar Schur term. -/
theorem repairedForm_split {T : V →ₗ[ℂ] V} (hT : T.IsSymmetric) (β : V →ₗ[ℂ] ℂ)
    {q w : V} (hq : β q = 1)
    (hproj : ∀ k : V, β k = 0 → ⟪k, T w⟫_ℂ = ⟪k, T q⟫_ℂ) (t : ℝ) (v : V) :
    repairedForm T β t v =
      hermitianForm T (v - (β v) • (q - w)) +
        ‖β v‖ ^ 2 * (hermitianForm T q + t - hermitianForm T w) := by
  have hβu : β (v - (β v) • q) = 0 := by
    simp [map_sub, map_smul, hq]
  have hv : v = (v - (β v) • q) + (β v) • q := by abel
  have hz : v - (β v) • (q - w) = (v - (β v) • q) + (β v) • w := by
    rw [smul_sub]; abel
  have h1 : hermitianForm T v =
      hermitianForm T (v - (β v) • q) + 2 * (⟪v - (β v) • q, T ((β v) • q)⟫_ℂ).re +
        hermitianForm T ((β v) • q) := by
    conv_lhs => rw [hv]
    exact hermitianForm_add hT _ _
  have h2 : hermitianForm T (v - (β v) • (q - w)) =
      hermitianForm T (v - (β v) • q) + 2 * (⟪v - (β v) • q, T ((β v) • w)⟫_ℂ).re +
        hermitianForm T ((β v) • w) := by
    rw [hz]
    exact hermitianForm_add hT _ _
  have hinner : ⟪v - (β v) • q, T ((β v) • w)⟫_ℂ = ⟪v - (β v) • q, T ((β v) • q)⟫_ℂ := by
    rw [map_smul, map_smul, inner_smul_right, inner_smul_right, hproj _ hβu]
  rw [hinner] at h2
  rw [hermitianForm_smul] at h1 h2
  unfold repairedForm
  rw [h1, h2]
  ring

/-- **Scalar Schur criterion, definite case.** -/
theorem repairedForm_pos_iff {T : V →ₗ[ℂ] V} (hT : T.IsSymmetric) (β : V →ₗ[ℂ] ℂ)
    {q w : V} (hq : β q = 1) (hw : β w = 0)
    (hproj : ∀ k : V, β k = 0 → ⟪k, T w⟫_ℂ = ⟪k, T q⟫_ℂ)
    (hB : ∀ k : V, β k = 0 → k ≠ 0 → 0 < hermitianForm T k) (t : ℝ) :
    (∀ v : V, v ≠ 0 → 0 < repairedForm T β t v) ↔
      0 < hermitianForm T q + t - hermitianForm T w := by
  constructor
  · intro h
    have hβ : β (q - w) = 1 := by rw [map_sub, hq, hw, sub_zero]
    have hne : q - w ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hβ
      exact one_ne_zero hβ.symm
    have := h (q - w) hne
    rw [repairedForm_split hT β hq hproj t (q - w), hβ] at this
    simpa [hermitianForm_zero] using this
  · intro hscalar v hv
    rw [repairedForm_split hT β hq hproj t v]
    have hzker : β (v - (β v) • (q - w)) = 0 := by
      simp [map_sub, map_smul, hq, hw]
    rcases eq_or_ne (β v) 0 with hc | hc
    · have hz : v - (β v) • (q - w) = v := by rw [hc]; simp
      rw [hz, hc]
      simpa using hB v hc hv
    · have h1 : 0 ≤ hermitianForm T (v - (β v) • (q - w)) := by
        rcases eq_or_ne (v - (β v) • (q - w)) 0 with h0 | h0
        · rw [h0, hermitianForm_zero]
        · exact (hB _ hzker h0).le
      have h2 : 0 < ‖β v‖ ^ 2 * (hermitianForm T q + t - hermitianForm T w) := by
        have : 0 < ‖β v‖ ^ 2 := by positivity
        exact mul_pos this hscalar
      linarith

/-- **Scalar Schur criterion, semidefinite case.** -/
theorem repairedForm_nonneg_iff {T : V →ₗ[ℂ] V} (hT : T.IsSymmetric) (β : V →ₗ[ℂ] ℂ)
    {q w : V} (hq : β q = 1) (hw : β w = 0)
    (hproj : ∀ k : V, β k = 0 → ⟪k, T w⟫_ℂ = ⟪k, T q⟫_ℂ)
    (hB : ∀ k : V, β k = 0 → 0 ≤ hermitianForm T k) (t : ℝ) :
    (∀ v : V, 0 ≤ repairedForm T β t v) ↔
      0 ≤ hermitianForm T q + t - hermitianForm T w := by
  constructor
  · intro h
    have hβ : β (q - w) = 1 := by rw [map_sub, hq, hw, sub_zero]
    have := h (q - w)
    rw [repairedForm_split hT β hq hproj t (q - w), hβ] at this
    simpa [hermitianForm_zero] using this
  · intro hscalar v
    rw [repairedForm_split hT β hq hproj t v]
    have hzker : β (v - (β v) • (q - w)) = 0 := by
      simp [map_sub, map_smul, hq, hw]
    have h1 : 0 ≤ hermitianForm T (v - (β v) • (q - w)) := hB _ hzker
    have h2 : 0 ≤ ‖β v‖ ^ 2 * (hermitianForm T q + t - hermitianForm T w) := by
      have : (0:ℝ) ≤ ‖β v‖ ^ 2 := by positivity
      exact mul_nonneg this hscalar
    linarith

/-- The Schur energy is the pairing of the kernel Riesz vector with `q`. -/
theorem hermitianForm_kernelRiesz_eq {T : V →ₗ[ℂ] V} {β : V →ₗ[ℂ] ℂ} {q w : V} (hw : β w = 0)
    (hproj : ∀ k : V, β k = 0 → ⟪k, T w⟫_ℂ = ⟪k, T q⟫_ℂ) :
    hermitianForm T w = (⟪w, T q⟫_ℂ).re := by
  rw [hermitianForm, hproj w hw]

/-- **Uvarov repair requires boundary kernel positivity.** -/
theorem uvarov_repair_requires_boundary_kernel_positivity [FiniteDimensional ℂ V]
    {T : V →ₗ[ℂ] V} (hT : T.IsSymmetric) {β : V →ₗ[ℂ] ℂ} {q : V} (hq : β q = 1) (t : ℝ) :
    ((∀ v : V, 0 ≤ repairedForm T β t v) → ∀ k : V, β k = 0 → 0 ≤ hermitianForm T k) ∧
      ((∀ v : V, v ≠ 0 → 0 < repairedForm T β t v) →
        ∀ k : V, β k = 0 → k ≠ 0 → 0 < hermitianForm T k) ∧
      ((∀ k : V, β k = 0 → k ≠ 0 → 0 < hermitianForm T k) →
        ∃ w : V, β w = 0 ∧ hermitianForm T w = (⟪w, T q⟫_ℂ).re ∧
          ((∀ v : V, v ≠ 0 → 0 < repairedForm T β t v) ↔
            0 < hermitianForm T q + t - hermitianForm T w)) := by
  refine ⟨fun h k hk => hermitianForm_nonneg_on_ker h hk,
    fun h k hk hk0 => hermitianForm_pos_on_ker h hk hk0, fun hB => ?_⟩
  obtain ⟨w, hw, hproj⟩ := exists_kernelRiesz (T := T) β hB q
  exact ⟨w, hw, hermitianForm_kernelRiesz_eq hw hproj,
    repairedForm_pos_iff hT β hq hw hproj hB t⟩

/-! ### The scalar shadow is not faithful without kernel positivity

On `ℂ ^ 2` with `T = -1`, the boundary functional `β (x, y) = x` and `t = 2`, the kernel vector `0`
represents `q = e₀` against `ker β`, so the Schur scalar is `-1 + 2 - 0 = 1 > 0`; yet the repaired
form is `-1` at `e₁`.  Hence the scalar criterion above genuinely needs the kernel form to be
positive definite: a positive scalar alone certifies nothing. -/

/-- The two-dimensional complex model space of the scalar-shadow countermodel. -/
abbrev ShadowSpace : Type := EuclideanSpace ℂ (Fin 2)

/-- The negative identity, whose Hermitian form is negative definite. -/
def shadowOperator : ShadowSpace →ₗ[ℂ] ShadowSpace := -LinearMap.id

/-- The boundary functional reading the first coordinate. -/
def shadowBoundary : ShadowSpace →ₗ[ℂ] ℂ :=
  (EuclideanSpace.proj (0 : Fin 2) : ShadowSpace →L[ℂ] ℂ).toLinearMap

/-- The normalized boundary point. -/
def shadowPoint : ShadowSpace := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)

/-- The direction invisible to the boundary functional. -/
def shadowKernelDirection : ShadowSpace := EuclideanSpace.single (1 : Fin 2) (1 : ℂ)

theorem shadowOperator_isSymmetric : (shadowOperator).IsSymmetric := by
  intro x y
  simp [shadowOperator, inner_neg_left, inner_neg_right]

theorem hermitianForm_shadowOperator (v : ShadowSpace) :
    hermitianForm shadowOperator v = -‖v‖ ^ 2 := by
  unfold hermitianForm shadowOperator
  rw [LinearMap.neg_apply, LinearMap.id_apply, inner_neg_right, Complex.neg_re]
  have := inner_self_eq_norm_sq (𝕜 := ℂ) v
  simp only [RCLike.re_to_complex] at this
  rw [this]

theorem shadowBoundary_shadowPoint : shadowBoundary shadowPoint = 1 := by
  simp [shadowBoundary, shadowPoint]

theorem shadowBoundary_shadowKernelDirection : shadowBoundary shadowKernelDirection = 0 := by
  simp [shadowBoundary, shadowKernelDirection]

/-- The zero vector is a kernel Riesz vector for `shadowPoint`. -/
theorem shadowProj (k : ShadowSpace) (hk : shadowBoundary k = 0) :
    ⟪k, shadowOperator 0⟫_ℂ = ⟪k, shadowOperator shadowPoint⟫_ℂ := by
  rw [map_zero, inner_zero_right]
  unfold shadowOperator shadowPoint
  rw [LinearMap.neg_apply, LinearMap.id_apply, inner_neg_right,
    EuclideanSpace.inner_single_right]
  have : (WithLp.ofLp k) (0 : Fin 2) = 0 := hk
  rw [this]
  simp

theorem shadowScalar : hermitianForm shadowOperator shadowPoint + 2
    - hermitianForm shadowOperator 0 = 1 := by
  rw [hermitianForm_shadowOperator, hermitianForm_shadowOperator]
  simp only [shadowPoint, norm_zero]
  norm_num

theorem shadowRepaired_neg :
    repairedForm shadowOperator shadowBoundary 2 shadowKernelDirection = -1 := by
  unfold repairedForm
  rw [hermitianForm_shadowOperator, shadowBoundary_shadowKernelDirection]
  simp [shadowKernelDirection]

/-- **The scalar shadow is not a certificate.**  A strictly positive Schur scalar coexists with a
repaired form that is not positive semidefinite when the boundary kernel carries a negative
direction. -/
theorem shadow_scalar_not_faithful :
    0 < hermitianForm shadowOperator shadowPoint + 2 - hermitianForm shadowOperator 0 ∧
      shadowBoundary shadowPoint = 1 ∧ shadowBoundary 0 = 0 ∧
      (∀ k : ShadowSpace, shadowBoundary k = 0 →
        ⟪k, shadowOperator 0⟫_ℂ = ⟪k, shadowOperator shadowPoint⟫_ℂ) ∧
      ¬ (∀ v : ShadowSpace, 0 ≤ repairedForm shadowOperator shadowBoundary 2 v) := by
  refine ⟨by rw [shadowScalar]; norm_num, shadowBoundary_shadowPoint, map_zero _, shadowProj, ?_⟩
  intro h
  have := h shadowKernelDirection
  rw [shadowRepaired_neg] at this
  norm_num at this

end GaloisForLFunctions.HTGeometry
