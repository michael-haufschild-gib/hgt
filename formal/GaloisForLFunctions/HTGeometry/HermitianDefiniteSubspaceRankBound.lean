import Mathlib

/-!
# Definite subspaces of a finite-rank self-adjoint operator: exact index and stability

For a self-adjoint bounded operator `A` on a complex Hilbert space, a subspace `V` on which the real
quadratic form `y ↦ Re ⟪A y, y⟫` is strictly positive and a subspace `W` on which it is strictly
negative are disjoint, and `A` is injective on `V ⊔ W`.  Hence, when `A` has finite-dimensional
range,

`finrank V + finrank W ≤ finrank (range A)`.

In particular a self-adjoint operator of rank two carrying one strictly positive and one strictly
negative quadratic value has positive index exactly one and negative index exactly one: it is one
hyperbolic plane.

The margin version `ε ‖y‖² < Re ⟪B y, y⟫` is stable under operator-norm perturbation: if
`‖B - A‖ < ε` then every `ε`-positive subspace of `B` is strictly positive for `A`.  This is the
mechanism that transports the exact index of a limit form to every sufficiently close approximant.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The real quadratic form `y ↦ Re ⟪A y, y⟫` of a bounded operator. -/
def reQuad (A : E →L[ℂ] E) (y : E) : ℝ := (inner ℂ (A y) y : ℂ).re

/-- Strict positivity of the real quadratic form on a submodule. -/
def StrictPositiveOn (A : E →L[ℂ] E) (V : Submodule ℂ E) : Prop :=
  ∀ y ∈ V, y ≠ 0 → 0 < reQuad A y

/-- Strict negativity of the real quadratic form on a submodule. -/
def StrictNegativeOn (A : E →L[ℂ] E) (W : Submodule ℂ E) : Prop :=
  ∀ y ∈ W, y ≠ 0 → reQuad A y < 0

/-- Positivity with margin `ε`: `ε ‖y‖² < Re ⟪A y, y⟫` on the submodule. -/
def MarginPositiveOn (A : E →L[ℂ] E) (ε : ℝ) (V : Submodule ℂ E) : Prop :=
  ∀ y ∈ V, y ≠ 0 → ε * ‖y‖ ^ 2 < reQuad A y

/-- Negativity with margin `ε`: `Re ⟪A y, y⟫ < -ε ‖y‖²` on the submodule. -/
def MarginNegativeOn (A : E →L[ℂ] E) (ε : ℝ) (W : Submodule ℂ E) : Prop :=
  ∀ y ∈ W, y ≠ 0 → reQuad A y < -(ε * ‖y‖ ^ 2)

@[simp]
theorem reQuad_zero (A : E →L[ℂ] E) : reQuad A (0 : E) = 0 := by
  simp [reQuad]

/-- The real quadratic form is homogeneous of degree two. -/
theorem reQuad_smul (A : E →L[ℂ] E) (c : ℂ) (y : E) :
    reQuad A (c • y) = ‖c‖ ^ 2 * reQuad A y := by
  unfold reQuad
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul' c]
  have hcast : ((‖c‖ : ℂ) ^ 2) = ((‖c‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.re_ofReal_mul]

/-- Strictly positive and strictly negative subspaces are disjoint. -/
theorem disjoint_of_definite {A : E →L[ℂ] E}
    {V W : Submodule ℂ E} (hV : StrictPositiveOn A V) (hW : StrictNegativeOn A W) :
    Disjoint V W := by
  rw [Submodule.disjoint_def]
  intro x hxV hxW
  by_contra hx
  have hpos := hV x hxV hx
  have hneg := hW x hxW hx
  linarith

/-- A strictly negative vector spans a strictly negative line. -/
theorem strictNegativeOn_span_singleton {A : E →L[ℂ] E} {m : E} (hm : reQuad A m < 0) :
    StrictNegativeOn A (ℂ ∙ m) := by
  intro y hy hy0
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hy0
  rw [reQuad_smul]
  have hc2 : 0 < ‖c‖ ^ 2 := by positivity
  exact mul_neg_of_pos_of_neg hc2 hm

/-- A strictly positive vector spans a strictly positive line. -/
theorem strictPositiveOn_span_singleton {A : E →L[ℂ] E} {m : E} (hm : 0 < reQuad A m) :
    StrictPositiveOn A (ℂ ∙ m) := by
  intro y hy hy0
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hy0
  rw [reQuad_smul]
  have hc2 : 0 < ‖c‖ ^ 2 := by positivity
  exact mul_pos hc2 hm

/-- A vector with strictly negative quadratic value is nonzero. -/
theorem ne_zero_of_reQuad_neg {A : E →L[ℂ] E} {m : E} (hm : reQuad A m < 0) : m ≠ 0 := by
  rintro rfl
  rw [reQuad_zero] at hm
  exact lt_irrefl _ hm

/-- A vector with strictly positive quadratic value is nonzero. -/
theorem ne_zero_of_reQuad_pos {A : E →L[ℂ] E} {m : E} (hm : 0 < reQuad A m) : m ≠ 0 := by
  rintro rfl
  rw [reQuad_zero] at hm
  exact lt_irrefl _ hm

section SelfAdjoint

variable [CompleteSpace E]

/-- The real quadratic form of a self-adjoint operator has a symmetric polarization. -/
theorem re_inner_apply_symm {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (x y : E) :
    (inner ℂ (A x) y : ℂ).re = (inner ℂ (A y) x : ℂ).re := by
  have h : inner ℂ (A y) x = inner ℂ y (A x) := by
    have := ContinuousLinearMap.adjoint_inner_left A x y
    rwa [hA.adjoint_eq] at this
  rw [h, ← inner_conj_symm (A x) y, Complex.conj_re]

/-- A strictly positive subspace and a strictly negative subspace of a self-adjoint operator meet
only in zero, and the operator is injective on their sum. -/
theorem eq_zero_of_apply_eq_zero_of_definite {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {V W : Submodule ℂ E} (hV : StrictPositiveOn A V) (hW : StrictNegativeOn A W)
    {y : E} (hy : y ∈ V ⊔ W) (h0 : A y = 0) : y = 0 := by
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  have h1 : (inner ℂ (A (v + w)) v : ℂ) = 0 := by rw [h0, inner_zero_left]
  have h2 : (inner ℂ (A (v + w)) w : ℂ) = 0 := by rw [h0, inner_zero_left]
  rw [map_add, inner_add_left] at h1 h2
  have h1r := congrArg Complex.re h1
  have h2r := congrArg Complex.re h2
  rw [Complex.add_re, Complex.zero_re] at h1r h2r
  have hsym := re_inner_apply_symm hA w v
  have hvw : reQuad A v = reQuad A w := by
    unfold reQuad
    linarith
  by_cases hv0 : v = 0
  · subst hv0
    by_cases hw0 : w = 0
    · simp [hw0]
    · have hneg := hW w hw hw0
      rw [reQuad_zero] at hvw
      linarith
  · have hpos := hV v hv hv0
    by_cases hw0 : w = 0
    · subst hw0
      rw [reQuad_zero] at hvw
      linarith
    · have hneg := hW w hw hw0
      linarith

/-- **Definite-subspace dimension bound.**  For a self-adjoint operator with finite-dimensional
range, a strictly positive subspace `V` and a strictly negative subspace `W` are finite-dimensional
and `finrank V + finrank W ≤ finrank (range A)`. -/
theorem finrank_add_finrank_le_finrank_range {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    [FiniteDimensional ℂ (LinearMap.range A.toLinearMap)]
    {V W : Submodule ℂ E} (hV : StrictPositiveOn A V) (hW : StrictNegativeOn A W) :
    FiniteDimensional ℂ V ∧ FiniteDimensional ℂ W ∧
      finrank ℂ V + finrank ℂ W ≤ finrank ℂ (LinearMap.range A.toLinearMap) := by
  let f : ↥(V ⊔ W) →ₗ[ℂ] ↥(LinearMap.range A.toLinearMap) :=
    LinearMap.codRestrict (LinearMap.range A.toLinearMap)
      (A.toLinearMap.domRestrict (V ⊔ W)) (fun y => LinearMap.mem_range_self _ _)
  have hf : Function.Injective f := by
    intro y₁ y₂ h
    have h' : A (y₁ : E) = A (y₂ : E) := by
      have := congrArg Subtype.val h
      simpa [f, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply] using this
    have hsub : A ((y₁ : E) - y₂) = 0 := by rw [map_sub, h', sub_self]
    have hmem : ((y₁ : E) - y₂) ∈ V ⊔ W := Submodule.sub_mem _ y₁.2 y₂.2
    exact Subtype.ext (sub_eq_zero.mp (eq_zero_of_apply_eq_zero_of_definite hA hV hW hmem hsub))
  haveI : FiniteDimensional ℂ ↥(V ⊔ W) := FiniteDimensional.of_injective f hf
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le (le_sup_left : V ≤ V ⊔ W)
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (le_sup_right : W ≤ V ⊔ W)
  refine ⟨inferInstance, inferInstance, ?_⟩
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h3 : V ⊓ W = ⊥ := disjoint_iff.mp (disjoint_of_definite hV hW)
  rw [h3, finrank_bot] at h2
  omega

/-- **Rank-two positive index bound.**  A self-adjoint operator of rank two with one strictly
negative quadratic value has no strictly positive subspace of dimension two. -/
theorem finrank_le_one_of_strictPositiveOn {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    [FiniteDimensional ℂ (LinearMap.range A.toLinearMap)]
    (hR : finrank ℂ (LinearMap.range A.toLinearMap) = 2)
    {m : E} (hm : reQuad A m < 0) {V : Submodule ℂ E} (hV : StrictPositiveOn A V) :
    FiniteDimensional ℂ V ∧ finrank ℂ V ≤ 1 := by
  obtain ⟨hVfd, _, hle⟩ :=
    finrank_add_finrank_le_finrank_range hA hV (strictNegativeOn_span_singleton hm)
  rw [hR, finrank_span_singleton (ne_zero_of_reQuad_neg hm)] at hle
  exact ⟨hVfd, by omega⟩

/-- **Rank-two negative index bound.**  A self-adjoint operator of rank two with one strictly
positive quadratic value has no strictly negative subspace of dimension two. -/
theorem finrank_le_one_of_strictNegativeOn {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    [FiniteDimensional ℂ (LinearMap.range A.toLinearMap)]
    (hR : finrank ℂ (LinearMap.range A.toLinearMap) = 2)
    {m : E} (hm : 0 < reQuad A m) {W : Submodule ℂ E} (hW : StrictNegativeOn A W) :
    FiniteDimensional ℂ W ∧ finrank ℂ W ≤ 1 := by
  obtain ⟨_, hWfd, hle⟩ :=
    finrank_add_finrank_le_finrank_range hA (strictPositiveOn_span_singleton hm) hW
  rw [hR, finrank_span_singleton (ne_zero_of_reQuad_pos hm)] at hle
  exact ⟨hWfd, by omega⟩

/-- **Exact hyperbolic-plane index.**  A self-adjoint operator of rank two carrying one strictly
positive and one strictly negative quadratic value has positive index exactly one and negative
index exactly one. -/
theorem rankTwo_mixed_exact_inertia {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    [FiniteDimensional ℂ (LinearMap.range A.toLinearMap)]
    (hR : finrank ℂ (LinearMap.range A.toLinearMap) = 2)
    {p m : E} (hp : 0 < reQuad A p) (hm : reQuad A m < 0) :
    (∀ V : Submodule ℂ E, StrictPositiveOn A V → FiniteDimensional ℂ V ∧ finrank ℂ V ≤ 1) ∧
    (∃ V : Submodule ℂ E, finrank ℂ V = 1 ∧ StrictPositiveOn A V) ∧
    (∀ W : Submodule ℂ E, StrictNegativeOn A W → FiniteDimensional ℂ W ∧ finrank ℂ W ≤ 1) ∧
    (∃ W : Submodule ℂ E, finrank ℂ W = 1 ∧ StrictNegativeOn A W) := by
  refine ⟨fun V hV => finrank_le_one_of_strictPositiveOn hA hR hm hV,
    ⟨ℂ ∙ p, finrank_span_singleton (ne_zero_of_reQuad_pos hp),
      strictPositiveOn_span_singleton hp⟩,
    fun W hW => finrank_le_one_of_strictNegativeOn hA hR hp hW,
    ⟨ℂ ∙ m, finrank_span_singleton (ne_zero_of_reQuad_neg hm),
      strictNegativeOn_span_singleton hm⟩⟩

end SelfAdjoint

/-! ## Stability of margin-definite subspaces under operator-norm perturbation -/

/-- The quadratic forms of two operators differ by at most `‖B - A‖ ‖y‖²`. -/
theorem reQuad_sub_le {A B : E →L[ℂ] E} (y : E) :
    reQuad B y - reQuad A y ≤ ‖B - A‖ * ‖y‖ ^ 2 := by
  have hrepr : reQuad B y - reQuad A y = (inner ℂ ((B - A) y) y : ℂ).re := by
    unfold reQuad
    rw [sub_apply, inner_sub_left, Complex.sub_re]
  rw [hrepr]
  calc (inner ℂ ((B - A) y) y : ℂ).re
      ≤ |(inner ℂ ((B - A) y) y : ℂ).re| := le_abs_self _
    _ ≤ ‖(inner ℂ ((B - A) y) y : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(B - A) y‖ * ‖y‖ := norm_inner_le_norm _ _
    _ ≤ (‖B - A‖ * ‖y‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right ((B - A).le_opNorm y) (norm_nonneg _)
    _ = ‖B - A‖ * ‖y‖ ^ 2 := by ring

/-- An `ε`-positive subspace of `B` is strictly positive for every `A` with `‖B - A‖ < ε`. -/
theorem strictPositiveOn_of_marginPositiveOn {A B : E →L[ℂ] E} {ε : ℝ} (hAB : ‖B - A‖ < ε)
    {V : Submodule ℂ E} (hB : MarginPositiveOn B ε V) : StrictPositiveOn A V := by
  intro y hy hy0
  have hεy := hB y hy hy0
  have hnorm : 0 < ‖y‖ ^ 2 := by positivity
  have hdiff := reQuad_sub_le (A := A) (B := B) y
  have hmul := mul_lt_mul_of_pos_right hAB hnorm
  linarith

/-- An `ε`-negative subspace of `B` is strictly negative for every `A` with `‖B - A‖ < ε`. -/
theorem strictNegativeOn_of_marginNegativeOn {A B : E →L[ℂ] E} {ε : ℝ} (hAB : ‖B - A‖ < ε)
    {W : Submodule ℂ E} (hB : MarginNegativeOn B ε W) : StrictNegativeOn A W := by
  intro y hy hy0
  have hεy := hB y hy hy0
  have hnorm : 0 < ‖y‖ ^ 2 := by positivity
  have hdiff := reQuad_sub_le (A := B) (B := A) y
  have hnormsym : ‖A - B‖ = ‖B - A‖ := norm_sub_rev _ _
  have hmul := mul_lt_mul_of_pos_right hAB hnorm
  rw [hnormsym] at hdiff
  linarith

/-- A vector with `ε`-positive quadratic value spans an `ε`-positive line. -/
theorem marginPositiveOn_span_singleton {B : E →L[ℂ] E} {ε : ℝ} {m : E}
    (hm : ε * ‖m‖ ^ 2 < reQuad B m) : MarginPositiveOn B ε (ℂ ∙ m) := by
  intro y hy hy0
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hy0
  have hc2 : 0 < ‖c‖ ^ 2 := by positivity
  rw [reQuad_smul, norm_smul, mul_pow]
  calc ε * (‖c‖ ^ 2 * ‖m‖ ^ 2) = ‖c‖ ^ 2 * (ε * ‖m‖ ^ 2) := by ring
    _ < ‖c‖ ^ 2 * reQuad B m := mul_lt_mul_of_pos_left hm hc2

/-- A vector with `ε`-negative quadratic value spans an `ε`-negative line. -/
theorem marginNegativeOn_span_singleton {B : E →L[ℂ] E} {ε : ℝ} {m : E}
    (hm : reQuad B m < -(ε * ‖m‖ ^ 2)) : MarginNegativeOn B ε (ℂ ∙ m) := by
  intro y hy hy0
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hy0
  have hc2 : 0 < ‖c‖ ^ 2 := by positivity
  rw [reQuad_smul, norm_smul, mul_pow]
  calc ‖c‖ ^ 2 * reQuad B m < ‖c‖ ^ 2 * (-(ε * ‖m‖ ^ 2)) := mul_lt_mul_of_pos_left hm hc2
    _ = -(ε * (‖c‖ ^ 2 * ‖m‖ ^ 2)) := by ring

/-- A vector with `ε`-positive quadratic value is nonzero. -/
theorem ne_zero_of_margin_pos {B : E →L[ℂ] E} {ε : ℝ} {m : E}
    (hm : ε * ‖m‖ ^ 2 < reQuad B m) : m ≠ 0 := by
  rintro rfl
  simp at hm

/-- A vector with `ε`-negative quadratic value is nonzero. -/
theorem ne_zero_of_margin_neg {B : E →L[ℂ] E} {ε : ℝ} {m : E}
    (hm : reQuad B m < -(ε * ‖m‖ ^ 2)) : m ≠ 0 := by
  rintro rfl
  simp at hm

section SelfAdjointStability

variable [CompleteSpace E]

/-- **Exact margin inertia of an approximant.**  If `A` is self-adjoint of rank two with one strictly
negative and one strictly positive quadratic value, and `B` is within operator-norm distance `ε` of
`A` while still carrying an `ε`-positive vector `p` and an `ε`-negative vector `m`, then the
`ε`-positive index and the `ε`-negative index of `B` are both exactly one. -/
theorem approximant_exact_margin_inertia {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    [FiniteDimensional ℂ (LinearMap.range A.toLinearMap)]
    (hR : finrank ℂ (LinearMap.range A.toLinearMap) = 2)
    {p₀ m₀ : E} (hp₀ : 0 < reQuad A p₀) (hm₀ : reQuad A m₀ < 0)
    {ε : ℝ} (hAB : ‖B - A‖ < ε)
    {p m : E} (hp : ε * ‖p‖ ^ 2 < reQuad B p) (hm : reQuad B m < -(ε * ‖m‖ ^ 2)) :
    (∀ V : Submodule ℂ E, MarginPositiveOn B ε V →
        FiniteDimensional ℂ V ∧ finrank ℂ V ≤ 1) ∧
    (∃ V : Submodule ℂ E, finrank ℂ V = 1 ∧ MarginPositiveOn B ε V) ∧
    (∀ W : Submodule ℂ E, MarginNegativeOn B ε W →
        FiniteDimensional ℂ W ∧ finrank ℂ W ≤ 1) ∧
    (∃ W : Submodule ℂ E, finrank ℂ W = 1 ∧ MarginNegativeOn B ε W) := by
  refine ⟨fun V hV => ?_, ⟨ℂ ∙ p, finrank_span_singleton (ne_zero_of_margin_pos hp),
      marginPositiveOn_span_singleton hp⟩, fun W hW => ?_,
    ⟨ℂ ∙ m, finrank_span_singleton (ne_zero_of_margin_neg hm),
      marginNegativeOn_span_singleton hm⟩⟩
  · exact finrank_le_one_of_strictPositiveOn hA hR hm₀
      (strictPositiveOn_of_marginPositiveOn hAB hV)
  · exact finrank_le_one_of_strictNegativeOn hA hR hp₀
      (strictNegativeOn_of_marginNegativeOn hAB hW)

end SelfAdjointStability

end

end GaloisForLFunctions.HTGeometry
