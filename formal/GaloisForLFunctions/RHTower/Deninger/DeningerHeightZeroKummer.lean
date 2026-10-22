import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The height-zero theorem and the bounded Kummer functional

Kronecker's theorem in height form: a nonzero element of a number field has height one — that is,
logarithmic height zero — exactly when it is a root of unity.  The Northcott property makes all
its powers lie in one finite set, so two powers coincide and the element has finite order; the
converse is the power law for the height.

Consequently a Kummer class map whose Hilbert norm is a positive multiple of the logarithmic
height annihilates exactly the roots of unity, which is the injectivity of the Kummer embedding.

A functional prescribed on a subspace and bounded by the Hilbert norm extends to a bounded
functional on the whole space by Hahn--Banach, and the extension is determined on the closed span
of that subspace, because the equalizer of two continuous functionals is a closed submodule.

* `deningerMulHeightOne_iff_isOfFinOrder`, `deningerLogHeightZero_iff_isOfFinOrder` : the
  height-zero theorem.
* `deningerKummerClass_eq_zero_iff` : injectivity of the Kummer class map.
* `deningerHilbertKummerBounded_extend` : the unique bounded functional attached to a bounded
  logarithmic modulus on a dense span.
* `deningerClosedSpan_eqOn`, `deningerHilbertKummerBounded_extend_closedSpan` : the same without a
  density hypothesis, on the closed span.
-/

namespace RHTower

section HeightZero

variable {K : Type*} [Field K] [NumberField K]

/-- **The height-zero theorem (Kronecker).**  A nonzero element of a number field has
multiplicative height one exactly when it is a root of unity. -/
theorem deningerMulHeightOne_iff_isOfFinOrder {x : K} (hx : x ≠ 0) :
    Height.mulHeight₁ x = 1 ↔ IsOfFinOrder x := by
  constructor
  · intro h
    have hS := NumberField.finite_setOf_mulHeight₁_le K 1
    haveI : Finite {y : K | Height.mulHeight₁ y ≤ 1} := hS.to_subtype
    have hmem : ∀ n : ℕ, x ^ n ∈ {y : K | Height.mulHeight₁ y ≤ 1} := by
      intro n
      simp only [Set.mem_setOf_eq, Height.mulHeight₁_pow, h, one_pow, le_refl]
    obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => (⟨x ^ n, hmem n⟩ : {y : K | Height.mulHeight₁ y ≤ 1}))
    have hxx : x ^ a = x ^ b := congrArg Subtype.val hfab
    have key : ∀ p q : ℕ, p < q → x ^ p = x ^ q → IsOfFinOrder x := by
      intro p q hlt hpq
      refine isOfFinOrder_iff_pow_eq_one.mpr ⟨q - p, Nat.sub_pos_of_lt hlt, ?_⟩
      have h2 : x ^ p * x ^ (q - p) = x ^ p * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le, ← hpq, mul_one]
      exact mul_left_cancel₀ (pow_ne_zero p hx) h2
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact key a b hlt hxx
    · exact key b a hlt hxx.symm
  · intro h
    obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp h
    have h1 : Height.mulHeight₁ x ^ n = 1 := by
      rw [← Height.mulHeight₁_pow, hxn, Height.mulHeight₁_one]
    have hlog : (n : ℝ) * Real.log (Height.mulHeight₁ x) = 0 := by
      rw [← Real.log_pow, h1, Real.log_one]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hzero := (mul_eq_zero.mp hlog).resolve_left hn'
    have hexp := congrArg Real.exp hzero
    rwa [Real.exp_log (Height.mulHeight₁_pos x), Real.exp_zero] at hexp

/-- **The height-zero theorem, logarithmic form.** -/
theorem deningerLogHeightZero_iff_isOfFinOrder {x : K} (hx : x ≠ 0) :
    Height.logHeight₁ x = 0 ↔ IsOfFinOrder x := by
  rw [Height.logHeight₁_eq_log_mulHeight₁, ← deningerMulHeightOne_iff_isOfFinOrder hx]
  constructor
  · intro h
    have hexp := congrArg Real.exp h
    rwa [Real.exp_log (Height.mulHeight₁_pos x), Real.exp_zero] at hexp
  · intro h
    rw [h, Real.log_one]

/-- **Injectivity of the Kummer class map.**  If the Hilbert norm of the class of `x` is a
positive multiple of its logarithmic height, then the class map annihilates exactly the roots of
unity, so it is injective on the quotient by the torsion subgroup. -/
theorem deningerKummerClass_eq_zero_iff {H : Type*} [NormedAddCommGroup H] (f : K → H) {c : ℝ}
    (hc : 0 < c) (hf : ∀ y : K, ‖f y‖ = c * Height.logHeight₁ y) {x : K} (hx : x ≠ 0) :
    f x = 0 ↔ IsOfFinOrder x := by
  rw [← deningerLogHeightZero_iff_isOfFinOrder hx, ← norm_eq_zero (a := f x), hf x,
    mul_eq_zero]
  constructor
  · intro h
    exact h.resolve_left hc.ne'
  · intro h
    exact Or.inr h

end HeightZero

section BoundedFunctional

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **The bounded functional attached to a bounded logarithmic modulus.**  A linear functional on
the span of a total set, bounded by the ambient norm, extends to a bounded functional on the whole
space, and the extension is unique because the span is dense.  Existence is Hahn--Banach;
uniqueness is that two continuous maps agreeing on a dense set are equal. -/
theorem deningerHilbertKummerBounded_extend {s : Set H}
    (hdense : Dense (Submodule.span ℝ s : Set H)) (φ : (Submodule.span ℝ s) →ₗ[ℝ] ℝ) (C : ℝ)
    (hφ : ∀ w : Submodule.span ℝ s, |φ w| ≤ C * ‖(w : H)‖) :
    ∃! L : H →L[ℝ] ℝ, ∀ w : Submodule.span ℝ s, L (w : H) = φ w := by
  have hbound : ∀ w : Submodule.span ℝ s, ‖φ w‖ ≤ C * ‖w‖ := by
    intro w
    simpa [Real.norm_eq_abs] using hφ w
  obtain ⟨L, hL, -⟩ := exists_extension_norm_eq (𝕜 := ℝ) (Submodule.span ℝ s)
    (φ.mkContinuous C hbound)
  refine ⟨L, fun w => hL w, fun L' hL' => ?_⟩
  refine ContinuousLinearMap.ext_on hdense ?_
  intro y hy
  have hymem : y ∈ Submodule.span ℝ s := Submodule.subset_span hy
  have h1 : L' y = φ ⟨y, hymem⟩ := hL' ⟨y, hymem⟩
  have h2 : L y = φ ⟨y, hymem⟩ := hL ⟨y, hymem⟩
  rw [h1, h2]

/-- **Two bounded functionals agreeing on a set agree on its closed span.**  The equalizer is a
closed submodule containing the set, hence contains the closure of the span.  No density
hypothesis is needed: the closed span is exactly the space on which the extension is determined. -/
theorem deningerClosedSpan_eqOn {s : Set H} {L₁ L₂ : H →L[ℝ] ℝ} (h : Set.EqOn L₁ L₂ s) :
    Set.EqOn L₁ L₂ ((Submodule.span ℝ s).topologicalClosure : Set H) := by
  have hspan : Submodule.span ℝ s ≤ LinearMap.eqLocus (L₁ : H →ₗ[ℝ] ℝ) (L₂ : H →ₗ[ℝ] ℝ) :=
    Submodule.span_le.mpr h
  have hclosed : IsClosed ((LinearMap.eqLocus (L₁ : H →ₗ[ℝ] ℝ) (L₂ : H →ₗ[ℝ] ℝ) : Set H)) :=
    isClosed_eq L₁.continuous L₂.continuous
  intro y hy
  exact Submodule.topologicalClosure_minimal _ hspan hclosed hy

/-- **The bounded Kummer functional, without a density hypothesis.**  A logarithmic modulus
bounded by the Hilbert norm on the Kummer classes extends to a bounded functional on the ambient
space, and any two such extensions agree on the *closed* span of the classes — which is the
Hilbert--Kummer space itself. -/
theorem deningerHilbertKummerBounded_extend_closedSpan {s : Set H}
    (φ : (Submodule.span ℝ s) →ₗ[ℝ] ℝ) (C : ℝ)
    (hφ : ∀ w : Submodule.span ℝ s, |φ w| ≤ C * ‖(w : H)‖) :
    ∃ L : H →L[ℝ] ℝ, (∀ w : Submodule.span ℝ s, L (w : H) = φ w) ∧
      ∀ L' : H →L[ℝ] ℝ, (∀ w : Submodule.span ℝ s, L' (w : H) = φ w) →
        Set.EqOn L L' ((Submodule.span ℝ s).topologicalClosure : Set H) := by
  have hbound : ∀ w : Submodule.span ℝ s, ‖φ w‖ ≤ C * ‖w‖ := by
    intro w
    simpa [Real.norm_eq_abs] using hφ w
  obtain ⟨L, hL, -⟩ := exists_extension_norm_eq (𝕜 := ℝ) (Submodule.span ℝ s)
    (φ.mkContinuous C hbound)
  refine ⟨L, fun w => hL w, fun L' hL' => deningerClosedSpan_eqOn ?_⟩
  intro y hy
  have hymem : y ∈ Submodule.span ℝ s := Submodule.subset_span hy
  rw [hL ⟨y, hymem⟩, hL' ⟨y, hymem⟩]
  rfl

end BoundedFunctional

end RHTower
