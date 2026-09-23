import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Off-axis resolvents of a skew generator on a smooth graph core

A skew-symmetric operator has purely imaginary numerical range, so for `Re z ≠ 0` the operator
`A - z` is bounded below by `|Re z|`.  Consequently any right inverse of `A - z` — the Hilbert
resolvent `R_z`, whose existence is what skew-adjointness supplies — obeys
`‖R_z y‖ ≤ |Re z|⁻¹ ‖y‖`.

The smooth graph core of a family of partially defined graph monomials is the intersection of
their domains, with graph seminorms given by their norms.  A resolvent that commutes with every
monomial preserves the core and contracts every graph seminorm by the same factor, so `A - z` is
a continuous linear automorphism of the core with continuous inverse `R_z`.

* `deningerSkew_lower_bound` : `|Re z| ‖x‖ ≤ ‖(A - z)x‖`.
* `deningerSkew_resolvent_norm_le` : `‖R_z y‖ ≤ |Re z|⁻¹ ‖y‖`.
* `deningerGraphSeminorm_resolvent_le` : the graph-seminorm estimate.
* `deningerCoreSub_bijective` : `A - z` is a bijection of the core.
-/

namespace RHTower

section SkewLowerBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A linear map defined on a subspace is skew-symmetric when `⟪Ax, y⟫ = -⟪x, Ay⟫`. -/
def DeningerSkewSymmetric {D : Submodule ℂ E} (A : D →ₗ[ℂ] E) : Prop :=
  ∀ x y : D, (inner ℂ (A x) (y : E) : ℂ) = -(inner ℂ (x : E) (A y) : ℂ)

variable {D : Submodule ℂ E} {A : D →ₗ[ℂ] E}

/-- The numerical range of a skew-symmetric operator is purely imaginary. -/
theorem deningerSkew_re_inner_self (hA : DeningerSkewSymmetric A) (x : D) :
    (inner ℂ (A x) (x : E) : ℂ).re = 0 := by
  have h := hA x x
  have hconj : (inner ℂ (x : E) (A x) : ℂ) = starRingEnd ℂ (inner ℂ (A x) (x : E)) := by
    rw [inner_conj_symm]
  rw [hconj] at h
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

/-- The real part of the shifted numerical value. -/
theorem deningerSkew_re_inner_sub (hA : DeningerSkewSymmetric A) (z : ℂ) (x : D) :
    (inner ℂ (A x - z • (x : E)) (x : E) : ℂ).re = -z.re * ‖(x : E)‖ ^ (2 : ℕ) := by
  rw [inner_sub_left, inner_smul_left]
  have hself : (inner ℂ (x : E) (x : E) : ℂ) = ((‖(x : E)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hself]
  simp only [Complex.sub_re, deningerSkew_re_inner_self hA x, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The off-axis lower bound.**  A skew-symmetric operator shifted off the imaginary axis is
bounded below by the distance to that axis. -/
theorem deningerSkew_lower_bound (hA : DeningerSkewSymmetric A) (z : ℂ) (x : D) :
    |z.re| * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖ := by
  rcases eq_or_ne (x : E) 0 with h0 | h0
  · rw [h0]
    simp
  · have hx : 0 < ‖(x : E)‖ := norm_pos_iff.mpr h0
    have hcs : |(inner ℂ (A x - z • (x : E)) (x : E) : ℂ).re|
        ≤ ‖A x - z • (x : E)‖ * ‖(x : E)‖ := by
      refine le_trans ?_ (norm_inner_le_norm (𝕜 := ℂ) (A x - z • (x : E)) ((x : E)))
      simpa [RCLike.re_to_complex] using
        RCLike.abs_re_le_norm (K := ℂ) (inner ℂ (A x - z • (x : E)) ((x : E)))
    rw [deningerSkew_re_inner_sub hA z x] at hcs
    have habs : |(-z.re * ‖(x : E)‖ ^ (2 : ℕ))| = |z.re| * ‖(x : E)‖ ^ (2 : ℕ) := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖(x : E)‖ ^ (2 : ℕ))]
    rw [habs] at hcs
    nlinarith [hcs, hx]

/-- **The resolvent estimate.**  Any right inverse of `A - z` on the domain of `A` is bounded by
the reciprocal distance to the imaginary axis. -/
theorem deningerSkew_resolvent_norm_le (hA : DeningerSkewSymmetric A) {z : ℂ} (hz : z.re ≠ 0)
    (R : E → D) (hR : ∀ y : E, A (R y) - z • ((R y : D) : E) = y) (y : E) :
    ‖((R y : D) : E)‖ ≤ |z.re|⁻¹ * ‖y‖ := by
  have habs : 0 < |z.re| := abs_pos.mpr hz
  have h := deningerSkew_lower_bound hA z (R y)
  rw [hR y] at h
  rw [inv_mul_eq_div, le_div_iff₀ habs, mul_comm]
  exact h

end SkewLowerBound

section GraphCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

/-- The common smooth graph core of a family of partially defined graph monomials. -/
def deningerGraphCore (P : ι → (E →ₗ.[ℂ] E)) : Submodule ℂ E :=
  ⨅ i, (P i).domain

theorem mem_deningerGraphCore {P : ι → (E →ₗ.[ℂ] E)} {x : E} :
    x ∈ deningerGraphCore P ↔ ∀ i, x ∈ (P i).domain := by
  simp [deningerGraphCore, Submodule.mem_iInf]

/-- The graph seminorm attached to one monomial. -/
noncomputable def deningerGraphSeminorm (P : ι → (E →ₗ.[ℂ] E)) (i : ι)
    {x : E} (hx : x ∈ deningerGraphCore P) : ℝ :=
  ‖(P i) ⟨x, mem_deningerGraphCore.mp hx i⟩‖

/-- A map that commutes with every graph monomial on that monomial's domain. -/
structure DeningerGraphCommuting (P : ι → (E →ₗ.[ℂ] E)) (R : E →ₗ[ℂ] E) : Prop where
  /-- Every monomial domain is preserved. -/
  mapsTo : ∀ (i : ι) (x : E), x ∈ (P i).domain → R x ∈ (P i).domain
  /-- The monomial commutes with the map. -/
  commutes : ∀ (i : ι) (x : E) (hx : x ∈ (P i).domain),
    (P i) ⟨R x, mapsTo i x hx⟩ = R ((P i) ⟨x, hx⟩)

variable {P : ι → (E →ₗ.[ℂ] E)} {R : E →ₗ[ℂ] E}

/-- **The graph core is preserved.** -/
theorem deningerGraphCore_map_mem (h : DeningerGraphCommuting P R)
    {x : E} (hx : x ∈ deningerGraphCore P) : R x ∈ deningerGraphCore P :=
  mem_deningerGraphCore.mpr fun i => h.mapsTo i x (mem_deningerGraphCore.mp hx i)

/-- **The graph-seminorm estimate.**  A resolvent bound on the ambient space passes to every
graph seminorm of the core, with the same constant. -/
theorem deningerGraphSeminorm_resolvent_le (h : DeningerGraphCommuting P R) {c : ℝ}
    (hc : ∀ y : E, ‖R y‖ ≤ c * ‖y‖) (i : ι) {x : E} (hx : x ∈ deningerGraphCore P) :
    deningerGraphSeminorm P i (deningerGraphCore_map_mem h hx)
      ≤ c * deningerGraphSeminorm P i hx := by
  have hxi : x ∈ (P i).domain := mem_deningerGraphCore.mp hx i
  have hcomm : (P i) ⟨R x, h.mapsTo i x hxi⟩ = R ((P i) ⟨x, hxi⟩) := h.commutes i x hxi
  show ‖(P i) ⟨R x, _⟩‖ ≤ c * ‖(P i) ⟨x, _⟩‖
  rw [hcomm]
  exact hc _

end GraphCore

section CoreAutomorphism

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {C : Submodule ℂ E}

/-- **`A - z` is a bijection of the core.**  Any two-sided inverse on the core exhibits the
shifted generator as an automorphism of it. -/
theorem deningerCoreSub_bijective (S T : C →ₗ[ℂ] C)
    (hleft : ∀ x, T (S x) = x) (hright : ∀ y, S (T y) = y) :
    Function.Bijective (S : C → C) :=
  Function.bijective_iff_has_inverse.mpr ⟨T, hleft, hright⟩

/-- The inverse of the shifted generator on the core is the restriction of the resolvent. -/
noncomputable def deningerCoreEquiv (S T : C →ₗ[ℂ] C)
    (hleft : ∀ x, T (S x) = x) (hright : ∀ y, S (T y) = y) : C ≃ₗ[ℂ] C :=
  LinearEquiv.ofLinear S T (LinearMap.ext hright) (LinearMap.ext hleft)

@[simp] theorem deningerCoreEquiv_apply (S T : C →ₗ[ℂ] C)
    (hleft : ∀ x, T (S x) = x) (hright : ∀ y, S (T y) = y) (x : C) :
    deningerCoreEquiv S T hleft hright x = S x := rfl

@[simp] theorem deningerCoreEquiv_symm_apply (S T : C →ₗ[ℂ] C)
    (hleft : ∀ x, T (S x) = x) (hright : ∀ y, S (T y) = y) (x : C) :
    (deningerCoreEquiv S T hleft hright).symm x = T x := rfl

end CoreAutomorphism

end RHTower
