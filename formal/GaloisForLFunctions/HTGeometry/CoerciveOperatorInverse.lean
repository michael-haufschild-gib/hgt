import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# A coercive bounded operator is boundedly invertible

If a bounded operator on a Hilbert space has a strictly positive numerical-range floor,

`c‖u‖² ≤ Re⟪A u, u⟫`,   `c > 0`,

then it is bounded below, so it is injective with closed range; and its range has trivial
orthogonal complement, because a vector orthogonal to the range is orthogonal to its own image.
Hence `A` is a linear homeomorphism, and the bound below transfers verbatim to the inverse:

`‖A⁻¹‖ ≤ c⁻¹`.

The point is that the floor is *all* that is used: no self-adjointness, no normality, no spectral
theory.  For a shifted operator `B + L·I` whose scalar part has real part growing like `log(1+|x|)`
this is exactly the resolvent bound `‖(B + L)⁻¹‖ ≤ 1/(log(1+|x|) + L − C)` in which the shift, not
any structure of `B`, does the work.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- **The numerical floor bounds the operator below.** -/
theorem norm_le_of_coercive {A : X →L[ℂ] X} {c : ℝ}
    (hcoe : ∀ u : X, c * ‖u‖ ^ 2 ≤ (inner ℂ (A u) u).re) (u : X) :
    c * ‖u‖ ≤ ‖A u‖ := by
  rcases eq_or_lt_of_le (norm_nonneg u) with hu | hu
  · rw [← hu, mul_zero]
    exact norm_nonneg _
  · have hup : (inner ℂ (A u) u).re ≤ ‖A u‖ * ‖u‖ :=
      le_trans (Complex.re_le_norm _) (norm_inner_le_norm (𝕜 := ℂ) (A u) u)
    have hkey : c * ‖u‖ * ‖u‖ ≤ ‖A u‖ * ‖u‖ := by
      have := hcoe u
      nlinarith [this, hup]
    exact le_of_mul_le_mul_right hkey hu

omit [CompleteSpace X] in
/-- A vector orthogonal to the range of a coercive operator is zero. -/
theorem eq_zero_of_mem_orthogonal_range {A : X →L[ℂ] X} {c : ℝ} (hc : 0 < c)
    (hcoe : ∀ u : X, c * ‖u‖ ^ 2 ≤ (inner ℂ (A u) u).re)
    {v : X} (hv : v ∈ (LinearMap.range (A : X →ₗ[ℂ] X))ᗮ) : v = 0 := by
  have hzero : (inner ℂ (A v) v : ℂ) = 0 :=
    hv (A v) ⟨v, rfl⟩
  have := hcoe v
  rw [hzero] at this
  simp only [Complex.zero_re] at this
  have hnn : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v, sq_nonneg ‖v‖]
  exact norm_eq_zero.mp this

/-- **A coercive operator has a bounded inverse with the reciprocal bound.** -/
theorem exists_inverse_of_coercive {A : X →L[ℂ] X} {c : ℝ} (hc : 0 < c)
    (hcoe : ∀ u : X, c * ‖u‖ ^ 2 ≤ (inner ℂ (A u) u).re) :
    ∃ S : X →L[ℂ] X, (∀ v, A (S v) = v) ∧ (∀ u, S (A u) = u) ∧ ∀ v, ‖S v‖ ≤ c⁻¹ * ‖v‖ := by
  have hlow : ∀ u : X, c * ‖u‖ ≤ ‖A u‖ := norm_le_of_coercive hcoe
  -- injectivity
  have hinj : Function.Injective A := by
    intro x y hxy
    have hsub : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have := hlow (x - y)
    rw [hsub, norm_zero] at this
    have : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
    have hz : x - y = 0 := norm_le_zero_iff.mp this
    exact sub_eq_zero.mp hz
  -- closed range
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) (A : X → X) := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have hsub : A x - A y = A (x - y) := (map_sub A x y).symm
    have hbase := hlow (x - y)
    rw [dist_eq_norm, dist_eq_norm, hsub]
    rw [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ c⁻¹)]
    rw [← le_div_iff₀' (by positivity : (0 : ℝ) < c)] at hbase
    calc ‖x - y‖ ≤ ‖A (x - y)‖ / c := hbase
      _ = c⁻¹ * ‖A (x - y)‖ := by ring
  have hclosedset : IsClosed (Set.range (A : X → X)) :=
    hanti.isClosed_range A.uniformContinuous
  have hclosed : IsClosed ((LinearMap.range (A : X →ₗ[ℂ] X) : Submodule ℂ X) : Set X) := by
    convert hclosedset using 1
    ext x
    simp [LinearMap.mem_range]
  -- full range
  haveI hcomplete : CompleteSpace (LinearMap.range (A : X →ₗ[ℂ] X)) :=
    hclosed.completeSpace_coe
  have hperp : (LinearMap.range (A : X →ₗ[ℂ] X))ᗮ = ⊥ := by
    refine Submodule.eq_bot_iff _ |>.mpr fun v hv => ?_
    exact eq_zero_of_mem_orthogonal_range hc hcoe hv
  have htop : LinearMap.range (A : X →ₗ[ℂ] X) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    exact hperp
  have hker : LinearMap.ker (A : X →ₗ[ℂ] X) = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  -- the inverse
  let E : X ≃L[ℂ] X := ContinuousLinearEquiv.ofBijective A hker htop
  have hEA : ∀ x : X, E x = A x := fun _ => rfl
  refine ⟨(E.symm : X →L[ℂ] X), ?_, ?_, ?_⟩
  · intro v
    rw [← hEA]
    exact E.apply_symm_apply v
  · intro u
    have : E.symm (E u) = u := E.symm_apply_apply u
    rw [hEA] at this
    exact this
  · intro v
    have hbase := hlow (E.symm v)
    have hAv : A (E.symm v) = v := by
      rw [← hEA]
      exact E.apply_symm_apply v
    rw [hAv] at hbase
    rw [← le_div_iff₀' (by positivity : (0 : ℝ) < c)] at hbase
    calc ‖(E.symm : X →L[ℂ] X) v‖ = ‖E.symm v‖ := rfl
      _ ≤ ‖v‖ / c := hbase
      _ = c⁻¹ * ‖v‖ := by ring

/-! ## The shifted form used by the Gamma-wall resolvent -/

/-- **The shift produces the floor.**  If the scalar part of `B` has real part at least `μ` and the
remaining part is self-adjoint and bounded by `τ`, the shifted operator `B + L·I` has floor
`μ + L − τ`, and the resolvent bound is its reciprocal. -/
theorem exists_inverse_of_shifted {B : X →L[ℂ] X} {μ τ L : ℝ}
    (hfloor : ∀ u : X, μ * ‖u‖ ^ 2 ≤ (inner ℂ (B u) u).re + τ * ‖u‖ ^ 2)
    (hgap : 0 < μ + L - τ) :
    ∃ S : X →L[ℂ] X,
      (∀ v, (B + (L : ℂ) • ContinuousLinearMap.id ℂ X) (S v) = v) ∧
      (∀ u, S ((B + (L : ℂ) • ContinuousLinearMap.id ℂ X) u) = u) ∧
      ∀ v, ‖S v‖ ≤ (μ + L - τ)⁻¹ * ‖v‖ := by
  set A : X →L[ℂ] X := B + (L : ℂ) • ContinuousLinearMap.id ℂ X with hA
  have hcoe : ∀ u : X, (μ + L - τ) * ‖u‖ ^ 2 ≤ (inner ℂ (A u) u).re := by
    intro u
    have hAu : A u = B u + (L : ℂ) • u := by
      rw [hA]
      simp
    have hshift : (inner ℂ (A u) u : ℂ)
        = inner ℂ (B u) u + ((L * ‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [hAu, inner_add_left, inner_smul_left, Complex.conj_ofReal,
        inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [hshift]
    simp only [Complex.add_re, Complex.ofReal_re]
    have := hfloor u
    linarith
  exact exists_inverse_of_coercive hgap hcoe

end GaloisForLFunctions.HTGeometry
