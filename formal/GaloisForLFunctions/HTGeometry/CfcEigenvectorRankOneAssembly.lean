import GaloisForLFunctions.HTGeometry.SelfAdjointFunctionalCalculusLowerBound

/-!
# Functional calculus on an eigenvector and the rank-one spectral assembly bound

For a bounded self-adjoint operator `A` on a complex Hilbert space with `A x = c • x` (`c` real)
and a real continuous function `g` on the spectrum, `g(A) x = g(c) • x`: the continuous functions
with this property form a closed subalgebra of `C(σ(A), ℝ)` containing the identity function, so
Stone–Weierstrass makes it everything.

Combined with the quadratic-form lower bound `c‖f‖² ≤ Re⟪g(A)f, f⟫`, this gives the rank-one
assembly inequality: if `A e = e` and `c ≤ g` on the spectrum, then for every vector `F`

`g(1)·|⟪e,F⟫|²/‖e‖² + c·‖F − P_e F‖² ≤ Re⟪g(A)F, F⟫`,

where `P_e` is the orthogonal projection onto the line through `e`.  The constant-mode weight and
the orthogonal remainder separate exactly, with no spectral measure.
-/

open scoped InnerProductSpace
open Topology

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A real eigenvalue of a nonzero eigenvector lies in the real spectrum. -/
theorem mem_spectrum_of_eigenvector (A : H →L[ℂ] H) {c : ℝ} {x : H}
    (hx : A x = (c : ℂ) • x) (hx0 : x ≠ 0) : c ∈ spectrum ℝ A := by
  rw [spectrum.mem_iff]
  intro hu
  apply hx0
  have hzero : (algebraMap ℝ (H →L[ℂ] H) c - A) x = 0 := by
    rw [sub_apply, hx, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, sub_eq_zero]
    exact RCLike.real_smul_eq_coe_smul c x
  rcases hu with ⟨u, hu⟩
  have h1 : ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) ((u : H →L[ℂ] H) x) = x := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, Units.inv_mul,
      one_apply_eq_self]
  rw [← h1, hu, hzero, map_zero]

/-- **Functional calculus on an eigenvector.**  If `A x = c • x` with `c` real then
`g(A) x = g(c) • x` for every real continuous `g` on the spectrum. -/
theorem cfc_apply_eigenvector_rankOne (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {c : ℝ} {x : H}
    (hx : A x = (c : ℂ) • x) {g : ℝ → ℝ} (hg : ContinuousOn g (spectrum ℝ A)) :
    cfc g A x = ((g c : ℝ) : ℂ) • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hc : c ∈ spectrum ℝ A := mem_spectrum_of_eigenvector A hx hx0
  set σ := spectrum ℝ A with hσ
  let cσ : σ := ⟨c, hc⟩
  -- the subalgebra of continuous functions acting on `x` by their value at `c`
  let S : Subalgebra ℝ C(σ, ℝ) :=
    { carrier := {φ | cfcHom hA φ x = ((φ cσ : ℝ) : ℂ) • x}
      mul_mem' := by
        intro φ ψ hφ hψ
        simp only [Set.mem_setOf_eq] at hφ hψ ⊢
        rw [map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hψ, map_smul, hφ, smul_smul,
          ContinuousMap.mul_apply, Complex.ofReal_mul, mul_comm]
      add_mem' := by
        intro φ ψ hφ hψ
        simp only [Set.mem_setOf_eq] at hφ hψ ⊢
        rw [map_add, add_apply, hφ, hψ, ContinuousMap.add_apply,
          Complex.ofReal_add, add_smul]
      algebraMap_mem' := by
        intro r
        simp only [Set.mem_setOf_eq]
        have h1 : (algebraMap ℝ C(σ, ℝ) r) cσ = r := by
          simp [Algebra.algebraMap_eq_smul_one]
        rw [h1, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self]
        exact RCLike.real_smul_eq_coe_smul r x }
  have hclosed : IsClosed (S : Set C(σ, ℝ)) := by
    apply isClosed_eq
    · exact (ContinuousLinearMap.apply ℂ H x).continuous.comp
        (cfcHom_isClosedEmbedding hA).continuous
    · exact (Complex.continuous_ofReal.comp (continuous_eval_const cσ)).smul
        continuous_const
  have hX : Polynomial.toContinuousMapOnAlgHom σ Polynomial.X ∈ S := by
    show cfcHom hA _ x = _
    have hid : Polynomial.toContinuousMapOnAlgHom σ Polynomial.X =
        ContinuousMap.restrict σ (ContinuousMap.id ℝ) := by
      ext z; simp
    rw [hid, cfcHom_id hA, hx]
    simp [cσ]
  have hpoly : polynomialFunctions σ ≤ S := by
    rw [polynomialFunctions.eq_adjoin_X]
    exact Algebra.adjoin_le (by simpa using hX)
  have htop : (⊤ : Subalgebra ℝ C(σ, ℝ)) ≤ S := by
    rw [← polynomialFunctions.topologicalClosure σ]
    exact Subalgebra.topologicalClosure_minimal hpoly hclosed
  have hmem : (⟨σ.restrict g, hg.restrict⟩ : C(σ, ℝ)) ∈ S := htop Algebra.mem_top
  rw [cfc_apply g A hA hg]
  exact hmem

/-- **Rank-one spectral assembly.**  For a bounded self-adjoint `A` with `A e = e`, `e ≠ 0`, and a
real continuous `g ≥ c` on the spectrum, the quadratic form of `g(A)` on any vector `F` is at least
the eigenvector weight `g(1)·|⟪e,F⟫|²/‖e‖²` plus `c` times the squared norm of the component of
`F` orthogonal to `e`. -/
theorem re_inner_cfc_self_ge_rankOne (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {e : H}
    (he : A e = e) (he0 : e ≠ 0) {g : ℝ → ℝ} (hg : ContinuousOn g (spectrum ℝ A)) {c : ℝ}
    (hc : ∀ x ∈ spectrum ℝ A, c ≤ g x) (F : H) :
    g 1 * (‖⟪e, F⟫_ℂ‖ ^ 2 / ‖e‖ ^ 2) + c * ‖F - (ℂ ∙ e).starProjection F‖ ^ 2 ≤
      RCLike.re ⟪cfc g A F, F⟫_ℂ := by
  set T := cfc g A with hT
  have hTsa : IsSelfAdjoint T := IsSelfAdjoint.cfc
  have hTe : T e = ((g 1 : ℝ) : ℂ) • e := by
    have h1 : A e = ((1 : ℝ) : ℂ) • e := by rw [he]; simp
    exact cfc_apply_eigenvector_rankOne A hA h1 hg
  set a : ℂ := ⟪e, F⟫_ℂ / ((‖e‖ ^ 2 : ℝ) : ℂ) with ha
  set Q := F - (ℂ ∙ e).starProjection F with hQ
  have hP : (ℂ ∙ e).starProjection F = a • e := Submodule.starProjection_singleton ℂ F
  have hF : F = a • e + Q := by rw [hQ, hP]; abel
  have hne : (‖e‖ ^ 2 : ℝ) ≠ 0 := by
    have := norm_pos_iff.mpr he0
    positivity
  have hQe : ⟪Q, e⟫_ℂ = 0 :=
    Submodule.starProjection_inner_eq_zero F e (Submodule.mem_span_singleton_self e)
  have heQ : ⟪e, Q⟫_ℂ = 0 := by
    rw [← inner_conj_symm, hQe, map_zero]
  have hTP : T (a • e) = ((g 1 : ℝ) : ℂ) • (a • e) := by
    rw [map_smul, hTe, smul_comm]
  have hTQ : ⟪T (a • e), Q⟫_ℂ = 0 := by
    rw [hTP, inner_smul_left, inner_smul_left, heQ, mul_zero, mul_zero]
  have hQT : ⟪T Q, a • e⟫_ℂ = 0 := by
    have h := ContinuousLinearMap.adjoint_inner_left T (a • e) Q
    rw [hTsa.adjoint_eq] at h
    rw [h, hTP, inner_smul_right, inner_smul_right, hQe, mul_zero, mul_zero]
  have hPP : RCLike.re ⟪T (a • e), a • e⟫_ℂ = g 1 * (‖⟪e, F⟫_ℂ‖ ^ 2 / ‖e‖ ^ 2) := by
    have hnorm : ‖a • e‖ ^ 2 = ‖⟪e, F⟫_ℂ‖ ^ 2 / ‖e‖ ^ 2 := by
      have h2 : ‖(((‖e‖ ^ 2 : ℝ)) : ℂ)‖ = ‖e‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [norm_smul, ha, norm_div, h2, mul_pow, div_pow]
      field_simp
    rw [hTP, inner_smul_left, inner_self_eq_norm_sq_to_K, ← hnorm]
    simp [← Complex.ofReal_pow]
  have hsplit : RCLike.re ⟪T F, F⟫_ℂ =
      RCLike.re ⟪T (a • e), a • e⟫_ℂ + RCLike.re ⟪T Q, Q⟫_ℂ := by
    conv_lhs => rw [hF]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hTQ, hQT]
    simp only [add_zero, zero_add, map_add]
  have hlow := re_inner_cfc_self_ge A hA hg hc Q
  rw [hsplit, hPP]
  linarith

end GaloisForLFunctions.HTGeometry
