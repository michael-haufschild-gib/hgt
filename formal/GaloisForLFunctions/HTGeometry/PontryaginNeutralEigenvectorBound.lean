import Mathlib

/-!
# Upper-half-plane eigenvalues of a self-adjoint operator in a space of finite negative index

Let `B` be a sesquilinear form on a complex vector space `V` which is positive definite on the
kernel of a linear map `π : V → ℂ^κ` (for a Pontryagin space of negative index `κ`, `π` is the
projection onto a fundamental negative subspace).  If `T` is `B`-self-adjoint and
`T v = λ v`, `T w = μ w` with `Im λ, Im μ > 0`, then `(λ̄ - μ) B(v,w) = 0` forces `B(v,w) = 0`.
Eigenvectors of distinct upper-half-plane eigenvalues are independent and span a totally
`B`-neutral subspace, on which `π` is injective.  Hence at most `κ` distinct eigenvalues of `T` lie
in the upper half-plane.
-/

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Eigenvectors of a `B`-self-adjoint operator for two upper-half-plane eigenvalues are
`B`-orthogonal. -/
theorem sesq_eq_zero_of_upper_eigenvectors (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, B (T x) y = B x (T y)) {v w : V} {l m : ℂ} (hv : T v = l • v)
    (hw : T w = m • w) (hl : 0 < l.im) (hm : 0 < m.im) : B v w = 0 := by
  have h := hT v w
  rw [hv, hw, LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul,
    smul_eq_mul] at h
  have hne : (starRingEnd ℂ) l - m ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have h2 : ((starRingEnd ℂ) l - m) * B v w = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left hne

/-- **Neutral eigenvector bound.** If `B` is positive definite on the kernel of `π : V → ℂ^κ` and
`T` is `B`-self-adjoint, then `T` has at most `κ` distinct eigenvalues in the upper half-plane. -/
theorem card_upper_eigenvalues_le (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {κ : ℕ} (π : V →ₗ[ℂ] (Fin κ → ℂ))
    (hπ : ∀ v, π v = 0 → v ≠ 0 → 0 < (B v v).re) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, B (T x) y = B x (T y)) {N : ℕ} (l : Fin N → ℂ) (hl : Function.Injective l)
    (hup : ∀ i, 0 < (l i).im) (v : Fin N → V) (hv0 : ∀ i, v i ≠ 0)
    (hTv : ∀ i, T (v i) = l i • v i) : N ≤ κ := by
  have hind : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (T : Module.End ℂ V) l hl v fun i =>
      Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hTv i), hv0 i⟩
  set W := Submodule.span ℂ (Set.range v)
  have hW : Module.finrank ℂ W = N := by rw [finrank_span_eq_card hind, Fintype.card_fin]
  have hneutral : ∀ x ∈ W, B x x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_eq_zero fun j _ => by
      rw [sesq_eq_zero_of_upper_eigenvectors B T hT (hTv j) (hTv i) (hup j) (hup i), smul_zero],
      smul_zero]
  have hinj : Function.Injective (π.comp W.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hpos := hπ x hx (by simpa using hx0)
    rw [hneutral x x.2, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [hW, Module.finrank_fin_fun] at h

end GaloisForLFunctions.HTGeometry
