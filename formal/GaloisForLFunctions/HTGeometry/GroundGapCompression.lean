import GaloisForLFunctions.HTGeometry.PsdHankelJetVanishing
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.Basic

/-!
# Spectral gap, approximate ground states, and simplicity below the gap

A symmetric operator with a ground vector `ξ` of energy `λ` and a gap `Δ` above it on `ξᗮ`
controls every approximate ground state: a unit vector whose Rayleigh quotient is at most `λ + ε`
is within `√(ε/Δ)` of the ground line.  The same gap makes every subspace on which the Rayleigh
quotient stays strictly below `λ + Δ` at most one-dimensional, because such a subspace meets `ξᗮ`
only in zero.

Both statements are elementary consequences of the orthogonal decomposition along `ξ`: no spectral
theorem is used, so they apply verbatim to a compression of the operator to a finite-dimensional
subspace, which is what a variational approximation argument needs.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Spectral-gap stability of an approximate ground state.**  A unit vector with Rayleigh
quotient at most `λ + ε` is within `ε/Δ` in squared norm of the ground line. -/
theorem norm_sub_ground_proj_sq_le (T : E →ₗ[ℝ] E)
    (hsymm : ∀ x y : E, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y))
    {ξ : E} (hξ : ‖ξ‖ = 1) {lam Δ : ℝ} (hTξ : T ξ = lam • ξ) (hΔ : 0 < Δ)
    (hgap : ∀ v : E, (inner ℝ ξ v : ℝ) = 0 → (lam + Δ) * ‖v‖ ^ 2 ≤ inner ℝ (T v) v)
    {η : E} (hη : ‖η‖ = 1) {ε : ℝ} (hray : (inner ℝ (T η) η : ℝ) ≤ lam + ε) :
    ‖η - (inner ℝ ξ η : ℝ) • ξ‖ ^ 2 ≤ ε / Δ := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (inner ℝ ξ η : ℝ) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : E, w = η - c • ξ := ⟨_, rfl⟩
  have hself : (inner ℝ ξ ξ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hξ]
    norm_num
  have hortho : (inner ℝ ξ w : ℝ) = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, hself, ← hc]
    ring
  have hdecomp : η = c • ξ + w := by
    rw [hw]
    abel
  have hpy : ‖η‖ ^ 2 = c ^ 2 + ‖w‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real, norm_smul, real_inner_smul_left, hortho]
    simp [hξ]
  have hTw : (inner ℝ (T w) ξ : ℝ) = 0 := by
    rw [hsymm, hTξ, real_inner_smul_right, real_inner_comm, hortho]
    ring
  have hTξξ : (inner ℝ (T ξ) ξ : ℝ) = lam := by
    rw [hTξ, real_inner_smul_left, hself]
    ring
  have hTξw : (inner ℝ (T ξ) w : ℝ) = 0 := by
    rw [hTξ, real_inner_smul_left, hortho]
    ring
  have hexpand : (inner ℝ (T η) η : ℝ) = c ^ 2 * lam + inner ℝ (T w) w := by
    rw [hdecomp]
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hTξξ, hTξw, hTw]
    ring
  have hwgap : (lam + Δ) * ‖w‖ ^ 2 ≤ inner ℝ (T w) w := hgap w hortho
  have hnorm : c ^ 2 + ‖w‖ ^ 2 = 1 := by
    rw [← hpy, hη]
    norm_num
  have hfinal : Δ * ‖w‖ ^ 2 ≤ ε := by
    rw [hexpand] at hray
    have h1 : c ^ 2 * lam + (lam + Δ) * ‖w‖ ^ 2 ≤ lam + ε := by linarith
    have h2 : c ^ 2 * lam + (lam + Δ) * ‖w‖ ^ 2
        = lam * (c ^ 2 + ‖w‖ ^ 2) + Δ * ‖w‖ ^ 2 := by ring
    rw [h2, hnorm] at h1
    linarith
  rw [← hc, ← hw, le_div_iff₀ hΔ]
  linarith

/-- **Below the gap the low-energy set meets the orthogonal complement of the ground only in
zero.** -/
theorem eq_zero_of_rayleigh_lt_of_inner_eq_zero (T : E →ₗ[ℝ] E) {ξ : E} {μ : ℝ}
    (hgap : ∀ v : E, (inner ℝ ξ v : ℝ) = 0 → μ * ‖v‖ ^ 2 ≤ inner ℝ (T v) v)
    {U : Submodule ℝ E} (hU : ∀ v ∈ U, v ≠ 0 → (inner ℝ (T v) v : ℝ) < μ * ‖v‖ ^ 2)
    {v : E} (hv : v ∈ U) (hvo : (inner ℝ ξ v : ℝ) = 0) : v = 0 := by
  by_contra hne
  have h1 := hU v hv hne
  have h2 := hgap v hvo
  linarith

/-- **Simplicity below the gap.**  A subspace on which the Rayleigh quotient stays strictly below
the gap threshold is at most one-dimensional. -/
theorem finrank_le_one_of_rayleigh_lt (T : E →ₗ[ℝ] E) {ξ : E} {μ : ℝ}
    (hgap : ∀ v : E, (inner ℝ ξ v : ℝ) = 0 → μ * ‖v‖ ^ 2 ≤ inner ℝ (T v) v)
    {U : Submodule ℝ E} (hU : ∀ v ∈ U, v ≠ 0 → (inner ℝ (T v) v : ℝ) < μ * ‖v‖ ^ 2) :
    Module.finrank ℝ U ≤ 1 := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : U →ₗ[ℝ] ℝ, ∀ v : U, f v = (inner ℝ ξ (v : E) : ℝ) :=
    ⟨{ toFun := fun v => (inner ℝ ξ (v : E) : ℝ)
       map_add' := by
         intro a b
         simp [inner_add_right]
       map_smul' := by
         intro c a
         simp [real_inner_smul_right] }, fun v => rfl⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hzero : (inner ℝ ξ ((a : E) - (b : E)) : ℝ) = 0 := by
      rw [inner_sub_right, ← hf a, ← hf b, hab]
      ring
    have hmem : ((a : E) - (b : E)) ∈ U := U.sub_mem a.2 b.2
    have := eq_zero_of_rayleigh_lt_of_inner_eq_zero T hgap hU hmem hzero
    exact Subtype.ext (by rwa [sub_eq_zero] at this)
  have hle := LinearMap.finrank_le_finrank_of_injective (f := f) hinj
  simpa using hle


/-! ## Convergence of a minimizing sequence -/

open Filter Topology

/-- **A minimizing sequence converges to the ground line.** -/
theorem tendsto_norm_sub_ground_proj (T : E →ₗ[ℝ] E)
    (hsymm : ∀ x y : E, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y))
    {ξ : E} (hξ : ‖ξ‖ = 1) {lam Δ : ℝ} (hTξ : T ξ = lam • ξ) (hΔ : 0 < Δ)
    (hgap : ∀ v : E, (inner ℝ ξ v : ℝ) = 0 → (lam + Δ) * ‖v‖ ^ 2 ≤ inner ℝ (T v) v)
    {ηs : ℕ → E} (hηs : ∀ n, ‖ηs n‖ = 1) {εs : ℕ → ℝ}
    (hε : Tendsto εs atTop (nhds 0))
    (hray : ∀ n, (inner ℝ (T (ηs n)) (ηs n) : ℝ) ≤ lam + εs n) :
    Tendsto (fun n => ‖ηs n - (inner ℝ ξ (ηs n) : ℝ) • ξ‖ ^ 2) atTop (nhds 0) := by
  refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_)
    (g := fun n => εs n / Δ) ?_
  · exact norm_sub_ground_proj_sq_le T hsymm hξ hTξ hΔ hgap (hηs n) (hray n)
  · simpa using hε.div_const Δ

/-- **A minimizing sequence with nonnegative ground overlap converges to the ground vector.** -/
theorem tendsto_norm_sub_ground (T : E →ₗ[ℝ] E)
    (hsymm : ∀ x y : E, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y))
    {ξ : E} (hξ : ‖ξ‖ = 1) {lam Δ : ℝ} (hTξ : T ξ = lam • ξ) (hΔ : 0 < Δ)
    (hgap : ∀ v : E, (inner ℝ ξ v : ℝ) = 0 → (lam + Δ) * ‖v‖ ^ 2 ≤ inner ℝ (T v) v)
    {ηs : ℕ → E} (hηs : ∀ n, ‖ηs n‖ = 1) {εs : ℕ → ℝ}
    (hε : Tendsto εs atTop (nhds 0))
    (hray : ∀ n, (inner ℝ (T (ηs n)) (ηs n) : ℝ) ≤ lam + εs n)
    (hsign : ∀ n, 0 ≤ (inner ℝ ξ (ηs n) : ℝ)) :
    Tendsto (fun n => ‖ηs n - ξ‖ ^ 2) atTop (nhds 0) := by
  have hself : (inner ℝ ξ ξ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hξ]
    norm_num
  have hsq : ∀ n : ℕ, ‖ηs n - ξ‖ ^ 2 = 2 - 2 * (inner ℝ ξ (ηs n) : ℝ) := by
    intro n
    rw [norm_sub_sq_real, hηs n, hξ, real_inner_comm]
    ring
  have hpy : ∀ n : ℕ, ‖ηs n - (inner ℝ ξ (ηs n) : ℝ) • ξ‖ ^ 2
      = 1 - (inner ℝ ξ (ηs n) : ℝ) ^ 2 := by
    intro n
    rw [norm_sub_sq_real, hηs n, norm_smul, real_inner_smul_right,
      real_inner_comm (ηs n) ξ]
    simp only [Real.norm_eq_abs, hξ, mul_one, sq_abs]
    ring
  have hmain := tendsto_norm_sub_ground_proj T hsymm hξ hTξ hΔ hgap hηs hε hray
  simp only [hpy] at hmain
  have hcsq : Tendsto (fun n => (inner ℝ ξ (ηs n) : ℝ) ^ 2) atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hmain
    simpa using h
  have hc : Tendsto (fun n => (inner ℝ ξ (ηs n) : ℝ)) atTop (nhds 1) := by
    have hsqrt : Tendsto (fun n => Real.sqrt ((inner ℝ ξ (ηs n) : ℝ) ^ 2)) atTop
        (nhds (Real.sqrt 1)) := (Real.continuous_sqrt.tendsto 1).comp hcsq
    rw [Real.sqrt_one] at hsqrt
    refine hsqrt.congr fun n => ?_
    rw [Real.sqrt_sq (hsign n)]
  simp only [hsq]
  have h := (tendsto_const_nhds (x := (2 : ℝ)) (f := atTop (α := ℕ))).sub
    (hc.const_mul (2 : ℝ))
  simpa using h



/-! ## Zero energy is the kernel -/

/-- **A zero-energy vector of a nonnegative symmetric operator lies in its kernel.**  This is the
step that turns "radical of the form" into "kernel of the operator". -/
theorem eq_zero_of_inner_self_eq_zero (T : E →ₗ[ℝ] E)
    (hsymm : ∀ x y : E, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y))
    (hpsd : ∀ x : E, 0 ≤ (inner ℝ (T x) x : ℝ))
    {v : E} (hv : (inner ℝ (T v) v : ℝ) = 0) : T v = 0 := by
  have hexp : ∀ (t : ℝ) (x y : E),
      (inner ℝ (T (x + t • y)) (x + t • y) : ℝ)
        = inner ℝ (T x) x + 2 * t * inner ℝ (T x) y + t ^ 2 * inner ℝ (T y) y := by
    intro t x y
    have hTy : (inner ℝ (T y) x : ℝ) = inner ℝ (T x) y := by
      rw [hsymm, real_inner_comm, hsymm]
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hTy]
    ring
  have hcs : ∀ w : E, (inner ℝ (T v) w : ℝ) ^ 2 ≤ inner ℝ (T v) v * inner ℝ (T w) w :=
    fun w => symmBilin_sq_le (comb := fun t x y => x + t • y) hexp hpsd v w
  have hzero : ∀ w : E, (inner ℝ (T v) w : ℝ) = 0 := by
    intro w
    have h := hcs w
    rw [hv, zero_mul] at h
    nlinarith [sq_nonneg (inner ℝ (T v) w : ℝ)]
  have hself : (inner ℝ (T v) (T v) : ℝ) = 0 := hzero (T v)
  exact inner_self_eq_zero.1 hself

/-! ## A simple ground has definite parity -/

/-- **A simple eigenvector of an operator commuting with an involution has definite parity.** -/
theorem reflection_ground_eq_or_neg {T R : E →ₗ[ℝ] E}
    (hcomm : ∀ x : E, R (T x) = T (R x)) (hinv : ∀ x : E, R (R x) = x)
    {ξ : E} (hξ : ξ ≠ 0) {lam : ℝ} (hTξ : T ξ = lam • ξ)
    (hsimple : ∀ v : E, T v = lam • v → ∃ c : ℝ, v = c • ξ) :
    R ξ = ξ ∨ R ξ = -ξ := by
  have hRe : T (R ξ) = lam • R ξ := by
    rw [← hcomm, hTξ, map_smul]
  obtain ⟨c, hc⟩ := hsimple (R ξ) hRe
  have hback : ξ = (c * c) • ξ := by
    have h := hinv ξ
    rw [hc, map_smul, hc, smul_smul] at h
    exact h.symm
  have hcsq : c * c = 1 := by
    by_contra hne
    have hsub : (c * c - 1) • ξ = 0 := by
      rw [sub_smul, one_smul, ← hback, sub_self]
    have hne' : c * c - 1 ≠ 0 := sub_ne_zero.2 hne
    exact hξ ((smul_eq_zero.1 hsub).resolve_left hne')
  have : c = 1 ∨ c = -1 := by
    rcases mul_self_eq_one_iff.1 hcsq with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases this with h | h
  · exact Or.inl (by rw [hc, h, one_smul])
  · exact Or.inr (by rw [hc, h, neg_one_smul])

end GaloisForLFunctions.HTGeometry

end
