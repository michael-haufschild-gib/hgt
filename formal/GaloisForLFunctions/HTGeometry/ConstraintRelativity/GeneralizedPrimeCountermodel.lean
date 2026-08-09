import Mathlib

/-!
# The generalized-prime compound countermodel

For a free abelian group of generalized-prime valuations, the group algebra carries a grading, a
radial character action `Γ_c`, valuation derivations `∂_j`, an identity-coefficient trace, and
prime/inverse-prime atoms `u_i` with `τ(u_i) = 1`, `φ_j(u_i) = −δ_ij` and `Γ_c^{⊗2} u_i = u_i`.

On the reciprocal two-leg space the twisted transports preserve the indefinite Stokes form for
*every* real `c`, while the scalar radial defect `1 − P_i^{2c}` is nonzero for every `c ≠ 0`, and
the contracted scalar port defect has rank one while the uncontracted coframe defect is injective.

So the whole organ conjunction is realized at every nonzero drift: no theorem using only these
identities can force `c = 0`.
-/

namespace HTGeometry.ConstraintRelativity

open Matrix

/-! ## The reciprocal two-leg transport preserves the Stokes form -/

/-- The indefinite Stokes form on the reciprocal two-leg space. -/
def stokesForm : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The twisted diagonal transport at generalized prime norm `P` and drift `c`. -/
noncomputable def legTransport (P c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![P ^ c, 0; 0, P ^ (-c)]

/-- **Card `(7)`.**  The twisted transport preserves the indefinite Stokes form for every real
drift. -/
theorem legTransport_stokes (P c : ℝ) (hP : 0 < P) :
    (legTransport P c)ᵀ * stokesForm * legTransport P c = stokesForm := by
  have hpow : P ^ c * P ^ (-c) = 1 := by
    rw [← Real.rpow_add hP]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [legTransport, stokesForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      hpow, mul_comm]

/-! ## The scalar radial defect -/

/-- **Card `(8)`.**  The scalar radial defect `1 − P^{2c}` is nonzero at every nonzero drift. -/
theorem radialDefect_ne_zero {P c : ℝ} (hP : 1 < P) (hc : c ≠ 0) : 1 - P ^ (2 * c) ≠ 0 := by
  intro h
  have hpow : P ^ (2 * c) = 1 := by linarith
  have hlog : (2 * c) * Real.log P = 0 := by
    have := congrArg Real.log hpow
    rwa [Real.log_rpow (lt_trans zero_lt_one hP), Real.log_one] at this
  have hlogP : Real.log P ≠ 0 := ne_of_gt (Real.log_pos hP)
  rcases mul_eq_zero.1 hlog with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · norm_num at h2
    · exact hc h2
  · exact hlogP h1

/-! ## The contracted scalar port defect has rank one -/

variable {ι : Type*} [Fintype ι]

/-- **Card `(8a)`.**  The contracted scalar port defect. -/
noncomputable def scalarPortDefect (P : ι → ℝ) (c : ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun a := ∑ i, a i * (1 - P i ^ (2 * c))
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_mul]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro r x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp]
theorem scalarPortDefect_apply (P : ι → ℝ) (c : ℝ) (a : ι → ℝ) :
    scalarPortDefect P c a = ∑ i, a i * (1 - P i ^ (2 * c)) := rfl

/-- The contracted scalar port defect is nonzero, hence of rank one. -/
theorem scalarPortDefect_ne_zero [DecidableEq ι] {P : ι → ℝ} {c : ℝ} (i₀ : ι)
    (hP : ∀ i, 1 < P i) (hc : c ≠ 0) : scalarPortDefect P c ≠ 0 := by
  intro h
  have hval : scalarPortDefect P c (Pi.single i₀ 1) = 0 := by rw [h]; rfl
  rw [scalarPortDefect_apply] at hval
  rw [Finset.sum_eq_single i₀] at hval
  · simp only [Pi.single_eq_same, one_mul] at hval
    exact radialDefect_ne_zero (hP i₀) hc hval
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hcon
    simp at hcon

omit [Fintype ι] in
/-- **Card, hostile audit item 4.**  The uncontracted coframe defect is diagonal and injective, so
it is not of rank one. -/
noncomputable def coframeDefect (P : ι → ℝ) (c : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun a := fun i => a i * (1 - P i ^ (2 * c))
  map_add' := by intro x y; funext i; simp [add_mul]
  map_smul' := by intro r x; funext i; simp; ring

omit [Fintype ι] in
@[simp]
theorem coframeDefect_apply (P : ι → ℝ) (c : ℝ) (a : ι → ℝ) (i : ι) :
    coframeDefect P c a i = a i * (1 - P i ^ (2 * c)) := rfl

omit [Fintype ι] in
theorem coframeDefect_injective {P : ι → ℝ} {c : ℝ} (hP : ∀ i, 1 < P i) (hc : c ≠ 0) :
    Function.Injective (coframeDefect P c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  funext i
  have hi : a i * (1 - P i ^ (2 * c)) = 0 := congrFun ha i
  rcases mul_eq_zero.1 hi with h | h
  · exact h
  · exact absurd h (radialDefect_ne_zero (hP i) hc)

end HTGeometry.ConstraintRelativity
