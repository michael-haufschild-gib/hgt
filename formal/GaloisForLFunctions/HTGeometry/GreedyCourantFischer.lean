import GaloisForLFunctions.HTGeometry.GreedySingularValues

/-!
# Courant–Fischer lower bounds for the greedy constrained norms

The greedy constrained norm `orthSup S v n` is by construction an upper bound: every unit vector
orthogonal to `v 0, …, v (n−1)` has `‖S y‖ ≤ orthSup S v n`.  Bounding it from *below* requires
producing such a vector, and the greedy family `v` is not explicit.

The standard device supplies one by dimension count.  Testing membership of the orthogonal
complement of `v 0, …, v (n−1)` is a linear map into an `n`-dimensional space, so any trial
subspace of dimension exceeding `n` meets that complement in a nonzero vector.  If `S` is
bounded below by `M` on the trial subspace, that vector certifies `M ≤ orthSup S v n`.

This is the min–max input needed to bound prolate concentration eigenvalues from below by
exhibiting a trial space of concentrated functions, and it is independent of any particular
choice of trial space.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The dimension count.**  A subspace of dimension exceeding `n` contains a nonzero vector
orthogonal to any `n` prescribed vectors: the `n` test functionals cannot be jointly injective
on it. -/
theorem exists_mem_ne_zero_orthogonal_of_finrank_lt
    (V : Submodule ℂ H) (w : ℕ → H) (n : ℕ) (hV : n < Module.finrank ℂ V) :
    ∃ x ∈ V, x ≠ 0 ∧ ∀ m < n, inner ℂ (w m) x = 0 := by
  have hpos : 0 < Module.finrank ℂ V := lt_of_le_of_lt (Nat.zero_le n) hV
  have hfin : Module.Finite ℂ V := Module.finite_of_finrank_pos hpos
  let f : V →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x m => inner ℂ (w (m : ℕ)) (x : H)
      map_add' := by
        intro x y
        funext m
        simp [inner_add_right]
      map_smul' := by
        intro c x
        funext m
        simp [inner_smul_right] }
  have hrange : Module.finrank ℂ (LinearMap.range f) ≤ n := by
    calc Module.finrank ℂ (LinearMap.range f)
        ≤ Module.finrank ℂ (Fin n → ℂ) := Submodule.finrank_le _
      _ = n := Module.finrank_fin_fun ℂ
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hkerne : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    have hzero : Module.finrank ℂ (LinearMap.ker f) = 0 := Submodule.finrank_eq_zero.mpr hbot
    omega
  obtain ⟨x, hxmem, hxne⟩ := (Submodule.ne_bot_iff _).mp hkerne
  refine ⟨(x : H), x.2, fun h => hxne (Subtype.ext h), fun m hm => ?_⟩
  have hfx : f x = 0 := LinearMap.mem_ker.mp hxmem
  simpa using congrFun hfx ⟨m, hm⟩

/-- **Courant–Fischer, lower bound.**  If `S` is bounded below by `M` on a trial subspace of
dimension exceeding `n`, then the greedy constrained norm at step `n` is at least `M`. -/
theorem le_orthSup_of_trial (S : H →L[ℂ] H) (v : ℕ → H) (n : ℕ)
    (V : Submodule ℂ H) (hV : n < Module.finrank ℂ V)
    {M : ℝ} (hM : ∀ x ∈ V, M * ‖x‖ ≤ ‖S x‖) :
    M ≤ orthSup S v n := by
  obtain ⟨x, hxV, hx0, hxorth⟩ := exists_mem_ne_zero_orthogonal_of_finrank_lt V v n hV
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  have hunit : ‖((‖x‖ : ℂ))⁻¹ • x‖ ≤ 1 := le_of_eq (norm_smul_inv_norm hx0)
  have horth : ∀ m < n, inner ℂ (v m) (((‖x‖ : ℂ))⁻¹ • x) = 0 := by
    intro m hm
    rw [inner_smul_right, hxorth m hm, mul_zero]
  have hb := le_orthSup S v n hunit horth
  rw [map_smul, norm_smul] at hb
  have hnorm : ‖((‖x‖ : ℂ))⁻¹‖ = ‖x‖⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  rw [hnorm] at hb
  have hlow : M * ‖x‖ ≤ ‖S x‖ := hM x hxV
  have hstep : M ≤ ‖x‖⁻¹ * ‖S x‖ := by
    rw [le_inv_mul_iff₀ hxn]
    linarith [hlow]
  linarith [hb, hstep]

end ContinuousLinearMap
