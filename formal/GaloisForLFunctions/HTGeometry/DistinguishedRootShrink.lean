import GaloisForLFunctions.HTGeometry.GermPreparationAlgebraic

/-!
# Roots of a nearly distinguished polynomial are small

A monic polynomial `z^d + a_{d-1} z^{d-1} + … + a_0` whose roots are known to lie in a disc of
radius `t` has all its roots in a disc of radius `ε` as soon as every coefficient is small: from
`ρ^d = −∑ a_j ρ^j` one gets `‖ρ‖^d ≤ A · ∑_{j<d} t^j`, so shrinking `A` shrinks `‖ρ‖`.

For the Weierstrass polynomial of a preparation the coefficients are holomorphic in the parameters
and vanish at the origin, so this makes the roots of the moving polynomial uniformly small on a
small enough parameter ball.  That is exactly the hypothesis the uniqueness of the division needs
on a shrunken polydisc.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

/-- **The root bound.**  A root of a monic polynomial with small coefficients is small. -/
theorem norm_root_pow_le {d : ℕ} {a : ℕ → ℂ} {ρ : ℂ} {t A : ℝ}
    (hρt : ‖ρ‖ ≤ t) (_ht : 0 ≤ t) (ha : ∀ j, j < d → ‖a j‖ ≤ A)
    (hroot : ρ ^ d + ∑ j ∈ Finset.range d, a j * ρ ^ j = 0) :
    ‖ρ‖ ^ d ≤ A * ∑ j ∈ Finset.range d, t ^ j := by
  have hsum : ρ ^ d = -∑ j ∈ Finset.range d, a j * ρ ^ j := by
    linear_combination hroot
  have h1 : ‖ρ‖ ^ d = ‖∑ j ∈ Finset.range d, a j * ρ ^ j‖ := by
    rw [← norm_pow, hsum, norm_neg]
  rw [h1]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjd : j < d := Finset.mem_range.mp hj
  rw [norm_mul, norm_pow]
  have hA : 0 ≤ A := le_trans (norm_nonneg _) (ha j hjd)
  have hjt : ‖ρ‖ ^ j ≤ t ^ j := pow_le_pow_left₀ (norm_nonneg ρ) hρt j
  calc ‖a j‖ * ‖ρ‖ ^ j ≤ A * ‖ρ‖ ^ j :=
        mul_le_mul_of_nonneg_right (ha j hjd) (pow_nonneg (norm_nonneg ρ) j)
    _ ≤ A * t ^ j := mul_le_mul_of_nonneg_left hjt hA

/-- **Small coefficients force small roots.** -/
theorem norm_root_lt {d : ℕ} (_hd : 0 < d) {a : ℕ → ℂ} {ρ : ℂ} {t A ε : ℝ}
    (hρt : ‖ρ‖ ≤ t) (ht : 0 ≤ t) (hε : 0 < ε)
    (ha : ∀ j, j < d → ‖a j‖ ≤ A)
    (hsmall : A * ∑ j ∈ Finset.range d, t ^ j < ε ^ d)
    (hroot : ρ ^ d + ∑ j ∈ Finset.range d, a j * ρ ^ j = 0) :
    ‖ρ‖ < ε := by
  have hpow : ‖ρ‖ ^ d < ε ^ d :=
    lt_of_le_of_lt (norm_root_pow_le hρt ht ha hroot) hsmall
  by_contra hc
  rw [not_lt] at hc
  exact absurd hpow (not_lt.mpr (pow_le_pow_left₀ hε.le hc d))

/-- **A prescribed root bound is achievable.**  For any target radius there is a coefficient bound
that forces every root inside a disc of radius `t` to lie inside the target disc. -/
theorem exists_coeff_bound {d : ℕ} (hd : 0 < d) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (a : ℕ → ℂ) (ρ : ℂ), ‖ρ‖ ≤ t → (∀ j, j < d → ‖a j‖ ≤ A) →
      ρ ^ d + ∑ j ∈ Finset.range d, a j * ρ ^ j = 0 → ‖ρ‖ < ε := by
  set S : ℝ := ∑ j ∈ Finset.range d, t ^ j with hS
  have hSpos : 0 < S := by
    rw [hS]
    refine Finset.sum_pos' (fun j _ => pow_nonneg ht j) ⟨0, Finset.mem_range.mpr hd, ?_⟩
    simp
  refine ⟨ε ^ d / (2 * S), by positivity, ?_⟩
  intro a ρ hρt ha hroot
  refine norm_root_lt hd hρt ht hε ha ?_ hroot
  rw [← hS]
  have hrw : ε ^ d / (2 * S) * S = ε ^ d / 2 := by
    field_simp
  rw [hrw]
  have hεd : 0 < ε ^ d := pow_pos hε d
  linarith

/-! ## Uniform shrinking on a parameter ball -/

variable {n : ℕ}

/-- **The roots of a moving distinguished polynomial are uniformly small near the origin.**  If the
coefficients are continuous and vanish at the origin, then for every target radius there is a
parameter ball on which every root inside the fixed disc lies inside the target disc. -/
theorem exists_param_ball_roots_lt {d : ℕ} (hd : 0 < d) {a : ℕ → (Fin n → ℂ) → ℂ}
    (hcont : ∀ j, ContinuousAt (a j) (0 : Fin n → ℂ)) (hzero : ∀ j, j < d → a j 0 = 0)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin n → ℂ, ‖y‖ < δ → ∀ ρ : ℂ, ‖ρ‖ ≤ t →
      ρ ^ d + ∑ j ∈ Finset.range d, a j y * ρ ^ j = 0 → ‖ρ‖ < ε := by
  classical
  obtain ⟨A, hA, hAspec⟩ := exists_coeff_bound hd ht hε
  have hev : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ∀ j ∈ Finset.range d, ‖a j y‖ ≤ A := by
    refine (Filter.eventually_all_finset _).mpr ?_
    intro j hj
    have hjd : j < d := Finset.mem_range.mp hj
    have hball : Metric.ball (a j (0 : Fin n → ℂ)) A ∈ 𝓝 (a j (0 : Fin n → ℂ)) :=
      Metric.ball_mem_nhds _ hA
    filter_upwards [(hcont j).eventually hball] with y hy
    rw [hzero j hjd, dist_zero_right] at hy
    exact hy.le
  obtain ⟨δ, hδ, hδspec⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, ?_⟩
  intro y hy ρ hρ hroot
  refine hAspec (fun j => a j y) ρ hρ ?_ hroot
  intro j hjd
  exact hδspec (by simpa [dist_zero_right] using hy) j (Finset.mem_range.mpr hjd)

end GaloisForLFunctions.HTGeometry
