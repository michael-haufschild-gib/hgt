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

/-- **The Cauchy root bound.**  Every root of a monic polynomial with coefficients bounded by `A`
has modulus at most `max 1 (A·d)`. -/
theorem norm_root_le_cauchy {d : ℕ} (hd : 0 < d) {a : ℕ → ℂ} {ρ : ℂ} {A : ℝ}
    (ha : ∀ j, j < d → ‖a j‖ ≤ A)
    (hroot : ρ ^ d + ∑ j ∈ Finset.range d, a j * ρ ^ j = 0) :
    ‖ρ‖ ≤ max 1 (A * d) := by
  by_cases h1 : ‖ρ‖ ≤ 1
  · exact le_trans h1 (le_max_left _ _)
  rw [not_le] at h1
  refine le_trans ?_ (le_max_right _ _)
  have hA : 0 ≤ A := le_trans (norm_nonneg _) (ha 0 hd)
  have hbound : ‖ρ‖ ^ d ≤ A * d * ‖ρ‖ ^ (d - 1) := by
    have hsum : ρ ^ d = -∑ j ∈ Finset.range d, a j * ρ ^ j := by
      linear_combination hroot
    have h2 : ‖ρ‖ ^ d = ‖∑ j ∈ Finset.range d, a j * ρ ^ j‖ := by
      rw [← norm_pow, hsum, norm_neg]
    rw [h2]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ j ∈ Finset.range d, ‖a j * ρ ^ j‖ ≤ A * ‖ρ‖ ^ (d - 1) := by
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      rw [norm_mul, norm_pow]
      refine le_trans (mul_le_mul_of_nonneg_right (ha j hjd)
        (pow_nonneg (norm_nonneg ρ) j)) ?_
      refine mul_le_mul_of_nonneg_left ?_ hA
      exact pow_le_pow_right₀ h1.le (by omega)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring_nf
    exact le_of_eq (by ring)
  have hpos : 0 < ‖ρ‖ ^ (d - 1) := pow_pos (lt_trans one_pos h1) _
  have hsplit : ‖ρ‖ ^ d = ‖ρ‖ * ‖ρ‖ ^ (d - 1) := by
    conv_lhs => rw [show d = 1 + (d - 1) from by omega]
    rw [pow_add, pow_one]
  rw [hsplit] at hbound
  exact le_of_mul_le_mul_right (by linarith [hbound]) hpos

/-- **Roots of a moving monic polynomial with small coefficients are small**, with no a priori
bound on the roots. -/
theorem exists_param_ball_roots_lt_monic {d : ℕ} (hd : 0 < d) {a : ℕ → (Fin n → ℂ) → ℂ}
    (hcont : ∀ j, ContinuousAt (a j) (0 : Fin n → ℂ)) (hzero : ∀ j, j < d → a j 0 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin n → ℂ, ‖y‖ < δ → ∀ ρ : ℂ,
      ρ ^ d + ∑ j ∈ Finset.range d, a j y * ρ ^ j = 0 → ‖ρ‖ < ε := by
  classical
  have htpos : (0 : ℝ) < max 1 (d : ℝ) := lt_of_lt_of_le one_pos (le_max_left _ _)
  obtain ⟨A', hA', hA'spec⟩ := exists_coeff_bound hd htpos.le hε
  have hApos : 0 < min 1 A' := lt_min one_pos hA'
  have hev : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ∀ j ∈ Finset.range d, ‖a j y‖ ≤ min 1 A' := by
    refine (Filter.eventually_all_finset _).mpr ?_
    intro j hj
    have hjd : j < d := Finset.mem_range.mp hj
    have hball : Metric.ball (a j (0 : Fin n → ℂ)) (min 1 A') ∈ 𝓝 (a j (0 : Fin n → ℂ)) :=
      Metric.ball_mem_nhds _ hApos
    filter_upwards [(hcont j).eventually hball] with y hy
    rw [hzero j hjd, dist_zero_right] at hy
    exact hy.le
  obtain ⟨δ, hδ, hδspec⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, ?_⟩
  intro y hy ρ hroot
  have hbnd : ∀ j, j < d → ‖a j y‖ ≤ min 1 A' := fun j hjd =>
    hδspec (by simpa [dist_zero_right] using hy) j (Finset.mem_range.mpr hjd)
  have hρt : ‖ρ‖ ≤ max 1 (d : ℝ) := by
    refine le_trans (norm_root_le_cauchy hd hbnd hroot) ?_
    refine max_le_max le_rfl ?_
    have : min 1 A' ≤ 1 := min_le_left _ _
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  exact hA'spec (fun j => a j y) ρ hρt (fun j hjd => le_trans (hbnd j hjd) (min_le_right _ _)) hroot

end GaloisForLFunctions.HTGeometry
