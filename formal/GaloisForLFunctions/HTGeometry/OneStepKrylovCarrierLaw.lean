import GaloisForLFunctions.HTGeometry.KrylovCarrierProjectionLaw

/-!
# Exact first Krylov innovation

For a centred frequency vector and a target orthogonal to the constant mode,
the order-one Krylov carrier is exactly the rank-one projection onto the
frequency vector.  Its squared norm is therefore one normalized directional
correlation.  This is the deterministic interface needed by the first
quenched local-Hamiltonian replica estimate.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem inner_spectralPowerVector_zero
    {I : Type*} [Fintype I] (frequency : I → ℝ)
    (x : EuclideanSpace ℂ I) :
    inner ℂ (spectralPowerVector frequency 0) x = ∑ i, x i := by
  simp [PiLp.inner_apply, spectralPowerVector, RCLike.inner_apply]

theorem inner_spectralPowerVector_zero_one
    {I : Type*} [Fintype I] (frequency : I → ℝ) :
    inner ℂ (spectralPowerVector frequency 0)
      (spectralPowerVector frequency 1) = ∑ i, (frequency i : ℂ) := by
  simp [PiLp.inner_apply, spectralPowerVector, RCLike.inner_apply]

/-- After removing the constant mode from both frequency and target, the
first Krylov carrier is precisely projection onto the frequency line. -/
theorem spectralKrylovCarrier_one_eq_lineProjection
    {I : Type*} [Fintype I] (frequency : I → ℝ)
    (x : EuclideanSpace ℂ I)
    (hxzero : inner ℂ (spectralPowerVector frequency 0) x = 0)
    (horth : inner ℂ (spectralPowerVector frequency 0)
      (spectralPowerVector frequency 1) = 0) :
    spectralKrylovCarrier frequency 1 x =
      (inner ℂ (spectralPowerVector frequency 1) x /
        ((‖spectralPowerVector frequency 1‖ ^ (2 : ℕ) : ℝ) : ℂ)) •
          spectralPowerVector frequency 1 := by
  let v := spectralPowerVector frequency 1
  let z := (ℂ ∙ v).starProjection x
  have hzline : z ∈ ℂ ∙ v := Submodule.starProjection_apply_mem _ _
  have hz : z ∈ spectralKrylovSubspace frequency 1 := by
    refine Submodule.span_induction (p := fun y _ => y ∈ spectralKrylovSubspace frequency 1)
      ?_ ?_ ?_ ?_ hzline
    · intro y hy
      rcases hy with rfl
      exact spectralPowerVector_mem_spectralKrylovSubspace frequency (K := 1) (k := 1) le_rfl
    · exact Submodule.zero_mem _
    · intro y z hy hz hiy hiz
      exact Submodule.add_mem _ hiy hiz
    · intro a y hy hiy
      exact Submodule.smul_mem _ a hiy
  have hresline : x - z ∈ (ℂ ∙ v)ᗮ := by
    exact Submodule.sub_starProjection_mem_orthogonal (K := ℂ ∙ v) x
  have hperp : ∀ y ∈ spectralKrylovSubspace frequency 1,
      inner ℂ (x - z) y = 0 := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => inner ℂ (x - z) y = 0)
      ?_ ?_ ?_ ?_ hy
    · rintro y ⟨k, rfl⟩
      fin_cases k
      · have hxzero' : inner ℂ x (spectralPowerVector frequency 0) = 0 :=
          inner_eq_zero_symm.mpr hxzero
        have hzorth : inner ℂ z (spectralPowerVector frequency 0) = 0 := by
          refine Submodule.span_induction (p := fun y _ =>
              inner ℂ y (spectralPowerVector frequency 0) = 0)
            ?_ ?_ ?_ ?_ hzline
          · intro y hy
            rcases hy with rfl
            exact inner_eq_zero_symm.mpr (by simpa [v] using horth)
          · simp
          · intro a b ha hb hia hib
            simp [hia, hib]
          · intro a y hy hiy
            simp [hiy]
        rw [inner_sub_left, hxzero', hzorth, sub_zero]
      · exact Submodule.inner_left_of_mem_orthogonal
          (Submodule.mem_span_singleton_self v) hresline
    · simp
    · intro y z hy hz hiy hiz
      simp [hiy, hiz]
    · intro a y hy hiy
      simp [hiy]
  have hproj : spectralKrylovCarrier frequency 1 x = z := by
    unfold spectralKrylovCarrier
    exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hz hperp
  rw [hproj]
  exact Submodule.starProjection_singleton ℂ x

/-- Squared first-carrier mass is one normalized directional correlation. -/
theorem norm_sq_spectralKrylovCarrier_one_eq
    {I : Type*} [Fintype I] (frequency : I → ℝ)
    (x : EuclideanSpace ℂ I)
    (hxzero : inner ℂ (spectralPowerVector frequency 0) x = 0)
    (horth : inner ℂ (spectralPowerVector frequency 0)
      (spectralPowerVector frequency 1) = 0) :
    ‖spectralKrylovCarrier frequency 1 x‖ ^ (2 : ℕ) =
      ‖inner ℂ (spectralPowerVector frequency 1) x‖ ^ (2 : ℕ) /
        ‖spectralPowerVector frequency 1‖ ^ (2 : ℕ) := by
  rw [spectralKrylovCarrier_one_eq_lineProjection frequency x hxzero horth]
  by_cases hv : ‖spectralPowerVector frequency 1‖ = 0
  · have hvzero : spectralPowerVector frequency 1 = 0 := norm_eq_zero.mp hv
    simp [hvzero]
  · rw [norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    field_simp

/-- Sum-zero form used for traceless Hamiltonians and scalar-removed Choi
targets. -/
theorem norm_sq_spectralKrylovCarrier_one_eq_of_sum_zero
    {I : Type*} [Fintype I] (frequency : I → ℝ)
    (x : EuclideanSpace ℂ I)
    (hxzero : ∑ i, x i = 0)
    (hfrequencyZero : ∑ i, frequency i = 0) :
    ‖spectralKrylovCarrier frequency 1 x‖ ^ (2 : ℕ) =
      ‖inner ℂ (spectralPowerVector frequency 1) x‖ ^ (2 : ℕ) /
        ‖spectralPowerVector frequency 1‖ ^ (2 : ℕ) := by
  apply norm_sq_spectralKrylovCarrier_one_eq frequency x
  · rwa [inner_spectralPowerVector_zero]
  · rw [inner_spectralPowerVector_zero_one]
    exact_mod_cast hfrequencyZero

end GaloisForLFunctions.HTGeometry
