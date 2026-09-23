import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow

/-!
# Full-sector polarization law

If a fundamental symmetry is `-1` on a sign sector and a bounded correction makes the total
quadratic form nonnegative, then the correction dominates the identity on that whole sector.
On an infinite-dimensional closed sector this forces noncompactness.  It also forces infinite
algebraic rank and leaves operator-norm distance at least one from every compact operator.

Self-adjointness of the correction is not used: positivity of the total quadratic form already
contains the exact input needed for the obstruction.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Full-sector compression law.**  Positivity of `J + G`, with `J = -1` on `S`, forces the
quadratic-form inequality `I_S ≤ G|_S`. -/
theorem fullSector_quadratic_lower_bound
    (J G : E →L[ℂ] E) (S : Submodule ℂ E)
    (hnegative : ∀ x ∈ S, J x = -x)
    (hpositive : ∀ x : E, 0 ≤ Complex.re ⟪(J + G) x, x⟫_ℂ)
    {x : E} (hx : x ∈ S) :
    ‖x‖ ^ (2 : ℕ) ≤ Complex.re ⟪G x, x⟫_ℂ := by
  have h := hpositive x
  rw [add_apply, hnegative x hx, inner_add_left, inner_neg_left] at h
  rw [inner_self_eq_norm_sq_to_K] at h
  rw [Complex.add_re, Complex.neg_re] at h
  norm_num [pow_two, Complex.mul_re] at h
  linarith

/-- Uniform positivity `J + G ≥ εI` strengthens the compression floor to `(1 + ε)I_S`. -/
theorem fullSector_quadratic_lower_bound_of_uniform
    (J G : E →L[ℂ] E) (S : Submodule ℂ E) (epsilon : ℝ)
    (hnegative : ∀ x ∈ S, J x = -x)
    (hpositive : ∀ x : E,
      epsilon * ‖x‖ ^ (2 : ℕ) ≤ Complex.re ⟪(J + G) x, x⟫_ℂ)
    {x : E} (hx : x ∈ S) :
    (1 + epsilon) * ‖x‖ ^ (2 : ℕ) ≤ Complex.re ⟪G x, x⟫_ℂ := by
  have h := hpositive x
  rw [add_apply, hnegative x hx, inner_add_left, inner_neg_left] at h
  rw [inner_self_eq_norm_sq_to_K] at h
  rw [Complex.add_re, Complex.neg_re] at h
  norm_num [pow_two, Complex.mul_re] at h
  linarith

/-- The full-sector quadratic estimate is a unit lower bound in norm. -/
theorem fullSector_norm_lower_bound
    (J G : E →L[ℂ] E) (S : Submodule ℂ E)
    (hnegative : ∀ x ∈ S, J x = -x)
    (hpositive : ∀ x : E, 0 ≤ Complex.re ⟪(J + G) x, x⟫_ℂ)
    {x : E} (hx : x ∈ S) :
    ‖x‖ ≤ ‖G x‖ := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hzero | hnorm
  · rw [← hzero]
    exact norm_nonneg _
  · have hquad := fullSector_quadratic_lower_bound J G S hnegative hpositive hx
    have hupper : Complex.re ⟪G x, x⟫_ℂ ≤ ‖G x‖ * ‖x‖ :=
      le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
    have hmul : ‖x‖ * ‖x‖ ≤ ‖G x‖ * ‖x‖ := by
      calc
        ‖x‖ * ‖x‖ = ‖x‖ ^ (2 : ℕ) := by ring
        _ ≤ Complex.re ⟪G x, x⟫_ℂ := hquad
        _ ≤ ‖G x‖ * ‖x‖ := hupper
    exact le_of_mul_le_mul_right hmul hnorm

/-- A full-sector correction on an infinite-dimensional closed sector cannot be compact. -/
theorem fullSector_not_isCompactOperator [CompleteSpace E]
    (J G : E →L[ℂ] E) (S : Submodule ℂ E)
    (hS : IsClosed (S : Set E)) (hSinfinite : ¬ FiniteDimensional ℂ S)
    (hnegative : ∀ x ∈ S, J x = -x)
    (hpositive : ∀ x : E, 0 ≤ Complex.re ⟪(J + G) x, x⟫_ℂ) :
    ¬ IsCompactOperator G := by
  intro hcompact
  apply hSinfinite
  exact finiteDimensional_of_isCompactOperator_of_bounded_below hcompact S hS one_pos
    (fun x hx => by simpa using fullSector_norm_lower_bound J G S hnegative hpositive hx)

/-- A full-sector correction on an infinite-dimensional sector has infinite algebraic rank. -/
theorem fullSector_not_finiteDimensional_range
    (J G : E →L[ℂ] E) (S : Submodule ℂ E)
    (hSinfinite : ¬ FiniteDimensional ℂ S)
    (hnegative : ∀ x ∈ S, J x = -x)
    (hpositive : ∀ x : E, 0 ≤ Complex.re ⟪(J + G) x, x⟫_ℂ) :
    ¬ FiniteDimensional ℂ (LinearMap.range (G : E →ₗ[ℂ] E)) := by
  intro hrange
  let f : S →ₗ[ℂ] LinearMap.range (G : E →ₗ[ℂ] E) :=
    { toFun := fun x => ⟨G x, ⟨x, rfl⟩⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }
  have hf : Function.Injective f := by
    intro x y hxy
    have hGxy : G (x : E) = G (y : E) := congrArg Subtype.val hxy
    have hmem : (x : E) - (y : E) ∈ S := S.sub_mem x.2 y.2
    have hlower := fullSector_norm_lower_bound J G S hnegative hpositive hmem
    have hGzero : G ((x : E) - (y : E)) = 0 := by
      rw [map_sub, hGxy, sub_self]
    rw [hGzero, norm_zero] at hlower
    exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hlower (norm_nonneg _))))
  letI : FiniteDimensional ℂ (LinearMap.range (G : E →ₗ[ℂ] E)) := hrange
  apply hSinfinite
  exact FiniteDimensional.of_injective f hf

/-- Every compact perturbation of a full-sector correction remains at operator-norm distance at
least one.  This is the raw compact-ideal form of the essential-norm lower bound. -/
theorem fullSector_one_le_norm_sub_compact [CompleteSpace E]
    (J G : E →L[ℂ] E) (S : Submodule ℂ E)
    (hS : IsClosed (S : Set E)) (hSinfinite : ¬ FiniteDimensional ℂ S)
    (hnegative : ∀ x ∈ S, J x = -x)
    (hpositive : ∀ x : E, 0 ≤ Complex.re ⟪(J + G) x, x⟫_ℂ)
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    1 ≤ ‖G - K‖ := by
  by_contra hnot
  have hlt : ‖G - K‖ < 1 := lt_of_not_ge hnot
  have hc : 0 < 1 - ‖G - K‖ := sub_pos.mpr hlt
  have hbdd : ∀ x ∈ S, (1 - ‖G - K‖) * ‖x‖ ≤ ‖K x‖ := by
    intro x hx
    have hGlow := fullSector_norm_lower_bound J G S hnegative hpositive hx
    have hdecomp : G x = (G - K) x + K x := by simp
    have hGupper : ‖G x‖ ≤ ‖(G - K) x‖ + ‖K x‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    have hdiff : ‖(G - K) x‖ ≤ ‖G - K‖ * ‖x‖ := (G - K).le_opNorm x
    nlinarith
  exact hSinfinite
    (finiteDimensional_of_isCompactOperator_of_bounded_below hK S hS hc hbdd)

end GaloisForLFunctions.HTGeometry
