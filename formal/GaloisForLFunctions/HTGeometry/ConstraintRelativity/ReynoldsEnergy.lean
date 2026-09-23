import Mathlib

/-!
# The Reynolds averaging energy of a unitary action

For a finite group acting unitarily on a complex inner product space, the Reynolds average
`Π s = |G|⁻¹ ∑_g U g s` satisfies `⟪Π s, Π s⟫ = ⟪Π s, s⟫`, and the averaged displacement energy is
exactly the norm defect of the average:

`(2|G|)⁻¹ ∑_g ‖U g s − s‖² = ‖s‖² − ‖Π s‖²`.

The energy vanishes exactly when `s` is a fixed vector.  This is the quantitative form of the
statement that a constitutive soldering is flat exactly when it is an intertwiner.
-/

namespace HTGeometry.ConstraintRelativity

open scoped ComplexInnerProductSpace

variable {G : Type*} [Group G] [Fintype G] {S : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S]

/-- The Reynolds average of a unitary action. -/
noncomputable def reynolds (U : G → (S ≃ₗᵢ[ℂ] S)) (s : S) : S :=
  ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, U g s

variable (U : G → (S ≃ₗᵢ[ℂ] S)) (hU : ∀ g h : G, U (g * h) = (U h).trans (U g))

include hU

/-- The Reynolds average is fixed by the action. -/
theorem reynolds_fixed (s : S) (h : G) : U h (reynolds U s) = reynolds U s := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  simp only [reynolds, map_smul, map_sum]
  congr 1
  have hrw : ∀ g : G, U h (U g s) = U (h * g) s := by
    intro g
    rw [hU h g]
    rfl
  rw [Finset.sum_congr rfl fun g _ => hrw g]
  exact Fintype.sum_bijective (fun g => h * g) (Group.mulLeft_bijective h) _ _ fun g => rfl

/-- The displacement inner products are constant along the group. -/
theorem inner_reynolds_self (s : S) :
    ⟪reynolds U s, reynolds U s⟫ = ⟪reynolds U s, s⟫ := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hsum : ∀ h : G, ⟪reynolds U s, U h s⟫ = ⟪reynolds U s, s⟫ := by
    intro h
    have hfix : U h (reynolds U s) = reynolds U s := reynolds_fixed U hU s h
    calc ⟪reynolds U s, U h s⟫ = ⟪U h (reynolds U s), U h s⟫ := by rw [hfix]
      _ = ⟪reynolds U s, s⟫ := (U h).inner_map_map _ _
  calc ⟪reynolds U s, reynolds U s⟫
      = ((Fintype.card G : ℂ))⁻¹ * ∑ h : G, ⟪reynolds U s, U h s⟫ := by
        rw [reynolds]
        rw [inner_smul_right, inner_sum]
    _ = ((Fintype.card G : ℂ))⁻¹ * ∑ _h : G, ⟪reynolds U s, s⟫ :=
        by rw [Finset.sum_congr rfl fun h _ => hsum h]
    _ = ⟪reynolds U s, s⟫ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hcard, one_mul]

/-- **The constitutive curvature energy.**  The averaged displacement energy is the norm defect of
the Reynolds average. -/
theorem reynolds_energy (s : S) :
    (2 * (Fintype.card G : ℝ))⁻¹ * ∑ g : G, ‖U g s - s‖ ^ (2 : ℕ)
      = ‖s‖ ^ (2 : ℕ) - ‖reynolds U s‖ ^ (2 : ℕ) := by
  have hcardR : (Fintype.card G : ℝ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hcardC : (Fintype.card G : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hterm : ∀ g : G, ‖U g s - s‖ ^ (2 : ℕ) = 2 * ‖s‖ ^ (2 : ℕ) - 2 * (⟪U g s, s⟫).re := by
    intro g
    rw [@norm_sub_sq ℂ, (U g).norm_map, RCLike.re_to_complex]
    ring
  have hsum : ∑ g : G, ‖U g s - s‖ ^ (2 : ℕ)
      = 2 * (Fintype.card G : ℝ) * ‖s‖ ^ (2 : ℕ) - 2 * (⟪reynolds U s, s⟫).re * (Fintype.card G : ℝ) := by
    rw [Finset.sum_congr rfl fun g _ => hterm g]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hre : ∑ g : G, (⟪U g s, s⟫).re = (Fintype.card G : ℝ) * (⟪reynolds U s, s⟫).re := by
      have hconj : ⟪reynolds U s, s⟫
          = ((Fintype.card G : ℂ))⁻¹ * ∑ g : G, ⟪U g s, s⟫ := by
        rw [reynolds, inner_smul_left, sum_inner]
        simp
      rw [hconj]
      rw [Complex.mul_re]
      have himzero : ((Fintype.card G : ℂ))⁻¹.im = 0 := by
        rw [show ((Fintype.card G : ℂ))⁻¹ = ((((Fintype.card G : ℝ))⁻¹ : ℝ) : ℂ) by
          push_cast; ring]
        simp
      have hrezero : ((Fintype.card G : ℂ))⁻¹.re = ((Fintype.card G : ℝ))⁻¹ := by
        rw [show ((Fintype.card G : ℂ))⁻¹ = ((((Fintype.card G : ℝ))⁻¹ : ℝ) : ℂ) by
          push_cast; ring]
        simp
      rw [himzero, hrezero, Complex.re_sum]
      field_simp
      ring
    rw [← Finset.mul_sum] at *
    rw [hre]
    ring
  rw [hsum]
  have hnorm : ‖reynolds U s‖ ^ (2 : ℕ) = (⟪reynolds U s, s⟫).re := by
    have h := inner_reynolds_self U hU s
    have hself : (⟪reynolds U s, reynolds U s⟫).re = ‖reynolds U s‖ ^ (2 : ℕ) := by
      rw [← RCLike.re_to_complex]
      exact inner_self_eq_norm_sq _
    rw [← hself, h]
  rw [hnorm]
  field_simp

omit hU in
/-- **Flatness classification.**  The curvature energy vanishes exactly when the vector is fixed by
the whole action, i.e. exactly when the soldering is an intertwiner. -/
theorem reynolds_energy_eq_zero_iff (s : S) :
    (2 * (Fintype.card G : ℝ))⁻¹ * ∑ g : G, ‖U g s - s‖ ^ (2 : ℕ) = 0 ↔ ∀ g : G, U g s = s := by
  have hcardR : (0 : ℝ) < 2 * (Fintype.card G : ℝ) := by
    have : (0 : ℝ) < (Fintype.card G : ℝ) := by
      exact_mod_cast Fintype.card_pos
    linarith
  constructor
  · intro hz g
    have hsum : ∑ g : G, ‖U g s - s‖ ^ (2 : ℕ) = 0 := by
      field_simp at hz
      simpa using hz
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun g _ => sq_nonneg ‖U g s - s‖)).1 hsum g (Finset.mem_univ g)
    have : ‖U g s - s‖ = 0 := by
      nlinarith [norm_nonneg (U g s - s)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · intro hfix
    have : ∑ g : G, ‖U g s - s‖ ^ (2 : ℕ) = 0 := by
      refine Finset.sum_eq_zero fun g _ => ?_
      rw [hfix g, sub_self, norm_zero]
      ring
    rw [this, mul_zero]

end HTGeometry.ConstraintRelativity
