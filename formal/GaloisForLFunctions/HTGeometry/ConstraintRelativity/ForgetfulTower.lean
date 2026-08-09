import Mathlib

/-!
# The source–norm–support forgetful tower

For the two-leg carrier with swap `τ`, twisted swap `T_δ`, and central scaling `L_c`, the
transport defect

`D = T_δ L_c − L_c τ`

is the single scalar `a = c(δ − 1)` placed in one matrix cell, and the two-column carrier
`Γ = [D | T_δ D]` satisfies the exact Gram identity `Γ Γ* = |a|² I`.  Consequently the support of
`Γ` is all or nothing, its Moore–Penrose inverse scales every vector by exactly `|a|⁻¹`, and
`det(Γ Γ*) = |a|⁴`.

Arithmetic orientation, positive Hilbert geometry, and exact support are therefore not independent
constraints: they are the successive forgetful shadows `a ↦ |a|² ↦ [a = 0]` of one framed scalar,
the first forgetting phase and the second forgetting magnitude.  A central scalar twist of all
block transports leaves every relative channel unchanged, so exact-category data alone cannot
select the untwisted frame.
-/

namespace HTGeometry.ConstraintRelativity

open Matrix Complex

/-! ## The two-leg carrier -/

/-- The swap involution. -/
def legSwap : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The twisted swap with parameter `δ`. -/
def legTwist (δ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; δ, 0]

/-- The central scaling by `c`. -/
def legScale (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![c, 0; 0, c]

/-- The framed source scalar `a = c(δ − 1)`. -/
def sourceScalar (δ c : ℂ) : ℂ := c * (δ - 1)

/-- The transport defect `D = T_δ L_c − L_c τ`. -/
def transportDefect (δ c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  legTwist δ * legScale c - legScale c * legSwap

/-- **The defect is one scalar in the lower-left cell.** -/
theorem transportDefect_eq (δ c : ℂ) :
    transportDefect δ c = !![0, 0; sourceScalar δ c, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transportDefect, legTwist, legScale, legSwap, sourceScalar] <;> ring

/-- **The transported defect is the same scalar in the upper-left cell.** -/
theorem legTwist_mul_transportDefect (δ c : ℂ) :
    legTwist δ * transportDefect δ c = !![sourceScalar δ c, 0; 0, 0] := by
  rw [transportDefect_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [legTwist, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two-column carrier `Γ = [D | T_δ D] : ℂ² ⊕ ℂ² → ℂ²`. -/
def legCarrier (δ c : ℂ) : Matrix (Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.of fun i => Sum.elim (transportDefect δ c i) ((legTwist δ * transportDefect δ c) i)

@[simp]
theorem legCarrier_inl (δ c : ℂ) (i j : Fin 2) :
    legCarrier δ c i (Sum.inl j) = (!![0, 0; sourceScalar δ c, 0] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  show transportDefect δ c i j = _
  rw [transportDefect_eq]

@[simp]
theorem legCarrier_inr (δ c : ℂ) (i j : Fin 2) :
    legCarrier δ c i (Sum.inr j) = (!![sourceScalar δ c, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  show (legTwist δ * transportDefect δ c) i j = _
  rw [legTwist_mul_transportDefect]

/-- **Explicit action of the carrier.**  `Γ(x, y) = a (y₀ e₀ + x₀ e₁)`. -/
theorem legCarrier_mulVec (δ c : ℂ) (x y : Fin 2 → ℂ) :
    legCarrier δ c *ᵥ Sum.elim x y
      = ![sourceScalar δ c * y 0, sourceScalar δ c * x 0] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

/-! ## The exact Gram identity -/

/-- **`Γ Γ* = |a|² I`.**  The two nonzero rows of the carrier are orthogonal of equal norm. -/
theorem legCarrier_mul_conjTranspose (δ c : ℂ) :
    legCarrier δ c * (legCarrier δ c)ᴴ = ((normSq (sourceScalar δ c) : ℝ) : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self, Matrix.one_apply] <;>
    ring

/-- **`det(Γ Γ*) = |a|⁴`.** -/
theorem det_legCarrier_mul_conjTranspose (δ c : ℂ) :
    (legCarrier δ c * (legCarrier δ c)ᴴ).det = ((normSq (sourceScalar δ c) : ℝ) : ℂ) ^ 2 := by
  rw [legCarrier_mul_conjTranspose, Matrix.det_smul, Matrix.det_one, mul_one]
  simp

/-! ## Support: all or nothing -/

/-- If the framed scalar vanishes the carrier vanishes. -/
theorem legCarrier_eq_zero (δ c : ℂ) (ha : sourceScalar δ c = 0) : legCarrier δ c = 0 := by
  ext i j
  rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp [ha]

/-- If the framed scalar is nonzero the carrier is surjective. -/
theorem legCarrier_surjective (δ c : ℂ) (ha : sourceScalar δ c ≠ 0) (v : Fin 2 → ℂ) :
    ∃ w : Fin 2 ⊕ Fin 2 → ℂ, legCarrier δ c *ᵥ w = v := by
  refine ⟨Sum.elim ![v 1 / sourceScalar δ c, 0] ![v 0 / sourceScalar δ c, 0], ?_⟩
  rw [legCarrier_mulVec]
  ext i
  fin_cases i <;> simp [mul_div_cancel₀ _ ha]

/-! ## The Moore–Penrose inverse and its exact scaling -/

/-- The Moore–Penrose inverse of the carrier when the framed scalar is nonzero. -/
def legCarrierPseudoInverse (δ c : ℂ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) ℂ :=
  ((normSq (sourceScalar δ c) : ℝ) : ℂ)⁻¹ • (legCarrier δ c)ᴴ

/-- The pseudo-inverse is a right inverse. -/
theorem legCarrier_mul_pseudoInverse (δ c : ℂ) (ha : sourceScalar δ c ≠ 0) :
    legCarrier δ c * legCarrierPseudoInverse δ c = 1 := by
  have hns : ((normSq (sourceScalar δ c) : ℝ) : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_eq_zero, Complex.normSq_eq_zero] using ha
  rw [legCarrierPseudoInverse, Matrix.mul_smul, legCarrier_mul_conjTranspose, smul_smul,
    inv_mul_cancel₀ hns, one_smul]

/-- **The adjoint carrier scales every vector by exactly `|a|`.** -/
theorem sum_normSq_conjTranspose_mulVec (δ c : ℂ) (x : Fin 2 → ℂ) :
    ∑ i, normSq (((legCarrier δ c)ᴴ *ᵥ x) i)
      = normSq (sourceScalar δ c) * ∑ i, normSq (x i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Complex.normSq_mul, Complex.normSq_conj]
  ring

/-- **`‖Γ†x‖ = ‖x‖ / |a|`.**  The Moore–Penrose inverse scales every vector by exactly `|a|⁻¹`,
so its operator norm is `|a|⁻¹`. -/
theorem sum_normSq_pseudoInverse_mulVec (δ c : ℂ) (ha : sourceScalar δ c ≠ 0)
    (x : Fin 2 → ℂ) :
    ∑ i, normSq ((legCarrierPseudoInverse δ c *ᵥ x) i)
      = (∑ i, normSq (x i)) / normSq (sourceScalar δ c) := by
  have hns : normSq (sourceScalar δ c) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using ha
  have hsmul : ∀ i, (legCarrierPseudoInverse δ c *ᵥ x) i
      = ((normSq (sourceScalar δ c) : ℝ) : ℂ)⁻¹ * (((legCarrier δ c)ᴴ *ᵥ x) i) := by
    intro i
    simp [legCarrierPseudoInverse, Matrix.smul_mulVec_assoc]
  calc ∑ i, normSq ((legCarrierPseudoInverse δ c *ᵥ x) i)
      = ∑ i, (normSq (sourceScalar δ c))⁻¹ ^ 2 * normSq (((legCarrier δ c)ᴴ *ᵥ x) i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsmul i, Complex.normSq_mul]
        simp [Complex.normSq_inv, sq]
    _ = (normSq (sourceScalar δ c))⁻¹ ^ 2 * ∑ i, normSq (((legCarrier δ c)ᴴ *ᵥ x) i) := by
        rw [Finset.mul_sum]
    _ = (∑ i, normSq (x i)) / normSq (sourceScalar δ c) := by
        rw [sum_normSq_conjTranspose_mulVec]
        field_simp
        ring

/-! ## The three shadows -/

/-- The magnitude shadow forgets the phase: every nonzero framed scalar has a distinct companion
of the same magnitude. -/
theorem normSq_forgets_phase (a : ℂ) (ha : a ≠ 0) :
    ∃ b : ℂ, b ≠ a ∧ normSq b = normSq a :=
  ⟨-a, by simpa using ha, by simp⟩

/-- The support shadow forgets the magnitude: two framed scalars can have the same vanishing
behaviour and different magnitudes. -/
theorem support_forgets_magnitude :
    ∃ a b : ℂ, ((a = 0) ↔ (b = 0)) ∧ normSq a ≠ normSq b :=
  ⟨1, 2, by norm_num, by norm_num [Complex.normSq_apply]⟩

/-- The support shadow factors through the magnitude shadow, which factors through the framed
scalar: the three route outputs are successive functions of one datum. -/
theorem shadow_tower (a : ℂ) : (a = 0) ↔ (normSq a = 0) := by
  simp [Complex.normSq_eq_zero]

/-! ## Central-twist isotriviality -/

/-- **Relative channels are blind to a central twist.**  Scaling every block transport by the same
nonzero scalar leaves every relative channel `T_j f T_i⁻¹` unchanged. -/
theorem relative_channel_central_twist {n : ℕ} (δ : ℂ) (hδ : δ ≠ 0)
    (Ti Tj f : Matrix (Fin n) (Fin n) ℂ) (hTi : IsUnit Ti.det) :
    (δ • Tj) * f * (δ • Ti)⁻¹ = Tj * f * Ti⁻¹ := by
  rw [Matrix.inv_smul _ hδ, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hδ, one_smul]
  · exact hTi

/-- A central twist does change the determinant holonomy, so the twist is visible to framed
determinant data even though it is invisible to relative channels. -/
theorem det_central_twist {n : ℕ} (δ : ℂ) (T : Matrix (Fin n) (Fin n) ℂ) :
    (δ • T).det = δ ^ n * T.det := by
  simp [Matrix.det_smul]

end HTGeometry.ConstraintRelativity
