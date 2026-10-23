import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The radial loss law of signed continuation

A source moving with a parameter is a path `ε ↦ u(ε)` in the receiver's inner product space, with
energy `E = ‖u‖²` and signed work `W = ⟪u, u'⟫`.  The continuation layer measures the **relative
loss** `L = −2W/(1 + E)`, whose integral over `[a, c]` is `log(1 + E(a)) − log(1 + E(c))`
(`hasDerivAt_log_one_add_energy`).

* **Only radial motion is charged** (`radialLoss_add_tangential`, `radialLoss_of_inner_eq_zero`):
  writing `u' = α u + v` with `v ⊥ u`, the loss is `−2α E/(1 + E)`.  Covariance of the tangent with
  directions orthogonal to the source costs nothing; motion along the source costs exactly its
  radial rate, and only shrinking (`α < 0` in the direction of continuation) is a debt.
* **Rates** (`abs_radialLoss_mul_norm_le`, `abs_radialLoss_le`): `|L| · ‖u‖ ≤ |⟪u, u'⟫|` and
  `|L| ≤ ‖u'‖`; integrated (`abs_log_energy_sub_le`), the log-energy changes by at most the length
  of the source path.  The tangent-norm receiver is therefore the crude, orientation-blind bound;
  the exact continuation criterion reads the signed radial rate only.
* **Free motion** (`log_energy_eq_of_tangential`): a path that is everywhere tangential keeps its
  energy.
-/

open RealInnerProductSpace Set

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The relative loss of a source `u` moving with tangent `u'`. -/
def radialLoss (u u' : E) : ℝ := -(2 * ⟪u, u'⟫) / (1 + ‖u‖ ^ 2)

omit [InnerProductSpace ℝ E] in
theorem one_add_norm_sq_pos (u : E) : 0 < 1 + ‖u‖ ^ 2 := by positivity

/-- **Only radial motion is charged.** -/
theorem radialLoss_add_tangential (u v : E) (α : ℝ) (h : ⟪u, v⟫ = 0) :
    radialLoss u (α • u + v) = -(2 * α * ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2) := by
  unfold radialLoss
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, h]
  ring_nf

theorem radialLoss_of_inner_eq_zero {u v : E} (h : ⟪u, v⟫ = 0) : radialLoss u v = 0 := by
  simp [radialLoss, h]

/-- The loss is at most the radial speed: `|L| ‖u‖ ≤ |⟪u, u'⟫|`. -/
theorem abs_radialLoss_mul_norm_le (u u' : E) : |radialLoss u u'| * ‖u‖ ≤ |⟪u, u'⟫| := by
  unfold radialLoss
  have hpos := one_add_norm_sq_pos u
  rw [abs_div, abs_neg, abs_mul, abs_two, abs_of_pos hpos, div_mul_eq_mul_div,
    div_le_iff₀ hpos]
  have h1 : 2 * ‖u‖ ≤ 1 + ‖u‖ ^ 2 := by nlinarith [sq_nonneg (‖u‖ - 1)]
  have h2 : 0 ≤ |⟪u, u'⟫| := abs_nonneg _
  nlinarith

/-- The loss is at most the tangent length: `|L| ≤ ‖u'‖`. -/
theorem abs_radialLoss_le (u u' : E) : |radialLoss u u'| ≤ ‖u'‖ := by
  unfold radialLoss
  have hpos := one_add_norm_sq_pos u
  rw [abs_div, abs_neg, abs_mul, abs_two, abs_of_pos hpos, div_le_iff₀ hpos]
  have h1 := abs_real_inner_le_norm u u'
  have h2 : 2 * ‖u‖ ≤ 1 + ‖u‖ ^ 2 := by nlinarith [sq_nonneg (‖u‖ - 1)]
  have h3 := norm_nonneg u'
  nlinarith

/-- **The log-energy evolves by minus the loss.** -/
theorem hasDerivAt_log_one_add_energy {γ : ℝ → E} {γ' : E} {t : ℝ} (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => Real.log (1 + ‖γ s‖ ^ 2)) (-radialLoss (γ t) γ') t := by
  have h1 : HasDerivAt (fun s => ‖γ s‖ ^ 2) (2 * ⟪γ t, γ'⟫) t := h.norm_sq
  have h2 := (h1.const_add 1).log (one_add_norm_sq_pos (γ t)).ne'
  convert h2 using 1
  unfold radialLoss
  ring

/-- **Path-length bound**: `|log(1 + E(c)) − log(1 + E(a))| ≤ B (c − a)` when `‖u'‖ ≤ B`. -/
theorem abs_log_energy_sub_le {γ γ' : ℝ → E} {a c B : ℝ} (hac : a ≤ c)
    (hd : ∀ t ∈ Icc a c, HasDerivAt γ (γ' t) t) (hB : ∀ t ∈ Icc a c, ‖γ' t‖ ≤ B) :
    |Real.log (1 + ‖γ c‖ ^ 2) - Real.log (1 + ‖γ a‖ ^ 2)| ≤ B * (c - a) := by
  have hderiv : ∀ t ∈ Icc a c, HasDerivWithinAt (fun s => Real.log (1 + ‖γ s‖ ^ 2))
      (-radialLoss (γ t) (γ' t)) (Icc a c) t :=
    fun t ht => (hasDerivAt_log_one_add_energy (hd t ht)).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico a c, ‖-radialLoss (γ t) (γ' t)‖ ≤ B := by
    intro t ht
    rw [norm_neg, Real.norm_eq_abs]
    exact (abs_radialLoss_le _ _).trans (hB t (Ico_subset_Icc_self ht))
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound c ⟨hac, le_rfl⟩
  simpa [Real.norm_eq_abs] using this

/-- **Free motion**: an everywhere tangential path keeps its energy. -/
theorem log_energy_eq_of_tangential {γ γ' : ℝ → E} {a c : ℝ} (hac : a ≤ c)
    (hd : ∀ t ∈ Icc a c, HasDerivAt γ (γ' t) t) (htan : ∀ t ∈ Icc a c, ⟪γ t, γ' t⟫ = 0) :
    ‖γ c‖ = ‖γ a‖ := by
  have hderiv : ∀ t ∈ Icc a c, HasDerivWithinAt (fun s => Real.log (1 + ‖γ s‖ ^ 2))
      0 (Icc a c) t := by
    intro t ht
    have := (hasDerivAt_log_one_add_energy (hd t ht)).hasDerivWithinAt (s := Icc a c)
    rwa [radialLoss_of_inner_eq_zero (htan t ht), neg_zero] at this
  have hbound : ∀ t ∈ Ico a c, ‖(0 : ℝ)‖ ≤ 0 := fun _ _ => by simp
  have h0 := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound c ⟨hac, le_rfl⟩
  simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at h0
  have hlog := Real.log_injOn_pos (one_add_norm_sq_pos (γ c)) (one_add_norm_sq_pos (γ a)) h0
  have hsq : ‖γ c‖ ^ 2 = ‖γ a‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
