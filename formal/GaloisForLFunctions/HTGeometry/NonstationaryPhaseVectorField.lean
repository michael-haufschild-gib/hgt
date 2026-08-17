import GaloisForLFunctions.HTGeometry.UnitCoefficientVariation

/-!
# The nonstationary-phase vector field

On the region where a phase has gradient of length at least `g`, the field `∇φ/‖∇φ‖²` differentiates
the oscillatory factor `e^{-itφ}` to `-it e^{-itφ}`: it pairs with the gradient to one.  Its length
is at most `1/g`, and its divergence -- the trace of its derivative -- is at most `(d+2)K/g²` when
the Hessian has norm at most `K` in dimension `d`.

The trace estimate is where the dimension enters: the Laplacian contributes `d` copies of the
Hessian norm and the radial term two more, both divided by the squared gradient length.  These are
the two constants that a single integration by parts against a smooth amplitude converts into a
`1/|t|` decay rate.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

section Field

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The nonstationary-phase field attached to a gradient vector. -/
noncomputable def phaseField (G : E) : E := (‖G‖ ^ 2)⁻¹ • G

/-- **The field differentiates the oscillation.**  Pairing the gradient with its phase field gives
one, so the directional derivative of `e^{-itφ}` along the field is `-it e^{-itφ}`. -/
theorem inner_phaseField_eq_one {G : E} (hG : G ≠ 0) : inner ℝ G (phaseField G) = 1 := by
  have hpos : 0 < ‖G‖ := norm_pos_iff.mpr hG
  rw [phaseField, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

/-- **The field is short.**  On `‖∇φ‖ ≥ g` the phase field has length at most `1/g`. -/
theorem norm_phaseField_le {G : E} {g : ℝ} (hg : 0 < g) (hG : g ≤ ‖G‖) :
    ‖phaseField G‖ ≤ 1 / g := by
  have hpos : 0 < ‖G‖ := lt_of_lt_of_le hg hG
  have hval : ‖phaseField G‖ = 1 / ‖G‖ := by
    rw [phaseField, norm_smul, norm_inv, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg G)]
    field_simp
  rw [hval]
  exact one_div_le_one_div_of_le hg hG

end Field

section Divergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The divergence estimate.**  The derivative of the phase field at a point with gradient `G` and
Hessian `H` is `v ↦ Hv/‖G‖² - 2⟪Hv,G⟫G/‖G‖⁴`; its trace is at most `(d+2)K/g²` in absolute value
whenever `‖G‖ ≥ g > 0` and `‖H‖ ≤ K`.  The Laplacian term contributes the dimension and the radial
term contributes two. -/
theorem abs_trace_le_of_phaseFieldDeriv (H : E →L[ℝ] E) (G : E) (L : E →ₗ[ℝ] E)
    (hL : ∀ v, L v = (‖G‖ ^ 2)⁻¹ • H v - (2 * inner ℝ (H v) G / ‖G‖ ^ 4) • G)
    {g K : ℝ} (hg : 0 < g) (hG : g ≤ ‖G‖) (hK : ‖H‖ ≤ K) :
    |LinearMap.trace ℝ E L| ≤ ((Module.finrank ℝ E : ℝ) + 2) * K / g ^ 2 := by
  classical
  set d := Module.finrank ℝ E with hd
  set b := stdOrthonormalBasis ℝ E with hb
  have hpos : 0 < ‖G‖ := lt_of_lt_of_le hg hG
  have hN2 : (0 : ℝ) < ‖G‖ ^ 2 := by positivity
  have hN4 : (0 : ℝ) < ‖G‖ ^ 4 := by positivity
  set T₁ : ℝ := ∑ i, inner ℝ (b i) (H (b i)) with hT₁
  set T₂ : ℝ := ∑ i, inner ℝ (H (b i)) G * inner ℝ (b i) G with hT₂
  -- the trace splits into the Laplacian and the radial term
  have htrace : LinearMap.trace ℝ E L = (‖G‖ ^ 2)⁻¹ * T₁ - (2 / ‖G‖ ^ 4) * T₂ := by
    rw [LinearMap.trace_eq_sum_inner L b, hT₁, hT₂, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hL, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
    ring
  -- the Laplacian term costs the dimension
  have h₁ : |T₁| ≤ (d : ℝ) * ‖H‖ := by
    have hstep : ∀ i, |inner ℝ (b i) (H (b i))| ≤ ‖H‖ := by
      intro i
      have hnorm : ‖b i‖ = 1 := b.orthonormal.1 i
      have hop : ‖H (b i)‖ ≤ ‖H‖ := by
        have hle := H.le_opNorm (b i)
        rw [hnorm, mul_one] at hle
        exact hle
      calc |inner ℝ (b i) (H (b i))| ≤ ‖b i‖ * ‖H (b i)‖ := abs_real_inner_le_norm _ _
        _ = ‖H (b i)‖ := by rw [hnorm, one_mul]
        _ ≤ ‖H‖ := hop
    calc |T₁| ≤ ∑ i, |inner ℝ (b i) (H (b i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, ‖H‖ := Finset.sum_le_sum fun i _ => hstep i
      _ = (d : ℝ) * ‖H‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the radial term is one adjoint quadratic form
  have h₂ : T₂ = inner ℝ (ContinuousLinearMap.adjoint H G) G := by
    rw [hT₂, ← b.sum_inner_mul_inner (ContinuousLinearMap.adjoint H G) G]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm (H (b i)) G]
  have h₂bound : |T₂| ≤ ‖H‖ * ‖G‖ ^ 2 := by
    rw [h₂]
    calc |inner ℝ (ContinuousLinearMap.adjoint H G) G|
        ≤ ‖ContinuousLinearMap.adjoint H G‖ * ‖G‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖ContinuousLinearMap.adjoint H‖ * ‖G‖) * ‖G‖ :=
          mul_le_mul_of_nonneg_right ((ContinuousLinearMap.adjoint H).le_opNorm _) (norm_nonneg G)
      _ = ‖H‖ * ‖G‖ ^ 2 := by
          rw [ContinuousLinearMap.adjoint.norm_map H]
          ring
  -- assemble
  have hHnn : (0 : ℝ) ≤ ‖H‖ := norm_nonneg H
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hmain : |LinearMap.trace ℝ E L| ≤ ((d : ℝ) + 2) * ‖H‖ / ‖G‖ ^ 2 := by
    rw [htrace]
    have hsplit : |(‖G‖ ^ 2)⁻¹ * T₁ - (2 / ‖G‖ ^ 4) * T₂|
        ≤ (‖G‖ ^ 2)⁻¹ * |T₁| + (2 / ‖G‖ ^ 4) * |T₂| := by
      calc |(‖G‖ ^ 2)⁻¹ * T₁ - (2 / ‖G‖ ^ 4) * T₂|
          ≤ |(‖G‖ ^ 2)⁻¹ * T₁| + |(2 / ‖G‖ ^ 4) * T₂| := by
            rw [sub_eq_add_neg]
            refine le_trans (abs_add_le _ _) ?_
            rw [abs_neg]
        _ = (‖G‖ ^ 2)⁻¹ * |T₁| + (2 / ‖G‖ ^ 4) * |T₂| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hN2)),
              abs_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < 2 / ‖G‖ ^ 4))]
    have hfirst : (‖G‖ ^ 2)⁻¹ * |T₁| ≤ (‖G‖ ^ 2)⁻¹ * ((d : ℝ) * ‖H‖) :=
      mul_le_mul_of_nonneg_left h₁ (le_of_lt (inv_pos.mpr hN2))
    have hsecond : (2 / ‖G‖ ^ 4) * |T₂| ≤ (2 / ‖G‖ ^ 4) * (‖H‖ * ‖G‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h₂bound (by positivity)
    have hcollect : (‖G‖ ^ 2)⁻¹ * ((d : ℝ) * ‖H‖) + (2 / ‖G‖ ^ 4) * (‖H‖ * ‖G‖ ^ 2)
        = ((d : ℝ) + 2) * ‖H‖ / ‖G‖ ^ 2 := by
      field_simp
    linarith [hsplit, hfirst, hsecond, hcollect.le, hcollect.ge]
  refine le_trans hmain ?_
  have hgg : g ^ 2 ≤ ‖G‖ ^ 2 := by nlinarith [hg.le, hG]
  have hg2 : (0 : ℝ) < g ^ 2 := by positivity
  have hKnn : (0 : ℝ) ≤ K := le_trans hHnn hK
  rw [div_le_div_iff₀ hN2 hg2]
  nlinarith [mul_le_mul_of_nonneg_left hK (by linarith : (0:ℝ) ≤ (d : ℝ) + 2),
    mul_le_mul_of_nonneg_left hgg (by positivity : (0:ℝ) ≤ ((d : ℝ) + 2) * K),
    mul_nonneg (by linarith : (0:ℝ) ≤ (d : ℝ) + 2) hHnn, hg2.le]

end Divergence

end GaloisForLFunctions.HTGeometry
