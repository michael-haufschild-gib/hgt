import Mathlib

/-!
# Isotropic law, passive gauge, intervention port, and open projective history

The source is the standard Gaussian on the plane `ℂ`, with `1` and `i` the two source coordinates
and the first one marked as an intervention port.  The passive family is the rotation orbit
`Y_t = R_t U`.

* `map_passiveRotation_sourceLaw` — every `Y_t` has the *same* law, so no passive statistic,
  moment, or positive quadratic form sees `t`; `passiveRotation_inner` is the Gram identity
  `R_t R_t^* = 1`;
* `interventionResponse_eq`, `supportLine_eq_iff` — after `do(U₁ = 0)` the response is supported on
  the line `span(R_t i)`, and two such lines agree exactly when `t ≡ s (mod π)`: the marked
  intervention sees `t` modulo `π` although nothing passive sees `t` at all;
* `supportLine_periodic`, `supportLine_int_mul_pi`, `lift_unbounded` — the projective
  interventional history is `π`-recurrent while its angle lift is unbounded;
* `map_swapSymmetry_sourceLaw`, `det_swapSymmetry`, `swap_support_ne` — the orientation-reversing
  symmetry has the same passive law and the same Gram operator but determinant `−1`, and its
  interventional support is the *other* axis.
-/

namespace GaloisForLFunctions.HTGeometry

open ProbabilityTheory MeasureTheory Complex

section PassiveGauge

/-- The passive source law: the standard Gaussian on the plane. -/
noncomputable def sourceLaw : Measure ℂ := stdGaussian ℂ

/-- The passive rotation family acting on the source. -/
noncomputable def passiveRotation (t : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ := rotation (Circle.exp t)

theorem passiveRotation_apply (t : ℝ) (z : ℂ) :
    passiveRotation t z = Complex.exp ((t : ℂ) * Complex.I) * z := by
  rw [passiveRotation, rotation_apply, Circle.coe_exp]

/-- **The passive law is completely independent of the rotation parameter.** -/
theorem map_passiveRotation_sourceLaw (t : ℝ) :
    Measure.map (passiveRotation t) sourceLaw = sourceLaw :=
  stdGaussian_map (passiveRotation t)

/-- **The Gram identity `R_t R_t^* = 1`.**  The rotation preserves every inner product, hence every
positive quadratic statistic. -/
theorem passiveRotation_inner (t : ℝ) (z w : ℂ) :
    (inner ℝ (passiveRotation t z) (passiveRotation t w) : ℝ) = inner ℝ z w :=
  (passiveRotation t).inner_map_map z w

theorem passiveRotation_norm (t : ℝ) (z : ℂ) : ‖passiveRotation t z‖ = ‖z‖ :=
  (passiveRotation t).norm_map z

end PassiveGauge

section InterventionPort

/-- The direction of the interventional response: the image of the unmarked source axis. -/
noncomputable def portDirection (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I) * Complex.I

theorem portDirection_eq (t : ℝ) : portDirection t = passiveRotation t Complex.I := by
  rw [portDirection, passiveRotation_apply]

theorem norm_portDirection (t : ℝ) : ‖portDirection t‖ = 1 := by
  rw [portDirection, norm_mul, Complex.norm_I, mul_one]
  have h : ((t : ℂ) * Complex.I) = ((t : ℝ) : ℂ) * Complex.I := rfl
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem portDirection_ne_zero (t : ℝ) : portDirection t ≠ 0 := by
  intro h
  have := norm_portDirection t
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- **The interventional response.**  After `do(U₁ = 0)` the source is `u · i` and the response is
`u` times the port direction. -/
theorem interventionResponse_eq (t : ℝ) (u : ℝ) :
    passiveRotation t ((u : ℝ) • Complex.I) = u • portDirection t := by
  rw [map_smul, portDirection_eq]

/-- The support line of the interventional response. -/
noncomputable def supportLine (t : ℝ) : Submodule ℝ ℂ := Submodule.span ℝ {portDirection t}

theorem exp_int_mul_pi_mul_I (k : ℤ) :
    Complex.exp ((k : ℂ) * (Real.pi : ℂ) * Complex.I) = (-1 : ℂ) ^ k := by
  rw [mul_assoc, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem portDirection_add_int_mul_pi (t : ℝ) (k : ℤ) :
    portDirection (t + k * Real.pi) = ((-1 : ℝ) ^ k) • portDirection t := by
  rw [portDirection, portDirection]
  have hsplit : (((t + k * Real.pi : ℝ)) : ℂ) * Complex.I
      = ((t : ℝ) : ℂ) * Complex.I + (k : ℂ) * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, exp_int_mul_pi_mul_I]
  have hcast : (((-1 : ℝ) ^ k : ℝ) : ℂ) = (-1 : ℂ) ^ k := by
    push_cast
    ring
  rw [Complex.real_smul, hcast]
  ring

/-- **The projective interventional history is `π`-recurrent.** -/
theorem supportLine_periodic (t : ℝ) : supportLine (t + Real.pi) = supportLine t := by
  have h := portDirection_add_int_mul_pi t 1
  simp only [zpow_one, Int.cast_one, one_mul] at h
  rw [supportLine, supportLine, h]
  exact Submodule.span_singleton_smul_eq (by norm_num) _

theorem supportLine_int_mul_pi (t : ℝ) (k : ℤ) :
    supportLine (t + k * Real.pi) = supportLine t := by
  rw [supportLine, supportLine, portDirection_add_int_mul_pi t k]
  refine Submodule.span_singleton_smul_eq ?_ _
  refine IsUnit.mk0 _ ?_
  exact zpow_ne_zero _ (by norm_num)

/-- **The marked intervention sees the rotation modulo `π`.** -/
theorem supportLine_eq_iff (t s : ℝ) :
    supportLine t = supportLine s ↔ ∃ k : ℤ, t - s = k * Real.pi := by
  constructor
  · intro h
    rw [supportLine, supportLine, Submodule.span_singleton_eq_span_singleton] at h
    obtain ⟨c, hc0⟩ := h
    have hc : ((c : ℝ)) • portDirection t = portDirection s := hc0
    have hnorm : ‖(c : ℝ)‖ = 1 := by
      have h1 : ‖(c : ℝ) • portDirection t‖ = ‖portDirection s‖ := by rw [hc]
      rw [norm_smul, norm_portDirection, norm_portDirection, mul_one] at h1
      exact h1
    have hc1 : (c : ℝ) = 1 ∨ (c : ℝ) = -1 := by
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp (by rwa [Real.norm_eq_abs] at hnorm) with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hexp : ∀ r : ℝ, (r : ℝ) • portDirection t = portDirection s →
        (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I) = Complex.exp ((s : ℂ) * Complex.I) := by
      intro r hr
      rw [portDirection, portDirection, Complex.real_smul, ← mul_assoc] at hr
      exact mul_right_cancel₀ Complex.I_ne_zero hr
    rcases hc1 with h1 | h1
    · rw [h1] at hc
      have h2 := hexp 1 hc
      rw [Complex.ofReal_one, one_mul] at h2
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h2
      refine ⟨2 * n, ?_⟩
      have hI : ((t : ℂ)) * Complex.I
          = (((s : ℂ)) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
        rw [hn]; ring
      have himag : ((t : ℂ)) = ((s : ℂ)) + (n : ℂ) * (2 * (Real.pi : ℂ)) :=
        mul_right_cancel₀ Complex.I_ne_zero hI
      have hreal : t = s + n * (2 * Real.pi) := by exact_mod_cast himag
      push_cast
      linarith
    · rw [h1] at hc
      have h2 := hexp (-1) hc
      rw [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul] at h2
      have h3 : Complex.exp (((t : ℂ)) * Complex.I + (Real.pi : ℂ) * Complex.I)
          = Complex.exp ((s : ℂ) * Complex.I) := by
        rw [Complex.exp_add, Complex.exp_pi_mul_I]
        linear_combination h2
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h3
      refine ⟨2 * n - 1, ?_⟩
      have hI : (((t : ℂ)) + (Real.pi : ℂ)) * Complex.I
          = (((s : ℂ)) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
        rw [add_mul, hn]; ring
      have himag : ((t : ℂ)) + (Real.pi : ℂ) = ((s : ℂ)) + (n : ℂ) * (2 * (Real.pi : ℂ)) :=
        mul_right_cancel₀ Complex.I_ne_zero hI
      have hreal : t + Real.pi = s + n * (2 * Real.pi) := by exact_mod_cast himag
      push_cast
      linarith
  · rintro ⟨k, hk⟩
    have ht : t = s + k * Real.pi := by linarith
    rw [ht, supportLine_int_mul_pi]

/-- The angle lift of the projective interventional history is unbounded. -/
theorem lift_unbounded (M : ℝ) : ∃ n : ℕ, M < (n : ℝ) * Real.pi := by
  obtain ⟨n, hn⟩ := exists_nat_gt (M / Real.pi)
  refine ⟨n, ?_⟩
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [div_lt_iff₀ hpi] at hn
  exact hn

/-- **Recurrent shadow, open lifted history.**  At the recurrent times `nπ` every passive observer
and the projective interventional support have returned, while the lift `nπ` is unbounded. -/
theorem recurrent_shadow_open_lift :
    (∀ (t : ℝ) (n : ℤ), supportLine (t + n * Real.pi) = supportLine t) ∧
      (∀ t : ℝ, Measure.map (passiveRotation t) sourceLaw = sourceLaw) ∧
      (∀ M : ℝ, ∃ n : ℕ, M < (n : ℝ) * Real.pi) :=
  ⟨supportLine_int_mul_pi, map_passiveRotation_sourceLaw, lift_unbounded⟩

end InterventionPort

section OrientationErasure

/-- The orientation-reversing source symmetry `z ↦ i · conj z`, the swap of the two source axes. -/
noncomputable def swapSymmetry : ℂ ≃ₗᵢ[ℝ] ℂ := conjLIE.trans (rotation (Circle.exp (Real.pi / 2)))

theorem swapSymmetry_apply (z : ℂ) : swapSymmetry z = Complex.I * (starRingEnd ℂ) z := by
  rw [swapSymmetry, LinearIsometryEquiv.trans_apply, rotation_apply, Circle.coe_exp]
  congr 1
  have h : (((Real.pi / 2 : ℝ)) : ℂ) * Complex.I = ((Real.pi : ℂ) / 2) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_mul_I]
  simp

theorem swapSymmetry_one : swapSymmetry 1 = Complex.I := by
  rw [swapSymmetry_apply]
  simp

theorem swapSymmetry_I : swapSymmetry Complex.I = 1 := by
  rw [swapSymmetry_apply]
  simp

/-- **The orientation-reversing symmetry has the same passive law.** -/
theorem map_swapSymmetry_sourceLaw : Measure.map swapSymmetry sourceLaw = sourceLaw :=
  stdGaussian_map swapSymmetry

/-- **and the same Gram operator.** -/
theorem swapSymmetry_inner (z w : ℂ) :
    (inner ℝ (swapSymmetry z) (swapSymmetry w) : ℝ) = inner ℝ z w :=
  swapSymmetry.inner_map_map z w

theorem toMatrix_swapSymmetry :
    LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (swapSymmetry.toLinearEquiv.toLinearMap) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, Complex.basisOneI, swapSymmetry_one, swapSymmetry_I]

/-- **The determinant separates the two orientations.** -/
theorem det_swapSymmetry :
    LinearMap.det (swapSymmetry.toLinearEquiv.toLinearMap : ℂ →ₗ[ℝ] ℂ) = -1 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, toMatrix_swapSymmetry,
    Matrix.det_fin_two_of]
  ring

theorem det_id : LinearMap.det (LinearMap.id : ℂ →ₗ[ℝ] ℂ) = 1 := LinearMap.det_id

/-- **The marked intervention separates the two orientations.**  The identity law is supported on
the `i`-axis, the swapped law on the `1`-axis, and these are different lines. -/
theorem swap_support_ne :
    Submodule.span ℝ {(1 : ℂ)} ≠ Submodule.span ℝ {Complex.I} := by
  intro h
  have hmem : Complex.I ∈ Submodule.span ℝ {(1 : ℂ)} := by
    rw [h]
    exact Submodule.mem_span_singleton_self _
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  have him := congrArg Complex.im ha
  simp [Complex.real_smul] at him

/-- **Positive passive data erase orientation; the marked port recovers it.** -/
theorem positive_erases_orientation :
    Measure.map swapSymmetry sourceLaw = sourceLaw ∧
      (∀ z w : ℂ, (inner ℝ (swapSymmetry z) (swapSymmetry w) : ℝ) = inner ℝ z w) ∧
      LinearMap.det (swapSymmetry.toLinearEquiv.toLinearMap : ℂ →ₗ[ℝ] ℂ) ≠
        LinearMap.det (LinearMap.id : ℂ →ₗ[ℝ] ℂ) ∧
      Submodule.span ℝ {swapSymmetry Complex.I} ≠ Submodule.span ℝ {Complex.I} := by
  refine ⟨map_swapSymmetry_sourceLaw, swapSymmetry_inner, ?_, ?_⟩
  · rw [det_swapSymmetry, det_id]
    norm_num
  · rw [swapSymmetry_I]
    exact swap_support_ne

end OrientationErasure

end GaloisForLFunctions.HTGeometry
