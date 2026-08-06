import GaloisForLFunctions.HTGeometry.ObserverCongruenceIsometry

/-!
# Bounding the distance by operator norms

The distance between two observer metrics is controlled by the operator norms of the two pencils:

```text
‖P⁻¹ Q‖ ≤ C,  ‖Q⁻¹ P‖ ≤ C,  1 ≤ C   →   observerDist P Q ≤ √n · log C.
```

This is the converse direction to the exponential metric increasing property, and it is the tool
that turns any operator estimate into a bound on the distance — in particular the estimate a
basepoint change needs, where one must show that two rays stay a bounded distance apart.

The mechanism is that every eigenvalue of the relative form is an eigenvalue of `P⁻¹ Q`, on the
vector obtained by applying the inverse square root, and its reciprocal is an eigenvalue of
`Q⁻¹ P` on the same vector.  So each logarithm is bounded by `log C` in absolute value, and the
distance — the Euclidean norm of those logarithms — by `√n log C`.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## Eigenvalues of the relative form are eigenvalues of the pencil -/

theorem invOp_comp_apply_eigenvector {P Q : E →ₗ[ℂ] E} (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) (hQ : Q.IsSymmetric)
    (hPpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (i : Fin n) :
    (invOp hP hn ∘ₗ Q) (invSqrtOp hP hn ((isSymmetric_relOp hP hn hQ).eigenvectorBasis hn i))
      = (((isSymmetric_relOp hP hn hQ).eigenvalues hn i : ℝ) : ℂ)
        • invSqrtOp hP hn ((isSymmetric_relOp hP hn hQ).eigenvectorBasis hn i) := by
  show invOp hP hn (Q (invSqrtOp hP hn _)) = _
  rw [← invSqrtOp_comp_invSqrtOp hP hn hPpos,
    show invSqrtOp hP hn (Q (invSqrtOp hP hn
        ((isSymmetric_relOp hP hn hQ).eigenvectorBasis hn i)))
      = relOp hP hn Q ((isSymmetric_relOp hP hn hQ).eigenvectorBasis hn i) from rfl,
    (isSymmetric_relOp hP hn hQ).apply_eigenvectorBasis hn i, map_smul]
  rfl

theorem invSqrtOp_ne_zero {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) {v : E} (hv : v ≠ 0) :
    invSqrtOp hP hn v ≠ 0 :=
  invOp_ne_zero (isSymmetric_sqrtOp hP hn) hn
    (fun _ hw => inner_sqrtOp_pos hP hn hpos hw) hv

/-! ## The bound -/

/-- **The distance is bounded by the logarithm of the pencil norms.**  If both `P⁻¹ Q` and
`Q⁻¹ P` have norm at most `C ≥ 1`, then the distance is at most `√n log C`. -/
theorem observerDist_le_of_norm_le {P Q : E →ₗ[ℂ] E} (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) (hQ : Q.IsSymmetric)
    (hPpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re)
    (hQpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) {C : ℝ} (hC : 1 ≤ C)
    (h1 : ‖LinearMap.toContinuousLinearMap (invOp hP hn ∘ₗ Q)‖ ≤ C)
    (h2 : ‖LinearMap.toContinuousLinearMap (invOp hQ hn ∘ₗ P)‖ ≤ C) :
    observerDist hP hn hQ ≤ Real.sqrt n * Real.log C := by
  classical
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  set u := (isSymmetric_relOp hP hn hQ).eigenvectorBasis hn with hu
  set α := (isSymmetric_relOp hP hn hQ).eigenvalues hn with hα
  have hαpos : ∀ i, 0 < α i :=
    eigenvalues_pos (isSymmetric_relOp hP hn hQ) hn
      fun v hv => inner_relOp_pos hP hn hPpos hQ hQpos hv
  -- each eigenvalue and its reciprocal are bounded by `C`
  have hbound : ∀ i, |Real.log (α i)| ≤ Real.log C := by
    intro i
    set v := invSqrtOp hP hn (u i) with hv
    have hvne : v ≠ 0 := invSqrtOp_ne_zero hP hn hPpos ((u).orthonormal.ne_zero i)
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hvne
    have hev : (invOp hP hn ∘ₗ Q) v = ((α i : ℝ) : ℂ) • v :=
      invOp_comp_apply_eigenvector hP hn hQ hPpos i
    -- the eigenvalue is at most `C`
    have hle : α i ≤ C := by
      have hnorm := (LinearMap.toContinuousLinearMap (invOp hP hn ∘ₗ Q)).le_opNorm v
      rw [show (LinearMap.toContinuousLinearMap (invOp hP hn ∘ₗ Q)) v
          = ((α i : ℝ) : ℂ) • v from hev, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hαpos i)] at hnorm
      have hstep : ‖LinearMap.toContinuousLinearMap (invOp hP hn ∘ₗ Q)‖ * ‖v‖ ≤ C * ‖v‖ :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hvpos)
      exact le_of_mul_le_mul_right (le_trans hnorm hstep) hvpos
    -- the reciprocal is at most `C`
    have hQv : Q v = ((α i : ℝ) : ℂ) • P v := by
      have h := congrArg (fun z => P z) hev
      rw [show P ((invOp hP hn ∘ₗ Q) v) = Q v from comp_invOp hP hn hPpos (Q v),
        map_smul] at h
      exact h
    have hevQ : (invOp hQ hn ∘ₗ P) v = (((α i)⁻¹ : ℝ) : ℂ) • v := by
      have hne : ((α i : ℝ) : ℂ) ≠ 0 := by
        simpa using ne_of_gt (hαpos i)
      have h : invOp hQ hn (Q v) = v := invOp_comp hQ hn hQpos v
      rw [hQv, map_smul] at h
      show invOp hQ hn (P v) = _
      rw [show invOp hQ hn (P v) = (((α i : ℝ) : ℂ))⁻¹ • (((α i : ℝ) : ℂ) • invOp hQ hn (P v))
          from by rw [smul_smul, inv_mul_cancel₀ hne, one_smul], h]
      norm_cast
    have hle' : (α i)⁻¹ ≤ C := by
      have hnorm := (LinearMap.toContinuousLinearMap (invOp hQ hn ∘ₗ P)).le_opNorm v
      rw [show (LinearMap.toContinuousLinearMap (invOp hQ hn ∘ₗ P)) v
          = (((α i)⁻¹ : ℝ) : ℂ) • v from hevQ, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 (hαpos i))] at hnorm
      have hstep : ‖LinearMap.toContinuousLinearMap (invOp hQ hn ∘ₗ P)‖ * ‖v‖ ≤ C * ‖v‖ :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt hvpos)
      exact le_of_mul_le_mul_right (le_trans hnorm hstep) hvpos
    -- combine
    rcases le_or_gt 1 (α i) with h | h
    · rw [abs_of_nonneg (Real.log_nonneg h)]
      exact Real.log_le_log (hαpos i) hle
    · rw [abs_of_nonpos (Real.log_nonpos (le_of_lt (hαpos i)) (le_of_lt h)), ← Real.log_inv]
      exact Real.log_le_log (inv_pos.2 (hαpos i)) hle'
  -- assemble
  rw [observerDist, distId_eq_sqrt, ← hα]
  have hsum : ∑ i, Real.log (α i) ^ 2 ≤ (n : ℝ) * Real.log C ^ 2 := by
    calc ∑ i, Real.log (α i) ^ 2 ≤ ∑ _i : Fin n, Real.log C ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← sq_abs (Real.log (α i))]
          exact pow_le_pow_left₀ (abs_nonneg _) (hbound i) 2
      _ = (n : ℝ) * Real.log C ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i, Real.log (α i) ^ 2)
      ≤ Real.sqrt ((n : ℝ) * Real.log C ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt n * Real.log C := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hlogC]

end GaloisForLFunctions.HTGeometry
