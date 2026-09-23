import GaloisForLFunctions.RHTower.XiShiftedHardEdgeChebyshevExpansion

/-!
# Orthogonality and Parseval for cosine polynomials

The cosines `cos(jθ)` are orthogonal on `[-π, π]`, with square norm `2π` at frequency zero and `π`
at every positive frequency.  Hence a cosine polynomial controls its own coefficients:

`∑_{j ≤ M} b_j² ≤ (1/π)·∫_{-π}^{π} (∑_j b_j cos(jθ))² dθ`,

and Cauchy–Schwarz turns that `ℓ²` bound into the `ℓ¹` bound `∑|b_j| ≤ √(M+1)·√(∑ b_j²)` which the
strip growth estimate needs.  Degree therefore bounds the analytic continuation of a cosine
polynomial off the real axis in terms of its `L²` norm on the axis alone.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- The primitive of a scaled cosine. -/
theorem integral_cos_mul_of_ne_zero {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    (∫ θ in a..b, Real.cos (c * θ)) = (Real.sin (c * b) - Real.sin (c * a)) / c := by
  have hderiv : ∀ θ ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => Real.sin (c * u) / c) (Real.cos (c * θ)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun u : ℝ => c * u) c θ := by
      simpa using (hasDerivAt_id θ).const_mul c
    have h2 : HasDerivAt (fun u : ℝ => Real.sin (c * u)) (Real.cos (c * θ) * c) θ :=
      (Real.hasDerivAt_sin (c * θ)).comp θ h1
    have h3 := h2.div_const c
    have hval : Real.cos (c * θ) * c / c = Real.cos (c * θ) := by
      field_simp
    rwa [hval] at h3
  have hint : IntervalIntegrable (fun θ : ℝ => Real.cos (c * θ)) volume a b :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- The full-period integral of an integer-frequency cosine. -/
theorem integral_cos_int_mul (n : ℤ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.cos ((n : ℝ) * θ))
      = if n = 0 then 2 * Real.pi else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
    ring
  · have hc : ((n : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hn
    rw [if_neg hn, integral_cos_mul_of_ne_zero hc]
    have h1 : Real.sin ((n : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi n
    have h2 : Real.sin ((n : ℝ) * -Real.pi) = 0 := by
      rw [show ((n : ℝ)) * -Real.pi = -((n : ℝ) * Real.pi) by ring, Real.sin_neg, h1, neg_zero]
    rw [h1, h2]
    simp

/-- **Cosine orthogonality on the full period.** -/
theorem integral_cos_mul_cos (j k : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ))
      = if j = k then (if j = 0 then 2 * Real.pi else Real.pi) else 0 := by
  have hprod : ∀ θ : ℝ, Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)
      = (Real.cos (((j : ℤ) - (k : ℤ) : ℤ) * θ) + Real.cos (((j : ℤ) + (k : ℤ) : ℤ) * θ)) / 2 := by
    intro θ
    have hsub : (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ = (j : ℝ) * θ - (k : ℝ) * θ := by
      push_cast
      ring
    have hadd : (((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ = (j : ℝ) * θ + (k : ℝ) * θ := by
      push_cast
      ring
    rw [hsub, hadd, Real.cos_sub, Real.cos_add]
    ring
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
    (Real.cos (((j : ℤ) - (k : ℤ) : ℤ) * θ) + Real.cos (((j : ℤ) + (k : ℤ) : ℤ) * θ)) / 2)
    (fun θ _ => hprod θ)]
  have hint1 : IntervalIntegrable
      (fun θ : ℝ => Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ)) volume (-Real.pi) Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun θ : ℝ => Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ)) volume (-Real.pi) Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hint1 hint2,
    integral_cos_int_mul, integral_cos_int_mul]
  rcases eq_or_ne j k with rfl | hjk
  · rw [if_pos rfl, sub_self, if_pos rfl]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · norm_num
    · have hne : ((j : ℤ) + (j : ℤ)) ≠ 0 := by
        have : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
        omega
      rw [if_neg hne, if_neg (by omega : ¬ j = 0)]
      ring
  · have hsub : ((j : ℤ) - (k : ℤ)) ≠ 0 := by
      intro h0
      exact hjk (by omega)
    rw [if_neg hjk, if_neg hsub]
    rcases Nat.eq_zero_or_pos (j + k) with hz | hp
    · exfalso
      omega
    · have hne : ((j : ℤ) + (k : ℤ)) ≠ 0 := by
        have : (0 : ℤ) < (j : ℤ) + (k : ℤ) := by exact_mod_cast hp
        omega
      rw [if_neg hne]
      norm_num

/-- The cosine polynomial attached to a coefficient family. -/
def cosPoly (M : ℕ) (b : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), b j * Real.cos ((j : ℝ) * θ)

/-- **Parseval for cosine polynomials.** -/
theorem integral_cosPoly_sq (M : ℕ) (b : ℕ → ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, cosPoly M b θ ^ (2 : ℕ))
      = ∑ j ∈ Finset.range (M + 1), (if j = 0 then 2 * Real.pi else Real.pi) * b j ^ (2 : ℕ) := by
  have hexpand : ∀ θ : ℝ, cosPoly M b θ ^ (2 : ℕ)
      = ∑ j ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
        (b j * b k) * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) := by
    intro θ
    rw [cosPoly, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
    ∑ j ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
      (b j * b k) * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)))
    (fun θ _ => hexpand θ)]
  have hintj : ∀ j ∈ Finset.range (M + 1), IntervalIntegrable
      (fun θ : ℝ => ∑ k ∈ Finset.range (M + 1),
        (b j * b k) * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)))
      volume (-Real.pi) Real.pi := by
    intro j _
    refine Continuous.intervalIntegrable ?_ _ _
    refine continuous_finsetSum _ fun k _ => ?_
    exact continuous_const.mul
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  rw [intervalIntegral.integral_finsetSum hintj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hintk : ∀ k ∈ Finset.range (M + 1), IntervalIntegrable
      (fun θ : ℝ => (b j * b k) * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)))
      volume (-Real.pi) Real.pi := by
    intro k _
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  rw [intervalIntegral.integral_finsetSum hintk]
  have hterm : ∀ k ∈ Finset.range (M + 1),
      (∫ θ in (-Real.pi)..Real.pi,
        (b j * b k) * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)))
        = (b j * b k) * (if j = k then (if j = 0 then 2 * Real.pi else Real.pi) else 0) := by
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_cos_mul_cos]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
    ring
  · intro k _ hkj
    rw [if_neg (fun h => hkj h.symm), mul_zero]
  · intro hjnot
    exact absurd hj hjnot

/-- The `ℓ²` mass of the coefficients is controlled by the `L²` norm. -/
theorem sum_sq_le_integral_cosPoly_sq (M : ℕ) (b : ℕ → ℝ) :
    Real.pi * ∑ j ∈ Finset.range (M + 1), b j ^ (2 : ℕ)
      ≤ ∫ θ in (-Real.pi)..Real.pi, cosPoly M b θ ^ (2 : ℕ) := by
  rw [integral_cosPoly_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases eq_or_ne j 0 with rfl | hj
  · rw [if_pos rfl]
    nlinarith [sq_nonneg (b 0), Real.pi_pos]
  · rw [if_neg hj]

/-- The `ℓ¹` mass of the coefficients through Cauchy--Schwarz. -/
theorem sum_abs_le_sqrt_card_mul (M : ℕ) (b : ℕ → ℝ) :
    ∑ j ∈ Finset.range (M + 1), |b j|
      ≤ Real.sqrt ((M : ℝ) + 1) * Real.sqrt (∑ j ∈ Finset.range (M + 1), b j ^ (2 : ℕ)) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (M + 1))
    (fun _ : ℕ => (1 : ℝ)) (fun j => |b j|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    sq_abs] at hcs
  have hnn : 0 ≤ ∑ j ∈ Finset.range (M + 1), |b j| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcard : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  rw [hcard] at hcs
  have hsq : 0 ≤ (M : ℝ) + 1 := by positivity
  have hsum : 0 ≤ ∑ j ∈ Finset.range (M + 1), b j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ j ∈ Finset.range (M + 1), |b j|
      = Real.sqrt ((∑ j ∈ Finset.range (M + 1), |b j|) ^ (2 : ℕ)) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (((M : ℝ) + 1) * ∑ j ∈ Finset.range (M + 1), b j ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hcs
    _ = Real.sqrt ((M : ℝ) + 1) * Real.sqrt (∑ j ∈ Finset.range (M + 1), b j ^ (2 : ℕ)) :=
        Real.sqrt_mul hsq _

end RHTower

end
