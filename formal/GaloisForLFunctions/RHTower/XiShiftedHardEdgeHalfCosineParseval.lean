import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCosineParseval

/-!
# Half-integer cosine polynomials and the `L²` Bernstein inequality

The half-density factor `cos(θ/2)` of the rational hard-edge test shifts every frequency by one
half, so `cos(θ/2)·q(θ)` is a cosine polynomial in the frequencies `j + 1/2`.  Those are still
orthogonal on the full period — the difference and the sum of two half-integer frequencies are
integers, and the sum never vanishes — with common square norm `π`.  Parseval then gives the `L²`
Bernstein inequality in its sharpest elementary form:

`‖G'‖₂² = π·∑ (j+1/2)²c_j² ≤ (M+1/2)²·‖G‖₂²`,

no interpolation formula required.  This is the equicontinuity half of the Kolmogorov–Riesz
criterion for the hard-edge packets.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- **Half-integer cosine orthogonality.** -/
theorem integral_halfCos_mul_halfCos (j k : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi,
        Real.cos (((j : ℝ) + 1 / 2) * θ) * Real.cos (((k : ℝ) + 1 / 2) * θ))
      = if j = k then Real.pi else 0 := by
  have hprod : ∀ θ : ℝ, Real.cos (((j : ℝ) + 1 / 2) * θ) * Real.cos (((k : ℝ) + 1 / 2) * θ)
      = (Real.cos (((j : ℤ) - (k : ℤ) : ℤ) * θ)
          + Real.cos (((j : ℤ) + (k : ℤ) + 1 : ℤ) * θ)) / 2 := by
    intro θ
    have hsub : (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ
        = ((j : ℝ) + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * θ := by
      push_cast
      ring
    have hadd : (((j : ℤ) + (k : ℤ) + 1 : ℤ) : ℝ) * θ
        = ((j : ℝ) + 1 / 2) * θ + ((k : ℝ) + 1 / 2) * θ := by
      push_cast
      ring
    rw [hsub, hadd, Real.cos_sub, Real.cos_add]
    ring
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
    (Real.cos (((j : ℤ) - (k : ℤ) : ℤ) * θ)
      + Real.cos (((j : ℤ) + (k : ℤ) + 1 : ℤ) * θ)) / 2) (fun θ _ => hprod θ)]
  have hint1 : IntervalIntegrable
      (fun θ : ℝ => Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ)) volume (-Real.pi) Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun θ : ℝ => Real.cos ((((j : ℤ) + (k : ℤ) + 1 : ℤ) : ℝ) * θ)) volume
        (-Real.pi) Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hsumne : ((j : ℤ) + (k : ℤ) + 1) ≠ 0 := by omega
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hint1 hint2,
    integral_cos_int_mul, integral_cos_int_mul, if_neg hsumne]
  rcases eq_or_ne j k with rfl | hjk
  · rw [if_pos rfl, sub_self, if_pos rfl]
    ring
  · have hsub : ((j : ℤ) - (k : ℤ)) ≠ 0 := by
      intro h0
      exact hjk (by omega)
    rw [if_neg hjk, if_neg hsub]
    norm_num

/-- **Half-integer sine orthogonality.** -/
theorem integral_halfSin_mul_halfSin (j k : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi,
        Real.sin (((j : ℝ) + 1 / 2) * θ) * Real.sin (((k : ℝ) + 1 / 2) * θ))
      = if j = k then Real.pi else 0 := by
  have hprod : ∀ θ : ℝ, Real.sin (((j : ℝ) + 1 / 2) * θ) * Real.sin (((k : ℝ) + 1 / 2) * θ)
      = (Real.cos (((j : ℤ) - (k : ℤ) : ℤ) * θ)
          - Real.cos (((j : ℤ) + (k : ℤ) + 1 : ℤ) * θ)) / 2 := by
    intro θ
    have hsub : (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ
        = ((j : ℝ) + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * θ := by
      push_cast
      ring
    have hadd : (((j : ℤ) + (k : ℤ) + 1 : ℤ) : ℝ) * θ
        = ((j : ℝ) + 1 / 2) * θ + ((k : ℝ) + 1 / 2) * θ := by
      push_cast
      ring
    rw [hsub, hadd, Real.cos_sub, Real.cos_add]
    ring
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
    (Real.cos (((j : ℤ) - (k : ℤ) : ℤ) * θ)
      - Real.cos (((j : ℤ) + (k : ℤ) + 1 : ℤ) * θ)) / 2) (fun θ _ => hprod θ)]
  have hint1 : IntervalIntegrable
      (fun θ : ℝ => Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ)) volume (-Real.pi) Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun θ : ℝ => Real.cos ((((j : ℤ) + (k : ℤ) + 1 : ℤ) : ℝ) * θ)) volume
        (-Real.pi) Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hsumne : ((j : ℤ) + (k : ℤ) + 1) ≠ 0 := by omega
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hint1 hint2,
    integral_cos_int_mul, integral_cos_int_mul, if_neg hsumne]
  rcases eq_or_ne j k with rfl | hjk
  · rw [if_pos rfl, sub_self, if_pos rfl]
    ring
  · have hsub : ((j : ℤ) - (k : ℤ)) ≠ 0 := by
      intro h0
      exact hjk (by omega)
    rw [if_neg hjk, if_neg hsub]
    norm_num

/-- A half-integer cosine polynomial. -/
def halfCosPoly (M : ℕ) (c : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), c j * Real.cos (((j : ℝ) + 1 / 2) * θ)

/-- Its termwise derivative. -/
def halfCosPolyDeriv (M : ℕ) (c : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), (-(c j * ((j : ℝ) + 1 / 2))) * Real.sin (((j : ℝ) + 1 / 2) * θ)

private theorem integral_halfPoly_sq_aux (M : ℕ) (w : ℕ → ℝ)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ j, Continuous (φ j))
    (horth : ∀ j k, (∫ θ in (-Real.pi)..Real.pi, φ j θ * φ k θ)
      = if j = k then Real.pi else 0) :
    (∫ θ in (-Real.pi)..Real.pi, (∑ j ∈ Finset.range (M + 1), w j * φ j θ) ^ (2 : ℕ))
      = Real.pi * ∑ j ∈ Finset.range (M + 1), w j ^ (2 : ℕ) := by
  have hexpand : ∀ θ : ℝ, (∑ j ∈ Finset.range (M + 1), w j * φ j θ) ^ (2 : ℕ)
      = ∑ j ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
        (w j * w k) * (φ j θ * φ k θ) := by
    intro θ
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
    ∑ j ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
      (w j * w k) * (φ j θ * φ k θ)) (fun θ _ => hexpand θ)]
  have hintj : ∀ j ∈ Finset.range (M + 1), IntervalIntegrable
      (fun θ : ℝ => ∑ k ∈ Finset.range (M + 1), (w j * w k) * (φ j θ * φ k θ))
      volume (-Real.pi) Real.pi := by
    intro j _
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_finsetSum _ fun k _ => continuous_const.mul ((hφ j).mul (hφ k))
  rw [intervalIntegral.integral_finsetSum hintj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hintk : ∀ k ∈ Finset.range (M + 1), IntervalIntegrable
      (fun θ : ℝ => (w j * w k) * (φ j θ * φ k θ)) volume (-Real.pi) Real.pi := by
    intro k _
    exact (continuous_const.mul ((hφ j).mul (hφ k))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hintk]
  have hterm : ∀ k ∈ Finset.range (M + 1),
      (∫ θ in (-Real.pi)..Real.pi, (w j * w k) * (φ j θ * φ k θ))
        = (w j * w k) * (if j = k then Real.pi else 0) := by
    intro k _
    rw [intervalIntegral.integral_const_mul, horth]
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single j]
  · rw [if_pos rfl]
    ring
  · intro k _ hkj
    rw [if_neg (fun h => hkj h.symm), mul_zero]
  · intro hjnot
    exact absurd hj hjnot

/-- **Parseval for half-integer cosine polynomials.** -/
theorem integral_halfCosPoly_sq (M : ℕ) (c : ℕ → ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, halfCosPoly M c θ ^ (2 : ℕ))
      = Real.pi * ∑ j ∈ Finset.range (M + 1), c j ^ (2 : ℕ) :=
  integral_halfPoly_sq_aux M c (fun j θ => Real.cos (((j : ℝ) + 1 / 2) * θ))
    (fun _ => Real.continuous_cos.comp (continuous_const.mul continuous_id))
    integral_halfCos_mul_halfCos

/-- **Parseval for the derivative.** -/
theorem integral_halfCosPolyDeriv_sq (M : ℕ) (c : ℕ → ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, halfCosPolyDeriv M c θ ^ (2 : ℕ))
      = Real.pi * ∑ j ∈ Finset.range (M + 1), (c j * ((j : ℝ) + 1 / 2)) ^ (2 : ℕ) := by
  have h := integral_halfPoly_sq_aux M (fun j => -(c j * ((j : ℝ) + 1 / 2)))
    (fun j θ => Real.sin (((j : ℝ) + 1 / 2) * θ))
    (fun _ => Real.continuous_sin.comp (continuous_const.mul continuous_id))
    integral_halfSin_mul_halfSin
  simp only [halfCosPolyDeriv]
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The `L²` Bernstein inequality for half-integer cosine polynomials.** -/
theorem integral_halfCosPolyDeriv_sq_le (M : ℕ) (c : ℕ → ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, halfCosPolyDeriv M c θ ^ (2 : ℕ))
      ≤ ((M : ℝ) + 1 / 2) ^ (2 : ℕ) * ∫ θ in (-Real.pi)..Real.pi, halfCosPoly M c θ ^ (2 : ℕ) := by
  rw [integral_halfCosPolyDeriv_sq, integral_halfCosPoly_sq]
  have hinner : ∑ j ∈ Finset.range (M + 1), (c j * ((j : ℝ) + 1 / 2)) ^ (2 : ℕ)
      ≤ ((M : ℝ) + 1 / 2) ^ (2 : ℕ) * ∑ j ∈ Finset.range (M + 1), c j ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    simp only [Finset.mem_range] at hj
    have hjM : (j : ℝ) + 1 / 2 ≤ (M : ℝ) + 1 / 2 := by
      have hjr : (j : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 hj
      linarith
    have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 / 2 := by positivity
    have hsq : ((j : ℝ) + 1 / 2) ^ (2 : ℕ) ≤ ((M : ℝ) + 1 / 2) ^ (2 : ℕ) := by nlinarith [hj0, hjM]
    calc (c j * ((j : ℝ) + 1 / 2)) ^ (2 : ℕ) = c j ^ (2 : ℕ) * ((j : ℝ) + 1 / 2) ^ (2 : ℕ) := by ring
      _ ≤ c j ^ (2 : ℕ) * ((M : ℝ) + 1 / 2) ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = ((M : ℝ) + 1 / 2) ^ (2 : ℕ) * c j ^ (2 : ℕ) := by ring
  calc Real.pi * ∑ j ∈ Finset.range (M + 1), (c j * ((j : ℝ) + 1 / 2)) ^ (2 : ℕ)
      ≤ Real.pi * (((M : ℝ) + 1 / 2) ^ (2 : ℕ) * ∑ j ∈ Finset.range (M + 1), c j ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hinner Real.pi_pos.le
    _ = ((M : ℝ) + 1 / 2) ^ (2 : ℕ) * (Real.pi * ∑ j ∈ Finset.range (M + 1), c j ^ (2 : ℕ)) := by ring

end RHTower

end
