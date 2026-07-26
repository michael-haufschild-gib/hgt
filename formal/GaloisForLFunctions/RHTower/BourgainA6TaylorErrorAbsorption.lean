/-
# Taylor-error absorption at Bourgain's local `A₆` scale

For a block of length `M` in denominator scale `N`, the cubic Taylor
remainder is uniformly bounded on a physical cube of radius `M² / 12`
provided `M² ≤ N`.  For unit coefficients the resulting bilinear error is
`O(M⁶)`, so it has no power loss relative to the sharp local main term.
-/
import GaloisForLFunctions.RHTower.BourgainA6PeriodicAveraging

namespace RHTower

noncomputable section

/-- Uniform third-derivative coefficient on the application range
`a ≥ 1/2`. -/
theorem bourgainSquareRootThirdDerivativeBound_le_fifteen
    {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) :
    bourgainSquareRootThirdDerivativeBound a ≤ 15 := by
  have ha2 : (1 / 4 : ℝ) ≤ a ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (a - 1 / 2)]
  have h3 :=
    bourgain_rpow_neg_le_of_le
      (A := (1 / 4 : ℝ)) (y := a ^ (2 : ℕ))
      (r := (3 / 2 : ℝ)) (by norm_num) ha2 (by norm_num)
  have h5 :=
    bourgain_rpow_neg_le_of_le
      (A := (1 / 4 : ℝ)) (y := a ^ (2 : ℕ))
      (r := (5 / 2 : ℝ)) (by norm_num) ha2 (by norm_num)
  have hquarter3 :
      (1 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) = 8 := by
    norm_num [Real.rpow_def_of_pos]
  have hquarter5 :
      (1 / 4 : ℝ) ^ (-(5 / 2 : ℝ)) = 32 := by
    norm_num [Real.rpow_def_of_pos]
  rw [hquarter3] at h3
  rw [hquarter5] at h5
  unfold bourgainSquareRootThirdDerivativeBound
  nlinarith

/-- A unit-coefficient block has uniformly bounded cubic Taylor error on
the local physical radius `M² / 12`. -/
theorem bourgainSquareRootLocalTaylorError_unit_le
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hMN : M ^ (2 : ℕ) ≤ N) {a : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) :
    bourgainSquareRootLocalTaylorError
        ((M : ℝ) ^ (2 : ℕ) / 12) a
        ((M : ℝ) / (N : ℝ)) (fun _ : Fin M => (1 : ℂ)) ≤
      5 * Real.pi / 4 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN' : (M : ℝ) ^ (2 : ℕ) ≤ (N : ℝ) := by
    exact_mod_cast hMN
  have hthird :
      bourgainSquareRootThirdDerivativeBound a ≤ 15 :=
    bourgainSquareRootThirdDerivativeBound_le_fifteen ha
  have hratio0 :
      0 ≤ (M : ℝ) ^ (2 : ℕ) / (N : ℝ) := by positivity
  have hratio1 :
      (M : ℝ) ^ (2 : ℕ) / (N : ℝ) ≤ 1 :=
    (div_le_one₀ hNr).2 hMN'
  have hcub :
      ((M : ℝ) ^ (2 : ℕ) / (N : ℝ)) ^ (3 : ℕ) ≤ 1 :=
    pow_le_one₀ hratio0 hratio1
  have hsum :
      (∑ _n : Fin M, ‖(1 : ℂ)‖) = (M : ℝ) := by simp
  unfold bourgainSquareRootLocalTaylorError
  rw [hsum]
  calc
    (2 * Real.pi *
        ((((M : ℝ) ^ (2 : ℕ) / 12) *
              bourgainSquareRootThirdDerivativeBound a) *
            ((M : ℝ) / (N : ℝ)) ^ (3 : ℕ) / 2)) *
          (M : ℝ) ≤
        (2 * Real.pi *
          ((((M : ℝ) ^ (2 : ℕ) / 12) * 15) *
            ((M : ℝ) / (N : ℝ)) ^ (3 : ℕ) / 2)) *
          (M : ℝ) := by
      gcongr
    _ = (5 * Real.pi / 4) *
        (((M : ℝ) ^ (2 : ℕ) / (N : ℝ)) ^ (3 : ℕ)) := by
      field_simp
      ring
    _ ≤ 5 * Real.pi / 4 := by
      nlinarith [Real.pi_pos]

/-- Explicit bilinear Taylor-error bound for two unit blocks at the local
physical scale. -/
theorem bourgainSquareRootBilinearTaylorError_unit_le
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hMN : M ^ (2 : ℕ) ≤ N)
    {a b : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (hb : (1 / 2 : ℝ) ≤ b) :
    bourgainSquareRootBilinearTaylorError
        ((M : ℝ) ^ (2 : ℕ) / 12) a b
        ((M : ℝ) / (N : ℝ))
        (fun _ : Fin M => (1 : ℂ)) (fun _ : Fin M => (1 : ℂ)) ≤
      2 * (M : ℝ) ^ (6 : ℕ) * (5 * Real.pi / 4) ^ (6 : ℕ) +
        (5 * Real.pi / 4) ^ (12 : ℕ) := by
  let E₁ :=
    bourgainSquareRootLocalTaylorError
      ((M : ℝ) ^ (2 : ℕ) / 12) a
      ((M : ℝ) / (N : ℝ)) (fun _ : Fin M => (1 : ℂ))
  let E₂ :=
    bourgainSquareRootLocalTaylorError
      ((M : ℝ) ^ (2 : ℕ) / 12) b
      ((M : ℝ) / (N : ℝ)) (fun _ : Fin M => (1 : ℂ))
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le (by norm_num) ha
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hb
  have hδ : 0 ≤ (M : ℝ) / (N : ℝ) := by positivity
  have hR : 0 ≤ (M : ℝ) ^ (2 : ℕ) / 12 := by positivity
  have hE₁0 : 0 ≤ E₁ := by
    exact bourgainSquareRootLocalTaylorError_nonneg hR ha0 hδ _
  have hE₂0 : 0 ≤ E₂ := by
    exact bourgainSquareRootLocalTaylorError_nonneg hR hb0 hδ _
  have hE₁ : E₁ ≤ 5 * Real.pi / 4 := by
    simpa only [E₁] using
      bourgainSquareRootLocalTaylorError_unit_le hN hM hMN ha
  have hE₂ : E₂ ≤ 5 * Real.pi / 4 := by
    simpa only [E₂] using
      bourgainSquareRootLocalTaylorError_unit_le hN hM hMN hb
  have hE₁6 : E₁ ^ (6 : ℕ) ≤ (5 * Real.pi / 4) ^ (6 : ℕ) :=
    pow_le_pow_left₀ hE₁0 hE₁ 6
  have hE₂6 : E₂ ^ (6 : ℕ) ≤ (5 * Real.pi / 4) ^ (6 : ℕ) :=
    pow_le_pow_left₀ hE₂0 hE₂ 6
  have hEprod :
      E₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ) ≤
        (5 * Real.pi / 4) ^ (12 : ℕ) := by
    calc
      E₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ) ≤
          (5 * Real.pi / 4) ^ (6 : ℕ) *
            (5 * Real.pi / 4) ^ (6 : ℕ) := by
        gcongr
      _ = (5 * Real.pi / 4) ^ (12 : ℕ) := by ring
  unfold bourgainSquareRootBilinearTaylorError
  simp only [norm_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  change
    (M : ℝ) ^ (6 : ℕ) * E₂ ^ (6 : ℕ) +
        E₁ ^ (6 : ℕ) * (M : ℝ) ^ (6 : ℕ) +
        E₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ) ≤ _
  calc
    (M : ℝ) ^ (6 : ℕ) * E₂ ^ (6 : ℕ) +
          E₁ ^ (6 : ℕ) * (M : ℝ) ^ (6 : ℕ) +
          E₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ) ≤
        (M : ℝ) ^ (6 : ℕ) * (5 * Real.pi / 4) ^ (6 : ℕ) +
          (5 * Real.pi / 4) ^ (6 : ℕ) * (M : ℝ) ^ (6 : ℕ) +
          (5 * Real.pi / 4) ^ (12 : ℕ) := by
      gcongr
    _ = _ := by ring

/-- The full bilinear Taylor error is a fixed constant times `M⁶`. -/
theorem bourgainSquareRootBilinearTaylorError_unit_le_mul
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hMN : M ^ (2 : ℕ) ≤ N)
    {a b : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (hb : (1 / 2 : ℝ) ≤ b) :
    bourgainSquareRootBilinearTaylorError
        ((M : ℝ) ^ (2 : ℕ) / 12) a b
        ((M : ℝ) / (N : ℝ))
        (fun _ : Fin M => (1 : ℂ)) (fun _ : Fin M => (1 : ℂ)) ≤
      (2 * (5 * Real.pi / 4) ^ (6 : ℕ) +
          (5 * Real.pi / 4) ^ (12 : ℕ)) *
        (M : ℝ) ^ (6 : ℕ) := by
  have hbase :=
    bourgainSquareRootBilinearTaylorError_unit_le
      hN hM hMN ha hb
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM6 : (1 : ℝ) ≤ (M : ℝ) ^ (6 : ℕ) := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hMone 6
  have htail :
      (5 * Real.pi / 4) ^ (12 : ℕ) ≤
        (5 * Real.pi / 4) ^ (12 : ℕ) * (M : ℝ) ^ (6 : ℕ) := by
    calc
      (5 * Real.pi / 4) ^ (12 : ℕ) =
          (5 * Real.pi / 4) ^ (12 : ℕ) * 1 := by ring
      _ ≤ (5 * Real.pi / 4) ^ (12 : ℕ) *
          (M : ℝ) ^ (6 : ℕ) :=
        mul_le_mul_of_nonneg_left hM6 (by positivity)
  calc
    bourgainSquareRootBilinearTaylorError
          ((M : ℝ) ^ (2 : ℕ) / 12) a b
          ((M : ℝ) / (N : ℝ))
          (fun _ : Fin M => (1 : ℂ)) (fun _ : Fin M => (1 : ℂ)) ≤
        2 * (M : ℝ) ^ (6 : ℕ) *
            (5 * Real.pi / 4) ^ (6 : ℕ) +
          (5 * Real.pi / 4) ^ (12 : ℕ) := hbase
    _ ≤ 2 * (M : ℝ) ^ (6 : ℕ) *
            (5 * Real.pi / 4) ^ (6 : ℕ) +
          (5 * Real.pi / 4) ^ (12 : ℕ) *
            (M : ℝ) ^ (6 : ℕ) := by
      exact add_le_add_right htail _
    _ = _ := by ring

end

end RHTower
