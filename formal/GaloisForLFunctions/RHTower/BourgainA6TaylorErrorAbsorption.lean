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

/-- The scalar third-derivative bound is decreasing in the positive base
parameter. -/
theorem bourgainSquareRootThirdDerivativeBound_le_of_lower
    {A a : ℝ} (hA : 0 < A) (hAa : A ≤ a) :
    bourgainSquareRootThirdDerivativeBound a ≤
      bourgainSquareRootThirdDerivativeBound A := by
  have hsq : A ^ (2 : ℕ) ≤ a ^ (2 : ℕ) :=
    pow_le_pow_left₀ hA.le hAa 2
  have h3 :=
    bourgain_rpow_neg_le_of_le
      (A := A ^ (2 : ℕ)) (y := a ^ (2 : ℕ))
      (r := (3 / 2 : ℝ)) (by positivity) hsq (by norm_num)
  have h5 :=
    bourgain_rpow_neg_le_of_le
      (A := A ^ (2 : ℕ)) (y := a ^ (2 : ℕ))
      (r := (5 / 2 : ℝ)) (by positivity) hsq (by norm_num)
  unfold bourgainSquareRootThirdDerivativeBound
  nlinarith

/-- Uniform unit-block Taylor constant for bases at least `A`. -/
def bourgainA6UnitLocalTaylorErrorConstant (A : ℝ) : ℝ :=
  Real.pi * bourgainSquareRootThirdDerivativeBound A / 12

theorem bourgainA6UnitLocalTaylorErrorConstant_nonneg
    {A : ℝ} (hA : 0 < A) :
    0 ≤ bourgainA6UnitLocalTaylorErrorConstant A := by
  unfold bourgainA6UnitLocalTaylorErrorConstant
    bourgainSquareRootThirdDerivativeBound
  positivity

/-- Local Taylor absorption with an arbitrary fixed positive lower base. -/
theorem bourgainSquareRootLocalTaylorError_unit_le_of_lower
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hMN : M ^ (2 : ℕ) ≤ N)
    {A a : ℝ} (hA : 0 < A) (hAa : A ≤ a) :
    bourgainSquareRootLocalTaylorError
        ((M : ℝ) ^ (2 : ℕ) / 12) a
        ((M : ℝ) / (N : ℝ)) (fun _ : Fin M => (1 : ℂ)) ≤
      bourgainA6UnitLocalTaylorErrorConstant A := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN' : (M : ℝ) ^ (2 : ℕ) ≤ (N : ℝ) := by
    exact_mod_cast hMN
  have hthird :=
    bourgainSquareRootThirdDerivativeBound_le_of_lower hA hAa
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
  have hK :
      0 ≤ bourgainA6UnitLocalTaylorErrorConstant A :=
    bourgainA6UnitLocalTaylorErrorConstant_nonneg hA
  unfold bourgainSquareRootLocalTaylorError
  rw [hsum]
  calc
    (2 * Real.pi *
        ((((M : ℝ) ^ (2 : ℕ) / 12) *
              bourgainSquareRootThirdDerivativeBound a) *
            ((M : ℝ) / (N : ℝ)) ^ (3 : ℕ) / 2)) *
          (M : ℝ) ≤
        (2 * Real.pi *
          ((((M : ℝ) ^ (2 : ℕ) / 12) *
              bourgainSquareRootThirdDerivativeBound A) *
            ((M : ℝ) / (N : ℝ)) ^ (3 : ℕ) / 2)) *
          (M : ℝ) := by
      gcongr
    _ = bourgainA6UnitLocalTaylorErrorConstant A *
        (((M : ℝ) ^ (2 : ℕ) / (N : ℝ)) ^ (3 : ℕ)) := by
      unfold bourgainA6UnitLocalTaylorErrorConstant
      field_simp
    _ ≤ bourgainA6UnitLocalTaylorErrorConstant A :=
      mul_le_of_le_one_right hK hcub

/-- Bilinear Taylor constant for two unit blocks with bases at least `A`. -/
def bourgainA6UnitBilinearTaylorErrorConstant (A : ℝ) : ℝ :=
  2 * bourgainA6UnitLocalTaylorErrorConstant A ^ (6 : ℕ) +
    bourgainA6UnitLocalTaylorErrorConstant A ^ (12 : ℕ)

theorem bourgainA6UnitBilinearTaylorErrorConstant_nonneg
    {A : ℝ} (hA : 0 < A) :
    0 ≤ bourgainA6UnitBilinearTaylorErrorConstant A := by
  unfold bourgainA6UnitBilinearTaylorErrorConstant
  have hK :=
    bourgainA6UnitLocalTaylorErrorConstant_nonneg hA
  positivity

/-- Taylor error is monotone in the nonnegative physical radius. -/
theorem bourgainSquareRootLocalTaylorError_mono_radius
    {R S a δ : ℝ} (_hR : 0 ≤ R) (hRS : R ≤ S)
    (ha : 0 < a) (hδ : 0 ≤ δ)
    {H : ℕ} (c : Fin H → ℂ) :
    bourgainSquareRootLocalTaylorError R a δ c ≤
      bourgainSquareRootLocalTaylorError S a δ c := by
  unfold bourgainSquareRootLocalTaylorError
    bourgainSquareRootThirdDerivativeBound
  gcongr

/-- The fixed-base bilinear error bound remains valid on every smaller
nonnegative physical radius. -/
theorem bourgainSquareRootBilinearTaylorError_unit_le_mul_of_lower_of_radius_le
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hMN : M ^ (2 : ℕ) ≤ N)
    {A a b R : ℝ} (hA : 0 < A) (hAa : A ≤ a) (hAb : A ≤ b)
    (hR : 0 ≤ R) (hRle : R ≤ (M : ℝ) ^ (2 : ℕ) / 12) :
    bourgainSquareRootBilinearTaylorError
        R a b ((M : ℝ) / (N : ℝ))
        (fun _ : Fin M => (1 : ℂ)) (fun _ : Fin M => (1 : ℂ)) ≤
      bourgainA6UnitBilinearTaylorErrorConstant A *
        (M : ℝ) ^ (6 : ℕ) := by
  let E₁ :=
    bourgainSquareRootLocalTaylorError
      R a ((M : ℝ) / (N : ℝ)) (fun _ : Fin M => (1 : ℂ))
  let E₂ :=
    bourgainSquareRootLocalTaylorError
      R b ((M : ℝ) / (N : ℝ)) (fun _ : Fin M => (1 : ℂ))
  let K : ℝ := bourgainA6UnitLocalTaylorErrorConstant A
  have ha0 : (0 : ℝ) < a := hA.trans_le hAa
  have hb0 : (0 : ℝ) < b := hA.trans_le hAb
  have hδ : 0 ≤ (M : ℝ) / (N : ℝ) := by positivity
  have hE₁0 : 0 ≤ E₁ := by
    exact bourgainSquareRootLocalTaylorError_nonneg hR ha0 hδ _
  have hE₂0 : 0 ≤ E₂ := by
    exact bourgainSquareRootLocalTaylorError_nonneg hR hb0 hδ _
  have hK : 0 ≤ K := by
    exact bourgainA6UnitLocalTaylorErrorConstant_nonneg hA
  have hE₁ : E₁ ≤ K := by
    calc
      E₁ ≤ bourgainSquareRootLocalTaylorError
          ((M : ℝ) ^ (2 : ℕ) / 12) a
          ((M : ℝ) / (N : ℝ)) (fun _ : Fin M => (1 : ℂ)) := by
        exact bourgainSquareRootLocalTaylorError_mono_radius
          hR hRle ha0 hδ _
      _ ≤ K := by
        simpa only [K] using
          bourgainSquareRootLocalTaylorError_unit_le_of_lower
            hN hM hMN hA hAa
  have hE₂ : E₂ ≤ K := by
    calc
      E₂ ≤ bourgainSquareRootLocalTaylorError
          ((M : ℝ) ^ (2 : ℕ) / 12) b
          ((M : ℝ) / (N : ℝ)) (fun _ : Fin M => (1 : ℂ)) := by
        exact bourgainSquareRootLocalTaylorError_mono_radius
          hR hRle hb0 hδ _
      _ ≤ K := by
        simpa only [K] using
          bourgainSquareRootLocalTaylorError_unit_le_of_lower
            hN hM hMN hA hAb
  have hE₁6 : E₁ ^ (6 : ℕ) ≤ K ^ (6 : ℕ) :=
    pow_le_pow_left₀ hE₁0 hE₁ 6
  have hE₂6 : E₂ ^ (6 : ℕ) ≤ K ^ (6 : ℕ) :=
    pow_le_pow_left₀ hE₂0 hE₂ 6
  have hEprod :
      E₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ) ≤ K ^ (12 : ℕ) := by
    calc
      E₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ) ≤
          K ^ (6 : ℕ) * K ^ (6 : ℕ) := by
        gcongr
      _ = K ^ (12 : ℕ) := by ring
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM6 : (1 : ℝ) ≤ (M : ℝ) ^ (6 : ℕ) := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hMone 6
  have htail : K ^ (12 : ℕ) ≤ K ^ (12 : ℕ) * (M : ℝ) ^ (6 : ℕ) := by
    calc
      K ^ (12 : ℕ) = K ^ (12 : ℕ) * 1 := by ring
      _ ≤ K ^ (12 : ℕ) * (M : ℝ) ^ (6 : ℕ) :=
        mul_le_mul_of_nonneg_left hM6 (by positivity)
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
        (M : ℝ) ^ (6 : ℕ) * K ^ (6 : ℕ) +
          K ^ (6 : ℕ) * (M : ℝ) ^ (6 : ℕ) +
          K ^ (12 : ℕ) := by
      gcongr
    _ ≤ (M : ℝ) ^ (6 : ℕ) * K ^ (6 : ℕ) +
          K ^ (6 : ℕ) * (M : ℝ) ^ (6 : ℕ) +
          K ^ (12 : ℕ) * (M : ℝ) ^ (6 : ℕ) := by
      exact add_le_add_right htail _
    _ = bourgainA6UnitBilinearTaylorErrorConstant A *
        (M : ℝ) ^ (6 : ℕ) := by
      unfold bourgainA6UnitBilinearTaylorErrorConstant
      dsimp only [K]
      ring

/-- Full bilinear Taylor error with arbitrary fixed positive lower base. -/
theorem bourgainSquareRootBilinearTaylorError_unit_le_mul_of_lower
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hMN : M ^ (2 : ℕ) ≤ N)
    {A a b : ℝ} (hA : 0 < A) (hAa : A ≤ a) (hAb : A ≤ b) :
    bourgainSquareRootBilinearTaylorError
        ((M : ℝ) ^ (2 : ℕ) / 12) a b
        ((M : ℝ) / (N : ℝ))
        (fun _ : Fin M => (1 : ℂ)) (fun _ : Fin M => (1 : ℂ)) ≤
      bourgainA6UnitBilinearTaylorErrorConstant A *
        (M : ℝ) ^ (6 : ℕ) :=
  bourgainSquareRootBilinearTaylorError_unit_le_mul_of_lower_of_radius_le
    hN hM hMN hA hAa hAb (by positivity) le_rfl

end

end RHTower
