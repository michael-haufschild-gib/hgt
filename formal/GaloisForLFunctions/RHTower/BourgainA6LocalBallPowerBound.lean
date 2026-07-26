/-
# Clean power bound on a local `A₆` ball

The separated-block Jacobian and the absorbed Taylor error are combined
here.  A translated radius-`M² / 12` ball has bilinear sixth moment
`Oε(N¹⁰ M^(4+ε))`, uniformly in its center.
-/
import GaloisForLFunctions.RHTower.BourgainA6LocalBallEstimate

open MeasureTheory

namespace RHTower

noncomputable section

/-- The reciprocal combined determinant factors into its osculating and
parabola-scale components. -/
theorem bourgainA6BlockPhaseDeterminant_inv_factorization
    (N M q₁ q₂ : ℕ) :
    |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| =
      |(3 *
          (Real.sqrt ((q₂ : ℝ) / (N : ℝ)) -
            Real.sqrt ((q₁ : ℝ) / (N : ℝ))) ^ (4 : ℕ) /
          (32 *
            Real.sqrt ((q₁ : ℝ) / (N : ℝ)) ^ (3 : ℕ) *
            Real.sqrt ((q₂ : ℝ) / (N : ℝ)) ^ (3 : ℕ)))⁻¹| *
        |(((M : ℝ) / (N : ℝ)) ^ (6 : ℕ))⁻¹| := by
  unfold bourgainA6BlockPhaseDeterminant
  dsimp only
  rw [mul_inv, abs_mul]
  ring

/-- Real quadratic main term on one radius-`M² / 12` ball. -/
def bourgainA6BlockLocalBallMainTerm
    (N M q₁ q₂ : ℕ) (C ε : ℝ) : ℝ :=
  |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| *
    ((M : ℝ) ^ (8 : ℕ) *
      (C * (M : ℝ) ^ ε *
        (M : ℝ) ^ (3 : ℕ) * (M : ℝ) ^ (3 : ℕ)))

/-- Determinant separation puts the local-ball main term at scale
`N¹⁰ M^(4+ε)`. -/
theorem bourgainA6BlockLocalBallMainTerm_le
    {N M q₁ q₂ : ℕ} {C ε : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hC : 0 ≤ C)
    (hq₁ : 0 < q₁) (hq : q₁ + M ≤ q₂) (hq₂N : q₂ ≤ N) :
    bourgainA6BlockLocalBallMainTerm N M q₁ q₂ C ε ≤
      (512 / 3 : ℝ) * C *
        (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hJ :=
    abs_inv_bourgainA6BlockPhaseDeterminant_le
      hN hM hq₁ hq hq₂N
  let B : ℝ :=
    (M : ℝ) ^ (8 : ℕ) *
      (C * (M : ℝ) ^ ε *
        (M : ℝ) ^ (3 : ℕ) * (M : ℝ) ^ (3 : ℕ))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hpow :
      (M : ℝ) ^ (4 + ε) =
        (M : ℝ) ^ (4 : ℕ) * (M : ℝ) ^ ε := by
    rw [Real.rpow_add hMr]
    norm_num [Real.rpow_natCast]
  unfold bourgainA6BlockLocalBallMainTerm
  change
    |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| * B ≤ _
  calc
    |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| * B ≤
        ((512 / 3 : ℝ) * ((N : ℝ) / (M : ℝ)) ^ (10 : ℕ)) * B :=
      mul_le_mul_of_nonneg_right hJ hB0
    _ = (512 / 3 : ℝ) * C *
        (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε) := by
      rw [hpow]
      dsimp [B]
      field_simp

/-- `ENNReal` form of the local-ball main-term estimate. -/
theorem bourgainA6BlockLocalBallMainTerm_ennreal_le
    {N M q₁ q₂ : ℕ} {C ε : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hC : 0 ≤ C)
    (hq₁ : 0 < q₁) (hq : q₁ + M ≤ q₂) (hq₂N : q₂ ≤ N) :
    ENNReal.ofReal
          |(3 *
              (Real.sqrt ((q₂ : ℝ) / (N : ℝ)) -
                Real.sqrt ((q₁ : ℝ) / (N : ℝ))) ^ (4 : ℕ) /
              (32 *
                Real.sqrt ((q₁ : ℝ) / (N : ℝ)) ^ (3 : ℕ) *
                Real.sqrt ((q₂ : ℝ) / (N : ℝ)) ^ (3 : ℕ)))⁻¹| *
        ENNReal.ofReal |(((M : ℝ) / (N : ℝ)) ^ (6 : ℕ))⁻¹| *
        ENNReal.ofReal
          ((M : ℝ) ^ (8 : ℕ) *
            (C * (M : ℝ) ^ ε *
              (M : ℝ) ^ (3 : ℕ) * (M : ℝ) ^ (3 : ℕ))) ≤
      ENNReal.ofReal
        ((512 / 3 : ℝ) * C *
          (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
  let A : ℝ :=
    |(3 *
        (Real.sqrt ((q₂ : ℝ) / (N : ℝ)) -
          Real.sqrt ((q₁ : ℝ) / (N : ℝ))) ^ (4 : ℕ) /
        (32 *
          Real.sqrt ((q₁ : ℝ) / (N : ℝ)) ^ (3 : ℕ) *
          Real.sqrt ((q₂ : ℝ) / (N : ℝ)) ^ (3 : ℕ)))⁻¹|
  let S : ℝ := |(((M : ℝ) / (N : ℝ)) ^ (6 : ℕ))⁻¹|
  let B : ℝ :=
    (M : ℝ) ^ (8 : ℕ) *
      (C * (M : ℝ) ^ ε *
        (M : ℝ) ^ (3 : ℕ) * (M : ℝ) ^ (3 : ℕ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have heq : A * S =
      |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| := by
    dsimp [A, S]
    rw [bourgainA6BlockPhaseDeterminant_inv_factorization]
  calc
    ENNReal.ofReal A * ENNReal.ofReal S * ENNReal.ofReal B =
        ENNReal.ofReal ((A * S) * B) := by
      rw [← ENNReal.ofReal_mul hA,
        ← ENNReal.ofReal_mul (mul_nonneg hA hS)]
    _ = ENNReal.ofReal
        (bourgainA6BlockLocalBallMainTerm N M q₁ q₂ C ε) := by
      congr 1
      unfold bourgainA6BlockLocalBallMainTerm
      rw [heq]
    _ ≤ ENNReal.ofReal
        ((512 / 3 : ℝ) * C *
          (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) :=
      ENNReal.ofReal_le_ofReal
        (bourgainA6BlockLocalBallMainTerm_le
          hN hM hC hq₁ hq hq₂N)

/-- Multiplying the absorbed Taylor error by the local ball volume costs at
most `M¹⁴`. -/
theorem bourgainA6UnitTaylorError_localBallVolume_le (M : ℕ) :
    bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (6 : ℕ) *
        (2 * ((M : ℝ) ^ (2 : ℕ) / 12)) ^ (4 : ℕ) ≤
      bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (14 : ℕ) := by
  have hK : 0 ≤ bourgainA6UnitTaylorErrorConstant := by
    unfold bourgainA6UnitTaylorErrorConstant
    positivity
  calc
    bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (6 : ℕ) *
          (2 * ((M : ℝ) ^ (2 : ℕ) / 12)) ^ (4 : ℕ) =
        (bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (14 : ℕ)) /
          1296 := by ring
    _ ≤ bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (14 : ℕ) := by
      apply div_le_self
      · positivity
      · norm_num

/-- At positive integral scales, `M¹⁴` is bounded by the same
`N¹⁰ M^(4+ε)` power as the quadratic main term. -/
theorem bourgain_natCast_fourteen_le_ten_mul_four_add
    {N M : ℕ} {ε : ℝ} (hM : 0 < M) (hMN : M ≤ N)
    (hε : 0 ≤ ε) :
    (M : ℝ) ^ (14 : ℕ) ≤
      (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMNr : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hpowMN :
      (M : ℝ) ^ (10 : ℕ) ≤ (N : ℝ) ^ (10 : ℕ) :=
    pow_le_pow_left₀ hMr.le hMNr 10
  have hrpow :
      (1 : ℝ) ≤ (M : ℝ) ^ ε := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hMone hε
  rw [Real.rpow_add hMr]
  norm_num [Real.rpow_natCast]
  calc
    (M : ℝ) ^ (14 : ℕ) =
        (M : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 : ℕ) := by ring
    _ ≤ (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 : ℕ) := by
      gcongr
    _ ≤ (N : ℝ) ^ (10 : ℕ) *
        ((M : ℝ) ^ (4 : ℕ) * (M : ℝ) ^ ε) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (M : ℝ) ^ (4 : ℕ) =
            (M : ℝ) ^ (4 : ℕ) * 1 := by ring
        _ ≤ (M : ℝ) ^ (4 : ℕ) * (M : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ = _ := by ring

/-- `ENNReal` form of Taylor-error absorption at the local-ball power
scale. -/
theorem bourgainA6UnitTaylorError_localBallVolume_ennreal_le
    {N M : ℕ} {ε : ℝ} (hM : 0 < M) (hMN : M ≤ N)
    (hε : 0 ≤ ε) :
    ENNReal.ofReal
          (bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (6 : ℕ)) *
        ENNReal.ofReal
          ((2 * ((M : ℝ) ^ (2 : ℕ) / 12)) ^ (4 : ℕ)) ≤
      ENNReal.ofReal
        (bourgainA6UnitTaylorErrorConstant *
          ((N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε))) := by
  have hK : 0 ≤ bourgainA6UnitTaylorErrorConstant := by
    unfold bourgainA6UnitTaylorErrorConstant
    positivity
  have hfirst :
      0 ≤ bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (6 : ℕ) := by
    positivity
  have hreal :
      bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (6 : ℕ) *
          (2 * ((M : ℝ) ^ (2 : ℕ) / 12)) ^ (4 : ℕ) ≤
        bourgainA6UnitTaylorErrorConstant *
          ((N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
    calc
      bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (6 : ℕ) *
            (2 * ((M : ℝ) ^ (2 : ℕ) / 12)) ^ (4 : ℕ) ≤
          bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (14 : ℕ) :=
        bourgainA6UnitTaylorError_localBallVolume_le M
      _ ≤ bourgainA6UnitTaylorErrorConstant *
          ((N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) :=
        mul_le_mul_of_nonneg_left
          (bourgain_natCast_fourteen_le_ten_mul_four_add hM hMN hε) hK
  rw [← ENNReal.ofReal_mul hfirst]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Clean unconditional local-ball power estimate for separated literal
`A₆` blocks. -/
theorem setLIntegral_bourgainA6PhysicalBlockSum_localBall_power
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M q₁ q₂ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hMN : M ≤ N) → (hM2N : M ^ (2 : ℕ) ≤ N) →
        (hq₁ : 0 < q₁) → (hq : q₁ + M ≤ q₂) →
        (hq₂N : q₂ ≤ N) →
        (ha : (1 / 2 : ℝ) ≤ Real.sqrt ((q₁ : ℝ) / (N : ℝ))) →
      ∀ y : BourgainPhaseSpace,
      let R : ℝ := (M : ℝ) ^ (2 : ℕ) / 12
      (∫⁻ x in {x : BourgainPhaseSpace | ‖x‖ ≤ R},
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) (x + y)‖ ^
                (6 : ℕ) *
            ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) (x + y)‖ ^
              (6 : ℕ))) ≤
        ENNReal.ofReal
          (C * (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
  obtain ⟨C₀, hC₀, hlocal⟩ :=
    setLIntegral_bourgainA6PhysicalBlockSum_localBall_unit_subpower hε
  let C : ℝ :=
    1024 * ((512 / 3 : ℝ) * C₀ +
      bourgainA6UnitTaylorErrorConstant)
  have hK : 0 ≤ bourgainA6UnitTaylorErrorConstant := by
    unfold bourgainA6UnitTaylorErrorConstant
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N M q₁ q₂ hN hM hMN hM2N hq₁ hq hq₂N ha y
  dsimp only
  let a : ℝ := Real.sqrt ((q₁ : ℝ) / (N : ℝ))
  let b : ℝ := Real.sqrt ((q₂ : ℝ) / (N : ℝ))
  let R : ℝ := (M : ℝ) ^ (2 : ℕ) / 12
  have hq12 : q₁ < q₂ := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : b ≤ 1 := by
    dsimp [b]
    apply Real.sqrt_le_one.mpr
    exact (div_le_one hNr).2 (by exact_mod_cast hq₂N)
  have hraw :=
    hlocal N M q₁ q₂ hN hM hMN hM2N hq12 ha hb y
  have hmain :=
    bourgainA6BlockLocalBallMainTerm_ennreal_le
      (C := C₀) (ε := ε) hN hM hC₀.le hq₁ hq hq₂N
  have herr :=
    bourgainA6UnitTaylorError_localBallVolume_ennreal_le
      (N := N) (M := M) hM hMN hε.le
  let P : ℝ :=
    (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)
  let A : ℝ := (512 / 3 : ℝ) * C₀
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hAP : 0 ≤ A * P := mul_nonneg hA hP
  have hKP : 0 ≤ bourgainA6UnitTaylorErrorConstant * P :=
    mul_nonneg hK hP
  calc
    (∫⁻ x in {x : BourgainPhaseSpace | ‖x‖ ≤ R},
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) (x + y)‖ ^
                (6 : ℕ) *
            ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) (x + y)‖ ^
              (6 : ℕ))) ≤
        (1024 : ENNReal) *
          (ENNReal.ofReal
                |(3 * (b - a) ^ (4 : ℕ) /
                  (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹| *
              ENNReal.ofReal
                |(((M : ℝ) / (N : ℝ)) ^ (6 : ℕ))⁻¹| *
              ENNReal.ofReal
                ((M : ℝ) ^ (8 : ℕ) *
                  (C₀ * (M : ℝ) ^ ε *
                    (M : ℝ) ^ (3 : ℕ) * (M : ℝ) ^ (3 : ℕ))) +
            ENNReal.ofReal
                (bourgainA6UnitTaylorErrorConstant *
                  (M : ℝ) ^ (6 : ℕ)) *
              ENNReal.ofReal ((2 * R) ^ (4 : ℕ))) := by
      simpa only [a, b, R] using hraw
    _ ≤ (1024 : ENNReal) *
        (ENNReal.ofReal (A * P) +
          ENNReal.ofReal (bourgainA6UnitTaylorErrorConstant * P)) := by
      apply mul_le_mul_right
      exact add_le_add
        (by simpa only [a, b, A, P, mul_assoc] using hmain)
        (by simpa only [R, P] using herr)
    _ = ENNReal.ofReal
        (C * (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
      rw [← ENNReal.ofReal_add hAP hKP,
        show (1024 : ENNReal) = ENNReal.ofReal (1024 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1024)]
      congr 1
      dsimp [C, A, P]
      ring

end

end RHTower
