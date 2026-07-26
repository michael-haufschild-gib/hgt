/-
# Local `A₆` power bound at an arbitrary positive base

Section 2 works on blocks bounded away from the singular endpoint by a
fixed scale-dependent constant.  This module removes the artificial
`a ≥ 1/2` restriction: for every `A > 0`, it chooses a smaller physical
radius using the explicit phase-operator norm and proves the same
`N¹⁰ M^(4+ε)` exponent, with only the constant depending on `A`.
-/
import GaloisForLFunctions.RHTower.BourgainA6LocalBallPowerBound

open MeasureTheory

namespace RHTower

noncomputable section

/-- Operator factor used to choose a physical radius simultaneously fitting
the phase map and the Taylor estimate. -/
def bourgainA6LocalOperatorFactor (A : ℝ) : ℝ :=
  max 6 (bourgainSquareRootPhaseOperatorBound A)

def bourgainA6LocalRadius (A : ℝ) (M : ℕ) : ℝ :=
  (M : ℝ) ^ (2 : ℕ) / (2 * bourgainA6LocalOperatorFactor A)

theorem bourgainA6LocalOperatorFactor_pos
    (A : ℝ) :
    0 < bourgainA6LocalOperatorFactor A := by
  unfold bourgainA6LocalOperatorFactor
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem bourgainSquareRootPhaseOperatorBound_le_localFactor
    (A : ℝ) :
    bourgainSquareRootPhaseOperatorBound A ≤
      bourgainA6LocalOperatorFactor A := by
  exact le_max_right _ _

theorem six_le_bourgainA6LocalOperatorFactor (A : ℝ) :
    (6 : ℝ) ≤ bourgainA6LocalOperatorFactor A := by
  exact le_max_left _ _

theorem bourgainA6LocalRadius_nonneg
    (A : ℝ) (M : ℕ) :
    0 ≤ bourgainA6LocalRadius A M := by
  unfold bourgainA6LocalRadius
  exact div_nonneg (sq_nonneg _)
    (mul_nonneg (by norm_num) (bourgainA6LocalOperatorFactor_pos A).le)

theorem bourgainA6LocalRadius_le_taylorRadius
    (A : ℝ) (M : ℕ) :
    bourgainA6LocalRadius A M ≤ (M : ℝ) ^ (2 : ℕ) / 12 := by
  have hQ : 0 < 2 * bourgainA6LocalOperatorFactor A := by
    exact mul_pos (by norm_num) (bourgainA6LocalOperatorFactor_pos A)
  rw [bourgainA6LocalRadius, div_le_div_iff₀ hQ (by norm_num)]
  have h6 := six_le_bourgainA6LocalOperatorFactor A
  nlinarith [sq_nonneg (M : ℝ)]

theorem bourgainA6LocalRadius_phase_fit
    (A : ℝ) (M : ℕ) :
    2 * bourgainSquareRootPhaseOperatorBound A *
        bourgainA6LocalRadius A M ≤
      (M : ℝ) ^ (2 : ℕ) := by
  have hR := bourgainA6LocalRadius_nonneg A M
  have hL :=
    bourgainSquareRootPhaseOperatorBound_le_localFactor A
  calc
    2 * bourgainSquareRootPhaseOperatorBound A *
          bourgainA6LocalRadius A M ≤
        2 * bourgainA6LocalOperatorFactor A *
          bourgainA6LocalRadius A M := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL (by norm_num)) hR
    _ = (M : ℝ) ^ (2 : ℕ) := by
      unfold bourgainA6LocalRadius
      field_simp [bourgainA6LocalOperatorFactor_pos A |>.ne']

/-- The local-radius Taylor error times volume remains below the common
`N¹⁰ M^(4+ε)` power. -/
theorem bourgainA6UnitTaylorError_localRadius_ennreal_le
    {N M : ℕ} {A ε : ℝ} (hA : 0 < A)
    (hM : 0 < M) (hMN : M ≤ N) (hε : 0 ≤ ε) :
    ENNReal.ofReal
          (bourgainA6UnitBilinearTaylorErrorConstant A *
            (M : ℝ) ^ (6 : ℕ)) *
        ENNReal.ofReal
          ((2 * bourgainA6LocalRadius A M) ^ (4 : ℕ)) ≤
      ENNReal.ofReal
        (bourgainA6UnitBilinearTaylorErrorConstant A *
          ((N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε))) := by
  have hK :
      0 ≤ bourgainA6UnitBilinearTaylorErrorConstant A :=
    bourgainA6UnitBilinearTaylorErrorConstant_nonneg hA
  have hRle := bourgainA6LocalRadius_le_taylorRadius A M
  have htwoR :
      2 * bourgainA6LocalRadius A M ≤ (M : ℝ) ^ (2 : ℕ) := by
    calc
      2 * bourgainA6LocalRadius A M ≤
          2 * ((M : ℝ) ^ (2 : ℕ) / 12) :=
        mul_le_mul_of_nonneg_left hRle (by norm_num)
      _ ≤ (M : ℝ) ^ (2 : ℕ) := by
        nlinarith [sq_nonneg (M : ℝ)]
  have hpow :
      (2 * bourgainA6LocalRadius A M) ^ (4 : ℕ) ≤
        (M : ℝ) ^ (8 : ℕ) := by
    calc
      (2 * bourgainA6LocalRadius A M) ^ (4 : ℕ) ≤
          ((M : ℝ) ^ (2 : ℕ)) ^ (4 : ℕ) :=
        pow_le_pow_left₀
          (mul_nonneg (by norm_num) (bourgainA6LocalRadius_nonneg A M))
          htwoR 4
      _ = (M : ℝ) ^ (8 : ℕ) := by ring
  have hreal :
      bourgainA6UnitBilinearTaylorErrorConstant A *
            (M : ℝ) ^ (6 : ℕ) *
          (2 * bourgainA6LocalRadius A M) ^ (4 : ℕ) ≤
        bourgainA6UnitBilinearTaylorErrorConstant A *
          ((N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
    calc
      bourgainA6UnitBilinearTaylorErrorConstant A *
            (M : ℝ) ^ (6 : ℕ) *
          (2 * bourgainA6LocalRadius A M) ^ (4 : ℕ) ≤
        bourgainA6UnitBilinearTaylorErrorConstant A *
            (M : ℝ) ^ (6 : ℕ) * (M : ℝ) ^ (8 : ℕ) := by
          gcongr
      _ = bourgainA6UnitBilinearTaylorErrorConstant A *
          (M : ℝ) ^ (14 : ℕ) := by ring
      _ ≤ bourgainA6UnitBilinearTaylorErrorConstant A *
          ((N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) :=
        mul_le_mul_of_nonneg_left
          (bourgain_natCast_fourteen_le_ten_mul_four_add hM hMN hε) hK
  rw [← ENNReal.ofReal_mul
    (mul_nonneg hK (by positivity : 0 ≤ (M : ℝ) ^ (6 : ℕ)))]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Clean local-ball power estimate for any fixed lower base `A > 0`. -/
theorem setLIntegral_bourgainA6PhysicalBlockSum_localBall_power_of_lower
    {ε : ℝ} (hε : 0 < ε) :
    ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M q₁ q₂ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hMN : M ≤ N) → (hM2N : M ^ (2 : ℕ) ≤ N) →
        (hq₁ : 0 < q₁) → (hq : q₁ + M ≤ q₂) →
        (hq₂N : q₂ ≤ N) →
        (ha : A ≤ Real.sqrt ((q₁ : ℝ) / (N : ℝ))) →
      ∀ y : BourgainPhaseSpace,
      (∫⁻ x in
        {x : BourgainPhaseSpace | ‖x‖ ≤ bourgainA6LocalRadius A M},
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) (x + y)‖ ^
                (6 : ℕ) *
            ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) (x + y)‖ ^
              (6 : ℕ))) ≤
        ENNReal.ofReal
          (C * (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
  intro A hA
  obtain ⟨C₀, hC₀, hlocal⟩ :=
    setLIntegral_bourgainSquareRootExactLocalSum_bilinear_translate_of_lower
      hε
  let C : ℝ :=
    1024 * ((512 / 3 : ℝ) * C₀ +
      bourgainA6UnitBilinearTaylorErrorConstant A)
  have hK :
      0 ≤ bourgainA6UnitBilinearTaylorErrorConstant A :=
    bourgainA6UnitBilinearTaylorErrorConstant_nonneg hA
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N M q₁ q₂ hN hM hMN hM2N hq₁ hq hq₂N ha y
  let a : ℝ := Real.sqrt ((q₁ : ℝ) / (N : ℝ))
  let b : ℝ := Real.sqrt ((q₂ : ℝ) / (N : ℝ))
  let R : ℝ := bourgainA6LocalRadius A M
  have hq12 : q₁ < q₂ := by omega
  have hab : a < b := sqrt_natCast_div_lt hN hq12
  have hAb : A ≤ b := ha.trans hab.le
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hb : b ≤ 1 := by
    dsimp [b]
    apply Real.sqrt_le_one.mpr
    exact (div_le_one hNr).2 (by exact_mod_cast hq₂N)
  have hraw :=
    hlocal hA ha hab hb (bourgainA6LocalRadius_nonneg A M) hNr
      M hM hMN' (fun _ : Fin M => (1 : ℂ))
      (fun _ : Fin M => (1 : ℂ)) y
      (bourgainA6LocalRadius_phase_fit A M)
  have herror :
      bourgainSquareRootBilinearTaylorError
          R a b ((M : ℝ) / (N : ℝ))
          (fun _ : Fin M => (1 : ℂ)) (fun _ : Fin M => (1 : ℂ)) ≤
        bourgainA6UnitBilinearTaylorErrorConstant A *
          (M : ℝ) ^ (6 : ℕ) := by
    exact
      bourgainSquareRootBilinearTaylorError_unit_le_mul_of_lower_of_radius_le
        hN hM hM2N hA ha hAb
        (bourgainA6LocalRadius_nonneg A M)
        (bourgainA6LocalRadius_le_taylorRadius A M)
  have hmain :=
    bourgainA6BlockLocalBallMainTerm_ennreal_le
      (C := C₀) (ε := ε) hN hM hC₀.le hq₁ hq hq₂N
  have herr :=
    bourgainA6UnitTaylorError_localRadius_ennreal_le
      (N := N) (M := M) hA hM hMN hε.le
  let P : ℝ :=
    (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)
  let A₀ : ℝ := (512 / 3 : ℝ) * C₀
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    positivity
  have hA₀P : 0 ≤ A₀ * P := mul_nonneg hA₀ hP
  have hKP :
      0 ≤ bourgainA6UnitBilinearTaylorErrorConstant A * P :=
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
                (bourgainSquareRootBilinearTaylorError
                  R a b ((M : ℝ) / (N : ℝ))
                  (fun _ : Fin M => (1 : ℂ))
                  (fun _ : Fin M => (1 : ℂ))) *
              ENNReal.ofReal ((2 * R) ^ (4 : ℕ))) := by
      simpa only [a, b, R,
        bourgainA6PhysicalBlockSum_eq_exactLocalSum,
        norm_one, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, one_pow] using hraw
    _ ≤ (1024 : ENNReal) *
        (ENNReal.ofReal (A₀ * P) +
          ENNReal.ofReal
            (bourgainA6UnitBilinearTaylorErrorConstant A * P)) := by
      apply mul_le_mul_right
      exact add_le_add
        (by simpa only [a, b, A₀, P, mul_assoc] using hmain)
        (calc
          ENNReal.ofReal
                (bourgainSquareRootBilinearTaylorError
                  R a b ((M : ℝ) / (N : ℝ))
                  (fun _ : Fin M => (1 : ℂ))
                  (fun _ : Fin M => (1 : ℂ))) *
              ENNReal.ofReal ((2 * R) ^ (4 : ℕ)) ≤
            ENNReal.ofReal
                (bourgainA6UnitBilinearTaylorErrorConstant A *
                  (M : ℝ) ^ (6 : ℕ)) *
              ENNReal.ofReal ((2 * R) ^ (4 : ℕ)) := by
                gcongr
          _ ≤ ENNReal.ofReal
              (bourgainA6UnitBilinearTaylorErrorConstant A * P) := by
            simpa only [R, P] using herr)
    _ = ENNReal.ofReal
        (C * (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
      rw [← ENNReal.ofReal_add hA₀P hKP,
        show (1024 : ENNReal) = ENNReal.ofReal (1024 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1024)]
      congr 1
      dsimp [C, A₀, P]
      ring

/-- A block beginning at `q` with `N ≤ Kq` has normalized square-root base
at least `1/√K`. -/
theorem one_div_sqrt_natCast_le_sqrt_natCast_div
    {N K q : ℕ} (hN : 0 < N) (hK : 0 < K)
    (hq : N ≤ K * q) :
    1 / Real.sqrt (K : ℝ) ≤
      Real.sqrt ((q : ℝ) / (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hq' : (N : ℝ) ≤ (K : ℝ) * (q : ℝ) := by
    exact_mod_cast hq
  have hfrac :
      1 / (K : ℝ) ≤ (q : ℝ) / (N : ℝ) := by
    rw [div_le_div_iff₀ hKr hNr]
    simpa [mul_comm] using hq'
  have hsqrt := Real.sqrt_le_sqrt hfrac
  have hid :
      Real.sqrt (1 / (K : ℝ)) = 1 / Real.sqrt (K : ℝ) := by
    rw [Real.sqrt_div (by positivity : 0 ≤ (1 : ℝ))]
    simp
  rwa [hid] at hsqrt

/-- Recurrence-ready local estimate: a fixed multiplicative lower bound on
the block start supplies the positive base required above. -/
theorem setLIntegral_bourgainA6PhysicalBlockSum_localBall_power_of_start
    {ε : ℝ} (hε : 0 < ε) :
    ∀ K : ℕ, 0 < K →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M q₁ q₂ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hMN : M ≤ N) → (hM2N : M ^ (2 : ℕ) ≤ N) →
        (hq₁ : 0 < q₁) → (hq : q₁ + M ≤ q₂) →
        (hq₂N : q₂ ≤ N) → (hstart : N ≤ K * q₁) →
      ∀ y : BourgainPhaseSpace,
      (∫⁻ x in
        {x : BourgainPhaseSpace |
          ‖x‖ ≤ bourgainA6LocalRadius (1 / Real.sqrt (K : ℝ)) M},
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) (x + y)‖ ^
                (6 : ℕ) *
            ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) (x + y)‖ ^
              (6 : ℕ))) ≤
        ENNReal.ofReal
          (C * (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
  intro K hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hA : 0 < 1 / Real.sqrt (K : ℝ) := by positivity
  obtain ⟨C, hC, hbound⟩ :=
    setLIntegral_bourgainA6PhysicalBlockSum_localBall_power_of_lower
      hε (1 / Real.sqrt (K : ℝ)) hA
  refine ⟨C, hC, ?_⟩
  intro N M q₁ q₂ hN hM hMN hM2N hq₁ hq hq₂N hstart y
  exact hbound N M q₁ q₂ hN hM hMN hM2N hq₁ hq hq₂N
    (one_div_sqrt_natCast_le_sqrt_natCast_div hN hK hstart) y

end

end RHTower
