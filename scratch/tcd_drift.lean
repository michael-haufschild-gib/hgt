import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveFiniteModuleNoGo

open Complex Real

namespace HTGeometry

noncomputable section

/-!
The normalized theta-source jet operator is the half-weight twist of the corpus `sl₂` field.
This scratch file tests the exact operator identities before they are used against TCD drift.
-/

def modularThetaSourcePositiveHalfTwistedE
    (P : ModularThetaSourcePositivePolynomial) :
    ModularThetaSourcePositivePolynomial :=
  modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P +
    MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B * P

def modularThetaSourcePositiveHalfTwistedF
    (P : ModularThetaSourcePositivePolynomial) :
    ModularThetaSourcePositivePolynomial :=
  modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P

def modularThetaSourcePositiveHalfTwistedH
    (P : ModularThetaSourcePositivePolynomial) :
    ModularThetaSourcePositivePolynomial :=
  modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H P +
    MvPolynomial.C (1 / 2 : ℂ) * P

theorem modularThetaSourcePositiveHalfTwistedE_add_F
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveHalfTwistedE P +
        modularThetaSourcePositiveHalfTwistedF P =
      modularThetaSourcePositiveNormalizedLie P := by
  have hLie : modularThetaSourcePositiveLie P =
      modularThetaSourcePositiveFieldLie
        modularThetaSourcePositiveVectorField P := by
    unfold modularThetaSourcePositiveLie
      modularThetaSourcePositiveFieldLie
    rw [show (Finset.univ : Finset ModularThetaSourcePositiveState) =
        {.U, .B, .Q} by
      ext i
      cases i <;> simp]
    simp
    ring
  unfold modularThetaSourcePositiveHalfTwistedE
    modularThetaSourcePositiveHalfTwistedF
    modularThetaSourcePositiveNormalizedLie
  rw [hLie]
  unfold modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E
    modularThetaSourcePositiveSl2F
  ring

private theorem halfTwisted_fieldLie_B
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
        (MvPolynomial.X .B * P) =
      -P + MvPolynomial.X .B *
        modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P := by
  rw [modularThetaSourcePositiveFieldLie_mul,
    modularThetaSourcePositiveFieldLie_X]
  simp [modularThetaSourcePositiveSl2F,
    modularThetaSourcePositiveLoweringField]

private theorem halfTwisted_fieldLie_scaledB
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
        (MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B * P) =
      -MvPolynomial.C (1 / 2 : ℂ) * P +
        MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B *
          modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P := by
  rw [modularThetaSourcePositiveFieldLie_mul,
    modularThetaSourcePositiveFieldLie_mul,
    modularThetaSourcePositiveFieldLie_C,
    modularThetaSourcePositiveFieldLie_X]
  simp [modularThetaSourcePositiveSl2F,
    modularThetaSourcePositiveLoweringField]

theorem modularThetaSourcePositiveHalfTwisted_ef
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveHalfTwistedE
        (modularThetaSourcePositiveHalfTwistedF P) -
      modularThetaSourcePositiveHalfTwistedF
        (modularThetaSourcePositiveHalfTwistedE P) =
      modularThetaSourcePositiveHalfTwistedH P := by
  unfold modularThetaSourcePositiveHalfTwistedE
    modularThetaSourcePositiveHalfTwistedF
    modularThetaSourcePositiveHalfTwistedH
  rw [modularThetaSourcePositiveFieldLie_add,
    halfTwisted_fieldLie_scaledB]
  have h := modularThetaSourcePositiveFieldLie_sl2_ef P
  linear_combination h

theorem modularThetaSourcePositiveHalfTwistedF_one :
    modularThetaSourcePositiveHalfTwistedF 1 = 0 := by
  unfold modularThetaSourcePositiveHalfTwistedF
  simpa only [map_one, map_zero] using
    modularThetaSourcePositiveFieldLie_C
      modularThetaSourcePositiveSl2F 1

theorem modularThetaSourcePositiveHalfTwistedH_one :
    modularThetaSourcePositiveHalfTwistedH 1 = MvPolynomial.C (1 / 2 : ℂ) := by
  unfold modularThetaSourcePositiveHalfTwistedH
  have h := modularThetaSourcePositiveFieldLie_C
    modularThetaSourcePositiveSl2H 1
  simpa only [map_one, map_zero, zero_add, mul_one] using congrArg
    (fun Q => Q + MvPolynomial.C (1 / 2 : ℂ) * 1) h

theorem modularThetaSourcePositiveHalfTwistedE_one :
    modularThetaSourcePositiveHalfTwistedE 1 =
      MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B := by
  unfold modularThetaSourcePositiveHalfTwistedE
  simp only [mul_one]
  rw [show (1 : ModularThetaSourcePositivePolynomial) =
      MvPolynomial.C 1 by simp]
  rw [modularThetaSourcePositiveFieldLie_C]
  simp

theorem modularThetaSourcePositiveHalfTwistedE_sq_one :
    modularThetaSourcePositiveHalfTwistedE
        (modularThetaSourcePositiveHalfTwistedE 1) =
      MvPolynomial.C 2 *
        (MvPolynomial.X .Q + MvPolynomial.C (3 / 8 : ℂ)) := by
  rw [modularThetaSourcePositiveHalfTwistedE_one]
  unfold modularThetaSourcePositiveHalfTwistedE
  rw [modularThetaSourcePositiveFieldLie_mul,
    modularThetaSourcePositiveFieldLie_C,
    modularThetaSourcePositiveFieldLie_X]
  simp [modularThetaSourcePositiveSl2E,
    modularThetaSourcePositiveVectorField,
    modularThetaSourcePositiveLoweringField]
  have h₁ : MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C 4 =
      (MvPolynomial.C 2 : ModularThetaSourcePositivePolynomial) := by
    rw [← map_mul]
    norm_num
  have h₂ : MvPolynomial.C (1 / 2 : ℂ) +
        MvPolynomial.C (1 / 2 : ℂ) ^ 2 =
      (MvPolynomial.C 2 : ModularThetaSourcePositivePolynomial) *
        MvPolynomial.C (3 / 8 : ℂ) := by
    rw [← map_pow, ← map_add, ← map_mul]
    norm_num
  calc
    _ = (MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C 4) *
          MvPolynomial.X (.Q : ModularThetaSourcePositiveState) +
        (MvPolynomial.C (1 / 2 : ℂ) +
          MvPolynomial.C (1 / 2 : ℂ) ^ 2) := by ring
    _ = MvPolynomial.C 2 * MvPolynomial.X .Q +
        MvPolynomial.C 2 * MvPolynomial.C (3 / 8 : ℂ) := by rw [h₁, h₂]
    _ = _ := by ring

theorem modularThetaSourcePositive_Q_eq_halfTwistedE_sq_vacuum_sub :
    MvPolynomial.X (.Q : ModularThetaSourcePositiveState) =
      MvPolynomial.C (1 / 2 : ℂ) *
          modularThetaSourcePositiveHalfTwistedE
            (modularThetaSourcePositiveHalfTwistedE 1) -
        MvPolynomial.C (3 / 8 : ℂ) := by
  rw [modularThetaSourcePositiveHalfTwistedE_sq_one]
  have h : MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C 2 =
      (1 : ModularThetaSourcePositivePolynomial) := by
    rw [← map_mul]
    norm_num
  calc
    _ = (1 : ModularThetaSourcePositivePolynomial) *
          (MvPolynomial.X .Q + MvPolynomial.C (3 / 8 : ℂ)) -
        MvPolynomial.C (3 / 8 : ℂ) := by ring
    _ = (MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C 2) *
          (MvPolynomial.X .Q + MvPolynomial.C (3 / 8 : ℂ)) -
        MvPolynomial.C (3 / 8 : ℂ) := by rw [h]
    _ = _ := by ring

end

end HTGeometry
