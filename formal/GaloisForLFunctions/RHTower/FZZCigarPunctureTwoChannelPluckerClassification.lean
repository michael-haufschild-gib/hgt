import GaloisForLFunctions.RHTower.FZZCigarPunctureAffineChannelClassification

/-!
# FZZ puncture two-channel Plücker classification

For a two-channel affine FZZ puncture source, this file classifies exactly when a
nonzero amplitude can lie in one internal row kernel and still carry a point mode.
The criterion is the vanishing of the Plücker minor between the internal and
on-shell rows together with nonvanishing of the minor between the internal and
transverse-slope rows.  A canonical example then shows that unconstrained matrix
mixing realizes the condition at every target energy, so matrix coupling alone
cannot select the zeta-zero energies.
-/

open Complex MeasureTheory Set
open scoped ENNReal BigOperators Matrix

namespace RHTower

noncomputable section

/-- Two-channel coordinate vector. -/
def fzzPunctureTwoChannelVector (z0 z1 : ℂ) : Fin 2 → ℂ :=
  ![z0, z1]

@[simp] theorem fzzPunctureAffineCollectiveOnShell_two
    (a0 a1 c0 c1 : ℂ) :
    fzzPunctureAffineCollectiveOnShell
        (fzzPunctureTwoChannelVector a0 a1)
        (fzzPunctureTwoChannelVector c0 c1) =
      a0 * c0 + a1 * c1 := by
  simp [fzzPunctureAffineCollectiveOnShell, fzzPunctureTwoChannelVector,
    Fin.sum_univ_two]

@[simp] theorem fzzPunctureAffineCollectiveSlope_two
    (a0 a1 d0 d1 : ℂ) :
    fzzPunctureAffineCollectiveSlope
        (fzzPunctureTwoChannelVector a0 a1)
        (fzzPunctureTwoChannelVector d0 d1) =
      a0 * d0 + a1 * d1 := by
  simp [fzzPunctureAffineCollectiveSlope, fzzPunctureTwoChannelVector,
    Fin.sum_univ_two]

/-- Nonzero internal-row kernel amplitude carrying a two-channel affine puncture mode. -/
def FZZPunctureTwoChannelInternalRowPointMode
    (E : ℝ) (p q c0 c1 d0 d1 : ℂ) : Prop :=
  (p ≠ 0 ∨ q ≠ 0) ∧
    ∃ a0 a1 : ℂ,
      (a0 ≠ 0 ∨ a1 ≠ 0) ∧
        p * a0 + q * a1 = 0 ∧
          FZZPunctureAffineChannelPointMode E
            (fzzPunctureTwoChannelVector a0 a1)
            (fzzPunctureTwoChannelVector c0 c1)
            (fzzPunctureTwoChannelVector d0 d1)

/-- Exact matrix-channel occurrence law in Plücker coordinates. -/
theorem fzzPunctureTwoChannelInternalRowPointMode_iff
    (E : ℝ) (p q c0 c1 d0 d1 : ℂ) :
    FZZPunctureTwoChannelInternalRowPointMode E p q c0 c1 d0 d1 ↔
      (p ≠ 0 ∨ q ≠ 0) ∧
        q * c0 - p * c1 = 0 ∧
          q * d0 - p * d1 ≠ 0 := by
  constructor
  · rintro ⟨hpq, a0, a1, ha, hrow, hmode⟩
    have hclass := (fzzPunctureAffineChannelPointMode_iff E
      (fzzPunctureTwoChannelVector a0 a1)
      (fzzPunctureTwoChannelVector c0 c1)
      (fzzPunctureTwoChannelVector d0 d1)).mp hmode
    simp only [fzzPunctureAffineCollectiveOnShell_two,
      fzzPunctureAffineCollectiveSlope_two] at hclass
    rcases hclass with ⟨hnode, hslope⟩
    refine ⟨hpq, ?_, ?_⟩
    · rcases ha with ha0 | ha1
      · apply (mul_left_cancel₀ ha0)
        linear_combination q * hnode - c1 * hrow
      · apply (mul_left_cancel₀ ha1)
        linear_combination c0 * hrow - p * hnode
    · intro hminor
      rcases hpq with hp | hq
      · have hpSlope : p * (a0 * d0 + a1 * d1) = 0 := by
          linear_combination d0 * hrow - a1 * hminor
        exact hslope ((mul_eq_zero.mp hpSlope).resolve_left hp)
      · have hqSlope : q * (a0 * d0 + a1 * d1) = 0 := by
          linear_combination d1 * hrow + a0 * hminor
        exact hslope ((mul_eq_zero.mp hqSlope).resolve_left hq)
  · rintro ⟨hpq, hnode, hslope⟩
    refine ⟨hpq, q, -p, ?_, ?_, ?_⟩
    · rcases hpq with hp | hq
      · exact Or.inr (neg_ne_zero.mpr hp)
      · exact Or.inl hq
    · ring
    · apply (fzzPunctureAffineChannelPointMode_iff E
        (fzzPunctureTwoChannelVector q (-p))
        (fzzPunctureTwoChannelVector c0 c1)
        (fzzPunctureTwoChannelVector d0 d1)).mpr
      simp only [fzzPunctureAffineCollectiveOnShell_two,
        fzzPunctureAffineCollectiveSlope_two]
      constructor
      · linear_combination hnode
      · intro hzero
        apply hslope
        linear_combination hzero

/-- If internal row is aligned with slope row, no two-channel puncture mode can survive. -/
theorem not_fzzPunctureTwoChannelInternalRowPointMode_of_slope_aligned
    (E : ℝ) (p q c0 c1 d0 d1 : ℂ)
    (halign : q * d0 - p * d1 = 0) :
    ¬ FZZPunctureTwoChannelInternalRowPointMode E p q c0 c1 d0 d1 := by
  rw [fzzPunctureTwoChannelInternalRowPointMode_iff]
  exact fun h => h.2.2 halign

/-- Canonical nodal/transverse matrix channel realizes a point mode at every target energy. -/
theorem fzzPunctureCanonicalTwoChannelInternalRowPointMode (E : ℝ) :
    FZZPunctureTwoChannelInternalRowPointMode E
      1 0 1 0 0 1 := by
  rw [fzzPunctureTwoChannelInternalRowPointMode_iff]
  norm_num

end

end RHTower
