import GaloisForLFunctions.HTGeometry.KleinGordonNoCascade

/-!
# The energy spectrum of a clock is frozen

In a weak real frequency-diagonal potential each band of frequencies carries an independent clock, and
the trapping law applies to each of them separately. So the energy in a band is confined, for all
time, to a fixed interval around its own initial value — the same interval `[(1−b)/(1+b),
(1+b)/(1−b)]` that governs the total energy — while the band energies continue to add up to the total.

The clock's whole spectral profile is therefore pinned: no band gains or loses more than a fixed
factor, ever. This is strictly stronger than the trapping of the total energy, which by itself would
permit energy to move freely between frequencies.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Frozen

variable {φ : E → ℂ} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The energy below a cutoff is trapped**, two-sidedly, around its own initial value. -/
theorem kgFieldEnergy_low_trapped (hφ : Measurable φ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ)
    (R : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    (‖kgLowPassOp R g‖ ^ (2 : ℕ) + ‖kgLowPassOp R h‖ ^ (2 : ℕ)) / ((1 + b) / (1 - b))
        ≤ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (kgLowPassOp R g) (kgLowPassOp R h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (kgLowPassOp R g) (kgLowPassOp R h) t‖ ^ (2 : ℕ)
      ∧ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (kgLowPassOp R g) (kgLowPassOp R h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (kgLowPassOp R g) (kgLowPassOp R h) t‖ ^ (2 : ℕ)
        ≤ (1 + b) / (1 - b) * (‖kgLowPassOp R g‖ ^ (2 : ℕ) + ‖kgLowPassOp R h‖ ^ (2 : ℕ)) :=
  kgFieldEnergy_trapped_diagonal hφ hb0 hb1 hC hreal (kgLowPassOp R g) (kgLowPassOp R h) t

set_option maxHeartbeats 1000000 in
/-- **The energy above a cutoff is trapped**, two-sidedly, around its own initial value. -/
theorem kgFieldEnergy_high_trapped (hφ : Measurable φ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ)
    (R : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    (‖g - kgLowPassOp R g‖ ^ (2 : ℕ) + ‖h - kgLowPassOp R h‖ ^ (2 : ℕ)) / ((1 + b) / (1 - b))
        ≤ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)
      ∧ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)
        ≤ (1 + b) / (1 - b) * (‖g - kgLowPassOp R g‖ ^ (2 : ℕ) + ‖h - kgLowPassOp R h‖ ^ (2 : ℕ)) :=
  kgFieldEnergy_trapped_diagonal hφ hb0 hb1 hC hreal (g - kgLowPassOp R g)
    (h - kgLowPassOp R h) t

set_option maxHeartbeats 1000000 in
/-- **The energy in any annulus of frequencies is trapped**, two-sidedly, around its own initial
value. -/
theorem kgFieldEnergy_annulus_trapped (hφ : Measurable φ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ)
    (R₁ R₂ : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    (‖kgAnnulusOp R₁ R₂ g‖ ^ (2 : ℕ) + ‖kgAnnulusOp R₁ R₂ h‖ ^ (2 : ℕ)) / ((1 + b) / (1 - b))
        ≤ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
      ∧ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
        ≤ (1 + b) / (1 - b) * (‖kgAnnulusOp R₁ R₂ g‖ ^ (2 : ℕ) + ‖kgAnnulusOp R₁ R₂ h‖ ^ (2 : ℕ)) :=
  kgFieldEnergy_trapped_diagonal hφ hb0 hb1 hC hreal (kgAnnulusOp R₁ R₂ g)
    (kgAnnulusOp R₁ R₂ h) t

set_option maxHeartbeats 1000000 in
/-- The energy of a clock splits across an annulus, in the autonomous register. -/
theorem kgFieldEnergy_annulus_split_static (hφ : Measurable φ) (hb0 : 0 ≤ b)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (R₁ R₂ : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad (fourierMulCLM hφ hb0 hC) g h t‖ ^ (2 : ℕ)
        + ‖kgFieldVel (fourierMulCLM hφ hb0 hC) g h t‖ ^ (2 : ℕ)
      = (‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ))
        + (‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)) := by
  have hsplit := kgFieldEnergyT_annulus_split (w := fun _ : ℝ => φ) (fun _ => hφ) hb0
    (fun _ => hC) (fun _ => continuous_const) R₁ R₂ g h t
  simp only [kgFieldGradT_const, kgFieldVelT_const] at hsplit
  exact hsplit

set_option maxHeartbeats 1000000 in
/-- **The spectral profile of a clock is frozen.** The energy carried by an annulus of frequencies
never leaves a fixed interval around its initial value, and the annulus energies still add up to the
total — so no band gains or loses more than the fixed factor `(1+b)/(1−b)`, at any time. -/
theorem kgFieldEnergy_spectrum_frozen (hφ : Measurable φ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ)
    (R₁ R₂ : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad (fourierMulCLM hφ hb0 hC) g h t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC) g h t‖ ^ (2 : ℕ)
        = (‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
                (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
            + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
                (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ))
          + (‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
                (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
            + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
                (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ))
      ∧ (‖kgAnnulusOp R₁ R₂ g‖ ^ (2 : ℕ) + ‖kgAnnulusOp R₁ R₂ h‖ ^ (2 : ℕ)) / ((1 + b) / (1 - b))
          ≤ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
                (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
            + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
                (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
      ∧ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
                (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
            + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
                (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
          ≤ (1 + b) / (1 - b) * (‖kgAnnulusOp R₁ R₂ g‖ ^ (2 : ℕ) + ‖kgAnnulusOp R₁ R₂ h‖ ^ (2 : ℕ)) := by
  obtain ⟨hlow, hhigh⟩ := kgFieldEnergy_annulus_trapped hφ hb0 hb1 hC hreal R₁ R₂ g h t
  exact ⟨kgFieldEnergy_annulus_split_static hφ hb0 hC R₁ R₂ g h t, hlow, hhigh⟩

end Frozen

end GaloisForLFunctions.HTGeometry
