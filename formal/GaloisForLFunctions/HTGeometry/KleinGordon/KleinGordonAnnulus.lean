import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandEnergySplit

/-!
# Frequency annuli

A band of frequencies is an annulus, not a disc. The annulus symbol is the indicator of
`R₁ < ‖ξ‖ ≤ R₂`: it is real, takes only the values `0` and `1`, and — when `R₁ ≤ R₂` — is the
difference of the two low-pass symbols. So the annulus operator is a self-adjoint projection and a
Fourier multiplier, hence a symmetry of every frequency-diagonal background.

Everything proved for the low-pass projections therefore holds for annuli: a clock's trajectory
decouples across any annulus of frequencies, and its energy is the sum of the energy carried inside
the annulus and the energy carried outside it, at every instant of time.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The annulus symbol -/

/-- The symbol of the annulus projection: one on `R₁ < ‖ξ‖ ≤ R₂`, zero elsewhere. -/
def kgAnnulus (R₁ R₂ : ℝ) (ξ : E) : ℂ := if R₁ < ‖ξ‖ ∧ ‖ξ‖ ≤ R₂ then 1 else 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgAnnulus (R₁ R₂ : ℝ) : Measurable (kgAnnulus (E := E) R₁ R₂) :=
  Measurable.ite
    ((measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_le continuous_norm.measurable measurable_const))
    measurable_const measurable_const

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgAnnulus_le (R₁ R₂ : ℝ) (ξ : E) : ‖kgAnnulus R₁ R₂ ξ‖ ≤ 1 := by
  rw [kgAnnulus]
  split <;> simp

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The annulus symbol is real. -/
theorem starRingEnd_kgAnnulus (R₁ R₂ : ℝ) (ξ : E) :
    (starRingEnd ℂ) (kgAnnulus R₁ R₂ ξ) = kgAnnulus R₁ R₂ ξ := by
  simp only [kgAnnulus]
  split <;> simp

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The annulus symbol takes only the values `0` and `1`. -/
theorem kgAnnulus_mul_self (R₁ R₂ : ℝ) (ξ : E) :
    kgAnnulus R₁ R₂ ξ = kgAnnulus R₁ R₂ ξ * kgAnnulus R₁ R₂ ξ := by
  simp only [kgAnnulus]
  split <;> simp

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- On an ordered pair of radii the annulus symbol is the difference of the two low-pass symbols. -/
theorem kgAnnulus_eq_sub {R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) (ξ : E) :
    kgAnnulus R₁ R₂ ξ = kgLowPass R₂ ξ - kgLowPass R₁ ξ := by
  simp only [kgAnnulus, kgLowPass]
  by_cases h₁ : ‖ξ‖ ≤ R₁
  · have h₂ : ‖ξ‖ ≤ R₂ := le_trans h₁ hR
    have hnot : ¬(R₁ < ‖ξ‖ ∧ ‖ξ‖ ≤ R₂) := fun hc => absurd h₁ (not_le.mpr hc.1)
    rw [if_neg hnot, if_pos h₂, if_pos h₁, sub_self]
  · by_cases h₂ : ‖ξ‖ ≤ R₂
    · have hmem : R₁ < ‖ξ‖ ∧ ‖ξ‖ ≤ R₂ := ⟨not_le.mp h₁, h₂⟩
      rw [if_pos hmem, if_pos h₂, if_neg h₁, sub_zero]
    · have hnot : ¬(R₁ < ‖ξ‖ ∧ ‖ξ‖ ≤ R₂) := fun hc => absurd hc.2 h₂
      rw [if_neg hnot, if_neg h₂, if_neg h₁, sub_self]

/-! ## The annulus projection -/

/-- **The annulus projection**, the Fourier multiplier cutting out the frequencies
`R₁ < ‖ξ‖ ≤ R₂`. -/
def kgAnnulusOp (R₁ R₂ : ℝ) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMulCLM (measurable_kgAnnulus (E := E) R₁ R₂) zero_le_one (norm_kgAnnulus_le R₁ R₂)

theorem norm_kgAnnulusOp_le (R₁ R₂ : ℝ) : ‖kgAnnulusOp (E := E) R₁ R₂‖ ≤ 1 :=
  norm_fourierMulCLM_le _ _ _

/-- **The annulus projection is idempotent.** -/
theorem kgAnnulusOp_idem (R₁ R₂ : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgAnnulusOp R₁ R₂ (kgAnnulusOp R₁ R₂ x) = kgAnnulusOp R₁ R₂ x := by
  have hae : ∀ᵐ ξ : E ∂(volume : Measure E),
      kgAnnulus R₁ R₂ ξ = kgAnnulus R₁ R₂ ξ * kgAnnulus R₁ R₂ ξ :=
    Eventually.of_forall (kgAnnulus_mul_self R₁ R₂)
  have hcomp := fourierMulCLM_comp (measurable_kgAnnulus (E := E) R₁ R₂)
    (measurable_kgAnnulus (E := E) R₁ R₂) (measurable_kgAnnulus (E := E) R₁ R₂)
    zero_le_one (norm_kgAnnulus_le R₁ R₂) zero_le_one (norm_kgAnnulus_le R₁ R₂)
    zero_le_one (norm_kgAnnulus_le R₁ R₂) hae
  exact ContinuousLinearMap.ext_iff.mp hcomp x

/-- **The annulus projection is self-adjoint**, hence an orthogonal projection. -/
theorem kgAnnulusOp_inner (R₁ R₂ : ℝ) (f g : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgAnnulusOp R₁ R₂ f) g : ℂ) = inner ℂ f (kgAnnulusOp R₁ R₂ g) :=
  fourierMulCLM_inner (measurable_kgAnnulus (E := E) R₁ R₂) zero_le_one (norm_kgAnnulus_le R₁ R₂)
    (starRingEnd_kgAnnulus R₁ R₂) f g

/-- On an ordered pair of radii the annulus projection is the difference of the two low-pass
projections. -/
theorem kgAnnulusOp_eq_sub {R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) :
    kgAnnulusOp (E := E) R₁ R₂ = kgLowPassOp R₂ - kgLowPassOp R₁ :=
  fourierMulCLM_sub (measurable_kgLowPass (E := E) R₂) (measurable_kgLowPass (E := E) R₁)
    (measurable_kgAnnulus (E := E) R₁ R₂) zero_le_one (norm_kgLowPass_le R₂) zero_le_one
    (norm_kgLowPass_le R₁) zero_le_one (norm_kgAnnulus_le R₁ R₂)
    (Eventually.of_forall (kgAnnulus_eq_sub hR))

/-! ## The clock decomposes over annuli -/

section AnnulusSplit

variable {b : ℝ} {w : ℝ → E → ℂ}

/-- **A clock in a frequency-diagonal background decouples across every annulus of frequencies.** -/
theorem kgFieldStateT_annulus_decouple (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (R₁ R₂ : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t
        = kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t
          + kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t
      ∧ kgDiagOp (kgAnnulusOp R₁ R₂)
            (kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t)
          = kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t
      ∧ kgDiagOp (kgAnnulusOp R₁ R₂)
            (kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t) = 0 :=
  kgFieldStateT_decouple hb0 (fun _ => norm_fourierMulCLM_le _ _ _) hWs
    (fourierMulCLM_kgCosOp_comm (measurable_kgAnnulus (E := E) R₁ R₂) zero_le_one
      (norm_kgAnnulus_le R₁ R₂))
    (fourierMulCLM_kgSinOp_comm (measurable_kgAnnulus (E := E) R₁ R₂) zero_le_one
      (norm_kgAnnulus_le R₁ R₂))
    (fourierMulCLM_kgFreqInvOp_comm (measurable_kgAnnulus (E := E) R₁ R₂) zero_le_one
      (norm_kgAnnulus_le R₁ R₂))
    (fun r x => fourierMulCLM_comm (measurable_kgAnnulus (E := E) R₁ R₂) (hw r) zero_le_one
      (norm_kgAnnulus_le R₁ R₂) hb0 (hwb r) x)
    (kgAnnulusOp_idem R₁ R₂) g h t

/-- **A clock's energy is the energy inside an annulus plus the energy outside it**, at every
instant. -/
theorem kgFieldEnergyT_annulus_split (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (R₁ R₂ : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t‖ ^ (2 : ℕ)
      = (‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ))
        + (‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ (2 : ℕ)) := by
  obtain ⟨hsum, hin, hout⟩ := kgFieldStateT_annulus_decouple hw hb0 hwb hWs R₁ R₂ g h t
  rw [kgFieldEnergyT_eq_norm_sq, kgFieldEnergyT_eq_norm_sq, kgFieldEnergyT_eq_norm_sq, hsum]
  exact norm_kgEnergy_add_sq (kgAnnulusOp_inner R₁ R₂) hin hout

end AnnulusSplit

end GaloisForLFunctions.HTGeometry
