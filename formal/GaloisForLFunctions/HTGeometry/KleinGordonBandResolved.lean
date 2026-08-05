import GaloisForLFunctions.HTGeometry.KleinGordonSpectrumFrozen

/-!
# The estimate, band by band

For a *moving* frequency-diagonal background the trapping law is no longer available — energy can be
pumped in — but the decoupling survives untouched: the bands still evolve independently and their
energies still add up. So the card's inequality can be applied to each band separately, with that
band's own initial energy on the right-hand side.

The decomposition is lossless: the initial energy splits orthogonally across the band as well, so the
band-resolved bounds add up to exactly the global bound. What the band-resolved form says that the
global one does not is that a band's growth is charged to its *own* initial energy — a band that starts
empty stays empty, however violently the background moves.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section DatumSplit

variable {Λ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}

/-- **A self-adjoint projection splits the norm of a datum orthogonally.** -/
theorem norm_sq_split_of_proj
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (Λ x) y : ℂ) = inner ℂ x (Λ y))
    (hidem : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (Λ x) = Λ x)
    (x : Lp ℂ 2 (volume : Measure E)) :
    ‖x‖ ^ 2 = ‖Λ x‖ ^ 2 + ‖x - Λ x‖ ^ 2 := by
  have hz : Λ (x - Λ x) = 0 := by
    rw [map_sub, hidem, sub_self]
  have h0 : (inner ℂ (Λ x) (x - Λ x) : ℂ) = 0 := inner_eq_zero_of_proj hsa (hidem x) hz
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Λ x) (x - Λ x) h0
  have hx : Λ x + (x - Λ x) = x := by abel
  rw [hx] at hp
  rw [pow_two, pow_two, pow_two]
  exact hp

/-- **The initial energy of a clock splits orthogonally across a band.** -/
theorem kgDatum_energy_split
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (Λ x) y : ℂ) = inner ℂ x (Λ y))
    (hidem : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (Λ x) = Λ x)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ‖g‖ ^ 2 + ‖h‖ ^ 2
      = (‖Λ g‖ ^ 2 + ‖Λ h‖ ^ 2) + (‖g - Λ g‖ ^ 2 + ‖h - Λ h‖ ^ 2) := by
  rw [norm_sq_split_of_proj hsa hidem g, norm_sq_split_of_proj hsa hidem h]
  ring

/-- The initial energy splits across any annulus of frequencies. -/
theorem kgDatum_energy_split_annulus (R₁ R₂ : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) :
    ‖g‖ ^ 2 + ‖h‖ ^ 2
      = (‖kgAnnulusOp R₁ R₂ g‖ ^ 2 + ‖kgAnnulusOp R₁ R₂ h‖ ^ 2)
        + (‖g - kgAnnulusOp R₁ R₂ g‖ ^ 2 + ‖h - kgAnnulusOp R₁ R₂ h‖ ^ 2) :=
  kgDatum_energy_split (kgAnnulusOp_inner R₁ R₂) (kgAnnulusOp_idem R₁ R₂) g h

end DatumSplit

section BandResolved

variable {b : ℝ} {w : ℝ → E → ℂ}

set_option maxHeartbeats 1000000 in
/-- **The energy inside an annulus obeys the card's inequality with its own initial energy**, even
when the background moves. -/
theorem kgFieldEnergyT_annulus_le (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (R₁ R₂ : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ 2
        + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ 2
      ≤ (‖kgAnnulusOp R₁ R₂ g‖ ^ 2 + ‖kgAnnulusOp R₁ R₂ h‖ ^ 2) * Real.exp (2 * (b * |t|)) :=
  kgFieldEnergyT_le hb0 (fun _ => norm_fourierMulCLM_le _ _ _) hWs
    (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t

set_option maxHeartbeats 1000000 in
/-- The same outside the annulus. -/
theorem kgFieldEnergyT_annulus_compl_le (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (R₁ R₂ : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ 2
        + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ 2
      ≤ (‖g - kgAnnulusOp R₁ R₂ g‖ ^ 2 + ‖h - kgAnnulusOp R₁ R₂ h‖ ^ 2)
          * Real.exp (2 * (b * |t|)) :=
  kgFieldEnergyT_le hb0 (fun _ => norm_fourierMulCLM_le _ _ _) hWs
    (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t

set_option maxHeartbeats 1000000 in
/-- **The card's inequality, band by band, for a moving frequency-diagonal background.** The energy
splits across the annulus at every time, the initial energy splits with it, and each part obeys the
estimate charged to its own initial energy: a band that starts empty stays empty. -/
theorem kgFieldEnergyT_band_resolved (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (R₁ R₂ : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t‖ ^ 2
            + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t‖ ^ 2
          = (‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
                  (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ 2
              + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
                  (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ 2)
            + (‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
                  (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ 2
              + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
                  (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ 2)
      ∧ ‖g‖ ^ 2 + ‖h‖ ^ 2
          = (‖kgAnnulusOp R₁ R₂ g‖ ^ 2 + ‖kgAnnulusOp R₁ R₂ h‖ ^ 2)
            + (‖g - kgAnnulusOp R₁ R₂ g‖ ^ 2 + ‖h - kgAnnulusOp R₁ R₂ h‖ ^ 2)
      ∧ ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ 2
            + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (kgAnnulusOp R₁ R₂ g) (kgAnnulusOp R₁ R₂ h) t‖ ^ 2
          ≤ (‖kgAnnulusOp R₁ R₂ g‖ ^ 2 + ‖kgAnnulusOp R₁ R₂ h‖ ^ 2)
              * Real.exp (2 * (b * |t|))
      ∧ ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ 2
            + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (g - kgAnnulusOp R₁ R₂ g) (h - kgAnnulusOp R₁ R₂ h) t‖ ^ 2
          ≤ (‖g - kgAnnulusOp R₁ R₂ g‖ ^ 2 + ‖h - kgAnnulusOp R₁ R₂ h‖ ^ 2)
              * Real.exp (2 * (b * |t|)) :=
  ⟨kgFieldEnergyT_annulus_split hw hb0 hwb hWs R₁ R₂ g h t,
    kgDatum_energy_split_annulus R₁ R₂ g h,
    kgFieldEnergyT_annulus_le hw hb0 hwb hWs R₁ R₂ g h t,
    kgFieldEnergyT_annulus_compl_le hw hb0 hwb hWs R₁ R₂ g h t⟩

end BandResolved

end GaloisForLFunctions.HTGeometry
