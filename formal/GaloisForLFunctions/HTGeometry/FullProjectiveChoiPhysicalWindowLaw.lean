import GaloisForLFunctions.HTGeometry.FullProjectiveChoiAffineTensorWindowLaw

open Real intervalIntegral MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- Physical frequency packet obtained by restoring the positive clock gap. -/
def clockScaledFullProjectiveFrequency (g : ℝ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun j => g * fullProjectiveFrequency y j

theorem zeroAnchoredMetricBallFamilyAngularVisit_clockScaled
    (g : ℝ) (y : Fin n → ℝ) (m : ℕ) (delta : ℝ)
    (target : Fin m → EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2))) :
    zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m delta target
        (clockScaledFullProjectiveFrequency g y) =
      (fun t : ℝ => g * t) ⁻¹'
        zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m delta target
          (fullProjectiveFrequency y) := by
  ext t
  simp only [zeroAnchoredMetricBallFamilyAngularVisit, Set.mem_setOf_eq,
    Set.mem_preimage, clockScaledFullProjectiveFrequency]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    convert ha using 1 <;> funext j <;> ring
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    convert ha using 1 <;> funext j <;> ring

theorem preimage_mul_inter_Ioc (g : ℝ) (hg : 0 < g) (S : Set ℝ) (u T : ℝ) :
    (fun t : ℝ => g * t) ⁻¹' (S ∩ Set.Ioc (g * u) (g * (u + T))) =
      (fun t : ℝ => g * t) ⁻¹' S ∩ Set.Ioc u (u + T) := by
  ext t
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc]
  constructor
  · rintro ⟨htS, hlow, hupp⟩
    exact ⟨htS, by constructor <;> nlinarith⟩
  · rintro ⟨htS, hlow, hupp⟩
    exact ⟨htS, by constructor <;> nlinarith⟩

theorem volumeReal_clockScaledVisit_inter_Ioc
    {g : ℝ} (hg : 0 < g) (y : Fin n → ℝ) (m : ℕ) (delta : ℝ)
    (target : Fin m → EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2)))
    (u T : ℝ) :
    volume.real
        (zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m delta target
            (clockScaledFullProjectiveFrequency g y) ∩ Set.Ioc u (u + T)) =
      g⁻¹ * volume.real
        (zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m delta target
            (fullProjectiveFrequency y) ∩ Set.Ioc (g * u) (g * (u + T))) := by
  have hg0 : g ≠ 0 := ne_of_gt hg
  rw [zeroAnchoredMetricBallFamilyAngularVisit_clockScaled]
  rw [← preimage_mul_inter_Ioc g hg]
  rw [Measure.real, Real.volume_preimage_mul_left hg0, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg g⁻¹), abs_of_pos (inv_pos.mpr hg)]
  rfl

/-- Full-projective tensor occupation law in laboratory time.  Restoring a
positive spectral clock gap leaves Haar occupation unchanged and suppresses
the finite-window Fourier cost by the dimensionless duration `g * T`. -/
theorem exists_fullProjectiveMetricBallFamily_centerFreeTensorPhysicalWindowUpper
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {g eps delta : ℝ} (hg : 0 < g) (heps : 0 < eps) (hdelta : 0 < delta)
    (N m : ℕ)
    (hsmall : 2 * zeroAnchoredChoiAngularRadius (n + 1) delta ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (target : Fin m →
          EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2)))
        (u T : ℝ), 0 < T →
        volume.real
          (zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m delta target
              (clockScaledFullProjectiveFrequency g y) ∩ Set.Ioc u (u + T)) ≤
          (2 : ℝ) ^ (n + 1) * T *
            (((m : ℕ) : ℝ) *
                (2 * zeroAnchoredChoiAngularRadius (n + 1) delta / (2 * π) +
                  periodicTentFejerError N
                    (2 * zeroAnchoredChoiAngularRadius (n + 1) delta)) ^ (n + 1) +
              (2 * C / (g * T)) * ((m : ℝ) *
                periodicFejerMajorantAffineCostUpperBound N n
                  (2 * zeroAnchoredChoiAngularRadius (n + 1) delta)
                  (periodicTentFejerError N
                    (2 * zeroAnchoredChoiAngularRadius (n + 1) delta)) eps)) := by
  obtain ⟨C, hC, hnormalized⟩ :=
    exists_fullProjectiveMetricBallFamily_centerFreeTensorWindowUpper
      hy heps hdelta N m hsmall
  refine ⟨C, hC, ?_⟩
  intro target u T hT
  let A : ℝ := ((m : ℕ) : ℝ) *
    (2 * zeroAnchoredChoiAngularRadius (n + 1) delta / (2 * π) +
      periodicTentFejerError N
        (2 * zeroAnchoredChoiAngularRadius (n + 1) delta)) ^ (n + 1)
  let B : ℝ := ((m : ℝ) *
    periodicFejerMajorantAffineCostUpperBound N n
      (2 * zeroAnchoredChoiAngularRadius (n + 1) delta)
      (periodicTentFejerError N
        (2 * zeroAnchoredChoiAngularRadius (n + 1) delta)) eps)
  have hgT : 0 < g * T := mul_pos hg hT
  have hnorm := hnormalized target (g * u) (g * T) hgT
  have hnorm' :
      volume.real
        (zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m delta target
            (fullProjectiveFrequency y) ∩ Set.Ioc (g * u) (g * (u + T))) ≤
        (2 : ℝ) ^ (n + 1) * (g * T) *
          (A + (2 * C / (g * T)) * B) := by
    simpa only [Measure.real, mul_add, A, B] using hnorm
  rw [volumeReal_clockScaledVisit_inter_Ioc hg y m delta target u T]
  calc
    g⁻¹ * volume.real
        (zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m delta target
            (fullProjectiveFrequency y) ∩ Set.Ioc (g * u) (g * (u + T))) ≤
      g⁻¹ * ((2 : ℝ) ^ (n + 1) * (g * T) *
        (A + (2 * C / (g * T)) * B)) :=
          mul_le_mul_of_nonneg_left hnorm' (inv_nonneg.mpr hg.le)
    _ = (2 : ℝ) ^ (n + 1) * T *
        (A + (2 * C / (g * T)) * B) := by
          field_simp [ne_of_gt hg]
    _ = _ := by rfl

end

end GaloisForLFunctions.HTGeometry
