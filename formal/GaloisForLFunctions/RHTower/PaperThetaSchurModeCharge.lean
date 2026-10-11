import GaloisForLFunctions.RHTower.HedenmalmThetaSchurQuarticSpectralDecayEquivalence

/-!
# The native theta quartic charge, retaining every stage and every mode

The fixed Hilbert--Schmidt ceiling converts a positive total charge into a uniformly
positive charge on at least one mode, independently of stage dimension and Schur choice.
This is the bridge needed to apply the proven paper ideal cost to the full mode operator.
-/

namespace RHTower.HedenmalmThetaSource
noncomputable section
open GaloisForLFunctions.HTGeometry Filter
open scoped BigOperators Topology NNReal

abbrev PaperThetaSchurFamily := ∀ k : ℕ, ThetaSourceStageSchurPacket k

abbrev PaperThetaSchurMode :=
  Σ k : ℕ, Fin (Fintype.card ↥(thetaSourceSignedCutoff k))

/-- The literal quartic charge of one eigenmode of an actual theta stage. -/
def paperThetaSchurModeCharge (S : PaperThetaSchurFamily) (p : PaperThetaSchurMode) : ℝ :=
  sourcePairPositiveQuarticCharge ((S p.1).T p.2 p.2).re ((S p.1).T p.2 p.2).im

theorem paperThetaSchurModeCharge_nonneg (S : PaperThetaSchurFamily)
    (p : PaperThetaSchurMode) : 0 ≤ paperThetaSchurModeCharge S p :=
  sourcePairPositiveQuarticCharge_nonneg _ _

theorem sum_paperThetaSchurModeCharge (S : PaperThetaSchurFamily) (k : ℕ) :
    ∑ i, paperThetaSchurModeCharge S ⟨k, i⟩ =
      thetaSourceStageSchurPositiveQuarticCharge (S k) := rfl

theorem paperThetaSchurModeCharge_le_total (S : PaperThetaSchurFamily)
    (p : PaperThetaSchurMode) :
    paperThetaSchurModeCharge S p ≤ thetaSourceStageSchurPositiveQuarticCharge (S p.1) :=
  Finset.single_le_sum (fun i _ => paperThetaSchurModeCharge_nonneg S ⟨p.1, i⟩)
    (Finset.mem_univ p.2)

/-- A source-dependent bound, independent of stage size and Schur realization. -/
def paperThetaSchurChargeBound : ℝ := 2300 * thetaSourceSignedHSCeiling ^ 4

theorem paperThetaSchurChargeBound_pos : 0 < paperThetaSchurChargeBound := by
  have hC := thetaSourceSignedHSCeiling_pos
  unfold paperThetaSchurChargeBound
  positivity

theorem paperThetaSchurModeCharge_le_bound (S : PaperThetaSchurFamily)
    (p : PaperThetaSchurMode) : paperThetaSchurModeCharge S p ≤ paperThetaSchurChargeBound := by
  have hC := thetaSourceSignedHSCeiling_pos
  calc
    paperThetaSchurModeCharge S p ≤
        2300 * (‖(S p.1).T p.2 p.2‖ ^ 2) ^ 2 := by
      simpa only [paperThetaSchurModeCharge, Complex.normSq_eq_norm_sq] using
        sourcePairPositiveQuarticCharge_le_normSq_sq ((S p.1).T p.2 p.2)
    _ ≤ 2300 * (thetaSourceSignedHSCeiling ^ 2) ^ 2 := by
      gcongr
      exact norm_thetaSourceStageSchurDiagonal_le_ceiling (S p.1) p.2
    _ = paperThetaSchurChargeBound := by unfold paperThetaSchurChargeBound; ring

/-- The quartic reporter controls the squared imaginary part of every mode. -/
theorem paperThetaSchur_im_sq_le_of_charge_le (a b : ℝ) (η : ℝ≥0)
    (h : sourcePairPositiveQuarticCharge a b ≤ 2300 * (η : ℝ) ^ 2) :
    b ^ 2 ≤ (η : ℝ) := by
  have hlower : 2300 * (b ^ 2) ^ 2 ≤ sourcePairPositiveQuarticCharge a b := by
    unfold sourcePairPositiveQuarticCharge
    nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  nlinarith [η.coe_nonneg, sq_nonneg b]

/-- Bounded local quartic charge controls total charge without a dimension factor. -/
theorem paperThetaSchur_total_le_of_mode_le {k : ℕ} (S : ThetaSourceStageSchurPacket k)
    (η : ℝ≥0)
    (h : ∀ i, sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
      2300 * (η : ℝ) ^ 2) :
    thetaSourceStageSchurPositiveQuarticCharge S ≤
      2300 * (η : ℝ) * thetaSourceSignedHSCeiling ^ 2 := by
  have hs := finiteMatrixSchurPositiveQuarticCharge_le_of_large_im_sq_le
    0 η le_rfl η.coe_nonneg S.toFiniteMatrixSchurPacket
    (fun i _ => paperThetaSchur_im_sq_le_of_charge_le _ _ η (h i))
  change thetaSourceStageSchurPositiveQuarticCharge S ≤
    2300 * (0 + (η : ℝ)) * matHSNormSq (thetaSourceSignedStageFinMatrix k) at hs
  simp only [zero_add] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    (matHSNormSq_thetaSourceSignedStageFinMatrix_le_ceiling k) (by positivity))

/-- A positive total charge forces a source-uniform positive mode threshold. -/
def paperThetaSchurModeThreshold (c : ℝ≥0) : ℝ :=
  2300 * ((c : ℝ) / (2300 * thetaSourceSignedHSCeiling ^ 2)) ^ 2

theorem paperThetaSchurModeThreshold_pos (c : ℝ≥0) (hc : c ≠ 0) :
    0 < paperThetaSchurModeThreshold c := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (pos_iff_ne_zero.mpr hc)
  have hC := thetaSourceSignedHSCeiling_pos
  unfold paperThetaSchurModeThreshold
  positivity

theorem exists_mode_paperThetaSchurModeThreshold_lt {k : ℕ}
    (S : ThetaSourceStageSchurPacket k) (c : ℝ≥0)
    (hc : (c : ℝ) < thetaSourceStageSchurPositiveQuarticCharge S) :
    ∃ i, paperThetaSchurModeThreshold c <
      sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im := by
  have hC := thetaSourceSignedHSCeiling_pos
  have hD : 0 < 2300 * thetaSourceSignedHSCeiling ^ 2 := by positivity
  let η : ℝ≥0 := ⟨(c : ℝ) / (2300 * thetaSourceSignedHSCeiling ^ 2),
    div_nonneg c.coe_nonneg hD.le⟩
  by_contra hn
  push Not at hn
  have hs := paperThetaSchur_total_le_of_mode_le S η hn
  have he : 2300 * (η : ℝ) * thetaSourceSignedHSCeiling ^ 2 = (c : ℝ) := by
    change 2300 * ((c : ℝ) / (2300 * thetaSourceSignedHSCeiling ^ 2)) *
      thetaSourceSignedHSCeiling ^ 2 = (c : ℝ)
    field_simp [ne_of_gt hC]
  rw [he] at hs
  exact (not_lt_of_ge hs) hc

/-- One choice of actual Schur packets exists without any arithmetic hypothesis. -/
def paperThetaCanonicalSchurFamily : PaperThetaSchurFamily :=
  fun k => Classical.choice (nonempty_thetaSourceStageSchurPacket k)

end
end RHTower.HedenmalmThetaSource
