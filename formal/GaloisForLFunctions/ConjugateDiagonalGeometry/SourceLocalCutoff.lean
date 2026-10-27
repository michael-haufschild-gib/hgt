import GaloisForLFunctions.ConjugateDiagonalGeometry.StripSourceCutoff
import GaloisForLFunctions.RHTower.SelbergPlanarTestScaling

/-!
# Local planar tests inside the fixed-strip source

Translations and dilations of the same fixed bump retain the exact inverse-
square Laplacian law. Small discs around the zero strip lie where the
stretched cutoff is identically one, so localization adds no cutoff error.
-/

open Complex Set Metric Laplacian InnerProductSpace
open scoped Laplacian
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.RHTower

/-- The fixed source bump localized at a spectral center and radius. -/
def sourceLocalCutoff (c : ℂ) (r : ℝ) : ℂ → ℝ :=
  SelbergPlanarTestScaling.rescale (sourceCutoff 0) c r

lemma contDiff_sourceLocalCutoff (c : ℂ) (r : ℝ) :
    ContDiff ℝ 2 (sourceLocalCutoff c r) :=
  SelbergPlanarTestScaling.rescale_contDiff (sourceCutoff 0).contDiff c r

lemma hasCompactSupport_sourceLocalCutoff (c : ℂ) {r : ℝ} (hr : r ≠ 0) :
    HasCompactSupport (sourceLocalCutoff c r) :=
  SelbergPlanarTestScaling.rescale_compact (sourceCutoff 0).hasCompactSupport c hr

lemma sourceLocalCutoff_nonneg (c : ℂ) (r : ℝ) (z : ℂ) :
    0 ≤ sourceLocalCutoff c r z := (sourceCutoff 0).nonneg

lemma sourceLocalCutoff_le_one (c : ℂ) (r : ℝ) (z : ℂ) :
    sourceLocalCutoff c r z ≤ 1 := (sourceCutoff 0).le_one

/-- The inner closed disc is retained with full weight. -/
lemma sourceLocalCutoff_eq_one (c : ℂ) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : ‖z - c‖ ≤ r) : sourceLocalCutoff c r z = 1 := by
  apply (sourceCutoff 0).one_of_mem_closedBall
  simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr), sourceCutoff, Nat.cast_zero, zero_add]
  exact (mul_le_mul_of_nonneg_left hz (inv_pos.mpr hr).le).trans_eq
    (inv_mul_cancel₀ hr.ne')

/-- The full support remains inside twice the prescribed radius. -/
lemma sourceLocalCutoff_support (c : ℂ) {r : ℝ} (hr : 0 < r) :
    tsupport (sourceLocalCutoff c r) ⊆ closedBall c (2 * r) := by
  intro z hz
  have h := tsupport_comp_subset_preimage (sourceCutoff 0 : ℂ → ℝ)
    ((continuous_id.sub continuous_const).const_smul r⁻¹) hz
  change r⁻¹ • (z - c) ∈ tsupport (sourceCutoff 0 : ℂ → ℝ) at h
  rw [(sourceCutoff 0).tsupport_eq] at h
  have hb : r⁻¹ * ‖z - c‖ ≤ 2 := by
    simpa only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), sourceCutoff, Nat.cast_zero, zero_add] using h
  have hh := mul_le_mul_of_nonneg_left hb hr.le
  rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hh
  simpa only [mem_closedBall, dist_eq_norm, mul_comm r] using hh

/-- The local bump has the exact inverse-square planar Laplacian scaling. -/
lemma sourceLocalCutoff_laplacian (c : ℂ) (r : ℝ) (z : ℂ) :
    Δ (sourceLocalCutoff c r) z = r⁻¹ ^ 2 *
      Δ (sourceCutoff 0 : ℂ → ℝ) (r⁻¹ • (z - c)) := by
  rw [Bottcher.laplacian_eq_dderiv _ (contDiff_sourceLocalCutoff c r),
    Bottcher.laplacian_eq_dderiv _ (sourceCutoff 0).contDiff]
  exact SelbergPlanarTestScaling.rescale_laplacian (sourceCutoff 0).contDiff c r z

/-- The same fixed derivative control pays every translated and scaled bump. -/
lemma abs_sourceLocalCutoff_laplacian_le (c : ℂ) (r : ℝ) (z : ℂ) :
    |Δ (sourceLocalCutoff c r) z| ≤ stripSourceCutoffControl / r ^ 2 := by
  have hb (w : ℂ) : |Δ (sourceCutoff 0 : ℂ → ℝ) w| ≤ stripSourceCutoffControl := by
    rw [Bottcher.laplacian_eq_dderiv _ (sourceCutoff 0).contDiff]
    refine ((abs_add_le _ _).trans
      (add_le_add (abs_stripBumpSecond_le 1 w) (abs_stripBumpSecond_le Complex.I w))).trans ?_
    unfold stripSourceCutoffControl
    linarith only [norm_nonneg (sourceCutoffDerivative 0 1),
      norm_nonneg (sourceCutoffDerivative 0 Complex.I)]
  rw [sourceLocalCutoff_laplacian, abs_mul, abs_of_nonneg (sq_nonneg _)]
  refine (mul_le_mul_of_nonneg_left (hb _) (sq_nonneg _)).trans_eq ?_
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- A small disc centered in the zero strip is fully retained by the source exhaustion. -/
lemma stripSourceCutoff_eq_one_on_local_support (n : ℕ) (c : ℂ)
    (hc : 0 ≤ c.re ∧ c.re ≤ 1) (hcy : |c.im| ≤ (n : ℝ) / 2)
    {r : ℝ} (hr : 0 < r) (hrmax : r ≤ 1 / 8)
    {z : ℂ} (hz : z ∈ tsupport (sourceLocalCutoff c r)) :
    stripSourceCutoff n z = 1 := by
  have hdist : ‖z - c‖ ≤ 2 * r := by
    simpa only [mem_closedBall, dist_eq_norm] using sourceLocalCutoff_support c hr hz
  have hRe := (Complex.abs_re_le_norm (z - c)).trans hdist
  have hIm := (Complex.abs_im_le_norm (z - c)).trans hdist
  rw [Complex.sub_re] at hRe
  rw [Complex.sub_im] at hIm
  have hδc : |c.re - 1 / 2| ≤ (1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith only [hc.1], by linarith only [hc.2]⟩
  have hδ : |z.re - 1 / 2| ≤ (3 / 4 : ℝ) := by
    have h := abs_add_le (z.re - c.re) (c.re - 1 / 2)
    rw [show z.re - c.re + (c.re - 1 / 2) = z.re - 1 / 2 by ring] at h
    linarith only [h, hRe, hδc, hrmax]
  have hy : |z.im| ≤ (n : ℝ) + 1 := by
    have h := abs_add_le (z.im - c.im) c.im
    rw [sub_add_cancel] at h
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith only [h, hIm, hcy, hrmax, hn]
  have hyscale : |z.im| / (4 * ((n : ℝ) + 1)) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    linarith only [hy]
  have hnorm : ‖stripSourcePoint n z‖ ≤
      |(stripSourcePoint n z).re| + |(stripSourcePoint n z).im| := by
    calc
      ‖stripSourcePoint n z‖ = ‖((stripSourcePoint n z).re : ℂ) +
          ((stripSourcePoint n z).im : ℂ) * Complex.I‖ :=
        congrArg norm (Complex.re_add_im (stripSourcePoint n z)).symm
      _ ≤ ‖((stripSourcePoint n z).re : ℂ)‖ +
          ‖((stripSourcePoint n z).im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = _ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  rw [stripSourcePoint_re, stripSourcePoint_im, abs_div,
    abs_of_pos (by positivity : 0 < 4 * ((n : ℝ) + 1))] at hnorm
  apply (sourceCutoff 0).one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right]
  simp only [sourceCutoff, Nat.cast_zero, zero_add]
  linarith only [hnorm, hδ, hyscale]

/-- The global cutoff leaves every admissible local test exactly unchanged. -/
lemma stripSourceCutoff_mul_local_eq (n : ℕ) (c : ℂ)
    (hc : 0 ≤ c.re ∧ c.re ≤ 1) (hcy : |c.im| ≤ (n : ℝ) / 2)
    {r : ℝ} (hr : 0 < r) (hrmax : r ≤ 1 / 8) :
    (fun z => stripSourceCutoff n z * sourceLocalCutoff c r z) = sourceLocalCutoff c r := by
  funext z
  by_cases hz : sourceLocalCutoff c r z = 0
  · rw [hz, mul_zero]
  · rw [stripSourceCutoff_eq_one_on_local_support n c hc hcy hr hrmax
      (subset_tsupport _ hz), one_mul]

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.abs_sourceLocalCutoff_laplacian_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.stripSourceCutoff_mul_local_eq
