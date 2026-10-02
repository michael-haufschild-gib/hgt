import GaloisForLFunctions.RHTower.ZetaChiDualSpatialAmplitude

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower


/-- The actual slow spatial amplitude at unit height. -/
def chiDualUnitSpatialAmplitude (s : ℂ) (x : ℝ) : ℂ :=
  smoothAFECutoff x * (x : ℂ) ^ (s - 1)

/-- Exact first spatial derivative of the unit-height amplitude. -/
def chiDualUnitSpatialFirst (s : ℂ) (x : ℝ) : ℂ :=
  deriv smoothAFECutoff x * (x : ℂ) ^ (s - 1) +
    smoothAFECutoff x * (s - 1) * (x : ℂ) ^ (s - 2)

/-- Exact second spatial derivative; the literal cutoff derivatives remain explicit. -/
def chiDualUnitSpatialSecond (s : ℂ) (x : ℝ) : ℂ :=
  deriv (deriv smoothAFECutoff) x * (x : ℂ) ^ (s - 1) +
    2 * deriv smoothAFECutoff x * (s - 1) * (x : ℂ) ^ (s - 2) +
      smoothAFECutoff x * (s - 1) * (s - 2) * (x : ℂ) ^ (s - 3)

private theorem hasDerivAt_positive_real_cpow (z : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ z) (z * (x : ℂ) ^ (z - 1)) x := by
  simpa only [neg_neg] using
    (hasDerivAt_ofReal_cpow_neg_highBlockCutoffMonotone (w := -z) hx)

theorem hasDerivAt_chiDualUnitSpatialAmplitude (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (chiDualUnitSpatialAmplitude s) (chiDualUnitSpatialFirst s x) x := by
  have hV : HasDerivAt smoothAFECutoff (deriv smoothAFECutoff x) x :=
    (contDiffOn_smoothAFECutoff_pos.differentiableOn (by norm_num)).hasDerivAt (Ioi_mem_nhds hx)
  have hp := hasDerivAt_positive_real_cpow (s - 1) hx
  rw [show (s - 1) - 1 = s - 2 by ring] at hp
  refine (hV.mul hp).congr_deriv ?_
  unfold chiDualUnitSpatialFirst
  ring

theorem hasDerivAt_chiDualUnitSpatialFirst (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (chiDualUnitSpatialFirst s) (chiDualUnitSpatialSecond s x) x := by
  have hc1 : ContDiffOn ℝ 1 (deriv smoothAFECutoff) (Ioi (0 : ℝ)) :=
    contDiffOn_smoothAFECutoff_pos.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hV : HasDerivAt smoothAFECutoff (deriv smoothAFECutoff x) x :=
    (contDiffOn_smoothAFECutoff_pos.differentiableOn (by norm_num)).hasDerivAt (Ioi_mem_nhds hx)
  have hV' : HasDerivAt (deriv smoothAFECutoff) (deriv (deriv smoothAFECutoff) x) x :=
    (hc1.differentiableOn (by norm_num)).hasDerivAt (Ioi_mem_nhds hx)
  have hp := hasDerivAt_positive_real_cpow (s - 1) hx
  have hp' := hasDerivAt_positive_real_cpow (s - 2) hx
  rw [show (s - 1) - 1 = s - 2 by ring] at hp
  rw [show (s - 2) - 1 = s - 3 by ring] at hp'
  refine ((hV'.mul hp).add ((hV.mul_const (s - 1)).mul hp')).congr_deriv ?_
  unfold chiDualUnitSpatialSecond
  ring

end RHTower
