import GaloisForLFunctions.RHTower.ZetaChiDualPiecewisePoisson
import GaloisForLFunctions.RHTower.ZetaChiDualWeightedInteriorMean
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff
noncomputable section
namespace RHTower


/-- The literal cutoff has the two spatial derivatives needed by finite-interval Poisson. -/
theorem contDiffOn_smoothAFECutoff_pos :
    ContDiffOn ℝ 2 smoothAFECutoff (Ioi (0 : ℝ)) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun x hx => (hasDerivAt_smoothAFECutoff hx).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  have hlog : ContDiffOn ℝ 1 Real.log (Ioi (0 : ℝ)) :=
    contDiffOn_id.log (fun _ hx => ne_of_gt hx)
  have hslope : ContDiffOn ℝ 1 (fun x : ℝ =>
      ((-(Real.exp (-(Real.log x) ^ 2 / 4) / (2 * Real.sqrt Real.pi * x)) : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
    have hnum : ContDiffOn ℝ 1 (fun x : ℝ => Real.exp (-(Real.log x) ^ 2 / 4))
        (Ioi (0 : ℝ)) := by fun_prop
    have hden : ContDiffOn ℝ 1 (fun x : ℝ => 2 * Real.sqrt Real.pi * x)
        (Ioi (0 : ℝ)) := by fun_prop
    have hnz : ∀ x ∈ Ioi (0 : ℝ), 2 * Real.sqrt Real.pi * x ≠ 0 := by
      intro x hx
      exact ne_of_gt (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)) hx)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((hnum.div hden hnz).neg)
  apply hslope.congr
  intro x hx
  exact (hasDerivAt_smoothAFECutoff hx).deriv

/-- The exact Gaussian/power/oscillation amplitude before its constant chi factor. -/
def zetaChiDualSpatialAmplitude (s : ℂ) (N t x : ℝ) : ℂ :=
  smoothAFECutoff (x / N) * (x : ℂ) ^ (s - 1) * bourgainOscillation (t * Real.log x)

theorem zetaChiDualSpatialAmplitude_nat (s : ℂ) (N t : ℝ) (n : ℕ) :
    zetaChi (s + (t : ℂ) * I) * zetaChiDualSpatialAmplitude s N t n =
      smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t := by
  unfold zetaChiDualSpatialAmplitude zetaChiDualInteriorAtom
  push_cast
  ring

/-- Spatial C² regularity is proved for the actual amplitude, with no derivative premise. -/
theorem contDiffOn_zetaChiDualSpatialAmplitude (s : ℂ) {N : ℝ} (hN : 0 < N) (t : ℝ) :
    ContDiffOn ℝ 2 (zetaChiDualSpatialAmplitude s N t) (Ioi (0 : ℝ)) := by
  have hcut : ContDiffOn ℝ 2 (fun x : ℝ => smoothAFECutoff (x / N)) (Ioi (0 : ℝ)) :=
    contDiffOn_smoothAFECutoff_pos.comp (by fun_prop) (fun _ hx => div_pos hx hN)
  have hlog : ContDiffOn ℝ 2 Real.log (Ioi (0 : ℝ)) :=
    contDiffOn_id.log (fun _ hx => ne_of_gt hx)
  have hcast : ContDiff ℝ 2 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hp : ContDiffOn ℝ 2 (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
    have he : ContDiffOn ℝ 2 (fun x : ℝ => Complex.exp ((Real.log x : ℂ) * (s - 1)))
        (Ioi (0 : ℝ)) := by fun_prop
    apply he.congr
    intro x hx
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hx)), ← Complex.ofReal_log hx.le]
  have hb : ContDiffOn ℝ 2 (fun x : ℝ => bourgainOscillation (t * Real.log x))
      (Ioi (0 : ℝ)) := by
    unfold bourgainOscillation
    fun_prop
  exact (hcut.mul hp).mul hb

/-- Finite-interval Poisson for the literal dual amplitude, retaining all
Fourier modes and every lattice endpoint condition. No tail estimate is assumed. -/
theorem tendsto_zetaChiDualSpatialAmplitude_cosTransform (s : ℂ) {N : ℝ} (hN : 0 < N)
    (t : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hna : ∀ k : ℤ, a ≠ (k : ℝ)) (hnb : ∀ k : ℤ, b ≠ (k : ℝ)) :
    Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K,
        (2 : ℂ) * ∫ x in a..b, zetaChiDualSpatialAmplitude s N t x *
          ((Real.cos (2 * Real.pi * x * ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop
      (𝓝 ((∑ m ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, zetaChiDualSpatialAmplitude s N t m) -
        ∫ x in a..b, zetaChiDualSpatialAmplitude s N t x)) := by
  have hc := contDiffOn_zetaChiDualSpatialAmplitude s hN t
  have hc' : ContDiffOn ℝ 1 (deriv (zetaChiDualSpatialAmplitude s N t)) (Ioi (0 : ℝ)) :=
    hc.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc'' : ContDiffOn ℝ 0 (deriv (deriv (zetaChiDualSpatialAmplitude s N t))) (Ioi (0 : ℝ)) :=
    hc'.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun _ hx => ha.trans_le hx.1
  have hd1 (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (zetaChiDualSpatialAmplitude s N t) (deriv (zetaChiDualSpatialAmplitude s N t) x) x :=
    (hc.differentiableOn (by norm_num)).hasDerivAt (Ioi_mem_nhds (hsub hx))
  have hd2 (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (deriv (zetaChiDualSpatialAmplitude s N t))
        (deriv (deriv (zetaChiDualSpatialAmplitude s N t)) x) x :=
    (hc'.differentiableOn (by norm_num)).hasDerivAt (Ioi_mem_nhds (hsub hx))
  simpa only [div_one, Complex.ofReal_ofNat, Complex.ofReal_one, one_mul, mul_one] using
    tendsto_complex_piecewise_cosTransform hab (by norm_num : (0 : ℝ) < 1)
      (by simpa only [div_one] using hna) (by simpa only [div_one] using hnb)
      hd1 hd2 (hc''.continuousOn.mono hsub)

end RHTower
