import GaloisForLFunctions.RHTower.SelbergMaassTraceArea
import Mathlib.NumberTheory.Modular

/-!
# Strict physical mass of the actual modular trace

Original nonvanishing and modular reduction put positive trace density in the closed
fundamental domain. Its closure-of-interior theorem and actual continuity give a
positive interior point, hence positive compact-core area mass. Horizontal Fubini
and the integrable cusp tail prove cutoff independence of core-plus-tail mass.
Thus the total physical mass is strictly positive at every cutoff at least one.

For a source in the exceptional interval the complete quarter identity therefore
forces a strictly negative combined core and Bessel boundary form. No nonnegative
lower bound for that form, and no Selberg conclusion, is assumed or proved here.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassTraceMass
open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceStokes
  SelbergModularDomainSlices SelbergMaassTraceArea
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The actual finite trace is continuous on the upper half-plane. -/
theorem density_continuous : Continuous (density N f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := ((density_contDiffOn N f).continuousOn.continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).comp UpperHalfPlane.continuous_coe.continuousAt
  simpa only [Function.comp_def, ofComplex_apply] using h

/-- Modularity and original nonvanishing give positive density inside the open modular domain. -/
theorem density_pos_interior : ∃ z ∈ fdo, 0 < density N f z := by
  obtain ⟨z, hz⟩ := density_pos_somewhere N f
  obtain ⟨A, hA⟩ := exists_smul_mem_fd z
  have hpos : 0 < density N f (A • z) := by rwa [density_invariant]
  let U : Set ℍ := (density N f) ⁻¹' Ioi 0
  have hU : IsOpen U := isOpen_Ioi.preimage (density_continuous N f)
  have hcl : A • z ∈ closure fdo := fd_eq_closure_fdo ▸ hA
  obtain ⟨w, hw⟩ := mem_closure_iff.mp hcl U hU hpos
  exact ⟨w, hw.2, hw.1⟩

/-- Actual planar hyperbolic trace-mass density. -/
def massDensity (p : ℝ × ℝ) : ℝ :=
  density N f (ofComplex (point p.1 p.2)) / p.2 ^ (2 : ℕ)

/-- The actual trace-mass density is everywhere nonnegative. -/
theorem massDensity_nonneg (p : ℝ × ℝ) : 0 ≤ massDensity N f p :=
  div_nonneg (density_nonneg N f _) (sq_nonneg _)

/-- The actual hyperbolic trace density is continuous at every positive-height point. -/
theorem massDensity_continuousAt {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (massDensity N f) p := by
  have hz : 0 < (point p.1 p.2).im := by simpa [point] using hp
  have hc := ((density_contDiffOn N f).continuousOn.continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).comp (f := fun q : ℝ × ℝ => point q.1 q.2)
      (show Continuous (fun q : ℝ × ℝ => point q.1 q.2) by unfold point; fun_prop).continuousAt
  exact hc.div ((continuous_snd.pow 2).continuousAt) (pow_ne_zero 2 hp.ne')

/-- A positive interior source value gives strictly positive standard core area mass above it. -/
theorem coreMass_pos_of_interior {z : ℍ} (hz : z ∈ fdo) (hpos : 0 < density N f z)
    {Y : ℝ} (hY : z.im < Y) : 0 < coreMass N f Y := by
  let p : ℝ × ℝ := (z.re, z.im)
  have hre := abs_lt.mp hz.2
  have hsq : 1 < z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by simpa [Complex.normSq_apply, pow_two] using hz.1
  have hx : z.re ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨hre.1.le, hre.2.le⟩
  have ha : arcHeight z.re < z.im := by
    have h := arcHeight_sq hx
    have ha0 := (arcHeight_pos hx).le
    nlinarith [z.im_pos]
  have hh : (1 / 2 : ℝ) < z.im := (arcHeight_half_le hx).trans_lt ha
  have hpz : ofComplex (point p.1 p.2) = z := by
    have h : point p.1 p.2 = (z : ℂ) := by
      apply Complex.ext <;> simp [point, p]
    rw [h, ofComplex_apply]
  have hpD : 0 < massDensity N f p := by
    unfold massDensity
    rw [hpz]
    exact div_pos hpos (sq_pos_of_pos z.im_pos)
  have hs : Function.support (massDensity N f) ∩ domain Y ∈ 𝓝 p := by
    have hn := (massDensity_continuousAt N f (p := p) z.im_pos).eventually_ne hpD.ne'
    have hxN : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
      continuous_fst.continuousAt.preimage_mem_nhds (Ioo_mem_nhds hre.1 hre.2)
    have hyN : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.2 ∈ Ioo (1 / 2 : ℝ) Y :=
      continuous_snd.continuousAt.preimage_mem_nhds (Ioo_mem_nhds hh hY)
    have haN : ∀ᶠ q : ℝ × ℝ in 𝓝 p, arcHeight q.1 < q.2 :=
      (isOpen_lt (continuous_arcHeight.comp continuous_fst) continuous_snd).mem_nhds ha
    filter_upwards [hn, hxN, hyN, haN] with q hq hxq hyq haq
    exact ⟨hq, ⟨⟨⟨hxq.1.le, hxq.2.le⟩, ⟨hyq.1.le, hyq.2.le⟩⟩, haq.le⟩⟩
  exact (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (massDensity_nonneg N f)) (core_mass_integrable N f Y)).2
      (Measure.measure_pos_of_mem_nhds volume hs)

/-- Some compact modular core carries strictly positive actual trace mass. -/
theorem exists_coreMass_pos : ∃ Y : ℝ, 1 ≤ Y ∧ 0 < coreMass N f Y := by
  obtain ⟨z, hz, hp⟩ := density_pos_interior N f
  refine ⟨max 1 (z.im + 1), le_max_left _ _, coreMass_pos_of_interior N f hz hp ?_⟩
  exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

/-- Actual unit-period hyperbolic trace-mass slice. -/
def sliceMass (y : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, density N f (ofComplex (point x y))) / y ^ (2 : ℕ)

/-- Above height one the standard domain slice is the actual normalized unit-period mass. -/
theorem horizontal_mass_slice {Y y : ℝ} (hy : y ∈ Icc 1 Y) :
    horizontalSliceIntegral (massDensity N f) Y y = sliceMass N f y := by
  rw [horizontalSliceIntegral_eq_full (massDensity N f) hy]
  unfold massDensity sliceMass
  dsimp only
  rw [intervalIntegral.integral_div]
  have hp := (density_slice_periodic N f (by linarith [hy.1])).intervalIntegral_add_eq (-(1 / 2)) 0
  norm_num at hp
  rw [hp]

/-- The standard core mass splits into its fixed lower part and its actual finite strip mass. -/
theorem coreMass_decomposition {Y : ℝ} (hY : 1 ≤ Y) :
    coreMass N f Y =
      (∫ y in arcFloor..1, horizontalSliceIntegral (massDensity N f) 1 y) +
        ∫ y in (1 : ℝ)..Y, sliceMass N f y := by
  let F := massDensity N f
  have hi : IntegrableOn F (domain Y) := core_mass_integrable N f Y
  have hS := integrable_horizontalSliceIntegral hi
  change (∫ p in domain Y, F p) = _
  rw [setIntegral_eq_horizontal hi, integral_horizontalSliceIntegral_eq_interval F hY,
    ← intervalIntegral.integral_add_adjacent_intervals (b := (1 : ℝ)) hS.intervalIntegrable hS.intervalIntegrable]
  congr 1
  · apply intervalIntegral.integral_congr
    intro y hy
    have hf : arcFloor ≤ 1 := arcHeight_le_one ⟨by norm_num, le_rfl⟩
    have hyI : y ∈ Icc arcFloor 1 := by simpa [uIcc_of_le hf] using hy
    dsimp only [F, horizontalSliceIntegral]
    rw [horizontalSlice_eq_sideSlivers hY hyI, horizontalSlice_eq_sideSlivers le_rfl hyI]
  · apply intervalIntegral.integral_congr
    intro y hy
    exact horizontal_mass_slice N f (by simpa [uIcc_of_le hY] using hy)

/-- The actual unit-strip tail trace mass is nonnegative. -/
theorem tailMass_nonneg (Y : ℝ) : 0 ≤ tailMass N f Y := by
  apply integral_nonneg
  intro y
  exact div_nonneg (intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    (fun x _ => density_nonneg N f (ofComplex (point x y)))) (sq_nonneg y)

/-- Actual total core-plus-tail trace mass is independent of every cutoff at least one. -/
theorem totalMass_eq_one (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 1 ≤ Y) :
    coreMass N f Y + tailMass N f Y = coreMass N f 1 + tailMass N f 1 := by
  have h1 := coreMass_decomposition N f (Y := 1) le_rfl
  simp only [intervalIntegral.integral_same, add_zero] at h1
  rw [coreMass_decomposition N f hY, h1]
  have ht := intervalIntegral.integral_interval_add_Ioi
    (density_tail_mass_integrable N lam f (by norm_num : (0 : ℝ) < 1))
    (density_tail_mass_integrable N lam f (by linarith : 0 < Y))
  change (∫ y in (1 : ℝ)..Y, sliceMass N f y) + tailMass N f Y = tailMass N f 1 at ht
  linarith

/-- The actual total physical trace mass is strictly positive at every cutoff at least one. -/
theorem totalMass_pos (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 1 ≤ Y) : 0 < coreMass N f Y + tailMass N f Y := by
  obtain ⟨B, hB, hp⟩ := exists_coreMass_pos N f
  rw [totalMass_eq_one N lam f hY, ← totalMass_eq_one N lam f hB]
  exact add_pos_of_pos_of_nonneg hp (tailMass_nonneg N f B)

/-- Any actual exceptional source forces a strictly negative combined core and Bessel boundary form. -/
theorem core_boundary_strict_neg (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (T : ℝ) (hT : 0 ≤ T) : coreQuarter N f (Real.exp T) + boundarySum N f T < 0 := by
  exact lt_of_le_of_lt (core_boundary_upper_bound N lam f T hT)
    (mul_neg_of_neg_of_pos (sub_neg.mpr lam.2.2) (totalMass_pos N lam f (Real.one_le_exp hT)))

end
end GaloisForLFunctions.RHTower.SelbergMaassTraceMass
