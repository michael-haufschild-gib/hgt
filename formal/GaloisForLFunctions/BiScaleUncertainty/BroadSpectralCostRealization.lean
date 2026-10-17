import GaloisForLFunctions.BiScaleUncertainty.FiniteSpectralEnvelopeRealization
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Removing the envelope cost from finite spectral realization

Compact smooth sources are globally Lipschitz. Their correlation increments have a global
linear bound; dilation and the finite first moment of the archimedean weight then produce
arbitrarily small normalized energy. Consequently every feasible finite spectral probability
has actual smooth compact polar grid sources approaching its spectral cost from above.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- The finite first moment used for a derivative-free dilation estimate on correlations. -/
def archWeightFirstMoment : ℝ := ∫ x in Ioi 0, x * archLevySinhWeight x

theorem mul_archLevySinhWeight_le {x : ℝ} (hx : 0 < x) :
    x * archLevySinhWeight x ≤ (2 * x + 1) * Real.exp (-(1 / 2 * x)) := by
  have hd := RHTower.one_sub_exp_neg_two_mul_ge hx
  have hp : 0 < 2 * x / (1 + 2 * x) := by positivity
  have he : Real.exp (-x / 2) = Real.exp (-(1 / 2 * x)) := by congr 1; ring
  rw [archLevySinhWeight, exp_half_div_sinh_eq hx, RHTower.archLevyDensity, he]
  have hb := div_le_div_of_nonneg_left (Real.exp_pos (-(1 / 2 * x))).le hp hd
  calc
    _ ≤ x * (2 * (Real.exp (-(1 / 2 * x)) / (2 * x / (1 + 2 * x)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb zero_le_two) hx.le
    _ = _ := by field_simp [hx.ne'] <;> ring

theorem integrableOn_mul_archLevySinhWeight :
    IntegrableOn (fun x => x * archLevySinhWeight x) (Ioi 0) := by
  have he : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2 * x))) (Ioi 0) := by
    simpa only [neg_mul] using (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0)
  have hi : IntegrableOn (fun x : ℝ => (2 * x + 1) * Real.exp (-(1 / 2 * x))) (Ioi 0) := by
    convert (RHTower.integrableOn_mul_exp_neg_half.const_mul 2).add he using 1
    ext x
    ring
  refine hi.mono' (by unfold archLevySinhWeight; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.le (archLevySinhWeight_pos hx).le)]
  exact mul_archLevySinhWeight_le hx

theorem archWeightFirstMoment_nonneg : 0 ≤ archWeightFirstMoment :=
  setIntegral_nonneg measurableSet_Ioi fun x hx =>
    mul_nonneg hx.le (archLevySinhWeight_pos hx).le

/-- Every compact `C²` source has a global linear correlation-increment bound. -/
theorem exists_autocorr_increment_linear_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, autocorr f 0 - autocorr f x ≤ M * |x| := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf (by norm_num)
  have hia : Integrable (fun u => |f u|) := (hf.continuous.integrable_of_hasCompactSupport hfc).abs
  refine ⟨(∫ u, |f u|) * (K : ℝ), mul_nonneg (integral_nonneg (fun _ => abs_nonneg _)) K.coe_nonneg, ?_⟩
  intro x
  have hi0 : Integrable (fun u => f u * f u) := by simpa using integrable_mul_shift hf.continuous hfc 0
  have hix := integrable_mul_shift hf.continuous hfc x
  have hi : Integrable (fun u => f u * (f u - f (u + x))) := by
    convert hi0.sub hix using 1
    ext u
    ring
  have hid : autocorr f 0 - autocorr f x = ∫ u, f u * (f u - f (u + x)) := by
    unfold autocorr
    simp only [add_zero]
    rw [← integral_sub hi0 hix]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  rw [hid]
  calc
    _ ≤ |∫ u, f u * (f u - f (u + x))| := le_abs_self _
    _ ≤ ∫ u, |f u * (f u - f (u + x))| := abs_integral_le_integral_abs
    _ ≤ ∫ u, |f u| * ((K : ℝ) * |x|) := by
      refine integral_mono hi.abs (hia.mul_const _) (fun u => ?_)
      rw [abs_mul]
      have hb := hK.dist_le_mul u (u + x)
      rw [Real.dist_eq, Real.dist_eq, show u - (u + x) = -x by ring, abs_neg] at hb
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

/-- Small positive scale produces a broad source. -/
def sourceRescale (f : ℝ → ℝ) (δ u : ℝ) : ℝ := f (δ * u)

theorem contDiff_sourceRescale {f : ℝ → ℝ} {r : WithTop ℕ∞} (hf : ContDiff ℝ r f) (δ : ℝ) :
    ContDiff ℝ r (sourceRescale f δ) := hf.comp (contDiff_const.mul contDiff_id)

theorem hasCompactSupport_sourceRescale {f : ℝ → ℝ} (hfc : HasCompactSupport f)
    {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (sourceRescale f δ) :=
  hfc.comp_homeomorph (Homeomorph.mulLeft₀ δ hδ.ne')

theorem autocorr_sourceRescale (f : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    autocorr (sourceRescale f δ) x = δ⁻¹ * autocorr f (δ * x) := by
  unfold autocorr sourceRescale
  simp_rw [mul_add]
  have h := Measure.integral_comp_mul_left (fun u => f u * f (u + δ * x)) δ
  simpa only [abs_of_pos (inv_pos.mpr hδ), smul_eq_mul] using h

/-- Broad real compact sources can have arbitrarily small normalized archimedean energy,
while retaining the seed's full differentiability order. -/
theorem exists_source_normalized_energy_lt {f : ℝ → ℝ} {r : WithTop ℕ∞}
    (hr : 2 ≤ r) (hf : ContDiff ℝ r f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ r g ∧ HasCompactSupport g ∧ 0 < autocorr g 0 ∧
      normalizedArchEnergy g < ε := by
  obtain ⟨M, hM, hbound⟩ := exists_autocorr_increment_linear_bound (hf.of_le hr) hfc
  let K := M * archWeightFirstMoment / autocorr f 0
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hM archWeightFirstMoment_nonneg) hR.le
  let δ := ε / (K + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hreg := contDiff_sourceRescale hf δ
  have hcomp := hasCompactSupport_sourceRescale hfc hδ
  have hmass : autocorr (sourceRescale f δ) 0 = δ⁻¹ * autocorr f 0 := by
    simpa only [mul_zero] using autocorr_sourceRescale f hδ 0
  have hpos : 0 < autocorr (sourceRescale f δ) 0 := by rw [hmass]; positivity
  refine ⟨sourceRescale f δ, hreg, hcomp, hpos, ?_⟩
  have hraw : biScaleLevyEnergy (sourceRescale f δ) ≤ M * archWeightFirstMoment := by
    unfold biScaleLevyEnergy archWeightFirstMoment
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_biScaleLevyIntegrand (hreg.of_le hr) hcomp)
      (integrableOn_mul_archLevySinhWeight.const_mul M) measurableSet_Ioi (fun x hx => ?_)
    rw [hmass, autocorr_sourceRescale f hδ]
    have hb := hbound (δ * x)
    rw [abs_of_pos (mul_pos hδ hx)] at hb
    have hmul := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hδ).le
    have heq : δ⁻¹ * (M * (δ * x)) = M * x := by field_simp [hδ.ne'] <;> ring
    rw [heq] at hmul
    have hi : δ⁻¹ * autocorr f 0 - δ⁻¹ * autocorr f (δ * x) ≤ M * x := by
      simpa only [mul_sub] using hmul
    calc
      _ ≤ (M * x) * archLevySinhWeight x := mul_le_mul_of_nonneg_right hi (archLevySinhWeight_pos hx).le
      _ = _ := by ring
  have hn : normalizedArchEnergy (sourceRescale f δ) ≤ δ * K := by
    unfold normalizedArchEnergy
    rw [hmass]
    calc
      _ ≤ (M * archWeightFirstMoment) / (δ⁻¹ * autocorr f 0) :=
        div_le_div_of_nonneg_right hraw (by positivity)
      _ = _ := by dsimp [K]; field_simp [hδ.ne', hR.ne'] <;> ring
  have heq : δ * (K + 1) = ε := by
    dsimp [δ]
    field_simp [ne_of_gt (show 0 < K + 1 by linarith)]
  have hlt := mul_lt_mul_of_pos_left (show K < K + 1 by linarith) hδ
  rw [heq] at hlt
  exact hn.trans_lt hlt

/-- A concrete nonzero smooth compact seed is available; no source-existence premise is needed. -/
theorem exists_smooth_compact_source_positive_mass :
    ∃ f : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧ 0 < autocorr f 0 := by
  let b : ContDiffBump (0 : ℝ) := default
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_self] using b.rIn_pos.le)
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_⟩
  unfold autocorr
  simp only [add_zero]
  exact (b.continuous.mul b.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
    b.hasCompactSupport.mul_right (fun x => mul_self_nonneg (b x)) (x := 0) (by rw [hb0]; norm_num)

/-- Every finite spectral probability satisfying the logarithmic cosine zeros is approached
from above by actual smooth compact polar scalar grid sources. No envelope-energy premise remains. -/
theorem exists_smooth_polar_grid_source_lt_spectral_cost (atoms : List (ℝ × ℝ))
    (hw : ∀ p ∈ atoms, 0 ≤ p.1) (hmass : spectralMixtureMass atoms = 1) (N : ℕ)
    (hgrid : ∀ n ∈ Finset.Icc 2 N, cosineMixture atoms (Real.log (n : ℝ)) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧ HasCompactSupport g ∧ 0 < autocorr g 0 ∧
      (∫ x in Ioi 0, autocorr g x * Real.cosh (x / 2)) = 0 ∧
      (∀ n ∈ Finset.Icc 2 N, autocorr g (Real.log (n : ℝ)) = 0) ∧
      normalizedArchEnergy g < spectralMixtureCost atoms + ε := by
  have hr : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hh : 0 < ε / 2 := by linarith
  obtain ⟨f, hf, hfc, hR⟩ := exists_smooth_compact_source_positive_mass
  obtain ⟨k, hk, hkc, hkR, hkE⟩ := exists_source_normalized_energy_lt hr hf hfc hR hh
  obtain ⟨g, hg, hgc, hgR, hpolar, hgridg, hE⟩ :=
    exists_polar_log_grid_source_of_spectral_mixture atoms hr hk hkc hkR hw hmass N hgrid hh
  exact ⟨g, hg, hgc, hgR, hpolar, hgridg, by linarith⟩

/-- Every valid smooth polar finite-grid lower bound lies below every feasible finite spectral
cost. This is the source-realization direction of the sharp spectral variational problem. -/
theorem polar_grid_lower_bound_le_spectral_cost (N : ℕ) (C : ℝ)
    (hC : ∀ f : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f → HasCompactSupport f →
      0 < autocorr f 0 → (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) = 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) → C ≤ normalizedArchEnergy f)
    (atoms : List (ℝ × ℝ)) (hw : ∀ p ∈ atoms, 0 ≤ p.1)
    (hmass : spectralMixtureMass atoms = 1)
    (hgrid : ∀ n ∈ Finset.Icc 2 N, cosineMixture atoms (Real.log (n : ℝ)) = 0) :
    C ≤ spectralMixtureCost atoms := by
  by_contra hbad
  have hgap : 0 < (C - spectralMixtureCost atoms) / 2 := by linarith
  obtain ⟨g, hg, hgc, hR, hp, hz, hE⟩ :=
    exists_smooth_polar_grid_source_lt_spectral_cost atoms hw hmass N hgrid hgap
  have := hC g hg hgc hR hp hz
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty
