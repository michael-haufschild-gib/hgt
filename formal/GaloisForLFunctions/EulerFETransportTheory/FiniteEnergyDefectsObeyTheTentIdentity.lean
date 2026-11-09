import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsConvergeToTheirBoundary
import GaloisForLFunctions.ExactEventTheory.TentPairingsOfIntegrableDefects
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The arithmetic tent identity for finite-energy defects

Strong Hardy convergence supplies the boundary term in the actual theta/tent identity.
The source needs only finite energy; no pointwise boundary values are assumed.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.HamburgerStability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ExactEventTheory
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

theorem defectLaplace_congr_ae {g f : ℝ → ℂ} (hgf : g =ᵐ[volume] f) (z : ℂ) :
    defectLaplace g z = defectLaplace f z := by
  unfold defectLaplace
  congr 1
  apply integral_congr_ae
  filter_upwards [hgf] with t ht
  rw [ht]

/-- The height-space tent corresponding to the scaled arithmetic pairing. -/
def defectTentTest (h n y : ℝ) : ℂ := (unitTent n (y / h) : ℂ)

theorem continuous_defectTentTest (h n : ℝ) : Continuous (defectTentTest h n) :=
  Complex.continuous_ofReal.comp ((continuous_unitTent n).comp (by fun_prop))

theorem support_defectTentTest {h : ℝ} (hh : 0 < h) (n : ℝ) :
    Function.support (defectTentTest h n) ⊆ Icc (h * (n - 1)) (h * (n + 1)) := by
  intro y hy
  have hab : |y / h - n| < 1 := by
    apply lt_of_not_ge
    intro ha
    exact hy (by simp only [defectTentTest, unitTent_eq_zero ha, Complex.ofReal_zero])
  constructor
  · have hl : (n - 1) * h < y := (lt_div_iff₀ hh).mp (by
      linarith only [(abs_lt.mp hab).1])
    simpa only [mul_comm] using hl.le
  · have hu : y < (n + 1) * h := (div_lt_iff₀ hh).mp (by
      linarith only [(abs_lt.mp hab).2])
    simpa only [mul_comm] using hu.le

theorem memLp_defectTentTest {h : ℝ} (hh : 0 < h) (n : ℝ) :
    MemLp (defectTentTest h n) 2 (volume : Measure ℝ) :=
  (continuous_defectTentTest h n).memLp_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_defectTentTest hh n))

/-- The canonical boundary paired with a physical tent. -/
def finiteEnergyTentError (g : DefectL2) (h n : ℝ) : ℝ :=
  (∫ y : ℝ, defectTentTest h n y * defectBoundaryL2 g y).re

private theorem memLp_defectLaplace_vertical {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) {σ : ℝ} (hσ : 0 < σ) :
    MemLp (fun y => defectLaplace g (hardyVerticalLine σ y)) 2 (volume : Measure ℝ) := by
  have h := (Lp.memLp (defectVerticalL2 (hg.toLp g) σ)).ae_eq
    (defectVerticalL2_ae (hg.toLp g) hσ)
  exact h.ae_eq (Eventually.of_forall fun y => defectLaplace_congr_ae hg.coeFn_toLp _)

private theorem tendsto_tent_integral_defectLaplace {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) {h : ℝ} (hh : 0 < h) (n : ℝ) :
    Tendsto (fun σ : ℝ => ∫ y : ℝ, defectTentTest h n y *
      defectLaplace g (hardyVerticalLine σ y)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y : ℝ, defectTentTest h n y * defectBoundaryL2 (hg.toLp g) y)) := by
  let k : DefectL2 := (memLp_defectTentTest hh n).toLp (defectTentTest h n)
  have he (f : ℝ → ℂ) : (∫ y : ℝ, (starRingEnd ℂ) (k y) * f y) =
      ∫ y : ℝ, defectTentTest h n y * f y := by
    apply integral_congr_ae
    filter_upwards [(memLp_defectTentTest hh n).coeFn_toLp] with y hy
    change k y = defectTentTest h n y at hy
    rw [hy]
    simp only [defectTentTest, Complex.conj_ofReal]
  have hJ (z : ℂ) : defectLaplace (hg.toLp g : ℝ → ℂ) z = defectLaplace g z :=
    defectLaplace_congr_ae hg.coeFn_toLp z
  simpa only [he, hJ] using tendsto_integral_defectLaplace_L2_boundary (hg.toLp g) k

private theorem integral_scaled_tent_eq_interval {h : ℝ} (hh : 0 < h)
    (n : ℝ) (f : ℝ → ℝ) :
    (∫ y : ℝ, unitTent n (y / h) * f y) =
      ∫ s in (-1 : ℝ)..1, h * (1 - |s|) * f (h * (n + s)) := by
  let F : ℝ → ℝ := fun y => unitTent n (y / h) * f y
  have he (s : ℝ) : unitTent 0 s * f (h * (n + s)) = F (h * (n + s)) := by
    dsimp only [F]
    congr 1
    simp only [unitTent, sub_zero]
    have hx : h * (n + s) / h - n = s := by field_simp [hh.ne']; ring
    rw [hx]
  have hcv : (∫ s : ℝ, unitTent 0 s * f (h * (n + s))) =
      h⁻¹ * ∫ y : ℝ, unitTent n (y / h) * f y := by
    calc
      _ = ∫ s : ℝ, F (h * (n + s)) := integral_congr_ae (Eventually.of_forall he)
      _ = ∫ s : ℝ, F (h * s) := integral_add_left_eq_self (fun s => F (h * s)) n
      _ = _ := by
        rw [Measure.integral_comp_mul_left]
        simp only [abs_of_pos (inv_pos.mpr hh), smul_eq_mul, F]
  symm
  calc
    _ = h * ∫ s in (-1 : ℝ)..1, (1 - |s|) * f (h * (n + s)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      ring
    _ = h * ∫ s : ℝ, unitTent 0 s * f (h * (n + s)) := by
      rw [intervalIntegral_window_eq_integral_unitTent]
    _ = h * (h⁻¹ * ∫ y : ℝ, unitTent n (y / h) * f y) := by rw [hcv]
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

private theorem integral_tentDefectKernel_eq_height {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) {h ε : ℝ}
    (hh : 0 < h) (hε : 0 < ε) (n : ℝ) :
    (∫ s in (-1 : ℝ)..1, tentDefectKernel g h n ε s) =
      (∫ y : ℝ, defectTentTest h n y *
        defectLaplace g (hardyVerticalLine (h * ε) y)).re := by
  have hI : Integrable (fun y : ℝ => defectTentTest h n y *
      defectLaplace g (hardyVerticalLine (h * ε) y)) :=
    (memLp_defectTentTest hh n).integrable_mul
      (memLp_defectLaplace_vertical hg (mul_pos hh hε))
  have hRe : (∫ y : ℝ, defectTentTest h n y *
      defectLaplace g (hardyVerticalLine (h * ε) y)).re =
      ∫ y : ℝ, (defectTentTest h n y *
        defectLaplace g (hardyVerticalLine (h * ε) y)).re := (integral_re hI).symm
  rw [hRe]
  have he : (fun y : ℝ => (defectTentTest h n y *
      defectLaplace g (hardyVerticalLine (h * ε) y)).re) =
      fun y => unitTent n (y / h) * (defectLaplace g (hardyVerticalLine (h * ε) y)).re := by
    funext y
    exact Complex.re_ofReal_mul _ _
  rw [he, integral_scaled_tent_eq_interval hh]
  apply intervalIntegral.integral_congr
  intro s _
  have hz : (h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I) =
      hardyVerticalLine (h * ε) (h * (n + s)) := by
    unfold hardyVerticalLine
    push_cast
    ring
  simp only [tentDefectKernel, hz]

/-- The actual finite-energy defect term passes through every positive-width tent. -/
theorem tendsto_tentDefectKernel_finiteEnergy {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) {h : ℝ} (hh : 0 < h) (n : ℝ) :
    Tendsto (fun ε : ℝ => ∫ s in (-1 : ℝ)..1, tentDefectKernel g h n ε s)
      (𝓝[>] (0 : ℝ)) (𝓝 (finiteEnergyTentError (hg.toLp g) h n)) := by
  have ht : Tendsto (fun ε : ℝ => h * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun ε : ℝ => h * ε) := continuous_const.mul continuous_id
      simpa using (hc.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · exact eventually_nhdsWithin_of_forall fun ε hε => mul_pos hh hε
  have hl := (Complex.continuous_re.tendsto _).comp
    ((tendsto_tent_integral_defectLaplace hg hh n).comp ht)
  refine hl.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_tentDefectKernel_eq_height hg hh hε n).symm

private theorem continuous_tentDefectKernel_of_polynomial {g : ℝ → ℂ}
    {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n : ℝ) :
    Continuous (tentDefectKernel g h n ε) := by
  have hc := (differentiableOn_defectLaplace hgm.aestronglyMeasurable hgb).continuousOn
  have hcu : ContinuousOn (fun s : ℝ => defectLaplace g
      ((h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I))) univ := by
    apply hc.comp (by fun_prop)
    intro s _
    simpa using mul_pos hh hε
  change Continuous fun s : ℝ => h * (1 - |s|) *
    (defectLaplace g ((h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I))).re
  exact (by fun_prop : Continuous fun s : ℝ => h * (1 - |s|)).mul
    (Complex.continuous_re.comp (continuousOn_univ.mp hcu))

private theorem tent_pairing_identity_of_polynomial_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h n ε : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hn : 1 ≤ n)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ u, (∫ s in (-1 : ℝ)..1, tentSeriesKernel h n ε s u) ∂ν =
      (∫ u, (∫ s in (-1 : ℝ)..1, tentDualKernel h n ε s u) ∂ν) +
        (∫ s in (-1 : ℝ)..1, tentPolarKernel h β n ε s) +
          ∫ s in (-1 : ℝ)..1, tentDefectKernel g h n ε s := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  have hS := integrable_tentSeriesKernel hsupp hmom hh hh1 hn hε hε1
  have hD := integrable_tentDualKernel hsupp hmom hh hε n
  have hDi : IntervalIntegrable (fun s : ℝ => ∫ u, tentDualKernel h n ε s u ∂ν) volume (-1) 1 :=
    intervalIntegrable_iff.mpr hD.integral_prod_left
  have hPi : IntervalIntegrable (tentPolarKernel h β n ε) volume (-1) 1 :=
    (continuous_tentPolarKernel h β n hε).intervalIntegrable (-1) 1
  have hJi : IntervalIntegrable (tentDefectKernel g h n ε) volume (-1) 1 :=
    (continuous_tentDefectKernel_of_polynomial hgm hgb hh hε n).intervalIntegrable (-1) 1
  have he : (∫ s in (-1 : ℝ)..1, ∫ u, tentSeriesKernel h n ε s u ∂ν) =
      (∫ s in (-1 : ℝ)..1, ∫ u, tentDualKernel h n ε s u ∂ν) +
        (∫ s in (-1 : ℝ)..1, tentPolarKernel h β n ε s) +
          ∫ s in (-1 : ℝ)..1, tentDefectKernel g h n ε s := by
    rw [intervalIntegral.integral_congr (fun s _ =>
      integral_tentSeriesKernel_eq_of_theta_defect hsupp hmom hgm hgb hθ hh hε n s),
      intervalIntegral.integral_add (hDi.add hPi) hJi,
      intervalIntegral.integral_add hDi hPi]
  rwa [intervalIntegral_integral_swap hS, intervalIntegral_integral_swap hD] at he

/-- The actual theta identity yields the same atomic and cosine pairing for every
finite-energy defect, with its canonical Hardy boundary as the error term. -/
theorem tent_boundary_identity_of_finite_energy_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h n : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hn : 1 < n) :
    (1 / 2) * (∫ u, unitTent n (u / h) ∂ν) =
      h * (∫ u, Real.cos (2 * Real.pi * (h * u) * n) * tentFourierWeight h u ∂ν) +
        h * β + finiteEnergyTentError (hg.toLp g) h n := by
  have hleft := tendsto_integral_tentSeriesKernel hsupp hmom hh hh1 hn.le
  have hright := ((tendsto_integral_tentDualKernel hsupp hmom hh n).add
    (tendsto_integral_tentPolarKernel h β hn.le)).add
      (tendsto_tentDefectKernel_finiteEnergy hg hh n)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact (tent_pairing_identity_of_polynomial_defect hsupp hmom hgm hgb hθ
    hh hh1 hn.le hε.1 hε.2.le).symm

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.tendsto_tentDefectKernel_finiteEnergy
#print axioms GaloisForLFunctions.EulerFETransportTheory.tent_boundary_identity_of_finite_energy_defect
