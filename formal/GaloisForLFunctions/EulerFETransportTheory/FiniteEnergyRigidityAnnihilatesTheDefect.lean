import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyFunctionalEquationsDetermineThePrimes
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticForcesBlindness
import GaloisForLFunctions.HTGeometry.LaplaceRayInjective
import GaloisForLFunctions.RHTower.ZetaChiVerticalGrowth
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Finite-energy arithmetic rigidity annihilates the actual defect

The Mellin source representation makes the Hamburger Laplace transform injective
on square-integrable data. Once arithmetic rigidity identifies the integer measure,
its exact Jacobi theta law forces the original defect to vanish almost everywhere.
Continuity in the original strip identity upgrades this to pointwise vanishing.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticPositiveDuality
open RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- The actual Hamburger Laplace transform has no nonzero finite-energy null source. -/
theorem ae_eq_zero_of_finiteEnergy_defectLaplace_eq_zero {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hzero : ∀ z : ℂ, 0 < z.re → defectLaplace g z = 0) :
    g =ᵐ[volume] 0 := by
  have hs := ae_eq_zero_of_laplaceRay_eq_zero
    (Lp.memLp (defectMellinSource (hg.toLp g))) (fun z hz => by
      rw [← defectLaplace_eq_laplaceRay (hg.toLp g) hz,
        defectLaplace_congr_ae hg.coeFn_toLp]
      exact hzero z hz)
  have hsource : defectMellinSource (hg.toLp g) = 0 := by
    apply Lp.ext
    filter_upwards [hs, Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))] with x hx hz
    exact hx.trans hz.symm
  have hLp : hg.toLp g = 0 := defectMellinSource_bijective.1 (by rw [hsource, map_zero])
  have he := hg.coeFn_toLp.symm
  rw [hLp] at he
  exact he.trans (Lp.coeFn_zero ℂ 2 volume)

/-- The actual finite-energy theta law forces the defect itself to vanish almost
everywhere, in addition to identifying all rational-prime generators. -/
theorem beurling_finiteEnergy_defect_ae_eq_zero
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    g =ᵐ[volume] 0 := by
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  have hβ := measure_pole_real_of_finiteEnergy_theta_defect hsupp hmom hgm hgb hg hθ
  have hθreal : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β.re : ℂ) + (β.re : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    simpa only [hβ] using hθ
  obtain ⟨hb, hν, _⟩ :=
    beurlingSystem_rigidity_of_finiteEnergy_theta_defect B hBsum hgm hgb hg hθreal
  have hbC : β = 1 / 2 := by rw [← hβ, hb]; norm_num
  have hθexact : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro x hx
    rw [hν, beurlingIntegerMeasure_riemannPrimeMeasure, hbC]
    simpa only [neg_div] using
      GaloisForLFunctions.ArithmeticCastelnuovoSeveri.measureTheta_nat_sum_relation hx
  apply ae_eq_zero_of_finiteEnergy_defectLaplace_eq_zero hg
  intro z hz
  have hdef := measureSeries_eq_of_theta_defect hsupp hmom hgm hgb hθ hz
  have hexact := measureSeries_eq_of_measureTheta_relation hsupp hmom hθexact hz
  linear_combination hexact - hdef

private theorem continuous_gamma_vertical {a : ℝ} (ha0 : a ≠ 0) (ha : -1 ≤ a) :
    Continuous (fun t : ℝ => Complex.Gammaℝ ((a : ℂ) + (t : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact ContinuousAt.comp (f := fun u : ℝ => (a : ℂ) + (u : ℂ) * I)
    (RHTower.continuousAt_Gammaℝ_of_ne_poles
      (RHTower.vertical_ne_neg_two_mul (t := t) ha0 ha)) (by fun_prop)

private theorem strip_defect_eq_zero_of_ae_eq_zero {E : ℂ → ℂ} {β : ℂ} {g : ℝ → ℂ}
    (hEc : ContinuousOn E (HTGeometry.verticalStrip (1 / 2) (3 / 2)))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hg : g =ᵐ[volume] 0) : ∀ t, g t = 0 := by
  let L : ℝ → ℂ := fun t => (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I
  have hL : Continuous L := by dsimp only [L]; fun_prop
  have hmem (t : ℝ) : L t ∈ HTGeometry.verticalStrip (1 / 2) (3 / 2) := by
    norm_num [L, HTGeometry.verticalStrip]
  have hmem' (t : ℝ) : 1 - L t ∈ HTGeometry.verticalStrip (1 / 2) (3 / 2) := by
    norm_num [L, HTGeometry.verticalStrip]
  have he : Continuous (fun t => E (L t)) := hEc.comp_continuous hL hmem
  have her : Continuous (fun t => E (1 - L t)) :=
    hEc.comp_continuous (continuous_const.sub hL) hmem'
  have hgam := continuous_gamma_vertical (a := -(1 / 2)) (by norm_num) (by norm_num)
  have hgm : Continuous (fun t => Complex.Gammaℝ (L t - 1)) := by
    have hh := hgam.comp (show Continuous (fun t : ℝ => 2 * t) by fun_prop)
    convert hh using 1
    funext t
    congr 1
    dsimp only [L]
    push_cast
    ring
  have hgn : Continuous (fun t => Complex.Gammaℝ (-L t)) := by
    have hh := hgam.comp (show Continuous (fun t : ℝ => -(2 * t)) by fun_prop)
    convert hh using 1
    funext t
    congr 1
    dsimp only [L]
    push_cast
    ring
  let F : ℝ → ℂ := fun t => E (L t) - E (1 - L t) +
    β * (Complex.Gammaℝ (L t - 1) - Complex.Gammaℝ (-L t))
  have hF : Continuous F := he.sub her |>.add (continuous_const.mul (hgm.sub hgn))
  have hEq (t : ℝ) : F t = Complex.Gammaℝ (L t) * g t := by
    have hh := hC (L t) (by norm_num [L])
    have him : (L t).im / 2 = t := by simp [L]
    rw [him] at hh
    dsimp only [F]
    linear_combination hh
  have hFae : F =ᵐ[volume] 0 := by
    filter_upwards [hg] with t ht
    rw [hEq, ht]
    exact mul_zero _
  have hFzero : F = 0 := Measure.eq_of_ae_eq hFae hF continuous_const
  intro t
  have hz : Complex.Gammaℝ (L t) * g t = 0 := by rw [← hEq, hFzero]; rfl
  exact (mul_eq_zero.mp hz).resolve_left
    (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [L]))

/-- The original pointwise Hamburger strip identity has no nonzero finite-energy
defect, including changes supported on null sets. -/
theorem beurling_finiteEnergy_strip_defect_eq_zero
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {Ng : ℕ}
    (hEc : ContinuousOn E (HTGeometry.verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ HTGeometry.verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * beurlingZeta B s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ Ng)
    (hg : MemLp g 2 (volume : Measure ℝ)) : ∀ t, g t = 0 := by
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_rpow_beurlingSystemIntegerMeasure B hBsum
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * measureDirichlet (beurlingSystemIntegerMeasure B) s =
        E s + β * Complex.Gammaℝ (s - 1) := by
    simpa only [measureDirichlet_beurlingSystemIntegerMeasure] using hR
  have hθ := measureTheta_defect_relation hsupp hmom hEc hEd hdecay hR' hC hgm hgb
  exact strip_defect_eq_zero_of_ae_eq_zero hEc hC
    (beurling_finiteEnergy_defect_ae_eq_zero B hBsum hgm hgb hg hθ)

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.ae_eq_zero_of_finiteEnergy_defectLaplace_eq_zero
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_finiteEnergy_defect_ae_eq_zero
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_finiteEnergy_strip_defect_eq_zero
