import GaloisForLFunctions.RHTower.SelbergMaassTraceBoundary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact paired Maass trace Stokes and cusp boundary identity

Actual C² derivatives of the finite congruence trace satisfy vertical and horizontal
FTC. Translation and inversion cancel the side and circular currents in the paired
coordinate integral. Its surviving top current equals twice the actual total cusp
flux, hence attaches to the complete Bessel boundary form and square remainder.

`pairedBulk` is a literal paired coordinate divergence integral. This module does
not identify it with a two-dimensional set integral on the modular domain and does
not prove a compact-core quarter bound or Selberg's conjecture.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassTraceStokes
open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceEnergy SelbergMaassTraceBoundary
noncomputable section

/-- Height of the unit-circle boundary in the modular strip. -/
def arcHeight (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

/-- The circular boundary stays strictly above the real axis on the modular strip. -/
theorem arcHeight_pos {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : 0 < arcHeight x := by
  apply Real.sqrt_pos.mpr
  nlinarith [hx.1, hx.2, sq_nonneg (x + 1 / 2), sq_nonneg (1 / 2 - x)]

/-- Exact squared height of the circular boundary. -/
theorem arcHeight_sq {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    arcHeight x ^ 2 = 1 - x ^ 2 :=
  Real.sq_sqrt (Real.sqrt_pos.mp (arcHeight_pos hx)).le

/-- Vertical FTC for an actual first directional trace current. -/
theorem vertical_current_integral (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v : ℂ) (x : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b, dir Complex.I (dir v (density N f ∘ ofComplex)) (point x y)) =
      currentAt N f v x b - currentAt N f v x a := by
  have hpos : uIcc a b ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact lt_of_lt_of_le (lt_min ha hb) hy.1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => currentAt_vertical N f v x (hpos hy))
    ((second_current_vertical_continuousOn N f Complex.I v x).mono hpos).intervalIntegrable

/-- Horizontal FTC for an actual first directional trace current. -/
theorem horizontal_current_integral (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v : ℂ) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    (∫ x in a..b, dir 1 (dir v (density N f ∘ ofComplex)) (point x y)) =
      currentAt N f v b y - currentAt N f v a y :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => currentAt_horizontal N f v hy x)
    ((second_current_horizontal_continuous N f 1 v hy).intervalIntegrable _ _)

/-- Literal paired vertical and weighted horizontal second-derivative integral. -/
def pairedBulk (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (Y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(1 / 2),
    ((∫ y in arcHeight x..Y, dir Complex.I (dir Complex.I (density N f ∘ ofComplex)) (point (-x) y)) +
      (∫ y in arcHeight x..Y, dir Complex.I (dir Complex.I (density N f ∘ ofComplex)) (point x y)) +
      (x / arcHeight x) *
        ((∫ q in (-(1 / 2 : ℝ))..(-x), dir 1 (dir 1 (density N f ∘ ofComplex)) (point q (arcHeight x))) +
          ∫ q in x..(1 / 2), dir 1 (dir 1 (density N f ∘ ofComplex)) (point q (arcHeight x))))

/-- Literal paired vertical current at the cutoff height. -/
def pairedTop (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (Y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(1 / 2), (currentAt N f Complex.I (-x) Y + currentAt N f Complex.I x Y)

/-- Actual arc and side cancellation leaves precisely the paired top current. -/
theorem paired_stokes (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {Y : ℝ} (hY : 0 < Y) : pairedBulk N f Y = pairedTop N f Y := by
  unfold pairedBulk pairedTop
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Icc (0 : ℝ) (1 / 2) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
  have hxF : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hxI.1], hxI.2⟩
  have ha := arcHeight_pos hxF
  dsimp only
  rw [vertical_current_integral N f Complex.I (-x) ha hY,
    vertical_current_integral N f Complex.I x ha hY,
    horizontal_current_integral N f 1 ha (-(1 / 2)) (-x),
    horizontal_current_integral N f 1 ha x (1 / 2), currentAt_side_cancellation N f ha]
  have h := currentAt_arc_cancellation N f (x := x) ha (by rw [arcHeight_sq hxF]; ring)
  linear_combination h

/-- Period one identifies the paired top with its actual unit-strip integral. -/
theorem pairedTop_eq_unit_current (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {Y : ℝ} (hY : 0 < Y) :
    pairedTop N f Y = ∫ x in (0 : ℝ)..1, currentAt N f Complex.I x Y := by
  have hc := currentAt_horizontal_continuous N f Complex.I hY
  have hneg : Continuous (fun x => currentAt N f Complex.I (-x) Y) := hc.comp continuous_neg
  unfold pairedTop
  rw [intervalIntegral.integral_add (hneg.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), intervalIntegral.integral_comp_neg (fun x => currentAt N f Complex.I x Y)]
  simp only [neg_zero]
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hp := (currentAt_periodic N f Complex.I hY).intervalIntegral_add_eq (-(1 / 2)) 0
  norm_num at hp
  exact hp

/-- The unit-strip vertical current equals twice the sum of physical Maass fluxes. -/
theorem unit_current_eq_sum_flux (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, currentAt N f Complex.I x y) =
      2 * ∑ q : Deck N, SelbergMaassFlux.flux N (quotientForm N f q) y := by
  let D : ℂ → ℝ := density N f ∘ ofComplex
  let G : ℂ → ℂ := fun z => (D z : ℂ)
  have hD : ContDiffOn ℝ 1 D {z : ℂ | 0 < z.im} :=
    (density_contDiffOn N f).of_le (by simp)
  have hG : ContDiffOn ℝ 1 G {z : ℂ | 0 < z.im} :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hD
  have he (x : ℝ) : directional Complex.I G (point x y) =
      (currentAt N f Complex.I x y : ℂ) := by
    have hp : 0 < (point x y).im := by simpa [point] using hy
    have hd := ((hD.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
    have hs := hd.comp_hasDerivAt y (point_vertical x y)
    exact (slice_vertical hG x hy).unique
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y hs)
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (periodIntegral_hasDerivAt 1 hG hy)
  change HasDerivAt (fun t => (periodIntegral 1 G t).re)
    (periodIntegral 1 (directional Complex.I G) y).re y at h
  have hv : (periodIntegral 1 (directional Complex.I G) y).re =
      ∫ x in (0 : ℝ)..1, currentAt N f Complex.I x y := by
    unfold periodIntegral
    simp_rw [he]
    rw [integral_complex_ofReal, Complex.ofReal_re,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hv] at h
  have hf : (fun t => (periodIntegral 1 G t).re) =
      (fun t => ∫ x in (0 : ℝ)..1, density N f (ofComplex (point x t))) := by
    funext t
    simp only [periodIntegral, G, D, Function.comp_def, integral_complex_ofReal,
      Complex.ofReal_re, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hf] at h
  exact h.unique (density_slice_mass_hasDerivAt N f hy)

/-- Exact source Stokes formula with its actual congruence-normalized cusp flux. -/
theorem paired_stokes_flux (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {Y : ℝ} (hY : 0 < Y) : pairedBulk N f Y =
      2 * ∑ q : Deck N, SelbergMaassFlux.flux N (quotientForm N f q) Y := by
  rw [paired_stokes N f hY, pairedTop_eq_unit_current N f hY, unit_current_eq_sum_flux N f hY]

/-- The paired source integral attaches to the full actual Bessel boundary form and square remainder. -/
theorem paired_stokes_bessel_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (T : ℝ) :
    -(1 / 2) * pairedBulk N f (Real.exp T) +
      ((lam : ℝ) - 1 / 4) * tailMass N f (Real.exp T) = boundarySum N f T + squareSum N f T := by
  rw [paired_stokes_flux N f (Real.exp_pos T)]
  convert trace_flux_boundary_identity N lam f T using 1
  ring

end
end GaloisForLFunctions.RHTower.SelbergMaassTraceStokes
