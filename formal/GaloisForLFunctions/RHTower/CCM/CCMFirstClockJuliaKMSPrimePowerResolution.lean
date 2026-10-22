import GaloisForLFunctions.RHTower.CCM.CCMFirstClockJuliaScaleFourTransfer
import GaloisForLFunctions.RHTower.VonMangoldtGammaDepthOneCauchy
import GaloisForLFunctions.HTGeometry.JuliaKMSScaleFourInnovation

/-!
# Julia--KMS scale resolution of the literal critical Mellin prime-power source

The critical Dirichlet density is the inverse finite-KMS fluctuation--dissipation factor.  At the
half logarithmic gap it cancels the depth-one Gamma source displacement exactly:

`D(h / 2) (1 - exp (-h)) = exp (-h / 2)`.

At `h = log q`, multiplication by `vonMangoldt q` is therefore the literal critical Mellin atom
`vonMangoldt q / sqrt q`.  Applying the scale-four Dirichlet--Julia telescope gives an exact
positive innovation resolution of every prime-power atom and hence of the finite first-clock prime
sine source.

The first innovation captures a strictly increasing fraction of the atom as the full integer
frequency `q` grows; its residual tail fraction is strictly decreasing.  This distinguishes
valuation exponents inside one prime tower, unlike prime-base-only attenuation laws.

Every innovation remains diagonal in the external sine phase.  A counter-phased atom is still
negative at every scale, so the result is not RH; it isolates the remaining need for non-diagonal
phase mixing or a signed inter-scale compensation theorem.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The inverse-KMS Dirichlet factor cancels a positive depth-one exponential displacement and
leaves its symmetric half-weight. -/
theorem criticalDirichletLevyRadialDensity_mul_depthOneDisplacement_eq_halfWeight
    {h : ℝ} (hh : 0 < h) :
    _root_.HTGeometry.criticalDirichletLevyRadialDensity (h / 2) *
        (1 - Real.exp (-h)) =
      Real.exp (-h / 2) := by
  have hh2 : 0 < h / 2 := by linarith
  have hden : 1 - Real.exp (-h) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  rw [_root_.HTGeometry.criticalDirichletLevyRadialDensity_eq_exp_neg_div hh2,
    show -2 * (h / 2) = -h by ring]
  simpa only [neg_div] using
    (div_mul_cancel₀ (Real.exp (-h / 2)) hden)

/-- At an integer logarithmic gap, the inverse-KMS depth-one displacement is exactly the critical
radial half-weight `q⁻¹ᐟ²`. -/
theorem criticalDirichletDepthOneDisplacement_eq_natHalfWeight
    {q : ℕ} (hq : 2 ≤ q) :
    _root_.HTGeometry.criticalDirichletLevyRadialDensity (Real.log q / 2) *
        (1 - Real.exp (-Real.log q)) =
      (q : ℝ) ^ (-1 / 2 : ℝ) := by
  have hqR : (0 : ℝ) < q := by positivity
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  rw [criticalDirichletLevyRadialDensity_mul_depthOneDisplacement_eq_halfWeight hlog,
    Real.rpow_def_of_pos hqR]
  congr 1
  ring

/-- **Critical Mellin inverse-FDT weld.**  Every nontrivial integer atom is von Mangoldt mass
times its depth-one Gamma displacement, renormalized by the critical inverse-KMS Dirichlet factor. -/
theorem criticalMellinAtomWeight_eq_dirichletDepthOneDisplacement
    {q : ℕ} (hq : 2 ≤ q) :
    criticalMellinAtomWeight q =
      (ArithmeticFunction.vonMangoldt q *
          (1 - Real.exp (-Real.log q))) *
        _root_.HTGeometry.criticalDirichletLevyRadialDensity (Real.log q / 2) := by
  rw [criticalMellinAtomWeight,
    ← criticalDirichletDepthOneDisplacement_eq_natHalfWeight hq]
  ring

/-- The same weld written with the literal depth-one anomaly coefficient already used by the
von Mangoldt--Gamma descent construction. -/
theorem criticalMellinAtomWeight_eq_dirichlet_mul_depthOneAnomalyCoefficient
    {q : ℕ} (hq : 2 ≤ q) :
    (criticalMellinAtomWeight q : ℂ) =
      (_root_.HTGeometry.criticalDirichletLevyRadialDensity
          (Real.log q / 2) : ℂ) *
        finiteExponentialDepthOneAnomalyCoefficient
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          finiteVonMangoldtFrequency q := by
  rw [finiteExponentialDepthOneAnomalyCoefficient,
    finiteVonMangoldtFrequency,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  norm_cast
  rw [criticalMellinAtomWeight_eq_dirichletDepthOneDisplacement hq]
  ring

/-- Scale-`j` Julia innovation contribution to the literal critical Mellin atom at `q`. -/
def criticalMellinJuliaKMSInnovationLayer (q : ℕ) (j : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt q *
      (1 - Real.exp (-Real.log q))) *
    ((4 : ℝ) ^ j *
      _root_.HTGeometry.juliaScaleFourInnovationDensity
        ((4 : ℝ) ^ j * (Real.log q / 2)))

/-- Residual critical Dirichlet response after resolving the first `n` Julia scales. -/
def criticalMellinJuliaKMSInnovationTail (q : ℕ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt q *
      (1 - Real.exp (-Real.log q))) *
    ((4 : ℝ) ^ n *
      _root_.HTGeometry.criticalDirichletLevyRadialDensity
        ((4 : ℝ) ^ n * (Real.log q / 2)))

/-- **Literal prime-power Julia innovation telescope.**  Every critical Mellin atom is exactly the
sum of its first `n` Julia inverse-FDT layers and one unresolved Dirichlet tail. -/
theorem criticalMellinAtomWeight_eq_juliaKMSInnovationTelescope
    {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    criticalMellinAtomWeight q =
      (∑ j ∈ Finset.range n, criticalMellinJuliaKMSInnovationLayer q j) +
        criticalMellinJuliaKMSInnovationTail q n := by
  rw [criticalMellinAtomWeight_eq_dirichletDepthOneDisplacement hq,
    _root_.HTGeometry.criticalDirichletLevyRadialDensity_scaleFour_telescope,
    mul_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [criticalMellinJuliaKMSInnovationLayer]

/-- Every literal critical-Mellin Julia layer is nonnegative. -/
theorem criticalMellinJuliaKMSInnovationLayer_nonneg
    {q : ℕ} (hq : 2 ≤ q) (j : ℕ) :
    0 ≤ criticalMellinJuliaKMSInnovationLayer q j := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hdisp : 0 < 1 - Real.exp (-Real.log q) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have harg : 0 < (4 : ℝ) ^ j * (Real.log q / 2) := by positivity
  have hJ := _root_.HTGeometry.juliaScaleFourInnovationDensity_pos harg
  rw [criticalMellinJuliaKMSInnovationLayer]
  positivity

/-- Every layer is strictly positive exactly on the prime-power support needed by the first-clock
source. -/
theorem criticalMellinJuliaKMSInnovationLayer_pos
    {q : ℕ} (hq : IsPrimePow q) (j : ℕ) :
    0 < criticalMellinJuliaKMSInnovationLayer q j := by
  have hq1 : 1 < q := IsPrimePow.one_lt hq
  have hq2 : 2 ≤ q := by omega
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq2)
  have hdisp : 0 < 1 - Real.exp (-Real.log q) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have harg : 0 < (4 : ℝ) ^ j * (Real.log q / 2) := by positivity
  have hJ := _root_.HTGeometry.juliaScaleFourInnovationDensity_pos harg
  have hvm := ArithmeticFunction.vonMangoldt_pos_iff.mpr hq
  rw [criticalMellinJuliaKMSInnovationLayer]
  positivity

/-- Every finite-resolution tail is strictly positive on prime powers. -/
theorem criticalMellinJuliaKMSInnovationTail_pos
    {q : ℕ} (hq : IsPrimePow q) (n : ℕ) :
    0 < criticalMellinJuliaKMSInnovationTail q n := by
  have hq1 : 1 < q := IsPrimePow.one_lt hq
  have hq2 : 2 ≤ q := by omega
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq2)
  have hdisp : 0 < 1 - Real.exp (-Real.log q) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have harg : 0 < (4 : ℝ) ^ n * (Real.log q / 2) := by positivity
  have hD : 0 < _root_.HTGeometry.criticalDirichletLevyRadialDensity
      ((4 : ℝ) ^ n * (Real.log q / 2)) := by
    rw [_root_.HTGeometry.criticalDirichletLevyRadialDensity]
    positivity
  have hvm := ArithmeticFunction.vonMangoldt_pos_iff.mpr hq
  rw [criticalMellinJuliaKMSInnovationTail]
  positivity

/-- The published finite first-clock prime sine source has an exact atomwise Julia innovation
resolution at every finite scale. -/
theorem ccmFirstClockPrimeSineMass_eq_juliaKMSInnovationTelescope
    (L xi : ℝ) (n : ℕ) :
    ccmFirstClockPrimeSineMass L xi =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        ((∑ j ∈ Finset.range n, criticalMellinJuliaKMSInnovationLayer q j) +
            criticalMellinJuliaKMSInnovationTail q n) *
          Real.sin (xi * Real.log q) := by
  rw [ccmFirstClockPrimeSineMass]
  apply Finset.sum_congr rfl
  intro q hq
  have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
  rw [← criticalMellinAtomWeight_eq_juliaKMSInnovationTelescope hq2 n]

/-- **Sharp diagonal phase no-go.**  A negative external first-clock phase stays negative on every
strictly positive prime-power Julia innovation layer. -/
theorem criticalMellinJuliaKMSInnovationLayer_mul_neg
    {q : ℕ} (hq : IsPrimePow q) (j : ℕ)
    {phase : ℝ} (hphase : phase < 0) :
    criticalMellinJuliaKMSInnovationLayer q j * phase < 0 :=
  mul_neg_of_pos_of_neg (criticalMellinJuliaKMSInnovationLayer_pos hq j) hphase

/-! ### Frequency ordering of captured and residual mass -/

/-- Fraction of Dirichlet mass captured by the first scale-four Julia innovation. -/
def juliaScaleFourCaptureFraction (x : ℝ) : ℝ :=
  1 - 1 / (Real.cosh x * Real.cosh (2 * x))

/-- The first Julia innovation is the Dirichlet density times its explicit capture fraction. -/
theorem juliaScaleFourInnovationDensity_eq_dirichlet_mul_captureFraction
    {x : ℝ} (hx : 0 < x) :
    _root_.HTGeometry.juliaScaleFourInnovationDensity x =
      _root_.HTGeometry.criticalDirichletLevyRadialDensity x *
        juliaScaleFourCaptureFraction x := by
  have hsx : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hs4x : Real.sinh (4 * x) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by linarith)).ne'
  have hcx : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hc2x : Real.cosh (2 * x) ≠ 0 := (Real.cosh_pos (2 * x)).ne'
  have hsinh4 : Real.sinh (4 * x) =
      4 * Real.sinh x * Real.cosh x * Real.cosh (2 * x) := by
    rw [show 4 * x = 2 * (2 * x) by ring, Real.sinh_two_mul,
      Real.sinh_two_mul]
    ring
  rw [_root_.HTGeometry.juliaScaleFourInnovationDensity,
    _root_.HTGeometry.criticalDirichletLevyRadialDensity,
    _root_.HTGeometry.criticalDirichletLevyRadialDensity,
    juliaScaleFourCaptureFraction, hsinh4]
  field_simp [hsx, hcx, hc2x]

/-- Capture fraction is strictly increasing on positive frequencies. -/
theorem juliaScaleFourCaptureFraction_strictMonoOn
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    juliaScaleFourCaptureFraction x < juliaScaleFourCaptureFraction y := by
  have hy : 0 < y := hx.trans hxy
  have hcx : Real.cosh x < Real.cosh y := by
    rw [Real.cosh_lt_cosh, abs_of_pos hx, abs_of_pos hy]
    exact hxy
  have h2x : 0 < 2 * x := by positivity
  have h2y : 0 < 2 * y := by positivity
  have hc2 : Real.cosh (2 * x) < Real.cosh (2 * y) := by
    rw [Real.cosh_lt_cosh, abs_of_pos h2x, abs_of_pos h2y]
    linarith
  have hprod : Real.cosh x * Real.cosh (2 * x) <
      Real.cosh y * Real.cosh (2 * y) :=
    mul_lt_mul hcx hc2.le (Real.cosh_pos _) (Real.cosh_pos _).le
  have hprodpos : 0 < Real.cosh x * Real.cosh (2 * x) := by positivity
  have hinv := one_div_lt_one_div_of_lt hprodpos hprod
  rw [juliaScaleFourCaptureFraction, juliaScaleFourCaptureFraction]
  linarith

/-- The captured fraction strictly increases with the full integer frequency, hence also with
valuation exponent inside any fixed prime tower. -/
theorem juliaScaleFourCaptureFraction_nat_strictMono
    {q r : ℕ} (hq : 2 ≤ q) (hqr : q < r) :
    juliaScaleFourCaptureFraction (Real.log q / 2) <
      juliaScaleFourCaptureFraction (Real.log r / 2) := by
  have hqR : (0 : ℝ) < q := by positivity
  have hqrR : (q : ℝ) < r := by exact_mod_cast hqr
  have hrR : (0 : ℝ) < r := hqR.trans hqrR
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hloglt : Real.log q < Real.log r :=
    (Real.log_lt_log_iff hqR hrR).mpr (by exact_mod_cast hqr)
  exact juliaScaleFourCaptureFraction_strictMonoOn (by linarith) (by linarith)

/-- The first literal prime-power innovation is exactly the critical atom times its capture
fraction. -/
theorem criticalMellinJuliaKMSInnovationLayer_zero_eq_captureFraction
    {q : ℕ} (hq : 2 ≤ q) :
    criticalMellinJuliaKMSInnovationLayer q 0 =
      criticalMellinAtomWeight q *
        juliaScaleFourCaptureFraction (Real.log q / 2) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  rw [criticalMellinJuliaKMSInnovationLayer, pow_zero, one_mul,
    juliaScaleFourInnovationDensity_eq_dirichlet_mul_captureFraction (by linarith),
    criticalMellinAtomWeight_eq_dirichletDepthOneDisplacement hq]
  ring_nf

/-- Fraction of critical mass remaining after the first Julia scale. -/
def juliaScaleFourTailFraction (x : ℝ) : ℝ :=
  1 - juliaScaleFourCaptureFraction x

/-- The first residual fraction is strictly decreasing on positive frequencies. -/
theorem juliaScaleFourTailFraction_strictAntiOn
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    juliaScaleFourTailFraction y < juliaScaleFourTailFraction x := by
  have hcapture := juliaScaleFourCaptureFraction_strictMonoOn hx hxy
  rw [juliaScaleFourTailFraction, juliaScaleFourTailFraction]
  linarith

/-- The residual fraction strictly decreases with the full integer prime-power frequency. -/
theorem juliaScaleFourTailFraction_nat_strictAnti
    {q r : ℕ} (hq : 2 ≤ q) (hqr : q < r) :
    juliaScaleFourTailFraction (Real.log r / 2) <
      juliaScaleFourTailFraction (Real.log q / 2) := by
  have hcapture := juliaScaleFourCaptureFraction_nat_strictMono hq hqr
  rw [juliaScaleFourTailFraction, juliaScaleFourTailFraction]
  linarith

/-- The scale-four Dirichlet residual is exactly the original density times the explicit tail
fraction. -/
theorem four_mul_criticalDirichletDensity_scaleFour_eq_mul_tailFraction
    {x : ℝ} (hx : 0 < x) :
    4 * _root_.HTGeometry.criticalDirichletLevyRadialDensity (4 * x) =
      _root_.HTGeometry.criticalDirichletLevyRadialDensity x *
        juliaScaleFourTailFraction x := by
  rw [juliaScaleFourTailFraction]
  have hcapture :=
    juliaScaleFourInnovationDensity_eq_dirichlet_mul_captureFraction hx
  rw [_root_.HTGeometry.juliaScaleFourInnovationDensity] at hcapture
  linarith

/-- The first unresolved literal prime-power tail is the critical atom times its strictly
decreasing frequency filter. -/
theorem criticalMellinJuliaKMSInnovationTail_one_eq_tailFraction
    {q : ℕ} (hq : 2 ≤ q) :
    criticalMellinJuliaKMSInnovationTail q 1 =
      criticalMellinAtomWeight q *
        juliaScaleFourTailFraction (Real.log q / 2) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  rw [criticalMellinJuliaKMSInnovationTail, pow_one,
    four_mul_criticalDirichletDensity_scaleFour_eq_mul_tailFraction (by linarith),
    criticalMellinAtomWeight_eq_dirichletDepthOneDisplacement hq]
  ring

end

end RHTower
