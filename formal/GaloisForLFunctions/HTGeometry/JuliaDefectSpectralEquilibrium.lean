import GaloisForLFunctions.HTGeometry.JuliaDefectAttenuation
import GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite

/-!
# Spectral equilibrium structure of the Julia defect

The scalar Gamma--Julia compression square is

`kappa(y) = cosh(y / 2)^2 / sqrt(cosh(2y))`.

Its negative logarithm has the classical hyperbolic Lévy--Khintchine density

`1 / (2 t sinh(pi t / 4)) - 2 / (t sinh(pi t))`.

This file proves the load-bearing pointwise fact: that density is strictly positive.  It also
separates the raw quadratically normalized Lean profile, whose value at zero is forced to be zero
by totalized division, from its canonical spectral extension with value one.  The raw profile is
not positive definite; any characteristic-function theorem must use the extension.
-/

open Set

namespace HTGeometry

noncomputable section

/-- Square of the canonical scalar Gamma--Julia compression. -/
def juliaCompressionSquareProfile (y : ℝ) : ℝ :=
  (Real.sqrt (juliaDefectQuartic (Real.tanh (y / 2))))⁻¹

/-- Hyperbolic closed form of the Julia compression square. -/
theorem juliaCompressionSquareProfile_eq_cosh_ratio (y : ℝ) :
    juliaCompressionSquareProfile y =
      Real.cosh (y / 2) ^ 2 / Real.sqrt (Real.cosh (2 * y)) := by
  rw [juliaCompressionSquareProfile,
    inv_sqrt_juliaDefectQuartic_tanh_eq_cosh_ratio]
  congr 2
  ring_nf

/-- Defect and compression are exact complements. -/
theorem juliaDefectSquareProfile_eq_one_sub_compression (y : ℝ) :
    juliaDefectSquareProfile y = 1 - juliaCompressionSquareProfile y := by
  rfl

/-- Canonical spectral extension of the normalized Julia defect.  The branch at zero is
load-bearing: `juliaDefectAttenuationProfile 0 = 0`, whereas a normalized characteristic
function must equal one there. -/
def juliaDefectAttenuationKernel (y : ℝ) : ℝ :=
  if y = 0 then 1 else juliaDefectAttenuationProfile y

@[simp] theorem juliaDefectAttenuationProfile_zero :
    juliaDefectAttenuationProfile 0 = 0 := by
  simp [juliaDefectAttenuationProfile, juliaDefectSquareProfile,
    juliaDefectQuartic]

@[simp] theorem juliaDefectAttenuationKernel_zero :
    juliaDefectAttenuationKernel 0 = 1 := by
  simp [juliaDefectAttenuationKernel]

theorem juliaDefectAttenuationKernel_eq_profile {y : ℝ} (hy : y ≠ 0) :
    juliaDefectAttenuationKernel y = juliaDefectAttenuationProfile y := by
  simp [juliaDefectAttenuationKernel, hy]

/-- **Anchored Gram capacity.**  For every normalized even real positive-definite kernel, its
origin correlation with a finite real packet is bounded in square by the full coherent Gram
energy.  The proof inserts the origin as one extra node with the optimizing coefficient
`-sum_i b_i K(t_i)`; it is the exact Schur-complement inequality needed by source applications. -/
theorem anchorCorrelation_sq_le_gramEnergy_of_positiveDefinite
    (K : ℝ → ℝ)
    (hPD : GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      (fun y => (K y : ℂ)))
    (hK0 : K 0 = 1) (hEven : ∀ y, K (-y) = K y)
    {N : ℕ} (t b : Fin N → ℝ) :
    (∑ i, b i * K (t i)) ^ 2 ≤
      ∑ i, ∑ j, b i * K (t j - t i) * b j := by
  let S : ℝ := ∑ i, b i * K (t i)
  let T : Fin (N + 1) → ℝ := Fin.cases 0 t
  let C : Fin (N + 1) → ℂ :=
    Fin.cases (-(S : ℂ)) (fun i => (b i : ℂ))
  obtain ⟨r, hr, hq⟩ := hPD (N + 1) T C
  have hsumKB :
      (∑ i, (K (t i) : ℂ) * (b i : ℂ)) = (S : ℂ) := by
    dsimp only [S]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have hsumBK :
      (∑ i, (b i : ℂ) * (K (t i) : ℂ)) = (S : ℂ) := by
    dsimp only [S]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rfl
  have hcrossRight :
      (∑ i, -(S : ℂ) * (K (t i) : ℂ) * (b i : ℂ)) =
        -(S : ℂ) ^ 2 := by
    calc
      _ = ∑ i, -(S : ℂ) * ((K (t i) : ℂ) * (b i : ℂ)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = -(S : ℂ) * ∑ i, (K (t i) : ℂ) * (b i : ℂ) := by
        rw [Finset.mul_sum]
      _ = _ := by rw [hsumKB]; ring
  have hcrossLeft :
      (∑ i, (b i : ℂ) * (K (t i) : ℂ) * -(S : ℂ)) =
        -(S : ℂ) ^ 2 := by
    calc
      _ = (∑ i, (b i : ℂ) * (K (t i) : ℂ)) * -(S : ℂ) := by
        rw [Finset.sum_mul]
      _ = _ := by rw [hsumBK]; ring
  have hinternal :
      (∑ i, ∑ j, (b i : ℂ) * (K (t j - t i) : ℂ) * (b j : ℂ)) =
        ((∑ i, ∑ j, b i * K (t j - t i) * b j : ℝ) : ℂ) := by
    push_cast
    rfl
  have hqform :
      (∑ i, ∑ j, star (C i) * (K (T j - T i) : ℂ) * C j) =
        ((∑ i, ∑ j, b i * K (t j - t i) * b j - S ^ 2 : ℝ) : ℂ) := by
    simp only [Fin.sum_univ_succ, T, C, Fin.cases_zero, Fin.cases_succ,
      Complex.star_def, map_neg, Complex.conj_ofReal, sub_zero, zero_sub,
      hEven]
    rw [hK0]
    rw [hcrossRight, Finset.sum_add_distrib, hcrossLeft, hinternal]
    push_cast
    ring
  rw [hqform] at hq
  have hre := congrArg Complex.re hq
  simp only [Complex.ofReal_re] at hre
  change S ^ 2 ≤ ∑ i, ∑ j, b i * K (t j - t i) * b j
  nlinarith

/-- The unnormalized Julia defect is strictly positive away from the wall on the positive side. -/
theorem juliaDefectSquareProfile_pos {y : ℝ} (hy : 0 < y) :
    0 < juliaDefectSquareProfile y := by
  let t := Real.tanh (y / 2)
  have ht : 0 < t := by
    dsimp only [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have hp : 1 < juliaDefectQuartic t := juliaDefectQuartic_gt_one ht
  have hs : 1 < Real.sqrt (juliaDefectQuartic t) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by positivity) hp
  change 0 < 1 - (Real.sqrt (juliaDefectQuartic t))⁻¹
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hs)

/-- The raw normalized profile is strictly positive at every positive aperture. -/
theorem juliaDefectAttenuationProfile_pos {y : ℝ} (hy : 0 < y) :
    0 < juliaDefectAttenuationProfile y := by
  rw [juliaDefectAttenuationProfile]
  exact div_pos (mul_pos (by norm_num) (juliaDefectSquareProfile_pos hy))
    (sq_pos_of_pos hy)

theorem juliaDefectQuartic_neg (t : ℝ) :
    juliaDefectQuartic (-t) = juliaDefectQuartic t := by
  simp only [juliaDefectQuartic, neg_sq]
  ring

theorem juliaDefectSquareProfile_neg (y : ℝ) :
    juliaDefectSquareProfile (-y) = juliaDefectSquareProfile y := by
  have harg : Real.tanh (-y / 2) = -Real.tanh (y / 2) := by
    rw [show -y / 2 = -(y / 2) by ring, Real.tanh_neg]
  rw [juliaDefectSquareProfile, juliaDefectSquareProfile, harg,
    juliaDefectQuartic_neg]

theorem juliaDefectAttenuationProfile_neg (y : ℝ) :
    juliaDefectAttenuationProfile (-y) = juliaDefectAttenuationProfile y := by
  simp [juliaDefectAttenuationProfile, juliaDefectSquareProfile_neg]

/-- The canonical spectral extension retains the reflection symmetry of the raw Julia profile. -/
theorem juliaDefectAttenuationKernel_neg (y : ℝ) :
    juliaDefectAttenuationKernel (-y) = juliaDefectAttenuationKernel y := by
  by_cases hy : y = 0
  · subst y
    simp
  · have hny : -y ≠ 0 := neg_ne_zero.mpr hy
    rw [juliaDefectAttenuationKernel_eq_profile hny,
      juliaDefectAttenuationKernel_eq_profile hy,
      juliaDefectAttenuationProfile_neg]

/-- The corrected Julia kernel is strictly positive at every real aperture. -/
theorem juliaDefectAttenuationKernel_pos (y : ℝ) :
    0 < juliaDefectAttenuationKernel y := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · rw [← juliaDefectAttenuationKernel_neg y,
      juliaDefectAttenuationKernel_eq_profile (neg_ne_zero.mpr hy.ne)]
    exact juliaDefectAttenuationProfile_pos (neg_pos.mpr hy)
  · simp
  · rw [juliaDefectAttenuationKernel_eq_profile hy.ne']
    exact juliaDefectAttenuationProfile_pos hy

/-- **Zero-value no-go.**  The raw totalized profile cannot be a positive-definite function on
the additive real line.  The explicit two-point witness uses its zero diagonal and its strictly
positive value at aperture one. -/
theorem not_positiveDefiniteOnReal_juliaDefectAttenuationProfile :
    ¬ GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      (fun y => (juliaDefectAttenuationProfile y : ℂ)) := by
  intro hpd
  obtain ⟨r, hr, hform⟩ := hpd 2 ![0, 1] ![1, -1]
  have hpos : 0 < juliaDefectAttenuationProfile 1 :=
    juliaDefectAttenuationProfile_pos zero_lt_one
  simp only [Fin.sum_univ_two] at hform
  simp [juliaDefectAttenuationProfile_neg] at hform
  have hre := congrArg Complex.re hform
  norm_num at hre
  nlinarith

/-- Positive-half-line Lévy density of the Julia compression square. -/
def juliaCompressionLevyDensity (t : ℝ) : ℝ :=
  1 / (2 * t * Real.sinh (Real.pi * t / 4)) -
    2 / (t * Real.sinh (Real.pi * t))

/-- **Strict Julia Lévy law.**  The exact Lévy density of the compression square is positive at
every positive frequency.  The proof is the scale-four identity
`sinh(4v) = 4 sinh(v) cosh(v) cosh(2v)` and uses no approximation. -/
theorem juliaCompressionLevyDensity_pos {t : ℝ} (ht : 0 < t) :
    0 < juliaCompressionLevyDensity t := by
  let v := Real.pi * t / 4
  have hv : 0 < v := by dsimp only [v]; positivity
  have hsv : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
  have hcv : 1 < Real.cosh v := Real.one_lt_cosh.mpr hv.ne'
  have hc2v : 1 < Real.cosh (2 * v) := Real.one_lt_cosh.mpr (by positivity)
  have hcprod : 1 < Real.cosh v * Real.cosh (2 * v) := by
    nlinarith [mul_pos (sub_pos.mpr hcv) (Real.cosh_pos (2 * v))]
  have hsinh4 : 4 * Real.sinh v < Real.sinh (4 * v) := by
    rw [show 4 * v = 2 * (2 * v) by ring, Real.sinh_two_mul,
      Real.sinh_two_mul]
    nlinarith [mul_pos (mul_pos (by positivity : 0 < 4 * Real.sinh v)
      (sub_pos.mpr hcprod)) (by norm_num : (0 : ℝ) < 1)]
  have hpit : Real.pi * t = 4 * v := by dsimp only [v]; ring
  have hsinhpit : 4 * Real.sinh v < Real.sinh (Real.pi * t) := by
    rwa [hpit]
  have hdenLeft : 0 < t * Real.sinh (Real.pi * t) := by
    exact mul_pos ht (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht))
  have hdenRight : 0 < 2 * t * Real.sinh (Real.pi * t / 4) := by
    rw [show Real.pi * t / 4 = v by rfl]
    positivity
  rw [juliaCompressionLevyDensity, sub_pos]
  rw [div_lt_div_iff₀ hdenLeft hdenRight]
  nlinarith [mul_lt_mul_of_pos_left hsinhpit ht]

/-! ### Scale-four Dirichlet innovation tower -/

/-- Radial density of the critical centered symmetric log-Beta/Dirichlet generator. -/
def criticalDirichletLevyRadialDensity (x : ℝ) : ℝ :=
  1 / (2 * Real.sinh x)

/-- Scale-four innovation left after removing four dilated copies of the critical Dirichlet
generator. -/
def juliaScaleFourInnovationDensity (x : ℝ) : ℝ :=
  criticalDirichletLevyRadialDensity x -
    4 * criticalDirichletLevyRadialDensity (4 * x)

/-- **Exact Dirichlet--Julia scale-four weld.**  After the canonical Fourier rescaling
`x = π t / 4`, the scale-four innovation of the critical log-Beta/Dirichlet generator is exactly
`t` times the Julia compression Lévy density. -/
theorem juliaScaleFourInnovationDensity_eq_rescaledLevy
    {t : ℝ} (ht : 0 < t) :
    juliaScaleFourInnovationDensity (Real.pi * t / 4) =
      t * juliaCompressionLevyDensity t := by
  have hv : 0 < Real.pi * t / 4 := by positivity
  have hpit : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hsv : Real.sinh (Real.pi * t / 4) ≠ 0 :=
    (Real.sinh_pos_iff.mpr hv).ne'
  have hspit : Real.sinh (Real.pi * t) ≠ 0 :=
    (Real.sinh_pos_iff.mpr hpit).ne'
  rw [juliaScaleFourInnovationDensity,
    criticalDirichletLevyRadialDensity,
    criticalDirichletLevyRadialDensity,
    show 4 * (Real.pi * t / 4) = Real.pi * t by ring,
    juliaCompressionLevyDensity]
  field_simp [ht.ne', hsv, hspit]
  all_goals ring

/-- The critical Dirichlet scale-four innovation is strictly positive at every positive radial
frequency.  Thus the Julia equilibrium law is the positive remainder of a genuine strict
fourfold subdivision, not merely a quotient of hyperbolic functions. -/
theorem juliaScaleFourInnovationDensity_pos {x : ℝ} (hx : 0 < x) :
    0 < juliaScaleFourInnovationDensity x := by
  let t := 4 * x / Real.pi
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have harg : Real.pi * t / 4 = x := by
    dsimp only [t]
    field_simp [Real.pi_ne_zero]
  rw [← harg, juliaScaleFourInnovationDensity_eq_rescaledLevy ht]
  exact mul_pos ht (juliaCompressionLevyDensity_pos ht)

/-- Exponential renewal form of the critical Dirichlet radial density. -/
theorem criticalDirichletLevyRadialDensity_eq_exp_neg_div
    {x : ℝ} (hx : 0 < x) :
    criticalDirichletLevyRadialDensity x =
      Real.exp (-x) / (1 - Real.exp (-2 * x)) := by
  have hsinh : Real.sinh x ≠ 0 :=
    (Real.sinh_pos_iff.mpr hx).ne'
  have hdiff : Real.exp x - Real.exp (-x) ≠ 0 := by
    have hspos := Real.sinh_pos_iff.mpr hx
    rw [Real.sinh_eq] at hspos
    linarith
  have hden : 1 - Real.exp (-2 * x) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  have hunit : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsq : Real.exp (-2 * x) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [criticalDirichletLevyRadialDensity, Real.sinh_eq]
  rw [show 2 * ((Real.exp x - Real.exp (-x)) / 2) =
    Real.exp x - Real.exp (-x) by ring]
  rw [hsq]
  have hden' : 1 - Real.exp (-x) * Real.exp (-x) ≠ 0 := by
    rw [← hsq]
    exact hden
  rw [div_eq_div_iff hdiff hden']
  nlinarith

/-- **Finite innovation decomposition.**  Every finite scale-four resolution of the critical
Dirichlet density splits exactly into positive Julia innovations plus one unresolved tail.
This is the algebraic multiscale law underlying the infinite Julia innovation tower. -/
theorem criticalDirichletLevyRadialDensity_scaleFour_telescope
    (x : ℝ) (n : ℕ) :
    criticalDirichletLevyRadialDensity x =
      (∑ j ∈ Finset.range n,
        (4 : ℝ) ^ j * juliaScaleFourInnovationDensity ((4 : ℝ) ^ j * x)) +
      (4 : ℝ) ^ n * criticalDirichletLevyRadialDensity ((4 : ℝ) ^ n * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have harg :
          4 * ((4 : ℝ) ^ n * x) = (4 : ℝ) ^ (n + 1) * x := by
        rw [pow_succ]
        ring
      have hpow : (4 : ℝ) ^ (n + 1) = (4 : ℝ) ^ n * 4 := by
        rw [pow_succ]
      rw [ih, Finset.sum_range_succ, juliaScaleFourInnovationDensity,
        harg, hpow]
      ring

end

end HTGeometry
