import GaloisForLFunctions.RHTower.PolynomialGaussianFourierAperture
import GaloisForLFunctions.RHTower.LargeValues

/-!
# Polynomial--Gaussian local concentration

Route U's C43-Y compact-mass estimate does not require a separate Mehler kernel development.
Finite oscillator energy and the one-dimensional Gallagher--Sobolev inequality already imply the
correct square-root degree law.  After the exact native heat scaling, this file proves

`∫_[-R,R] ‖Q(x²)² exp(-t x²)‖ dx ≤ 18 R sqrt(t(deg Q+1)) M_Q(t)`.

Every theorem is unconditional.  In particular, no coefficient bound, nonzero-polynomial premise,
or RH premise occurs.
-/

open scoped Real SchwartzMap
open Complex Real MeasureTheory Set

noncomputable section

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The full derivative of a degree-`n` polynomial times the self-dual Gaussian has energy at most
`16(n+1)` times its mass.  This deliberately uses a rational constant; the sharper oscillator
constant is unnecessary for the Route-U concentration law. -/
theorem norm_deriv_polyGaussSchwartz_sq_le (P : Polynomial ℝ) :
    ‖(derivSCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) ≤
      16 * (P.natDegree + 1) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
  let f : 𝓢(ℝ, ℂ) := polyGaussSchwartz P
  let B : 𝓢(ℝ, ℂ) := annihilationCLM f
  let A : 𝓢(ℝ, ℂ) := creationCLM f
  have hN := numberCLM_polyGauss_norm_le P
  change ‖(numberCLM f).toLp 2 (volume : Measure ℝ)‖ ≤
    4 * Real.pi * P.natDegree * ‖f.toLp 2 (volume : Measure ℝ)‖ at hN
  have hB0 := norm_toLp_annihilationCLM_sq_le f
  have hB : ‖B.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) ≤
      4 * Real.pi * P.natDegree * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
    change ‖(annihilationCLM f).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) ≤ _
    calc
      ‖(annihilationCLM f).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
          ≤ ‖f.toLp 2 (volume : Measure ℝ)‖ *
              ‖(numberCLM f).toLp 2 (volume : Measure ℝ)‖ := hB0
      _ ≤ ‖f.toLp 2 (volume : Measure ℝ)‖ *
            (4 * Real.pi * P.natDegree * ‖f.toLp 2 (volume : Measure ℝ)‖) :=
        mul_le_mul_of_nonneg_left hN (norm_nonneg _)
      _ = 4 * Real.pi * P.natDegree *
            ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by ring
  have htoLpK :
      (numberCLM f + (4 * (Real.pi : ℂ)) • f).toLp 2 (volume : Measure ℝ) =
        (numberCLM f).toLp 2 (volume : Measure ℝ) +
          (4 * (Real.pi : ℂ)) • f.toLp 2 (volume : Measure ℝ) := by
    change (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))
        (numberCLM f + (4 * (Real.pi : ℂ)) • f) = _
    rw [map_add, map_smul, SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply]
  have hscalar :
      ‖(4 * (Real.pi : ℂ)) • f.toLp 2 (volume : Measure ℝ)‖ =
        4 * Real.pi * ‖f.toLp 2 (volume : Measure ℝ)‖ := by
    rw [norm_smul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hK :
      ‖(numberCLM f + (4 * (Real.pi : ℂ)) • f).toLp 2 (volume : Measure ℝ)‖ ≤
        4 * Real.pi * (P.natDegree + 1) *
          ‖f.toLp 2 (volume : Measure ℝ)‖ := by
    rw [htoLpK]
    calc
      ‖(numberCLM f).toLp 2 (volume : Measure ℝ) +
          (4 * (Real.pi : ℂ)) • f.toLp 2 (volume : Measure ℝ)‖
          ≤ ‖(numberCLM f).toLp 2 (volume : Measure ℝ)‖ +
              ‖(4 * (Real.pi : ℂ)) • f.toLp 2 (volume : Measure ℝ)‖ := norm_add_le _ _
      _ = ‖(numberCLM f).toLp 2 (volume : Measure ℝ)‖ +
            4 * Real.pi * ‖f.toLp 2 (volume : Measure ℝ)‖ := by rw [hscalar]
      _ ≤ 4 * Real.pi * P.natDegree * ‖f.toLp 2 (volume : Measure ℝ)‖ +
            4 * Real.pi * ‖f.toLp 2 (volume : Measure ℝ)‖ := add_le_add hN le_rfl
      _ = 4 * Real.pi * (P.natDegree + 1) *
            ‖f.toLp 2 (volume : Measure ℝ)‖ := by ring
  have hA0 := norm_toLp_creationCLM_sq_le f
  have hA : ‖A.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) ≤
      4 * Real.pi * (P.natDegree + 1) * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
    change ‖(creationCLM f).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) ≤ _
    calc
      ‖(creationCLM f).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
          ≤ ‖f.toLp 2 (volume : Measure ℝ)‖ *
              ‖(numberCLM f + (4 * (Real.pi : ℂ)) • f).toLp 2
                (volume : Measure ℝ)‖ := hA0
      _ ≤ ‖f.toLp 2 (volume : Measure ℝ)‖ *
            (4 * Real.pi * (P.natDegree + 1) *
              ‖f.toLp 2 (volume : Measure ℝ)‖) :=
        mul_le_mul_of_nonneg_left hK (norm_nonneg _)
      _ = 4 * Real.pi * (P.natDegree + 1) *
            ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by ring
  have hsub :
      ‖(B - A).toLp 2 (volume : Measure ℝ)‖ ≤
        ‖B.toLp 2 (volume : Measure ℝ)‖ + ‖A.toLp 2 (volume : Measure ℝ)‖ := by
    rw [toLp_sub]
    exact norm_sub_le _ _
  rw [show derivSCLM f = ((2 : ℂ)⁻¹) • (B - A) by
    simpa only [A, B] using derivSCLM_eq_oscillator f]
  rw [toLp_smul, norm_smul]
  have hinv : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hinv]
  have hsubsq : ‖(B - A).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) ≤
      (‖B.toLp 2 (volume : Measure ℝ)‖ + ‖A.toLp 2 (volume : Measure ℝ)‖) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hsub 2
  have hpi : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
  have hcoef : 2 * Real.pi * (2 * (P.natDegree : ℝ) + 1) ≤
      16 * ((P.natDegree : ℝ) + 1) := by
    calc
      2 * Real.pi * (2 * (P.natDegree : ℝ) + 1)
          ≤ 8 * (2 * (P.natDegree : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hpi (by positivity)
      _ ≤ 16 * ((P.natDegree : ℝ) + 1) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) P.natDegree]
  calc
    (1 / 2 * ‖(B - A).toLp 2 (volume : Measure ℝ)‖) ^ (2 : ℕ)
        ≤ (1 / 2) ^ (2 : ℕ) *
            (‖B.toLp 2 (volume : Measure ℝ)‖ + ‖A.toLp 2 (volume : Measure ℝ)‖) ^ (2 : ℕ) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hsubsq (sq_nonneg _)
    _ ≤ (1 / 2 : ℝ) *
          (‖B.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) +
            ‖A.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)) := by
      nlinarith [sq_nonneg
        (‖B.toLp 2 (volume : Measure ℝ)‖ - ‖A.toLp 2 (volume : Measure ℝ)‖)]
    _ ≤ (1 / 2 : ℝ) *
          (4 * Real.pi * P.natDegree * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) +
            4 * Real.pi * (P.natDegree + 1) *
              ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)) := by gcongr
    _ = 2 * Real.pi * (2 * (P.natDegree : ℝ) + 1) *
          ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by ring
    _ ≤ 16 * ((P.natDegree : ℝ) + 1) *
          ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ = 16 * (P.natDegree + 1) *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
      simp only [f]

/-- A unit interval contains no more squared Schwartz mass than the whole line. -/
private theorem intervalIntegral_norm_sq_le_toLp_sq (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ u in x..x + 1, ‖f u‖ ^ (2 : ℕ)) ≤
      ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
  have hint : Integrable (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp
      (f.memLp 2 (volume : Measure ℝ))
  rw [intervalIntegral.integral_of_le (by linarith : x ≤ x + 1),
    norm_toLp_sq_eq_integral]
  exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-- **Finite-oscillator pointwise anti-concentration.**  A degree-`n` polynomial times the
self-dual Gaussian has squared point value at most `9 sqrt(n+1)` times its total squared mass.
This is the reproducing-kernel estimate needed by C43-Y, obtained without a Mehler expansion. -/
theorem norm_polyGaussSchwartz_sq_le (P : Polynomial ℝ) (x : ℝ) :
    ‖polyGaussSchwartz P x‖ ^ (2 : ℕ) ≤
      9 * Real.sqrt (P.natDegree + 1) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
  let f : 𝓢(ℝ, ℂ) := polyGaussSchwartz P
  let D : 𝓢(ℝ, ℂ) := derivSCLM f
  let s : ℝ := Real.sqrt (P.natDegree + 1)
  let η : ℝ := 1 / (4 * s)
  have hspos : 0 < s := by
    change 0 < Real.sqrt (P.natDegree + 1)
    rw [Real.sqrt_pos]
    positivity
  have hηpos : 0 < η := by
    change 0 < 1 / (4 * s)
    positivity
  have hderiv : ∀ y ∈ Set.Icc x (x + (1 : ℕ) * (1 : ℝ)),
      HasDerivAt (fun z : ℝ => f z) (D y) y := by
    intro y _
    simpa only [D, derivSCLM_apply] using f.hasDerivAt y
  have hg'int : IntervalIntegrable (fun y : ℝ =>
      2 * inner ℝ (f y) (D y)) volume x (x + (1 : ℕ) * (1 : ℝ)) :=
    (by fun_prop : Continuous (fun y : ℝ =>
      2 * inner ℝ (f y) (D y))).intervalIntegrable x _
  have hgint : IntervalIntegrable (fun y : ℝ => ‖f y‖ ^ (2 : ℕ))
      volume x (x + (1 : ℕ) * (1 : ℝ)) :=
    (by fun_prop : Continuous (fun y : ℝ => ‖f y‖ ^ (2 : ℕ))).intervalIntegrable x _
  have hDint : IntervalIntegrable (fun y : ℝ => ‖D y‖ ^ (2 : ℕ))
      volume x (x + (1 : ℕ) * (1 : ℝ)) :=
    (by fun_prop : Continuous (fun y : ℝ => ‖D y‖ ^ (2 : ℕ))).intervalIntegrable x _
  have hcrossint : IntervalIntegrable (fun y : ℝ => 2 * (‖f y‖ * ‖D y‖))
      volume x (x + (1 : ℕ) * (1 : ℝ)) :=
    (by fun_prop : Continuous (fun y : ℝ =>
      2 * (‖f y‖ * ‖D y‖))).intervalIntegrable x _
  have hlarge := large_values_count (A := x) (δ := (1 : ℝ)) (V := ‖f x‖) (η := η)
    (by norm_num) hηpos (norm_nonneg _) 1 hderiv hg'int hgint hDint hcrossint
    (by
      intro r hr
      have hr0 : r = 0 := by omega
      subst r
      simp)
  have hlarge' :
      ‖f x‖ ^ (2 : ℕ) ≤
        (1 + 1 / η) * (∫ u in x..x + 1, ‖f u‖ ^ (2 : ℕ)) +
          η * (∫ u in x..x + 1, ‖D u‖ ^ (2 : ℕ)) := by
    simpa using hlarge
  have hfLocal := intervalIntegral_norm_sq_le_toLp_sq f x
  have hDLocal := intervalIntegral_norm_sq_le_toLp_sq D x
  have henergy : ‖D.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) ≤
      16 * (P.natDegree + 1) * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
    simpa only [D, f] using norm_deriv_polyGaussSchwartz_sq_le P
  have hs_sq : s ^ (2 : ℕ) = (P.natDegree : ℝ) + 1 := by
    change Real.sqrt (P.natDegree + 1) ^ (2 : ℕ) = _
    rw [Real.sq_sqrt]
    positivity
  have hη : η = 1 / (4 * s) := rfl
  have hsone : 1 ≤ s := by
    apply (sq_le_sq₀ zero_le_one hspos.le).mp
    rw [one_pow, hs_sq]
    have hn : (0 : ℝ) ≤ P.natDegree := by positivity
    linarith
  calc
    ‖f x‖ ^ (2 : ℕ)
        ≤ (1 + 1 / η) * (∫ u in x..x + 1, ‖f u‖ ^ (2 : ℕ)) +
            η * (∫ u in x..x + 1, ‖D u‖ ^ (2 : ℕ)) := hlarge'
    _ ≤ (1 + 1 / η) * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) +
          η * ‖D.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by gcongr
    _ ≤ (1 + 1 / η) * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) +
          η * (16 * (P.natDegree + 1) *
            ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)) := by gcongr
    _ = (1 + 8 * s) * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
      rw [hη]
      field_simp
      rw [← hs_sq]
      ring
    _ ≤ 9 * s * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
      gcongr
      linarith
    _ = 9 * Real.sqrt (P.natDegree + 1) *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
      simp only [s, f]

theorem norm_polynomialGaussianEnergy_eq_norm_polyGauss_sq
    (P : Polynomial ℝ) (x : ℝ) :
    ‖polynomialGaussianEnergy P x‖ = ‖polyGaussSchwartz P x‖ ^ (2 : ℕ) := by
  rw [polynomialGaussianEnergy_apply, polyGaussSchwartz_apply]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (gaussReal_pos x), gaussReal]
  rw [mul_pow, sq_abs, ← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- Compact mass bound in the self-dual Gaussian normalization. -/
theorem integral_Icc_norm_polynomialGaussianEnergy_le
    (P : Polynomial ℝ) (R : {R : ℝ // 0 ≤ R}) :
    (∫ x in Icc (-(R : ℝ)) (R : ℝ), ‖polynomialGaussianEnergy P x‖) ≤
      18 * (R : ℝ) * Real.sqrt (P.natDegree + 1) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
  have hint : Integrable (fun x : ℝ => ‖polynomialGaussianEnergy P x‖)
      (volume : Measure ℝ) := by
    have hsq : Integrable (fun x : ℝ => ‖polyGaussSchwartz P x‖ ^ (2 : ℕ))
        (volume : Measure ℝ) :=
      (memLp_two_iff_integrable_sq_norm
        (polyGaussSchwartz P).continuous.aestronglyMeasurable).mp
        ((polyGaussSchwartz P).memLp 2 (volume : Measure ℝ))
    exact hsq.congr (Filter.Eventually.of_forall fun x =>
      (norm_polynomialGaussianEnergy_eq_norm_polyGauss_sq P x).symm)
  have hconst : IntegrableOn
      (fun _ : ℝ => 9 * Real.sqrt (P.natDegree + 1) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ))
      (Icc (-(R : ℝ)) (R : ℝ)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hmono := setIntegral_mono_on hint.integrableOn hconst measurableSet_Icc
    (fun x _ => by
      rw [norm_polynomialGaussianEnergy_eq_norm_polyGauss_sq]
      exact norm_polyGaussSchwartz_sq_le P x)
  calc
    (∫ x in Icc (-(R : ℝ)) (R : ℝ), ‖polynomialGaussianEnergy P x‖)
        ≤ ∫ _x in Icc (-(R : ℝ)) (R : ℝ),
            (9 * Real.sqrt (P.natDegree + 1) *
              ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) : ℝ) := hmono
    _ = 18 * (R : ℝ) * Real.sqrt (P.natDegree + 1) *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
      rw [MeasureTheory.setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith [R.property])]
      simp only [smul_eq_mul]
      ring

/-- **Route-U polynomial--Gaussian local concentration (PGLC.1 / C43-Y (24.135)).**

The exact native density has at most `18 R sqrt(t(deg Q+1))` times its total mass inside
`[-R,R]`. Heat positivity and radius nonnegativity are encoded in their types; the statement
remains valid for the zero polynomial. -/
theorem integral_Icc_norm_routeUPolynomialGaussianDensity_le
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (R : {R : ℝ // 0 ≤ R}) :
    (∫ x in Icc (-(R : ℝ)) (R : ℝ), ‖routeUPolynomialGaussianDensity Q t x‖) ≤
      18 * (R : ℝ) * Real.sqrt ((t : ℝ) * (Q.natDegree + 1)) *
        routeUPolynomialGaussianMass Q t := by
  let δ : ℝ := Real.sqrt (2 * Real.pi / (t : ℝ))
  let P : Polynomial ℝ := routeURescaledEvenPolynomial Q t
  let M : ℝ := ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
  have hδpos : 0 < δ := Real.sqrt_pos.2 (div_pos (by positivity) t.property)
  have hδsq : δ ^ (2 : ℕ) = 2 * Real.pi / (t : ℝ) := by
    change Real.sqrt (2 * Real.pi / (t : ℝ)) ^ (2 : ℕ) = _
    rw [Real.sq_sqrt]
    exact (div_pos (by positivity) t.property).le
  have hdegree : P.natDegree = 2 * Q.natDegree :=
    natDegree_routeURescaledEvenPolynomial Q t
  have hpoint (x : ℝ) :
      ‖routeUPolynomialGaussianDensity Q t x‖ ≤
        9 * Real.sqrt (2 * Q.natDegree + 1) * M := by
    rw [routeUPolynomialGaussianDensity_eq_dilate]
    change ‖polynomialGaussianEnergy P (x / δ)‖ ≤ _
    rw [norm_polynomialGaussianEnergy_eq_norm_polyGauss_sq]
    have h := norm_polyGaussSchwartz_sq_le P (x / δ)
    rw [hdegree] at h
    have hcast : ((2 * Q.natDegree : ℕ) : ℝ) + 1 =
        2 * (Q.natDegree : ℝ) + 1 := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [hcast] at h
    simpa only [M] using h
  have hconst : IntegrableOn
      (fun _ : ℝ => 9 * Real.sqrt (2 * Q.natDegree + 1) * M)
      (Icc (-(R : ℝ)) (R : ℝ)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hdensityMeas : AEStronglyMeasurable
      (fun x : ℝ => ‖routeUPolynomialGaussianDensity Q t x‖)
      ((volume : Measure ℝ).restrict (Icc (-(R : ℝ)) (R : ℝ))) := by
    apply Continuous.aestronglyMeasurable
    unfold routeUPolynomialGaussianDensity evenSquarePolynomial
    fun_prop
  have hdensityInt : IntegrableOn
      (fun x : ℝ => ‖routeUPolynomialGaussianDensity Q t x‖)
      (Icc (-(R : ℝ)) (R : ℝ)) := by
    refine hconst.mono' hdensityMeas ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hpoint x
  have hmono := setIntegral_mono_on hdensityInt hconst measurableSet_Icc
    (fun x _ => hpoint x)
  have hlocal :
      (∫ x in Icc (-(R : ℝ)) (R : ℝ), ‖routeUPolynomialGaussianDensity Q t x‖) ≤
        18 * (R : ℝ) * Real.sqrt (2 * Q.natDegree + 1) * M := by
    calc
      (∫ x in Icc (-(R : ℝ)) (R : ℝ), ‖routeUPolynomialGaussianDensity Q t x‖)
          ≤ ∫ _x in Icc (-(R : ℝ)) (R : ℝ),
              (9 * Real.sqrt (2 * Q.natDegree + 1) * M : ℝ) := hmono
      _ = 18 * (R : ℝ) * Real.sqrt (2 * Q.natDegree + 1) * M := by
        rw [MeasureTheory.setIntegral_const,
          Real.volume_real_Icc_of_le (by linarith [R.property])]
        simp only [smul_eq_mul]
        ring
  have hscale : Real.sqrt (2 * Q.natDegree + 1) ≤
      Real.sqrt ((t : ℝ) * (Q.natDegree + 1)) * δ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hδpos.le)).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * (Q.natDegree : ℝ) + 1), mul_pow,
      Real.sq_sqrt (mul_nonneg t.property.le (by positivity)), hδsq]
    have hrhs :
        ((t : ℝ) * ((Q.natDegree : ℝ) + 1)) *
            (2 * Real.pi / (t : ℝ)) =
          2 * Real.pi * ((Q.natDegree : ℝ) + 1) := by
      field_simp [t.property.ne']
    rw [hrhs]
    have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc
      2 * (Q.natDegree : ℝ) + 1 ≤ 2 * ((Q.natDegree : ℝ) + 1) := by
        linarith
      _ ≤ 2 * Real.pi * ((Q.natDegree : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [routeUPolynomialGaussianMass_eq]
  change (∫ x in Icc (-(R : ℝ)) (R : ℝ), ‖routeUPolynomialGaussianDensity Q t x‖) ≤
    18 * (R : ℝ) * Real.sqrt ((t : ℝ) * (Q.natDegree + 1)) * (δ * M)
  calc
    (∫ x in Icc (-(R : ℝ)) (R : ℝ), ‖routeUPolynomialGaussianDensity Q t x‖)
        ≤ 18 * (R : ℝ) * Real.sqrt (2 * Q.natDegree + 1) * M := hlocal
    _ ≤ 18 * (R : ℝ) * (Real.sqrt ((t : ℝ) * (Q.natDegree + 1)) * δ) * M := by
      gcongr
      exact mul_nonneg (by norm_num) R.property
    _ = 18 * (R : ℝ) * Real.sqrt ((t : ℝ) * (Q.natDegree + 1)) * (δ * M) := by ring

end RHTower
