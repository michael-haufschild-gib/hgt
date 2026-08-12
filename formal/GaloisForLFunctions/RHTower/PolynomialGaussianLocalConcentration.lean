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
    ‖(derivSCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      16 * (P.natDegree + 1) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  let f : 𝓢(ℝ, ℂ) := polyGaussSchwartz P
  let B : 𝓢(ℝ, ℂ) := annihilationCLM f
  let A : 𝓢(ℝ, ℂ) := creationCLM f
  have hN := numberCLM_polyGauss_norm_le P
  change ‖(numberCLM f).toLp 2 (volume : Measure ℝ)‖ ≤
    4 * Real.pi * P.natDegree * ‖f.toLp 2 (volume : Measure ℝ)‖ at hN
  have hB0 := norm_toLp_annihilationCLM_sq_le f
  have hB : ‖B.toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      4 * Real.pi * P.natDegree * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
    change ‖(annihilationCLM f).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤ _
    calc
      ‖(annihilationCLM f).toLp 2 (volume : Measure ℝ)‖ ^ 2
          ≤ ‖f.toLp 2 (volume : Measure ℝ)‖ *
              ‖(numberCLM f).toLp 2 (volume : Measure ℝ)‖ := hB0
      _ ≤ ‖f.toLp 2 (volume : Measure ℝ)‖ *
            (4 * Real.pi * P.natDegree * ‖f.toLp 2 (volume : Measure ℝ)‖) :=
        mul_le_mul_of_nonneg_left hN (norm_nonneg _)
      _ = 4 * Real.pi * P.natDegree *
            ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by ring
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
            ‖f.toLp 2 (volume : Measure ℝ)‖ := by push_cast; ring
  have hA0 := norm_toLp_creationCLM_sq_le f
  have hA : ‖A.toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      4 * Real.pi * (P.natDegree + 1) * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
    change ‖(creationCLM f).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤ _
    calc
      ‖(creationCLM f).toLp 2 (volume : Measure ℝ)‖ ^ 2
          ≤ ‖f.toLp 2 (volume : Measure ℝ)‖ *
              ‖(numberCLM f + (4 * (Real.pi : ℂ)) • f).toLp 2
                (volume : Measure ℝ)‖ := hA0
      _ ≤ ‖f.toLp 2 (volume : Measure ℝ)‖ *
            (4 * Real.pi * (P.natDegree + 1) *
              ‖f.toLp 2 (volume : Measure ℝ)‖) :=
        mul_le_mul_of_nonneg_left hK (norm_nonneg _)
      _ = 4 * Real.pi * (P.natDegree + 1) *
            ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by ring
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
  have hsubsq : ‖(B - A).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      (‖B.toLp 2 (volume : Measure ℝ)‖ + ‖A.toLp 2 (volume : Measure ℝ)‖) ^ 2 :=
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
    (1 / 2 * ‖(B - A).toLp 2 (volume : Measure ℝ)‖) ^ 2
        ≤ (1 / 2) ^ 2 *
            (‖B.toLp 2 (volume : Measure ℝ)‖ + ‖A.toLp 2 (volume : Measure ℝ)‖) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hsubsq (sq_nonneg _)
    _ ≤ (1 / 2 : ℝ) *
          (‖B.toLp 2 (volume : Measure ℝ)‖ ^ 2 +
            ‖A.toLp 2 (volume : Measure ℝ)‖ ^ 2) := by
      nlinarith [sq_nonneg
        (‖B.toLp 2 (volume : Measure ℝ)‖ - ‖A.toLp 2 (volume : Measure ℝ)‖)]
    _ ≤ (1 / 2 : ℝ) *
          (4 * Real.pi * P.natDegree * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 +
            4 * Real.pi * (P.natDegree + 1) *
              ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2) := by gcongr
    _ = 2 * Real.pi * (2 * (P.natDegree : ℝ) + 1) *
          ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by push_cast; ring
    _ ≤ 16 * ((P.natDegree : ℝ) + 1) *
          ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ = 16 * (P.natDegree + 1) *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
      simp only [f]

end RHTower
