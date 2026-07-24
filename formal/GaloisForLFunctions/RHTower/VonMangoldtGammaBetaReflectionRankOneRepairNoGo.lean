import GaloisForLFunctions.RHTower.VonMangoldtGammaFactorialBetaReflection
import GaloisForLFunctions.HTGeometry.EventualNegDefFromEntrywise
import GaloisForLFunctions.HTGeometry.KreinLangerInertia

/-!
# A rank-one boundary channel cannot repair factorial/Beta reflection

The prior factorial/Beta-reflection obstruction exhibits one negative determinant.  That does not
by itself exclude repair by one positive boundary channel.  This file computes the negative index
needed for that exact question.

On Borel orders `0,1,2,3`, scale the cofinal von Mangoldt--Gamma factorial form by `2^(x+1)`.
First-prime dominance gives the limit

`L(i,j) = (log 2)^(i+j+2) / (i+j+1)!`.

Two explicit columns compress `L` to

`(log 2)^2 * diag(-1/12, -1/100800)`.

The corresponding complex two-plane is therefore negative definite for every sufficiently large
source displacement.  The complex Krein--Langer rank bound then proves that adding any one positive
rank-one outer product still cannot make the source matrix positive semidefinite.
-/

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Complexification of the cofinal factorial/Beta-reflected source on Borel orders `0,1,2,3`. -/
def betaFactorialFourComplexGram (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j ↦
    (infiniteVonMangoldtGammaFactorialTraceGram x
      (fun k : Fin 4 ↦ (k : ℕ)) i j : ℂ)

/-- First-prime projective limit of the scaled four-order factorial source matrix. -/
def betaFactorialFourFirstPrimeLimit : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j ↦
    ((Real.log 2) ^ ((i : ℕ) + (j : ℕ) + 2) /
      (((i : ℕ) + (j : ℕ) + 1).factorial : ℝ) : ℂ)

/-- First-prime dominance transferred from the Euler coordinate `x+1` to source displacement
`x`. -/
theorem tendsto_scaled_infiniteVonMangoldtGammaRawMoment (m : ℕ) :
    Tendsto
      (fun x : ℝ ↦
        (2 : ℝ) ^ (x + 1) * infiniteVonMangoldtGammaRawMoment x m)
      atTop (nhds ((Real.log 2) ^ (m + 1))) := by
  have hshift : Tendsto (fun x : ℝ ↦ x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have h := (tendsto_scaled_vonMangoldtLogMoment m).comp hshift
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [infiniteVonMangoldtGammaRawMoment_eq_vonMangoldtLogMoment hx]
  rfl

/-- Entrywise convergence of the scaled four-order factorial source matrix. -/
theorem tendsto_scaled_betaFactorialFourComplexGram_apply (i j : Fin 4) :
    Tendsto
      (fun x : ℝ ↦
        Complex.ofReal ((2 : ℝ) ^ (x + 1)) *
          betaFactorialFourComplexGram x i j)
      atTop (nhds (betaFactorialFourFirstPrimeLimit i j)) := by
  have hreal :=
    (tendsto_scaled_infiniteVonMangoldtGammaRawMoment
      ((i : ℕ) + (j : ℕ) + 1)).div_const
        ((((i : ℕ) + (j : ℕ) + 1).factorial : ℝ))
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  convert hcomplex using 1
  · funext x
    simp only [Function.comp_apply, betaFactorialFourComplexGram,
      infiniteVonMangoldtGammaFactorialTraceGram, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  · simp only [betaFactorialFourFirstPrimeLimit, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_natCast]

/-- Explicit frame for two independent negative directions of the factorial limit. -/
def betaFactorialNegativePlaneFrame : Matrix (Fin 4) (Fin 2) ℂ :=
  let ell : ℝ := Real.log 2
  !![((-1 / 2 : ℝ) : ℂ), ((-1 / 120 : ℝ) : ℂ);
     ((ell⁻¹ : ℝ) : ℂ), (((1 / 10 : ℝ) * ell⁻¹ : ℝ) : ℂ);
     0, (((-1 / 2 : ℝ) * (ell ^ 2)⁻¹ : ℝ) : ℂ);
     0, (((ell ^ 3)⁻¹ : ℝ) : ℂ)]

/-- Compression of the scaled source matrix to the explicit two-column frame. -/
def betaFactorialCompressedScaledGram (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  betaFactorialNegativePlaneFrameᴴ *
    ((Complex.ofReal ((2 : ℝ) ^ (x + 1))) • betaFactorialFourComplexGram x) *
      betaFactorialNegativePlaneFrame

/-- Negative diagonal limit of the compressed source form. -/
def betaFactorialCompressedLimit : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![
    ((-(Real.log 2) ^ 2 / 12 : ℝ) : ℂ),
    ((-(Real.log 2) ^ 2 / 100800 : ℝ) : ℂ)]

/-- Exact factorial chamber calculation: the two frame columns diagonalize the first-prime limit
with two strictly negative pivots. -/
theorem betaFactorialNegativePlaneFrame_compresses_limit :
    betaFactorialNegativePlaneFrameᴴ *
        betaFactorialFourFirstPrimeLimit *
          betaFactorialNegativePlaneFrame =
      betaFactorialCompressedLimit := by
  have hell : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hclog_ne : Complex.log (2 : ℂ) ≠ 0 := by
    have heq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
      (Complex.ofReal_log (by norm_num)).symm
    rw [heq]
    exact Complex.ofReal_ne_zero.mpr hell
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [betaFactorialNegativePlaneFrame,
      betaFactorialFourFirstPrimeLimit, betaFactorialCompressedLimit,
      Matrix.mul_apply, Fin.sum_univ_succ, -Complex.ofNat_log]
  all_goals field_simp [hell, hclog_ne]
  all_goals norm_num [map_ofNat]

set_option maxHeartbeats 800000 in
/-- Entrywise convergence persists after compression to the negative frame. -/
theorem tendsto_betaFactorialCompressedScaledGram_apply (i j : Fin 2) :
    Tendsto (fun x : ℝ ↦ betaFactorialCompressedScaledGram x i j)
      atTop (nhds (betaFactorialCompressedLimit i j)) := by
  rw [← betaFactorialNegativePlaneFrame_compresses_limit]
  simp only [betaFactorialCompressedScaledGram, Matrix.mul_apply,
    Matrix.smul_apply, smul_eq_mul]
  apply tendsto_finsetSum
  intro k hk
  apply Tendsto.mul_const
  apply tendsto_finsetSum
  intro l hl
  exact tendsto_const_nhds.mul
    (tendsto_scaled_betaFactorialFourComplexGram_apply l k)

/-- The compressed actual cofinal source is eventually negative definite. -/
theorem betaFactorialCompressedScaledGram_eventually_negDef :
    ∀ᶠ x : ℝ in atTop, ∀ z : Fin 2 → ℂ, z ≠ 0 →
      (star z ⬝ᵥ (betaFactorialCompressedScaledGram x).mulVec z).re < 0 := by
  let ell : ℝ := Real.log 2
  let c : Fin 2 → ℝ := ![-ell ^ 2 / 12, -ell ^ 2 / 100800]
  have hell : 0 < ell := Real.log_pos (by norm_num)
  apply eventually_negDef_of_entrywise_tendsto_diagonal
    betaFactorialCompressedScaledGram c
    (δ := ell ^ 2 / 100800)
  · positivity
  · intro j
    fin_cases j
    · simp [c]
      nlinarith [sq_pos_of_pos hell]
    · simp [c]
      rw [neg_div]
  · intro ε hε
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hball :=
      (tendsto_betaFactorialCompressedScaledGram_apply i j).eventually
        (Metric.ball_mem_nhds _ hε)
    filter_upwards [hball] with x hx
    have hlt : ‖betaFactorialCompressedScaledGram x i j -
        betaFactorialCompressedLimit i j‖ < ε := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hlimit :
        betaFactorialCompressedLimit i j =
          (Matrix.diagonal fun k => ((c k : ℝ) : ℂ)) i j := by
      fin_cases i <;> fin_cases j <;>
        simp [betaFactorialCompressedLimit, c, ell]
    rw [← hlimit]
    exact le_of_lt hlt

/-- The explicit two-column negative frame is injective. -/
theorem betaFactorialNegativePlaneFrame_mulVec_injective :
    Function.Injective betaFactorialNegativePlaneFrame.mulVec := by
  intro z w h
  have hell : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  norm_num [betaFactorialNegativePlaneFrame, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at h0 h1
  have hclog_ne : Complex.log (2 : ℂ) ≠ 0 := by
    have heq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
      (Complex.ofReal_log (by norm_num)).symm
    rw [heq]
    exact Complex.ofReal_ne_zero.mpr hell
  field_simp [hclog_ne] at h1
  have hz : z 0 = w 0 := by
    linear_combination (-12 / 5 : ℂ) * h0 - (1 / 50 : ℂ) * h1
  have hz1 : z 1 = w 1 := by
    linear_combination h1 - 10 * hz
  funext i
  fin_cases i
  · exact hz
  · exact hz1

/-- The explicit complex two-plane in the four-order source packet. -/
def betaFactorialNegativePlane : Submodule ℂ (Fin 4 → ℂ) :=
  LinearMap.range betaFactorialNegativePlaneFrame.mulVecLin

/-- The negative plane has complex dimension exactly two. -/
theorem finrank_betaFactorialNegativePlane :
    Module.finrank ℂ betaFactorialNegativePlane = 2 := by
  rw [betaFactorialNegativePlane,
    LinearMap.finrank_range_of_inj
      betaFactorialNegativePlaneFrame_mulVec_injective,
    Module.finrank_fin_fun]

/-- The compressed quadratic form is the positive first-prime scale times the original source
quadratic form restricted to the frame. -/
theorem betaFactorialCompressedScaledGram_quadForm (x : ℝ) (z : Fin 2 → ℂ) :
    star z ⬝ᵥ (betaFactorialCompressedScaledGram x).mulVec z =
      Complex.ofReal ((2 : ℝ) ^ (x + 1)) *
        (star (betaFactorialNegativePlaneFrame.mulVec z) ⬝ᵥ
          (betaFactorialFourComplexGram x).mulVec
            (betaFactorialNegativePlaneFrame.mulVec z)) := by
  simp only [betaFactorialCompressedScaledGram, Matrix.mulVec_mulVec,
    Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.mul_assoc]

/-- The actual cofinal factorial/Beta source is eventually negative definite on the fixed complex
two-plane. -/
theorem betaFactorialFourComplexGram_eventually_negDef_on_plane :
    ∀ᶠ x : ℝ in atTop,
      ∀ y ∈ betaFactorialNegativePlane, y ≠ 0 →
        (star y ⬝ᵥ (betaFactorialFourComplexGram x).mulVec y).re < 0 := by
  filter_upwards
    [betaFactorialCompressedScaledGram_eventually_negDef] with x hx
  intro y hy hy0
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
  have hz : z ≠ 0 := by
    intro hz
    apply hy0
    rw [hz]
    exact betaFactorialNegativePlaneFrame.mulVecLin.map_zero
  have hscaled := hx z hz
  rw [betaFactorialCompressedScaledGram_quadForm] at hscaled
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hscaled
  have hscale : 0 < (2 : ℝ) ^ (x + 1) := by positivity
  change
    (star (betaFactorialNegativePlaneFrame.mulVec z) ⬝ᵥ
      (betaFactorialFourComplexGram x).mulVec
      (betaFactorialNegativePlaneFrame.mulVec z)).re < 0
  nlinarith

/-- **Rank-one repair no-go.** For every sufficiently large source displacement, no single
positive rank-one channel can make the cofinal factorial/Beta reflection positive semidefinite. -/
theorem betaFactorialFourComplexGram_eventually_not_posSemidef_add_rankOne :
    ∀ᶠ x : ℝ in atTop, ∀ b : Fin 4 → ℂ,
      ¬ (betaFactorialFourComplexGram x +
        Matrix.of (fun i j => b i * star (b j))).PosSemidef := by
  filter_upwards
    [betaFactorialFourComplexGram_eventually_negDef_on_plane] with x hneg
  intro b hPSD
  let v : Fin 1 → (Fin 4 → ℂ) := fun _ ↦ b
  have hPSD' :
      (betaFactorialFourComplexGram x +
        ∑ i, Matrix.of (fun j k => v i j * star (v i k))).PosSemidef := by
    simpa [v, Fin.sum_univ_one] using hPSD
  have hle := GaloisForLFunctions.neg_inertia_le_of_posSemidef
    (betaFactorialFourComplexGram x) v hPSD'
      betaFactorialNegativePlane hneg
  rw [finrank_betaFactorialNegativePlane] at hle
  omega

end

end RHTower
