import GaloisForLFunctions.RHTower.CHMDLightConePrimeKernelDecomposition
import GaloisForLFunctions.HTGeometry.SechComplexFourierTransform

/-!
# The half-time secant factor: the two-point sum packet as a single spectral square

The two-point sum packet `φ_Λ(0) + φ_Λ(y)` of the causal wave is, up to the factor `2`, the even
Weil functional of one spectral square: with the half-time secant factor

`Ψ_{y/2}(z) = cos((y/2) ρ(z)) sech(z/2)`,  `ρ(z) = √(z² + 2)`,

the identity `cos²(w) = (1 + cos 2w)/2` gives `Ψ_{y/2} Ψ_{y/2}^# = ½(sech² + cos(yρ) sech²)` on
the strip `|Im z| < √2`, hence

`(φ_Λ(0) + φ_Λ(y))/2 = L_Λ(Ψ_{y/2} Ψ_{y/2}^#) = A(g_{y/2}) − T_Λ(g_{y/2} ⋆ g̃_{y/2})`,

the archimedean-plus-pole energy minus the prime pairing of the autocorrelation of the single real
even test `g_{y/2} = stripTest Ψ_{y/2}` (the inverse Fourier transform of `Ψ_{y/2}` on the line).
At the polar anti-nodes `y_k = (2k+1)π/√(7/4)` the factor vanishes at the pole points `±i/2`, so
`g_{y_k/2}` is an even pole-free test and the two-point sum is a pure archimedean-minus-prime
energy.  Under the Riemann hypothesis all these energies are nonnegative (two-point sum criterion);
no positivity is asserted here.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real ComplexConjugate

noncomputable section

namespace RHTower.CHMDHalfTime

open WeilOneSided WeilSpectral RHTower.EvenSector RHTower.CHMDStage11 RHTower.CHMDStage22
open RHTower.CHMDGrowthCollapse RHTower.CHMDStage3

/-! ## Section 1: the half-time secant factor is an even strip function -/

/-- The half-time secant factor `Ψ_{y/2}(z) = cos((y/2) ρ(z)) sech(z/2)`. -/
def halfTimeSecant (y : ℝ) (z : ℂ) : ℂ :=
  Complex.cos (((y / 2 : ℝ) : ℂ) * rhoC z) * sechHalf z

theorem evenStrip_halfTimeSecant (y : ℝ) : EvenStrip (halfTimeSecant y) := by
  obtain ⟨ε, C, hε, hs⟩ := evenStrip_sechHalf.strip
  refine ⟨⟨ε, Real.exp (|y / 2| * (5 / 4)) * C, hε, fun z hz => ?_, fun z hz => ?_⟩,
    fun z => ?_, fun r => ?_⟩
  · exact ((differentiableAt_rhoC (abs_im_lt_sqrt_two hz)).const_mul _).ccos.mul (hs.diff z hz)
  · unfold halfTimeSecant
    rw [norm_mul]
    have h1 : ‖Complex.cos (((y / 2 : ℝ) : ℂ) * rhoC z)‖ ≤ Real.exp (|y / 2| * (5 / 4)) :=
      (norm_cos_mul_rhoC_le (y / 2)).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hz (abs_nonneg _)))
    calc ‖Complex.cos (((y / 2 : ℝ) : ℂ) * rhoC z)‖ * ‖sechHalf z‖
        ≤ Real.exp (|y / 2| * (5 / 4)) * (C * Real.exp (-(ε * |z.re|))) :=
          mul_le_mul h1 (hs.bound z hz) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · unfold halfTimeSecant
    rw [rhoC_neg, evenStrip_sechHalf.even]
  · unfold halfTimeSecant
    rw [Complex.mul_im, cos_mul_rhoC_ofReal_im, evenStrip_sechHalf.real]
    ring

/-! ## Section 2: the single-square identity -/

/-- **Half-time factorization**: on `|Im z| < √2`,
`Ψ_{y/2} Ψ_{y/2}^# = ½ (sech sech^# + cos(y ρ) sech sech^#)`. -/
theorem specSq_halfTimeSecant (y : ℝ) {z : ℂ} (hz : |z.im| < Real.sqrt 2) :
    specSq (halfTimeSecant y) z =
      (1 / 2 : ℂ) * (specSq sechHalf z + rhoCosShift y sechHalf z) := by
  have hc := (conj_trig_rhoC_conj (y / 2) hz).1
  unfold specSq halfTimeSecant rhoCosShift specSq
  rw [map_mul, hc]
  have h2 : Complex.cos (((y / 2 : ℝ) : ℂ) * rhoC z) ^ 2 =
      1 / 2 + Complex.cos ((y : ℂ) * rhoC z) / 2 := by
    rw [Complex.cos_sq]
    congr 2
    push_cast
    ring_nf
  linear_combination (sechHalf z * conj (sechHalf (conj z))) * h2

theorem abs_im_I_div_two_lt : |(I / 2 : ℂ).im| < Real.sqrt 2 :=
  abs_im_lt_sqrt_two (by simp; norm_num)

theorem abs_im_neg_I_div_two_lt : |(-I / 2 : ℂ).im| < Real.sqrt 2 :=
  abs_im_lt_sqrt_two (by simp [abs_div]; norm_num)

/-! ## Section 3: the two-point sum is the even Weil functional of the single square -/

/-- The growth bound on the von Mangoldt weights used by the even sector. -/
theorem vonMangoldt_growth :
    ∀ n : ℕ, 2 ≤ n → |(ArithmeticFunction.vonMangoldt n : ℝ)| ≤
      1 * Real.sqrt n * (1 + Real.log n) :=
  fun n hn => abs_vonMangoldt_le_sqrt_mul_one_add_log n hn

theorem chmdWave_zero_eq : chmdWave 0 =
    evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq sechHalf) := by
  unfold chmdWave cosineShiftFn
  congr 1
  funext z
  unfold rhoCosShift
  simp

/-- The even Weil functional of `½(K₁ + K₂)` is the half-sum of the functionals. -/
theorem evenWeilDensity_half_add {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {K₁ K₂ : ℂ → ℂ}
    (h₁ : GoodDensity K₁) (h₂ : GoodDensity K₂) :
    evenWeilDensity lam (fun z => (1 / 2 : ℂ) * (K₁ z + K₂ z)) =
      (evenWeilDensity lam K₁ + evenWeilDensity lam K₂) / 2 := by
  have h := evenWeilDensity_sum hg (Finset.univ : Finset (Fin 2)) (fun _ => (1 / 2 : ℝ))
    (K := ![K₁, K₂]) (fun i _ => by fin_cases i <;> simpa)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  rw [show (fun z => (1 / 2 : ℂ) * (K₁ z + K₂ z)) =
    fun z => (1 / 2 : ℂ) * K₁ z + (1 / 2 : ℂ) * K₂ z from funext fun z => by ring]
  rw [h]
  ring

/-- **The two-point sum packet is the functional of one spectral square**:
`(φ_Λ(0) + φ_Λ(y))/2 = L_Λ(Ψ_{y/2} Ψ_{y/2}^#)`. -/
theorem half_two_point_sum_eq_evenWeilDensity_halfTimeSecant (y : ℝ) :
    (chmdWave 0 + chmdWave y) / 2 =
      evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (specSq (halfTimeSecant y)) := by
  have hcongr := evenWeilDensity_congr (lam := fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (K₁ := specSq (halfTimeSecant y))
    (K₂ := fun z => (1 / 2 : ℂ) * (specSq sechHalf z + rhoCosShift y sechHalf z))
    (specSq_halfTimeSecant y abs_im_I_div_two_lt)
    (specSq_halfTimeSecant y abs_im_neg_I_div_two_lt)
    (fun r => specSq_halfTimeSecant y (abs_im_lt_sqrt_two (by simp; norm_num)))
  rw [hcongr, evenWeilDensity_half_add vonMangoldt_growth (goodDensity_specSq evenStrip_sechHalf)
    (goodDensity_cosShift y evenStrip_sechHalf), chmdWave_zero_eq]
  rfl

/-- **Weil-form reading**: the half two-point sum is the archimedean-plus-pole energy of the real
even test `g_{y/2} = stripTest Ψ_{y/2}` minus the prime pairing of its autocorrelation. -/
theorem half_two_point_sum_eq_archPoleEnergy_sub_atomPairing (y : ℝ) :
    (chmdWave 0 + chmdWave y) / 2 =
      archPoleEnergy (stripTest (halfTimeSecant y)) -
        atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (crossCorr (stripTest (halfTimeSecant y)) (stripTest (halfTimeSecant y))) := by
  rw [half_two_point_sum_eq_evenWeilDensity_halfTimeSecant]
  obtain ⟨ε, C, hε, hs⟩ := (evenStrip_halfTimeSecant y).strip
  exact evenWeilDensity_specSq (by norm_num : (1 / 2 : ℝ) < 5 / 4) hε hs
    (evenStrip_halfTimeSecant y).sym

/-- The spatial test `g_{y/2}` is real, even, and its Fourier transform is `Ψ_{y/2}` on the strip. -/
theorem paperFT_stripTest_halfTimeSecant (y : ℝ) {z : ℂ} (hz : |z.im| < 5 / 4) :
    paperFT (fun u => (stripTest (halfTimeSecant y) u : ℂ)) z = halfTimeSecant y z := by
  obtain ⟨ε, C, hε, hs⟩ := (evenStrip_halfTimeSecant y).strip
  exact paperFT_stripTest (by norm_num) hε hs (evenStrip_halfTimeSecant y).sym hz

theorem stripTest_halfTimeSecant_neg (y x : ℝ) :
    stripTest (halfTimeSecant y) (-x) = stripTest (halfTimeSecant y) x :=
  stripTest_neg (evenStrip_halfTimeSecant y).even x

/-! ## Section 4: the polar anti-nodes give even pole-free tests -/

/-- The polar anti-nodes `y_k = (2k+1)π/√(7/4)`, the zeros of the pole wave's cosine. -/
def polarAntiNode (k : ℕ) : ℝ := (2 * k + 1) * π / Real.sqrt (7 / 4)

/-- The half-time secant factor at the upper pole point. -/
theorem halfTimeSecant_I_div_two (y : ℝ) :
    halfTimeSecant y (I / 2) =
      ((Real.cos (y / 2 * Real.sqrt (7 / 4)) * (Real.cos (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) := by
  unfold halfTimeSecant
  rw [rhoC_I_div_two, sechHalf_I_div_two, ← Complex.ofReal_mul, ← Complex.ofReal_cos,
    ← Complex.ofReal_mul]

theorem halfTimeSecant_neg_I_div_two (y : ℝ) :
    halfTimeSecant y (-I / 2) =
      ((Real.cos (y / 2 * Real.sqrt (7 / 4)) * (Real.cos (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) := by
  rw [show (-I / 2 : ℂ) = -(I / 2) by ring, (evenStrip_halfTimeSecant y).even,
    halfTimeSecant_I_div_two]

theorem cos_polarAntiNode (k : ℕ) :
    Real.cos (polarAntiNode k / 2 * Real.sqrt (7 / 4)) = 0 := by
  have hs : Real.sqrt (7 / 4) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [Real.cos_eq_zero_iff]
  refine ⟨k, ?_⟩
  unfold polarAntiNode
  push_cast
  field_simp

/-- **Pole-freeness at the anti-nodes**: `Ψ_{y_k/2}(±i/2) = 0`. -/
theorem halfTimeSecant_polarAntiNode_I_div_two (k : ℕ) :
    halfTimeSecant (polarAntiNode k) (I / 2) = 0 := by
  rw [halfTimeSecant_I_div_two, cos_polarAntiNode, zero_mul, Complex.ofReal_zero]

theorem halfTimeSecant_polarAntiNode_neg_I_div_two (k : ℕ) :
    halfTimeSecant (polarAntiNode k) (-I / 2) = 0 := by
  rw [halfTimeSecant_neg_I_div_two, cos_polarAntiNode, zero_mul, Complex.ofReal_zero]

/-- The test `g_{y_k/2}` is pole-free: its Fourier transform vanishes at `±i/2`. -/
theorem paperFT_stripTest_polarAntiNode_I_div_two (k : ℕ) :
    paperFT (fun u => (stripTest (halfTimeSecant (polarAntiNode k)) u : ℂ)) (I / 2) = 0 := by
  rw [paperFT_stripTest_halfTimeSecant _ (by simp; norm_num)]
  exact halfTimeSecant_polarAntiNode_I_div_two k

theorem paperFT_stripTest_polarAntiNode_neg_I_div_two (k : ℕ) :
    paperFT (fun u => (stripTest (halfTimeSecant (polarAntiNode k)) u : ℂ)) (-I / 2) = 0 := by
  rw [paperFT_stripTest_halfTimeSecant _ (by simp [abs_div]; norm_num)]
  exact halfTimeSecant_polarAntiNode_neg_I_div_two k

/-- The pole part of the single square vanishes at the anti-nodes. -/
theorem evenPolePart_specSq_halfTimeSecant_polarAntiNode (k : ℕ) :
    evenPolePart (specSq (halfTimeSecant (polarAntiNode k))) = 0 := by
  unfold evenPolePart specSq
  have c1 : conj (I / 2 : ℂ) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have c2 : conj (-I / 2 : ℂ) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [c1, c2, halfTimeSecant_polarAntiNode_I_div_two, halfTimeSecant_polarAntiNode_neg_I_div_two]
  simp

/-- **At the polar anti-nodes the two-point sum is a pure archimedean-minus-prime energy**:
`(φ_Λ(0) + φ_Λ(y_k))/2 = (1/2π) ∫ |Ψ_{y_k/2}(r)|² γ(r) dr − Σ_n (Λ(n)/√n)(1/π)∫ |Ψ_{y_k/2}(r)|² cos(r log n) dr`,
with no pole term. -/
theorem half_two_point_sum_polarAntiNode_eq_arch_sub_prime (k : ℕ) :
    (chmdWave 0 + chmdWave (polarAntiNode k)) / 2 =
      1 / (2 * π) * evenArchPart (specSq (halfTimeSecant (polarAntiNode k))) -
        evenPrimePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (specSq (halfTimeSecant (polarAntiNode k))) := by
  rw [half_two_point_sum_eq_evenWeilDensity_halfTimeSecant, evenWeilDensity_eq_parts,
    evenPolePart_specSq_halfTimeSecant_polarAntiNode, zero_add]

/-- **Under the Riemann hypothesis the anti-node energies are nonnegative**: for every `k`,
`0 ≤ (1/2π) ∫ |Ψ_{y_k/2}|² γ − Σ_n (Λ(n)/√n)(1/π)∫ |Ψ_{y_k/2}|² cos(r log n)`, an even pole-free
Weil positivity with no pole help. -/
theorem polarAntiNode_energy_nonneg_of_rh (hRH : RiemannHypothesis) (k : ℕ) :
    0 ≤ 1 / (2 * π) * evenArchPart (specSq (halfTimeSecant (polarAntiNode k))) -
      evenPrimePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (specSq (halfTimeSecant (polarAntiNode k))) := by
  rw [← half_two_point_sum_polarAntiNode_eq_arch_sub_prime]
  have h := riemannHypothesis_iff_forall_neg_zero_value_le_chmdWave.mp hRH (polarAntiNode k)
  linarith

/-- **The two-point sum criterion restricted to the single-square form**: RH iff the even Weil
functional of every half-time square `Ψ_{y/2} Ψ_{y/2}^#` is nonnegative. -/
theorem riemannHypothesis_iff_forall_evenWeilDensity_specSq_halfTimeSecant_nonneg :
    RiemannHypothesis ↔ ∀ y : ℝ, 0 ≤ evenWeilDensity
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq (halfTimeSecant y)) := by
  rw [riemannHypothesis_iff_forall_neg_zero_value_le_chmdWave]
  constructor
  · intro h y
    rw [← half_two_point_sum_eq_evenWeilDensity_halfTimeSecant]
    linarith [h y]
  · intro h y
    have := h y
    rw [← half_two_point_sum_eq_evenWeilDensity_halfTimeSecant] at this
    linarith


/-! ## Section 5: the light-cone transmutation of the half-time test from `sech(πx)` -/

open GaloisForLFunctions.HTGeometry RHTower.CHMDLightCone

/-- The initial profile `g₀(x) = sech(πx)`, the inverse Fourier transform of `sech(r/2)`. -/
def sechPiProfile (x : ℝ) : ℝ := (Real.cosh (π * x))⁻¹

theorem sechPiProfile_pos (x : ℝ) : 0 < sechPiProfile x := inv_pos.mpr (Real.cosh_pos _)

theorem sechPiProfile_neg (x : ℝ) : sechPiProfile (-x) = sechPiProfile x := by
  unfold sechPiProfile
  rw [mul_neg, Real.cosh_neg]

theorem continuous_inv_cosh_half : Continuous fun r : ℝ => (Real.cosh (r / 2))⁻¹ :=
  (by fun_prop : Continuous fun r : ℝ => Real.cosh (r / 2)).inv₀ fun r => (Real.cosh_pos _).ne'

/-- `sech(r/2)` is integrable on the line. -/
theorem integrable_inv_cosh_half : Integrable fun r : ℝ => (Real.cosh (r / 2))⁻¹ := by
  have h := (_root_.HTGeometry.integrable_cosh_rpow_neg one_pos).comp_mul_left'
    (R := (1 / 2 : ℝ)) (by norm_num)
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp only
  rw [Real.rpow_neg (Real.cosh_pos _).le, Real.rpow_one, show (1 / 2 : ℝ) * r = r / 2 by ring]

theorem integrable_inv_cosh_half_mul_cos (x : ℝ) :
    Integrable fun r : ℝ => (Real.cosh (r / 2))⁻¹ * Real.cos (r * x) := by
  refine integrable_inv_cosh_half.mono' (continuous_inv_cosh_half.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have hc : 0 < (Real.cosh (r / 2))⁻¹ := inv_pos.mpr (Real.cosh_pos _)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos hc]
  exact mul_le_of_le_one_right hc.le (Real.abs_cos_le_one _)

theorem integrable_ofReal_inv_cosh_half_mul_cexp (x : ℝ) :
    Integrable fun r : ℝ =>
      (((Real.cosh (r / 2))⁻¹ : ℝ) : ℂ) * Complex.exp (((x * r : ℝ) : ℂ) * I) := by
  refine integrable_inv_cosh_half.norm.mono'
    ((Complex.continuous_ofReal.comp continuous_inv_cosh_half).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The sech Fourier pair**: `∫ sech(r/2) cos(rx) dr = 2π sech(πx)`. -/
theorem integral_inv_cosh_half_mul_cos (x : ℝ) :
    ∫ r : ℝ, (Real.cosh (r / 2))⁻¹ * Real.cos (r * x) = 2 * π * sechPiProfile x := by
  have hz : |(((-2 * x : ℝ)) : ℂ).im| < 1 := by simp
  have h := integral_cexp_div_cosh hz
  have hcosh : Complex.cosh ((Real.pi : ℂ) * (((-2 * x : ℝ)) : ℂ) / 2) =
      ((Real.cosh (π * x) : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) * (((-2 * x : ℝ)) : ℂ) / 2 = -((π * x : ℝ) : ℂ) by push_cast; ring,
      Complex.cosh_neg, Complex.ofReal_cosh]
  rw [hcosh] at h
  have hsub := MeasureTheory.Measure.integral_comp_div
    (fun t : ℝ => Complex.exp (-((((-2 * x : ℝ)) : ℂ) * (t : ℂ)) * I) / (Real.cosh t : ℂ)) 2
  beta_reduce at hsub
  rw [h, abs_two] at hsub
  have hre := integral_re (integrable_ofReal_inv_cosh_half_mul_cexp x)
  simp only [RCLike.re_to_complex] at hre
  calc ∫ r : ℝ, (Real.cosh (r / 2))⁻¹ * Real.cos (r * x)
      = ∫ r : ℝ, ((((Real.cosh (r / 2))⁻¹ : ℝ) : ℂ) * Complex.exp (((x * r : ℝ) : ℂ) * I)).re := by
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        simp only
        rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, mul_comm x r]
    _ = (∫ r : ℝ, (((Real.cosh (r / 2))⁻¹ : ℝ) : ℂ) * Complex.exp (((x * r : ℝ) : ℂ) * I)).re := hre
    _ = (∫ r : ℝ, Complex.exp (-((((-2 * x : ℝ)) : ℂ) * ((r / 2 : ℝ) : ℂ)) * I) /
          (Real.cosh (r / 2) : ℂ)).re := by
        congr 2
        funext r
        rw [show -((((-2 * x : ℝ)) : ℂ) * ((r / 2 : ℝ) : ℂ)) * I = ((x * r : ℝ) : ℂ) * I by
          push_cast; ring, Complex.ofReal_inv]
        ring
    _ = ((2 : ℝ) • ((Real.pi : ℂ) / ((Real.cosh (π * x) : ℝ) : ℂ))).re := by rw [hsub]
    _ = 2 * π * sechPiProfile x := by
        rw [Complex.real_smul, ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
        unfold sechPiProfile
        ring

/-- The cosine-modulated sech pair: `∫ cos(ar) sech(r/2) cos(rx) dr = π (sech(π(x+a)) + sech(π(x−a)))`. -/
theorem integral_cos_mul_inv_cosh_half_mul_cos (a x : ℝ) :
    ∫ r : ℝ, Real.cos (a * r) * (Real.cosh (r / 2))⁻¹ * Real.cos (r * x) =
      π * (sechPiProfile (x + a) + sechPiProfile (x - a)) := by
  have hpt : ∀ r : ℝ, Real.cos (a * r) * (Real.cosh (r / 2))⁻¹ * Real.cos (r * x) =
      (1 / 2) * ((Real.cosh (r / 2))⁻¹ * Real.cos (r * (x + a))) +
        (1 / 2) * ((Real.cosh (r / 2))⁻¹ * Real.cos (r * (x - a))) := by
    intro r
    rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub, mul_comm r a]
    ring
  simp_rw [hpt]
  rw [integral_add ((integrable_inv_cosh_half_mul_cos _).const_mul _)
    ((integrable_inv_cosh_half_mul_cos _).const_mul _), integral_const_mul, integral_const_mul,
    integral_inv_cosh_half_mul_cos, integral_inv_cosh_half_mul_cos]
  ring

theorem sechSqHalf_mul_cosh_half (r : ℝ) :
    sechSqHalf r * Real.cosh (r / 2) = (Real.cosh (r / 2))⁻¹ := by
  rw [sechSqHalf_eq_cosh, Real.rpow_neg (Real.cosh_pos _).le, Real.rpow_two]
  have hc := (Real.cosh_pos (r / 2)).ne'
  field_simp

/-- The real-line restriction of the half-time factor, `cos((y/2)√(r²+2)) sech(r/2)`. -/
def halfTimeProfileSymbol (y r : ℝ) : ℝ :=
  Real.cos (y / 2 * Real.sqrt (r ^ 2 + 2)) * (Real.cosh (r / 2))⁻¹

theorem continuous_halfTimeProfileSymbol (y : ℝ) : Continuous (halfTimeProfileSymbol y) :=
  (by fun_prop : Continuous fun r : ℝ => Real.cos (y / 2 * Real.sqrt (r ^ 2 + 2))).mul
    continuous_inv_cosh_half

theorem abs_halfTimeProfileSymbol_le (y r : ℝ) :
    |halfTimeProfileSymbol y r| ≤ (Real.cosh (r / 2))⁻¹ := by
  unfold halfTimeProfileSymbol
  rw [abs_mul, abs_of_pos (inv_pos.mpr (Real.cosh_pos _))]
  exact mul_le_of_le_one_left (inv_pos.mpr (Real.cosh_pos _)).le (Real.abs_cos_le_one _)

theorem halfTimeSecant_ofReal (y r : ℝ) :
    halfTimeSecant y r = (halfTimeProfileSymbol y r : ℂ) := by
  unfold halfTimeSecant halfTimeProfileSymbol
  rw [rhoC_ofReal, sechHalf_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_cos, ← Complex.ofReal_mul]

/-- The half-time test as a cosine transform of its symbol. -/
theorem stripTest_halfTimeSecant_eq_integral (y x : ℝ) :
    stripTest (halfTimeSecant y) x =
      1 / (2 * π) * ∫ r : ℝ, halfTimeProfileSymbol y r * Real.cos (r * x) := by
  unfold stripTest stripInvFT
  have hint : Integrable fun r : ℝ =>
      (halfTimeProfileSymbol y r : ℂ) * Complex.exp (-(I * r * x)) := by
    refine integrable_inv_cosh_half.mono'
      ((Complex.continuous_ofReal.comp (continuous_halfTimeProfileSymbol y)).mul
        (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show -(I * (r : ℂ) * (x : ℂ)) = ((-(r * x) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact abs_halfTimeProfileSymbol_le y r
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  simp_rw [halfTimeSecant_ofReal]
  rw [show (1 / (2 * (Real.pi : ℂ))) = (((1 / (2 * π) : ℝ)) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, ← hre]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [show -(I * (r : ℂ) * (x : ℂ)) = ((-(r * x) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- **Light-cone splitting of the symbol transform**: the free d'Alembert pair at half time minus
the Bessel light-cone tail, with `g₀ = sech(πx)`. -/
theorem integral_halfTimeProfileSymbol_mul_cos (y x : ℝ) :
    ∫ r : ℝ, halfTimeProfileSymbol y r * Real.cos (r * x) =
      π * (sechPiProfile (x + y / 2) + sechPiProfile (x - y / 2)) -
        (y / 2) ^ 2 / 2 * ∫ t in (-1 : ℝ)..1,
          lightConeBesselReal (2 * (y / 2) ^ 2 * (1 - t ^ 2)) *
            (π * (sechPiProfile (x + y / 2 * t) + sechPiProfile (x - y / 2 * t))) := by
  have hg : Continuous fun r : ℝ => Real.cosh (r / 2) * Real.cos (r * x) := by fun_prop
  have hgi : Integrable fun r : ℝ => sechSqHalf r * (Real.cosh (r / 2) * Real.cos (r * x)) := by
    refine (integrable_inv_cosh_half_mul_cos x).congr (Eventually.of_forall fun r => ?_)
    simp only
    rw [← mul_assoc, sechSqHalf_mul_cosh_half]
  have h := integral_cos_sqrt_mul_sechSqHalf_mul_eq (y / 2) hg hgi
  have hpt2 : ∀ r : ℝ, Real.cos (y / 2 * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
      (Real.cosh (r / 2) * Real.cos (r * x)) = halfTimeProfileSymbol y r * Real.cos (r * x) := by
    intro r
    unfold halfTimeProfileSymbol
    rw [← sechSqHalf_mul_cosh_half]
    ring
  have hpt : ∀ a r : ℝ, Real.cos (a * r) * sechSqHalf r * (Real.cosh (r / 2) * Real.cos (r * x)) =
      Real.cos (a * r) * (Real.cosh (r / 2))⁻¹ * Real.cos (r * x) := by
    intro a r
    rw [← sechSqHalf_mul_cosh_half]
    ring
  simp_rw [hpt2, hpt] at h
  have hI : ∀ t : ℝ, ∫ r : ℝ, Real.cos (y / 2 * t * r) * (Real.cosh (r / 2))⁻¹ * Real.cos (r * x) =
      π * (sechPiProfile (x + y / 2 * t) + sechPiProfile (x - y / 2 * t)) :=
    fun t => integral_cos_mul_inv_cosh_half_mul_cos _ _
  rw [h, integral_cos_mul_inv_cosh_half_mul_cos]
  simp_rw [hI]

/-- The light-cone transmuted profile
`½(g₀(x+y/2) + g₀(x−y/2)) − (y²/8) ∫_{−1}^{1} B(y²(1−t²)/2) ½(g₀(x+yt/2) + g₀(x−yt/2)) dt`. -/
def halfTimeLightConeProfile (y x : ℝ) : ℝ :=
  (sechPiProfile (x + y / 2) + sechPiProfile (x - y / 2)) / 2 -
    y ^ 2 / 8 * ∫ t in (-1 : ℝ)..1, lightConeBesselReal (y ^ 2 / 2 * (1 - t ^ 2)) *
      ((sechPiProfile (x + y / 2 * t) + sechPiProfile (x - y / 2 * t)) / 2)

/-- **Light-cone transmutation of the half-time test**: `g_{y/2}` is the d'Alembert average of
`g₀ = sech(πx)` at time `y/2` minus the Bessel light-cone tail. -/
theorem stripTest_halfTimeSecant_eq_lightCone (y x : ℝ) :
    stripTest (halfTimeSecant y) x = halfTimeLightConeProfile y x := by
  rw [stripTest_halfTimeSecant_eq_integral, integral_halfTimeProfileSymbol_mul_cos]
  unfold halfTimeLightConeProfile
  rw [show (2 : ℝ) * (y / 2) ^ 2 = y ^ 2 / 2 by ring]
  have hpull : ∫ t in (-1 : ℝ)..1, lightConeBesselReal (y ^ 2 / 2 * (1 - t ^ 2)) *
      (π * (sechPiProfile (x + y / 2 * t) + sechPiProfile (x - y / 2 * t))) =
      (2 * π) * ∫ t in (-1 : ℝ)..1, lightConeBesselReal (y ^ 2 / 2 * (1 - t ^ 2)) *
        ((sechPiProfile (x + y / 2 * t) + sechPiProfile (x - y / 2 * t)) / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [hpull]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem halfTimeSecant_zero : halfTimeSecant 0 = sechHalf := by
  funext z
  unfold halfTimeSecant
  simp

/-- **The initial profile**: `g₀ = stripTest(sech(·/2)) = sech(πx)`. -/
theorem stripTest_sechHalf_eq (x : ℝ) : stripTest sechHalf x = sechPiProfile x := by
  rw [← halfTimeSecant_zero, stripTest_halfTimeSecant_eq_lightCone]
  unfold halfTimeLightConeProfile
  have h0 : (0 : ℝ) ^ 2 / 8 = 0 := by norm_num
  rw [h0, zero_mul, sub_zero, zero_div, add_zero, sub_zero]
  ring

theorem stripTest_sechHalf_pos (x : ℝ) : 0 < stripTest sechHalf x := by
  rw [stripTest_sechHalf_eq]
  exact sechPiProfile_pos x

/-! ## Section 6: the two-point kernel sum is the convolution square of the half-time test -/

theorem norm_halfTimeSecant_ofReal_sq (y r : ℝ) :
    ‖halfTimeSecant y r‖ ^ 2 =
      (1 / 2 + Real.cos (y * Real.sqrt (r ^ 2 + 2)) / 2) * sechSqHalf r := by
  rw [halfTimeSecant_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold halfTimeProfileSymbol
  rw [mul_pow, Real.cos_sq, sechSqHalf_eq_cosh, Real.rpow_neg (Real.cosh_pos _).le, Real.rpow_two,
    inv_pow, show 2 * (y / 2 * Real.sqrt (r ^ 2 + 2)) = y * Real.sqrt (r ^ 2 + 2) by ring]

/-- **The convolution-square identity**: `½(K₀ + K_y) = 2 (g_{y/2} ⋆ g_{y/2})`, the half-sum of the
prime kernels at times `0` and `y` is twice the autocorrelation of the half-time test. -/
theorem half_kernel_sum_eq_two_mul_crossCorr (y u : ℝ) :
    (chmdPrimeKernel 0 u + chmdPrimeKernel y u) / 2 =
      2 * crossCorr (stripTest (halfTimeSecant y)) (stripTest (halfTimeSecant y)) u := by
  obtain ⟨ε, C, hε, hs⟩ := (evenStrip_halfTimeSecant y).strip
  rw [crossCorr_stripTest (by norm_num : (0 : ℝ) < 5 / 4) hε hs (evenStrip_halfTimeSecant y).sym]
  simp_rw [norm_halfTimeSecant_ofReal_sq]
  unfold chmdPrimeKernel
  have h0 : ∀ r : ℝ, Real.cos (0 * Real.sqrt (r ^ 2 + 2)) = 1 := fun r => by simp
  simp_rw [h0, one_mul]
  have hi1 : Integrable fun r : ℝ => sechSqHalf r * Real.cos (r * u) :=
    integrable_sechSqHalf_mul (by fun_prop) fun r => Real.abs_cos_le_one _
  have hi2 : Integrable fun r : ℝ =>
      Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * u) := by
    have := integrable_sechSqHalf_mul
      (g := fun r => Real.cos (y * Real.sqrt (r ^ 2 + 2)) * Real.cos (r * u)) (by fun_prop)
      (fun r => by
        rw [abs_mul]
        simpa using mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _)
          zero_le_one)
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only
    ring
  have hpt : ∀ r : ℝ, (1 / 2 + Real.cos (y * Real.sqrt (r ^ 2 + 2)) / 2) * sechSqHalf r *
      Real.cos (r * u) = (1 / 2) * (sechSqHalf r * Real.cos (r * u)) +
        (1 / 2) * (Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * u)) :=
    fun r => by ring
  simp_rw [hpt]
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul]
  ring

end RHTower.CHMDHalfTime

end
