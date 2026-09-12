import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicContinuousGreenAction
import GaloisForLFunctions.HTGeometry.TwistedRadialDerivative

/-!
# The harmonic master equation as the corpus `++` hypergeometric equation

In the horizon coordinate `z = 1 − r⁻²` the undressed master operator
`twist²y + (2r/(r²−1))twist y + (μ/(r²(r²−1)) − 4s²/(r²−1)²)y` of a harmonic at rate `2s` and angular
eigenvalue `μ` equals `4/(r²(r²−1))` times the hypergeometric expression
`z(1−z)Y'' + (C − (A+B+1)z)Y' − ABY` whenever `C = 1 + 2s`, `A + B = 1/2 + 2s` and
`AB = s² + s/2 − μ/4` (`masterOp_comp_zmap`). The Birmingham–Mokhtari parameters of the corpus `++`
second-harmonic jet at overtone `n` and angular parameter `chi` satisfy these relations for
`s = −i·chi − (2n + 3/2)` and `μ = −(1/4 + chi²)` (`dict_C`, `dict_ApB`, `dict_AB`). Consequently the
corpus regular-horizon/normalizable-AdS Green response with forcing `g` solves the undressed sourced
master equation with source `(4/(r²(r²−1)))·g(z)` on the exterior (`greenResponse_masterOp`).
-/

open GaloisForLFunctions.HTGeometry.TwistedRadial Set Filter Topology

namespace RHTower.D4BMScalarStream

noncomputable section

/-- The horizon coordinate `z = 1 − r⁻²`. -/
def zmap (r : ℝ) : ℝ := 1 - r⁻¹ ^ 2

theorem hasDerivAt_zmap (r : ℝ) (hr : r ≠ 0) : HasDerivAt zmap (2 * r⁻¹ ^ 3) r := by
  have h := ((hasDerivAt_inv hr).pow 2).const_sub 1
  refine h.congr_deriv ?_
  norm_num
  field_simp

theorem zmap_mem (r : ℝ) (hr : 1 < r) : zmap r ∈ Ioo (0 : ℝ) 1 := by
  unfold zmap
  have h0 : 0 < r := by linarith
  have h1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have h2 : 0 < r⁻¹ := inv_pos.mpr h0
  constructor <;> nlinarith

/-- The master operator on `y = Y ∘ zmap` is `4/(r²(r²−1))` times the hypergeometric jet expression
`z(1−z)Y'' + (C − (A+B+1)z)Y' − ABY` whenever `C = 1 + 2s`, `A + B = 1/2 + 2s`, `AB = s² + s/2 − μ/4`. -/
theorem masterOp_comp_zmap (s μ A B C : ℂ) (hC : C = 1 + 2 * s) (hAB : A + B = 1 / 2 + 2 * s)
    (hP : A * B = s ^ 2 + s / 2 - μ / 4) (Y Y1 Y2 : ℝ → ℂ)
    (hY : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt Y (Y1 z) z)
    (hY1 : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt Y1 (Y2 z) z) {r : ℝ} (hr1 : 1 < r) :
    twist s (twist s (Y ∘ zmap)) r + 2 * r / ((r : ℂ) ^ 2 - 1) * twist s (Y ∘ zmap) r +
      (μ / ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1)) - 4 * s ^ 2 / ((r : ℂ) ^ 2 - 1) ^ 2) * (Y ∘ zmap) r =
      4 / ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1)) *
        (((zmap r * (1 - zmap r) : ℝ) : ℂ) * Y2 (zmap r) + (C - (A + B + 1) * (zmap r : ℂ)) * Y1 (zmap r) -
          A * B * Y (zmap r)) := by
  have hr0 : r ≠ 0 := by linarith
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hfC : (r : ℂ) ^ 2 - 1 ≠ 0 := by exact_mod_cast (by nlinarith : r ^ 2 - 1 ≠ 0)
  have hy : ∀ r' : ℝ, 1 < r' → HasDerivAt (Y ∘ zmap) ((2 * r'⁻¹ ^ 3 : ℝ) • Y1 (zmap r')) r' := by
    intro r' hr'
    exact (hY _ (zmap_mem r' hr')).scomp r' (hasDerivAt_zmap r' (by linarith))
  have htw : twist s (Y ∘ zmap) =ᶠ[𝓝 r] fun r' => ((2 * r'⁻¹ ^ 3 : ℝ) : ℂ) * Y1 (zmap r') +
      2 * s / ((r' : ℂ) * ((r' : ℂ) ^ 2 - 1)) * Y (zmap r') := by
    filter_upwards [isOpen_Ioi.mem_nhds hr1] with r' hr'
    simp only [twist, (hy r' hr').deriv, Complex.real_smul, Function.comp]
  have hd : HasDerivAt (fun r' : ℝ => ((2 * r'⁻¹ ^ 3 : ℝ) : ℂ) * Y1 (zmap r') +
      2 * s / ((r' : ℂ) * ((r' : ℂ) ^ 2 - 1)) * Y (zmap r'))
      ((((2 * (3 * r⁻¹ ^ 2 * (-(r ^ 2)⁻¹))) : ℝ) : ℂ) * Y1 (zmap r) +
        ((2 * r⁻¹ ^ 3 : ℝ) : ℂ) * ((2 * r⁻¹ ^ 3 : ℝ) • Y2 (zmap r)) +
        ((0 * ((r : ℂ) * ((r : ℂ) ^ 2 - 1)) - 2 * s * (1 * ((r : ℂ) ^ 2 - 1) + (r : ℂ) * (2 * (r : ℂ) ^ (2 - 1) * 1 - 0))) /
            ((r : ℂ) * ((r : ℂ) ^ 2 - 1)) ^ 2 * Y (zmap r) +
          2 * s / ((r : ℂ) * ((r : ℂ) ^ 2 - 1)) * ((2 * r⁻¹ ^ 3 : ℝ) • Y1 (zmap r)))) r := by
    have hR : HasDerivAt (fun r' : ℝ => (r' : ℂ)) 1 r := by simpa using (hasDerivAt_id r).ofReal_comp
    have h1 : HasDerivAt (fun r' : ℝ => ((2 * r'⁻¹ ^ 3 : ℝ) : ℂ))
        (((2 * (3 * r⁻¹ ^ 2 * (-(r ^ 2)⁻¹))) : ℝ) : ℂ) r :=
      (((hasDerivAt_inv hr0).pow 3).const_mul 2).ofReal_comp
    have h2 : HasDerivAt (fun r' : ℝ => Y1 (zmap r')) ((2 * r⁻¹ ^ 3 : ℝ) • Y2 (zmap r)) r :=
      (hY1 _ (zmap_mem r hr1)).scomp r (hasDerivAt_zmap r hr0)
    have h3 : HasDerivAt (fun r' : ℝ => 2 * s / ((r' : ℂ) * ((r' : ℂ) ^ 2 - 1)))
        ((0 * ((r : ℂ) * ((r : ℂ) ^ 2 - 1)) - 2 * s * (1 * ((r : ℂ) ^ 2 - 1) + (r : ℂ) * (2 * (r : ℂ) ^ (2 - 1) * 1 - 0))) /
          ((r : ℂ) * ((r : ℂ) ^ 2 - 1)) ^ 2) r :=
      (hasDerivAt_const r (2 * s)).div (hR.mul ((hR.pow 2).sub (hasDerivAt_const r (1 : ℂ))))
        (mul_ne_zero hrC hfC)
    have h4 : HasDerivAt (fun r' : ℝ => Y (zmap r')) ((2 * r⁻¹ ^ 3 : ℝ) • Y1 (zmap r)) r :=
      (hY _ (zmap_mem r hr1)).scomp r (hasDerivAt_zmap r hr0)
    exact (h1.mul h2).add (h3.mul h4)
  rw [twist_congr s htw, twist, hd.deriv, hP, hAB, hC]
  simp only [twist, (hy r hr1).deriv, Complex.real_smul, Function.comp, zmap]
  push_cast
  field_simp
  ring

/-- Rate of the harmonic at overtone `n` and angular parameter `chi`: `s = −i·chi − (2n + 3/2)`. -/
def dictRate (n : ℕ) (chi : ℂ) : ℂ := -(Complex.I * chi) - d4BMCausalDecay n

/-- Angular eigenvalue at angular parameter `chi`: `μ = −(1/4 + chi²)`. -/
def dictEigen (chi : ℂ) : ℂ := -(1 / 4 + chi ^ 2)

theorem dict_C (n : ℕ) (chi : ℂ) :
    d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) = 1 + 2 * dictRate n chi := by
  unfold d4BMCausalRadialC d4BMCausalPlusPlusFrequency d4BMCausalQNMPlus dictRate
  linear_combination (2 * d4BMCausalDecay n) * Complex.I_sq

theorem dict_ApB (n : ℕ) (chi : ℂ) :
    d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
      d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi = 1 / 2 + 2 * dictRate n chi := by
  unfold d4BMCausalHypergeometricA d4BMCausalHypergeometricB d4BMCausalRadialA d4BMCausalRadialB
    d4BMCausalPlusPlusFrequency d4BMCausalQNMPlus dictRate
  linear_combination (2 * d4BMCausalDecay n) * Complex.I_sq

theorem dict_AB (n : ℕ) (chi : ℂ) :
    d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi *
      d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi =
      dictRate n chi ^ 2 + dictRate n chi / 2 - dictEigen chi / 4 := by
  unfold d4BMCausalHypergeometricA d4BMCausalHypergeometricB d4BMCausalRadialA d4BMCausalRadialB
    d4BMCausalPlusPlusFrequency d4BMCausalQNMPlus dictRate dictEigen
  linear_combination (d4BMCausalDecay n / 2 + d4BMCausalDecay n ^ 2 * (Complex.I ^ 2 - 1) -
    2 * Complex.I * chi * d4BMCausalDecay n - chi ^ 2 / 4) * Complex.I_sq

/-- The corpus `++` Green response with forcing `g`, pulled back to the exterior radius, solves the
undressed master equation with source `(4/(r²(r²−1)))·g(z)`. -/
theorem greenResponse_masterOp (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioo 0 1)) {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    {r : ℝ} (hr1 : 1 < r) :
    twist (dictRate n chi) (twist (dictRate n chi) (d4BMPlusPlusContinuousGreenResponse n chi g a b ∘ zmap)) r +
      2 * r / ((r : ℂ) ^ 2 - 1) * twist (dictRate n chi) (d4BMPlusPlusContinuousGreenResponse n chi g a b ∘ zmap) r +
      (dictEigen chi / ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1)) - 4 * dictRate n chi ^ 2 / ((r : ℂ) ^ 2 - 1) ^ 2) *
        (d4BMPlusPlusContinuousGreenResponse n chi g a b ∘ zmap) r =
      4 / ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1)) * g (zmap r) := by
  rw [masterOp_comp_zmap (dictRate n chi) (dictEigen chi) _ _ _ (dict_C n chi) (dict_ApB n chi) (dict_AB n chi)
    (d4BMPlusPlusContinuousGreenResponse n chi g a b) (d4BMPlusPlusContinuousGreenResponseDerivative n chi g a b)
    (d4BMPlusPlusContinuousGreenResponseSecondDerivative n chi g a b)
    (fun z hz => hasDerivAt_d4BMPlusPlusContinuousGreenResponse n chi hchi hg ha hb hz)
    (fun z hz => hasDerivAt_d4BMPlusPlusContinuousGreenResponseDerivative n chi hchi hg ha hb hz) hr1]
  have h := d4BMPlusPlusContinuousGreenResponse_forcedJet n chi hchi g a b (zmap_mem r hr1)
  unfold d4BMPlusPlusHypergeometricJet at h
  rw [h]

end
end RHTower.D4BMScalarStream
