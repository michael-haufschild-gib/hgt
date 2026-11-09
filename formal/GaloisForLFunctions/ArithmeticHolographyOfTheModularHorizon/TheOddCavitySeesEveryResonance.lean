import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.OneCavityFunctionSeesEveryResonanceThatAPairSees
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheDualSideHasNoSign
import GaloisForLFunctions.BlackHoleRingdown.TheCuspFormsExist
import GaloisForLFunctions.RHTower.EisensteinLineModelBounds
import GaloisForLFunctions.RHTower.EisensteinTruncatedRowSum
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding
import GaloisForLFunctions.RHTower.HalfWeightRankinSelberg

/-!
# The odd cavity sees every resonance

The mirror `ι z = −z̄` normalizes `SL₂(ℤ)` and the Eisenstein channel is mirror-even, so a mirror-odd modular
function has zero mean on every closed horocycle: the **odd sector is a cavity**
(`BlackHoleRingdown.OddCusp.horocycle_mean_eq_zero_of_odd`). This module proves that the cavity nevertheless
sees every resonance of the Eisenstein channel through the energies of its functions: B109 holds in the
cavity-function form, unconditionally.

**Odd cusp fields.** For a continuous height profile `φ` vanishing below height `2` and above some height, the
profile `φ(Im w) sin(2π Re w)` extends to a continuous, `SL₂(ℤ)`-invariant, mirror-odd field `G_φ` on `ℍ`
(`oddCuspField`), equal to the profile above height `½` and bounded by `M e^{−π Im z}`.

**The pairing unfolds to the strip.** For `s ≠ 1`, on `𝒟` the field is its profile, and only the rows
`(0, ±1)` of the unfolding meet the support (`setIntegral_fd_eq_strip_of_high`), so

  `∫_𝒟 G_φ² E*(s − ½) = ∫_0^∞ φ(y)² W_s(y) dy/y²`,   `W_s(y) = ∫_0^1 sin²(2πx) E*(s − ½; x, y) dx`

(`pairing_oddCuspField`).

**At a resonance.** If `ξ(2s) = 0` the growing power of `E*` drops out and
`W_s(y) = ½κ y^{1−s} + T_s(y)` with `κ = ξ(2s − 1)/((2s − 2)(2s − 1))` and a bounded tail `T_s`
(`horocycleProfile_eq_of_resonance`, `exists_tail_bound`). For `s = ρ/2` with `Re ρ > 0`, `κ ≠ 0` because
`ξ(ρ − 1) = ξ(2 − ρ)` and `Re(2 − ρ) > 1` (`resonance_data`). On a tent `[j + 3, j + 4]` far up the cusp the
phase of `y^{1−s}` turns by at most `|Im s|/(j + 3)` and its size `y^{1−Re s}` beats the tail. This is the
**phase law** (`exists_tent_phase`): `Re(e^{iθ} d_j(s)) > 0` for the tent energy `d_j(s) = ∫_𝒟 G_j² E*(s − ½)`
whenever `cos(θ + arg κ − Im s · log(j + 7/2)) ≥ ¾`. In particular `d_j(s) ≠ 0` (`exists_tent_seeing`).

**B109 in the cavity.** Over the tent family, Baire gives a dense set of coefficient vectors whose cavity
function sees every right resonance (`dense_odd_cavity_seeing`). The result is a **complete cuspidal receiver**
(`exists_odd_cavity_receiver`): a continuous, modular, mirror-odd function `g` with zero horocycle means such
that a horocycle rate `y^α` of `|g|²` forces `Re ρ ≤ 2 − 2α` at every zero `ρ` of `ζ` with `Re ρ > ½`.
-/

open Complex MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown EisensteinSeries
open UpperHalfPlane (ofComplex)
open BlackHoleRingdown.OddCusp (mirror mirrorSL mirror_smul coe_mirror mirror_im reduceSL reduceSL_mem
  im_lt_two_of_ne_zero exists_int_of_bottom_zero)

/-! ### Odd cusp fields -/

/-- An admissible height profile: continuous, zero below height `2` and above some height. -/
structure IsHeightProfile (φ : ℝ → ℝ) : Prop where
  continuous : Continuous φ
  low : ∀ y, y ≤ 2 → φ y = 0
  high : ∃ b, ∀ y, b ≤ y → φ y = 0

variable {φ : ℝ → ℝ}

/-- The odd profile `φ(Im w) sin(2π Re w)`. -/
def oddProfile (φ : ℝ → ℝ) (w : ℂ) : ℝ := φ w.im * Real.sin (2 * Real.pi * w.re)

theorem oddProfile_eq_zero_of_im_le (hφ : IsHeightProfile φ) {w : ℂ} (hw : w.im ≤ 2) : oddProfile φ w = 0 := by
  rw [oddProfile, hφ.low _ hw, zero_mul]

theorem oddProfile_add_int (w : ℂ) (n : ℤ) : oddProfile φ (w + n) = oddProfile φ w := by
  simp only [oddProfile, Complex.add_im, Complex.intCast_im, add_zero, Complex.add_re, Complex.intCast_re]
  rw [show 2 * Real.pi * (w.re + n) = 2 * Real.pi * w.re + n * (2 * Real.pi) by ring,
    Real.sin_add_int_mul_two_pi]

theorem oddProfile_mirror (w : ℂ) : oddProfile φ (-(starRingEnd ℂ) w) = -oddProfile φ w := by
  simp only [oddProfile, Complex.neg_im, Complex.conj_im, neg_neg, Complex.neg_re, Complex.conj_re,
    mul_neg, Real.sin_neg]

/-- If `Im w > ½` and `Im gw > ½`, the profile agrees at `w` and `gw`. -/
theorem oddProfile_smul_eq (hφ : IsHeightProfile φ) (g : SL(2, ℤ)) {w : ℍ} (hw : 1 / 2 < w.im)
    (hgw : 1 / 2 < (g • w).im) : oddProfile φ (g • w : ℍ) = oddProfile φ w := by
  by_cases hc : g 1 0 = 0
  · obtain ⟨n, hn⟩ := exists_int_of_bottom_zero hc w
    rw [hn, oddProfile_add_int]
  · have h1 : (g • w).im < 2 := im_lt_two_of_ne_zero hc hw
    have hinv : (g⁻¹) 1 0 = -g 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      rfl
    have hc' : (g⁻¹) 1 0 ≠ 0 := by rw [hinv]; exact neg_ne_zero.mpr hc
    have h2 : w.im < 2 := by
      have := im_lt_two_of_ne_zero hc' hgw
      rwa [inv_smul_smul] at this
    rw [oddProfile_eq_zero_of_im_le hφ (by exact h1.le), oddProfile_eq_zero_of_im_le hφ (by exact h2.le)]

/-- **The odd cusp field** `G_φ(z) = φ(Im γz) sin(2π Re γz)` for any `γ` with `Im γz > ½`. -/
def oddCuspField (φ : ℝ → ℝ) (z : ℍ) : ℝ := oddProfile φ (reduceSL z • z : ℍ)

theorem oddCuspField_eq (hφ : IsHeightProfile φ) {z : ℍ} (g : SL(2, ℤ)) (hg : 1 / 2 < (g • z).im) :
    oddCuspField φ z = oddProfile φ (g • z : ℍ) := by
  have e : (reduceSL z * g⁻¹) • g • z = reduceSL z • z := by rw [smul_smul, inv_mul_cancel_right]
  have hr : 1 / 2 < ((reduceSL z * g⁻¹) • g • z).im := by
    rw [e]; exact OddCusp.half_lt_im_of_mem_fd (reduceSL_mem z)
  rw [oddCuspField, ← e, oddProfile_smul_eq hφ _ hg hr]

theorem oddCuspField_of_half_lt (hφ : IsHeightProfile φ) {z : ℍ} (hz : 1 / 2 < z.im) :
    oddCuspField φ z = oddProfile φ z := by
  rw [oddCuspField_eq hφ 1 (by rwa [one_smul]), one_smul]

theorem oddCuspField_smul (hφ : IsHeightProfile φ) (A : SL(2, ℤ)) (z : ℍ) :
    oddCuspField φ (A • z) = oddCuspField φ z := by
  have e : (reduceSL z * A⁻¹) • A • z = reduceSL z • z := by rw [smul_smul, inv_mul_cancel_right]
  rw [oddCuspField_eq hφ (reduceSL z * A⁻¹) (by rw [e]; exact OddCusp.half_lt_im_of_mem_fd (reduceSL_mem z)), e]
  rfl

theorem oddCuspField_mirror (hφ : IsHeightProfile φ) (z : ℍ) : oddCuspField φ (mirror z) = -oddCuspField φ z := by
  have e : mirrorSL (reduceSL z) • mirror z = mirror (reduceSL z • z) := (mirror_smul _ _).symm
  rw [oddCuspField_eq hφ (mirrorSL (reduceSL z))
    (by rw [e, mirror_im]; exact OddCusp.half_lt_im_of_mem_fd (reduceSL_mem z)), e, coe_mirror,
    oddProfile_mirror]
  rfl

theorem continuous_oddProfile (hφ : IsHeightProfile φ) : Continuous (oddProfile φ) :=
  (hφ.continuous.comp Complex.continuous_im).mul
    (Real.continuous_sin.comp (continuous_const.mul Complex.continuous_re))

/-- **The odd cusp field is continuous**: near every point it is the profile composed with one modular map. -/
theorem continuous_oddCuspField (hφ : IsHeightProfile φ) : Continuous (oddCuspField φ) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  set g := reduceSL z₀
  have hg : 1 / 2 < (g • z₀).im := OddCusp.half_lt_im_of_mem_fd (reduceSL_mem z₀)
  have hcg : Continuous fun z : ℍ => g • z := RHTower.HalfWeight.continuous_smul_sl g
  have hopen : IsOpen {z : ℍ | 1 / 2 < (g • z).im} :=
    isOpen_lt continuous_const (UpperHalfPlane.continuous_im.comp hcg)
  have hev : (fun z : ℍ => oddProfile φ (g • z : ℍ)) =ᶠ[𝓝 z₀] oddCuspField φ := by
    filter_upwards [hopen.mem_nhds hg] with z hz
    exact (oddCuspField_eq hφ g hz).symm
  exact (((continuous_oddProfile hφ).comp (UpperHalfPlane.continuous_coe.comp hcg)).continuousAt).congr hev

theorem abs_oddCuspField_le {B : ℝ} (hB : ∀ y, |φ y| ≤ B) (z : ℍ) :
    |oddCuspField φ z| ≤ B := by
  rw [oddCuspField, oddProfile, abs_mul]
  exact (mul_le_mul (hB _) (Real.abs_sin_le_one _) (abs_nonneg _)
    ((abs_nonneg _).trans (hB 0))).trans_eq (mul_one B)

theorem oddCuspField_eq_zero_of_high (hφ : IsHeightProfile φ) {b : ℝ} (hb : ∀ y, b ≤ y → φ y = 0) {z : ℍ}
    (hz : max b 1 ≤ z.im) : oddCuspField φ z = 0 := by
  rw [oddCuspField_of_half_lt hφ (by linarith [le_max_right b 1]), oddProfile]
  exact mul_eq_zero_of_left (hb _ ((le_max_left b 1).trans hz)) _

/-- The odd cusp field lies under an envelope `M e^{−π Im z}`. -/
theorem exists_envelope_oddCuspField (hφ : IsHeightProfile φ) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℍ, ‖(oddCuspField φ z : ℂ)‖ ≤ M * Real.exp (-Real.pi * z.im) := by
  obtain ⟨b, hb⟩ := hφ.high
  obtain ⟨B, hB⟩ : ∃ B, ∀ y, |φ y| ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (2 : ℝ)) (b := max b 2)).exists_bound_of_continuousOn
      hφ.continuous.continuousOn
    refine ⟨B, fun y => ?_⟩
    by_cases h1 : y ≤ 2
    · rw [hφ.low y h1, abs_zero]; exact (norm_nonneg _).trans (hB 2 ⟨le_rfl, le_max_right _ _⟩)
    by_cases h2 : max b 2 ≤ y
    · rw [hb y ((le_max_left b 2).trans h2), abs_zero]
      exact (norm_nonneg _).trans (hB 2 ⟨le_rfl, le_max_right _ _⟩)
    · exact hB y ⟨(not_le.1 h1).le, (not_le.1 h2).le⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine ⟨B * Real.exp (Real.pi * max b 1) + 1, by positivity, fun z => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hz : max b 1 ≤ z.im
  · rw [oddCuspField_eq_zero_of_high hφ hb hz, abs_zero]; positivity
  · have h1 : 1 ≤ Real.exp (Real.pi * max b 1) * Real.exp (-Real.pi * z.im) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [Real.pi_pos, (not_le.1 hz).le])
    calc |oddCuspField φ z| ≤ B := abs_oddCuspField_le hB z
      _ ≤ B * (Real.exp (Real.pi * max b 1) * Real.exp (-Real.pi * z.im)) := le_mul_of_one_le_right hB0 h1
      _ ≤ (B * Real.exp (Real.pi * max b 1) + 1) * Real.exp (-Real.pi * z.im) := by
          nlinarith [Real.exp_pos (-Real.pi * z.im)]

/-! ### Reduction to the strip -/

/-- A translation-periodic function vanishing at heights `≤ 1` has the same integral over `𝒟` and over the
strip: only the rows `(0, ±1)` of the unfolding meet its support. -/
theorem setIntegral_fd_eq_strip_of_high {H : ℍ → ℂ} (hT : ∀ (n : ℤ) (z : ℍ), H (ModularGroup.T ^ n • z) = H z)
    (hint : IntegrableOn H modularStrip volume) (hlow : ∀ z : ℍ, z.im ≤ 1 → H z = 0) :
    ∫ z in ModularGroup.fd, H z = ∫ z in modularStrip, H z := by
  have hU := tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip H hT hint
  have hterm : ∀ v : gammaSet 1 1 0, ∫ z in ModularGroup.fd, H (gammaSetMatrix v • z) =
      if v = rowPlus ∨ v = rowMinus then ∫ z in ModularGroup.fd, H z else 0 := by
    intro v
    split_ifs with hv
    · have hc : gammaSetMatrix v 1 0 = 0 := by
        rw [gammaSetMatrix_apply_one_zero]; exact (first_zero_iff v).2 hv
      refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z _ => ?_
      obtain ⟨n, hn⟩ := exists_int_of_bottom_zero hc z
      have : gammaSetMatrix v • z = ModularGroup.T ^ n • z := by
        apply UpperHalfPlane.ext
        rw [hn, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
        push_cast; ring
      rw [this, hT]
    · have hv0 : v.1 0 ≠ 0 := fun h => hv ((first_zero_iff v).1 h)
      refine (setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z hz => ?_).trans
        (integral_zero _ _)
      exact hlow _ (rowHeight_le_one_of_mem_fd hz hv0)
  have hsum : ∑' v : gammaSet 1 1 0, ∫ z in ModularGroup.fd, H (gammaSetMatrix v • z) =
      2 * ∫ z in ModularGroup.fd, H z := by
    rw [tsum_congr hterm, tsum_eq_sum (s := {rowPlus, rowMinus}) (fun v hv => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      simp [hv.1, hv.2])]
    rw [Finset.sum_pair rowPlus_ne_rowMinus]
    simp [rowPlus_ne_rowMinus, rowPlus_ne_rowMinus.symm]
    ring
  rw [hsum] at hU
  linear_combination hU / 2

/-! ### The completed Eisenstein function at a resonance -/

/-- The coefficient `κ(u) = ξ(2u)/((2u − 1)(2u))` of the surviving power `Y^{½−u}` of `E*(u)`. -/
def resonanceCoefficient (u : ℂ) : ℂ := xi (2 * u) / ((2 * u - 1) * (2 * u))

/-- **At a resonance the growing power drops out**: if `ξ(1 + 2u) = 0`, then
`E*(u; x, Y) = κ(u) Y^{½−u} + tail(x, Y)`. -/
theorem completedEisenstein_eq_of_resonance {u : ℂ} (hres : xi (1 + 2 * u) = 0) (h1 : 1 + 2 * u ≠ 0)
    (h2 : 2 * u ≠ 0) (h3 : 2 * u - 1 ≠ 0) (x Y : ℝ) :
    EisAuto.completedEisenstein u x Y = resonanceCoefficient u * (Y : ℂ) ^ (1 / 2 - u) + eisTail u x Y := by
  have hu : u ≠ 0 := fun h => h2 (by rw [h, mul_zero])
  unfold EisAuto.completedEisenstein eisensteinNumerator resonanceCoefficient
  rw [hres]
  field_simp
  ring

/-- The data of a resonance `s = ρ/2`, `ζ(ρ) = 0`, `Re ρ > 0`. With `u = s − ½`: `ξ(1 + 2u) = ξ(ρ) = 0`, the
denominators `ρ, ρ − 1, ρ − 2` are nonzero, and `κ(u) = ξ(ρ − 1)/((ρ − 2)(ρ − 1)) ≠ 0` since
`ξ(ρ − 1) = ξ(2 − ρ)` with `Re(2 − ρ) > 1`. -/
theorem resonance_data {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    xi (1 + 2 * (ρ / 2 - 1 / 2)) = 0 ∧ 1 + 2 * (ρ / 2 - 1 / 2) ≠ 0 ∧ 2 * (ρ / 2 - 1 / 2) ≠ 0 ∧
      2 * (ρ / 2 - 1 / 2) - 1 ≠ 0 ∧ resonanceCoefficient (ρ / 2 - 1 / 2) ≠ 0 ∧ ρ.re < 1 := by
  have hlt : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
  have e1 : 1 + 2 * (ρ / 2 - 1 / 2) = ρ := by ring
  have e2 : 2 * (ρ / 2 - 1 / 2) = ρ - 1 := by ring
  have e3 : 2 * (ρ / 2 - 1 / 2) - 1 = ρ - 2 := by ring
  have h0 : ρ ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
  have h1 : ρ - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h2 : ρ - 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hxi : xi ρ = 0 := by
    refine xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.2 ⟨hζ, fun n hn => ?_⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hk : xi (ρ - 1) ≠ 0 := by
    rw [show ρ - 1 = 1 - (2 - ρ) by ring, xi_one_sub]
    exact xi_ne_zero_of_one_le_re (by simp; linarith)
  refine ⟨by rw [e1]; exact hxi, by rw [e1]; exact h0, by rw [e2]; exact h1, by rw [e3]; exact h2, ?_, hlt⟩
  rw [resonanceCoefficient, e3, e2]
  exact div_ne_zero hk (mul_ne_zero h2 h1)

/-- `∫_0^1 sin²(2πx) dx = ½`. -/
theorem integral_sin_sq_two_pi : ∫ x in Ico (0 : ℝ) 1, Real.sin (2 * Real.pi * x) ^ 2 = 1 / 2 := by
  have hc : (2 * Real.pi) ≠ 0 := by positivity
  have h : ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 =
      (2 * Real.pi)⁻¹ • ∫ x in (2 * Real.pi * 0)..(2 * Real.pi * 1), Real.sin x ^ 2 :=
    intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hc
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, h, integral_sin_sq]
  simp only [mul_zero, mul_one, Real.sin_zero, Real.sin_two_pi, zero_mul, sub_zero, smul_eq_mul]
  field_simp
  ring

/-! ### The horocycle profile of `E*` -/

/-- The horocycle profile `W_s(y) = ∫_0^1 sin²(2πx) E*(s − ½; x, y) dx`. -/
def horocycleProfile (s : ℂ) (y : ℝ) : ℂ :=
  ∫ x in Ico (0 : ℝ) 1, ((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) * EisAuto.completedEisenstein (s - 1 / 2) x y

theorem continuous_eisTail_x (u : ℂ) {Y : ℝ} (hY : 0 < Y) : Continuous fun x => eisTail u x Y := by
  unfold eisTail
  simp_rw [weightedTail_eq_signedSqrtWhittakerTail]
  exact (continuous_signedSqrtWhittakerTail_x false hY u).add (continuous_signedSqrtWhittakerTail_x true hY u)

theorem continuous_sin_sq_two_pi : Continuous fun x : ℝ => ((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) := by
  fun_prop

/-- **At a resonance the profile is a power plus a tail**: `W_s(y) = ½ κ y^{1−s} + T_s(y)`, where
`T_s(y) = ∫_0^1 sin²(2πx) tail(x, y) dx`. -/
theorem horocycleProfile_eq_of_resonance {s : ℂ} (hres : xi (1 + 2 * (s - 1 / 2)) = 0)
    (h1 : 1 + 2 * (s - 1 / 2) ≠ 0) (h2 : 2 * (s - 1 / 2) ≠ 0) (h3 : 2 * (s - 1 / 2) - 1 ≠ 0) {y : ℝ}
    (hy : 0 < y) :
    horocycleProfile s y = 1 / 2 * resonanceCoefficient (s - 1 / 2) * (y : ℂ) ^ (1 - s) +
      ∫ x in Ico (0 : ℝ) 1, ((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) * eisTail (s - 1 / 2) x y := by
  have hA : IntegrableOn (fun x : ℝ => ((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) *
      (resonanceCoefficient (s - 1 / 2) * (y : ℂ) ^ (1 - s))) (Ico 0 1) :=
    ((continuous_sin_sq_two_pi.mul continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ico_subset_Icc_self
  have hB : IntegrableOn (fun x : ℝ => ((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) *
      eisTail (s - 1 / 2) x y) (Ico 0 1) :=
    ((continuous_sin_sq_two_pi.mul (continuous_eisTail_x _ hy)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ico_subset_Icc_self
  have e : horocycleProfile s y = ∫ x in Ico (0 : ℝ) 1, (((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) *
      (resonanceCoefficient (s - 1 / 2) * (y : ℂ) ^ (1 - s)) +
      ((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) * eisTail (s - 1 / 2) x y) := by
    unfold horocycleProfile
    refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
    rw [completedEisenstein_eq_of_resonance hres h1 h2 h3, show (1 : ℂ) / 2 - (s - 1 / 2) = 1 - s by ring,
      mul_add]
  rw [e, integral_add hA hB, integral_mul_const, integral_complex_ofReal, integral_sin_sq_two_pi]
  push_cast
  ring

/-- The tail of the profile is bounded high in the cusp. -/
theorem exists_tail_bound (u : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 / 2 ≤ y →
      ‖∫ x in Ico (0 : ℝ) 1, ((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) * eisTail u x y‖ ≤ C := by
  obtain ⟨Ct, hCt0, hCt⟩ := CuspRSC.norm_weightedTail_le (abs_nonneg u.re)
  refine ⟨2 * Ct, by positivity, fun y hy => ?_⟩
  have hb : ∀ x ∈ Ico (0 : ℝ) 1,
      ‖((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) * eisTail u x y‖ ≤ 2 * Ct := by
    intro x _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hT : ‖eisTail u x y‖ ≤ 2 * Ct := by
      unfold eisTail
      refine (norm_add_le _ _).trans ?_
      linarith [hCt u false x y le_rfl hy, hCt u true x y le_rfl hy]
    calc Real.sin (2 * Real.pi * x) ^ 2 * ‖eisTail u x y‖ ≤ 1 * (2 * Ct) :=
          mul_le_mul (Real.sin_sq_le_one _) hT (norm_nonneg _) zero_le_one
      _ = 2 * Ct := one_mul _
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ico (0 : ℝ) 1) measure_Ico_lt_top hb
  rwa [measureReal_def, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal zero_le_one, mul_one] at h

/-! ### The pairing of an odd cusp field -/

theorem IsHeightProfile.exists_bound (hφ : IsHeightProfile φ) : ∃ B, 0 ≤ B ∧ ∀ y, |φ y| ≤ B := by
  obtain ⟨b, hb⟩ := hφ.high
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (2 : ℝ)) (b := max b 2)).exists_bound_of_continuousOn
    hφ.continuous.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 2 ⟨le_rfl, le_max_right _ _⟩)
  refine ⟨B, hB0, fun y => ?_⟩
  by_cases h1 : y ≤ 2
  · rw [hφ.low y h1, abs_zero]; exact hB0
  by_cases h2 : max b 2 ≤ y
  · rw [hb y ((le_max_left b 2).trans h2), abs_zero]; exact hB0
  · exact hB y ⟨(not_le.1 h1).le, (not_le.1 h2).le⟩

/-- The strip integrand `φ(Im z)² sin²(2π Re z) E*(s − ½; z)`. -/
def oddStripIntegrand (φ : ℝ → ℝ) (s : ℂ) (z : ℍ) : ℂ :=
  ((oddProfile φ z ^ 2 : ℝ) : ℂ) * EisAuto.completedEisenstein (s - 1 / 2) z.re z.im

theorem coe_T_zpow_smul (n : ℤ) (z : ℍ) : ((ModularGroup.T ^ n • z : ℍ) : ℂ) = (z : ℂ) + n := by
  rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  push_cast; ring

theorem oddStripIntegrand_T {s : ℂ} (hs : s ≠ 1) (n : ℤ) (z : ℍ) :
    oddStripIntegrand φ s (ModularGroup.T ^ n • z) = oddStripIntegrand φ s z := by
  have hu : s - 1 / 2 ≠ 1 / 2 := fun h => hs (by linear_combination h)
  unfold oddStripIntegrand
  rw [EisAuto.completedEisenstein_smul _ z hu, coe_T_zpow_smul, oddProfile_add_int]

theorem oddStripIntegrand_eq_zero_of_im_le (hφ : IsHeightProfile φ) {s : ℂ} {z : ℍ} (hz : z.im ≤ 2) :
    oddStripIntegrand φ s z = 0 := by
  rw [oddStripIntegrand, oddProfile_eq_zero_of_im_le hφ (w := (z : ℂ)) hz]
  simp

theorem oddStripIntegrand_eq_max (hφ : IsHeightProfile φ) (s : ℂ) (z : ℍ) :
    oddStripIntegrand φ s z = ((oddProfile φ z ^ 2 : ℝ) : ℂ) *
      EisAuto.completedEisenstein (s - 1 / 2) z.re (max z.im (1 / 2)) := by
  by_cases hz : z.im ≤ 2
  · rw [oddStripIntegrand_eq_zero_of_im_le hφ hz, oddProfile_eq_zero_of_im_le hφ (w := (z : ℂ)) hz]; simp
  · rw [oddStripIntegrand, max_eq_left (by linarith [not_le.1 hz])]

theorem continuous_oddStripIntegrand (hφ : IsHeightProfile φ) (s : ℂ) : Continuous (oddStripIntegrand φ s) := by
  rw [show oddStripIntegrand φ s = fun z : ℍ => ((oddProfile φ z ^ 2 : ℝ) : ℂ) *
      EisAuto.completedEisenstein (s - 1 / 2) z.re (max z.im (1 / 2)) from funext (oddStripIntegrand_eq_max hφ s)]
  exact (Complex.continuous_ofReal.comp
    (((continuous_oddProfile hφ).comp UpperHalfPlane.continuous_coe).pow 2)).mul
      (CuspRSC.continuous_completed_max _)

/-- The strip integrand is bounded by a multiple of the indicator of `Im z ≥ 2`. -/
theorem exists_oddStripIntegrand_bound (hφ : IsHeightProfile φ) {s : ℂ} (hs : s ≠ 1) :
    ∃ K : ℝ, ∀ z : ℍ,
      ‖oddStripIntegrand φ s z‖ ≤ K * ‖{z : ℍ | 2 ≤ z.im}.indicator (fun _ => (1 : ℂ)) z‖ := by
  have hu : s - 1 / 2 ≠ 1 / 2 := fun h => hs (by linear_combination h)
  obtain ⟨b, hb⟩ := hφ.high
  obtain ⟨B, hB0, hB⟩ := hφ.exists_bound
  obtain ⟨α, β, a, hα, hβ, ha, hN⟩ := exists_kernel_bound (K := {s - 1 / 2}) isCompact_singleton
    (fun u hu' => by rw [mem_singleton_iff.1 hu']; exact hu)
  set b' := max b 2
  set D := ‖(1 + 2 * (s - 1 / 2)) * (2 * (s - 1 / 2))‖
  refine ⟨B ^ 2 * ((α * b' ^ a + β) / D), fun z => ?_⟩
  have hK0 : 0 ≤ B ^ 2 * ((α * b' ^ a + β) / D) := by positivity
  by_cases hz2 : 2 ≤ z.im
  · rw [indicator_of_mem (show z ∈ {z : ℍ | 2 ≤ z.im} from hz2), norm_one, mul_one]
    by_cases hzb : b' ≤ z.im
    · have h0 : oddProfile φ z = 0 := by
        rw [oddProfile]; exact mul_eq_zero_of_left (hb _ ((le_max_left b 2).trans hzb)) _
      rw [oddStripIntegrand, h0]; simpa using hK0
    · have hz0 : 0 < z.im := z.im_pos
      have hp : oddProfile φ z ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        rw [oddProfile, abs_mul]
        exact (mul_le_mul (hB _) (Real.abs_sin_le_one _) (abs_nonneg _) hB0).trans_eq (mul_one B)
      have hE : ‖EisAuto.completedEisenstein (s - 1 / 2) z.re z.im‖ ≤ (α * b' ^ a + β) / D := by
        rw [EisAuto.completedEisenstein, norm_div]
        refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
        refine (hN _ (mem_singleton _) z.re z.im (by linarith)).trans ?_
        have := Real.rpow_le_rpow hz0.le (not_le.1 hzb).le ha
        nlinarith
      rw [oddStripIntegrand, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul hp hE (norm_nonneg _) (sq_nonneg _)
  · rw [oddStripIntegrand_eq_zero_of_im_le hφ (not_le.1 hz2).le, norm_zero]
    exact mul_nonneg hK0 (norm_nonneg _)

theorem integrableOn_oddStripIntegrand (hφ : IsHeightProfile φ) {s : ℂ} (hs : s ≠ 1) :
    IntegrableOn (oddStripIntegrand φ s) modularStrip volume := by
  obtain ⟨K, hK⟩ := exists_oddStripIntegrand_bound hφ hs
  exact Integrable.mono' ((integrableOn_indicator_im_ge_modularStrip (c := 2) (by norm_num)).norm.const_mul K)
    (continuous_oddStripIntegrand hφ s).aestronglyMeasurable (Eventually.of_forall fun z => hK z)

/-- **The pairing of an odd cusp field unfolds to the strip.** For `s ≠ 1`,
`∫_𝒟 G_φ² E*(s − ½) = ∫_0^∞ φ(y)² W_s(y) dy/y²`, with an integrable integrand. -/
theorem pairing_oddCuspField (hφ : IsHeightProfile φ) {s : ℂ} (hs : s ≠ 1) :
    IntegrableOn (fun y : ℝ => ((φ y ^ 2 / y ^ 2 : ℝ) : ℂ) * horocycleProfile s y) (Ioi 0) ∧
      pairing s (fun z => (oddCuspField φ z : ℂ)) (fun z => (oddCuspField φ z : ℂ)) =
        ∫ y in Ioi (0 : ℝ), ((φ y ^ 2 / y ^ 2 : ℝ) : ℂ) * horocycleProfile s y := by
  have hP := integrableOn_oddStripIntegrand hφ hs
  have hinner : ∀ y : ℝ, 0 < y →
      (y ^ 2)⁻¹ • ∫ x in Ico (0 : ℝ) 1, oddStripIntegrand φ s (ofComplex ⟨x, y⟩) =
        ((φ y ^ 2 / y ^ 2 : ℝ) : ℂ) * horocycleProfile s y := by
    intro y hy
    have e : ∀ x : ℝ, oddStripIntegrand φ s (ofComplex ⟨x, y⟩) = ((φ y ^ 2 : ℝ) : ℂ) *
        (((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) * EisAuto.completedEisenstein (s - 1 / 2) x y) := by
      intro x
      have hc : ofComplex (⟨x, y⟩ : ℂ) = ⟨⟨x, y⟩, hy⟩ := UpperHalfPlane.ofComplex_apply_of_im_pos hy
      have hp : oddProfile φ (⟨x, y⟩ : ℂ) = φ y * Real.sin (2 * Real.pi * x) := rfl
      rw [oddStripIntegrand, hc]
      change ((oddProfile φ (⟨x, y⟩ : ℂ) ^ 2 : ℝ) : ℂ) * EisAuto.completedEisenstein (s - 1 / 2) x y = _
      rw [hp]
      push_cast; ring
    simp_rw [e]
    rw [integral_const_mul, horocycleProfile, Complex.real_smul]
    push_cast; ring
  have hfd : pairing s (fun z => (oddCuspField φ z : ℂ)) (fun z => (oddCuspField φ z : ℂ)) =
      ∫ z in ModularGroup.fd, oddStripIntegrand φ s z := by
    unfold pairing
    refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z hz => ?_
    have hG := oddCuspField_of_half_lt hφ (OddCusp.half_lt_im_of_mem_fd hz)
    simp only [pairIntegrand, oddStripIntegrand, hG, Complex.conj_ofReal]
    push_cast; ring
  have hstrip := setIntegral_fd_eq_strip_of_high (oddStripIntegrand_T hs) hP
    (fun z hz => oddStripIntegrand_eq_zero_of_im_le hφ (by linarith))
  have hiter := setIntegral_modularStrip_eq_iterated _ hP
  have hint : IntegrableOn (fun y : ℝ => ((φ y ^ 2 / y ^ 2 : ℝ) : ℂ) * horocycleProfile s y) (Ioi 0) := by
    have h1 := (integrableOn_modularStrip_iff _).mp hP
    rw [Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at h1
    refine h1.integral_prod_left.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simp only [stripChartIntegrand]
    rw [integral_smul]
    exact hinner y hy
  refine ⟨hint, ?_⟩
  rw [hfd, hstrip, hiter]
  exact setIntegral_congr_fun measurableSet_Ioi fun y hy => hinner y hy

/-! ### Tents high in the cusp -/

/-- The tent of height `½` on `[j + 3, j + 4]`. -/
def tent (j : ℕ) (y : ℝ) : ℝ := max 0 (1 / 2 - |y - (j + 7 / 2)|)

theorem tent_eq_zero {j : ℕ} {y : ℝ} (hy : y ≤ j + 3 ∨ j + 4 ≤ y) : tent j y = 0 := by
  refine max_eq_left ?_
  rcases hy with hy | hy
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem tent_pos {j : ℕ} {y : ℝ} (hy : y ∈ Ioo ((j : ℝ) + 3) (j + 4)) : 0 < tent j y := by
  refine lt_max_of_lt_right ?_
  have : |y - (j + 7 / 2)| < 1 / 2 := abs_lt.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
  linarith

theorem tent_le (j : ℕ) (y : ℝ) : |tent j y| ≤ 1 / 2 := by
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le (by norm_num) (by linarith [abs_nonneg (y - (j + 7 / 2))])

theorem isHeightProfile_tent (j : ℕ) : IsHeightProfile (tent j) where
  continuous := continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).abs))
  low y hy := tent_eq_zero (Or.inl (by have := j.cast_nonneg (α := ℝ); linarith))
  high := ⟨(j : ℝ) + 4, fun _ hy => tent_eq_zero (Or.inr hy)⟩

/-- `Re(e^{iψ} y^{1−s}) = y^{1−σ} cos(ψ − τ log y)` for `y > 0` and `s = σ + iτ`. -/
theorem re_exp_mul_cpow {y : ℝ} (hy : 0 < y) (ψ : ℝ) (s : ℂ) :
    (Complex.exp ((ψ : ℂ) * I) * (y : ℂ) ^ (1 - s)).re = y ^ (1 - s.re) * Real.cos (ψ - s.im * Real.log y) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Complex.cpow_def_of_ne_zero hy', ← Complex.ofReal_log hy.le, ← Complex.exp_add, Complex.exp_re,
    Real.rpow_def_of_pos hy]
  congr 2
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring

/-- `|log c − log y| ≤ 1/a` for `a < y < a + 1` and `c = a + ½`. -/
theorem abs_log_sub_log_le {a y : ℝ} (ha : 0 < a) (hy : y ∈ Ioo a (a + 1)) :
    |Real.log (a + 1 / 2) - Real.log y| ≤ 1 / a := by
  have hy0 : 0 < y := ha.trans hy.1
  have hc0 : 0 < a + 1 / 2 := by linarith
  have h1 : Real.log (a + 1 / 2) - Real.log y ≤ (a + 1 / 2) / y - 1 := by
    rw [← Real.log_div hc0.ne' hy0.ne']; exact Real.log_le_sub_one_of_pos (div_pos hc0 hy0)
  have h2 : Real.log y - Real.log (a + 1 / 2) ≤ y / (a + 1 / 2) - 1 := by
    rw [← Real.log_div hy0.ne' hc0.ne']; exact Real.log_le_sub_one_of_pos (div_pos hy0 hc0)
  have h3 : (a + 1 / 2) / y - 1 ≤ 1 / a := by
    rw [div_sub_one hy0.ne', div_le_div_iff₀ hy0 ha]
    nlinarith [mul_pos ha (sub_pos.2 hy.1)]
  have h4 : y / (a + 1 / 2) - 1 ≤ 1 / a := by
    rw [div_sub_one hc0.ne', div_le_div_iff₀ hc0 ha]
    nlinarith [mul_pos ha (sub_pos.2 hy.1), mul_lt_mul_of_pos_left (show y - a < 1 by linarith [hy.2]) ha]
  rw [abs_le]; constructor <;> linarith

/-- The tent energy `d_j(s) = ∫_𝒟 G_{φ_j}² E*(s − ½)`. -/
def tentEnergy (s : ℂ) (j : ℕ) : ℂ :=
  pairing s (fun z => (oddCuspField (tent j) z : ℂ)) (fun z => (oddCuspField (tent j) z : ℂ))

/-- **The phase law of the tent energies.** Let `ζ(ρ) = 0`, `Re ρ > 0`, `s = ρ/2 = σ + iτ` and `κ = κ(s − ½)`.
Far up the cusp, `Re(e^{iθ} d_j(s)) ≥ |κ|/2048 · (j + 3)^{−1−σ}` whenever `cos(θ + arg κ − τ log(j + 7/2)) ≥ ¾`.
On the tent `[j + 3, j + 4]` the profile is `½κ y^{1−s}` plus a tail bounded by `C`; the phase of `y^{1−s}`
moves by at most `|τ|/(j + 3) ≤ ½` and its size `y^{1−σ}` exceeds `16C/|κ|`, so
`Re(e^{iθ} W_s) ≥ |κ| y^{1−σ}/16` there; the tent is at least `¼` on its middle half. -/
theorem exists_tent_phase {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ θ : ℝ,
      3 / 4 ≤ Real.cos (θ + (resonanceCoefficient (ρ / 2 - 1 / 2)).arg - (ρ / 2).im * Real.log (j + 7 / 2)) →
      ‖resonanceCoefficient (ρ / 2 - 1 / 2)‖ / 2048 * ((j : ℝ) + 3) ^ (-1 - (ρ / 2).re) ≤
        (Complex.exp ((θ : ℂ) * I) * tentEnergy (ρ / 2) j).re := by
  obtain ⟨hres, h1, h2, h3, hκ, hlt⟩ := resonance_data hζ hpos
  set s : ℂ := ρ / 2 with hs_def
  set κ := resonanceCoefficient (s - 1 / 2)
  have hsre : s.re = ρ.re / 2 := by rw [hs_def]; simp
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  have hσ : 0 < 1 - s.re := by rw [hsre]; linarith
  have hκ0 : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  obtain ⟨C, hC0, hC⟩ := exists_tail_bound (s - 1 / 2)
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop
  obtain ⟨J, hJ⟩ := eventually_atTop.1 ((((tendsto_rpow_atTop hσ).comp ht).eventually_gt_atTop
    (16 * C / ‖κ‖)).and (ht.eventually_ge_atTop (2 * |s.im|)))
  refine ⟨J, fun j hj θ hθ => ?_⟩
  obtain ⟨hj1, hj2⟩ := hJ j hj
  simp only [Function.comp] at hj1
  set a : ℝ := (j : ℝ) + 3 with ha_def
  have ha0 : 0 < a := by positivity
  have ha3 : 3 ≤ a := by rw [ha_def]; linarith [j.cast_nonneg (α := ℝ)]
  have hc : (j : ℝ) + 7 / 2 = a + 1 / 2 := by rw [ha_def]; ring
  rw [hc] at hθ
  set ω : ℂ := Complex.exp ((θ : ℂ) * I)
  have hω : ‖ω‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  obtain ⟨hint, hpair⟩ := pairing_oddCuspField (isHeightProfile_tent j) hs1
  -- `ω W(y)` lies in the right half-plane on `(a, a + 1)`
  have hW : ∀ y ∈ Ioo a (a + 1), ‖κ‖ / 16 * a ^ (1 - s.re) ≤ (ω * horocycleProfile s y).re := by
    intro y hy
    have hy0 : 0 < y := ha0.trans hy.1
    set T := ∫ x in Ico (0 : ℝ) 1, ((Real.sin (2 * Real.pi * x) ^ 2 : ℝ) : ℂ) * eisTail (s - 1 / 2) x y
    rw [horocycleProfile_eq_of_resonance hres h1 h2 h3 hy0, mul_add, Complex.add_re]
    have hmain : (ω * (1 / 2 * κ * (y : ℂ) ^ (1 - s))).re =
        1 / 2 * ‖κ‖ * (y ^ (1 - s.re) * Real.cos (θ + κ.arg - s.im * Real.log y)) := by
      have e1 : ω * (1 / 2 * κ * (y : ℂ) ^ (1 - s)) =
          ((1 / 2 * ‖κ‖ : ℝ) : ℂ) * (Complex.exp (((θ + κ.arg : ℝ) : ℂ) * I) * (y : ℂ) ^ (1 - s)) := by
        have hk := Complex.norm_mul_exp_arg_mul_I κ
        have hexp : Complex.exp (((θ + κ.arg : ℝ) : ℂ) * I) =
            ω * Complex.exp ((κ.arg : ℂ) * I) := by
          rw [← Complex.exp_add]; push_cast; ring_nf
        rw [hexp]
        push_cast
        linear_combination (-(1 / 2) * ω * (y : ℂ) ^ (1 - s)) * hk
      rw [e1, Complex.re_ofReal_mul, re_exp_mul_cpow hy0]
    have hcos : 1 / 4 ≤ Real.cos (θ + κ.arg - s.im * Real.log y) := by
      have hD := abs_log_sub_log_le ha0 hy
      have hd : |(θ + κ.arg - s.im * Real.log y) - (θ + κ.arg - s.im * Real.log (a + 1 / 2))| ≤ 1 / 2 := by
        rw [show (θ + κ.arg - s.im * Real.log y) - (θ + κ.arg - s.im * Real.log (a + 1 / 2)) =
          s.im * (Real.log (a + 1 / 2) - Real.log y) by ring, abs_mul]
        calc |s.im| * |Real.log (a + 1 / 2) - Real.log y| ≤ (a / 2) * (1 / a) :=
              mul_le_mul (by linarith) hD (abs_nonneg _) (by positivity)
          _ = 1 / 2 := by field_simp
      have := Real.abs_cos_sub_cos_le (θ + κ.arg - s.im * Real.log y) (θ + κ.arg - s.im * Real.log (a + 1 / 2))
      linarith [(abs_le.1 (this.trans hd)).1]
    have htail : -C ≤ (ω * T).re := by
      have h := Complex.abs_re_le_norm (ω * T)
      rw [norm_mul, hω, one_mul] at h
      linarith [(abs_le.1 h).1, hC y (by linarith [hy.1])]
    have hay : a ^ (1 - s.re) ≤ y ^ (1 - s.re) := Real.rpow_le_rpow ha0.le hy.1.le hσ.le
    have hpow : 16 * C < y ^ (1 - s.re) * ‖κ‖ := (div_lt_iff₀ hκ0).1 (lt_of_lt_of_le hj1 hay)
    have hP : 0 < y ^ (1 - s.re) := Real.rpow_pos_of_pos hy0 _
    rw [hmain]
    nlinarith [mul_nonneg (sub_nonneg.2 hcos) (by positivity : 0 ≤ ‖κ‖ * y ^ (1 - s.re)),
      mul_le_mul_of_nonneg_left hay hκ0.le]
  -- the rotated energy is positive
  set f : ℝ → ℝ := fun y => (ω * (((tent j y ^ 2 / y ^ 2 : ℝ) : ℂ) * horocycleProfile s y)).re
  have hf : ∀ y, f y = tent j y ^ 2 / y ^ 2 * (ω * horocycleProfile s y).re := by
    intro y
    simp only [f]
    rw [show ω * (((tent j y ^ 2 / y ^ 2 : ℝ) : ℂ) * horocycleProfile s y) =
      ((tent j y ^ 2 / y ^ 2 : ℝ) : ℂ) * (ω * horocycleProfile s y) by ring, Complex.re_ofReal_mul]
  have hfi : IntegrableOn f (Ioi 0) := (hint.const_mul ω).re
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    refine Eventually.of_forall fun y => ?_
    rw [hf]
    by_cases hy : y ∈ Ioo a (a + 1)
    · exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
        ((by positivity : (0 : ℝ) ≤ ‖κ‖ / 16 * a ^ (1 - s.re)).trans (hW y hy))
    · have h0 : tent j y = 0 := tent_eq_zero (by
        simp only [mem_Ioo, not_and_or, not_lt] at hy
        rcases hy with hy | hy
        · left; linarith
        · right; linarith)
      simp [h0]
  -- the tent is at least `¼` on its middle half
  have hsub : Icc (a + 1 / 4) (a + 3 / 4) ⊆ Ioi (0 : ℝ) := fun y hy => by
    show (0 : ℝ) < y; linarith [hy.1]
  have hlow : ∀ y ∈ Icc (a + 1 / 4) (a + 3 / 4),
      1 / 16 * (1 / (a + 1) ^ 2) * (‖κ‖ / 16 * a ^ (1 - s.re)) ≤ f y := by
    intro y hy
    have hyI : y ∈ Ioo a (a + 1) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hy0 : 0 < y := ha0.trans hyI.1
    have ht : 1 / 4 ≤ tent j y := by
      have : |y - ((j : ℝ) + 7 / 2)| ≤ 1 / 4 :=
        abs_le.2 ⟨by linarith [hy.1, ha_def], by linarith [hy.2, ha_def]⟩
      exact le_max_of_le_right (by linarith)
    have ht2 : 1 / 16 ≤ tent j y ^ 2 := by nlinarith
    have hy2 : 1 / (a + 1) ^ 2 ≤ 1 / y ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hy0.le hyI.2.le 2)
    rw [hf, div_eq_mul_one_div (tent j y ^ 2)]
    have hk0 : 0 ≤ ‖κ‖ / 16 * a ^ (1 - s.re) := by positivity
    exact mul_le_mul (mul_le_mul ht2 hy2 (by positivity) (sq_nonneg _)) (hW y hyI) hk0
      (mul_nonneg (sq_nonneg _) (by positivity))
  have hge := setIntegral_ge_of_const_le measurableSet_Icc (by simp [Real.volume_Icc]) hlow
    (hfi.mono_set hsub)
  rw [Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hge
  have hmono : ∫ y in Icc (a + 1 / 4) (a + 3 / 4), f y ≤ ∫ y in Ioi (0 : ℝ), f y :=
    setIntegral_mono_set hfi hnn hsub.eventuallyLE
  have hre : (ω * tentEnergy s j).re = ∫ y in Ioi (0 : ℝ), f y := by
    rw [tentEnergy, hpair, ← integral_const_mul]
    have := integral_re (hint.const_mul ω)
    simp only [RCLike.re_to_complex] at this
    rw [this]
  rw [hre]
  refine le_trans ?_ (hge.trans hmono)
  have hP : 0 < a ^ (1 - s.re) := Real.rpow_pos_of_pos ha0 _
  have hexp : a ^ (-1 - s.re) = a ^ (1 - s.re) / a ^ 2 := by
    rw [show (-1 - s.re) = (1 - s.re) - 2 by ring, Real.rpow_sub ha0, Real.rpow_two]
  have h4 : 1 / (4 * a ^ 2) ≤ 1 / (a + 1) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  rw [hexp]
  calc ‖κ‖ / 2048 * (a ^ (1 - s.re) / a ^ 2) = ‖κ‖ * a ^ (1 - s.re) / 512 * (1 / (4 * a ^ 2)) := by
        field_simp; ring
    _ ≤ ‖κ‖ * a ^ (1 - s.re) / 512 * (1 / (a + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (a + 3 / 4 - (a + 1 / 4)) * (1 / 16 * (1 / (a + 1) ^ 2) * (‖κ‖ / 16 * a ^ (1 - s.re))) := by ring

/-- The phase law gives positivity: `Re(e^{iθ} d_j(s)) > 0` far up the cusp. -/
theorem exists_tent_phase_pos {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ θ : ℝ,
      3 / 4 ≤ Real.cos (θ + (resonanceCoefficient (ρ / 2 - 1 / 2)).arg - (ρ / 2).im * Real.log (j + 7 / 2)) →
      0 < (Complex.exp ((θ : ℂ) * I) * tentEnergy (ρ / 2) j).re := by
  obtain ⟨-, -, -, -, hκ, -⟩ := resonance_data hζ hpos
  obtain ⟨J, hJ⟩ := exists_tent_phase hζ hpos
  refine ⟨J, fun j hj θ hθ => lt_of_lt_of_le ?_ (hJ j hj θ hθ)⟩
  have : 0 < ‖resonanceCoefficient (ρ / 2 - 1 / 2)‖ := norm_pos_iff.2 hκ
  positivity

/-- **Size of the tent energies.** At a resonance `s = ρ/2`, `|d_j(s)| ≤ U (j + 3)^{−1−Re s}` for every `j`:
on the tent, `|W_s(y)| ≤ ½|κ| y^{1−Re s} + C`. -/
theorem exists_tentEnergy_le {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    ∃ U : ℝ, ∀ j : ℕ, ‖tentEnergy (ρ / 2) j‖ ≤ U * ((j : ℝ) + 3) ^ (-1 - (ρ / 2).re) := by
  obtain ⟨hres, h1, h2, h3, -, hlt⟩ := resonance_data hζ hpos
  set s : ℂ := ρ / 2 with hs_def
  set κ := resonanceCoefficient (s - 1 / 2)
  have hsre : s.re = ρ.re / 2 := by rw [hs_def]; simp
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  have hσ : 0 ≤ 1 - s.re := by rw [hsre]; linarith
  have hσ1 : 1 - s.re ≤ 1 := by rw [hsre]; linarith
  obtain ⟨C, hC0, hC⟩ := exists_tail_bound (s - 1 / 2)
  refine ⟨(‖κ‖ + C) / 4, fun j => ?_⟩
  set a : ℝ := (j : ℝ) + 3 with ha_def
  have ha1 : 1 ≤ a := by rw [ha_def]; linarith [j.cast_nonneg (α := ℝ)]
  have ha0 : 0 < a := by linarith
  obtain ⟨-, hpair⟩ := pairing_oddCuspField (isHeightProfile_tent j) hs1
  set F : ℝ → ℂ := fun y => ((tent j y ^ 2 / y ^ 2 : ℝ) : ℂ) * horocycleProfile s y
  have hzero : ∀ y ∈ Ioi (0 : ℝ) \ Ioo a (a + 1), F y = 0 := by
    intro y hy
    have hy2 : y ∉ Ioo a (a + 1) := hy.2
    have h0 : tent j y = 0 := tent_eq_zero (by
      simp only [mem_Ioo, not_and_or, not_lt] at hy2
      rcases hy2 with hy2 | hy2
      · left; linarith
      · right; linarith)
    simp [F, h0]
  have hB : ∀ y ∈ Ioo a (a + 1), ‖F y‖ ≤ 1 / 4 * (1 / a ^ 2) * (1 / 2 * ‖κ‖ * (a + 1) ^ (1 - s.re) + C) := by
    intro y hy
    have hy0 : 0 < y := ha0.trans hy.1
    have hW : ‖horocycleProfile s y‖ ≤ 1 / 2 * ‖κ‖ * (a + 1) ^ (1 - s.re) + C := by
      rw [horocycleProfile_eq_of_resonance hres h1 h2 h3 hy0]
      refine (norm_add_le _ _).trans (add_le_add ?_ (hC y (by linarith [hy.1])))
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, show (1 - s).re = 1 - s.re by simp]
      have : y ^ (1 - s.re) ≤ (a + 1) ^ (1 - s.re) := Real.rpow_le_rpow hy0.le hy.2.le hσ
      have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [hn]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have ht : tent j y ^ 2 ≤ 1 / 4 := by
      have := tent_le j y
      nlinarith [abs_nonneg (tent j y), sq_abs (tent j y)]
    have hy2 : 1 / y ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ ha0.le hy.1.le 2)
    simp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)),
      div_eq_mul_one_div (tent j y ^ 2)]
    exact mul_le_mul (mul_le_mul ht hy2 (by positivity) (by norm_num)) hW (norm_nonneg _)
      (by positivity)
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioo_lt_top hB
  rw [measureReal_def, Real.volume_Ioo, show a + 1 - a = 1 by ring, ENNReal.toReal_ofReal zero_le_one,
    mul_one] at hI
  rw [tentEnergy, hpair, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun y hy => ha0.trans hy.1) hzero]
  refine hI.trans ?_
  have hP1 : 1 ≤ a ^ (1 - s.re) := Real.one_le_rpow ha1 hσ
  have h2a : (a + 1) ^ (1 - s.re) ≤ 2 * a ^ (1 - s.re) := by
    calc (a + 1) ^ (1 - s.re) ≤ (2 * a) ^ (1 - s.re) := Real.rpow_le_rpow (by linarith) (by linarith) hσ
      _ = 2 ^ (1 - s.re) * a ^ (1 - s.re) := Real.mul_rpow (by norm_num) ha0.le
      _ ≤ 2 * a ^ (1 - s.re) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (2 : ℝ) ^ (1 - s.re) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
            _ = 2 := Real.rpow_one 2
  have hexp : a ^ (-1 - s.re) = a ^ (1 - s.re) / a ^ 2 := by
    rw [show (-1 - s.re) = (1 - s.re) - 2 by ring, Real.rpow_sub ha0, Real.rpow_two]
  rw [hexp]
  have hκ0 := norm_nonneg κ
  calc 1 / 4 * (1 / a ^ 2) * (1 / 2 * ‖κ‖ * (a + 1) ^ (1 - s.re) + C)
      ≤ 1 / 4 * (1 / a ^ 2) * (1 / 2 * ‖κ‖ * (2 * a ^ (1 - s.re)) + C * a ^ (1 - s.re)) := by
        gcongr
        nlinarith
    _ = (‖κ‖ + C) / 4 * (a ^ (1 - s.re) / a ^ 2) := by ring

/-- **Every resonance is seen by a tent field.** For every zero `ρ` of `ζ` with `Re ρ > 0` some tent `φ_j` has
`∫_𝒟 G_{φ_j}² E*(ρ/2 − ½) ≠ 0`: take the rotation that aligns the main term in the phase law. -/
theorem exists_tent_seeing {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    ∃ j : ℕ, tentEnergy (ρ / 2) j ≠ 0 := by
  obtain ⟨J, hJ⟩ := exists_tent_phase_pos hζ hpos
  refine ⟨J, fun h0 => ?_⟩
  have := hJ J le_rfl ((ρ / 2).im * Real.log (J + 7 / 2) - (resonanceCoefficient (ρ / 2 - 1 / 2)).arg)
    (by rw [show (ρ / 2).im * Real.log (J + 7 / 2) - (resonanceCoefficient (ρ / 2 - 1 / 2)).arg +
      (resonanceCoefficient (ρ / 2 - 1 / 2)).arg - (ρ / 2).im * Real.log (J + 7 / 2) = 0 by ring,
      Real.cos_zero]; norm_num)
  rw [h0, mul_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

/-! ### The odd cavity -/

/-- The envelope constant of the tent field `G_j`. -/
def tentMass (j : ℕ) : ℝ := (exists_envelope_oddCuspField (isHeightProfile_tent j)).choose

theorem tentMass_pos (j : ℕ) : 0 < tentMass j :=
  (exists_envelope_oddCuspField (isHeightProfile_tent j)).choose_spec.1

/-- The odd cavity family `u_j = G_{φ_j} / M_j` of normalized tent fields. -/
def oddFamily (j : ℕ) (z : ℍ) : ℂ := ((tentMass j : ℂ))⁻¹ * (oddCuspField (tent j) z : ℂ)

theorem isCavityFamily_oddFamily : IsCavityFamily oddFamily Real.pi where
  pos := Real.pi_pos
  invariant j γ z := by
    show ((tentMass j : ℂ))⁻¹ * (oddCuspField (tent j) (γ • z) : ℂ) = _
    rw [oddCuspField_smul (isHeightProfile_tent j)]
    rfl
  continuous j := continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_oddCuspField (isHeightProfile_tent j)))
  envelope j z := by
    have hb := (exists_envelope_oddCuspField (isHeightProfile_tent j)).choose_spec.2 z
    have hM := tentMass_pos j
    rw [oddFamily, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM.le, inv_mul_le_iff₀ hM]
    exact hb

theorem pairEntry_oddFamily (s : ℂ) (j : ℕ) :
    pairEntry oddFamily s j j = ((tentMass j : ℂ))⁻¹ * ((tentMass j : ℂ))⁻¹ * tentEnergy s j := by
  unfold pairEntry tentEnergy pairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [pairIntegrand, oddFamily, map_mul, map_inv₀, Complex.conj_ofReal]
  ring

theorem cavity_oddFamily_mirror (x : ℕ →ᵇ ℂ) (z : ℍ) :
    cavity oddFamily x (mirror z) = -cavity oddFamily x z := by
  have h : ∀ j, oddFamily j (mirror z) = -oddFamily j z := fun j => by
    rw [oddFamily, oddFamily, oddCuspField_mirror (isHeightProfile_tent j)]; push_cast; ring
  simp only [cavity, h, mul_neg, tsum_neg]

/-- **Every odd cavity function is cuspidal**: it is mirror-odd, so its horocycle means vanish. -/
theorem response_cavity_oddFamily (x : ℕ →ᵇ ℂ) {y : ℝ} (hy : 0 < y) :
    response (cavity oddFamily x) y = 0 := by
  have h := OddCusp.horocycle_mean_eq_zero_of_odd (f := cavity oddFamily x)
    (fun A z => (isSeed_cavity isCavityFamily_oddFamily x).invariant A z) (cavity_oddFamily_mirror x) hy 0
  rw [zero_add] at h
  rw [response, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, ← h]
  refine intervalIntegral.integral_congr fun t _ => ?_
  show cavity oddFamily x (ofComplex ⟨t, y⟩) = cavity oddFamily x (OddCusp.cuspPoint t y hy)
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hy]
  rfl

/-- **B109 in the cavity: one odd cavity function sees every resonance.** The coefficient vectors `x` for
which the energy `|g_x|²` of the mirror-odd cuspidal function `g_x = Σ x_j 2^{−j} G_j / M_j` has
`Λ_{|g_x|²}(ρ/2) ≠ 0` at every zero `ρ` of `ζ` with `Re ρ > ½` are dense. -/
theorem dense_odd_cavity_seeing :
    Dense (⋂ s ∈ rightResonances, {x : ℕ →ᵇ ℂ | pairForm oddFamily s x x ≠ 0}) := by
  refine dense_cavity_seeing isCavityFamily_oddFamily countable_rightResonances
    (fun s hs => rightResonances_ne hs) fun s hs => ?_
  obtain ⟨ρ, ⟨hζ, hρ⟩, rfl⟩ := hs
  obtain ⟨j, hj⟩ := exists_tent_seeing hζ (by linarith)
  refine ⟨j, j, ?_⟩
  rw [pairEntry_oddFamily]
  have hM : ((tentMass j : ℂ)) ≠ 0 := by exact_mod_cast (tentMass_pos j).ne'
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero hM) (inv_ne_zero hM)) hj

theorem exists_odd_cavity_seeing_every_right_zero :
    ∃ x : ℕ →ᵇ ℂ, ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re →
      seedTransform (fun z => ((‖cavity oddFamily x z‖ ^ 2 : ℝ) : ℂ)) (ρ / 2) ≠ 0 := by
  refine (cavity_sees_every_right_zero_iff isCavityFamily_oddFamily).2 fun ρ hζ hρ => ?_
  obtain ⟨j, hj⟩ := exists_tent_seeing hζ (by linarith)
  refine ⟨j, j, ?_⟩
  rw [pairEntry_oddFamily]
  have hM : ((tentMass j : ℂ)) ≠ 0 := by exact_mod_cast (tentMass_pos j).ne'
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero hM) (inv_ne_zero hM)) hj

/-- **The odd cavity is a complete receiver.** There is a continuous, modular, mirror-odd function `g` with
`|g| ≤ C e^{−π Im z}` and zero mean on every closed horocycle such that a horocycle rate
`|a_{|g|²}(y) − c| ≤ C y^α` on `(0, 1]` for its energy forces `Re ρ ≤ 2 − 2α` at every zero `ρ` of `ζ` with
`Re ρ > ½`. Rate `y^{½+δ}` is a zero-free strip; rate `y^{3/4}` leaves no zero right of the critical line. -/
theorem exists_odd_cavity_receiver :
    ∃ x : ℕ →ᵇ ℂ, IsSeed (cavity oddFamily x) ∧
      (∀ z, cavity oddFamily x (mirror z) = -cavity oddFamily x z) ∧
      (∀ y : ℝ, 0 < y → response (cavity oddFamily x) y = 0) ∧
      ∀ (α : ℝ) (c : ℂ) (C : ℝ), (∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖response (fun z => ((‖cavity oddFamily x z‖ ^ 2 : ℝ) : ℂ)) y - c‖ ≤ C * y ^ α) →
        ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re ≤ 2 - 2 * α := by
  obtain ⟨x, hx⟩ := exists_odd_cavity_seeing_every_right_zero
  exact ⟨x, isSeed_cavity isCavityFamily_oddFamily x, cavity_oddFamily_mirror x,
    fun y hy => response_cavity_oddFamily x hy,
    fun α c C hrate ρ hζ hρ => re_le_of_cavity_rate isCavityFamily_oddFamily hx hrate hζ hρ⟩

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
