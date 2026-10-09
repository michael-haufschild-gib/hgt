import GaloisForLFunctions.HTGeometry.HalfLineMellinUnitary
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionMellin
import GaloisForLFunctions.RHTower.PrimeBlindCarlsonThreshold
import GaloisForLFunctions.RHTower.ZetaVerticalSqrtBound
import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenInequality
import GaloisForLFunctions.RHTower.BoundedSupportFourierUncertainty
import GaloisForLFunctions.RHTower.ChronologicalHeatMellin

/-!
# Integer dilates of the Bose defect are complete in `L²(0,∞)`

Let `β(t) = 1/t - 1/(e^t - 1)` and `β_k(t) = β(kt)`.  The chronological heat error of a row `a`
is `e^{-t} + Σ a_k β_k(t)`.

**Theorem** (`boseDilateL2_eq_zero_of_inner_eq_zero`, `boseDilateL2_span_dense`).  The integer
dilates `β_k`, `k ≥ 1`, are complete in `L²((0,∞), dt)`: a vector orthogonal to every `β_p`,
`p` prime, is zero.  Hence `e^{-t}` is a limit of finite combinations of the `β_k`, with no
hypothesis on the zeros of `ζ`.

**Proof.**  The Mellin unitary carries `β_k` to `-k^{-s} Γ(s) ζ(s)` on `Re s = 1/2`.  For `g`
orthogonal to every `β_p`, the function `w(t) = conj(Γζ)(1/2 - it) · (𝓜 g)(t/2π)` has vanishing
Dirichlet moments `∫ w(t) p^{-it} dt` at every prime.  Since `|Γ(1/2 + it)| ≤ √(2π) e^{-π|t|/2}`
and `ζ` grows at most linearly on the critical line, `w` decays at the Carlson rate `π/2` up to an
`L²` factor and a polynomial.  The Carlson theorem at the primes
(`fourier_eq_zero_of_primeMoment_eq_zero_room`) kills the Fourier transform of `w`, so `w = 0`.
The zeros of `ζ` on the line are countable, so `𝓜 g = 0` almost everywhere and `g = 0`.

Combined with `chronologicalL2Norm_offLine_floor`, the arithmetic content of the chronological
route is therefore not completeness but the size of the coefficients: arbitrary rows approximate
`e^{-t}` unconditionally, while rows bounded by a fixed constant approximate it only if RH holds.
The Gamma factor decays exactly at the rate `π/2` at which `log ℕ` stops being a uniqueness set.
-/

open MeasureTheory Set Filter Complex
open scoped Topology ENNReal FourierTransform ComplexConjugate InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The dilated Bose defect `t ↦ β(kt)`, complex valued. -/
def boseDilate (k : ℕ) (t : ℝ) : ℂ := (fusionBoseDefect ((k : ℝ) * t) : ℂ)

theorem memLp_boseDilate {k : ℕ} (hk : 1 ≤ k) :
    MemLp (boseDilate k) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (chronological_memLp_dilate chronologicalBose_memLp chronologicalBose_continuousOn
    (d := (k : ℝ)) (by exact_mod_cast hk)).ofReal

/-- `β_{k+1}` as a vector of `L²((0,∞))`. -/
def boseDilateL2 (k : ℕ) : HalfLineL2 :=
  (memLp_boseDilate (Nat.le_add_left 1 k)).toLp (boseDilate (k + 1))

theorem continuous_halfDensityPullback_boseDilate {k : ℕ} (hk : 1 ≤ k) :
    Continuous (halfDensityPullback (boseDilate k)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hin : Continuous fun x : ℝ => fusionBoseDefect ((k : ℝ) * Real.exp x) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hpos : (0 : ℝ) < (k : ℝ) * Real.exp x := mul_pos hk0 (Real.exp_pos x)
    have hc := (chronologicalBose_continuousOn.continuousAt (Ioi_mem_nhds hpos))
    have hm : ContinuousAt (fun y : ℝ => (k : ℝ) * Real.exp y) x :=
      (continuous_const.mul Real.continuous_exp).continuousAt
    exact ContinuousAt.comp (f := fun y : ℝ => (k : ℝ) * Real.exp y) hc hm
  unfold halfDensityPullback boseDilate
  exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Real.continuous_exp)).mul
    (Complex.continuous_ofReal.comp hin)

theorem norm_halfDensityPullback_boseDilate_le {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    ‖halfDensityPullback (boseDilate k) x‖ ≤ Real.exp (-(1 / 2 * |x|)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (k : ℝ) * Real.exp x := mul_pos (by linarith) (Real.exp_pos x)
  obtain ⟨h0, h1, h2⟩ := fusionBoseDefect_bounds ((k : ℝ) * Real.exp x)
  have hsq : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf
  unfold halfDensityPullback boseDilate
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg h0, hsq]
  rcases le_total x 0 with hx | hx
  · rw [abs_of_nonpos hx]
    calc Real.exp (x / 2) * fusionBoseDefect ((k : ℝ) * Real.exp x)
        ≤ Real.exp (x / 2) * 1 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (-(1 / 2 * -x)) := by ring_nf
  · rw [abs_of_nonneg hx]
    rw [abs_of_pos hpos] at h2
    have hkx : Real.exp x ≤ (k : ℝ) * Real.exp x := by nlinarith [Real.exp_pos x]
    calc Real.exp (x / 2) * fusionBoseDefect ((k : ℝ) * Real.exp x)
        ≤ Real.exp (x / 2) * (1 / ((k : ℝ) * Real.exp x)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ ≤ Real.exp (x / 2) * (1 / Real.exp x) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (Real.exp_pos x) hkx)
            (Real.exp_pos _).le
      _ = Real.exp (-(1 / 2 * x)) := by
          rw [one_div, ← Real.exp_neg, ← Real.exp_add]; ring_nf

theorem integrable_halfDensityPullback_boseDilate {k : ℕ} (hk : 1 ≤ k) :
    Integrable (halfDensityPullback (boseDilate k)) := by
  have hexp : Integrable fun x : ℝ => Real.exp (-(1 / 2 * |x|)) := by
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 8)
      (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 * |x|)
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    have hpos : 0 < 1 + x ^ 2 := by positivity
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    rw [show 8 * (1 + x ^ 2)⁻¹ * Real.exp (1 / 2 * |x|) =
      8 * Real.exp (1 / 2 * |x|) / (1 + x ^ 2) by field_simp]
    rw [le_div_iff₀ hpos]
    nlinarith [abs_nonneg x]
  exact hexp.mono' (continuous_halfDensityPullback_boseDilate hk).aestronglyMeasurable
    (Eventually.of_forall (norm_halfDensityPullback_boseDilate_le hk))

/-- The Mellin transform of `β_k` in the strip: `-k^{-s} Γ(s) ζ(s)`. -/
theorem mellin_boseDilate {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s ∈ fusionMellinStrip) :
    mellin (boseDilate k) s = -((k : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta s) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := mellin_comp_mul_left fusionBoseKernel s hk0
  have he : boseDilate k = fun t => fusionBoseKernel ((k : ℝ) * t) := rfl
  rw [he, h, fusionBoseKernel_mellin hs, smul_eq_mul]
  push_cast
  ring

/-- The critical-line parameter `s(ξ) = 1/2 - 2πiξ` of the Mellin unitary. -/
def mellinLinePoint (ξ : ℝ) : ℂ := 1 / 2 - 2 * Real.pi * ξ * Complex.I

theorem mellinLinePoint_mem_strip (ξ : ℝ) : mellinLinePoint ξ ∈ fusionMellinStrip := by
  constructor <;> simp [mellinLinePoint]; norm_num

theorem halfLineMellinUnitary_boseDilateL2 (k : ℕ) :
    (halfLineMellinUnitary (boseDilateL2 k) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) *
        Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)) := by
  have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have h := halfLineMellinUnitary_ae_eq_mellin (boseDilateL2 k) (boseDilate (k + 1))
    (MemLp.coeFn_toLp _) (integrable_halfDensityPullback_boseDilate hk)
  filter_upwards [h] with ξ hξ
  rw [hξ]
  exact mellin_boseDilate hk (mellinLinePoint_mem_strip ξ)

/-- `|Γ(1/2 + it) ζ(1/2 + it)| ≤ 18 √(2π) (1 + |t|) e^{-π|t|/2}`. -/
theorem norm_Gamma_mul_zeta_half_le (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I) * riemannZeta (1 / 2 + (t : ℂ) * Complex.I)‖ ≤
      18 * Real.sqrt (2 * Real.pi) * (1 + |t|) * Real.exp (-(Real.pi / 2 * |t|)) := by
  set s : ℂ := 1 / 2 + (t : ℂ) * Complex.I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have him : s.im = t := by simp [hs]
  -- Gamma
  have hG : ‖Complex.Gamma s‖ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2 * |t|)) := by
    have hsq := norm_Gamma_half_add_I_sq t
    have hcosh : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
      rw [Real.cosh_eq]
      rcases le_total 0 t with ht | ht
      · rw [abs_of_nonneg ht]; nlinarith [Real.exp_pos (-(Real.pi * t))]
      · rw [abs_of_nonpos ht]
        have : -(Real.pi * t) = Real.pi * -t := by ring
        rw [this]; nlinarith [Real.exp_pos (Real.pi * t)]
    have hcpos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
    have hle : ‖Complex.Gamma s‖ ^ 2 ≤
        (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2 * |t|))) ^ 2 := by
      rw [hsq, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
      rw [div_le_iff₀ hcpos]
      have he : ((2 : ℕ) : ℝ) * -(Real.pi / 2 * |t|) = -(Real.pi * |t|) := by push_cast; ring
      rw [he]
      have hmul : Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) = 1 := by
        rw [← Real.exp_add]; simp
      have hnn : 0 ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by positivity
      calc Real.pi = 2 * Real.pi * Real.exp (-(Real.pi * |t|)) *
            (Real.exp (Real.pi * |t|) / 2) := by
            rw [show 2 * Real.pi * Real.exp (-(Real.pi * |t|)) * (Real.exp (Real.pi * |t|) / 2) =
              Real.pi * (Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|)) by ring, hmul,
              mul_one]
        _ ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) * Real.cosh (Real.pi * t) :=
            mul_le_mul_of_nonneg_left hcosh hnn
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle
  -- zeta
  have hZ : ‖riemannZeta s‖ ≤ 18 * (1 + |t|) := by
    have hsep : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
      have h1 : |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
      have h2 : (s - 1).re = -(1 / 2) := by simp [hs]; norm_num
      rw [h2] at h1; norm_num at h1; linarith
    have hb := norm_riemannZeta_le_sqrt_norm_add_two_half (s := s) (by rw [hre])
      (by norm_num : (0 : ℝ) < 1 / 2) hsep
    have hsn : ‖s‖ ≤ 1 / 2 + |t| := by
      calc ‖s‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = 1 / 2 + |t| := by simp
    have hsqrt : Real.sqrt (‖s‖ + 2) ≤ 3 * (1 + |t|) := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [abs_nonneg t, norm_nonneg s]
    calc ‖riemannZeta s‖ ≤ (2 + 1 / (1 / 2) + 2) * Real.sqrt (‖s‖ + 2) := hb
      _ ≤ 6 * (3 * (1 + |t|)) := by norm_num; nlinarith [Real.sqrt_nonneg (‖s‖ + 2)]
      _ = 18 * (1 + |t|) := by ring
  rw [norm_mul]
  calc ‖Complex.Gamma s‖ * ‖riemannZeta s‖
      ≤ (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2 * |t|))) * (18 * (1 + |t|)) :=
        mul_le_mul hG hZ (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- `(1 + |t|)³ ≤ 11 e^{π|t|/2}`. -/
theorem one_add_abs_pow_three_le_exp (t : ℝ) :
    (1 + |t|) ^ 3 ≤ 11 * Real.exp (Real.pi / 2 * |t|) := by
  set u := |t| with hu
  have hu0 : 0 ≤ u := abs_nonneg t
  have hx : 3 / 2 * u ≤ Real.pi / 2 * u := by nlinarith [Real.pi_gt_three]
  have hexp : Real.exp (3 / 2 * u) ≤ Real.exp (Real.pi / 2 * u) := Real.exp_le_exp.mpr hx
  have hsum := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / 2 * u) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hsum
  norm_num at hsum
  nlinarith [hsum, hexp, hu0, sq_nonneg u, mul_nonneg hu0 (sq_nonneg u)]

open PrimeBlindCarlson in
theorem one_div_eleven_le_roomWeight_three (t : ℝ) : 1 / 11 ≤ roomWeight 3 t := by
  unfold roomWeight
  have hpos : 0 < 1 + |t| := by positivity
  rw [Real.rpow_neg hpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, div_le_div_iff₀ (by norm_num) (by positivity)]
  have := one_add_abs_pow_three_le_exp t
  linarith

theorem mellinLinePoint_eq (ξ : ℝ) :
    mellinLinePoint ξ = 1 / 2 + ((-(2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I := by
  simp [mellinLinePoint]; ring

theorem mellinLinePoint_re (ξ : ℝ) : (mellinLinePoint ξ).re = 1 / 2 := by
  simp [mellinLinePoint]

theorem mellinLinePoint_ne_one (ξ : ℝ) : mellinLinePoint ξ ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [mellinLinePoint_re] at this
  norm_num at this

theorem mellinLinePoint_injective : Function.Injective mellinLinePoint := by
  intro a b h
  have := congrArg Complex.im h
  simpa [mellinLinePoint, Real.pi_ne_zero] using this

theorem continuous_mellinLinePoint : Continuous mellinLinePoint := by
  unfold mellinLinePoint; fun_prop

theorem continuous_Gamma_mul_zeta_mellinLinePoint :
    Continuous fun ξ : ℝ =>
      Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ) := by
  rw [continuous_iff_continuousAt]
  intro ξ
  have hG : ContinuousAt Complex.Gamma (mellinLinePoint ξ) := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).continuousAt
    have := congrArg Complex.re h
    rw [mellinLinePoint_re] at this
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hZ : ContinuousAt riemannZeta (mellinLinePoint ξ) :=
    (differentiableAt_riemannZeta (mellinLinePoint_ne_one ξ)).continuousAt
  exact (hG.comp continuous_mellinLinePoint.continuousAt).mul
    (hZ.comp continuous_mellinLinePoint.continuousAt)

/-- The Carlson weight of a vector in Mellin coordinates: `conj(Γζ(s(ξ))) · (𝓜 g)(ξ)`. -/
def boseMellinWeight (g : HalfLineL2) (ξ : ℝ) : ℂ :=
  conj (Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)) *
    (halfLineMellinUnitary g : ℝ → ℂ) ξ

theorem stronglyMeasurable_boseMellinWeight (g : HalfLineL2) :
    StronglyMeasurable (boseMellinWeight g) :=
  ((Complex.continuous_conj.comp continuous_Gamma_mul_zeta_mellinLinePoint).stronglyMeasurable).mul
    (Lp.stronglyMeasurable _)

theorem norm_boseMellinWeight_le (g : HalfLineL2) (ξ : ℝ) :
    ‖boseMellinWeight g ξ‖ ≤ 18 * Real.sqrt (2 * Real.pi) * (1 + |2 * Real.pi * ξ|) *
      Real.exp (-(Real.pi / 2 * |2 * Real.pi * ξ|)) *
        ‖(halfLineMellinUnitary g : ℝ → ℂ) ξ‖ := by
  unfold boseMellinWeight
  rw [norm_mul, Complex.norm_conj, mellinLinePoint_eq]
  have h := norm_Gamma_mul_zeta_half_le (-(2 * Real.pi * ξ))
  rw [abs_neg] at h
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

open PrimeBlindCarlson in
theorem integrable_boseMellinWeight_room (g : HalfLineL2) :
    Integrable fun ξ => ‖boseMellinWeight g ξ‖ * roomWeight 3 (2 * Real.pi * ξ) := by
  set Mg : ℝ → ℂ := (halfLineMellinUnitary g : ℝ → ℂ) with hMg
  have hK1 : MemLp (fun ξ : ℝ => (1 + ‖ξ‖) ^ (-(2 : ℝ))) 2 volume := by
    refine (memLp_two_iff_integrable_sq
      (Measurable.aestronglyMeasurable (by fun_prop))).mpr ?_
    refine (integrable_one_add_norm (E := ℝ) (r := 4) (by norm_num)).congr
      (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    try norm_num
  have hK2 : MemLp (fun ξ => ‖Mg ξ‖) 2 volume := (Lp.memLp _).norm
  have hK : Integrable (fun ξ : ℝ => (1 + ‖ξ‖) ^ (-(2 : ℝ)) * ‖Mg ξ‖) := hK1.integrable_mul hK2
  refine (hK.const_mul (18 * Real.sqrt (2 * Real.pi))).mono'
    (((stronglyMeasurable_boseMellinWeight g).norm.mul
      (by unfold roomWeight; fun_prop : Measurable fun ξ : ℝ =>
        roomWeight 3 (2 * Real.pi * ξ)).stronglyMeasurable).aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  have hrw : 0 ≤ roomWeight 3 (2 * Real.pi * ξ) := roomWeight_nonneg _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hrw)]
  set x := |2 * Real.pi * ξ| with hx
  have hxξ : |ξ| ≤ x := by
    rw [hx, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [abs_nonneg ξ, Real.pi_gt_three]
  have hb := norm_boseMellinWeight_le g ξ
  rw [← hx] at hb
  have hroom : roomWeight 3 (2 * Real.pi * ξ) = Real.exp (Real.pi / 2 * x) * (1 + x) ^ (-(3 : ℝ)) := by
    unfold roomWeight; rw [hx]
  have hpos1 : 0 < 1 + x := by positivity
  have hpow : (1 + x) * (1 + x) ^ (-(3 : ℝ)) = (1 + x) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_one_add' hpos1.le (by norm_num)]; norm_num
  have hmono : (1 + x) ^ (-(2 : ℝ)) ≤ (1 + ‖ξ‖) ^ (-(2 : ℝ)) := by
    rw [Real.norm_eq_abs]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hexp : Real.exp (-(Real.pi / 2 * x)) * Real.exp (Real.pi / 2 * x) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖boseMellinWeight g ξ‖ * roomWeight 3 (2 * Real.pi * ξ)
      ≤ (18 * Real.sqrt (2 * Real.pi) * (1 + x) * Real.exp (-(Real.pi / 2 * x)) * ‖Mg ξ‖) *
          roomWeight 3 (2 * Real.pi * ξ) := mul_le_mul_of_nonneg_right hb hrw
    _ = 18 * Real.sqrt (2 * Real.pi) * ((1 + x) * (1 + x) ^ (-(3 : ℝ))) * ‖Mg ξ‖ *
          (Real.exp (-(Real.pi / 2 * x)) * Real.exp (Real.pi / 2 * x)) := by rw [hroom]; ring
    _ = 18 * Real.sqrt (2 * Real.pi) * ((1 + x) ^ (-(2 : ℝ)) * ‖Mg ξ‖) := by
          rw [hpow, hexp]; ring
    _ ≤ 18 * Real.sqrt (2 * Real.pi) * ((1 + ‖ξ‖) ^ (-(2 : ℝ)) * ‖Mg ξ‖) := by
          gcongr

theorem conj_natCast_cpow_neg_mellinLinePoint {n : ℕ} (hn : 0 < n) (ξ : ℝ) :
    conj ((n : ℂ) ^ (-mellinLinePoint ξ)) =
      cexp (-((Real.log n : ℝ) : ℂ) / 2) *
        cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * ((Real.log n : ℝ) : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg n)]; push_cast; rfl
  rw [cpow_def_of_ne_zero hn0, hlog, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [mellinLinePoint, map_mul, map_neg, map_sub, Complex.conj_ofReal, map_div₀, map_one,
    map_ofNat, Complex.conj_I]
  push_cast
  ring

/-- **Mellin form of the orthogonality relations.**  For `p ≥ 2`,
`⟪β_p, g⟫ = -p^{-1/2} ∫ conj(Γζ(s(ξ))) (𝓜 g)(ξ) e^{-2πiξ log p} dξ`. -/
theorem inner_boseDilateL2_eq {p : ℕ} (hp : 2 ≤ p) (g : HalfLineL2) :
    ⟪boseDilateL2 (p - 1), g⟫_ℂ =
      -cexp (-((Real.log p : ℝ) : ℂ) / 2) *
        ∫ ξ, boseMellinWeight g ξ *
          cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * ((Real.log p : ℝ) : ℂ)) := by
  have hk : p - 1 + 1 = p := by omega
  have hin : ∀ x y : ℂ, ⟪x, y⟫_ℂ = conj x * y := fun x y => by simp [mul_comm]
  rw [← halfLineMellinUnitary.inner_map_map, MeasureTheory.L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [halfLineMellinUnitary_boseDilateL2 (p - 1)] with ξ hξ
  rw [hin, hξ, hk, map_neg, map_mul, map_mul,
    conj_natCast_cpow_neg_mellinLinePoint (by omega : 0 < p) ξ]
  unfold boseMellinWeight
  rw [map_mul]
  ring

/-- **Completeness of the integer Bose dilates.**  A vector of `L²((0,∞))` orthogonal to every
prime dilate `β_p` is zero. -/
theorem boseDilateL2_eq_zero_of_inner_eq_zero {g : HalfLineL2}
    (hg : ∀ p : ℕ, p.Prime → ⟪boseDilateL2 (p - 1), g⟫_ℂ = 0) : g = 0 := by
  set W := boseMellinWeight g with hWdef
  have h2pi0 : 0 < 2 * Real.pi := by positivity
  have h2pi : 2 * Real.pi ≠ 0 := h2pi0.ne'
  set w : ℝ → ℂ := fun t => W (t / (2 * Real.pi)) with hwdef
  have hmomξ : ∀ p : ℕ, p.Prime →
      ∫ ξ, W ξ * cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * ((Real.log p : ℝ) : ℂ)) = 0 := by
    intro p hp
    have h := inner_boseDilateL2_eq hp.two_le g
    rw [hg p hp] at h
    have hne : cexp (-((Real.log p : ℝ) : ℂ) / 2) ≠ 0 := Complex.exp_ne_zero _
    have h' := h.symm
    rw [neg_mul, neg_eq_zero, mul_eq_zero] at h'
    exact h'.resolve_left hne
  have htransport : ∀ x : ℝ, ∫ t, w t * cexp (-(I * t) * x) =
      (2 * Real.pi : ℝ) • ∫ ξ, W ξ * cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * x) := by
    intro x
    have h := Measure.integral_comp_div
      (fun ξ => W ξ * cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * x)) (2 * Real.pi)
    rw [abs_of_pos h2pi0] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hwdef]
    have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
    rw [ht]
  have hmom : ∀ p : ℕ, p.Prime → ∫ t, w t * cexp (-(I * t) * Real.log p) = 0 := by
    intro p hp
    rw [htransport, hmomξ p hp, smul_zero]
  have hWsm := stronglyMeasurable_boseMellinWeight g
  have hwm : AEStronglyMeasurable w volume :=
    (hWsm.comp_measurable (measurable_id.div_const _)).aestronglyMeasurable
  have hroom : Integrable fun t => ‖w t‖ * PrimeBlindCarlson.roomWeight 3 t := by
    refine ((integrable_boseMellinWeight_room g).comp_div h2pi).congr
      (Eventually.of_forall fun t => ?_)
    simp only [hwdef]
    have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
    rw [ht]
  have hcarl := fun x => PrimeBlindCarlson.fourier_eq_zero_of_primeMoment_eq_zero_room
    (by norm_num : (0 : ℝ) ≤ 3) hwm hroom hmom x
  have hWint : Integrable W := by
    refine ((integrable_boseMellinWeight_room g).const_mul 11).mono'
      hWsm.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    have h := one_div_eleven_le_roomWeight_three (2 * Real.pi * ξ)
    have h0 := norm_nonneg (W ξ)
    nlinarith
  have hF : ∀ y, FourierTransform.fourier W y = 0 := by
    intro y
    have h := hcarl y
    rw [htransport, smul_eq_zero] at h
    have h' := h.resolve_left (by exact_mod_cast h2pi)
    rw [Real.fourier_real_eq, ← h']
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring
  have hW0 : W =ᵐ[volume] 0 := integrable_ae_eq_zero_of_fourier_eq_zero hWint hF
  have hcount : (mellinLinePoint ⁻¹' {s | zetaEntire s = 0}).Countable :=
    countable_setOf_zetaEntire_eq_zero.preimage mellinLinePoint_injective
  have hnull : ∀ᵐ ξ ∂volume, ξ ∉ mellinLinePoint ⁻¹' {s | zetaEntire s = 0} :=
    hcount.ae_notMem volume
  have hMg : (halfLineMellinUnitary g : ℝ → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [hW0, hnull] with ξ h1 h2
    have hz : riemannZeta (mellinLinePoint ξ) ≠ 0 := by
      intro hz
      apply h2
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [zetaEntire_eq (mellinLinePoint_ne_one ξ), hz, mul_zero]
    have hG : Complex.Gamma (mellinLinePoint ξ) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by rw [mellinLinePoint_re]; norm_num)
    have h1' : W ξ = 0 := h1
    simp only [hWdef, boseMellinWeight, mul_eq_zero, map_eq_zero] at h1'
    rcases h1' with (h | h) | h
    · exact absurd h hG
    · exact absurd h hz
    · simpa using h
  have hzero : halfLineMellinUnitary g = 0 := (Lp.eq_zero_iff_ae_eq_zero).mpr hMg
  exact (LinearIsometryEquiv.map_eq_zero_iff halfLineMellinUnitary).mp hzero

/-- **The integer Bose dilates span a dense subspace of `L²((0,∞))`.** -/
theorem boseDilateL2_span_dense :
    (Submodule.span ℂ (Set.range boseDilateL2)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  exact boseDilateL2_eq_zero_of_inner_eq_zero fun p _ =>
    hg _ (Submodule.subset_span ⟨p - 1, rfl⟩)

/-- `b` agrees almost everywhere on `(0,∞)` with a finite Bose combination `Σ_{k ≤ N} c_k β(kt)`. -/
def IsBoseCombination (b : HalfLineL2) : Prop :=
  ∃ N : ℕ, ∃ c : ℕ → ℂ, (b : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
    fun t => ∑ k ∈ Finset.Ioc 0 N, c k * (fusionBoseDefect ((k : ℝ) * t) : ℂ)

private theorem sum_Ioc_ite_le {M N : ℕ} (h : N ≤ M) (f : ℕ → ℂ) :
    ∑ k ∈ Finset.Ioc 0 M, (if k ≤ N then f k else 0) = ∑ k ∈ Finset.Ioc 0 N, f k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  omega

theorem isBoseCombination_of_mem_span {b : HalfLineL2}
    (hb : b ∈ Submodule.span ℂ (Set.range boseDilateL2)) : IsBoseCombination b := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨j + 1, fun k => if k = j + 1 then 1 else 0, ?_⟩
    filter_upwards [MemLp.coeFn_toLp (memLp_boseDilate (Nat.le_add_left 1 j))] with t ht
    rw [boseDilateL2, ht]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_Ioc]
    simp [boseDilate]
  | zero =>
    refine ⟨0, fun _ => 0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))] with t ht
    rw [ht]; simp
  | add x y _ _ hx hy =>
    obtain ⟨N₁, c₁, h₁⟩ := hx
    obtain ⟨N₂, c₂, h₂⟩ := hy
    refine ⟨N₁ + N₂, fun k => (if k ≤ N₁ then c₁ k else 0) + (if k ≤ N₂ then c₂ k else 0), ?_⟩
    filter_upwards [Lp.coeFn_add x y, h₁, h₂] with t ht ht₁ ht₂
    rw [ht, Pi.add_apply, ht₁, ht₂]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [sum_Ioc_ite_le (by omega) (fun k => c₁ k * (fusionBoseDefect ((k : ℝ) * t) : ℂ)),
      sum_Ioc_ite_le (by omega) (fun k => c₂ k * (fusionBoseDefect ((k : ℝ) * t) : ℂ))]
  | smul a x _ hx =>
    obtain ⟨N, c, h⟩ := hx
    refine ⟨N, fun k => a * c k, ?_⟩
    filter_upwards [Lp.coeFn_smul a x, h] with t ht ht'
    rw [ht, Pi.smul_apply, ht', smul_eq_mul, Finset.mul_sum]
    simp only [mul_assoc]

/-- **Unbounded rows approximate unconditionally.**  For every `ε > 0` some finite real row has
chronological heat error below `ε` in `L²(0,∞)`.  With `chronologicalL2Norm_offLine_floor`, this
places the whole arithmetic content of the chronological route in the coefficient bound. -/
theorem exists_chronologicalHeatError_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ a : ℕ → ℝ, chronologicalL2Norm (chronologicalHeatError a N) < ε := by
  have hEm : MemLp (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    chronologicalExponential_memLp.ofReal
  set E : HalfLineL2 := hEm.toLp _ with hE
  have hcl : -E ∈ closure ((Submodule.span ℂ (Set.range boseDilateL2) : Set HalfLineL2)) := by
    rw [← Submodule.topologicalClosure_coe, boseDilateL2_span_dense]; trivial
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
  obtain ⟨N, c, hbc⟩ := isBoseCombination_of_mem_span hb
  refine ⟨N, fun k => (c k).re, lt_of_le_of_lt ?_ hdist⟩
  rw [dist_comm, dist_eq_norm, sub_neg_eq_add, Lp.norm_def]
  unfold chronologicalL2Norm
  rw [← toReal_eLpNorm (chronologicalHeatError_memLp _ _).1]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_mono_ae ?_)
  filter_upwards [Lp.coeFn_add b E, hbc, MemLp.coeFn_toLp hEm] with t h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  have hre : chronologicalHeatError (fun k => (c k).re) N t =
      ((∑ k ∈ Finset.Ioc 0 N, c k * (fusionBoseDefect ((k : ℝ) * t) : ℂ)) +
        ((Real.exp (-t) : ℝ) : ℂ)).re := by
    rw [chronologicalHeatError, Complex.add_re, Complex.re_sum, Complex.ofReal_re, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_mul_ofReal]
  rw [hre, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

end RHTower
