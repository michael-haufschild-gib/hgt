import GaloisForLFunctions.HTGeometry.EulerWildProximity
import GaloisForLFunctions.HTGeometry.DivisorMassCharacteristic
import GaloisForLFunctions.HTGeometry.LogSelfBoundArithmetic
import GaloisForLFunctions.HTGeometry.OmittedValueLogarithmicGrowth
import GaloisForLFunctions.HTGeometry.PicardLittleTheorem
import GaloisForLFunctions.HTGeometry.EulerDominantConstantTerm
import GaloisForLFunctions.HTGeometry.EulerAutonomousPolynomial
import GaloisForLFunctions.HTGeometry.ZeroFreeRadiusSelection

/-!
# The wild branch forces logarithmic characteristic

The wild bound `c‖f‖^{m+1} ≤ ‖z f′‖^m` gives `T(r,f) ≤ m·m(r, f′/(f−a)) + m·log r + E`, and the
logarithmic-derivative estimate bounds the right side by a logarithm of `T` itself.  Choosing the
inner radius by the Borel growth lemma and the three outer radii inside the Borel window — one of
them on a circle free of zeros — turns the estimate into

```text
T ≤ A + 8m·log(T+1),
```

which collapses to `T(r,f) = O(log r)`.  Every ingredient is at radii within the Borel window, so no
comparison between `T(r)` and `T(2r)` is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open ValueDistribution Metric Real Set MeromorphicOn

/-- `log (1 + y) ≤ log 2 + log P` when `y ≤ P` and `1 ≤ P`. -/
theorem log_one_add_le_of_le {y P : ℝ} (hy : 0 ≤ y) (hP : 1 ≤ P) (h : y ≤ P) :
    Real.log (1 + y) ≤ Real.log 2 + Real.log P := by
  have h2P : 1 + y ≤ 2 * P := by linarith
  have hpos : (0 : ℝ) < 1 + y := by linarith
  calc Real.log (1 + y) ≤ Real.log (2 * P) := Real.log_le_log hpos h2P
    _ = Real.log 2 + Real.log P := Real.log_mul (by norm_num) (by linarith)

/-- `log (Q * u ^ 4 * v ^ 4) = log Q + 4 log u + 4 log v`. -/
theorem log_pow_product {Q u v : ℝ} (hQ : 0 < Q) (hu : 0 < u) (hv : 0 < v) :
    Real.log (Q * u ^ 4 * v ^ 4) = Real.log Q + 4 * Real.log u + 4 * Real.log v := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `t ^ (-(1/2)) ≤ 1 + t⁻¹` for `t > 0`. -/
theorem rpow_neg_half_le {t : ℝ} (ht : 0 < t) : t ^ (-(1/2 : ℝ)) ≤ 1 + t⁻¹ := by
  rw [Real.rpow_neg ht.le]
  have hpos : (0 : ℝ) < t ^ ((1 : ℝ)/2) := Real.rpow_pos_of_pos ht _
  rcases le_or_gt 1 t with h1 | h1
  · have : (1 : ℝ) ≤ t ^ ((1 : ℝ)/2) := Real.one_le_rpow h1 (by norm_num)
    have hinv : (t ^ ((1 : ℝ)/2))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact this
    have : (0 : ℝ) < t⁻¹ := by positivity
    linarith
  · have hle : t ≤ t ^ ((1 : ℝ)/2) := by
      have := Real.rpow_le_rpow_of_exponent_ge ht h1.le (by norm_num : (1:ℝ)/2 ≤ 1)
      simpa using this
    have hinv : (t ^ ((1 : ℝ)/2))⁻¹ ≤ t⁻¹ := by
      exact inv_anti₀ ht hle
    linarith

/-- `y ^ (1/2) ≤ 1 + y` for `y ≥ 0`. -/
theorem rpow_half_le_one_add {y : ℝ} (hy : 0 ≤ y) : y ^ ((1 : ℝ)/2) ≤ 1 + y := by
  rcases le_or_gt y 1 with h1 | h1
  · have : y ^ ((1 : ℝ)/2) ≤ (1 : ℝ) ^ ((1 : ℝ)/2) := Real.rpow_le_rpow hy h1 (by norm_num)
    rw [Real.one_rpow] at this
    linarith
  · have : y ^ ((1 : ℝ)/2) ≤ y ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num)
    rw [Real.rpow_one] at this
    linarith

/-- `x ^ (-(1/2)) ≤ 1` for `x ≥ 1`. -/
theorem rpow_neg_half_le_one {x : ℝ} (hx : 1 ≤ x) : x ^ (-(1/2 : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)

/-- The constant of the wild collapse: it depends only on the shift constant of the relation. -/
noncomputable def wildConst (Ka : ℝ) : ℝ :=
  1 + (2 * π)⁻¹ * (256 * (6 + 2 * Ka)) * (sinNegPowerConst (1 / 2) + 57)
    + (1 + 128 * (6 + 2 * Ka))

theorem one_le_wildConst {Ka : ℝ} (hKa : 0 ≤ Ka) : 1 ≤ wildConst Ka := by
  have h1 : 0 ≤ sinNegPowerConst (1 / 2) := sinNegPowerConst_nonneg _
  have h2 : (0 : ℝ) < 2 * π := by positivity
  rw [wildConst]
  have h3 : 0 ≤ (2 * π)⁻¹ * (256 * (6 + 2 * Ka)) * (sinNegPowerConst (1 / 2) + 57) := by positivity
  have h4 : 0 ≤ 1 + 128 * (6 + 2 * Ka) := by positivity
  linarith

/-- The logarithm of a ratio close to one is at least half the relative increment. -/
theorem log_div_lower {p q : ℝ} (hq : 0 < q) (hpq : q ≤ p) : (p - q) / p ≤ Real.log (p / q) := by
  have hp : 0 < p := lt_of_lt_of_le hq hpq
  have h := Real.one_sub_inv_le_log_of_pos (x := p / q) (by positivity)
  have hinv : (p / q)⁻¹ = q / p := by
    rw [inv_div]
  rw [hinv] at h
  have : 1 - q / p = (p - q) / p := by field_simp
  linarith [h, this]

set_option maxHeartbeats 1000000 in
/-- **The divisor mass at the two scales.**  With the outer radii inside the Borel window, the mass
in the disc of radius `R` is at most a fixed power of `x + 1` and `T + 1`. -/
theorem divisorMass_rpow_le_scales {g : ℂ → ℂ} (hgdiff : Differentiable ℂ g)
    (horder : ∀ z : ℂ, meromorphicOrderAt g z ≠ ⊤) (hg0norm : ‖g 0‖ = 1)
    {x step R R' R'' T₀ Ka u v : ℝ}
    (hu : u = x + 1) (hv : v = T₀ + 1)
    (hx1 : 1 ≤ x) (hstep0 : 0 < step) (hstep1 : step ≤ 1) (hT₀ : 0 ≤ T₀) (hKa : 0 ≤ Ka)
    (hstepsq : step ^ 2 = (T₀ + 1)⁻¹)
    (hR1 : x + step / 8 ≤ R) (hR2 : R ≤ x + 2 * step / 8)
    (hR'def : R' = x + 3 * step / 8) (hR''def : R'' = x + 4 * step / 8)
    (hKzero : max |Real.log ‖g 0‖| |Real.log ‖meromorphicTrailingCoeffAt g 0‖| = 0)
    (hTR'' : characteristic g ⊤ R'' ≤ 2 * T₀ + 1 + Ka) :
    (∑ᶠ w : ℂ, (|(MeromorphicOn.divisor g (closedBall (0 : ℂ) |R|) w : ℤ)| : ℝ) ^ ((1 : ℝ) / 2))
      ≤ 256 * (6 + 2 * Ka) * u ^ 2 * v ^ 2 := by
  classical
  have hu1 : (1 : ℝ) ≤ u := by rw [hu]; linarith
  have hv1 : (1 : ℝ) ≤ v := by rw [hv]; linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hstepv : step * (step * v) = 1 := by
    have h : step ^ 2 * v = 1 := by
      rw [hstepsq, hv]
      field_simp
    nlinarith [h]
  have hinvstep : 1 / step ≤ v := by
    rw [div_le_iff₀ hstep0]
    nlinarith [hstepv, hstep1, hstep0, hv1]
  have hRx1 : step / 8 ≤ R - x := by linarith
  have hxR : x < R := by linarith
  have hRu : R ≤ u := by rw [hu]; linarith
  have hR'R : step / 8 ≤ R' - R := by rw [hR'def]; linarith
  have hRR' : R < R' := by linarith
  have hR''R' : R' < R'' := by rw [hR'def, hR''def]; linarith
  have hR''1 : (1 : ℝ) ≤ R'' := by rw [hR''def]; linarith
  have hR''u : R'' ≤ u := by rw [hR''def, hu]; linarith
  have hR'0 : (0 : ℝ) < R' := by linarith
  have hmassA := divisorMass_rpow_le (f := g) (R := R) (α := (1 : ℝ) / 2)
    (by norm_num) (by norm_num)
  have hnonneg : 0 ≤ MeromorphicOn.divisor g (closedBall (0 : ℂ) |R|) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ => hgdiff.analyticAt z)
  have habs : ∀ w : ℂ, |((MeromorphicOn.divisor g (closedBall (0 : ℂ) |R|) w : ℤ) : ℝ)|
      = ((MeromorphicOn.divisor g (closedBall (0 : ℂ) |R|) w : ℤ) : ℝ) := by
    intro w
    have hw := hnonneg w
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply] at hw
    rw [abs_of_nonneg (by exact_mod_cast hw)]
  have hmassC := divisorMass_le_characteristic hgdiff horder hg0norm
    (by linarith : (0 : ℝ) < R) hRR' hR''R' hR''1
  rw [hKzero] at hmassC
  have hlogratio : step / (16 * u) ≤ Real.log (R' / R) := by
    have hstep' : (R' - R) / R' ≤ Real.log (R' / R) := log_div_lower (by linarith) (le_of_lt hRR')
    have h1 : step / (16 * u) ≤ (R' - R) / R' := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 16 * u) (by linarith : (0:ℝ) < R')]
      have hR'le : R' ≤ 2 * u := by rw [hR'def, hu]; linarith
      nlinarith [hR'R, hstep0, hu1, hR'le]
    linarith
  have hTge : (0 : ℝ) ≤ characteristic g ⊤ R'' :=
    ValueDistribution.characteristic_nonneg (by linarith)
  refine le_trans hmassA ?_
  rw [finsum_congr habs]
  refine le_trans hmassC ?_
  have hden : 0 < Real.log (R' / R) := lt_of_lt_of_le (by positivity) hlogratio
  have hnum : (R'' + R') / (R'' - R') * (2 * characteristic g ⊤ R'' + 0)
      ≤ (16 * u / step) * ((6 + 2 * Ka) * v) := by
    have hdiff : R'' - R' = step / 8 := by rw [hR'def, hR''def]; ring
    have hratio : (R'' + R') / (R'' - R') ≤ 16 * u / step := by
      rw [hdiff, div_le_div_iff₀ (by positivity) hstep0]
      have hsum : R'' + R' ≤ 2 * u := by rw [hR'def, hR''def, hu]; linarith
      nlinarith [hsum, hstep0]
    have hchar : 2 * characteristic g ⊤ R'' + 0 ≤ (6 + 2 * Ka) * v := by
      rw [hv]
      nlinarith [hTR'', hT₀, hKa]
    have h1 : (0 : ℝ) ≤ 16 * u / step := by positivity
    have h3 : (0 : ℝ) ≤ 2 * characteristic g ⊤ R'' + 0 := by linarith
    exact mul_le_mul hratio hchar h3 h1
  have hstepdiv : ((16 : ℝ) * u / step) * ((6 + 2 * Ka) * v) / Real.log (R' / R)
      ≤ ((16 * u / step) * ((6 + 2 * Ka) * v)) * (16 * u / step) := by
    rw [div_le_iff₀ hden]
    have hpos : (0 : ℝ) ≤ (16 * u / step) * ((6 + 2 * Ka) * v) := by positivity
    have h16 : (0 : ℝ) < 16 * u / step := by positivity
    have hprod : (1 : ℝ) ≤ (16 * u / step) * Real.log (R' / R) := by
      have hmul := mul_le_mul_of_nonneg_left hlogratio h16.le
      calc (1 : ℝ) = (16 * u / step) * (step / (16 * u)) := by field_simp
        _ ≤ (16 * u / step) * Real.log (R' / R) := hmul
    nlinarith [hprod, hpos]
  have hfinal : ((16 : ℝ) * u / step) * ((6 + 2 * Ka) * v) * (16 * u / step)
      = 256 * (6 + 2 * Ka) * u ^ 2 * v * (1 / step ^ 2) := by
    field_simp
    ring
  have hstepinv : (1 : ℝ) / step ^ 2 = v := by
    rw [hstepsq, hv]
    field_simp
  have hdivmono : (R'' + R') / (R'' - R') * (2 * characteristic g ⊤ R'' + 0)
      / Real.log (R' / R)
      ≤ ((16 : ℝ) * u / step) * ((6 + 2 * Ka) * v) / Real.log (R' / R) :=
    div_le_div_of_nonneg_right hnum hden.le
  refine le_trans hdivmono (le_trans hstepdiv ?_)
  rw [hfinal, hstepinv]
  nlinarith [hu1, hv1, hKa]

/-- The boundary factor of the logarithmic-derivative estimate. -/
theorem boundary_factor_le {x step R v kA : ℝ} (hx1 : 1 ≤ x) (hstep0 : 0 < step)
    (hv1 : 1 ≤ v) (hkA0 : 0 ≤ kA) (hRx1 : step / 8 ≤ R - x) (hinvstep : 1 / step ≤ v) :
    x ^ (-((1 : ℝ) / 2)) * kA + 2 * π * (R - x) ^ (-((1 : ℝ) / 2)) ≤ (kA + 57) * v := by
  have hRx0 : (0 : ℝ) < R - x := lt_of_lt_of_le (by positivity) hRx1
  have h1 : x ^ (-((1 : ℝ) / 2)) ≤ 1 := rpow_neg_half_le_one hx1
  have h1' : (0 : ℝ) ≤ x ^ (-((1 : ℝ) / 2)) := Real.rpow_nonneg (by linarith) _
  have hinvRx : (R - x)⁻¹ ≤ 8 * v := by
    have hstepinv : (R - x)⁻¹ ≤ (step / 8)⁻¹ := inv_anti₀ (by positivity) hRx1
    have heq : (step / 8)⁻¹ = 8 * (1 / step) := by field_simp
    rw [heq] at hstepinv
    nlinarith [hstepinv, hinvstep]
  have h2 : (R - x) ^ (-((1 : ℝ) / 2)) ≤ 1 + (R - x)⁻¹ := rpow_neg_half_le hRx0
  have hle9 : (R - x) ^ (-((1 : ℝ) / 2)) ≤ 9 * v := by linarith [h2, hinvRx, hv1]
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  have h5 : 2 * π * (R - x) ^ (-((1 : ℝ) / 2)) ≤ 2 * π * (9 * v) :=
    mul_le_mul_of_nonneg_left hle9 (by positivity)
  have h6 : 2 * π * (9 * v) ≤ 57 * v := by nlinarith [hpi, hv1]
  have h7 : x ^ (-((1 : ℝ) / 2)) * kA ≤ kA := by nlinarith [h1, h1', hkA0]
  nlinarith [h5, h6, h7, hkA0, hv1]

/-- The characteristic factor of the logarithmic-derivative estimate. -/
theorem char_factor_le {x step R T Ka u v : ℝ} (hx1 : 1 ≤ x) (hstep0 : 0 < step)
    (hu1 : 1 ≤ u) (hv1 : 1 ≤ v) (hKa : 0 ≤ Ka) (hT : 0 ≤ T)
    (hRx1 : step / 8 ≤ R - x) (hRu : R ≤ u) (hstepinv : (1 : ℝ) / step ^ 2 = v)
    (hchar : 2 * T ≤ (6 + 2 * Ka) * v) :
    (2 * R / (R - x) ^ 2 * (2 * T + 0)) ^ ((1 : ℝ) / 2)
      ≤ 1 + 128 * (6 + 2 * Ka) * (u * v ^ 2) := by
  have hRx0 : (0 : ℝ) < R - x := lt_of_lt_of_le (by positivity) hRx1
  have hR0 : (0 : ℝ) < R := by linarith
  have hfac : 2 * R / (R - x) ^ 2 ≤ 128 * (u * v) := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : (step / 8) ^ 2 ≤ (R - x) ^ 2 := by nlinarith [hRx1, hstep0]
    have h1 : (128 : ℝ) * (u * v) * (step / 8) ^ 2 = 2 * u * (v * step ^ 2) := by ring
    have hv2 : v * step ^ 2 = 1 := by
      have hs : step ^ 2 ≠ 0 := by positivity
      field_simp at hstepinv
      nlinarith [hstepinv]
    have h2 : (128 : ℝ) * (u * v) * (step / 8) ^ 2 = 2 * u := by
      rw [h1, hv2]; ring
    have h3 : (128 : ℝ) * (u * v) * (step / 8) ^ 2 ≤ 128 * (u * v) * (R - x) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith [h2, h3, hRu]
  have hbase : 2 * R / (R - x) ^ 2 * (2 * T + 0) ≤ 128 * (6 + 2 * Ka) * (u * v ^ 2) := by
    have h1 : (0 : ℝ) ≤ 2 * R / (R - x) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * T + 0 := by linarith
    calc 2 * R / (R - x) ^ 2 * (2 * T + 0)
        ≤ (128 * (u * v)) * ((6 + 2 * Ka) * v) := by
          refine mul_le_mul hfac (by linarith) h2 (by positivity)
      _ = 128 * (6 + 2 * Ka) * (u * v ^ 2) := by ring
  have hnn : (0 : ℝ) ≤ 2 * R / (R - x) ^ 2 * (2 * T + 0) := by positivity
  have hmono : (2 * R / (R - x) ^ 2 * (2 * T + 0)) ^ ((1 : ℝ) / 2)
      ≤ (128 * (6 + 2 * Ka) * (u * v ^ 2)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hnn hbase (by norm_num)
  have hb2 := rpow_half_le_one_add (y := 128 * (6 + 2 * Ka) * (u * v ^ 2)) (by positivity)
  linarith [hmono, hb2]

set_option maxHeartbeats 2000000 in
/-- **The logarithmic-derivative proximity at a Borel-good radius.**  With the three outer radii
inside the Borel window and the first of them on a circle free of zeros, the estimate is a logarithm
of `x + 1` and of `T + 1`. -/
theorem proximity_logDeriv_le_log_of_radii {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℂ}
    (hga : f 0 - a = 1)
    (horder : ∀ z : ℂ, meromorphicOrderAt (fun w => f w - a) z ≠ ⊤)
    {x step R R' R'' T₀ Ka : ℝ}
    (hx1 : 1 ≤ x) (hstep0 : 0 < step) (hstep1 : step ≤ 1) (hT₀ : 0 ≤ T₀) (hKa : 0 ≤ Ka)
    (hstepsq : step ^ 2 = (T₀ + 1)⁻¹)
    (hR1 : x + step / 8 ≤ R) (hR2 : R ≤ x + 2 * step / 8)
    (hR'def : R' = x + 3 * step / 8) (hR''def : R'' = x + 4 * step / 8)
    (hTR : characteristic (fun w => f w - a) ⊤ R ≤ 2 * T₀ + 1 + Ka)
    (hTR'' : characteristic (fun w => f w - a) ⊤ R'' ≤ 2 * T₀ + 1 + Ka)
    (hzero : ∀ w ∈ sphere (0 : ℂ) |R|,
      MeromorphicOn.divisor (fun w => f w - a) (closedBall (0 : ℂ) |R|) w = 0) :
    proximity (fun z => deriv f z / (f z - a)) ⊤ x
      ≤ 2 * (Real.log 2 + Real.log (wildConst Ka)
          + 4 * Real.log (x + 1) + 4 * Real.log (T₀ + 1)) := by
  classical
  set g : ℂ → ℂ := fun w => f w - a with hgdef
  have hgdiff : Differentiable ℂ g := hf.sub_const a
  have hg0 : g 0 = 1 := hga
  have hg0norm : ‖g 0‖ = 1 := by rw [hg0]; simp
  have hKzero : max |Real.log ‖g 0‖| |Real.log ‖meromorphicTrailingCoeffAt g 0‖| = 0 := by
    have htr : meromorphicTrailingCoeffAt g 0 = g 0 :=
      (hgdiff.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero (by rw [hg0]; norm_num)
    rw [htr, hg0]
    simp
  set u : ℝ := x + 1 with hu
  set v : ℝ := T₀ + 1 with hv
  have hu1 : (1 : ℝ) ≤ u := by rw [hu]; linarith
  have hv1 : (1 : ℝ) ≤ v := by rw [hv]; linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hstepv : step * (step * v) = 1 := by
    have h : step ^ 2 * v = 1 := by
      rw [hstepsq, hv]
      field_simp
    nlinarith [h]
  have hinvstep : 1 / step ≤ v := by
    rw [div_le_iff₀ hstep0]
    nlinarith [hstepv, hstep1, hstep0, hv1]
  have hstepinv : (1 : ℝ) / step ^ 2 = v := by
    rw [hstepsq, hv]
    field_simp
  have hRx1 : step / 8 ≤ R - x := by linarith
  have hRx0 : (0 : ℝ) < R - x := by linarith
  have hxR : x < R := by linarith
  have hRu : R ≤ u := by rw [hu]; linarith
  have hR1' : (1 : ℝ) ≤ R := by linarith
  have hkA0 : 0 ≤ sinNegPowerConst ((1 : ℝ) / 2) := sinNegPowerConst_nonneg _
  have hTRge : (0 : ℝ) ≤ characteristic g ⊤ R :=
    ValueDistribution.characteristic_nonneg (by linarith)
  -- the three ingredients
  have hmass := divisorMass_rpow_le_scales hgdiff horder hg0norm hu hv hx1 hstep0 hstep1 hT₀ hKa
    hstepsq hR1 hR2 hR'def hR''def hKzero hTR''
  have hfac1 := boundary_factor_le (x := x) (step := step) (R := R) (v := v)
    (kA := sinNegPowerConst ((1 : ℝ) / 2)) hx1 hstep0 hv1 hkA0 hRx1 hinvstep
  have hterm2 := char_factor_le (x := x) (step := step) (R := R)
    (T := characteristic g ⊤ R) (Ka := Ka) (u := u) (v := v)
    hx1 hstep0 hu1 hv1 hKa hTRge hRx1 hRu hstepinv (by rw [hv]; nlinarith [hTR, hT₀, hKa])
  have hLDL := proximity_logDeriv_sub_const_le (α := (1 : ℝ) / 2) (by norm_num) (by norm_num)
    (r := x) (R := R) hx0 hxR hR1' a hf horder hzero
  rw [hKzero] at hLDL
  -- assemble the argument of the logarithm
  set MASS : ℝ := ∑ᶠ w : ℂ,
    (|(MeromorphicOn.divisor g (closedBall (0 : ℂ) |R|) w : ℤ)| : ℝ) ^ ((1 : ℝ) / 2) with hMASS
  set FAC : ℝ := x ^ (-((1 : ℝ) / 2)) * sinNegPowerConst ((1 : ℝ) / 2)
    + 2 * π * (R - x) ^ (-((1 : ℝ) / 2)) with hFAC
  set TRM : ℝ := (2 * R / (R - x) ^ 2 * (2 * characteristic g ⊤ R + 0)) ^ ((1 : ℝ) / 2) with hTRM
  have hMASS0 : 0 ≤ MASS := by
    rw [hMASS]
    refine finsum_nonneg fun w => ?_
    positivity
  have hFAC0 : 0 ≤ FAC := by
    rw [hFAC]
    have h1 : (0 : ℝ) ≤ x ^ (-((1 : ℝ) / 2)) := Real.rpow_nonneg (by linarith) _
    have h2 : (0 : ℝ) ≤ (R - x) ^ (-((1 : ℝ) / 2)) := Real.rpow_nonneg (by linarith) _
    have hpi0 : (0 : ℝ) < π := Real.pi_pos
    positivity
  have hTRM0 : 0 ≤ TRM := by
    rw [hTRM]
    exact Real.rpow_nonneg (by positivity) _
  have hπ0 : (0 : ℝ) < (2 * π)⁻¹ := by
    have := Real.pi_pos
    positivity
  have hprod1 : (2 * π)⁻¹ * (MASS * FAC)
      ≤ (2 * π)⁻¹ * (256 * (6 + 2 * Ka)) * (sinNegPowerConst ((1 : ℝ) / 2) + 57)
        * (u ^ 2 * v ^ 3) := by
    have hstep' : MASS * FAC
        ≤ (256 * (6 + 2 * Ka) * u ^ 2 * v ^ 2)
          * ((sinNegPowerConst ((1 : ℝ) / 2) + 57) * v) :=
      mul_le_mul hmass hfac1 hFAC0 (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hstep' hπ0.le
    calc (2 * π)⁻¹ * (MASS * FAC)
        ≤ (2 * π)⁻¹ * ((256 * (6 + 2 * Ka) * u ^ 2 * v ^ 2)
            * ((sinNegPowerConst ((1 : ℝ) / 2) + 57) * v)) := hmul
      _ = (2 * π)⁻¹ * (256 * (6 + 2 * Ka)) * (sinNegPowerConst ((1 : ℝ) / 2) + 57)
            * (u ^ 2 * v ^ 3) := by ring
  have hpow : (1 : ℝ) ≤ u ^ 4 * v ^ 4 := by
    have h1 : (1 : ℝ) ≤ u ^ 4 := one_le_pow₀ hu1
    have h2 : (1 : ℝ) ≤ v ^ 4 := one_le_pow₀ hv1
    nlinarith
  have hA : u ^ 2 * v ^ 3 ≤ u ^ 4 * v ^ 4 := by
    have h1 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by omega)
    have h2 : v ^ 3 ≤ v ^ 4 := pow_le_pow_right₀ hv1 (by omega)
    have h3 : (0 : ℝ) ≤ u ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ v ^ 3 := by positivity
    nlinarith [h1, h2, h3, h4, one_le_pow₀ hu1 (n := 2), one_le_pow₀ hv1 (n := 3)]
  have hB : u * v ^ 2 ≤ u ^ 4 * v ^ 4 := by
    have h1 : u ≤ u ^ 4 := le_self_pow₀ hu1 (by omega)
    have h2 : v ^ 2 ≤ v ^ 4 := pow_le_pow_right₀ hv1 (by omega)
    nlinarith [h1, h2, hu1, hv1]
  have htotal : 1 + ((2 * π)⁻¹ * (MASS * FAC) + TRM) ≤ wildConst Ka * u ^ 4 * v ^ 4 := by
    have hcoef1 : (0 : ℝ) ≤ (2 * π)⁻¹ * (256 * (6 + 2 * Ka))
        * (sinNegPowerConst ((1 : ℝ) / 2) + 57) := by positivity
    have hcoef2 : (0 : ℝ) ≤ 128 * (6 + 2 * Ka) := by positivity
    rw [wildConst]
    nlinarith [hprod1, hterm2, hA, hB, hcoef1, hcoef2, hpow]
  have htotal' : (2 * π)⁻¹ * (MASS * FAC) + TRM ≤ wildConst Ka * u ^ 4 * v ^ 4 := by
    linarith [htotal]
  have hinner0 : (0 : ℝ) ≤ (2 * π)⁻¹ * (MASS * FAC) + TRM := by positivity
  have hlogbd := log_one_add_le_of_le hinner0
    (by nlinarith [one_le_wildConst hKa, hpow] : (1 : ℝ) ≤ wildConst Ka * u ^ 4 * v ^ 4) htotal'
  have hsplit : Real.log (wildConst Ka * u ^ 4 * v ^ 4)
      = Real.log (wildConst Ka) + 4 * Real.log u + 4 * Real.log v :=
    log_pow_product (by linarith [one_le_wildConst hKa]) hu0 hv0
  rw [hsplit] at hlogbd
  refine le_trans hLDL ?_
  have hhalf : (1 : ℝ) / ((1 : ℝ) / 2) = 2 := by norm_num
  rw [hhalf]
  have : Real.log (1 + ((2 * π)⁻¹ * (MASS * FAC) + TRM))
      ≤ Real.log 2 + (Real.log (wildConst Ka) + 4 * Real.log u + 4 * Real.log v) := hlogbd
  rw [hu, hv] at this
  linarith [this]

set_option maxHeartbeats 4000000 in
/-- **The wild branch forces a logarithmic characteristic.**  If the relation makes
`c‖f‖^{m+1} ≤ ‖z f′‖^m` wherever `‖f‖` is large, then `T(r,f) = O(log r)`. -/
theorem exists_characteristic_le_log_of_wild {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {m : ℕ} (hm : 1 ≤ m) {c R₂ : ℝ} (hc : 0 < c) (hR₂ : 1 ≤ R₂)
    (hwild : ∀ z : ℂ, R₂ ≤ ‖f z‖ → c * ‖f z‖ ^ (m + 1) ≤ ‖z * deriv f z‖ ^ m) :
    ∃ A B : ℝ, ∀ s : ℝ, 1 ≤ s → characteristic f ⊤ s ≤ A * Real.log (s + 2) + B := by
  classical
  set a : ℂ := f 0 - 1 with hadef
  have hga : f 0 - a = 1 := by rw [hadef]; ring
  set g : ℂ → ℂ := fun w => f w - a with hgdef
  have hgdiff : Differentiable ℂ g := hf.sub_const a
  have hg0 : g 0 = 1 := hga
  have hgne : ∃ w : ℂ, g w ≠ 0 := ⟨0, by rw [hg0]; norm_num⟩
  have horder : ∀ z : ℂ, meromorphicOrderAt g z ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_exists_ne_zero hgdiff hgne
  set Ka : ℝ := Real.posLog ‖a‖ + Real.log 2 with hKadef
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKa : 0 ≤ Ka := by
    have := Real.posLog_nonneg (x := ‖a‖)
    rw [hKadef]
    linarith
  set E₁ : ℝ := (|Real.log c| + ((m : ℝ) + 1) * Real.log R₂) + (m : ℝ) * Ka with hE₁
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hE₁0 : 0 ≤ E₁ := by
    have h1 : (0 : ℝ) ≤ |Real.log c| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ Real.log R₂ := Real.log_nonneg hR₂
    rw [hE₁]
    have : (0 : ℝ) ≤ ((m : ℝ) + 1) * Real.log R₂ := by positivity
    have h3 : (0 : ℝ) ≤ (m : ℝ) * Ka := by positivity
    linarith
  have hstage : ∀ r : ℝ, 1 ≤ r → characteristic f ⊤ r
      ≤ (m : ℝ) * proximity (fun z => deriv f z / (f z - a)) ⊤ r + (m : ℝ) * Real.log r + E₁ := by
    intro r hr
    have := characteristic_le_logDeriv_shift_of_wild hf a horder hm hc hR₂ hwild hr
    rw [hE₁, hKadef]
    exact this
  set W : ℝ := Nevanlinna.borelWindow ((1 : ℝ) / 2) with hW
  have hW1 : 1 ≤ W := Nevanlinna.one_le_borelWindow _
  set Q : ℝ := wildConst Ka with hQ
  have hQ1 : 1 ≤ Q := one_le_wildConst hKa
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  set Acoef : ℝ := 18 * (m : ℝ) with hAcoef
  set Bconst : ℝ := (4 * (m : ℝ) * (Real.log 2 + Real.log Q) + 2 * E₁
      + 16 * (m : ℝ) * |Real.log (32 * (m : ℝ))| + 1) + Acoef * Real.log (W + 1) with hBconst
  refine ⟨Acoef, Bconst, ?_⟩
  intro s hs
  -- a Borel-good radius in the window above `s`
  obtain ⟨x, hxmem, hxborel⟩ :=
    Nevanlinna.exists_mem_Icc_lt_two_mul_rpow_window (monotone_charPlusOne hf)
      (one_le_charPlusOne hf) (by norm_num : (0:ℝ) < 1/2) s
  have hxs : s ≤ x := hxmem.1
  have hxW : x ≤ s + W := hxmem.2
  have hx1 : (1 : ℝ) ≤ x := le_trans hs hxs
  have hx0 : (0 : ℝ) < x := by linarith
  set T₀ : ℝ := characteristic f ⊤ x with hT₀def
  have hT₀ : 0 ≤ T₀ := characteristic_nonneg_of_entire hf x
  have hTx : charPlusOne f x = T₀ + 1 := charPlusOne_eq hx1
  set step : ℝ := (charPlusOne f x) ^ (-(1/2 : ℝ)) with hstepdef
  have hstep0 : 0 < step := Real.rpow_pos_of_pos (by linarith [one_le_charPlusOne hf x]) _
  have hstep1 : step ≤ 1 := by
    rw [hstepdef]
    exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_charPlusOne hf x) (by norm_num)
  have hstepsq : step ^ 2 = (T₀ + 1)⁻¹ := by
    rw [hstepdef, hTx, ← Real.rpow_natCast ((T₀ + 1) ^ (-(1/2 : ℝ))) 2,
      ← Real.rpow_mul (by linarith)]
    norm_num
    rw [Real.rpow_neg_one]
  -- the outer radii
  set R'' : ℝ := x + 4 * step / 8 with hR''def
  set R' : ℝ := x + 3 * step / 8 with hR'def
  have hxa : (0 : ℝ) < x + step / 8 := by linarith
  have hab : x + step / 8 < x + 2 * step / 8 := by linarith
  obtain ⟨R, hRmem, hRzero⟩ := exists_radius_divisor_sphere_eq_zero hgdiff horder hxa hab
  have hR1 : x + step / 8 ≤ R := hRmem.1
  have hR2 : R ≤ x + 2 * step / 8 := hRmem.2
  -- the Borel step and the characteristic at the outer radii
  have hcharstep : characteristic f ⊤ (x + step) ≤ 2 * T₀ + 1 := by
    have h := hxborel
    rw [hTx] at h
    have hR1' : (1 : ℝ) ≤ x + step := by linarith
    have hR' : charPlusOne f (x + step) = characteristic f ⊤ (x + step) + 1 :=
      charPlusOne_eq hR1'
    rw [hR'] at h
    linarith
  have hmonoF := ValueDistribution.characteristic_monotoneOn
    (f := f) (fun z => (hf.analyticAt z).meromorphicAt)
  have hcharR'' : characteristic f ⊤ R'' ≤ 2 * T₀ + 1 := by
    refine le_trans (hmonoF (Set.mem_Ioi.mpr (by rw [hR''def]; linarith))
      (Set.mem_Ioi.mpr (by linarith)) (by rw [hR''def]; linarith)) hcharstep
  have hcharR : characteristic f ⊤ R ≤ 2 * T₀ + 1 := by
    refine le_trans (hmonoF (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by linarith))
      (by linarith : R ≤ x + step)) hcharstep
  have hTR : characteristic g ⊤ R ≤ 2 * T₀ + 1 + Ka := by
    have := characteristic_sub_const_le hf a R
    rw [hKadef]
    rw [hgdef]
    linarith [this, hcharR]
  have hTR'' : characteristic g ⊤ R'' ≤ 2 * T₀ + 1 + Ka := by
    have := characteristic_sub_const_le hf a R''
    rw [hKadef]
    rw [hgdef]
    linarith [this, hcharR'']
  -- the logarithmic-derivative estimate at `x`
  have hprox := proximity_logDeriv_le_log_of_radii hf hga horder hx1 hstep0 hstep1 hT₀ hKa
    hstepsq hR1 hR2 hR'def hR''def hTR hTR'' hRzero
  -- the self-bounding inequality
  have hself := hstage x hx1
  have hlogx : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have hcoll : T₀ ≤ (2 * (m : ℝ) * (Real.log 2 + Real.log Q) + 9 * (m : ℝ) * Real.log (x + 1) + E₁)
      + (8 * (m : ℝ)) * Real.log (T₀ + 1) := by
    rw [← hQ] at hprox
    nlinarith [hself, hprox, hm1, hlogx]
  have hA0 : (0 : ℝ) ≤ 2 * (m : ℝ) * (Real.log 2 + Real.log Q)
      + 9 * (m : ℝ) * Real.log (x + 1) + E₁ := by
    have h1 : (0 : ℝ) ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ 2 * (m : ℝ) * (Real.log 2 + Real.log Q) := by positivity
    have h3 : (0 : ℝ) ≤ 9 * (m : ℝ) * Real.log (x + 1) := by positivity
    linarith
  have hcm : (0 : ℝ) < 8 * (m : ℝ) := by linarith
  have hfinal := le_of_le_add_mul_log hT₀ hcm hA0 hcoll
  -- transport back to `s`
  have hlogxs : Real.log (x + 1) ≤ Real.log (W + 1) + Real.log (s + 2) := by
    have h1 : x + 1 ≤ (W + 1) * (s + 2) := by nlinarith [hxW, hW1, hs]
    have h2 : Real.log (x + 1) ≤ Real.log ((W + 1) * (s + 2)) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by linarith) (by linarith)] at h2
    exact h2
  have hmonos : characteristic f ⊤ s ≤ T₀ :=
    hmonoF (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr hx0) hxs
  have h18 : (0 : ℝ) ≤ 18 * (m : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlogxs h18
  have habs32 : (4 : ℝ) * (8 * (m : ℝ)) = 32 * (m : ℝ) := by ring
  rw [habs32] at hfinal
  rw [hAcoef, hBconst, hAcoef]
  linarith [hfinal, hmonos, hmul]

open Filter in
/-- **A logarithmic characteristic bound recognises a polynomial.** -/
theorem exists_polynomial_of_characteristic_le_log {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A B : ℝ} (hAB : ∀ s : ℝ, 1 ≤ s → characteristic f ⊤ s ≤ A * Real.log (s + 2) + B) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z := by
  set K : ℝ := |A| + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  refine exists_polynomial_of_frequently_characteristic_le_log hf hK0 ?_
  have hev : ∀ᶠ s : ℝ in atTop, characteristic f ⊤ s ≤ K * Real.log s := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (Real.exp (|A| * Real.log 3 + B))] with s hs1 hs2
    have hs0 : (0 : ℝ) < s := by linarith
    have hlog3 : Real.log (s + 2) ≤ Real.log s + Real.log 3 := by
      have h1 : s + 2 ≤ 3 * s := by linarith
      have h2 : Real.log (s + 2) ≤ Real.log (3 * s) := Real.log_le_log (by linarith) h1
      rw [Real.log_mul (by norm_num) (ne_of_gt hs0)] at h2
      linarith
    have hlog0 : 0 ≤ Real.log (s + 2) := Real.log_nonneg (by linarith)
    have hAle : A * Real.log (s + 2) ≤ |A| * (Real.log s + Real.log 3) := by
      have h1 : A * Real.log (s + 2) ≤ |A| * Real.log (s + 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self A) hlog0
      have h2 : |A| * Real.log (s + 2) ≤ |A| * (Real.log s + Real.log 3) :=
        mul_le_mul_of_nonneg_left hlog3 (abs_nonneg A)
      linarith
    have hbig : |A| * Real.log 3 + B ≤ Real.log s := by
      have := Real.log_le_log (Real.exp_pos (|A| * Real.log 3 + B)) hs2
      rwa [Real.log_exp] at this
    have := hAB s hs1
    rw [hK]
    nlinarith [this, hAle, hbig]
  exact hev.frequently

/-- **The dominant-constant-term case: the Euler relation forces a polynomial.** -/
theorem exists_polynomial_of_dominant_constant_term {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {m : ℕ} (hm : 1 ≤ m) {C : ℕ → Polynomial ℂ} (hCm : C m ≠ 0) (hC0 : C 0 ≠ 0)
    (hdom : ∀ k, 1 ≤ k → k ≤ m → (C k).natDegree + k + 1 ≤ (C 0).natDegree)
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1), (C k).eval (f z) * (z * deriv f z) ^ k = 0) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z := by
  obtain ⟨cw, R₂, hcw0, hR₂1, hwild⟩ :=
    exists_wild_of_dominant_constant_term hm hCm hC0 hdom (Y := f)
      (W := fun z => z * deriv f z) hrel
  obtain ⟨A, B, hAB⟩ := exists_characteristic_le_log_of_wild hf hm hcw0 hR₂1 hwild
  exact exists_polynomial_of_characteristic_le_log hf hAB

/-- A function that agrees with a polynomial has finitely many nonzero Taylor coefficients. -/
theorem eventually_taylorCoeff_eq_zero_of_polynomial {f : ℂ → ℂ} {p : Polynomial ℂ}
    (hp : ∀ z : ℂ, f z = p.eval z) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → taylorCoeff f n = 0 := by
  classical
  set D : ℕ := p.natDegree with hD
  set S : ℝ := ∑ i ∈ Finset.range (D + 1), ‖p.coeff i‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨D + 1, fun n hn => ?_⟩
  by_contra hne
  have hpos : 0 < ‖taylorCoeff f n‖ := norm_pos_iff.mpr hne
  set Rr : ℝ := S / ‖taylorCoeff f n‖ + 2 with hRr
  have hRr1 : (1 : ℝ) ≤ Rr := by
    have h0 : 0 ≤ S / ‖taylorCoeff f n‖ := by positivity
    rw [hRr]; linarith
  have hRr0 : (0 : ℝ) < Rr := by linarith
  have hbound : ∀ z : ℂ, ‖z‖ = Rr → ‖f z‖ ≤ S * Rr ^ D := by
    intro z hznorm
    rw [hp z]
    have hb := norm_eval_le_mul_pow p (y := z) (by rw [hznorm]; exact hRr1)
    rw [hznorm] at hb
    exact hb
  have hfdiff : Differentiable ℂ f := by
    have hfe : f = fun z => p.eval z := funext hp
    rw [hfe]
    exact p.differentiable
  have hcauchy := norm_taylorCoeff_le (f := f) hfdiff (R := Rr) (C := S * Rr ^ D) hRr0 hbound n
  have hsplit : Rr ^ n = Rr ^ D * Rr ^ (n - D) := by
    rw [← pow_add]
    congr 1
    omega
  have hge : Rr ≤ Rr ^ (n - D) := by
    have h1 : 1 ≤ n - D := by omega
    calc Rr = Rr ^ 1 := (pow_one Rr).symm
      _ ≤ Rr ^ (n - D) := pow_le_pow_right₀ hRr1 h1
  have hRD0 : (0 : ℝ) < Rr ^ D := by positivity
  have hkey : ‖taylorCoeff f n‖ ≤ S / Rr ^ (n - D) := by
    refine le_trans hcauchy ?_
    rw [hsplit, div_le_div_iff₀ (by positivity) (by positivity)]
    ring_nf
    nlinarith [hS0, hRD0]
  have hSlt : S / Rr ^ (n - D) < ‖taylorCoeff f n‖ := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : S / ‖taylorCoeff f n‖ < Rr := by rw [hRr]; linarith
    rw [div_lt_iff₀ hpos] at h1
    nlinarith [h1, hge, hpos]
  linarith [hkey, hSlt]

set_option maxHeartbeats 1000000 in
/-- **The Euler relation forces a polynomial, with no hypothesis on the Newton configuration.**
An entire `f` satisfying `∑_{k ≤ m} C_k(f)·(z f′)^k = 0` with `C_m ≠ 0` and `m ≥ 1` has only
finitely many nonzero Taylor coefficients.  The largest index carrying the maximal total degree is
either positive — where Gol'dberg's bound and the Wiman--Valiron dichotomy apply — or zero, where the
constant term dominates and the wild bound holds at every point, forcing `T(r,f) = O(log r)`. -/
theorem eventually_taylorCoeff_eq_zero_of_euler_relation_general {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    {m : ℕ} (hm : 1 ≤ m) {C : ℕ → Polynomial ℂ} (hCm : C m ≠ 0)
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1), (C k).eval (f z) * (z * deriv f z) ^ k = 0) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → taylorCoeff f n = 0 := by
  classical
  set S : Finset ℕ := (Finset.range (m + 1)).filter (fun k => C k ≠ 0) with hSdef
  have hmS : m ∈ S := by
    rw [hSdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hCm⟩
  have hSne : S.Nonempty := ⟨m, hmS⟩
  set d : ℕ := S.sup (fun k => (C k).natDegree + k) with hddef
  have hdle : ∀ k ∈ S, (C k).natDegree + k ≤ d := by
    intro k hk
    rw [hddef]
    exact Finset.le_sup (f := fun k => (C k).natDegree + k) hk
  have hdm : (C m).natDegree + m ≤ d := hdle m hmS
  set Tset : Finset ℕ := S.filter (fun k => (C k).natDegree + k = d) with hTdef
  have hTne : Tset.Nonempty := by
    obtain ⟨k, hkS, hkeq⟩ := Finset.exists_mem_eq_sup S hSne (fun k => (C k).natDegree + k)
    exact ⟨k, Finset.mem_filter.mpr ⟨hkS, hkeq.symm⟩⟩
  set ms : ℕ := Tset.max' hTne with hmsdef
  have hmsT : ms ∈ Tset := Tset.max'_mem hTne
  have hmsS : ms ∈ S := (Finset.mem_filter.mp hmsT).1
  have hmsd : (C ms).natDegree + ms = d := (Finset.mem_filter.mp hmsT).2
  have hmsrange : ms ∈ Finset.range (m + 1) := by
    rw [hSdef] at hmsS
    exact (Finset.mem_filter.mp hmsS).1
  have hmsm : ms ≤ m := by
    have := Finset.mem_range.mp hmsrange
    omega
  have hCms : C ms ≠ 0 := by
    rw [hSdef] at hmsS
    exact (Finset.mem_filter.mp hmsS).2
  have hdegtop : ∀ k ≤ m, (C k).natDegree + k ≤ (C ms).natDegree + ms := by
    intro k hk
    rw [hmsd]
    by_cases hCk : C k = 0
    · rw [hCk, Polynomial.natDegree_zero, zero_add]
      omega
    · refine hdle k ?_
      rw [hSdef]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hCk⟩
  have htopmax : ∀ k ≤ m, (C k).natDegree + k = (C ms).natDegree + ms → k ≤ ms := by
    intro k hk hkeq
    rw [hmsd] at hkeq
    by_cases hCk : C k = 0
    · exfalso
      rw [hCk, Polynomial.natDegree_zero, zero_add] at hkeq
      have hkm : k = m := by omega
      rw [hkm] at hCk
      exact hCm hCk
    · refine Finset.le_max' Tset k ?_
      rw [hTdef, hSdef]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hCk⟩, hkeq⟩
  rcases Nat.eq_zero_or_pos ms with hms0 | hms1
  · -- the constant term carries the maximal total degree
    have hC0 : C 0 ≠ 0 := by rw [← hms0]; exact hCms
    have hdom : ∀ k, 1 ≤ k → k ≤ m → (C k).natDegree + k + 1 ≤ (C 0).natDegree := by
      intro k hk1 hkm
      have hle := hdegtop k hkm
      rw [hms0, Nat.add_zero] at hle
      rcases Nat.lt_or_ge ((C k).natDegree + k) ((C 0).natDegree) with hlt | hge
      · omega
      · exfalso
        have heq : (C k).natDegree + k = (C ms).natDegree + ms := by
          rw [hms0, Nat.add_zero]
          omega
        have := htopmax k hkm heq
        omega
    obtain ⟨p, hp⟩ := exists_polynomial_of_dominant_constant_term hf hm hCm hC0 hdom hrel
    exact eventually_taylorCoeff_eq_zero_of_polynomial hp
  · exact eventually_taylorCoeff_eq_zero_of_euler_relation hf hm hCm hms1 hmsm hCms hdegtop
      htopmax hrel

end GaloisForLFunctions.HTGeometry
