import GaloisForLFunctions.HTGeometry.SturmAmplitudeEnvelope

/-!
# The sharp majorant of the Sturm amplitude on a barrier

`abs_deriv_sturmAmplitudeVar_le` bounds the logarithmic derivative of the amplitude by
`2k + |K'|/K`, with `k = sqrt K / p` the local rate.  On a barrier that bound is lossy by a factor
two in the *scale* term: the amplitude of the recessive branch behaves like `K^(-1/2)`, not like
`K^(-1)`, so the sharp majorant is

```text
-G'/G  =  2k + (1/2)(K'/K)  +  error ,
```

and the error is governed entirely by the deviation of the Riccati ratio

```text
rho = -(p R')/(sqrt K · R)
```

from one.  Writing `G = R²(1 + rho²)` and using `Q p = -K`, the derivative collapses to
`G' = -R²(4 k rho + rho² K'/K)`, whence the identity

```text
G'/G + 2k + (1/2)(K'/K)  =  ( 2k (1 - rho)² + (K'/K)(1 - rho²)/2 ) / (1 + rho²) .
```

Both error terms are quadratic in `rho - 1`, which is what makes their accumulated mass finite on a
barrier whose length grows: the first is `2k(1-rho)²` and the second is `|K'/K|·|1-rho²|/2`.  The
crude majorant, by contrast, keeps the full `|K'|/K`, whose mass is a logarithm of the scale ratio.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

/-- The Riccati ratio of a solution against the local rate, `rho = -(p R')/(sqrt K · R)`. -/
def sturmRiccatiRatio (p R DR K : ℝ → ℝ) (y : ℝ) : ℝ :=
  -(p y * DR y) / (Real.sqrt (K y) * R y)

theorem sturmRiccatiRatio_spec {p R DR K : ℝ → ℝ} {y : ℝ} (hK : 0 < K y) (hR : R y ≠ 0) :
    p y * DR y = -(Real.sqrt (K y) * (sturmRiccatiRatio p R DR K y * R y)) := by
  have hsq : Real.sqrt (K y) ≠ 0 := (Real.sqrt_pos.2 hK).ne'
  rw [sturmRiccatiRatio]
  field_simp

/-- The amplitude in terms of the Riccati ratio. -/
theorem sturmAmplitudeVar_eq_mul_one_add_sq {p R DR K : ℝ → ℝ} {y ρ : ℝ} (hK : 0 < K y)
    (hρ : p y * DR y = -(Real.sqrt (K y) * (ρ * R y))) :
    sturmAmplitudeVar p R DR K y = R y ^ 2 * (1 + ρ ^ 2) := by
  have hsq : Real.sqrt (K y) ^ 2 = K y := Real.sq_sqrt hK.le
  rw [sturmAmplitudeVar, hρ]
  have hnum : (-(Real.sqrt (K y) * (ρ * R y))) ^ 2 = K y * (ρ ^ 2 * R y ^ 2) := by
    rw [neg_pow, mul_pow, mul_pow, hsq]
    ring
  rw [hnum]
  field_simp

/-- **The sharp majorant identity.**  On a barrier the logarithmic derivative of the amplitude
deviates from `-(2k + (1/2) K'/K)` by terms quadratic in the deviation of the Riccati ratio from
one. -/
theorem abs_logDeriv_sturmAmplitudeVar_sub_sharp {p Q R DR K DK : ℝ → ℝ} {y ρ : ℝ}
    (hK : 0 < K y) (hp : 0 < p y) (hQ : Q y * p y = -(K y)) (hR : R y ≠ 0)
    (hρ : p y * DR y = -(Real.sqrt (K y) * (ρ * R y))) :
    |(2 * R y * (p y * DR y) * (1 / p y - Q y / K y)
        - (p y * DR y) ^ 2 * DK y / K y ^ 2) / sturmAmplitudeVar p R DR K y
      + (2 * (Real.sqrt (K y) / p y) + DK y / K y / 2)|
      ≤ 2 * (Real.sqrt (K y) / p y) * (1 - ρ) ^ 2
        + |DK y / K y| * |1 - ρ ^ 2| / 2 := by
  have hsq : Real.sqrt (K y) ^ 2 = K y := Real.sq_sqrt hK.le
  have hsqpos : 0 < Real.sqrt (K y) := Real.sqrt_pos.2 hK
  have hG : sturmAmplitudeVar p R DR K y = R y ^ 2 * (1 + ρ ^ 2) :=
    sturmAmplitudeVar_eq_mul_one_add_sq hK hρ
  have hρ0 : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
  have hR2 : (0 : ℝ) < R y ^ 2 := by positivity
  set k : ℝ := Real.sqrt (K y) / p y with hkdef
  have hk0 : 0 ≤ k := by
    rw [hkdef]
    positivity
  set d : ℝ := DK y / K y with hddef
  -- the drift coefficient collapses
  have hcoef : 1 / p y - Q y / K y = 2 / p y := by
    have hQval : Q y = -(K y) / p y := by
      field_simp at hQ ⊢
      linarith [hQ]
    rw [hQval]
    field_simp
    norm_num
  -- the numerator, in terms of the ratio
  have hnum : 2 * R y * (p y * DR y) * (1 / p y - Q y / K y)
      - (p y * DR y) ^ 2 * DK y / K y ^ 2
      = -(R y ^ 2 * (4 * k * ρ + ρ ^ 2 * d)) := by
    rw [hcoef, hρ, hkdef, hddef]
    have hnumsq : (-(Real.sqrt (K y) * (ρ * R y))) ^ 2 = K y * (ρ ^ 2 * R y ^ 2) := by
      rw [neg_pow, mul_pow, mul_pow, hsq]
      ring
    rw [hnumsq]
    field_simp
    ring
  rw [hnum, hG]
  have hquot : -(R y ^ 2 * (4 * k * ρ + ρ ^ 2 * d)) / (R y ^ 2 * (1 + ρ ^ 2))
      = -((4 * k * ρ + ρ ^ 2 * d) / (1 + ρ ^ 2)) := by
    rw [neg_div]
    congr 1
    rw [mul_div_mul_left _ _ (ne_of_gt hR2)]
  rw [hquot]
  have hkey : -((4 * k * ρ + ρ ^ 2 * d) / (1 + ρ ^ 2)) + (2 * k + d / 2)
      = (2 * k * (1 - ρ) ^ 2 + d * (1 - ρ ^ 2) / 2) / (1 + ρ ^ 2) := by
    field_simp
    ring
  rw [hkey]
  have habs : |(2 * k * (1 - ρ) ^ 2 + d * (1 - ρ ^ 2) / 2) / (1 + ρ ^ 2)|
      ≤ (2 * k * (1 - ρ) ^ 2 + |d| * |1 - ρ ^ 2| / 2) / (1 + ρ ^ 2) := by
    rw [abs_div, abs_of_pos hρ0]
    refine div_le_div_of_nonneg_right ?_ hρ0.le
    calc |2 * k * (1 - ρ) ^ 2 + d * (1 - ρ ^ 2) / 2|
        ≤ |2 * k * (1 - ρ) ^ 2| + |d * (1 - ρ ^ 2) / 2| := abs_add_le _ _
      _ = 2 * k * (1 - ρ) ^ 2 + |d| * |1 - ρ ^ 2| / 2 := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * k * (1 - ρ) ^ 2)]
          rw [abs_div, abs_mul]
          norm_num
  refine le_trans habs ?_
  rw [div_le_iff₀ hρ0]
  have hLnn : (0 : ℝ) ≤ 2 * k * (1 - ρ) ^ 2 + |d| * |1 - ρ ^ 2| / 2 := by positivity
  nlinarith [hLnn, sq_nonneg ρ]


/-- The sharp majorant of the amplitude: twice the local rate plus *half* the logarithmic
variation of the scale. -/
def sturmSharpMajorant (p K DK : ℝ → ℝ) (y : ℝ) : ℝ :=
  2 * (Real.sqrt (K y) / p y) + DK y / K y / 2

/-- **The sharp two-sided amplitude transport.**  With an error control `e` dominating the
quadratic Riccati defect, the amplitude ratio across a barrier is the exponential of the sharp
majorant, to within the accumulated error mass. -/
theorem sturmAmplitudeVar_sharp_transport {p Q R DR K DK e : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hKpos : ∀ y ∈ Icc a b, 0 < K y) (hp : ∀ y ∈ Icc a b, 0 < p y)
    (hQ : ∀ y ∈ Icc a b, Q y * p y = -(K y))
    (hRne : ∀ y ∈ Icc a b, R y ≠ 0)
    (hR : ∀ y ∈ Icc a b, HasDerivAt R (DR y) y)
    (hfluxd : ∀ y ∈ Icc a b, HasDerivAt (fun t => p t * DR t) (-(Q y * R y)) y)
    (hKd : ∀ y ∈ Icc a b, HasDerivAt K (DK y) y)
    (hup : ContinuousOn (fun y => sturmSharpMajorant p K DK y + e y) (Icc a b))
    (hlo : ContinuousOn (fun y => sturmSharpMajorant p K DK y - e y) (Icc a b))
    (hbound : ∀ y ∈ Icc a b,
      2 * (Real.sqrt (K y) / p y) * (1 - sturmRiccatiRatio p R DR K y) ^ 2
        + |DK y / K y| * |1 - sturmRiccatiRatio p R DR K y ^ 2| / 2 ≤ e y) :
    sturmAmplitudeVar p R DR K b
        * Real.exp (∫ t in a..b, (sturmSharpMajorant p K DK t - e t))
      ≤ sturmAmplitudeVar p R DR K a ∧
    sturmAmplitudeVar p R DR K a
      ≤ sturmAmplitudeVar p R DR K b
        * Real.exp (∫ t in a..b, (sturmSharpMajorant p K DK t + e t)) := by
  set G : ℝ → ℝ := sturmAmplitudeVar p R DR K with hGdef
  set G' : ℝ → ℝ := fun y => 2 * R y * (p y * DR y) * (1 / p y - Q y / K y)
    - (p y * DR y) ^ 2 * DK y / K y ^ 2 with hG'def
  have hGd : ∀ y ∈ Icc a b, HasDerivAt G (G' y) y := fun y hy =>
    hasDerivAt_sturmAmplitudeVar (Q := Q) (hKpos y hy).ne' (hp y hy).ne' (hR y hy) (hfluxd y hy)
      (hKd y hy)
  have hGpos : ∀ y ∈ Icc a b, 0 < G y := by
    intro y hy
    have hρ := sturmRiccatiRatio_spec (p := p) (R := R) (DR := DR) (K := K) (y := y)
      (hKpos y hy) (hRne y hy)
    have hval : G y = R y ^ 2 * (1 + sturmRiccatiRatio p R DR K y ^ 2) :=
      sturmAmplitudeVar_eq_mul_one_add_sq (hKpos y hy) hρ
    have hR2 : (0 : ℝ) < R y ^ 2 := by
      have := hRne y hy
      positivity
    rw [hval]
    have : (0 : ℝ) < 1 + sturmRiccatiRatio p R DR K y ^ 2 := by positivity
    positivity
  have hkey : ∀ y ∈ Icc a b, |G' y / G y + sturmSharpMajorant p K DK y| ≤ e y := by
    intro y hy
    have hρ := sturmRiccatiRatio_spec (p := p) (R := R) (DR := DR) (K := K) (y := y)
      (hKpos y hy) (hRne y hy)
    have h := abs_logDeriv_sturmAmplitudeVar_sub_sharp (p := p) (Q := Q) (R := R) (DR := DR)
      (K := K) (DK := DK) (y := y) (ρ := sturmRiccatiRatio p R DR K y)
      (hKpos y hy) (hp y hy) (hQ y hy) (hRne y hy) hρ
    exact le_trans h (hbound y hy)
  have hupper : ∀ y ∈ Icc a b, G' y ≤ -(sturmSharpMajorant p K DK y - e y) * G y := by
    intro y hy
    have h := abs_le.mp (hkey y hy)
    have hG0 : 0 < G y := hGpos y hy
    have h2 : G' y / G y ≤ e y - sturmSharpMajorant p K DK y := by linarith [h.2]
    rw [div_le_iff₀ hG0] at h2
    calc G' y ≤ (e y - sturmSharpMajorant p K DK y) * G y := h2
      _ = -(sturmSharpMajorant p K DK y - e y) * G y := by ring
  have hlower : ∀ y ∈ Icc a b, -(sturmSharpMajorant p K DK y + e y) * G y ≤ G' y := by
    intro y hy
    have h := abs_le.mp (hkey y hy)
    have hG0 : 0 < G y := hGpos y hy
    have h2 : -(e y) - sturmSharpMajorant p K DK y ≤ G' y / G y := by linarith [h.1]
    rw [le_div_iff₀ hG0] at h2
    calc -(sturmSharpMajorant p K DK y + e y) * G y
        = (-(e y) - sturmSharpMajorant p K DK y) * G y := by ring
      _ ≤ G' y := h2
  constructor
  · have hU : ContinuousOn (fun y => -(sturmSharpMajorant p K DK y - e y)) (Icc a b) := hlo.neg
    have h := le_mul_exp_integral_of_logDeriv_le' hab hGd hGpos hU hupper
    have hint : (∫ t in a..b, -(sturmSharpMajorant p K DK t - e t))
        = -∫ t in a..b, (sturmSharpMajorant p K DK t - e t) := intervalIntegral.integral_neg
    rw [hint, Real.exp_neg] at h
    have hpos : (0 : ℝ) < Real.exp (∫ t in a..b, (sturmSharpMajorant p K DK t - e t)) :=
      Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right h hpos.le
    calc G b * Real.exp (∫ t in a..b, (sturmSharpMajorant p K DK t - e t))
        ≤ (G a * (Real.exp (∫ t in a..b, (sturmSharpMajorant p K DK t - e t)))⁻¹)
            * Real.exp (∫ t in a..b, (sturmSharpMajorant p K DK t - e t)) := hmul
      _ = G a := by field_simp
  · have hL : ContinuousOn (fun y => -(sturmSharpMajorant p K DK y + e y)) (Icc a b) := hup.neg
    have h := mul_exp_integral_le_of_logDeriv_ge' hab hGd hGpos hL hlower
    have hint : (∫ t in a..b, -(sturmSharpMajorant p K DK t + e t))
        = -∫ t in a..b, (sturmSharpMajorant p K DK t + e t) := intervalIntegral.integral_neg
    rw [hint, Real.exp_neg] at h
    have hpos : (0 : ℝ) < Real.exp (∫ t in a..b, (sturmSharpMajorant p K DK t + e t)) :=
      Real.exp_pos _
    rw [mul_inv_le_iff₀ hpos] at h
    linarith [h]

end GaloisForLFunctions.HTGeometry

end
