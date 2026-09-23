import GaloisForLFunctions.RHTower.ProlateBandErrorMass
import GaloisForLFunctions.RHTower.ProlateBarrierRatioSharp
import GaloisForLFunctions.RHTower.ProlatePhaseSeparation

/-!
# The sharp amplitude transport of the prolate band

The abstract transport `sturmAmplitudeVar_sharp_transport` applies to the band data
`p = 1 - y²`, `Q = c²(s - y²)`, `K = prolateBandScale c s`, with the error control

```text
e(y) = 2 c P(y) δ(y)² + |K'/K| · δ(y)(2 + δ(y)) / 2 ,     δ(y) = (1/y + 9/(1-y)) / (c P(y)) ,
```

where `δ` is the two-sided Riccati defect of `abs_one_sub_sturmRiccatiRatio_prolate_le`.  The
identity `Q p = -K` and the evaluation `sqrt K / p = c P` are both immediate from the definitions,
so the whole instantiation is the verification that `δ` dominates the two quadratic error terms.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

theorem div_le_div_right_of_le {a b d : ℝ} (h : a ≤ b) (hd : 0 < d) : a / d ≤ b / d := by
  have hstep := mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.2 hd))
  simpa [div_eq_mul_inv] using hstep

/-- The two-sided Riccati defect of the band. -/
def prolateRiccatiDefect (c s y : ℝ) : ℝ :=
  (1 / y + 9 / (1 - y)) / (c * prolateWKBProfile s y)

/-- The error control of the sharp band transport. -/
def prolateBandErrorControl (c s y : ℝ) : ℝ :=
  2 * (c * prolateWKBProfile s y) * prolateRiccatiDefect c s y ^ (2 : ℕ)
    + |prolateBandScaleDeriv c s y / prolateBandScale c s y|
      * (prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y)) / 2

theorem prolateRiccatiDefect_nonneg {c s y : ℝ} (hc : 0 < c) (hsy : s < y ^ (2 : ℕ)) (hy0 : 0 < y)
    (hy1 : y < 1) : 0 ≤ prolateRiccatiDefect c s y := by
  have h2 : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hP : 0 < prolateWKBProfile s y := by
    rw [prolateWKBProfile]
    exact Real.sqrt_pos.2 (by positivity)
  rw [prolateRiccatiDefect]
  have h1y : (0 : ℝ) < 1 - y := by linarith
  positivity

/-- The band data satisfies the structural identity `Q p = -K`. -/
theorem prolateBand_Q_mul_p {c s y : ℝ} :
    c ^ (2 : ℕ) * (s - y ^ (2 : ℕ)) * (1 - y ^ (2 : ℕ)) = -(prolateBandScale c s y) := by
  rw [prolateBandScale]
  ring

/-- The local rate of the band is the scaled WKB profile. -/
theorem sqrt_prolateBandScale_div {c s y : ℝ} (hc : 0 < c) (hsy : s < y ^ (2 : ℕ)) (hy : y ^ (2 : ℕ) < 1) :
    Real.sqrt (prolateBandScale c s y) / (1 - y ^ (2 : ℕ)) = c * prolateWKBProfile s y := by
  have h2 : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by linarith
  rw [sqrt_prolateBandScale_eq hc hsy hy]
  field_simp

/-- **The error control dominates the quadratic Riccati defect.** -/
theorem prolateBand_error_bound {c s y : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hsy : s < y ^ (2 : ℕ)) (hy0 : 0 < y) (hy1 : y < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ t = -(s * c ^ (2 : ℕ)) * Φ t)
    (hpos : ∀ t ∈ Icc y 1, 0 < Φ t)
    (hbar : prolateLogDeriv Φ y ≤ prolateAnchoredBarrier c (-(s * c ^ (2 : ℕ))) y)
    (hs1 : s < 1) :
    2 * (Real.sqrt (prolateBandScale c s y) / (1 - y ^ (2 : ℕ)))
        * (1 - sturmRiccatiRatio (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) y) ^ (2 : ℕ)
      + |prolateBandScaleDeriv c s y / prolateBandScale c s y|
        * |1 - sturmRiccatiRatio (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) y ^ (2 : ℕ)| / 2
      ≤ prolateBandErrorControl c s y := by
  have hy2 : y ^ (2 : ℕ) < 1 := by nlinarith
  set ρ : ℝ := sturmRiccatiRatio (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) y with hρ
  have hδ := abs_one_sub_sturmRiccatiRatio_prolate_le (c := c) (s := s) (y := y)
    (Φ := Φ) (DΦ := deriv Φ) hc hsy hy0 hy1 hsm heig hpos hbar rfl hs1
  rw [← hρ] at hδ
  have hδ' : |1 - ρ| ≤ prolateRiccatiDefect c s y := hδ
  have hδnn : 0 ≤ prolateRiccatiDefect c s y :=
    prolateRiccatiDefect_nonneg hc hsy hy0 hy1
  have hrate : Real.sqrt (prolateBandScale c s y) / (1 - y ^ (2 : ℕ)) = c * prolateWKBProfile s y :=
    sqrt_prolateBandScale_div hc hsy hy2
  have hratenn : (0 : ℝ) ≤ c * prolateWKBProfile s y := by
    have : (0 : ℝ) ≤ prolateWKBProfile s y := Real.sqrt_nonneg _
    positivity
  -- the quadratic term
  have hsq : (1 - ρ) ^ (2 : ℕ) ≤ prolateRiccatiDefect c s y ^ (2 : ℕ) := by
    have h := sq_abs (1 - ρ)
    nlinarith [hδ', abs_nonneg (1 - ρ), h]
  -- the cross term
  have hcross : |1 - ρ ^ (2 : ℕ)|
      ≤ prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y) := by
    have hfac : (1 : ℝ) - ρ ^ (2 : ℕ) = (1 - ρ) * (1 + ρ) := by ring
    have habs : |1 - ρ ^ (2 : ℕ)| = |1 - ρ| * |1 + ρ| := by
      rw [hfac, abs_mul]
    have hplus : |1 + ρ| ≤ 2 + prolateRiccatiDefect c s y := by
      have hid : (1 : ℝ) + ρ = 2 - (1 - ρ) := by ring
      rw [hid]
      have habs2 : |(2 : ℝ)| = 2 := by norm_num
      calc |(2 : ℝ) - (1 - ρ)| ≤ |(2 : ℝ)| + |1 - ρ| := abs_sub _ _
        _ = 2 + |1 - ρ| := by rw [habs2]
        _ ≤ 2 + prolateRiccatiDefect c s y := by linarith [hδ']
    rw [habs]
    have hnn : (0 : ℝ) ≤ |1 + ρ| := abs_nonneg _
    calc |1 - ρ| * |1 + ρ| ≤ prolateRiccatiDefect c s y * |1 + ρ| :=
          mul_le_mul_of_nonneg_right hδ' hnn
      _ ≤ prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y) :=
          mul_le_mul_of_nonneg_left hplus hδnn
  rw [prolateBandErrorControl, hrate]
  have hKnn : (0 : ℝ) ≤ |prolateBandScaleDeriv c s y / prolateBandScale c s y| := abs_nonneg _
  have hterm1 : 2 * (c * prolateWKBProfile s y) * (1 - ρ) ^ (2 : ℕ)
      ≤ 2 * (c * prolateWKBProfile s y) * prolateRiccatiDefect c s y ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hterm2 : |prolateBandScaleDeriv c s y / prolateBandScale c s y| * |1 - ρ ^ (2 : ℕ)| / 2
      ≤ |prolateBandScaleDeriv c s y / prolateBandScale c s y|
        * (prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y)) / 2 := by
    have := mul_le_mul_of_nonneg_left hcross hKnn
    linarith [this]
  linarith [hterm1, hterm2]



set_option maxHeartbeats 1600000 in
/-- **The pointwise error control, as a single fraction over `c·sqrt(y²-s)`.** -/
theorem prolateBandErrorControl_le {c s a α y : ℝ}
    (hc : 0 < c) (ha : 0 < a) (has : s < a ^ (2 : ℕ))
    (hay : a ≤ y) (hyα : y ≤ α) (hα1 : α < 1)
    (hδ1 : prolateRiccatiDefect c s y ≤ 1) :
    prolateBandErrorControl c s y
      ≤ (2 / y ^ (2 : ℕ) + 4 * (9 / (1 - α)) / a + 2 * (9 / (1 - α)) ^ (2 : ℕ)
          + 3 * (1 + 9 / (1 - α)) / Real.sqrt (y ^ (2 : ℕ) - s) ^ (2 : ℕ)
          + 3 * (1 / a + 9 / (1 - α)) / (1 - α ^ (2 : ℕ)))
        / (c * Real.sqrt (y ^ (2 : ℕ) - s)) := by
  have hy0 : 0 < y := lt_of_lt_of_le ha hay
  have hy1 : y < 1 := lt_of_le_of_lt hyα hα1
  have hy2 : y ^ (2 : ℕ) < 1 := by nlinarith
  have hsy : s < y ^ (2 : ℕ) := by nlinarith [hay, ha]
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have hα0 : (0 : ℝ) < 1 - α := by linarith
  have hαsq : (0 : ℝ) < 1 - α ^ (2 : ℕ) := by nlinarith
  set u : ℝ := Real.sqrt (y ^ (2 : ℕ) - s) with hu
  set v : ℝ := Real.sqrt (1 - y ^ (2 : ℕ)) with hv
  have hu0 : 0 < u := Real.sqrt_pos.2 (by linarith)
  have hv0 : 0 < v := Real.sqrt_pos.2 (by linarith)
  have hu2 : u ^ (2 : ℕ) = y ^ (2 : ℕ) - s := Real.sq_sqrt (by linarith)
  have hv2 : v ^ (2 : ℕ) = 1 - y ^ (2 : ℕ) := Real.sq_sqrt (by linarith)
  have hv1 : v ≤ 1 := by nlinarith [hv2, hv0]
  have hP : prolateWKBProfile s y = u / v := prolateWKBProfile_eq_div hsy.le
  set M : ℝ := 9 / (1 - α) with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  set B : ℝ := 1 / y + 9 / (1 - y) with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  have hBle : B ≤ 1 / y + M := by
    have hle : 9 / (1 - y) ≤ M := by
      rw [hM, div_le_div_iff₀ h1y hα0]
      linarith
    rw [hB]
    linarith [hle]
  have hBa : B ≤ 1 / a + M := by
    have h1a : 1 / y ≤ 1 / a := by
      rw [div_le_div_iff₀ hy0 ha]
      linarith
    linarith [hBle, h1a]
  have hcu : (0 : ℝ) < c * u := by positivity
  have hδ : prolateRiccatiDefect c s y = B * v / (c * u) := by
    rw [prolateRiccatiDefect, hP, ← hB]
    field_simp
  have hfirst : 2 * (c * prolateWKBProfile s y) * prolateRiccatiDefect c s y ^ (2 : ℕ)
      = 2 * B ^ (2 : ℕ) * v / (c * u) := by
    rw [hP, hδ]
    field_simp
  have hKle : |prolateBandScaleDeriv c s y / prolateBandScale c s y|
      ≤ 2 * y / (y ^ (2 : ℕ) - s) + 2 * y / (1 - y ^ (2 : ℕ)) := by
    have hK := abs_prolateBandScaleDeriv_div_le (c := c) (s := s) (y := y) hc hy0.le hsy hy2
    have hKpos : 0 < prolateBandScale c s y := prolateBandScale_pos hc hsy hy2
    have hval : |prolateBandScaleDeriv c s y / prolateBandScale c s y|
        = |prolateBandScaleDeriv c s y| / prolateBandScale c s y := by
      rw [abs_div, abs_of_pos hKpos]
    rw [hval]
    exact hK
  have hδ0 : 0 ≤ prolateRiccatiDefect c s y := by rw [hδ]; positivity
  have hsecond : |prolateBandScaleDeriv c s y / prolateBandScale c s y|
      * (prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y)) / 2
      ≤ (2 * y / (y ^ (2 : ℕ) - s) + 2 * y / (1 - y ^ (2 : ℕ))) * ((3 / 2) * (B * v / (c * u))) := by
    have hstep : prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y) / 2
        ≤ (3 / 2) * (B * v / (c * u)) := by
      have hd : prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y) / 2
          ≤ (3 / 2) * prolateRiccatiDefect c s y := by nlinarith [hδ1, hδ0]
      calc prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y) / 2
          ≤ (3 / 2) * prolateRiccatiDefect c s y := hd
        _ = (3 / 2) * (B * v / (c * u)) := by rw [hδ]
    have hKnn : (0 : ℝ) ≤ |prolateBandScaleDeriv c s y / prolateBandScale c s y| := abs_nonneg _
    have hcoef : (0 : ℝ) ≤ (3 / 2) * (B * v / (c * u)) := by positivity
    calc |prolateBandScaleDeriv c s y / prolateBandScale c s y|
          * (prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y)) / 2
        = |prolateBandScaleDeriv c s y / prolateBandScale c s y|
          * (prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y) / 2) := by ring
      _ ≤ |prolateBandScaleDeriv c s y / prolateBandScale c s y| * ((3 / 2) * (B * v / (c * u))) :=
          mul_le_mul_of_nonneg_left hstep hKnn
      _ ≤ (2 * y / (y ^ (2 : ℕ) - s) + 2 * y / (1 - y ^ (2 : ℕ))) * ((3 / 2) * (B * v / (c * u))) :=
          mul_le_mul_of_nonneg_right hKle hcoef
  -- the three numerator bounds
  have hBsq : 2 * B ^ (2 : ℕ) * v ≤ 2 / y ^ (2 : ℕ) + 4 * M / a + 2 * M ^ (2 : ℕ) := by
    have hv1' : 2 * B ^ (2 : ℕ) * v ≤ 2 * B ^ (2 : ℕ) := by nlinarith [hv1, hv0, sq_nonneg B]
    have hsq : B ^ (2 : ℕ) ≤ (1 / y + M) ^ (2 : ℕ) := by nlinarith [hBle, hB0]
    have hexp : 2 * (1 / y + M) ^ (2 : ℕ) = 2 / y ^ (2 : ℕ) + 4 * M / y + 2 * M ^ (2 : ℕ) := by
      field_simp
      ring
    have hMy : 4 * M / y ≤ 4 * M / a := by
      rw [div_le_div_iff₀ hy0 ha]
      nlinarith [hM0, hay]
    linarith [hv1', hsq, hexp.le, hexp.ge, hMy]
  have hyB : y * B ≤ 1 + M * y := by
    have hstep : y * B ≤ y * (1 / y + M) := by nlinarith [hBle, hy0]
    have hval : y * (1 / y + M) = 1 + M * y := by field_simp
    linarith [hstep, hval.le, hval.ge]
  have hyBv : y * B * v ≤ 1 + M := by
    have hyB0 : (0 : ℝ) ≤ y * B := le_of_lt (mul_pos hy0 hB0)
    have h1 : y * B * v ≤ y * B := by
      nlinarith [mul_le_mul_of_nonneg_left hv1 hyB0]
    nlinarith [h1, hyB, hM0, hy1]
  have hyBa : y * B ≤ 1 / a + M := by nlinarith [hBa, hy0, hy1, hB0]
  -- assemble as a single fraction
  have hid : (2 / y ^ (2 : ℕ) + 4 * M / a + 2 * M ^ (2 : ℕ) + 3 * (1 + M) / u ^ (2 : ℕ)
        + 3 * (1 / a + M) / (1 - α ^ (2 : ℕ))) / (c * u)
      = (2 / y ^ (2 : ℕ) + 4 * M / a + 2 * M ^ (2 : ℕ)) / (c * u)
        + (3 * (1 + M) / u ^ (2 : ℕ) / (c * u) + 3 * (1 / a + M) / (1 - α ^ (2 : ℕ)) / (c * u)) := by
    field_simp
    ring
  have hle1 : prolateBandErrorControl c s y
      ≤ 2 * B ^ (2 : ℕ) * v / (c * u)
        + (2 * y / (y ^ (2 : ℕ) - s) + 2 * y / (1 - y ^ (2 : ℕ))) * ((3 / 2) * (B * v / (c * u))) := by
    rw [prolateBandErrorControl, hfirst]
    linarith [hsecond]
  have hexpand : (2 * y / (y ^ (2 : ℕ) - s) + 2 * y / (1 - y ^ (2 : ℕ))) * ((3 / 2) * (B * v / (c * u)))
      = 3 * (y * B * v) / u ^ (2 : ℕ) / (c * u) + 3 * (y * B) / v / (c * u) := by
    rw [← hu2, ← hv2]
    field_simp
  rw [hexpand] at hle1
  refine le_trans hle1 ?_
  rw [hid]
  have hA : 2 * B ^ (2 : ℕ) * v / (c * u) ≤ (2 / y ^ (2 : ℕ) + 4 * M / a + 2 * M ^ (2 : ℕ)) / (c * u) :=
    div_le_div_right_of_le hBsq hcu
  have hBt : 3 * (y * B * v) / u ^ (2 : ℕ) / (c * u) ≤ 3 * (1 + M) / u ^ (2 : ℕ) / (c * u) := by
    have hnum : 3 * (y * B * v) / u ^ (2 : ℕ) ≤ 3 * (1 + M) / u ^ (2 : ℕ) :=
      div_le_div_right_of_le (by linarith [hyBv]) (by positivity)
    exact div_le_div_right_of_le hnum hcu
  have hCt : 3 * (y * B) / v / (c * u) ≤ 3 * (1 / a + M) / (1 - α ^ (2 : ℕ)) / (c * u) := by
    have hvge : (1 : ℝ) - α ^ (2 : ℕ) ≤ v := by
      have h1 : Real.sqrt (1 - α ^ (2 : ℕ)) ≤ v := by
        rw [hv]
        exact Real.sqrt_le_sqrt (by nlinarith [hyα, hy0, hα1])
      have h2 : (1 : ℝ) - α ^ (2 : ℕ) ≤ Real.sqrt (1 - α ^ (2 : ℕ)) := by
        nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - α ^ (2 : ℕ)),
          Real.sqrt_nonneg (1 - α ^ (2 : ℕ)), hαsq, hα1]
      linarith
    have hnum : 3 * (y * B) / v ≤ 3 * (1 / a + M) / (1 - α ^ (2 : ℕ)) := by
      rw [div_le_div_iff₀ hv0 hαsq]
      have hpos : (0 : ℝ) ≤ 3 * (1 / a + M) := by positivity
      nlinarith [hyBa, hvge, hαsq, hpos, hM0, ha]
    exact div_le_div_right_of_le hnum hcu
  linarith [hA, hBt, hCt]


/-- The error majorant of the band, in the three-mass shape. -/
def prolateBandErrorMajorant (c s a α : ℝ) (y : ℝ) : ℝ :=
  1 / c * (2 * (1 / (y ^ (2 : ℕ) * Real.sqrt (y ^ (2 : ℕ) - s)))
    + 3 * (1 + 9 / (1 - α)) * (1 / Real.sqrt (y ^ (2 : ℕ) - s) ^ (3 : ℕ))
    + (4 * (9 / (1 - α)) / a + 2 * (9 / (1 - α)) ^ (2 : ℕ)
        + 3 * (1 / a + 9 / (1 - α)) / (1 - α ^ (2 : ℕ))) * (1 / Real.sqrt (y ^ (2 : ℕ) - s)))

theorem prolateBandErrorControl_le_majorant {c s a α y : ℝ}
    (hc : 0 < c) (ha : 0 < a) (has : s < a ^ (2 : ℕ))
    (hay : a ≤ y) (hyα : y ≤ α) (hα1 : α < 1)
    (hδ1 : prolateRiccatiDefect c s y ≤ 1) :
    prolateBandErrorControl c s y ≤ prolateBandErrorMajorant c s a α y := by
  have h := prolateBandErrorControl_le hc ha has hay hyα hα1 hδ1
  refine le_trans h (le_of_eq ?_)
  have hy0 : 0 < y := lt_of_lt_of_le ha hay
  have hsy : s < y ^ (2 : ℕ) := by nlinarith [hay, ha]
  have hu0 : 0 < Real.sqrt (y ^ (2 : ℕ) - s) := Real.sqrt_pos.2 (by linarith)
  have hα0 : (0 : ℝ) < 1 - α := by linarith
  have hy1 : y < 1 := lt_of_le_of_lt hyα hα1
  have hαsq : (0 : ℝ) < 1 - α ^ (2 : ℕ) := by nlinarith [hα1, hy0, hay, ha]
  rw [prolateBandErrorMajorant]
  field_simp
  ring

/-- **The abstract transport defect is dominated by the majorant.** -/
theorem prolateBand_defect_le_majorant {c s a α y : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (ha : 0 < a) (has : s < a ^ (2 : ℕ))
    (hay : a ≤ y) (hyα : y ≤ α) (hα1 : α < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ t = -(s * c ^ (2 : ℕ)) * Φ t)
    (hpos : ∀ t ∈ Icc y 1, 0 < Φ t)
    (hbar : prolateLogDeriv Φ y ≤ prolateAnchoredBarrier c (-(s * c ^ (2 : ℕ))) y)
    (hs1 : s < 1) (hδ1 : prolateRiccatiDefect c s y ≤ 1) :
    2 * (Real.sqrt (prolateBandScale c s y) / (1 - y ^ (2 : ℕ)))
        * (1 - sturmRiccatiRatio (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) y) ^ (2 : ℕ)
      + |prolateBandScaleDeriv c s y / prolateBandScale c s y|
        * |1 - sturmRiccatiRatio (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) y ^ (2 : ℕ)| / 2
      ≤ prolateBandErrorMajorant c s a α y := by
  have hy0 : 0 < y := lt_of_lt_of_le ha hay
  have hy1 : y < 1 := lt_of_le_of_lt hyα hα1
  have hsy : s < y ^ (2 : ℕ) := by nlinarith [hay, ha]
  exact le_trans (prolateBand_error_bound hc hsy hy0 hy1 hsm heig hpos hbar hs1)
    (prolateBandErrorControl_le_majorant hc ha has hay hyα hα1 hδ1)


theorem continuous_prolateBandScale (c s : ℝ) : Continuous (prolateBandScale c s) := by
  unfold prolateBandScale
  fun_prop

theorem continuous_prolateBandScaleDeriv (c s : ℝ) : Continuous (prolateBandScaleDeriv c s) := by
  unfold prolateBandScaleDeriv
  fun_prop

theorem continuousOn_prolateBandErrorMajorant {c s a α : ℝ} (ha : 0 < a) (has : s < a ^ (2 : ℕ)) :
    ContinuousOn (prolateBandErrorMajorant c s a α) (Icc a α) := by
  have hmem : ∀ y ∈ Icc a α, 0 < y ∧ s < y ^ (2 : ℕ) := by
    intro y hy
    have hya : a ≤ y := hy.1
    have hy0 : 0 < y := lt_of_lt_of_le ha hya
    exact ⟨hy0, by nlinarith [hya, ha]⟩
  have hsqrt : ContinuousOn (fun y : ℝ => Real.sqrt (y ^ (2 : ℕ) - s)) (Icc a α) :=
    Real.continuous_sqrt.comp_continuousOn ((continuousOn_pow 2).sub continuousOn_const)
  have hne : ∀ y ∈ Icc a α, Real.sqrt (y ^ (2 : ℕ) - s) ≠ 0 := by
    intro y hy
    obtain ⟨_, hys⟩ := hmem y hy
    exact (Real.sqrt_pos.2 (by linarith)).ne'
  have h1 : ContinuousOn (fun y : ℝ => 1 / (y ^ (2 : ℕ) * Real.sqrt (y ^ (2 : ℕ) - s))) (Icc a α) := by
    refine ContinuousOn.div continuousOn_const ((continuousOn_pow 2).mul hsqrt) fun y hy => ?_
    obtain ⟨hy0, hys⟩ := hmem y hy
    have hp1 : (0 : ℝ) < y ^ (2 : ℕ) := by positivity
    have hp2 : 0 < Real.sqrt (y ^ (2 : ℕ) - s) := Real.sqrt_pos.2 (by linarith)
    exact (mul_pos hp1 hp2).ne'
  have h2 : ContinuousOn (fun y : ℝ => 1 / Real.sqrt (y ^ (2 : ℕ) - s) ^ (3 : ℕ)) (Icc a α) := by
    refine ContinuousOn.div continuousOn_const (hsqrt.pow 3) fun y hy => ?_
    obtain ⟨_, hys⟩ := hmem y hy
    exact (pow_pos (Real.sqrt_pos.2 (by linarith)) 3).ne'
  have h3 : ContinuousOn (fun y : ℝ => 1 / Real.sqrt (y ^ (2 : ℕ) - s)) (Icc a α) :=
    ContinuousOn.div continuousOn_const hsqrt hne
  unfold prolateBandErrorMajorant
  exact continuousOn_const.mul
    (((continuousOn_const.mul h1).add (continuousOn_const.mul h2)).add
      (continuousOn_const.mul h3))

theorem continuousOn_prolateSharpMajorant {c s a α : ℝ} (hc : 0 < c) (hα1 : α < 1) (ha : 0 < a)
    (has : s < a ^ (2 : ℕ)) :
    ContinuousOn (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c s)
      (prolateBandScaleDeriv c s)) (Icc a α) := by
  have hmem : ∀ y ∈ Icc a α, 0 < y ∧ s < y ^ (2 : ℕ) ∧ y < 1 := by
    intro y hy
    have hya : a ≤ y := hy.1
    have hy0 : 0 < y := lt_of_lt_of_le ha hya
    exact ⟨hy0, by nlinarith [hya, ha], lt_of_le_of_lt hy.2 hα1⟩
  have hpne : ∀ y ∈ Icc a α, (1 : ℝ) - y ^ (2 : ℕ) ≠ 0 := by
    intro y hy
    obtain ⟨hy0, _, hy1⟩ := hmem y hy
    have : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
    exact this.ne'
  have hKne : ∀ y ∈ Icc a α, prolateBandScale c s y ≠ 0 := by
    intro y hy
    obtain ⟨hy0, hys, hy1⟩ := hmem y hy
    have hy2 : y ^ (2 : ℕ) < 1 := by nlinarith
    have h1 : (0 : ℝ) < y ^ (2 : ℕ) - s := by linarith
    have h2 : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by linarith
    have hc0 : (0 : ℝ) < c ^ (2 : ℕ) * (y ^ (2 : ℕ) - s) * (1 - y ^ (2 : ℕ)) := by positivity
    rw [prolateBandScale]
    exact hc0.ne'
  unfold sturmSharpMajorant
  refine ContinuousOn.add ?_ ?_
  · exact continuousOn_const.mul (ContinuousOn.div
      (Real.continuous_sqrt.comp_continuousOn (continuous_prolateBandScale c s).continuousOn)
      (by fun_prop) hpne)
  · exact (ContinuousOn.div (continuous_prolateBandScaleDeriv c s).continuousOn
      (continuous_prolateBandScale c s).continuousOn hKne).div_const 2


set_option maxHeartbeats 1600000 in
/-- **The sharp two-sided amplitude transport of the prolate band.**  Both bounds carry the sharp
majorant `2 c P + (1/2)(K'/K)`; they differ only by the accumulated error majorant, whose mass is
`O(1/K²) + O(1/K) + O(1/sqrt c)` at the matching point `a = K/sqrt c`. -/
theorem prolateBand_sharp_transport {c s a α : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (ha : 0 < a) (has : s < a ^ (2 : ℕ)) (haα : a ≤ α) (hα1 : α < 1) (hs1 : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ t = -(s * c ^ (2 : ℕ)) * Φ t)
    (hode : ∀ x : ℝ, (x ^ (2 : ℕ) - 1) * deriv (deriv Φ) x + 2 * x * deriv Φ x
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * Φ x = 0)
    (hpos : ∀ t ∈ Icc a 1, 0 < Φ t)
    (hbar : ∀ y ∈ Icc a α, prolateLogDeriv Φ y ≤ prolateAnchoredBarrier c (-(s * c ^ (2 : ℕ))) y)
    (hδ1 : ∀ y ∈ Icc a α, prolateRiccatiDefect c s y ≤ 1) :
    sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) α
        * Real.exp (∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c s)
            (prolateBandScaleDeriv c s) t - prolateBandErrorMajorant c s a α t))
      ≤ sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) a ∧
    sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) a
      ≤ sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) α
        * Real.exp (∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c s)
            (prolateBandScaleDeriv c s) t + prolateBandErrorMajorant c s a α t)) := by
  have hmem : ∀ y ∈ Icc a α, 0 < y ∧ s < y ^ (2 : ℕ) ∧ y < 1 := by
    intro y hy
    have hya : a ≤ y := hy.1
    have hy0 : 0 < y := lt_of_lt_of_le ha hya
    exact ⟨hy0, by nlinarith [hya, ha], lt_of_le_of_lt hy.2 hα1⟩
  have hdiff : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hdiff2 : Differentiable ℝ (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).1
  refine sturmAmplitudeVar_sharp_transport (Q := fun t => c ^ (2 : ℕ) * (s - t ^ (2 : ℕ))) haα ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨hy0, hys, hy1⟩ := hmem y hy
    exact prolateBandScale_pos hc hys (by nlinarith)
  · intro y hy
    obtain ⟨hy0, _, hy1⟩ := hmem y hy
    nlinarith
  · intro y _
    exact prolateBand_Q_mul_p
  · intro y hy
    have hya : a ≤ y := hy.1
    exact (hpos y ⟨hya, le_trans hy.2 hα1.le⟩).ne'
  · intro y _
    exact (hdiff y).hasDerivAt
  · intro y _
    have h1 : HasDerivAt (fun u : ℝ => 1 - u ^ (2 : ℕ)) (-(2 * y)) y := by
      have h0 := (hasDerivAt_pow 2 y).const_sub 1
      refine h0.congr_deriv ?_
      push_cast
      ring
    have h := h1.mul ((hdiff2 y).hasDerivAt)
    refine h.congr_deriv ?_
    have ho := hode y
    linear_combination -ho
  · intro y _
    exact hasDerivAt_prolateBandScale c s y
  · exact (continuousOn_prolateSharpMajorant hc hα1 ha has).add
      (continuousOn_prolateBandErrorMajorant ha has)
  · exact (continuousOn_prolateSharpMajorant hc hα1 ha has).sub
      (continuousOn_prolateBandErrorMajorant ha has)
  · intro y hy
    obtain ⟨hy0, hys, hy1⟩ := hmem y hy
    have hya : a ≤ y := hy.1
    exact prolateBand_defect_le_majorant hc ha has hya hy.2 hα1 hsm heig
      (fun t ht => hpos t ⟨le_trans hya ht.1, ht.2⟩) (hbar y hy) hs1 (hδ1 y hy)


theorem integral_prolateBandScale_logDeriv {c s a b : ℝ} (hc : 0 < c) (ha : 0 < a)
    (has : s < a ^ (2 : ℕ)) (hab : a ≤ b) (hb : b < 1) :
    (∫ y in a..b, prolateBandScaleDeriv c s y / prolateBandScale c s y)
      = Real.log (prolateBandScale c s b) - Real.log (prolateBandScale c s a) := by
  have hmem : ∀ y ∈ uIcc a b, 0 < y ∧ s < y ^ (2 : ℕ) ∧ y ^ (2 : ℕ) < 1 := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hya : a ≤ y := hy.1
    have hy0 : 0 < y := lt_of_lt_of_le ha hya
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 hb
    exact ⟨hy0, by nlinarith [hya, ha], by nlinarith⟩
  have hKne : ∀ y ∈ uIcc a b, prolateBandScale c s y ≠ 0 := by
    intro y hy
    obtain ⟨_, hys, hy2⟩ := hmem y hy
    exact (prolateBandScale_pos hc hys hy2).ne'
  have hderiv : ∀ y ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => Real.log (prolateBandScale c s t))
        (prolateBandScaleDeriv c s y / prolateBandScale c s y) y := by
    intro y hy
    exact (hasDerivAt_prolateBandScale c s y).log (hKne y hy)
  have hcont : ContinuousOn (fun y : ℝ => prolateBandScaleDeriv c s y / prolateBandScale c s y)
      (uIcc a b) :=
    ContinuousOn.div (continuous_prolateBandScaleDeriv c s).continuousOn
      (continuous_prolateBandScale c s).continuousOn hKne
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- **The sharp majorant integrates to the action plus HALF the scale logarithm.** -/
theorem integral_prolateSharpMajorant {c s a b : ℝ} (hc : 0 < c) (ha : 0 < a)
    (has : s < a ^ (2 : ℕ)) (hab : a ≤ b) (hb : b < 1) :
    (∫ y in a..b, sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c s)
        (prolateBandScaleDeriv c s) y)
      = 2 * c * (bandEndpointPhase s a - bandEndpointPhase s b)
        + (Real.log (prolateBandScale c s b) - Real.log (prolateBandScale c s a)) / 2 := by
  have hmem : ∀ y ∈ uIcc a b, 0 < y ∧ s < y ^ (2 : ℕ) ∧ y ^ (2 : ℕ) < 1 := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hya : a ≤ y := hy.1
    have hy0 : 0 < y := lt_of_lt_of_le ha hya
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 hb
    exact ⟨hy0, by nlinarith [hya, ha], by nlinarith⟩
  have hKne : ∀ y ∈ uIcc a b, prolateBandScale c s y ≠ 0 := by
    intro y hy
    obtain ⟨_, hys, hy2⟩ := hmem y hy
    exact (prolateBandScale_pos hc hys hy2).ne'
  have hpne : ∀ y ∈ uIcc a b, (1 : ℝ) - y ^ (2 : ℕ) ≠ 0 := by
    intro y hy
    obtain ⟨_, _, hy2⟩ := hmem y hy
    have : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by linarith
    exact this.ne'
  have hrw : ∀ y ∈ uIcc a b,
      sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c s)
        (prolateBandScaleDeriv c s) y
      = 2 * (c * prolateWKBProfile s y)
        + prolateBandScaleDeriv c s y / prolateBandScale c s y / 2 := by
    intro y hy
    obtain ⟨_, hys, hy2⟩ := hmem y hy
    rw [sturmSharpMajorant, sqrt_prolateBandScale_div hc hys hy2]
  have hcongr : (∫ y in a..b, sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c s)
        (prolateBandScaleDeriv c s) y)
      = ∫ y in a..b, (2 * (c * prolateWKBProfile s y)
        + prolateBandScaleDeriv c s y / prolateBandScale c s y / 2) :=
    intervalIntegral.integral_congr hrw
  rw [hcongr]
  have hcontP : ContinuousOn (fun y : ℝ => 2 * (c * prolateWKBProfile s y)) (uIcc a b) := by
    have hsub : uIcc a b ⊆ Ioo (-1 : ℝ) 1 := by
      intro y hy
      obtain ⟨hy0, _, hy2⟩ := hmem y hy
      constructor <;> nlinarith
    exact (continuousOn_const.mul (continuousOn_const.mul
      ((continuousOn_prolateWKBProfile_Ioo s).mono hsub)))
  have hcontK : ContinuousOn
      (fun y : ℝ => prolateBandScaleDeriv c s y / prolateBandScale c s y / 2) (uIcc a b) :=
    (ContinuousOn.div (continuous_prolateBandScaleDeriv c s).continuousOn
      (continuous_prolateBandScale c s).continuousOn hKne).div_const 2
  rw [intervalIntegral.integral_add hcontP.intervalIntegrable hcontK.intervalIntegrable]
  have h1 : (∫ y in a..b, 2 * (c * prolateWKBProfile s y))
      = 2 * c * (bandEndpointPhase s a - bandEndpointPhase s b) := by
    have hphase := bandEndpointPhase_sub_eq_integral (s := s) (a := a) (b := b) ha.le hab hb
      (by nlinarith [has, ha])
    rw [show (fun y : ℝ => 2 * (c * prolateWKBProfile s y))
        = fun y : ℝ => (2 * c) * prolateWKBProfile s y by funext y; ring,
      intervalIntegral.integral_const_mul, ← hphase]
  have h2 : (∫ y in a..b, prolateBandScaleDeriv c s y / prolateBandScale c s y / 2)
      = (Real.log (prolateBandScale c s b) - Real.log (prolateBandScale c s a)) / 2 := by
    rw [intervalIntegral.integral_div, integral_prolateBandScale_logDeriv hc ha has hab hb]
  rw [h1, h2]


/-- With the Riccati defect below one the amplitude is at most five times the squared value: the
flux term cannot dominate. -/
theorem prolateBand_amplitude_le_five_sq {c s y : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hsy : s < y ^ (2 : ℕ)) (hy0 : 0 < y) (hy1 : y < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ t = -(s * c ^ (2 : ℕ)) * Φ t)
    (hpos : ∀ t ∈ Icc y 1, 0 < Φ t)
    (hbar : prolateLogDeriv Φ y ≤ prolateAnchoredBarrier c (-(s * c ^ (2 : ℕ))) y)
    (hs1 : s < 1) (hδ1 : prolateRiccatiDefect c s y ≤ 1) :
    sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) y
      ≤ 5 * Φ y ^ (2 : ℕ) := by
  have hy2 : y ^ (2 : ℕ) < 1 := by nlinarith
  have hKpos : 0 < prolateBandScale c s y := prolateBandScale_pos hc hsy hy2
  have hΦne : Φ y ≠ 0 := (hpos y ⟨le_rfl, hy1.le⟩).ne'
  set ρ : ℝ := sturmRiccatiRatio (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) y with hρ
  have hδ := abs_one_sub_sturmRiccatiRatio_prolate_le (c := c) (s := s) (y := y)
    (Φ := Φ) (DΦ := deriv Φ) hc hsy hy0 hy1 hsm heig hpos hbar rfl hs1
  rw [← hρ] at hδ
  have hle : |1 - ρ| ≤ 1 := le_trans hδ hδ1
  have hbound : ρ ^ (2 : ℕ) ≤ 4 := by
    have h := abs_le.mp hle
    nlinarith [h.1, h.2]
  have hspec := sturmRiccatiRatio_spec (p := fun t => 1 - t ^ (2 : ℕ)) (R := Φ) (DR := deriv Φ)
    (K := prolateBandScale c s) (y := y) hKpos hΦne
  have hG : sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) y
      = Φ y ^ (2 : ℕ) * (1 + ρ ^ (2 : ℕ)) := by
    rw [hρ]
    exact sturmAmplitudeVar_eq_mul_one_add_sq hKpos hspec
  rw [hG]
  nlinarith [hbound, sq_nonneg (Φ y)]


set_option maxHeartbeats 1600000 in
/-- **The squared value at the matching point is two-sided at the sharp rate.**  Both bounds carry
the same sharp majorant; they differ by an absolute factor five and the accumulated error mass. -/
theorem prolateBand_sq_two_sided_sharp {c s a α : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (ha : 0 < a) (has : s < a ^ (2 : ℕ)) (haα : a ≤ α) (hα1 : α < 1) (hs1 : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ t = -(s * c ^ (2 : ℕ)) * Φ t)
    (hode : ∀ x : ℝ, (x ^ (2 : ℕ) - 1) * deriv (deriv Φ) x + 2 * x * deriv Φ x
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * Φ x = 0)
    (hpos : ∀ t ∈ Icc a 1, 0 < Φ t)
    (hbar : ∀ y ∈ Icc a α, prolateLogDeriv Φ y ≤ prolateAnchoredBarrier c (-(s * c ^ (2 : ℕ))) y)
    (hδ1 : ∀ y ∈ Icc a α, prolateRiccatiDefect c s y ≤ 1) :
    Φ a ^ (2 : ℕ) ≥ sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) α
        * Real.exp (∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c s)
            (prolateBandScaleDeriv c s) t - prolateBandErrorMajorant c s a α t)) / 5 ∧
      Φ a ^ (2 : ℕ) ≤ sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) α
        * Real.exp (∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c s)
            (prolateBandScaleDeriv c s) t + prolateBandErrorMajorant c s a α t)) := by
  obtain ⟨hlow, hup⟩ := prolateBand_sharp_transport hc ha has haα hα1 hs1 hsm heig hode hpos
    hbar hδ1
  have hy1 : a < 1 := lt_of_le_of_lt haα hα1
  have ha2 : a ^ (2 : ℕ) < 1 := by nlinarith
  have hKpos : 0 < prolateBandScale c s a := prolateBandScale_pos hc has ha2
  have hsq : Φ a ^ (2 : ℕ) ≤ sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ)
      (prolateBandScale c s) a := sq_le_sturmAmplitudeVar hKpos
  have hfive : sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ (deriv Φ) (prolateBandScale c s) a
      ≤ 5 * Φ a ^ (2 : ℕ) :=
    prolateBand_amplitude_le_five_sq hc has ha hy1 hsm heig
      (fun t ht => hpos t ⟨ht.1, ht.2⟩) (hbar a ⟨le_rfl, haα⟩) hs1 (hδ1 a ⟨le_rfl, haα⟩)
  constructor
  · linarith [hlow, hfive]
  · linarith [hsq, hup]


set_option maxHeartbeats 2400000 in
/-- **The sharp amplitude ratio of two apertures at a common matching point.**  Both squared values
are pinned to their collar values by the *same* sharp majorant, so the amplitude factor cancels and
only the exponential separation of the two phases survives. -/
theorem prolateBand_sq_ratio_sharp {c sn sm a α : ℝ} {Φn Φm : ℝ → ℝ}
    (hc : 0 < c) (ha : 0 < a) (haα : a ≤ α) (hα : 1 / 2 < α) (hα1 : α < 1)
    (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hsn0 : 0 < sn) (hsn8 : sn ≤ 1 / 8) (hsna : sn < a ^ (2 : ℕ))
    (hsm0 : 0 ≤ sm) (hsm8 : sm ≤ 1 / 8) (hsma : sm < a ^ (2 : ℕ))
    (hsmn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φn)
    (heign : ∀ t ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φn t = -(sn * c ^ (2 : ℕ)) * Φn t)
    (hoden : ∀ x : ℝ, (x ^ (2 : ℕ) - 1) * deriv (deriv Φn) x + 2 * x * deriv Φn x
      - (sn * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * Φn x = 0)
    (hΦn1 : Φn 1 = 1) (hposn : ∀ t ∈ Icc a 1, 0 < Φn t)
    (hbarn : ∀ y ∈ Icc a α, prolateLogDeriv Φn y ≤ prolateAnchoredBarrier c (-(sn * c ^ (2 : ℕ))) y)
    (hδn : ∀ y ∈ Icc a α, prolateRiccatiDefect c sn y ≤ 1)
    (hsmm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φm)
    (heigm : ∀ t ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φm t = -(sm * c ^ (2 : ℕ)) * Φm t)
    (hodem : ∀ x : ℝ, (x ^ (2 : ℕ) - 1) * deriv (deriv Φm) x + 2 * x * deriv Φm x
      - (sm * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * Φm x = 0)
    (hΦm1 : Φm 1 = 1) (hposm : ∀ t ∈ Icc a 1, 0 < Φm t)
    (hbarm : ∀ y ∈ Icc a α, prolateLogDeriv Φm y ≤ prolateAnchoredBarrier c (-(sm * c ^ (2 : ℕ))) y)
    (hδm : ∀ y ∈ Icc a α, prolateRiccatiDefect c sm y ≤ 1)
    (hzn : 0 < c * bandEndpointPhase sn α) (hzm : 1 ≤ c * bandEndpointPhase sm α) :
    Φn a ^ (2 : ℕ)
      ≤ 4050 * Real.pi ^ (3 : ℕ) * (c * bandEndpointPhase sm α / (c * bandEndpointPhase sn α))
        * Real.exp (2 * (c * bandEndpointPhase sn α) - 2 * (c * bandEndpointPhase sm α)
          + (∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c sn)
              (prolateBandScaleDeriv c sn) t + prolateBandErrorMajorant c sn a α t))
          - (∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c sm)
              (prolateBandScaleDeriv c sm) t - prolateBandErrorMajorant c sm a α t)))
        * Φm a ^ (2 : ℕ) := by
  have hsn1 : sn < 1 := by linarith
  have hsm1 : sm < 1 := by linarith
  have hα1' : α < 1 := hα1
  have hzm0 : 0 < c * bandEndpointPhase sm α := lt_of_lt_of_le zero_lt_one hzm
  have hΦnα : 0 < Φn α := hposn α ⟨haα, hα1.le⟩
  have hΦmα : 0 < Φm α := hposm α ⟨haα, hα1.le⟩
  -- the collar bounds
  have hoden' : ∀ x ∈ Ioo α 1, (1 - x ^ (2 : ℕ)) * deriv (deriv Φn) x - 2 * x * deriv Φn x
      + (sn * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * Φn x = 0 := by
    intro x _
    linarith [hoden x]
  have hodem' : ∀ x ∈ Ioo α 1, (1 - x ^ (2 : ℕ)) * deriv (deriv Φm) x - 2 * x * deriv Φm x
      + (sm * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * Φm x = 0 := by
    intro x _
    linarith [hodem x]
  have hcolln : Φn α ^ (2 : ℕ) ≤ 9 * Real.pi / 2
      * Real.exp (2 * (c * bandEndpointPhase sn α)) / (c * bandEndpointPhase sn α) :=
    prolateBand_collar_sq_le hsn0.le hsn8 hc hα hα1 hcollar hsmn hoden' hΦn1 hzn hΦnα.le
  have hcollm : Real.exp (c * bandEndpointPhase sm α)
      / (6 * Real.pi * Real.sqrt (c * bandEndpointPhase sm α)) ≤ Φm α :=
    exp_div_le_prolateBand_collar hsm0 hsm8 hc hα hα1 hcollar hsmm hodem' hΦm1 hzm
  have hcollm2 : Real.exp (2 * (c * bandEndpointPhase sm α))
      / (36 * Real.pi ^ (2 : ℕ) * (c * bandEndpointPhase sm α)) ≤ Φm α ^ (2 : ℕ) := by
    have hden : (0 : ℝ) < 6 * Real.pi * Real.sqrt (c * bandEndpointPhase sm α) := by
      have h1 : (0 : ℝ) < Real.sqrt (c * bandEndpointPhase sm α) := Real.sqrt_pos.2 hzm0
      have := Real.pi_pos
      positivity
    have hnn : (0 : ℝ) ≤ Real.exp (c * bandEndpointPhase sm α)
        / (6 * Real.pi * Real.sqrt (c * bandEndpointPhase sm α)) := le_of_lt (by positivity)
    have hsq := pow_le_pow_left₀ hnn hcollm 2
    have hval : (Real.exp (c * bandEndpointPhase sm α)
        / (6 * Real.pi * Real.sqrt (c * bandEndpointPhase sm α))) ^ (2 : ℕ)
        = Real.exp (2 * (c * bandEndpointPhase sm α))
          / (36 * Real.pi ^ (2 : ℕ) * (c * bandEndpointPhase sm α)) := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hzm0.le, ← Real.exp_nat_mul]
      norm_num
    rwa [hval] at hsq
  -- the two-sided transports
  obtain ⟨hnlow, hnup⟩ := prolateBand_sq_two_sided_sharp hc ha hsna haα hα1 hsn1 hsmn heign
    hoden hposn hbarn hδn
  obtain ⟨hmlow, hmup⟩ := prolateBand_sq_two_sided_sharp hc ha hsma haα hα1 hsm1 hsmm heigm
    hodem hposm hbarm hδm
  -- the amplitude at the collar
  have hGn : sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φn (deriv Φn) (prolateBandScale c sn) α
      ≤ 5 * Φn α ^ (2 : ℕ) :=
    prolateBand_amplitude_le_five_sq hc (by nlinarith [hsna, haα, ha]) (lt_of_lt_of_le ha haα)
      hα1 hsmn heign (fun t ht => hposn t ⟨le_trans haα ht.1, ht.2⟩)
      (hbarn α ⟨haα, le_rfl⟩) hsn1 (hδn α ⟨haα, le_rfl⟩)
  have hGm : Φm α ^ (2 : ℕ)
      ≤ sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φm (deriv Φm) (prolateBandScale c sm) α := by
    have hα2 : α ^ (2 : ℕ) < 1 := by nlinarith
    exact sq_le_sturmAmplitudeVar (prolateBandScale_pos hc (by nlinarith [hsma, haα, ha]) hα2)
  set zn : ℝ := c * bandEndpointPhase sn α with hzndef
  set zm : ℝ := c * bandEndpointPhase sm α with hzmdef
  set Eup : ℝ := ∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c sn)
      (prolateBandScaleDeriv c sn) t + prolateBandErrorMajorant c sn a α t) with hEup
  set Elo : ℝ := ∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c sm)
      (prolateBandScaleDeriv c sm) t - prolateBandErrorMajorant c sm a α t) with hElo
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hn : Φn a ^ (2 : ℕ) ≤ 5 * (9 * Real.pi / 2) * (Real.exp (2 * zn) / zn) * Real.exp Eup := by
    have h1 : Φn a ^ (2 : ℕ) ≤ 5 * Φn α ^ (2 : ℕ) * Real.exp Eup := by
      have := mul_le_mul_of_nonneg_right hGn (Real.exp_pos Eup).le
      linarith [hnup, this]
    have h2 : 5 * Φn α ^ (2 : ℕ) * Real.exp Eup
        ≤ 5 * (9 * Real.pi / 2 * Real.exp (2 * zn) / zn) * Real.exp Eup := by
      have hstep : 5 * Φn α ^ (2 : ℕ) ≤ 5 * (9 * Real.pi / 2 * Real.exp (2 * zn) / zn) := by
        linarith [hcolln]
      exact mul_le_mul_of_nonneg_right hstep (Real.exp_pos Eup).le
    have h3 : 5 * (9 * Real.pi / 2 * Real.exp (2 * zn) / zn) * Real.exp Eup
        = 5 * (9 * Real.pi / 2) * (Real.exp (2 * zn) / zn) * Real.exp Eup := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hm : Real.exp (2 * zm) / (180 * Real.pi ^ (2 : ℕ) * zm) * Real.exp Elo ≤ Φm a ^ (2 : ℕ) := by
    have h1 : Real.exp (2 * zm) / (36 * Real.pi ^ (2 : ℕ) * zm) * Real.exp Elo / 5 ≤ Φm a ^ (2 : ℕ) := by
      have hstep : Real.exp (2 * zm) / (36 * Real.pi ^ (2 : ℕ) * zm) * Real.exp Elo
          ≤ Φm α ^ (2 : ℕ) * Real.exp Elo :=
        mul_le_mul_of_nonneg_right hcollm2 (Real.exp_pos Elo).le
      have hstep2 : Φm α ^ (2 : ℕ) * Real.exp Elo
          ≤ sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φm (deriv Φm) (prolateBandScale c sm) α
            * Real.exp Elo := mul_le_mul_of_nonneg_right hGm (Real.exp_pos Elo).le
      linarith [hmlow, hstep, hstep2]
    have hval : Real.exp (2 * zm) / (36 * Real.pi ^ (2 : ℕ) * zm) * Real.exp Elo / 5
        = Real.exp (2 * zm) / (180 * Real.pi ^ (2 : ℕ) * zm) * Real.exp Elo := by
      field_simp
      ring
    linarith [h1, hval.le, hval.ge]
  have hexp : Real.exp (2 * zn - 2 * zm + Eup - Elo) * (Real.exp (2 * zm) * Real.exp Elo)
      = Real.exp (2 * zn) * Real.exp Eup := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hcoef : (0 : ℝ) ≤ 4050 * Real.pi ^ (3 : ℕ) * (zm / zn)
      * Real.exp (2 * zn - 2 * zm + Eup - Elo) := by positivity
  refine le_trans hn ?_
  have hkey : 4050 * Real.pi ^ (3 : ℕ) * (zm / zn) * Real.exp (2 * zn - 2 * zm + Eup - Elo)
      * (Real.exp (2 * zm) / (180 * Real.pi ^ (2 : ℕ) * zm) * Real.exp Elo)
      = 5 * (9 * Real.pi / 2) * (Real.exp (2 * zn) / zn) * Real.exp Eup := by
    have hzn0 : zn ≠ 0 := hzn.ne'
    have hzm0' : zm ≠ 0 := hzm0.ne'
    have hπ0 : Real.pi ≠ 0 := hπ.ne'
    have hrw : 4050 * Real.pi ^ (3 : ℕ) * (zm / zn) * Real.exp (2 * zn - 2 * zm + Eup - Elo)
        * (Real.exp (2 * zm) / (180 * Real.pi ^ (2 : ℕ) * zm) * Real.exp Elo)
        = (4050 * Real.pi ^ (3 : ℕ) * (zm / zn) / (180 * Real.pi ^ (2 : ℕ) * zm))
          * (Real.exp (2 * zn - 2 * zm + Eup - Elo) * (Real.exp (2 * zm) * Real.exp Elo)) := by
      ring
    rw [hrw, hexp]
    have hcoefeq : 4050 * Real.pi ^ (3 : ℕ) * (zm / zn) / (180 * Real.pi ^ (2 : ℕ) * zm)
        = 5 * (9 * Real.pi / 2) / zn := by
      field_simp
      ring
    rw [hcoefeq]
    field_simp
  rw [← hkey]
  exact mul_le_mul_of_nonneg_left hm hcoef


/-- **The exponent of the sharp ratio, in closed form.**  The two collar phases cancel exactly,
leaving the phase separation at the matching point, half the difference of the two scale logarithms,
and the two error masses. -/
theorem prolateBand_sharp_exponent_eq {c sn sm a α : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hsna : sn < a ^ (2 : ℕ)) (hsma : sm < a ^ (2 : ℕ)) (haα : a ≤ α) (hα1 : α < 1) :
    2 * (c * bandEndpointPhase sn α) - 2 * (c * bandEndpointPhase sm α)
        + (∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c sn)
            (prolateBandScaleDeriv c sn) t + prolateBandErrorMajorant c sn a α t))
        - (∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c sm)
            (prolateBandScaleDeriv c sm) t - prolateBandErrorMajorant c sm a α t))
      = 2 * c * (bandEndpointPhase sn a - bandEndpointPhase sm a)
        + (Real.log (prolateBandScale c sn α) - Real.log (prolateBandScale c sn a)) / 2
        - (Real.log (prolateBandScale c sm α) - Real.log (prolateBandScale c sm a)) / 2
        + (∫ t in a..α, prolateBandErrorMajorant c sn a α t)
        + (∫ t in a..α, prolateBandErrorMajorant c sm a α t) := by
  have hmn : IntervalIntegrable (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c sn)
      (prolateBandScaleDeriv c sn)) volume a α := by
    have h := continuousOn_prolateSharpMajorant (c := c) (s := sn) (a := a) (α := α) hc hα1 ha hsna
    rw [← uIcc_of_le haα] at h
    exact h.intervalIntegrable
  have hmm : IntervalIntegrable (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c sm)
      (prolateBandScaleDeriv c sm)) volume a α := by
    have h := continuousOn_prolateSharpMajorant (c := c) (s := sm) (a := a) (α := α) hc hα1 ha hsma
    rw [← uIcc_of_le haα] at h
    exact h.intervalIntegrable
  have hen : IntervalIntegrable (prolateBandErrorMajorant c sn a α) volume a α := by
    have h := continuousOn_prolateBandErrorMajorant (c := c) (s := sn) (a := a) (α := α) ha hsna
    rw [← uIcc_of_le haα] at h
    exact h.intervalIntegrable
  have hem : IntervalIntegrable (prolateBandErrorMajorant c sm a α) volume a α := by
    have h := continuousOn_prolateBandErrorMajorant (c := c) (s := sm) (a := a) (α := α) ha hsma
    rw [← uIcc_of_le haα] at h
    exact h.intervalIntegrable
  rw [intervalIntegral.integral_add hmn hen, intervalIntegral.integral_sub hmm hem,
    integral_prolateSharpMajorant hc ha hsna haα hα1,
    integral_prolateSharpMajorant hc ha hsma haα hα1]
  ring


theorem log_prolateBandScale {c s y : ℝ} (hc : 0 < c) (hsy : s < y ^ (2 : ℕ)) (hy2 : y ^ (2 : ℕ) < 1) :
    Real.log (prolateBandScale c s y)
      = Real.log (c ^ (2 : ℕ)) + Real.log (y ^ (2 : ℕ) - s) + Real.log (1 - y ^ (2 : ℕ)) := by
  have h1 : (c : ℝ) ^ (2 : ℕ) ≠ 0 := by positivity
  have h2 : (y : ℝ) ^ (2 : ℕ) - s ≠ 0 := by
    have : (0 : ℝ) < y ^ (2 : ℕ) - s := by linarith
    exact this.ne'
  have h3 : (1 : ℝ) - y ^ (2 : ℕ) ≠ 0 := by
    have : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by linarith
    exact this.ne'
  rw [prolateBandScale, Real.log_mul (mul_ne_zero h1 h2) h3, Real.log_mul h1 h2]

/-- **The scale-logarithm difference is bounded by an anchor term alone.**  The endpoint factors
`1 - y²` cancel between the two apertures, and the collar contribution has the favourable sign. -/
theorem prolateBand_scaleLog_diff_le {c sn sm a α : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hmn : sm ≤ sn) (hsna : sn < a ^ (2 : ℕ)) (haα : a ≤ α) (hα1 : α < 1) :
    (Real.log (prolateBandScale c sn α) - Real.log (prolateBandScale c sn a)) / 2
      - (Real.log (prolateBandScale c sm α) - Real.log (prolateBandScale c sm a)) / 2
      ≤ (Real.log (a ^ (2 : ℕ) - sm) - Real.log (a ^ (2 : ℕ) - sn)) / 2 := by
  have ha2 : a ^ (2 : ℕ) < 1 := by nlinarith [haα, hα1, ha]
  have hα2 : α ^ (2 : ℕ) < 1 := by nlinarith [hα1, haα, ha]
  have hsma : sm < a ^ (2 : ℕ) := lt_of_le_of_lt hmn hsna
  have hsnα : sn < α ^ (2 : ℕ) := by nlinarith [hsna, haα, ha]
  have hsmα : sm < α ^ (2 : ℕ) := lt_of_le_of_lt hmn hsnα
  rw [log_prolateBandScale hc hsnα hα2, log_prolateBandScale hc hsna ha2,
    log_prolateBandScale hc hsmα hα2, log_prolateBandScale hc hsma ha2]
  have hcollar : Real.log (α ^ (2 : ℕ) - sn) ≤ Real.log (α ^ (2 : ℕ) - sm) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith [hcollar]


/-- **The full exponent bound.**  The three pieces of `prolateBand_sharp_exponent_eq`, bounded. -/
theorem prolateBand_sharp_exponent_le {c sn sm a α : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hsm0 : 0 ≤ sm) (hmn : sm ≤ sn) (hsna : sn < a ^ (2 : ℕ)) (haα : a ≤ α) (hα1 : α < 1)
    (ha1 : a < 1) :
    2 * (c * bandEndpointPhase sn α) - 2 * (c * bandEndpointPhase sm α)
        + (∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c sn)
            (prolateBandScaleDeriv c sn) t + prolateBandErrorMajorant c sn a α t))
        - (∫ t in a..α, (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ)) (prolateBandScale c sm)
            (prolateBandScaleDeriv c sm) t - prolateBandErrorMajorant c sm a α t))
      ≤ -(c * (sn - sm) * Real.log (1 / a))
        + (Real.log (a ^ (2 : ℕ) - sm) - Real.log (a ^ (2 : ℕ) - sn)) / 2
        + (∫ t in a..α, prolateBandErrorMajorant c sn a α t)
        + (∫ t in a..α, prolateBandErrorMajorant c sm a α t) := by
  have hsma : sm < a ^ (2 : ℕ) := lt_of_le_of_lt hmn hsna
  rw [prolateBand_sharp_exponent_eq hc ha hsna hsma haα hα1]
  have hphase : (sn - sm) / 2 * Real.log (1 / a)
      ≤ bandEndpointPhase sm a - bandEndpointPhase sn a :=
    bandEndpointPhase_sub_ge hsm0 hmn hsna ha ha1
  have hscale := prolateBand_scaleLog_diff_le hc ha hmn hsna haα hα1
  have hmul := mul_le_mul_of_nonneg_left hphase (by positivity : (0 : ℝ) ≤ 2 * c)
  nlinarith [hmul, hscale]


/-- The WKB profile increases across the band: numerator up, denominator down. -/
theorem prolateWKBProfile_mono {s a y : ℝ} (hs1 : s < 1) (ha : 0 < a) (hsa : s < a ^ (2 : ℕ))
    (hay : a ≤ y) (hy1 : y < 1) :
    prolateWKBProfile s a ≤ prolateWKBProfile s y := by
  have ha1 : a < 1 := lt_of_le_of_lt hay hy1
  have ha2 : a ^ (2 : ℕ) < 1 := by nlinarith
  have hy0 : 0 < y := lt_of_lt_of_le ha hay
  have hy2 : y ^ (2 : ℕ) < 1 := by nlinarith
  have hsy : s < y ^ (2 : ℕ) := by nlinarith [hay, ha]
  rw [prolateWKBProfile, prolateWKBProfile]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hsq : a ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by nlinarith [hay, ha]
  nlinarith [mul_nonneg (sub_nonneg.2 hsq) (le_of_lt (sub_pos.2 hs1))]

/-- A single scalar condition at the matching point forces the Riccati defect below one on the
whole window. -/
theorem prolateRiccatiDefect_le_one {c s a α y : ℝ} (hc : 0 < c) (ha : 0 < a) (hs1 : s < 1)
    (hsa : s < a ^ (2 : ℕ)) (hay : a ≤ y) (hyα : y ≤ α) (hα1 : α < 1)
    (hsuff : 1 / a + 9 / (1 - α) ≤ c * prolateWKBProfile s a) :
    prolateRiccatiDefect c s y ≤ 1 := by
  have hy0 : 0 < y := lt_of_lt_of_le ha hay
  have hy1 : y < 1 := lt_of_le_of_lt hyα hα1
  have hα0 : (0 : ℝ) < 1 - α := by linarith
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have hsy : s < y ^ (2 : ℕ) := by nlinarith [hay, ha]
  have hy2 : y ^ (2 : ℕ) < 1 := by nlinarith
  have hPy : 0 < prolateWKBProfile s y := by
    rw [prolateWKBProfile]
    exact Real.sqrt_pos.2 (by positivity)
  have hmono : prolateWKBProfile s a ≤ prolateWKBProfile s y :=
    prolateWKBProfile_mono hs1 ha hsa hay hy1
  have hnum : 1 / y + 9 / (1 - y) ≤ 1 / a + 9 / (1 - α) := by
    have h1 : 1 / y ≤ 1 / a := by
      rw [div_le_div_iff₀ hy0 ha]
      linarith
    have h2 : 9 / (1 - y) ≤ 9 / (1 - α) := by
      rw [div_le_div_iff₀ h1y hα0]
      linarith
    linarith
  rw [prolateRiccatiDefect, div_le_one (by positivity)]
  nlinarith [hnum, hsuff, hmono, hc, hPy]


/-- **The anchored barrier dominates on the whole collar window.**  The terminal inequality is
available arbitrarily close to the endpoint, so the backward comparison reaches any fixed collar. -/
theorem prolateLogDeriv_le_anchoredBarrier_on_collar {c s a α : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs1 : s < 1) (ha : 0 < a) (haα : a ≤ α) (hα1 : α < 1) (h2sa : 2 * s ≤ a ^ (2 : ℕ))
    (hs0 : 0 ≤ s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (hpos : ∀ y ∈ Icc a 1, 0 < Φ y) :
    ∀ y ∈ Icc a α, prolateLogDeriv Φ y
      ≤ prolateAnchoredBarrier c (-(s * c ^ (2 : ℕ))) y := by
  have hev := eventually_prolateLogDeriv_le_anchoredBarrier_at_one (c := c) (s := s) (Φ := Φ)
    hc hs1 hsm hΦ1
  have h1 : ∀ᶠ b : ℝ in 𝓝[<] (1 : ℝ), α < b :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds hα1)
  have h2 : ∀ᶠ b : ℝ in 𝓝[<] (1 : ℝ), b < 1 := self_mem_nhdsWithin
  obtain ⟨b, ⟨hbterm, hαb⟩, hb1⟩ := ((hev.and h1).and h2).exists
  have hab : a ≤ b := le_trans haα hαb.le
  have hQ : ∀ y ∈ Icc a b, 0 < -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ) := by
    intro y hy
    have hya : a ≤ y := hy.1
    have hy2 : a ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by nlinarith [hya, ha]
    have hc2 : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
    have hys : 0 < y ^ (2 : ℕ) - s := by nlinarith [h2sa, hy2, hs0]
    nlinarith [mul_pos hc2 hys]
  have hcond : ∀ y ∈ Icc a b, 0 ≤ -(s * c ^ (2 : ℕ)) * (2 - y ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ) := by
    intro y hy
    have hya : a ≤ y := hy.1
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 hb1
    have hy2 : a ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by nlinarith [hya, ha]
    have hkey : 0 ≤ y ^ (2 : ℕ) * (1 + s) - 2 * s := by nlinarith [h2sa, hy2, hs0]
    nlinarith [hkey, sq_nonneg c, hc]
  have hposb : ∀ y ∈ Icc a b, 0 < Φ y := fun y hy =>
    hpos y ⟨hy.1, le_trans hy.2 hb1.le⟩
  have hmain := prolateLogDeriv_le_anchoredBarrier (c := c) (χ := -(s * c ^ (2 : ℕ))) (Φ := Φ)
    hsm heig hab ha hb1 hQ hcond hposb hbterm
  intro y hy
  exact hmain y ⟨hy.1, le_trans hy.2 hαb.le⟩


/-- **The accumulated error mass of the band, in closed form.** -/
theorem integral_prolateBandErrorMajorant_le {c s a α : ℝ} (hc : 0 < c) (hs : 0 < s) (ha : 0 < a)
    (has : s < a ^ (2 : ℕ)) (haα : a ≤ α) (hα1 : α < 1) :
    (∫ t in a..α, prolateBandErrorMajorant c s a α t)
      ≤ 1 / c * (2 * (1 / a ^ (2 : ℕ))
          + 3 * (1 + 9 / (1 - α)) * (a / (s * Real.sqrt (a ^ (2 : ℕ) - s)))
          + (4 * (9 / (1 - α)) / a + 2 * (9 / (1 - α)) ^ (2 : ℕ)
              + 3 * (1 / a + 9 / (1 - α)) / (1 - α ^ (2 : ℕ)))
            * ((α - a) / Real.sqrt (a ^ (2 : ℕ) - s))) := by
  have hα0 : (0 : ℝ) < 1 - α := by linarith
  have hαsq : (0 : ℝ) < 1 - α ^ (2 : ℕ) := by
    have ha1 : a < 1 := lt_of_le_of_lt haα hα1
    nlinarith [ha, haα, hα1]
  set M : ℝ := 9 / (1 - α) with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  set C₁ : ℝ := 3 * (1 + M) with hC₁
  set C₂ : ℝ := 4 * M / a + 2 * M ^ (2 : ℕ) + 3 * (1 / a + M) / (1 - α ^ (2 : ℕ)) with hC₂
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hfun : ∀ t : ℝ, prolateBandErrorMajorant c s a α t
      = 1 / c * (2 * (1 / (t ^ (2 : ℕ) * Real.sqrt (t ^ (2 : ℕ) - s)))
        + C₁ * (1 / Real.sqrt (t ^ (2 : ℕ) - s) ^ (3 : ℕ)) + C₂ * (1 / Real.sqrt (t ^ (2 : ℕ) - s))) := by
    intro t
    rw [prolateBandErrorMajorant, hC₁, hC₂, hM]
  have hcongr : (∫ t in a..α, prolateBandErrorMajorant c s a α t)
      = 1 / c * ∫ t in a..α, (2 * (1 / (t ^ (2 : ℕ) * Real.sqrt (t ^ (2 : ℕ) - s)))
        + C₁ * (1 / Real.sqrt (t ^ (2 : ℕ) - s) ^ (3 : ℕ)) + C₂ * (1 / Real.sqrt (t ^ (2 : ℕ) - s))) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => hfun t
  rw [hcongr]
  have hmass := integral_errorMajorant_le (s := s) (a := a) (b := α) (C₁ := C₁) (C₂ := C₂)
    hs ha has haα hC₁0 hC₂0
  have hcnn : (0 : ℝ) ≤ 1 / c := by positivity
  exact mul_le_mul_of_nonneg_left hmass hcnn

end GaloisForLFunctions.RHTower

end
