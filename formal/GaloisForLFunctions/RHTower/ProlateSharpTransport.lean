import GaloisForLFunctions.RHTower.ProlateBandErrorMass

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

set_option maxHeartbeats 3200000

noncomputable section

open Set Filter Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

/-- The two-sided Riccati defect of the band. -/
def prolateRiccatiDefect (c s y : ℝ) : ℝ :=
  (1 / y + 9 / (1 - y)) / (c * prolateWKBProfile s y)

/-- The error control of the sharp band transport. -/
def prolateBandErrorControl (c s y : ℝ) : ℝ :=
  2 * (c * prolateWKBProfile s y) * prolateRiccatiDefect c s y ^ 2
    + |prolateBandScaleDeriv c s y / prolateBandScale c s y|
      * (prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y)) / 2

theorem prolateRiccatiDefect_nonneg {c s y : ℝ} (hc : 0 < c) (hsy : s < y ^ 2) (hy0 : 0 < y)
    (hy1 : y < 1) : 0 ≤ prolateRiccatiDefect c s y := by
  have h2 : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  have hP : 0 < prolateWKBProfile s y := by
    rw [prolateWKBProfile]
    exact Real.sqrt_pos.2 (by positivity)
  rw [prolateRiccatiDefect]
  have h1y : (0 : ℝ) < 1 - y := by linarith
  positivity

/-- The band data satisfies the structural identity `Q p = -K`. -/
theorem prolateBand_Q_mul_p {c s y : ℝ} :
    c ^ 2 * (s - y ^ 2) * (1 - y ^ 2) = -(prolateBandScale c s y) := by
  rw [prolateBandScale]
  ring

/-- The local rate of the band is the scaled WKB profile. -/
theorem sqrt_prolateBandScale_div {c s y : ℝ} (hc : 0 < c) (hsy : s < y ^ 2) (hy : y ^ 2 < 1) :
    Real.sqrt (prolateBandScale c s y) / (1 - y ^ 2) = c * prolateWKBProfile s y := by
  have h2 : (0 : ℝ) < 1 - y ^ 2 := by linarith
  rw [sqrt_prolateBandScale_eq hc hsy hy]
  field_simp

/-- **The error control dominates the quadratic Riccati defect.** -/
theorem prolateBand_error_bound {c s y : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hsy : s < y ^ 2) (hy0 : 0 < y) (hy1 : y < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ t = -(s * c ^ 2) * Φ t)
    (hpos : ∀ t ∈ Icc y 1, 0 < Φ t)
    (hbar : prolateLogDeriv Φ y ≤ prolateAnchoredBarrier c (-(s * c ^ 2)) y)
    (hs1 : s < 1) :
    2 * (Real.sqrt (prolateBandScale c s y) / (1 - y ^ 2))
        * (1 - sturmRiccatiRatio (fun t => 1 - t ^ 2) Φ (deriv Φ) (prolateBandScale c s) y) ^ 2
      + |prolateBandScaleDeriv c s y / prolateBandScale c s y|
        * |1 - sturmRiccatiRatio (fun t => 1 - t ^ 2) Φ (deriv Φ) (prolateBandScale c s) y ^ 2| / 2
      ≤ prolateBandErrorControl c s y := by
  have hy2 : y ^ 2 < 1 := by nlinarith
  set ρ : ℝ := sturmRiccatiRatio (fun t => 1 - t ^ 2) Φ (deriv Φ) (prolateBandScale c s) y with hρ
  have hδ := abs_one_sub_sturmRiccatiRatio_prolate_le (c := c) (s := s) (y := y)
    (Φ := Φ) (DΦ := deriv Φ) hc hsy hy0 hy1 hsm heig hpos hbar rfl hs1
  rw [← hρ] at hδ
  have hδ' : |1 - ρ| ≤ prolateRiccatiDefect c s y := hδ
  have hδnn : 0 ≤ prolateRiccatiDefect c s y :=
    prolateRiccatiDefect_nonneg hc hsy hy0 hy1
  have hrate : Real.sqrt (prolateBandScale c s y) / (1 - y ^ 2) = c * prolateWKBProfile s y :=
    sqrt_prolateBandScale_div hc hsy hy2
  have hratenn : (0 : ℝ) ≤ c * prolateWKBProfile s y := by
    have : (0 : ℝ) ≤ prolateWKBProfile s y := Real.sqrt_nonneg _
    positivity
  -- the quadratic term
  have hsq : (1 - ρ) ^ 2 ≤ prolateRiccatiDefect c s y ^ 2 := by
    have h := sq_abs (1 - ρ)
    nlinarith [hδ', abs_nonneg (1 - ρ), h]
  -- the cross term
  have hcross : |1 - ρ ^ 2|
      ≤ prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y) := by
    have hfac : (1 : ℝ) - ρ ^ 2 = (1 - ρ) * (1 + ρ) := by ring
    have habs : |1 - ρ ^ 2| = |1 - ρ| * |1 + ρ| := by
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
  have hterm1 : 2 * (c * prolateWKBProfile s y) * (1 - ρ) ^ 2
      ≤ 2 * (c * prolateWKBProfile s y) * prolateRiccatiDefect c s y ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hterm2 : |prolateBandScaleDeriv c s y / prolateBandScale c s y| * |1 - ρ ^ 2| / 2
      ≤ |prolateBandScaleDeriv c s y / prolateBandScale c s y|
        * (prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y)) / 2 := by
    have := mul_le_mul_of_nonneg_left hcross hKnn
    linarith [this]
  linarith [hterm1, hterm2]


/-- **The pointwise error control, decomposed into the three elementary masses.** -/
theorem prolateBandErrorControl_le {c s a α y : ℝ}
    (hc : 0 < c) (ha : 0 < a) (has : s < a ^ 2)
    (hay : a ≤ y) (hyα : y ≤ α) (hα1 : α < 1)
    (hδ1 : prolateRiccatiDefect c s y ≤ 1) :
    prolateBandErrorControl c s y
      ≤ 2 / (c * (y ^ 2 * Real.sqrt (y ^ 2 - s)))
        + 3 * (1 + 9 / (1 - α)) / (c * Real.sqrt (y ^ 2 - s) ^ 3)
        + (4 * (9 / (1 - α)) / a + 2 * (9 / (1 - α)) ^ 2
            + 3 * (1 / a + 9 / (1 - α)) / (1 - α ^ 2)) / (c * Real.sqrt (y ^ 2 - s)) := by
  have hy0 : 0 < y := lt_of_lt_of_le ha hay
  have hy1 : y < 1 := lt_of_le_of_lt hyα hα1
  have hy2 : y ^ 2 < 1 := by nlinarith
  have hsy : s < y ^ 2 := by nlinarith [hay, ha]
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have hα0 : (0 : ℝ) < 1 - α := by linarith
  have hαsq : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  set u : ℝ := Real.sqrt (y ^ 2 - s) with hu
  set v : ℝ := Real.sqrt (1 - y ^ 2) with hv
  have hu0 : 0 < u := Real.sqrt_pos.2 (by linarith)
  have hv0 : 0 < v := Real.sqrt_pos.2 (by linarith)
  have hu2 : u ^ 2 = y ^ 2 - s := Real.sq_sqrt (by linarith)
  have hv2 : v ^ 2 = 1 - y ^ 2 := Real.sq_sqrt (by linarith)
  have hv1 : v ≤ 1 := by nlinarith [hv2, hv0]
  have hP : prolateWKBProfile s y = u / v := prolateWKBProfile_eq_div hsy.le
  set M : ℝ := 9 / (1 - α) with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  set B : ℝ := 1 / y + 9 / (1 - y) with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  have hBle : B ≤ 1 / y + M := by
    have hle : 9 / (1 - y) ≤ M := by
      rw [hM]
      rw [div_le_div_iff₀ h1y hα0]
      linarith
    linarith [hle]
  -- the defect in closed form
  have hδ : prolateRiccatiDefect c s y = B * v / (c * u) := by
    rw [prolateRiccatiDefect, hP, ← hB]
    field_simp
  -- the two pieces of the error control
  have hfirst : 2 * (c * prolateWKBProfile s y) * prolateRiccatiDefect c s y ^ 2
      = 2 * B ^ 2 * v / (c * u) := by
    rw [hP, hδ]
    field_simp
  have hKle : |prolateBandScaleDeriv c s y / prolateBandScale c s y|
      ≤ 2 * y / (y ^ 2 - s) + 2 * y / (1 - y ^ 2) := by
    have hK := abs_prolateBandScaleDeriv_div_le (c := c) (s := s) (y := y) hc hy0.le hsy hy2
    have hKpos : 0 < prolateBandScale c s y := prolateBandScale_pos hc hsy hy2
    have hval : |prolateBandScaleDeriv c s y / prolateBandScale c s y|
        = |prolateBandScaleDeriv c s y| / prolateBandScale c s y := by
      rw [abs_div, abs_of_pos hKpos]
    rw [hval]
    exact hK
  have hsecond : |prolateBandScaleDeriv c s y / prolateBandScale c s y|
      * (prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y)) / 2
      ≤ (2 * y / (y ^ 2 - s) + 2 * y / (1 - y ^ 2)) * (3 / 2) * (B * v / (c * u)) := by
    have hδ0 : 0 ≤ prolateRiccatiDefect c s y := by
      rw [hδ]
      positivity
    have hstep : prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y) / 2
        ≤ (3 / 2) * (B * v / (c * u)) := by
      rw [hδ] at hδ1 ⊢
      nlinarith [hδ1, hδ0, hδ]
    have hKnn : (0 : ℝ) ≤ |prolateBandScaleDeriv c s y / prolateBandScale c s y| := abs_nonneg _
    have hcoef : (0 : ℝ) ≤ (3 / 2) * (B * v / (c * u)) := by positivity
    calc |prolateBandScaleDeriv c s y / prolateBandScale c s y|
          * (prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y)) / 2
        = |prolateBandScaleDeriv c s y / prolateBandScale c s y|
          * (prolateRiccatiDefect c s y * (2 + prolateRiccatiDefect c s y) / 2) := by ring
      _ ≤ |prolateBandScaleDeriv c s y / prolateBandScale c s y| * ((3 / 2) * (B * v / (c * u))) :=
          mul_le_mul_of_nonneg_left hstep hKnn
      _ ≤ (2 * y / (y ^ 2 - s) + 2 * y / (1 - y ^ 2)) * (3 / 2) * (B * v / (c * u)) := by
          have := mul_le_mul_of_nonneg_right hKle hcoef
          linarith [this]
  -- the numerator estimate
  have hcu : (0 : ℝ) < c * u := by positivity
  have hBsq : 2 * B ^ 2 * v ≤ 2 / y ^ 2 + 4 * M / a + 2 * M ^ 2 := by
    have hsq : B ^ 2 ≤ (1 / y + M) ^ 2 := by nlinarith [hBle, hB0]
    have hexp : (1 / y + M) ^ 2 = 1 / y ^ 2 + 2 * M / y + M ^ 2 := by
      field_simp
      ring
    have hMy : 2 * M / y ≤ 2 * M / a := by
      rw [div_le_div_iff₀ hy0 ha]
      nlinarith [hM0, hay]
    nlinarith [hsq, hexp, hMy, hv1, hv0, hB0, sq_nonneg B]
  have hu2y : (2 : ℝ) * y / (y ^ 2 - s) = 2 * y / u ^ 2 := by rw [hu2]
  have hv2y : (2 : ℝ) * y / (1 - y ^ 2) = 2 * y / v ^ 2 := by rw [hv2]
  have hterm2 : (2 * y / (y ^ 2 - s)) * (3 / 2) * (B * v) ≤ 3 * (1 + M) / u ^ 2 := by
    rw [hu2y]
    have hyB : y * B ≤ 1 + M * y := by
      have : y * B ≤ y * (1 / y + M) := by nlinarith [hBle, hy0]
      have hval : y * (1 / y + M) = 1 + M * y := by field_simp; ring
      linarith [this, hval.le, hval.ge]
    have hMy1 : M * y ≤ M := by nlinarith [hM0, hy1, hy0]
    have hstep : 2 * y / u ^ 2 * (3 / 2) * (B * v) ≤ 3 * (y * B) / u ^ 2 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hv1, hv0, hB0, hy0, sq_nonneg u]
    have hfinal : 3 * (y * B) / u ^ 2 ≤ 3 * (1 + M) / u ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hyB, hMy1]
    linarith [hstep, hfinal]
  have hterm3 : (2 * y / (1 - y ^ 2)) * (3 / 2) * (B * v) ≤ 3 * (1 / a + M) / (1 - α ^ 2) := by
    rw [hv2y]
    have hvsq : (1 : ℝ) - α ^ 2 ≤ v ^ 2 := by
      rw [hv2]
      nlinarith [hyα, hy0, hα1]
    have hstep : 2 * y / v ^ 2 * (3 / 2) * (B * v) ≤ 3 * B / v ^ 2 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hv1, hv0, hB0, hy0, hy1, sq_nonneg v]
    have hBa : B ≤ 1 / a + M := by
      have h1a : 1 / y ≤ 1 / a := by
        rw [div_le_div_iff₀ hy0 ha]
        linarith
      linarith [hBle, h1a]
    have hfinal : 3 * B / v ^ 2 ≤ 3 * (1 / a + M) / (1 - α ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [hBa, hvsq, hB0, hM0, ha]
    linarith [hstep, hfinal]
  -- assemble
  have hsum : prolateBandErrorControl c s y
      ≤ (2 / y ^ 2 + 4 * M / a + 2 * M ^ 2 + 3 * (1 + M) / u ^ 2
          + 3 * (1 / a + M) / (1 - α ^ 2)) / (c * u) := by
    rw [prolateBandErrorControl, hfirst]
    have hdiv : 2 * B ^ 2 * v / (c * u)
        + (2 * y / (y ^ 2 - s) + 2 * y / (1 - y ^ 2)) * (3 / 2) * (B * v / (c * u))
        = (2 * B ^ 2 * v + ((2 * y / (y ^ 2 - s)) * (3 / 2) * (B * v)
            + (2 * y / (1 - y ^ 2)) * (3 / 2) * (B * v))) / (c * u) := by
      field_simp
      ring
    have hle1 : prolateBandErrorControl c s y ≤ 2 * B ^ 2 * v / (c * u)
        + (2 * y / (y ^ 2 - s) + 2 * y / (1 - y ^ 2)) * (3 / 2) * (B * v / (c * u)) := by
      rw [prolateBandErrorControl, hfirst]
      linarith [hsecond]
    refine le_trans hle1 ?_
    rw [hdiv, div_le_div_iff₀ hcu hcu]
    nlinarith [hBsq, hterm2, hterm3, hcu]
  refine le_trans hsum (le_of_eq ?_)
  field_simp
  ring

end GaloisForLFunctions.RHTower

end
