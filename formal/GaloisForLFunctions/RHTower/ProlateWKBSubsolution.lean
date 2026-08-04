import GaloisForLFunctions.RHTower.ProlateRiccati

/-!
# The WKB profile is a Riccati subsolution on the outer band

The WKB profile of the prolate equation is

```text
V(y) = sqrt ((chi + c² y²)/(1 - y²)),
```

the square root of the Riccati potential.  Because `V² = q` exactly, the Riccati defect of `V` collapses to
one term:

```text
V' - (V² + b V - q) = V' - b V,      b = 2y/(1-y²),
```

and a two-line computation turns `V' <= b V` into the *sign of the derivative of `(chi + c² y²)(1-y²)`*:
it holds precisely where `c²(1 - 2y²) <= chi`, i.e. on the outer part of the band.  There the WKB profile is
a Riccati **sub**solution, so the backward comparison applies: matching it above the logarithmic derivative
at the right endpoint propagates the bound *leftwards* across the whole outer band.

This is the sharp direction of the tunneling estimate — no error term, and the resulting decay integral
`∫ sqrt((chi + c² y²)/(1-y²))` is the exact WKB exponent whose value is `c(1 + o(1))`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set intervalIntegral MeasureTheory

open _root_.RHTower

/-- The WKB profile of the prolate equation: the square root of the Riccati potential. -/
def prolateWKB (c χ : ℝ) (y : ℝ) : ℝ := Real.sqrt ((χ + c ^ 2 * y ^ 2) / (1 - y ^ 2))

/-- The derivative of the Riccati potential. -/
theorem hasDerivAt_prolatePotential {c χ y : ℝ} (hw : (1 : ℝ) - y ^ 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => (χ + c ^ 2 * t ^ 2) / (1 - t ^ 2))
      ((2 * c ^ 2 * y * (1 - y ^ 2) + 2 * y * (χ + c ^ 2 * y ^ 2)) / (1 - y ^ 2) ^ 2) y := by
  have hnum : HasDerivAt (fun t : ℝ => χ + c ^ 2 * t ^ 2) (2 * c ^ 2 * y) y := by
    have h := (hasDerivAt_pow 2 y).const_mul (c ^ 2)
    have h2 := h.const_add χ
    refine h2.congr_deriv ?_
    norm_num
    ring
  have hden : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y := by
    have h := (hasDerivAt_pow 2 y).const_sub (1 : ℝ)
    refine h.congr_deriv ?_
    norm_num
  have hquot := hnum.div hden hw
  refine hquot.congr_deriv ?_
  field_simp
  ring

/-- The derivative of the WKB profile. -/
theorem hasDerivAt_prolateWKB {c χ y : ℝ} (hw : (1 : ℝ) - y ^ 2 ≠ 0)
    (hR : 0 < (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2)) :
    HasDerivAt (prolateWKB c χ)
      ((2 * c ^ 2 * y * (1 - y ^ 2) + 2 * y * (χ + c ^ 2 * y ^ 2)) / (1 - y ^ 2) ^ 2
        / (2 * prolateWKB c χ y)) y := by
  have hbase := hasDerivAt_prolatePotential (c := c) (χ := χ) hw
  have hsqrt := hbase.sqrt (ne_of_gt hR)
  exact hsqrt

/-- **The WKB profile is a Riccati subsolution on the outer band.** -/
theorem prolateWKB_subsolution {c χ y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) (hy0 : 0 ≤ y)
    (hQ : 0 < χ + c ^ 2 * y ^ 2) (houter : c ^ 2 * (1 - 2 * y ^ 2) ≤ χ) :
    (2 * c ^ 2 * y * (1 - y ^ 2) + 2 * y * (χ + c ^ 2 * y ^ 2)) / (1 - y ^ 2) ^ 2
        / (2 * prolateWKB c χ y)
      ≤ (prolateWKB c χ y) ^ 2 + (2 * y / (1 - y ^ 2)) * prolateWKB c χ y
        - (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2) := by
  have hp : 0 < 1 - y ^ 2 := by
    have h1 : -1 < y := hy.1
    have h2 : y < 1 := hy.2
    nlinarith
  have hR : 0 < (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2) := div_pos hQ hp
  have hVpos : 0 < prolateWKB c χ y := by
    rw [prolateWKB]
    exact Real.sqrt_pos.mpr hR
  have hVsq : (prolateWKB c χ y) ^ 2 = (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2) := by
    rw [prolateWKB]
    exact Real.sq_sqrt (le_of_lt hR)
  -- the Riccati defect collapses to a single term
  rw [hVsq]
  have hcollapse : (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2)
      + (2 * y / (1 - y ^ 2)) * prolateWKB c χ y - (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2)
      = (2 * y / (1 - y ^ 2)) * prolateWKB c χ y := by ring
  rw [hcollapse]
  -- the numerator inequality: `Q' p <= 2 y Q`
  have hnum : 2 * c ^ 2 * y * (1 - y ^ 2) + 2 * y * (χ + c ^ 2 * y ^ 2)
      ≤ 4 * y * (χ + c ^ 2 * y ^ 2) := by
    have hstep : 2 * c ^ 2 * y * (1 - y ^ 2) ≤ 2 * y * (χ + c ^ 2 * y ^ 2) := by
      have h := mul_le_mul_of_nonneg_left houter (by linarith : (0 : ℝ) ≤ 2 * y)
      nlinarith [h]
    linarith
  -- divide by the positive factors
  rw [div_div, div_le_iff₀ (by positivity : (0 : ℝ) < (1 - y ^ 2) ^ 2 * (2 * prolateWKB c χ y))]
  have hVsq' : prolateWKB c χ y * prolateWKB c χ y = (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2) := by
    rw [← sq]
    exact hVsq
  have hkey : 2 * y / (1 - y ^ 2) * prolateWKB c χ y
      * ((1 - y ^ 2) ^ 2 * (2 * prolateWKB c χ y))
      = 4 * y * (χ + c ^ 2 * y ^ 2) := by
    have hpne : (1 : ℝ) - y ^ 2 ≠ 0 := ne_of_gt hp
    field_simp
    rw [hVsq]
    field_simp
    ring
  rw [hkey]
  exact hnum

/-! ## The sharp outer-band decay bound -/

theorem continuousOn_prolateWKB {c χ a b : ℝ} (hpne : ∀ y ∈ Icc a b, (1 : ℝ) - y ^ 2 ≠ 0) :
    ContinuousOn (prolateWKB c χ) (Icc a b) := by
  have hnum : ContinuousOn (fun y : ℝ => χ + c ^ 2 * y ^ 2) (Icc a b) := by fun_prop
  have hden : ContinuousOn (fun y : ℝ => 1 - y ^ 2) (Icc a b) := by fun_prop
  exact Real.continuous_sqrt.comp_continuousOn (hnum.div hden hpne)

theorem continuousOn_prolateLogDeriv {a b : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (hne : ∀ y ∈ Icc a b, Φ y ≠ 0) :
    ContinuousOn (prolateLogDeriv Φ) (Icc a b) := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hd2 : Differentiable ℝ (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hsm).2)).1
  have hquot : ContinuousOn (fun y => deriv Φ y / Φ y) (Icc a b) :=
    (hd2.continuous.continuousOn).div (hd1.continuous.continuousOn) hne
  exact hquot.neg

/-- **The logarithmic derivative is bounded by the WKB profile on the outer band.**  The backward
comparison, started from the right endpoint, propagates the subsolution bound leftwards. -/
theorem prolateLogDeriv_le_prolateWKB {c χ a b : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    (hab : a ≤ b) (ha0 : (0 : ℝ) ≤ a) (ha : -1 < a) (hb : b < 1)
    (hpos : ∀ y ∈ Icc a b, 0 < Φ y)
    (hQ : ∀ y ∈ Icc a b, 0 < χ + c ^ 2 * y ^ 2)
    (houter : ∀ y ∈ Icc a b, c ^ 2 * (1 - 2 * y ^ 2) ≤ χ)
    (hinit : prolateLogDeriv Φ b ≤ prolateWKB c χ b) :
    ∀ y ∈ Icc a b, prolateLogDeriv Φ y ≤ prolateWKB c χ y := by
  have hpne : ∀ y ∈ Icc a b, (1 : ℝ) - y ^ 2 ≠ 0 := by
    intro y hy
    have h1 : -1 < y := lt_of_lt_of_le ha hy.1
    have h2 : y < 1 := lt_of_le_of_lt hy.2 hb
    nlinarith
  have hppos : ∀ y ∈ Icc a b, 0 < 1 - y ^ 2 := by
    intro y hy
    have h1 : -1 < y := lt_of_lt_of_le ha hy.1
    have h2 : y < 1 := lt_of_le_of_lt hy.2 hb
    nlinarith
  refine HTGeometry.riccati_le_of_le_of_subsolution (u := prolateLogDeriv Φ)
    (U := prolateWKB c χ)
    (u' := fun y => (prolateLogDeriv Φ y) ^ 2 + (2 * y / (1 - y ^ 2)) * prolateLogDeriv Φ y
      - (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2))
    (U' := fun y => (2 * c ^ 2 * y * (1 - y ^ 2) + 2 * y * (χ + c ^ 2 * y ^ 2)) / (1 - y ^ 2) ^ 2
      / (2 * prolateWKB c χ y))
    (bcoef := fun y => 2 * y / (1 - y ^ 2)) (q := fun y => (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2))
    hab (continuousOn_prolateLogDeriv hsm fun y hy => ne_of_gt (hpos y hy))
    (continuousOn_prolateWKB hpne) ?_ ?_ ?_ ?_ ?_ hinit
  · -- the Riccati equation of the solution
    intro y hy
    have hymem : y ∈ Icc a b := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hyband : y ∈ Ioo (-1 : ℝ) 1 :=
      ⟨lt_of_lt_of_le ha (le_of_lt hy.1), lt_trans hy.2 hb⟩
    exact hasDerivAt_prolateLogDeriv hsm heig hyband (ne_of_gt (hpos y hymem))
  · -- the derivative of the profile
    intro y hy
    have hymem : y ∈ Icc a b := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    exact hasDerivAt_prolateWKB (hpne y hymem) (div_pos (hQ y hymem) (hppos y hymem))
  · -- continuity of the first-order coefficient
    have hnum : ContinuousOn (fun y : ℝ => 2 * y) (Icc a b) := by fun_prop
    have hden : ContinuousOn (fun y : ℝ => 1 - y ^ 2) (Icc a b) := by fun_prop
    exact hnum.div hden hpne
  · -- the equation, by definition of the derivative field
    intro y _
    rfl
  · -- the subsolution inequality
    intro y hy
    have hymem : y ∈ Icc a b := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hyband : y ∈ Ioo (-1 : ℝ) 1 :=
      ⟨lt_of_lt_of_le ha (le_of_lt hy.1), lt_trans hy.2 hb⟩
    exact prolateWKB_subsolution hyband (le_trans ha0 hymem.1) (hQ y hymem) (houter y hymem)

/-- **The sharp WKB decay bound on the outer band.**  The solution decays at most like the exponential of
the exact WKB integral — no error term. -/
theorem le_endpoint_prolateWKB {c χ a b : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    (hab : a ≤ b) (ha0 : (0 : ℝ) ≤ a) (ha : -1 < a) (hb : b < 1)
    (hpos : ∀ y ∈ Icc a b, 0 < Φ y)
    (hQ : ∀ y ∈ Icc a b, 0 < χ + c ^ 2 * y ^ 2)
    (houter : ∀ y ∈ Icc a b, c ^ 2 * (1 - 2 * y ^ 2) ≤ χ)
    (hinit : prolateLogDeriv Φ b ≤ prolateWKB c χ b) :
    Φ a * Real.exp (-∫ t in a..b, prolateWKB c χ t) ≤ Φ b := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hpne : ∀ y ∈ Icc a b, (1 : ℝ) - y ^ 2 ≠ 0 := by
    intro y hy
    have h1 : -1 < y := lt_of_lt_of_le ha hy.1
    have h2 : y < 1 := lt_of_le_of_lt hy.2 hb
    nlinarith
  refine le_endpoint_of_logDeriv_le hab hd1 (continuousOn_prolateWKB hpne) hpos fun y hy => ?_
  exact prolateLogDeriv_le_prolateWKB hsm heig hab ha0 ha hb hpos hQ houter hinit y
    ⟨le_of_lt hy.1, le_of_lt hy.2⟩

end GaloisForLFunctions.RHTower

end
