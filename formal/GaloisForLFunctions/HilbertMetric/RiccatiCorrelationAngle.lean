import GaloisForLFunctions.HilbertMetric.ThreePointCorrelationAngle
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Riccati transport to correlation-angle concavity

For a normalized correlation `exp (-q)`, monotonicity of its normalized second curvature is the
Riccati margin `2 q' q'' - q'''`.  An exact first-order transport identity turns nonnegativity of
that margin into concavity, hence subadditivity, of the spherical correlation angle.
-/

open Set

namespace HilbertMetric

noncomputable section

/-- Certificate controlling the second derivative of `arccos (exp (-q))`. -/
def riccatiCorrelationAngleCertificate
    (q q₁ q₂ : ℝ → ℝ) (t : ℝ) : ℝ :=
  q₁ t ^ (2 : ℕ) - q₂ t * (1 - Real.exp (-2 * q t))

/-- Correlation angle associated with a nonnegative logarithmic action. -/
def riccatiCorrelationAngle (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.arccos (Real.exp (-q t))

/-- First derivative of the correlation angle away from the normalized seam. -/
def riccatiCorrelationAngleSlope
    (q q₁ : ℝ → ℝ) (t : ℝ) : ℝ :=
  q₁ t * Real.exp (-q t) /
    Real.sqrt (1 - Real.exp (-2 * q t))

/-- Second derivative of the correlation angle in certificate coordinates. -/
def riccatiCorrelationAngleCurvature
    (q q₁ q₂ : ℝ → ℝ) (t : ℝ) : ℝ :=
  -Real.exp (-q t) * riccatiCorrelationAngleCertificate q q₁ q₂ t /
    ((1 - Real.exp (-2 * q t)) *
      Real.sqrt (1 - Real.exp (-2 * q t)))

/-- Exact transport identity from the Riccati margin to the angle-curvature certificate. -/
theorem hasDerivAt_riccatiCorrelationAngleCertificate
    {q q₁ q₂ q₃ : ℝ → ℝ} {t : ℝ}
    (hq : HasDerivAt q (q₁ t) t)
    (hq₁ : HasDerivAt q₁ (q₂ t) t)
    (hq₂ : HasDerivAt q₂ (q₃ t) t) :
    HasDerivAt
      (riccatiCorrelationAngleCertificate q q₁ q₂)
      ((2 * q₁ t * q₂ t - q₃ t) *
        (1 - Real.exp (-2 * q t))) t := by
  have hexp :
      HasDerivAt (fun s => Real.exp (-2 * q s))
        ((-2 * q₁ t) * Real.exp (-2 * q t)) t := by
    exact ((hq.const_mul (-2)).exp).congr_deriv (by ring)
  have hraw := (hq₁.pow 2).sub
    (hq₂.mul ((hasDerivAt_const t 1).sub hexp))
  have hfun :
      riccatiCorrelationAngleCertificate q q₁ q₂ =
        q₁ ^ (2 : ℕ) - q₂ * ((fun _ : ℝ => 1) -
          fun s => Real.exp (-2 * q s)) := by
    funext s
    rfl
  rw [hfun]
  apply hraw.congr_deriv
  norm_num
  ring

/-- A nonnegative Riccati margin transports the zero seam certificate into a nonnegative
certificate throughout the interval. -/
theorem riccatiCorrelationAngleCertificate_nonneg
    {q q₁ q₂ q₃ : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hq0 : q 0 = 0) (hq₁0 : q₁ 0 = 0)
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q (q₁ t) t)
    (hq₁ : ∀ t ∈ Icc 0 T, HasDerivAt q₁ (q₂ t) t)
    (hq₂ : ∀ t ∈ Icc 0 T, HasDerivAt q₂ (q₃ t) t)
    (hqnonneg : ∀ t ∈ Icc 0 T, 0 ≤ q t)
    (hmargin : ∀ t ∈ Icc 0 T, 0 ≤ 2 * q₁ t * q₂ t - q₃ t) :
    ∀ t ∈ Icc 0 T,
      0 ≤ riccatiCorrelationAngleCertificate q q₁ q₂ t := by
  let C := riccatiCorrelationAngleCertificate q q₁ q₂
  have hCderiv (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt C
        ((2 * q₁ t * q₂ t - q₃ t) *
          (1 - Real.exp (-2 * q t))) t := by
    exact hasDerivAt_riccatiCorrelationAngleCertificate
      (hq t ht) (hq₁ t ht) (hq₂ t ht)
  have hCmono : MonotoneOn C (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
    · intro t ht
      exact (hCderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hCderiv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Icc 0 T := interior_subset ht
      exact mul_nonneg (hmargin t ht')
        (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by
          nlinarith [hqnonneg t ht'])))
  intro t ht
  have hzero : C 0 = 0 := by
    simp [C, riccatiCorrelationAngleCertificate, hq0, hq₁0]
  rw [← hzero]
  exact hCmono ⟨le_rfl, hT⟩ ht ht.1

/-- First derivative of the correlation angle away from its normalized seam. -/
theorem hasDerivAt_riccatiCorrelationAngle
    {q q₁ : ℝ → ℝ} {t : ℝ}
    (hq : HasDerivAt q (q₁ t) t) (hqpos : 0 < q t) :
    HasDerivAt (riccatiCorrelationAngle q)
      (riccatiCorrelationAngleSlope q q₁ t) t := by
  have hrho :
      HasDerivAt (fun s => Real.exp (-q s))
        ((-q₁ t) * Real.exp (-q t)) t :=
    by
      rw [show (fun s => Real.exp (-q s)) =
          (fun s => Real.exp ((-q) s)) by
        funext s
        rw [Pi.neg_apply]]
      exact hq.neg.exp.congr_deriv (by rw [Pi.neg_apply]; ring)
  have hrhoPos : 0 < Real.exp (-q t) := Real.exp_pos _
  have hrhoLt : Real.exp (-q t) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hsq :
      Real.exp (-q t) ^ (2 : ℕ) = Real.exp (-2 * q t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hraw := (Real.hasDerivAt_arccos
    (by linarith : Real.exp (-q t) ≠ -1)
    hrhoLt.ne).comp t hrho
  rw [show riccatiCorrelationAngle q =
      Real.arccos ∘ fun s => Real.exp (-q s) by
    funext s
    rfl]
  apply hraw.congr_deriv
  unfold riccatiCorrelationAngleSlope
  rw [hsq]
  ring

/-- Second derivative of the correlation angle in exact certificate form. -/
theorem hasDerivAt_riccatiCorrelationAngleSlope
    {q q₁ q₂ : ℝ → ℝ} {t : ℝ}
    (hq : HasDerivAt q (q₁ t) t)
    (hq₁ : HasDerivAt q₁ (q₂ t) t)
    (hqpos : 0 < q t) :
    HasDerivAt (riccatiCorrelationAngleSlope q q₁)
      (riccatiCorrelationAngleCurvature q q₁ q₂ t) t := by
  let e := Real.exp (-q t)
  let e₂ := Real.exp (-2 * q t)
  let w := 1 - e₂
  let d := Real.sqrt w
  have he :
      HasDerivAt (fun s => Real.exp (-q s))
        ((-q₁ t) * e) t := by
    rw [show (fun s => Real.exp (-q s)) =
        (fun s => Real.exp ((-q) s)) by
      funext s
      rw [Pi.neg_apply]]
    exact hq.neg.exp.congr_deriv (by rw [Pi.neg_apply]; dsimp [e]; ring)
  have he₂ :
      HasDerivAt (fun s => Real.exp (-2 * q s))
        ((-2 * q₁ t) * e₂) t := by
    exact ((hq.const_mul (-2)).exp).congr_deriv (by dsimp [e₂]; ring)
  have hw :
      HasDerivAt (fun s => 1 - Real.exp (-2 * q s))
        (2 * q₁ t * e₂) t := by
    have hraw := (hasDerivAt_const t 1).sub he₂
    rw [show (fun s => 1 - Real.exp (-2 * q s)) =
        (fun _ : ℝ => 1) - (fun s => Real.exp (-2 * q s)) by
      funext s
      rfl]
    exact hraw.congr_deriv (by ring)
  have hwpos : 0 < w := by
    dsimp [w, e₂]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hdpos : 0 < d := Real.sqrt_pos.2 hwpos
  have hd :
      HasDerivAt
        (fun s => Real.sqrt (1 - Real.exp (-2 * q s)))
        (q₁ t * e₂ / d) t := by
    have hsqrt := hw.sqrt hwpos.ne'
    exact hsqrt.congr_deriv (by dsimp [d]; ring)
  have hn :
      HasDerivAt (fun s => q₁ s * Real.exp (-q s))
        ((q₂ t - q₁ t ^ (2 : ℕ)) * e) t := by
    have hraw := hq₁.mul he
    rw [show (fun s => q₁ s * Real.exp (-q s)) =
        q₁ * (fun s => Real.exp (-q s)) by
      funext s
      rfl]
    exact hraw.congr_deriv (by dsimp [e]; ring)
  have hraw := hn.div hd hdpos.ne'
  rw [show riccatiCorrelationAngleSlope q q₁ =
      (fun s => q₁ s * Real.exp (-q s)) /
        (fun s => Real.sqrt (1 - Real.exp (-2 * q s))) by
    funext s
    rfl]
  apply hraw.congr_deriv
  unfold riccatiCorrelationAngleCurvature
    riccatiCorrelationAngleCertificate
  change
    (((q₂ t - q₁ t ^ (2 : ℕ)) * e * d -
        q₁ t * e * (q₁ t * e₂ / d)) / d ^ (2 : ℕ)) =
      -e * (q₁ t ^ (2 : ℕ) - q₂ t * w) / (w * d)
  have hsq : d ^ (2 : ℕ) = w := by
    exact Real.sq_sqrt hwpos.le
  field_simp [hdpos.ne', hwpos.ne']
  rw [hsq]
  have he₂eq : e₂ = 1 - w := by linarith
  rw [he₂eq]
  ring

/-- Nonnegative Riccati margin makes the spherical correlation angle concave on the closed
normalized interval. -/
theorem concaveOn_riccatiCorrelationAngle_of_margin_nonneg
    {q q₁ q₂ q₃ : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hq0 : q 0 = 0) (hq₁0 : q₁ 0 = 0)
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q (q₁ t) t)
    (hq₁ : ∀ t ∈ Icc 0 T, HasDerivAt q₁ (q₂ t) t)
    (hq₂ : ∀ t ∈ Icc 0 T, HasDerivAt q₂ (q₃ t) t)
    (hqnonneg : ∀ t ∈ Icc 0 T, 0 ≤ q t)
    (hqpos : ∀ t ∈ interior (Icc 0 T), 0 < q t)
    (hmargin : ∀ t ∈ Icc 0 T, 0 ≤ 2 * q₁ t * q₂ t - q₃ t) :
    ConcaveOn ℝ (Icc 0 T) (riccatiCorrelationAngle q) := by
  have hcertificate :=
    riccatiCorrelationAngleCertificate_nonneg hT hq0 hq₁0
      hq hq₁ hq₂ hqnonneg hmargin
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 T)
  · intro t ht
    rw [show riccatiCorrelationAngle q =
        (fun s => Real.arccos (Real.exp (-q s))) by
      funext s
      rfl]
    exact (Real.continuous_arccos.continuousAt.comp
      ((hq t ht).neg.exp).continuousAt).continuousWithinAt
  · intro t ht
    exact (hasDerivAt_riccatiCorrelationAngle
      (hq t (interior_subset ht)) (hqpos t ht)).hasDerivWithinAt
  · intro t ht
    exact (hasDerivAt_riccatiCorrelationAngleSlope
      (hq t (interior_subset ht))
      (hq₁ t (interior_subset ht))
      (hqpos t ht)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Icc 0 T := interior_subset ht
    have hcert := hcertificate t ht'
    have hwpos :
        0 < 1 - Real.exp (-2 * q t) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by
        linarith [hqpos t ht]))
    unfold riccatiCorrelationAngleCurvature
    have hnum :
        -Real.exp (-q t) *
            riccatiCorrelationAngleCertificate q q₁ q₂ t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Real.exp_pos _).le) hcert
    exact div_nonpos_of_nonpos_of_nonneg
      hnum
      (mul_nonneg hwpos.le (Real.sqrt_nonneg _))

/-- A concave normalized angle is subadditive on every packet contained in its interval. -/
theorem correlationAngle_subadditive_of_concaveOn
    {α : ℝ → ℝ} {T x y : ℝ}
    (hα : ConcaveOn ℝ (Icc 0 T) α)
    (hα0 : α 0 = 0)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyT : x + y ≤ T) :
    α (x + y) ≤ α x + α y := by
  by_cases hs : x + y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0, hα0]
  · have hspos : 0 < x + y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs)
    have hsmem : x + y ∈ Icc 0 T := ⟨hspos.le, hxyT⟩
    have h0mem : (0 : ℝ) ∈ Icc 0 T :=
      ⟨le_rfl, hspos.le.trans hxyT⟩
    have hweights : x / (x + y) + y / (x + y) = 1 := by
      field_simp [hs]
    have hxconc := hα.2 hsmem h0mem
      (div_nonneg hx hspos.le) (div_nonneg hy hspos.le) hweights
    have hyconc := hα.2 hsmem h0mem
      (div_nonneg hy hspos.le) (div_nonneg hx hspos.le)
      (by linarith [hweights])
    have hxscale : x / (x + y) * (x + y) = x := by
      field_simp [hs]
    have hyscale : y / (x + y) * (x + y) = y := by
      field_simp [hs]
    simp only [smul_eq_mul, hα0, mul_zero, add_zero] at hxconc hyconc
    rw [hxscale] at hxconc
    rw [hyscale] at hyconc
    calc
      α (x + y) =
          (x / (x + y) + y / (x + y)) * α (x + y) := by
            rw [hweights, one_mul]
      _ = x / (x + y) * α (x + y) +
          y / (x + y) * α (x + y) := by ring
      _ ≤ α x + α y := add_le_add hxconc hyconc

/-- **Riccati-to-angle transport.**  A nonnegative normalized-curvature margin forces the
correlation-angle triangle inequality. -/
theorem riccatiCorrelationAngle_subadditive_of_margin_nonneg
    {q q₁ q₂ q₃ : ℝ → ℝ} {T x y : ℝ}
    (hT : 0 ≤ T)
    (hq0 : q 0 = 0) (hq₁0 : q₁ 0 = 0)
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q (q₁ t) t)
    (hq₁ : ∀ t ∈ Icc 0 T, HasDerivAt q₁ (q₂ t) t)
    (hq₂ : ∀ t ∈ Icc 0 T, HasDerivAt q₂ (q₃ t) t)
    (hqnonneg : ∀ t ∈ Icc 0 T, 0 ≤ q t)
    (hqpos : ∀ t ∈ interior (Icc 0 T), 0 < q t)
    (hmargin : ∀ t ∈ Icc 0 T, 0 ≤ 2 * q₁ t * q₂ t - q₃ t)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyT : x + y ≤ T) :
    riccatiCorrelationAngle q (x + y) ≤
      riccatiCorrelationAngle q x + riccatiCorrelationAngle q y := by
  apply correlationAngle_subadditive_of_concaveOn
    (concaveOn_riccatiCorrelationAngle_of_margin_nonneg
      hT hq0 hq₁0 hq hq₁ hq₂ hqnonneg hqpos hmargin)
  · simp [riccatiCorrelationAngle, hq0]
  · exact hx
  · exact hy
  · exact hxyT

/-- **Seam reconstruction.**  Difference-chamber Riccati control and the two center-zero
margins force the sum-chamber margin.  This scalar law is independent of any particular
correlation model. -/
theorem sumRiccatiMargin_nonneg_of_difference_and_center
    {hₐ hᵦ cₐ cᵦ dₐ dᵦ : ℝ}
    (hh : hᵦ ≤ hₐ) (hᵦ0 : 0 ≤ hᵦ)
    (hdifference :
      0 ≤ 2 * (hₐ - hᵦ) * (cₐ + cᵦ) - (dₐ - dᵦ))
    (hcenterₐ : 0 ≤ 4 * hₐ * cₐ - dₐ)
    (hcenterᵦ : 0 ≤ 4 * hᵦ * cᵦ - dᵦ) :
    0 ≤ 2 * (hₐ + hᵦ) * (cₐ + cᵦ) - (dₐ + dᵦ) := by
  by_cases hc : cₐ ≤ cᵦ
  · nlinarith [
      mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr hc)]
  · have hc' : cᵦ ≤ cₐ := (le_of_lt (lt_of_not_ge hc))
    nlinarith [
      mul_nonneg hᵦ0 (sub_nonneg.mpr hc')]

end

end HilbertMetric
