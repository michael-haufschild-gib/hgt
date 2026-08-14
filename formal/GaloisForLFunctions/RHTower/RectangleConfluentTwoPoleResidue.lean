import GaloisForLFunctions.RHTower.RectangleTwoPoleResidue

/-!
# Rectangle residue theorem with a confluent double pole

A squared Cauchy kernel has a global primitive off its pole, hence its four rectangle-edge
integrals telescope to zero even when the pole is inside.  Consequently a decomposition with one
simple pole and one double-pole packet contributes only the two residue coefficients; coefficient
of the squared inverse never contributes.  Both entire-remainder and local analytic-remainder
forms are provided.
-/

open Complex intervalIntegral Set

noncomputable section

namespace RHTower

/-- Primitive of squared Cauchy kernel away from its pole. -/
def doublePolePrimitive (a : ℂ) : ℂ → ℂ := -(fun z => z - a)⁻¹

/-- Derivative of primitive is squared Cauchy kernel away from pole. -/
lemma hasDerivAt_doublePolePrimitive {a z : ℂ} (hza : z ≠ a) :
    HasDerivAt (doublePolePrimitive a) ((z - a)⁻¹ ^ 2) z := by
  unfold doublePolePrimitive
  have h := (((hasDerivAt_id z).sub_const a).inv (sub_ne_zero.mpr hza)).neg
  have hcoef : -(-1 / (z - a) ^ 2) = (z - a)⁻¹ ^ 2 := by
    field_simp [sub_ne_zero.mpr hza]
  simp only [id_eq] at h
  rw [hcoef] at h
  exact h

/-- Horizontal edge integral of squared Cauchy kernel is primitive difference. -/
lemma integral_horizontal_doublePole {a : ℂ} {h l r : ℝ}
    (hne : ∀ x ∈ uIcc l r, (x : ℂ) + h * I ≠ a) :
    (∫ x in l..r, (((x : ℂ) + h * I) - a)⁻¹ ^ 2) =
      doublePolePrimitive a ((r : ℂ) + h * I) -
        doublePolePrimitive a ((l : ℂ) + h * I) := by
  have hHD : ∀ x ∈ uIcc l r,
      HasDerivAt (fun x : ℝ => doublePolePrimitive a ((x : ℂ) + h * I))
        ((((x : ℂ) + h * I) - a)⁻¹ ^ 2) x := by
    intro x hx
    have hin : HasDerivAt (fun x : ℝ => (x : ℂ) + (h : ℂ) * I) 1 x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((h : ℂ) * I))
    have hout := hasDerivAt_doublePolePrimitive (hne x hx)
    have hcomp := hout.scomp x hin
    change HasDerivAt (fun y : ℝ => doublePolePrimitive a ((y : ℂ) + h * I)) _ x at hcomp
    simpa only [one_smul] using hcomp
  have hcont : ContinuousOn (fun x : ℝ => ((((x : ℂ) + h * I) - a)⁻¹ ^ 2))
      (uIcc l r) := by
    exact (((Complex.continuous_ofReal.comp continuous_id).add continuous_const).sub
      continuous_const).continuousOn.inv₀
        (fun x hx => sub_ne_zero.mpr (hne x hx)) |>.pow 2
  rw [integral_eq_sub_of_hasDerivAt hHD hcont.intervalIntegrable]

/-- Oriented vertical edge integral of squared Cauchy kernel is primitive difference. -/
lemma integral_vertical_doublePole {a : ℂ} {v l r : ℝ}
    (hne : ∀ y ∈ uIcc l r, (v : ℂ) + y * I ≠ a) :
    I • (∫ y in l..r, (((v : ℂ) + y * I) - a)⁻¹ ^ 2) =
      doublePolePrimitive a ((v : ℂ) + r * I) -
        doublePolePrimitive a ((v : ℂ) + l * I) := by
  have hHD : ∀ y ∈ uIcc l r,
      HasDerivAt (fun y : ℝ => doublePolePrimitive a ((v : ℂ) + y * I))
        (I * ((((v : ℂ) + y * I) - a)⁻¹ ^ 2)) y := by
    intro y hy
    have hin : HasDerivAt (fun y : ℝ => (v : ℂ) + (y : ℂ) * I) I y := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (v : ℂ)
    have hout := hasDerivAt_doublePolePrimitive (hne y hy)
    have hcomp := hout.scomp y hin
    change HasDerivAt (fun w : ℝ => doublePolePrimitive a ((v : ℂ) + w * I)) _ y at hcomp
    simpa only [smul_eq_mul] using hcomp
  have hcont : ContinuousOn
      (fun y : ℝ => I * ((((v : ℂ) + y * I) - a)⁻¹ ^ 2)) (uIcc l r) := by
    apply continuousOn_const.mul
    exact (((continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).sub
        continuous_const).continuousOn.inv₀
          (fun y hy => sub_ne_zero.mpr (hne y hy)) |>.pow 2)
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  rw [integral_eq_sub_of_hasDerivAt hHD hcont.intervalIntegrable]

/-- Rectangle integral of an enclosed squared Cauchy kernel vanishes exactly. -/
theorem rectIntegral_doublePoleKernel {a z₁ z₂ : ℂ}
    (hre1 : z₁.re < a.re) (hre2 : a.re < z₂.re)
    (him1 : z₁.im < a.im) (him2 : a.im < z₂.im) :
    rectIntegral (fun z => (z - a)⁻¹ ^ 2) z₁ z₂ = 0 := by
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, (x : ℂ) + z₁.im * I ≠ a := by
    intro x hx heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
    linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, (x : ℂ) + z₂.im * I ≠ a := by
    intro x hx heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
    linarith
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, (z₂.re : ℂ) + y * I ≠ a := by
    intro y hy heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
    linarith
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, (z₁.re : ℂ) + y * I ≠ a := by
    intro y hy heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
    linarith
  unfold rectIntegral
  rw [integral_horizontal_doublePole hbot, integral_horizontal_doublePole htop,
    integral_vertical_doublePole hright, integral_vertical_doublePole hleft]
  ring

/-- Confluent two-pole rectangle theorem with an entire remainder. -/
theorem rectIntegral_eq_confluent_two_pole_residues
    {F R : ℂ → ℂ} {p q rp dq rq z₁ z₂ : ℂ}
    (hp1 : z₁.re < p.re) (hp2 : p.re < z₂.re)
    (hp3 : z₁.im < p.im) (hp4 : p.im < z₂.im)
    (hq1 : z₁.re < q.re) (hq2 : q.re < z₂.re)
    (hq3 : z₁.im < q.im) (hq4 : q.im < z₂.im)
    (hR : Differentiable ℂ R)
    (hdecomp : ∀ z, z ≠ p → z ≠ q →
      F z = dq * (z - q)⁻¹ ^ 2 +
        (rp * (z - p)⁻¹ + (rq * (z - q)⁻¹ + R z))) :
    rectIntegral F z₁ z₂ = 2 * Real.pi * I * (rp + rq) := by
  let S : Set ℂ := {z | z ≠ p ∧ z ≠ q}
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      ((x : ℂ) + z₁.im * I) ∈ S := by
    intro x hx
    constructor <;> intro heq <;>
      have him := congrArg Complex.im heq <;>
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
    · linarith
    · linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re,
      ((x : ℂ) + z₂.im * I) ∈ S := by
    intro x hx
    constructor <;> intro heq <;>
      have him := congrArg Complex.im heq <;>
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
    · linarith
    · linarith
  have hright : ∀ y ∈ uIcc z₁.im z₂.im,
      ((z₂.re : ℂ) + y * I) ∈ S := by
    intro y hy
    constructor <;> intro heq <;>
      have hre := congrArg Complex.re heq <;>
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
    · linarith
    · linarith
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      ((z₁.re : ℂ) + y * I) ∈ S := by
    intro y hy
    constructor <;> intro heq <;>
      have hre := congrArg Complex.re heq <;>
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
    · linarith
    · linarith
  have hdouble : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      ∀ (c pole : ℂ), (∀ t ∈ uIcc a b, pt t ≠ pole) →
        IntervalIntegrable (fun t => c * (pt t - pole)⁻¹ ^ 2)
          MeasureTheory.volume a b := by
    intro a b pt hpt c pole hne
    exact (continuousOn_const.mul
      (((hpt.continuousOn.sub continuousOn_const).inv₀
        (fun t ht => sub_ne_zero.mpr (hne t ht))).pow 2)).intervalIntegrable
  have hsimple : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      ∀ (c pole : ℂ), (∀ t ∈ uIcc a b, pt t ≠ pole) →
        IntervalIntegrable (fun t => c * (pt t - pole)⁻¹)
          MeasureTheory.volume a b := by
    intro a b pt hpt c pole hne
    exact (continuousOn_const.mul
      ((hpt.continuousOn.sub continuousOn_const).inv₀
        (fun t ht => sub_ne_zero.mpr (hne t ht)))).intervalIntegrable
  have hregular : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      IntervalIntegrable (fun t => R (pt t)) MeasureTheory.volume a b := by
    intro a b pt hpt
    exact (hR.continuous.comp hpt).intervalIntegrable a b
  have htwo : rectIntegral
      (fun z => rp * (z - p)⁻¹ + (rq * (z - q)⁻¹ + R z)) z₁ z₂ =
      2 * Real.pi * I * (rp + rq) := by
    exact rectIntegral_eq_two_pole_residues hp1 hp2 hp3 hp4 hq1 hq2 hq3 hq4 hR
      (by intro z hzp hzq; rfl)
  rw [rectIntegral_congr
    (fun z hz => hdecomp z hz.1 hz.2) hbot htop hright hleft,
    rectIntegral_add
      (hdouble _ (by fun_prop) dq q (fun x hx => (hbot x hx).2))
      ((hsimple _ (by fun_prop) rp p (fun x hx => (hbot x hx).1)).add
        ((hsimple _ (by fun_prop) rq q (fun x hx => (hbot x hx).2)).add
          (hregular _ (by fun_prop))))
      (hdouble _ (by fun_prop) dq q (fun x hx => (htop x hx).2))
      ((hsimple _ (by fun_prop) rp p (fun x hx => (htop x hx).1)).add
        ((hsimple _ (by fun_prop) rq q (fun x hx => (htop x hx).2)).add
          (hregular _ (by fun_prop))))
      (hdouble _ (by fun_prop) dq q (fun y hy => (hright y hy).2))
      ((hsimple _ (by fun_prop) rp p (fun y hy => (hright y hy).1)).add
        ((hsimple _ (by fun_prop) rq q (fun y hy => (hright y hy).2)).add
          (hregular _ (by fun_prop))))
      (hdouble _ (by fun_prop) dq q (fun y hy => (hleft y hy).2))
      ((hsimple _ (by fun_prop) rp p (fun y hy => (hleft y hy).1)).add
        ((hsimple _ (by fun_prop) rq q (fun y hy => (hleft y hy).2)).add
          (hregular _ (by fun_prop)))),
    rectIntegral_const_mul, rectIntegral_doublePoleKernel hq1 hq2 hq3 hq4,
    htwo]
  ring

/-- Confluent two-pole rectangle theorem with a remainder analytic only near the rectangle. -/
theorem rectIntegral_eq_confluent_two_pole_residues_of_analyticOnNhd
    {F R : ℂ → ℂ} {p q rp dq rq z₁ z₂ : ℂ} {U : Set ℂ}
    (hp1 : z₁.re < p.re) (hp2 : p.re < z₂.re)
    (hp3 : z₁.im < p.im) (hp4 : p.im < z₂.im)
    (hq1 : z₁.re < q.re) (hq2 : q.re < z₂.re)
    (hq3 : z₁.im < q.im) (hq4 : q.im < z₂.im)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hR : AnalyticOnNhd ℂ R U)
    (hdecomp : ∀ z, z ≠ p → z ≠ q →
      F z = dq * (z - q)⁻¹ ^ 2 +
        (rp * (z - p)⁻¹ + (rq * (z - q)⁻¹ + R z))) :
    rectIntegral F z₁ z₂ = 2 * Real.pi * I * (rp + rq) := by
  let S : Set ℂ := {z | z ≠ p ∧ z ≠ q}
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      ((x : ℂ) + z₁.im * I) ∈ S := by
    intro x hx
    constructor <;> intro heq <;>
      have him := congrArg Complex.im heq <;>
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
    · linarith
    · linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re,
      ((x : ℂ) + z₂.im * I) ∈ S := by
    intro x hx
    constructor <;> intro heq <;>
      have him := congrArg Complex.im heq <;>
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
    · linarith
    · linarith
  have hright : ∀ y ∈ uIcc z₁.im z₂.im,
      ((z₂.re : ℂ) + y * I) ∈ S := by
    intro y hy
    constructor <;> intro heq <;>
      have hre := congrArg Complex.re heq <;>
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
    · linarith
    · linarith
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      ((z₁.re : ℂ) + y * I) ∈ S := by
    intro y hy
    constructor <;> intro heq <;>
      have hre := congrArg Complex.re heq <;>
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
    · linarith
    · linarith
  have hdouble : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      ∀ (c pole : ℂ), (∀ t ∈ uIcc a b, pt t ≠ pole) →
        IntervalIntegrable (fun t => c * (pt t - pole)⁻¹ ^ 2)
          MeasureTheory.volume a b := by
    intro a b pt hpt c pole hne
    exact (continuousOn_const.mul
      (((hpt.continuousOn.sub continuousOn_const).inv₀
        (fun t ht => sub_ne_zero.mpr (hne t ht))).pow 2)).intervalIntegrable
  have hsimple : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      ∀ (c pole : ℂ), (∀ t ∈ uIcc a b, pt t ≠ pole) →
        IntervalIntegrable (fun t => c * (pt t - pole)⁻¹)
          MeasureTheory.volume a b := by
    intro a b pt hpt c pole hne
    exact (continuousOn_const.mul
      ((hpt.continuousOn.sub continuousOn_const).inv₀
        (fun t ht => sub_ne_zero.mpr (hne t ht)))).intervalIntegrable
  have hRbot : IntervalIntegrable
      (fun x : ℝ => R ((x : ℂ) + z₁.im * I)) MeasureTheory.volume z₁.re z₂.re := by
    apply ContinuousOn.intervalIntegrable
    change ContinuousOn (R ∘ fun x : ℝ => (x : ℂ) + z₁.im * I) (uIcc z₁.re z₂.re)
    exact hR.continuousOn.comp
      (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + z₁.im * I)
        (uIcc z₁.re z₂.re))
      (fun x hx => hsub ⟨by simpa using hx, by simp⟩)
  have hRtop : IntervalIntegrable
      (fun x : ℝ => R ((x : ℂ) + z₂.im * I)) MeasureTheory.volume z₁.re z₂.re := by
    apply ContinuousOn.intervalIntegrable
    change ContinuousOn (R ∘ fun x : ℝ => (x : ℂ) + z₂.im * I) (uIcc z₁.re z₂.re)
    exact hR.continuousOn.comp
      (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + z₂.im * I)
        (uIcc z₁.re z₂.re))
      (fun x hx => hsub ⟨by simpa using hx, by simp⟩)
  have hRright : IntervalIntegrable
      (fun y : ℝ => R ((z₂.re : ℂ) + y * I)) MeasureTheory.volume z₁.im z₂.im := by
    apply ContinuousOn.intervalIntegrable
    change ContinuousOn (R ∘ fun y : ℝ => (z₂.re : ℂ) + y * I) (uIcc z₁.im z₂.im)
    exact hR.continuousOn.comp
      (by fun_prop : ContinuousOn (fun y : ℝ => (z₂.re : ℂ) + y * I)
        (uIcc z₁.im z₂.im))
      (fun y hy => hsub ⟨by simp, by simpa using hy⟩)
  have hRleft : IntervalIntegrable
      (fun y : ℝ => R ((z₁.re : ℂ) + y * I)) MeasureTheory.volume z₁.im z₂.im := by
    apply ContinuousOn.intervalIntegrable
    change ContinuousOn (R ∘ fun y : ℝ => (z₁.re : ℂ) + y * I) (uIcc z₁.im z₂.im)
    exact hR.continuousOn.comp
      (by fun_prop : ContinuousOn (fun y : ℝ => (z₁.re : ℂ) + y * I)
        (uIcc z₁.im z₂.im))
      (fun y hy => hsub ⟨by simp, by simpa using hy⟩)
  rw [rectIntegral_congr
    (fun z hz => hdecomp z hz.1 hz.2) hbot htop hright hleft,
    rectIntegral_add
      (hdouble _ (by fun_prop) dq q (fun x hx => (hbot x hx).2))
      ((hsimple _ (by fun_prop) rp p (fun x hx => (hbot x hx).1)).add
        ((hsimple _ (by fun_prop) rq q (fun x hx => (hbot x hx).2)).add hRbot))
      (hdouble _ (by fun_prop) dq q (fun x hx => (htop x hx).2))
      ((hsimple _ (by fun_prop) rp p (fun x hx => (htop x hx).1)).add
        ((hsimple _ (by fun_prop) rq q (fun x hx => (htop x hx).2)).add hRtop))
      (hdouble _ (by fun_prop) dq q (fun y hy => (hright y hy).2))
      ((hsimple _ (by fun_prop) rp p (fun y hy => (hright y hy).1)).add
        ((hsimple _ (by fun_prop) rq q (fun y hy => (hright y hy).2)).add hRright))
      (hdouble _ (by fun_prop) dq q (fun y hy => (hleft y hy).2))
      ((hsimple _ (by fun_prop) rp p (fun y hy => (hleft y hy).1)).add
        ((hsimple _ (by fun_prop) rq q (fun y hy => (hleft y hy).2)).add hRleft)),
    rectIntegral_add
      (hsimple _ (by fun_prop) rp p (fun x hx => (hbot x hx).1))
      ((hsimple _ (by fun_prop) rq q (fun x hx => (hbot x hx).2)).add hRbot)
      (hsimple _ (by fun_prop) rp p (fun x hx => (htop x hx).1))
      ((hsimple _ (by fun_prop) rq q (fun x hx => (htop x hx).2)).add hRtop)
      (hsimple _ (by fun_prop) rp p (fun y hy => (hright y hy).1))
      ((hsimple _ (by fun_prop) rq q (fun y hy => (hright y hy).2)).add hRright)
      (hsimple _ (by fun_prop) rp p (fun y hy => (hleft y hy).1))
      ((hsimple _ (by fun_prop) rq q (fun y hy => (hleft y hy).2)).add hRleft),
    rectIntegral_add
      (hsimple _ (by fun_prop) rq q (fun x hx => (hbot x hx).2)) hRbot
      (hsimple _ (by fun_prop) rq q (fun x hx => (htop x hx).2)) hRtop
      (hsimple _ (by fun_prop) rq q (fun y hy => (hright y hy).2)) hRright
      (hsimple _ (by fun_prop) rq q (fun y hy => (hleft y hy).2)) hRleft,
    rectIntegral_const_mul, rectIntegral_doublePoleKernel hq1 hq2 hq3 hq4,
    rectIntegral_const_mul, rectIntegral_cauchyKernel hp1 hp2 hp3 hp4,
    rectIntegral_const_mul, rectIntegral_cauchyKernel hq1 hq2 hq3 hq4,
    rectIntegral_eq_zero_of_analyticOnNhd hsub hR]
  ring

end RHTower
