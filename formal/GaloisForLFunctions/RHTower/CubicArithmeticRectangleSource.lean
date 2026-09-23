import GaloisForLFunctions.RHTower.CubicCirculantWindingIntegral
import GaloisForLFunctions.RHTower.FormationAnchoredCubicContourCharge
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Literal arithmetic rectangle to faithful cubic index

Four smooth stationary ramps traverse the literal rectangle once with positive orientation.
Their exact change-of-variables law identifies the whole-line current of XiC along that path
with the already-proved continued prime--Gamma contour integral. The faithful circulant Hardy
construction then yields genuine orthogonal projections whose ordinary cubic trace is exactly
the enclosed Xi multiplicity-copy count, with fixed constants and nuclear source corrections.

No zero count or index enters the path or source definition. Source recovery is pointwise before
compression; no bounded inverse or linear prime-label transport after compression is claimed.
This is an unconditional arithmetic realization theorem on admissible contours, not a source
estimate forcing the charge of a contour isolating off-critical zeros to vanish.
-/

open Complex Set MeasureTheory ContinuousLinearMap
open scoped ContDiff BigOperators
noncomputable section
namespace RHTower

private theorem transition_deriv_zero {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · apply IsLocalMin.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun y => by
      rw [Real.smoothTransition.zero_of_nonpos hx]
      exact Real.smoothTransition.nonneg y)
  · apply IsLocalMax.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun y => by
      rw [Real.smoothTransition.one_of_one_le hx]
      exact Real.smoothTransition.le_one y)

/-- A smooth traversal of a real segment, stationary outside one unit interval. -/
def cubicContourRamp (a b k x : ℝ) : ℝ :=
  a + (b-a)*Real.smoothTransition (x-k)

theorem cubicContourRamp_smooth (a b k : ℝ) :
    ContDiff ℝ ∞ (cubicContourRamp a b k) := by
  exact contDiff_const.add (contDiff_const.mul
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)))

theorem cubicContourRamp_deriv (a b k x : ℝ) :
    deriv (cubicContourRamp a b k) x = (b-a)*deriv Real.smoothTransition (x-k) := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have h := (hs.differentiable (by simp) (x-k)).hasDerivAt
  have hd : HasDerivAt (cubicContourRamp a b k)
      ((b-a)*deriv Real.smoothTransition (x-k)) x := by
    convert ((h.comp x ((hasDerivAt_id x).sub_const k)).const_mul (b-a)).const_add a
      using 1 <;> try congr <;> simp only [mul_one]
  exact hd.deriv

theorem cubicContourRamp_left {a b k x : ℝ} (hx : x ≤ k) :
    cubicContourRamp a b k x = a := by
  simp [cubicContourRamp, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx)]

theorem cubicContourRamp_right {a b k x : ℝ} (hx : k+1 ≤ x) :
    cubicContourRamp a b k x = b := by
  rw [cubicContourRamp, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem cubicContourRamp_mem (a b k x : ℝ) : cubicContourRamp a b k x ∈ uIcc a b := by
  have h0 := Real.smoothTransition.nonneg (x-k)
  have h1 := Real.smoothTransition.le_one (x-k)
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    constructor <;> dsimp [cubicContourRamp] <;> nlinarith
  · rw [uIcc_of_ge h]
    constructor <;> dsimp [cubicContourRamp] <;> nlinarith

theorem cubicContourRamp_deriv_zero {a b k x : ℝ} (hx : x ≤ k ∨ k+1 ≤ x) :
    deriv (cubicContourRamp a b k) x = 0 := by
  have h : x-k ≤ 0 ∨ 1 ≤ x-k := by
    rcases hx with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rw [cubicContourRamp_deriv, transition_deriv_zero h, mul_zero]

theorem cubicContourRamp_deriv_compact (a b k : ℝ) :
    HasCompactSupport (deriv (cubicContourRamp a b k)) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (cubicContourRamp_deriv_zero (Or.inl (le_of_not_ge h)))
  · by_contra h
    exact hx (cubicContourRamp_deriv_zero (Or.inr (le_of_not_ge h)))

/-- Smooth change of variables retains the oriented edge integral exactly. -/
theorem cubicContourRamp_integral (a b k : ℝ) (g : ℝ → ℂ)
    (hg : ContinuousOn g (uIcc a b)) :
    Integrable (fun x => deriv (cubicContourRamp a b k) x • g (cubicContourRamp a b k x)) ∧
    (∫ x : ℝ, deriv (cubicContourRamp a b k) x • g (cubicContourRamp a b k x)) =
      ∫ y in a..b, g y := by
  have hf := cubicContourRamp_smooth a b k
  have hgc : Continuous (fun x => g (cubicContourRamp a b k x)) :=
    hg.comp_continuous hf.continuous (fun x => cubicContourRamp_mem a b k x)
  constructor
  · exact ((hf.continuous_deriv (by simp)).smul hgc).integrable_of_hasCompactSupport
      ((cubicContourRamp_deriv_compact a b k).smul_right)
  · have hs : Function.support (fun x =>
        deriv (cubicContourRamp a b k) x • g (cubicContourRamp a b k x)) ⊆ Ioc k (k+1) := by
      intro x hx
      constructor
      · by_contra h
        exact hx (by simp only [cubicContourRamp_deriv_zero (a:=a) (b:=b)
          (Or.inl (le_of_not_gt h)), zero_smul])
      · by_contra h
        exact hx (by simp only [cubicContourRamp_deriv_zero (a:=a) (b:=b)
          (Or.inr (le_of_not_ge h)), zero_smul])
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
    have h := intervalIntegral.integral_deriv_smul_comp'
      (fun x (_ : x ∈ uIcc k (k+1)) => (hf.differentiable (by simp) x).hasDerivAt)
      (hf.continuous_deriv (by simp)).continuousOn
      (hg.mono (by rintro _ ⟨x, _, rfl⟩; exact cubicContourRamp_mem a b k x))
    simpa only [Function.comp_apply, cubicContourRamp_left le_rfl,
      cubicContourRamp_right le_rfl] using h

/-- Positive rectangle traversal; no zero, multiplicity or index enters its definition. -/
def cubicSmoothRectangle (z₁ z₂ : ℂ) (x : ℝ) : ℂ :=
  ((cubicContourRamp z₁.re z₂.re 0 x + cubicContourRamp z₂.re z₁.re 2 x-z₂.re : ℝ) : ℂ) +
    ((cubicContourRamp z₁.im z₂.im 1 x + cubicContourRamp z₂.im z₁.im 3 x-z₂.im : ℝ) : ℂ)*I

theorem cubicSmoothRectangle_smooth (z₁ z₂ : ℂ) :
    ContDiff ℝ ∞ (cubicSmoothRectangle z₁ z₂) := by
  exact (Complex.ofRealCLM.contDiff.comp
    (((cubicContourRamp_smooth _ _ _).add (cubicContourRamp_smooth _ _ _)).sub
      contDiff_const)).add ((Complex.ofRealCLM.contDiff.comp
    (((cubicContourRamp_smooth _ _ _).add (cubicContourRamp_smooth _ _ _)).sub
      contDiff_const)).mul contDiff_const)

theorem cubicSmoothRectangle_bottom {z₁ z₂ : ℂ} {x : ℝ} (hx : x ∈ Icc 0 1) :
    cubicSmoothRectangle z₁ z₂ x = (cubicContourRamp z₁.re z₂.re 0 x : ℂ)+z₁.im*I := by
  rw [cubicSmoothRectangle, cubicContourRamp_left (a:=z₂.re) (b:=z₁.re) (k:=2) (by linarith [hx.2]),
    cubicContourRamp_left (a:=z₁.im) (b:=z₂.im) (k:=1) hx.2,
    cubicContourRamp_left (a:=z₂.im) (b:=z₁.im) (k:=3) (by linarith [hx.2])]
  simp

theorem cubicSmoothRectangle_rightEdge {z₁ z₂ : ℂ} {x : ℝ} (hx : x ∈ Icc 1 2) :
    cubicSmoothRectangle z₁ z₂ x = (z₂.re : ℂ)+(cubicContourRamp z₁.im z₂.im 1 x : ℂ)*I := by
  rw [cubicSmoothRectangle, cubicContourRamp_right (a:=z₁.re) (b:=z₂.re) (k:=0) (by linarith [hx.1]),
    cubicContourRamp_left (a:=z₂.re) (b:=z₁.re) (k:=2) hx.2,
    cubicContourRamp_left (a:=z₂.im) (b:=z₁.im) (k:=3) (by linarith [hx.2])]
  simp

theorem cubicSmoothRectangle_top {z₁ z₂ : ℂ} {x : ℝ} (hx : x ∈ Icc 2 3) :
    cubicSmoothRectangle z₁ z₂ x = (cubicContourRamp z₂.re z₁.re 2 x : ℂ)+z₂.im*I := by
  rw [cubicSmoothRectangle, cubicContourRamp_right (a:=z₁.re) (b:=z₂.re) (k:=0) (by linarith [hx.1]),
    cubicContourRamp_right (a:=z₁.im) (b:=z₂.im) (k:=1) (by linarith [hx.1]),
    cubicContourRamp_left (a:=z₂.im) (b:=z₁.im) (k:=3) hx.2]
  simp

theorem cubicSmoothRectangle_leftEdge {z₁ z₂ : ℂ} {x : ℝ} (hx : x ∈ Icc 3 4) :
    cubicSmoothRectangle z₁ z₂ x = (z₁.re : ℂ)+(cubicContourRamp z₂.im z₁.im 3 x : ℂ)*I := by
  rw [cubicSmoothRectangle, cubicContourRamp_right (a:=z₁.re) (b:=z₂.re) (k:=0) (by linarith [hx.1]),
    cubicContourRamp_right (a:=z₂.re) (b:=z₁.re) (k:=2) (by linarith [hx.1]),
    cubicContourRamp_right (a:=z₁.im) (b:=z₂.im) (k:=1) (by linarith [hx.1])]
  simp

theorem cubicSmoothRectangle_left {z₁ z₂ : ℂ} {x : ℝ} (hx : x ≤ 0) :
    cubicSmoothRectangle z₁ z₂ x = z₁ := by
  rw [cubicSmoothRectangle, cubicContourRamp_left (k:=0) hx,
    cubicContourRamp_left (k:=2) (by linarith),
    cubicContourRamp_left (k:=1) (by linarith), cubicContourRamp_left (k:=3) (by linarith)]
  simp

theorem cubicSmoothRectangle_right {z₁ z₂ : ℂ} {x : ℝ} (hx : 4 ≤ x) :
    cubicSmoothRectangle z₁ z₂ x = z₁ := by
  rw [cubicSmoothRectangle, cubicContourRamp_right (k:=0) (by linarith),
    cubicContourRamp_right (k:=2) (by linarith),
    cubicContourRamp_right (k:=1) (by linarith), cubicContourRamp_right (k:=3) (by linarith)]
  simp

theorem cubicSmoothRectangle_deriv (z₁ z₂ : ℂ) (x : ℝ) :
    deriv (cubicSmoothRectangle z₁ z₂) x =
      ((deriv (cubicContourRamp z₁.re z₂.re 0) x : ℝ):ℂ) +
      ((deriv (cubicContourRamp z₂.re z₁.re 2) x : ℝ):ℂ) +
      (((deriv (cubicContourRamp z₁.im z₂.im 1) x : ℝ):ℂ) +
      ((deriv (cubicContourRamp z₂.im z₁.im 3) x : ℝ):ℂ))*I := by
  have h (a b k : ℝ) := ((cubicContourRamp_smooth a b k).differentiable (by simp) x).hasDerivAt
  have hD := (((h z₁.re z₂.re 0).add (h z₂.re z₁.re 2)).sub_const z₂.re).ofReal_comp.add
    ((((h z₁.im z₂.im 1).add (h z₂.im z₁.im 3)).sub_const z₂.im).ofReal_comp.mul_const I)
  simpa only [ofReal_add] using! hD.deriv

theorem cubicSmoothRectangle_property (z₁ z₂ : ℂ) (P : ℂ → Prop)
    (hB : ∀ y ∈ uIcc z₁.re z₂.re, P ((y:ℂ)+z₁.im*I))
    (hT : ∀ y ∈ uIcc z₁.re z₂.re, P ((y:ℂ)+z₂.im*I))
    (hR : ∀ y ∈ uIcc z₁.im z₂.im, P ((z₂.re:ℂ)+y*I))
    (hL : ∀ y ∈ uIcc z₁.im z₂.im, P ((z₁.re:ℂ)+y*I))
    (x : ℝ) : P (cubicSmoothRectangle z₁ z₂ x) := by
  have hcorner : P z₁ := by simpa using hB z₁.re left_mem_uIcc
  rcases le_total x 0 with hx | hx
  · rw [cubicSmoothRectangle_left hx]; exact hcorner
  rcases le_total x 1 with h1 | h1
  · rw [cubicSmoothRectangle_bottom ⟨hx, h1⟩]
    exact hB _ (cubicContourRamp_mem _ _ _ _)
  rcases le_total x 2 with h2 | h2
  · rw [cubicSmoothRectangle_rightEdge ⟨h1, h2⟩]
    exact hR _ (cubicContourRamp_mem _ _ _ _)
  rcases le_total x 3 with h3 | h3
  · rw [cubicSmoothRectangle_top ⟨h2, h3⟩]
    exact hT _ (by rw [uIcc_comm]; exact cubicContourRamp_mem _ _ _ _)
  rcases le_total x 4 with h4 | h4
  · rw [cubicSmoothRectangle_leftEdge ⟨h3, h4⟩]
    exact hL _ (by rw [uIcc_comm]; exact cubicContourRamp_mem _ _ _ _)
  · rw [cubicSmoothRectangle_right h4]; exact hcorner

private theorem ramp_current_congr (a b k : ℝ) (g₁ g₂ : ℝ → ℂ)
    (heq : ∀ x ∈ Icc k (k+1), g₁ x = g₂ x) (x : ℝ) :
    deriv (cubicContourRamp a b k) x • g₁ x =
      deriv (cubicContourRamp a b k) x • g₂ x := by
  by_cases hx : x ∈ Icc k (k+1)
  · rw [heq x hx]
  · have ho : x ≤ k ∨ k+1 ≤ x := by
      have hh : x < k ∨ k+1 < x := by
        simpa only [mem_Icc, not_and_or, not_le] using hx
      exact hh.imp le_of_lt le_of_lt
    rw [cubicContourRamp_deriv_zero ho, zero_smul, zero_smul]

/-- The smooth whole-line contour current is the literal positively oriented rectangle integral. -/
theorem cubicSmoothRectangle_integral (z₁ z₂ : ℂ) (g : ℂ → ℂ)
    (hB : ContinuousOn (fun y : ℝ => g ((y:ℂ)+z₁.im*I)) (uIcc z₁.re z₂.re))
    (hT : ContinuousOn (fun y : ℝ => g ((y:ℂ)+z₂.im*I)) (uIcc z₁.re z₂.re))
    (hR : ContinuousOn (fun y : ℝ => g ((z₂.re:ℂ)+y*I)) (uIcc z₁.im z₂.im))
    (hL : ContinuousOn (fun y : ℝ => g ((z₁.re:ℂ)+y*I)) (uIcc z₁.im z₂.im)) :
    (∫ x : ℝ, deriv (cubicSmoothRectangle z₁ z₂) x * g (cubicSmoothRectangle z₁ z₂ x)) =
      rectIntegral g z₁ z₂ := by
  let B := cubicContourRamp z₁.re z₂.re 0
  let T := cubicContourRamp z₂.re z₁.re 2
  let R := cubicContourRamp z₁.im z₂.im 1
  let L := cubicContourRamp z₂.im z₁.im 3
  let b : ℝ → ℂ := fun x => deriv B x • g ((B x:ℂ)+z₁.im*I)
  let t : ℝ → ℂ := fun x => deriv T x • g ((T x:ℂ)+z₂.im*I)
  let r : ℝ → ℂ := fun x => deriv R x • g ((z₂.re:ℂ)+R x*I)
  let l : ℝ → ℂ := fun x => deriv L x • g ((z₁.re:ℂ)+L x*I)
  obtain ⟨hb,hbi⟩ := cubicContourRamp_integral z₁.re z₂.re 0 _ hB
  obtain ⟨ht,hti⟩ := cubicContourRamp_integral z₂.re z₁.re 2 _ (by
    simpa only [uIcc_comm] using hT)
  obtain ⟨hr,hri⟩ := cubicContourRamp_integral z₁.im z₂.im 1 _ hR
  obtain ⟨hl,hli⟩ := cubicContourRamp_integral z₂.im z₁.im 3 _ (by
    simpa only [uIcc_comm] using hL)
  change Integrable b at hb
  change Integrable t at ht
  change Integrable r at hr
  change Integrable l at hl
  have heq (x : ℝ) : deriv (cubicSmoothRectangle z₁ z₂) x * g (cubicSmoothRectangle z₁ z₂ x) =
      b x+t x+(I*r x+I*l x) := by
    have h₀ := ramp_current_congr z₁.re z₂.re 0 (fun s => g (cubicSmoothRectangle z₁ z₂ s))
      (fun s => g ((B s:ℂ)+z₁.im*I)) (by
        intro s hs; rw [cubicSmoothRectangle_bottom (by simpa using hs)]) x
    have h₂ := ramp_current_congr z₂.re z₁.re 2 (fun s => g (cubicSmoothRectangle z₁ z₂ s))
      (fun s => g ((T s:ℂ)+z₂.im*I)) (by
        intro s hs; rw [cubicSmoothRectangle_top (by norm_num at hs ⊢; exact hs)]) x
    have h₁ := ramp_current_congr z₁.im z₂.im 1 (fun s => g (cubicSmoothRectangle z₁ z₂ s))
      (fun s => g ((z₂.re:ℂ)+R s*I)) (by
        intro s hs; rw [cubicSmoothRectangle_rightEdge (by norm_num at hs ⊢; exact hs)]) x
    have h₃ := ramp_current_congr z₂.im z₁.im 3 (fun s => g (cubicSmoothRectangle z₁ z₂ s))
      (fun s => g ((z₁.re:ℂ)+L s*I)) (by
        intro s hs; rw [cubicSmoothRectangle_leftEdge (by norm_num at hs ⊢; exact hs)]) x
    change _ = b x at h₀
    change _ = t x at h₂
    change _ = r x at h₁
    change _ = l x at h₃
    rw [← h₀, ← h₂, ← h₁, ← h₃, cubicSmoothRectangle_deriv]
    simp only [Complex.real_smul]
    ring
  simp_rw [heq]
  have hadd := integral_add (hb.add ht) ((hr.const_mul I).add (hl.const_mul I))
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add hb ht, integral_add (hr.const_mul I) (hl.const_mul I),
    integral_const_mul, integral_const_mul]
  change (∫ x, b x) = _ at hbi
  change (∫ x, t x) = _ at hti
  change (∫ x, r x) = _ at hri
  change (∫ x, l x) = _ at hli
  rw [hbi, hti, hri, hli, intervalIntegral.integral_symm z₁.re z₂.re,
    intervalIntegral.integral_symm z₁.im z₂.im]
  simp only [rectIntegral, smul_eq_mul]
  ring

/-- Literal completed arithmetic source on the fixed smooth rectangle. -/
def cubicArithmeticRectangleSource (z₁ z₂ : ℂ) (x : ℝ) : ℂ :=
  XiC (cubicSmoothRectangle z₁ z₂ x)

theorem cubicArithmeticRectangleSource_smooth (z₁ z₂ : ℂ) :
    ContDiff ℝ ∞ (cubicArithmeticRectangleSource z₁ z₂) :=
  (XiC_differentiable.contDiff.restrict_scalars ℝ).comp (cubicSmoothRectangle_smooth z₁ z₂)

theorem cubicArithmeticRectangleSource_compact (z₁ z₂ : ℂ) :
    HasCompactSupport (fun x => cubicArithmeticRectangleSource z₁ z₂ x-XiC z₁) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(0:ℝ)) (b:=4))
  intro x hx
  constructor
  · by_contra h
    exact hx (by simp only [cubicArithmeticRectangleSource,
      cubicSmoothRectangle_left (le_of_not_ge h), sub_self])
  · by_contra h
    exact hx (by simp only [cubicArithmeticRectangleSource,
      cubicSmoothRectangle_right (le_of_not_ge h), sub_self])

theorem cubicArithmeticRectangleSource_ne_zero (z₁ z₂ : ℂ)
    (hB : ∀ y ∈ uIcc z₁.re z₂.re, XiExplicitAdmissible ((y:ℂ)+z₁.im*I))
    (hT : ∀ y ∈ uIcc z₁.re z₂.re, XiExplicitAdmissible ((y:ℂ)+z₂.im*I))
    (hR : ∀ y ∈ uIcc z₁.im z₂.im, XiExplicitAdmissible ((z₂.re:ℂ)+y*I))
    (hL : ∀ y ∈ uIcc z₁.im z₂.im, XiExplicitAdmissible ((z₁.re:ℂ)+y*I))
    (x : ℝ) : cubicArithmeticRectangleSource z₁ z₂ x ≠ 0 :=
  XiC_ne_zero_of_admissible (cubicSmoothRectangle_property z₁ z₂ _ hB hT hR hL x)

theorem cubicArithmeticRectangleSource_deriv (z₁ z₂ : ℂ) (x : ℝ) :
    deriv (cubicArithmeticRectangleSource z₁ z₂) x =
      deriv XiC (cubicSmoothRectangle z₁ z₂ x)*deriv (cubicSmoothRectangle z₁ z₂) x := by
  have h := (XiC_differentiable (cubicSmoothRectangle z₁ z₂ x)).hasDerivAt.complexToReal_fderiv
    |>.comp_hasDerivAt x (((cubicSmoothRectangle_smooth z₁ z₂).differentiable (by simp) x).hasDerivAt)
  simpa only [smul_apply, one_apply_eq_self,
    smul_eq_mul] using! h.deriv

private theorem xiLogDeriv_continuousAt {z : ℂ} (hz : XiC z ≠ 0) :
    ContinuousAt (logDeriv XiC) z :=
  XiC_differentiable.deriv.continuous.continuousAt.div
    XiC_differentiable.continuous.continuousAt hz

/-- Exact source transport: the whole-line logarithmic current is the continued arithmetic contour,
with the fixed prime--Gamma coefficients and no divisor selected in the source construction. -/
theorem cubicArithmeticRectangleSource_integral (z₁ z₂ : ℂ)
    (hB : ∀ y ∈ uIcc z₁.re z₂.re, XiExplicitAdmissible ((y:ℂ)+z₁.im*I))
    (hT : ∀ y ∈ uIcc z₁.re z₂.re, XiExplicitAdmissible ((y:ℂ)+z₂.im*I))
    (hR : ∀ y ∈ uIcc z₁.im z₂.im, XiExplicitAdmissible ((z₂.re:ℂ)+y*I))
    (hL : ∀ y ∈ uIcc z₁.im z₂.im, XiExplicitAdmissible ((z₁.re:ℂ)+y*I)) :
    (∫ x : ℝ, deriv (cubicArithmeticRectangleSource z₁ z₂) x /
      cubicArithmeticRectangleSource z₁ z₂ x) =
        rectIntegral continuedPrimeArchSourceRelativeTrace z₁ z₂ := by
  have hb : ContinuousOn (fun y : ℝ => logDeriv XiC ((y:ℂ)+z₁.im*I)) (uIcc z₁.re z₂.re) := by
    intro y hy
    exact ((xiLogDeriv_continuousAt (XiC_ne_zero_of_admissible (hB y hy))).comp
      (f := fun w : ℝ => (w:ℂ)+z₁.im*I)
      (by fun_prop : ContinuousAt (fun w : ℝ => (w:ℂ)+z₁.im*I) y)).continuousWithinAt
  have ht : ContinuousOn (fun y : ℝ => logDeriv XiC ((y:ℂ)+z₂.im*I)) (uIcc z₁.re z₂.re) := by
    intro y hy
    exact ((xiLogDeriv_continuousAt (XiC_ne_zero_of_admissible (hT y hy))).comp
      (f := fun w : ℝ => (w:ℂ)+z₂.im*I)
      (by fun_prop : ContinuousAt (fun w : ℝ => (w:ℂ)+z₂.im*I) y)).continuousWithinAt
  have hr : ContinuousOn (fun y : ℝ => logDeriv XiC ((z₂.re:ℂ)+y*I)) (uIcc z₁.im z₂.im) := by
    intro y hy
    exact ((xiLogDeriv_continuousAt (XiC_ne_zero_of_admissible (hR y hy))).comp
      (f := fun w : ℝ => (z₂.re:ℂ)+w*I)
      (by fun_prop : ContinuousAt (fun w : ℝ => (z₂.re:ℂ)+w*I) y)).continuousWithinAt
  have hl : ContinuousOn (fun y : ℝ => logDeriv XiC ((z₁.re:ℂ)+y*I)) (uIcc z₁.im z₂.im) := by
    intro y hy
    exact ((xiLogDeriv_continuousAt (XiC_ne_zero_of_admissible (hL y hy))).comp
      (f := fun w : ℝ => (z₁.re:ℂ)+w*I)
      (by fun_prop : ContinuousAt (fun w : ℝ => (z₁.re:ℂ)+w*I) y)).continuousWithinAt
  have heq (x : ℝ) : deriv (cubicArithmeticRectangleSource z₁ z₂) x /
      cubicArithmeticRectangleSource z₁ z₂ x =
      deriv (cubicSmoothRectangle z₁ z₂) x * logDeriv XiC (cubicSmoothRectangle z₁ z₂ x) := by
    rw [cubicArithmeticRectangleSource_deriv, cubicArithmeticRectangleSource, logDeriv_apply]
    ring
  simp_rw [heq]
  rw [cubicSmoothRectangle_integral z₁ z₂ _ hb ht hr hl]
  apply rectIntegral_congr (S := {z | XiExplicitAdmissible z}) _ hB hT hR hL
  intro z hz
  exact (logDeriv_XiC_eq_relativeResolventTrace (XiC_ne_zero_of_admissible hz)).trans
    (continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hz.re_pos hz.ne_one hz.zeta_ne).symm

/-- The source-loop normalization counts the literal Xi divisor copies, not distinct zeros. -/
theorem cubicArithmeticRectangleSource_winding (z₁ z₂ : ℂ)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hB : ∀ y ∈ uIcc z₁.re z₂.re, XiExplicitAdmissible ((y:ℂ)+z₁.im*I))
    (hT : ∀ y ∈ uIcc z₁.re z₂.re, XiExplicitAdmissible ((y:ℂ)+z₂.im*I))
    (hR : ∀ y ∈ uIcc z₁.im z₂.im, XiExplicitAdmissible ((z₂.re:ℂ)+y*I))
    (hL : ∀ y ∈ uIcc z₁.im z₂.im, XiExplicitAdmissible ((z₁.re:ℂ)+y*I)) :
    (2*(Real.pi:ℂ)*I)⁻¹ * (∫ x : ℝ, deriv (cubicArithmeticRectangleSource z₁ z₂) x /
      cubicArithmeticRectangleSource z₁ z₂ x) = ((xiZeroCopyClosedRectangle z₁ z₂).card : ℂ) := by
  rw [cubicArithmeticRectangleSource_integral z₁ z₂ hB hT hR hL]
  exact formationCompletedRectangleWinding_eq_xiMultiplicityCopies hre him hB hT hR hL

/-- Fixed arithmetic source to genuine Hardy cubic, with exact pointwise arithmetic source recovery,
trace-class source corrections, and multiplicity-normalized ordinary trace. The constants precede
the rectangle; neither the index nor the zeros are inputs to the source symbol. -/
theorem exists_faithful_arithmetic_rectangle_cubic :
    ∃ t b : ℝ, t^(2 : ℕ)+b^(2 : ℕ)=1 ∧ 6*(t*b)^(2 : ℕ)=1 ∧ t*b ≠ 0 ∧
    ∀ (z₁ z₂ : ℂ) (_ : z₁.re < z₂.re) (_ : z₁.im < z₂.im)
      (hB : ∀ y ∈ uIcc z₁.re z₂.re, XiExplicitAdmissible ((y:ℂ)+z₁.im*I))
      (hT : ∀ y ∈ uIcc z₁.re z₂.re, XiExplicitAdmissible ((y:ℂ)+z₂.im*I))
      (hR : ∀ y ∈ uIcc z₁.im z₂.im, XiExplicitAdmissible ((z₂.re:ℂ)+y*I))
      (hL : ∀ y ∈ uIcc z₁.im z₂.im, XiExplicitAdmissible ((z₁.re:ℂ)+y*I)),
    let A := cyclicFaithfulSourceSymbol t b (cubicArithmeticRectangleSource z₁ z₂) (XiC z₁)
      (cubicArithmeticRectangleSource_smooth z₁ z₂)
      (cubicArithmeticRectangleSource_ne_zero z₁ z₂ hB hT hR hL)
      (cubicArithmeticRectangleSource_compact z₁ z₂)
    (∀ x, cyclicFaithfulSourceRecover (t*b) (cubicFiniteSymbolValue (A 0+A 1+A 2) x) =
      XiC (cubicSmoothRectangle z₁ z₂ x)) ∧
    ∃ P Q R : CubicTwoChannel (CubicFiniteChannel (Fin 2 × Fin 3) SoninL2) →L[ℂ]
        CubicTwoChannel (CubicFiniteChannel (Fin 2 × Fin 3) SoninL2),
      IsSelfAdjoint P ∧ IsSelfAdjoint Q ∧ IsSelfAdjoint R ∧
      IsIdempotentElem P ∧ IsIdempotentElem Q ∧ IsIdempotentElem R ∧
      MemSchattenClass 1 (P-cubicDoubleOperator
        (cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier (A 0)*cubicFiniteHardyCutoff)) ∧
      MemSchattenClass 1 (Q-cubicDoubleOperator
        (cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier (A 2)*cubicFiniteHardyCutoff)) ∧
      MemSchattenClass 1 (R-cubicDoubleOperator
        (cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier (A 1)*cubicFiniteHardyCutoff)) ∧
      MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) ∧
      opTrace (formationAnchoredCubicAssociator R Q P) =
        ((xiZeroCopyClosedRectangle z₁ z₂).card : ℂ) := by
  obtain ⟨t,b,hnorm,hunit,hne,h⟩ := exists_faithful_circulant_winding_cubic
  refine ⟨t,b,hnorm,hunit,hne,?_⟩
  intro z₁ z₂ hre him hB hT hR hL
  have hw := h (cubicArithmeticRectangleSource z₁ z₂) (XiC z₁)
    (cubicArithmeticRectangleSource_smooth z₁ z₂)
    (cubicArithmeticRectangleSource_ne_zero z₁ z₂ hB hT hR hL)
    (cubicArithmeticRectangleSource_compact z₁ z₂)
  simp only [cubicArithmeticRectangleSource_winding z₁ z₂ hre him hB hT hR hL] at hw
  exact hw

end RHTower
