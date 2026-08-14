import GaloisForLFunctions.HTGeometry.SchwartzCompactSupport
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Compactly supported primitives and the du Bois-Reymond lemma

A smooth function supported in `[a,b]` with vanishing integral has a smooth primitive supported in
the same interval.  Consequently a distribution whose derivative vanishes on an interval is a
constant multiple of Lebesgue measure there: the value on a test function depends only on its
integral.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- The primitive of a smooth function is smooth. -/
theorem contDiff_primitive {φ : ℝ → Y} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ∫ t in a..x, φ t) := by
  have hcont : Continuous φ := hφ.continuous
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∫ t in a..y, φ t) (φ x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable a x)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hderivEq : deriv (fun y : ℝ => ∫ t in a..y, φ t) = φ := by
    funext x
    exact (hderiv x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (hderiv x).differentiableAt, ?_⟩
  rw [hderivEq]
  exact hφ

omit [CompleteSpace Y] in
/-- A smooth function supported in `(a,b)` with vanishing integral has a primitive supported in
`(a,b)`. -/
theorem primitive_eq_zero_outside {φ : ℝ → Y} {a b : ℝ} (hcont : Continuous φ)
    (hsupp : ∀ x, x ∉ Ioo a b → φ x = 0) (hzero : (∫ t in a..b, φ t) = 0) :
    ∀ x, x ∉ Ioo a b → (∫ t in a..x, φ t) = 0 := by
  intro x hx
  rcases le_or_gt x a with hxa | hxa
  · have hcongr : (∫ t in a..x, φ t) = ∫ _t in a..x, (0 : Y) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_ge hxa] at ht
      refine hsupp t ?_
      intro hmem
      have h1 : a < t := hmem.1
      have h2 : t ≤ a := ht.2
      linarith
    rw [hcongr]
    simp
  · have hxb : b ≤ x := by
      by_contra hcon
      exact hx ⟨hxa, not_le.mp hcon⟩
    have hsplit : (∫ t in a..x, φ t) = (∫ t in a..b, φ t) + ∫ t in b..x, φ t :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable a b) (hcont.intervalIntegrable b x)).symm
    have hbx : (∫ t in b..x, φ t) = 0 := by
      have hcongr : (∫ t in b..x, φ t) = ∫ t in b..x, (0 : Y) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hxb] at ht
        refine hsupp t ?_
        intro hmem
        have h1 : t < b := hmem.2
        have h2 : b ≤ t := ht.1
        linarith
      rw [hcongr]
      simp
    rw [hsplit, hzero, hbx, add_zero]

/-- **The du Bois-Reymond lemma.**  A distribution whose derivative annihilates every test function
supported in an interval is, on that interval, a constant multiple of Lebesgue measure. -/
theorem apply_eq_integral_smul_of_deriv_zero {u : SchwartzMap ℝ ℂ →L[ℂ] X} {a b : ℝ}
    (hzero : ∀ ψ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (ψ : ℝ → ℂ) x = 0) →
      u (SchwartzMap.derivCLM ℂ ℂ ψ) = 0)
    {χ : SchwartzMap ℝ ℂ} (hχsupp : ∀ x, x ∉ Ioo a b → (χ : ℝ → ℂ) x = 0)
    (hχint : (∫ t in a..b, (χ : ℝ → ℂ) t) = 1) :
    ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      u φ = (∫ t in a..b, (φ : ℝ → ℂ) t) • u χ := by
  intro φ hφsupp
  set I : ℂ := ∫ t in a..b, (φ : ℝ → ℂ) t with hI
  set g : SchwartzMap ℝ ℂ := φ - I • χ with hg
  have hgcoe : (g : ℝ → ℂ) = fun x => (φ : ℝ → ℂ) x - I * (χ : ℝ → ℂ) x := by
    rw [hg]
    push_cast
    rfl
  have hgsupp : ∀ x, x ∉ Ioo a b → (g : ℝ → ℂ) x = 0 := by
    intro x hx
    rw [hgcoe]
    simp only
    rw [hφsupp x hx, hχsupp x hx, mul_zero, sub_zero]
  have hgcont : Continuous (g : ℝ → ℂ) := g.smooth'.continuous
  have hgint : (∫ t in a..b, (g : ℝ → ℂ) t) = 0 := by
    have hsub : (∫ t in a..b, (g : ℝ → ℂ) t)
        = (∫ t in a..b, (φ : ℝ → ℂ) t) - I * ∫ t in a..b, (χ : ℝ → ℂ) t := by
      rw [hgcoe]
      show (∫ t in a..b, ((φ : ℝ → ℂ) t - I * (χ : ℝ → ℂ) t))
        = (∫ t in a..b, (φ : ℝ → ℂ) t) - I * ∫ t in a..b, (χ : ℝ → ℂ) t
      rw [intervalIntegral.integral_sub (f := fun t : ℝ => (φ : ℝ → ℂ) t)
        (g := fun t : ℝ => I * (χ : ℝ → ℂ) t)
        (φ.smooth'.continuous.intervalIntegrable a b)
        ((χ.smooth'.continuous.intervalIntegrable a b).const_mul I),
        intervalIntegral.integral_const_mul]
    rw [hsub, hχint, mul_one, ← hI, sub_self]
  -- the primitive of `g`
  have hprimsupp : ∀ x, x ∉ Ioo a b → (∫ t in a..x, (g : ℝ → ℂ) t) = 0 :=
    primitive_eq_zero_outside hgcont hgsupp hgint
  have hprimcd : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ∫ t in a..x, (g : ℝ → ℂ) t) :=
    contDiff_primitive g.smooth' a
  have hprimcs : HasCompactSupport (fun x : ℝ => ∫ t in a..x, (g : ℝ → ℂ) t) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := a) (b := b)) fun x hx => ?_
    refine hprimsupp x ?_
    intro hmem
    exact hx ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
  set ψ : SchwartzMap ℝ ℂ := schwartzOfCompactSupport hprimcd hprimcs with hψ
  have hψsupp : ∀ x, x ∉ Ioo a b → (ψ : ℝ → ℂ) x = 0 := hprimsupp
  have hderiv : SchwartzMap.derivCLM ℂ ℂ ψ = g := by
    refine SchwartzMap.ext fun x => ?_
    have hd : HasDerivAt (fun y : ℝ => ∫ t in a..y, (g : ℝ → ℂ) t) ((g : ℝ → ℂ) x) x :=
      intervalIntegral.integral_hasDerivAt_right (hgcont.intervalIntegrable a x)
        (hgcont.stronglyMeasurableAtFilter _ _) hgcont.continuousAt
    show deriv (ψ : ℝ → ℂ) x = (g : ℝ → ℂ) x
    exact hd.deriv
  have hug : u g = 0 := by
    have := hzero ψ hψsupp
    rwa [hderiv] at this
  have hlin : u g = u φ - I • u χ := by
    rw [hg, map_sub, map_smul]
  rw [hlin] at hug
  have := sub_eq_zero.mp hug
  rw [this, hI]

end

end GaloisForLFunctions.HTGeometry
