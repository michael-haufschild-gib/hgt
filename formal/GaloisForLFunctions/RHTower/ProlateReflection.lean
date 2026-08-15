import GaloisForLFunctions.RHTower.ProlateBandHilbertSum

/-!
# Reflection intertwines the band transform and the prolate action

Both the Slepian band transform and the prolate Sturm--Liouville action commute with the reflection
`x ↦ -x`: the sinc kernel depends only on the difference of its arguments and is even, and the
prolate coefficients are even.  Consequently the even and odd parts of a joint band/prolate
eigenfunction are again joint eigenfunctions with the same pair of eigenvalues, and an even and an
odd profile are orthogonal on the aperture.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- The band transform intertwines reflection. -/
theorem bandTransform_comp_neg (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    bandTransform c (fun y => f (-y)) x = bandTransform c f (-x) := by
  have hneg := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun y : ℝ => sincKernelSmooth c (-x) y * f y)
  rw [neg_neg] at hneg
  rw [bandTransform, bandTransform, ← hneg]
  refine intervalIntegral.integral_congr fun y _ => ?_
  show sincKernelSmooth c x y * f (-y) = sincKernelSmooth c (-x) (-y) * f (-y)
  congr 1
  unfold sincKernelSmooth
  rw [show -x - -y = -(x - y) by ring, sincSmooth_even]

/-- The prolate action intertwines reflection. -/
theorem prolateSLAction_comp_neg (c : ℝ) {f : ℝ → ℝ} (_hf : Differentiable ℝ f)
    (_hf' : Differentiable ℝ (deriv f)) (x : ℝ) :
    prolateSLAction c (fun y => f (-y)) x = prolateSLAction c f (-x) := by
  have hd1 : deriv (fun y : ℝ => f (-y)) = fun y : ℝ => -deriv f (-y) := by
    funext y
    exact deriv_comp_neg f y
  have hd2 : deriv (fun y : ℝ => -deriv f (-y)) = fun y : ℝ => deriv (deriv f) (-y) := by
    funext y
    have hstep : deriv (fun z : ℝ => -deriv f (-z)) y = -deriv (fun z : ℝ => deriv f (-z)) y := by
      simp
    rw [hstep, deriv_comp_neg (deriv f) y]
    ring
  rw [prolateSLAction, prolateSLAction, hd1, hd2]
  show (1 - x ^ 2) * deriv (deriv f) (-x) - 2 * x * (-deriv f (-x)) - c ^ 2 * x ^ 2 * f (-x)
    = (1 - (-x) ^ 2) * deriv (deriv f) (-x) - 2 * -x * deriv f (-x) - c ^ 2 * (-x) ^ 2 * f (-x)
  ring

/-- Reflection preserves the global band eigenrelation. -/
theorem bandTransform_eigen_comp_neg {c lam : ℝ} {f : ℝ → ℝ}
    (h : ∀ x : ℝ, bandTransform c f x = lam * f x) (x : ℝ) :
    bandTransform c (fun y => f (-y)) x = lam * f (-x) := by
  rw [bandTransform_comp_neg, h]

/-- Reflection preserves the prolate eigenrelation. -/
theorem prolateSLAction_eigen_comp_neg {c eta : ℝ} {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (h : ∀ x : ℝ, prolateSLAction c f x = eta * f x) (x : ℝ) :
    prolateSLAction c (fun y => f (-y)) x = eta * f (-x) := by
  rw [prolateSLAction_comp_neg c hf hf', h]

/-- The odd part of a profile. -/
def oddPart (f : ℝ → ℝ) (x : ℝ) : ℝ := (f x - f (-x)) / 2

/-- The even part of a profile. -/
def evenPart (f : ℝ → ℝ) (x : ℝ) : ℝ := (f x + f (-x)) / 2

theorem even_evenPart (f : ℝ → ℝ) : Function.Even (evenPart f) := by
  intro x
  unfold evenPart
  rw [neg_neg]
  ring

theorem odd_oddPart (f : ℝ → ℝ) (x : ℝ) : oddPart f (-x) = -oddPart f x := by
  unfold oddPart
  rw [neg_neg]
  ring

theorem evenPart_add_oddPart (f : ℝ → ℝ) (x : ℝ) : evenPart f x + oddPart f x = f x := by
  unfold evenPart oddPart
  ring

theorem continuous_evenPart {f : ℝ → ℝ} (hf : Continuous f) : Continuous (evenPart f) := by
  unfold evenPart
  exact (hf.add (hf.comp continuous_neg)).div_const 2

theorem continuous_oddPart {f : ℝ → ℝ} (hf : Continuous f) : Continuous (oddPart f) := by
  unfold oddPart
  exact (hf.sub (hf.comp continuous_neg)).div_const 2

theorem contDiff_evenPart {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (evenPart f) := by
  unfold evenPart
  exact (hf.add (hf.comp contDiff_neg)).div_const 2

theorem contDiff_oddPart {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (oddPart f) := by
  unfold oddPart
  exact (hf.sub (hf.comp contDiff_neg)).div_const 2

/-- The kernel section is continuous. -/
theorem continuous_sincKernelSmooth_snd (c x : ℝ) :
    Continuous fun y : ℝ => sincKernelSmooth c x y := by
  have h : Continuous fun y : ℝ => x - y := continuous_const.sub continuous_id
  simpa [sincKernelSmooth, Function.comp_def] using (contDiff_sincSmooth c).continuous.comp h

/-- The band transform is additive in its profile. -/
theorem bandTransform_sub (c : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (x : ℝ) :
    bandTransform c (fun y => f y - g y) x = bandTransform c f x - bandTransform c g x := by
  have hker := continuous_sincKernelSmooth_snd c x
  have h1 : IntervalIntegrable (fun y : ℝ => sincKernelSmooth c x y * f y) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact hker.mul hf
  have h2 : IntervalIntegrable (fun y : ℝ => sincKernelSmooth c x y * g y) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact hker.mul hg
  rw [bandTransform, bandTransform, bandTransform,
    ← intervalIntegral.integral_sub h1 h2]
  refine intervalIntegral.integral_congr fun y _ => ?_
  show sincKernelSmooth c x y * (f y - g y)
    = sincKernelSmooth c x y * f y - sincKernelSmooth c x y * g y
  ring

/-- The band transform commutes with scaling. -/
theorem bandTransform_div_two (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    bandTransform c (fun y => f y / 2) x = bandTransform c f x / 2 := by
  rw [bandTransform, bandTransform, ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun y _ => ?_
  show sincKernelSmooth c x y * (f y / 2) = sincKernelSmooth c x y * f y / 2
  ring

/-- The odd part of a global band eigenfunction is a global band eigenfunction. -/
theorem bandTransform_oddPart {c lam : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ x : ℝ, bandTransform c f x = lam * f x) (x : ℝ) :
    bandTransform c (oddPart f) x = lam * oddPart f x := by
  have hrefl : Continuous fun y : ℝ => f (-y) := hf.comp continuous_neg
  have hodd : oddPart f = fun y : ℝ => (f y - f (-y)) / 2 := rfl
  rw [hodd, bandTransform_div_two, bandTransform_sub c hf hrefl, h,
    bandTransform_comp_neg, h]
  show (lam * f x - lam * f (-x)) / 2 = lam * ((f x - f (-x)) / 2)
  ring

/-- An even and an odd profile are orthogonal on the aperture. -/
theorem integral_even_mul_odd_eq_zero {g h : ℝ → ℝ} (_hgc : Continuous g) (_hhc : Continuous h)
    (hg : Function.Even g) (hh : ∀ x : ℝ, h (-x) = -h x) :
    (∫ y in (-1 : ℝ)..1, g y * h y) = 0 := by
  have hcomp := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun y : ℝ => g y * h y)
  rw [neg_neg] at hcomp
  have hval : (∫ y in (-1 : ℝ)..1, g (-y) * h (-y)) = -∫ y in (-1 : ℝ)..1, g y * h y := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ => ?_
    show g (-y) * h (-y) = -(g y * h y)
    rw [hg y, hh y]
    ring
  rw [hval] at hcomp
  linarith [hcomp]

end RHTower
