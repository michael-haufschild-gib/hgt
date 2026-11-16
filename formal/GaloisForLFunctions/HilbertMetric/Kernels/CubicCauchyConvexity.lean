import GaloisForLFunctions.HTGeometry.ConvexAntitoneComposition
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The cubic Cauchy interaction kernel

The reciprocal quadratic `1/(A²+At+t²)` is strictly decreasing and
strictly convex for `A ≥ 0`, `t > 0`. Multiplication by `1/√t` and
composition with `S^(2/3)` recover the positive interaction kernel
for pairs of Cauchy poles on the rays of arguments `±π/3`.

The proof extends the same-direction product and decreasing-convex
composition mechanisms used for the Hilbert–Hankel integrand.
-/

noncomputable section
open Set

namespace GaloisForLFunctions.HilbertMetric

def cubicDenominator (A t : ℝ) : ℝ := A ^ 2 + A * t + t ^ 2

def reciprocalCubic (A t : ℝ) : ℝ := (cubicDenominator A t)⁻¹

private theorem cubicDenominator_pos {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    0 < cubicDenominator A t := by
  unfold cubicDenominator
  positivity

private theorem hasDerivAt_cubicDenominator (A t : ℝ) :
    HasDerivAt (cubicDenominator A) (A + 2 * t) t := by
  have h := (((hasDerivAt_id t).const_mul A).const_add (A ^ 2)).add
    ((hasDerivAt_id t).pow 2)
  exact h.congr_deriv (by simp)

private def reciprocalCubic₁ (A t : ℝ) : ℝ :=
  -(A + 2 * t) / cubicDenominator A t ^ 2

private theorem hasDerivAt_reciprocalCubic {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    HasDerivAt (reciprocalCubic A) (reciprocalCubic₁ A t) t := by
  exact (hasDerivAt_cubicDenominator A t).inv (cubicDenominator_pos hA ht).ne'

/-- The second derivative has a positive numerator with no cancellation. -/
private theorem hasDerivAt_reciprocalCubic₁ {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    HasDerivAt (reciprocalCubic₁ A)
      (6 * t * (A + t) / cubicDenominator A t ^ 3) t := by
  have hD := hasDerivAt_cubicDenominator A t
  have hn := (((hasDerivAt_id t).const_mul 2).const_add A).neg
  have h := hn.div (hD.pow 2) (pow_ne_zero 2 (cubicDenominator_pos hA ht).ne')
  apply h.congr_deriv
  dsimp
  field_simp [(cubicDenominator_pos hA ht).ne']
  unfold cubicDenominator
  ring

theorem reciprocalCubic_pos {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    0 < reciprocalCubic A t := inv_pos.mpr (cubicDenominator_pos hA ht)

theorem strictAntiOn_reciprocalCubic {A : ℝ} (hA : 0 ≤ A) :
    StrictAntiOn (reciprocalCubic A) (Ioi 0) := by
  intro x hx y hy hxy
  apply inv_strictAnti₀ (cubicDenominator_pos hA hx)
  unfold cubicDenominator
  have hAt := mul_nonneg hA (sub_pos.mpr hxy).le
  have hsq := sq_lt_sq₀ hx.le hy.le |>.mpr hxy
  nlinarith only [hAt, hsq]

theorem strictConvexOn_reciprocalCubic {A : ℝ} (hA : 0 ≤ A) :
    StrictConvexOn ℝ (Ioi 0) (reciprocalCubic A) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
    (fun t ht => (hasDerivAt_reciprocalCubic hA ht).continuousAt.continuousWithinAt)
  intro t ht
  have he : deriv (reciprocalCubic A) =ᶠ[nhds t] reciprocalCubic₁ A :=
    Filter.Eventually.mono (isOpen_Ioi.mem_nhds ht)
      (fun y hy => (hasDerivAt_reciprocalCubic hA hy).deriv)
  change 0 < deriv (deriv (reciprocalCubic A)) t
  rw [((hasDerivAt_reciprocalCubic₁ hA ht).congr_of_eventuallyEq he).deriv]
  exact div_pos (mul_pos (mul_pos (by norm_num) ht) (add_pos_of_nonneg_of_pos hA ht))
    (pow_pos (cubicDenominator_pos hA ht) 3)

/-- The reciprocal square-root weight preserves convexity and strict decrease. -/
def weightedReciprocalCubic (A t : ℝ) : ℝ :=
  (Real.sqrt t)⁻¹ * reciprocalCubic A t

theorem weightedReciprocalCubic_pos {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    0 < weightedReciprocalCubic A t :=
  mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr ht)) (reciprocalCubic_pos hA ht)

theorem convexOn_weightedReciprocalCubic {A : ℝ} (hA : 0 ≤ A) :
    ConvexOn ℝ (Ioi 0) (weightedReciprocalCubic A) := by
  apply GaloisForLFunctions.ConvexOn.mul_of_sameDirection convexOn_inv_sqrt
    (strictConvexOn_reciprocalCubic hA).convexOn
  · intro t ht
    exact (inv_pos.mpr (Real.sqrt_pos.mpr ht)).le
  · intro t ht
    exact (reciprocalCubic_pos hA ht).le
  · exact sameDirection_of_antitoneOn antitoneOn_inv_sqrt
      (strictAntiOn_reciprocalCubic hA).antitoneOn

theorem strictAntiOn_weightedReciprocalCubic {A : ℝ} (hA : 0 ≤ A) :
    StrictAntiOn (weightedReciprocalCubic A) (Ioi 0) := by
  intro x hx y hy hxy
  calc weightedReciprocalCubic A y
      ≤ (Real.sqrt x)⁻¹ * reciprocalCubic A y :=
        mul_le_mul_of_nonneg_right (antitoneOn_inv_sqrt hx hy hxy.le)
          (reciprocalCubic_pos hA hy).le
    _ < weightedReciprocalCubic A x :=
        mul_lt_mul_of_pos_left (strictAntiOn_reciprocalCubic hA hx hy hxy)
          (inv_pos.mpr (Real.sqrt_pos.mpr hx))

/-- Strict concavity inside a strictly decreasing convex function gives strict convexity. -/
theorem convex_comp_strictConcave_of_strictAnti {s t : Set ℝ} {f g : ℝ → ℝ}
    (hf : ConvexOn ℝ t f) (hanti : StrictAntiOn f t)
    (hg : StrictConcaveOn ℝ s g) (hmaps : ∀ x ∈ s, g x ∈ t) :
    StrictConvexOn ℝ s (fun x => f (g x)) := by
  refine ⟨hg.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hgc := hmaps _ (hg.1 hx hy ha.le hb.le hab)
  have hcomb := hf.1 (hmaps x hx) (hmaps y hy) ha.le hb.le hab
  exact (hanti hcomb hgc (hg.2 hx hy hxy ha hb hab)).trans_le
    (hf.2 (hmaps x hx) (hmaps y hy) ha.le hb.le hab)

/-- The positive Cauchy interaction kernel in power coordinates. -/
def cubicCauchyKernel (X S : ℝ) : ℝ :=
  (X ^ (2 / 3 : ℝ) / Real.sqrt 3) *
    weightedReciprocalCubic (X ^ (2 / 3 : ℝ)) (S ^ (2 / 3 : ℝ))

theorem cubicCauchyKernel_pos {X S : ℝ} (hX : 0 < X) (hS : 0 < S) :
    0 < cubicCauchyKernel X S :=
  mul_pos (div_pos (Real.rpow_pos_of_pos hX _) (Real.sqrt_pos.mpr (by norm_num)))
    (weightedReciprocalCubic_pos (Real.rpow_pos_of_pos hX _).le
      (Real.rpow_pos_of_pos hS _))

theorem strictAntiOn_cubicCauchyKernel {X : ℝ} (hX : 0 < X) :
    StrictAntiOn (cubicCauchyKernel X) (Ioi 0) := by
  intro S hS T hT hST
  apply mul_lt_mul_of_pos_left _
    (div_pos (Real.rpow_pos_of_pos hX _) (Real.sqrt_pos.mpr (by norm_num)))
  exact strictAntiOn_weightedReciprocalCubic (Real.rpow_pos_of_pos hX _).le
    (Real.rpow_pos_of_pos hS _) (Real.rpow_pos_of_pos hT _)
    (Real.rpow_lt_rpow hS.le hST (by norm_num))

theorem strictConvexOn_cubicCauchyKernel {X : ℝ} (hX : 0 < X) :
    StrictConvexOn ℝ (Ioi 0) (cubicCauchyKernel X) := by
  have hA := (Real.rpow_pos_of_pos hX (2 / 3 : ℝ)).le
  have hg := (Real.strictConcaveOn_rpow (p := (2 / 3 : ℝ)) (by norm_num) (by norm_num)).subset
    Ioi_subset_Ici_self (convex_Ioi 0)
  have h := convex_comp_strictConcave_of_strictAnti
    (convexOn_weightedReciprocalCubic hA) (strictAntiOn_weightedReciprocalCubic hA)
    hg (fun S hS => Real.rpow_pos_of_pos hS _)
  have hc : 0 < X ^ (2 / 3 : ℝ) / Real.sqrt 3 :=
    div_pos (Real.rpow_pos_of_pos hX _) (Real.sqrt_pos.mpr (by norm_num))
  refine ⟨h.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hh := mul_lt_mul_of_pos_left (h.2 hx hy hxy ha hb hab) hc
  simpa only [cubicCauchyKernel, smul_eq_mul, mul_add, mul_assoc, mul_left_comm] using hh

/-- Identification with the kernel in the original fractional powers. -/
theorem cubicCauchyKernel_eq {X S : ℝ} (hX : 0 < X) (hS : 0 < S) :
    cubicCauchyKernel X S =
      X ^ (2 / 3 : ℝ) * S ^ (-(1 / 3 : ℝ)) /
        (Real.sqrt 3 * (X ^ (4 / 3 : ℝ) +
          X ^ (2 / 3 : ℝ) * S ^ (2 / 3 : ℝ) + S ^ (4 / 3 : ℝ))) := by
  have hs : Real.sqrt (S ^ (2 / 3 : ℝ)) = S ^ (1 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hS.le]
    norm_num
  have hpow (x : ℝ) (hx : 0 < x) : (x ^ (2 / 3 : ℝ)) ^ 2 = x ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx.le]
    norm_num
  simp only [cubicCauchyKernel, weightedReciprocalCubic, reciprocalCubic,
    cubicDenominator, hs, hpow X hX, hpow S hS, Real.rpow_neg hS.le,
    div_eq_mul_inv, mul_inv]
  ring

#print axioms strictConvexOn_reciprocalCubic
#print axioms convex_comp_strictConcave_of_strictAnti
#print axioms strictConvexOn_cubicCauchyKernel
#print axioms cubicCauchyKernel_eq

end GaloisForLFunctions.HilbertMetric
