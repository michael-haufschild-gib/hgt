import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Positive symmetric filters for deleting nonreal exponents

A three-point probability average annihilates a prescribed conjugate-reflected quartet.
Its exponential moment is bounded by a Gaussian with variance parameter equal to the
square of its shift. Finite compositions add these parameters, rather than their support
radii. This distinction permits deletion of increasingly large zero sets at bounded cost.
-/

open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Laplace multiplier of the symmetric average at shifts `-h, 0, h`. -/
def quartetFactor (a h : ℝ) (w : ℂ) : ℂ :=
  (Complex.cosh ((h : ℂ) * w) + (Real.cosh (h * a) : ℂ)) /
    (1 + (Real.cosh (h * a) : ℂ))

/-- The corresponding positive average of a real function. -/
def quartetAverage (a h : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f (t - h) / 2 + Real.cosh (h * a) * f t + f (t + h) / 2) /
    (1 + Real.cosh (h * a))

private theorem denominator_pos (a h : ℝ) : 0 < 1 + Real.cosh (h * a) := by
  linarith [Real.cosh_pos (h * a)]

private theorem denominator_ne_zero (a h : ℝ) :
    (1 + (Real.cosh (h * a) : ℂ)) ≠ 0 := by
  exact_mod_cast (denominator_pos a h).ne'

@[simp] theorem quartetFactor_zero (a h : ℝ) : quartetFactor a h 0 = 1 := by
  simp only [quartetFactor, mul_zero, Complex.cosh_zero]
  exact div_self (denominator_ne_zero a h)

@[simp] theorem quartetFactor_neg (a h : ℝ) (w : ℂ) :
    quartetFactor a h (-w) = quartetFactor a h w := by
  simp only [quartetFactor, mul_neg, Complex.cosh_neg]

/-- The half-period shift kills the prescribed exponent exactly. -/
theorem quartetFactor_root (a h γ : ℝ) (hphase : h * γ = Real.pi) :
    quartetFactor a h ((a : ℂ) + (γ : ℂ) * I) = 0 := by
  have he : (h : ℂ) * ((a : ℂ) + (γ : ℂ) * I) =
      ((h * a : ℝ) : ℂ) + (Real.pi : ℂ) * I := by
    calc _ = ((h * a : ℝ) : ℂ) + ((h * γ : ℝ) : ℂ) * I := by push_cast; ring
         _ = _ := by rw [hphase]
  rw [quartetFactor, he, Complex.cosh_add]
  have hc : Complex.cosh ((Real.pi : ℂ) * I) = -1 := by
    simp [Complex.cosh, Complex.exp_pi_mul_I, Complex.exp_neg]
  have hs : Complex.sinh ((Real.pi : ℂ) * I) = 0 := by
    simp [Complex.sinh, Complex.exp_pi_mul_I, Complex.exp_neg]
  rw [hc, hs, mul_zero, add_zero, mul_neg_one, ← Complex.ofReal_cosh,
    neg_add_cancel, zero_div]

/-- Positive averages preserve every pointwise inequality. -/
theorem quartetAverage_mono (a h : ℝ) {f g : ℝ → ℝ} (hfg : ∀ t, f t ≤ g t) (t : ℝ) :
    quartetAverage a h f t ≤ quartetAverage a h g t := by
  unfold quartetAverage
  apply div_le_div_of_nonneg_right _ (denominator_pos a h).le
  exact add_le_add
    (add_le_add (div_le_div_of_nonneg_right (hfg _) (by norm_num))
      (mul_le_mul_of_nonneg_left (hfg _) (Real.cosh_pos _).le))
    (div_le_div_of_nonneg_right (hfg _) (by norm_num))

@[simp] theorem quartetAverage_const (a h c t : ℝ) :
    quartetAverage a h (fun _ => c) t = c := by
  unfold quartetAverage
  apply (div_eq_iff (denominator_pos a h).ne').mpr
  ring

theorem quartetAverage_add (a h : ℝ) (f g : ℝ → ℝ) (t : ℝ) :
    quartetAverage a h (fun u => f u + g u) t =
      quartetAverage a h f t + quartetAverage a h g t := by
  unfold quartetAverage
  ring

theorem quartetAverage_mul (a h c : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    quartetAverage a h (fun u => c * f u) t = c * quartetAverage a h f t := by
  unfold quartetAverage
  ring

/-- Real exponential functions diagonalize the averaging operator. -/
theorem quartetAverage_exp (a h s t : ℝ) :
    quartetAverage a h (fun u => Real.exp (s * u)) t =
      ((Real.cosh (h * s) + Real.cosh (h * a)) / (1 + Real.cosh (h * a))) *
        Real.exp (s * t) := by
  dsimp only [quartetAverage]
  rw [show s * (t - h) = s * t + -(h * s) by ring,
    show s * (t + h) = s * t + h * s by ring, Real.exp_add, Real.exp_add,
    Real.cosh_eq (h * s)]
  ring

/-- The variance bound does not depend on the real part of the deleted exponent. -/
theorem quartet_mgf_le (a h s : ℝ) :
    (Real.cosh (h * s) + Real.cosh (h * a)) / (1 + Real.cosh (h * a)) ≤
      Real.exp (s ^ 2 * h ^ 2 / 2) := by
  have hcosh := Real.cosh_le_exp_half_sq (h * s)
  have hexp : 1 ≤ Real.exp (s ^ 2 * h ^ 2 / 2) :=
    Real.one_le_exp (by positivity)
  have hcosh' : Real.cosh (h * s) ≤ Real.exp (s ^ 2 * h ^ 2 / 2) := by
    convert hcosh using 2; ring
  apply (div_le_iff₀ (denominator_pos a h)).mpr
  have hh := mul_le_mul_of_nonneg_right hexp (Real.cosh_pos (h * a)).le
  nlinarith only [hcosh', hh]

/-- Composition of positive three-point averages. -/
def tailAverage : List (ℝ × ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | (a, h) :: l, f => quartetAverage a h (tailAverage l f)

/-- Sum of squared shifts, the Gaussian variance parameter. -/
def squareCost (l : List (ℝ × ℝ)) : ℝ := (l.map fun p => p.2 ^ 2).sum

theorem squareCost_nonneg (l : List (ℝ × ℝ)) : 0 ≤ squareCost l := by
  induction l with
  | nil => simp [squareCost]
  | cons p l ih => simpa [squareCost] using add_nonneg (sq_nonneg p.2) ih

theorem tailAverage_mono (l : List (ℝ × ℝ)) {f g : ℝ → ℝ}
    (hfg : ∀ t, f t ≤ g t) (t : ℝ) : tailAverage l f t ≤ tailAverage l g t := by
  induction l generalizing t with
  | nil => exact hfg t
  | cons p l ih => exact quartetAverage_mono _ _ ih t

@[simp] theorem tailAverage_const (l : List (ℝ × ℝ)) (c t : ℝ) :
    tailAverage l (fun _ => c) t = c := by
  induction l generalizing t with
  | nil => rfl
  | cons p l ih => simp only [tailAverage, show tailAverage l (fun _ => c) = fun _ => c from funext ih,
      quartetAverage_const]

theorem tailAverage_add (l : List (ℝ × ℝ)) (f g : ℝ → ℝ) (t : ℝ) :
    tailAverage l (fun u => f u + g u) t = tailAverage l f t + tailAverage l g t := by
  induction l generalizing t with
  | nil => rfl
  | cons p l ih =>
      simp only [tailAverage, show tailAverage l (fun u => f u + g u) =
        fun u => tailAverage l f u + tailAverage l g u from funext ih, quartetAverage_add]

theorem tailAverage_mul (l : List (ℝ × ℝ)) (c : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    tailAverage l (fun u => c * f u) t = c * tailAverage l f t := by
  induction l generalizing t with
  | nil => rfl
  | cons p l ih =>
      simp only [tailAverage, show tailAverage l (fun u => c * f u) =
        fun u => c * tailAverage l f u from funext ih, quartetAverage_mul]

/-- The exponential moment of every finite deletion is bounded by its square cost. -/
theorem tailAverage_exp_le (l : List (ℝ × ℝ)) (s t : ℝ) :
    tailAverage l (fun u => Real.exp (s * u)) t ≤
      Real.exp (s ^ 2 * squareCost l / 2) * Real.exp (s * t) := by
  induction l generalizing t with
  | nil => simp [tailAverage, squareCost]
  | cons p l ih =>
      calc tailAverage (p :: l) (fun u => Real.exp (s * u)) t
          ≤ quartetAverage p.1 p.2
            (fun u => Real.exp (s ^ 2 * squareCost l / 2) * Real.exp (s * u)) t :=
              quartetAverage_mono _ _ ih t
        _ = Real.exp (s ^ 2 * squareCost l / 2) *
            (((Real.cosh (p.2 * s) + Real.cosh (p.2 * p.1)) /
              (1 + Real.cosh (p.2 * p.1))) * Real.exp (s * t)) := by
                rw [quartetAverage_mul, quartetAverage_exp]
        _ ≤ Real.exp (s ^ 2 * squareCost l / 2) *
            (Real.exp (s ^ 2 * p.2 ^ 2 / 2) * Real.exp (s * t)) := by
              gcongr
              exact quartet_mgf_le _ _ _
        _ = _ := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          simp only [squareCost, List.map_cons, List.sum_cons]
          ring

/-- A local ceiling survives deletion, with an explicit Gaussian leakage from its complement.
The number and total support radius of the shifts do not occur in the bound. -/
theorem tailAverage_local_ceiling (l : List (ℝ × ℝ)) {f : ℝ → ℝ}
    {K C D q L : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hglobal : ∀ u, f u ≤ C * Real.exp (D * |u|))
    (hlocal : ∀ u, |u| ≤ L → f u ≤ K) :
    tailAverage l f 0 ≤ K +
      2 * C * Real.exp (-q * L + (D + q) ^ 2 * squareCost l / 2) := by
  let E : ℝ := C * Real.exp (-q * L)
  have hE : 0 ≤ E := mul_nonneg hC (Real.exp_pos _).le
  have hp : ∀ u, f u ≤ K + E *
      (Real.exp ((D + q) * u) + Real.exp (-(D + q) * u)) := by
    intro u
    by_cases hu : |u| ≤ L
    · exact (hlocal u hu).trans (le_add_of_nonneg_right (by positivity))
    · have hLu : L ≤ |u| := (lt_of_not_ge hu).le
      have he : Real.exp (D * |u|) ≤
          Real.exp (-q * L) * Real.exp ((D + q) * |u|) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hLu hq])
      have habs : Real.exp ((D + q) * |u|) ≤
          Real.exp ((D + q) * u) + Real.exp (-(D + q) * u) := by
        rcases le_total 0 u with hu0 | hu0
        · rw [abs_of_nonneg hu0]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [abs_of_nonpos hu0, mul_neg, ← neg_mul]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
      calc f u ≤ C * Real.exp (D * |u|) := hglobal u
        _ ≤ E * Real.exp ((D + q) * |u|) := by
          dsimp only [E]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left he hC
        _ ≤ E * (Real.exp ((D + q) * u) + Real.exp (-(D + q) * u)) :=
          mul_le_mul_of_nonneg_left habs hE
        _ ≤ K + E * (Real.exp ((D + q) * u) + Real.exp (-(D + q) * u)) :=
          le_add_of_nonneg_left hK
  have hm := tailAverage_mono l hp 0
  rw [tailAverage_add, tailAverage_const, tailAverage_mul, tailAverage_add] at hm
  have hplus := tailAverage_exp_le l (D + q) 0
  have hminus := tailAverage_exp_le l (-(D + q)) 0
  simp only [mul_zero, Real.exp_zero, mul_one, neg_sq] at hplus hminus
  calc tailAverage l f 0 ≤ K + E *
        (tailAverage l (fun u => Real.exp ((D + q) * u)) 0 +
          tailAverage l (fun u => Real.exp (-(D + q) * u)) 0) := hm
    _ ≤ K + E * (2 * Real.exp ((D + q) ^ 2 * squareCost l / 2)) := by
      gcongr
      linarith only [hplus, hminus]
    _ = _ := by dsimp only [E]; rw [Real.exp_add]; ring

/-- A local lower bound is stable under positive zero deletion with the same leakage cost. -/
theorem tailAverage_local_floor (l : List (ℝ × ℝ)) {f : ℝ → ℝ}
    {K C D q L : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hglobal : ∀ u, -C * Real.exp (D * |u|) ≤ f u)
    (hlocal : ∀ u, |u| ≤ L → -K ≤ f u) :
    -K - 2 * C * Real.exp (-q * L + (D + q) ^ 2 * squareCost l / 2) ≤
      tailAverage l f 0 := by
  have h := tailAverage_local_ceiling l hK hC hq
    (f := fun u => (-1 : ℝ) * f u)
    (fun u => by linarith only [hglobal u])
    (fun u hu => by linarith only [hlocal u hu])
  rw [tailAverage_mul] at h
  linarith only [h]

#print axioms quartetFactor_root
#print axioms tailAverage_exp_le
#print axioms tailAverage_local_floor

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
