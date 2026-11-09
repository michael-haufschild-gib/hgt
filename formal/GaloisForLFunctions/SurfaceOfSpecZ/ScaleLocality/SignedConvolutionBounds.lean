import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SignedDeletionFilters
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.MixedPositiveMoments

/-!
# Total-variation bounds for complex deletion

The deletion operator has complex coefficients. The triangle inequality
bounds its action by the absolute coefficient moments; successive filters
add quadratic variation and mixed linear/quadratic moment costs.
-/

open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Complex three-point translation with multiplier `signedDeletionFactor`. -/
def signedAverage (a h : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (f (t - h) / 2 + signedDeletionCenter (h * a) * f t + f (t + h) / 2) /
    (1 + signedDeletionCenter (h * a))

/-- Absolute coefficient moment of a complex deletion kernel. -/
def signedVariationMoment (a h s : ℝ) : ℝ :=
  (Real.cosh (h * s) + ‖signedDeletionCenter (h * a)‖) /
    ‖1 + signedDeletionCenter (h * a)‖

/-- Absolute moments pay quadratic variation and the smaller of support and variance. -/
theorem signedVariationMoment_le (a h s : ℝ) :
    signedVariationMoment a h s ≤
      Real.exp (3 / 2 * (h * a) ^ 2 + min |h * s| (s ^ 2 * h ^ 2 / 2)) := by
  have hc : Real.cosh (h * s) ≤
      Real.exp (min |h * s| (s ^ 2 * h ^ 2 / 2)) := by
    have hl : Real.cosh (h * s) ≤ Real.exp |h * s| := by
      rw [Real.cosh_eq]
      linarith only [Real.exp_le_exp.mpr (le_abs_self (h * s)),
        Real.exp_le_exp.mpr (neg_le_abs (h * s))]
    have hq : Real.cosh (h * s) ≤ Real.exp (s ^ 2 * h ^ 2 / 2) := by
      convert Real.cosh_le_exp_half_sq (h * s) using 2 <;> ring
    rcases le_total |h * s| (s ^ 2 * h ^ 2 / 2) with he | he
    · rwa [min_eq_left he]
    · rwa [min_eq_right he]
  have hone : 1 ≤ Real.exp (min |h * s| (s ^ 2 * h ^ 2 / 2)) :=
    Real.one_le_exp (le_min (abs_nonneg _) (by positivity))
  have hb := mul_le_mul_of_nonneg_left hone (norm_nonneg (signedDeletionCenter (h * a)))
  have hn : Real.cosh (h * s) + ‖signedDeletionCenter (h * a)‖ ≤
      (1 + ‖signedDeletionCenter (h * a)‖) *
        Real.exp (min |h * s| (s ^ 2 * h ^ 2 / 2)) := by
    nlinarith only [hc, hb]
  unfold signedVariationMoment
  calc
    _ ≤ ((1 + ‖signedDeletionCenter (h * a)‖) *
        Real.exp (min |h * s| (s ^ 2 * h ^ 2 / 2))) /
        ‖1 + signedDeletionCenter (h * a)‖ :=
      div_le_div_of_nonneg_right hn (norm_nonneg _)
    _ = ((1 + ‖signedDeletionCenter (h * a)‖) /
        ‖1 + signedDeletionCenter (h * a)‖) *
        Real.exp (min |h * s| (s ^ 2 * h ^ 2 / 2)) := by ring
    _ ≤ Real.exp (3 / 2 * (h * a) ^ 2) *
        Real.exp (min |h * s| (s ^ 2 * h ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_right (signedDeletion_variation_le _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

/-- Triangle inequality for the complex translation operator. -/
theorem norm_signedAverage_le (a h : ℝ) (f : ℝ → ℂ) (t : ℝ) :
    ‖signedAverage a h f t‖ ≤
      (‖f (t - h)‖ / 2 + ‖signedDeletionCenter (h * a)‖ * ‖f t‖ +
        ‖f (t + h)‖ / 2) / ‖1 + signedDeletionCenter (h * a)‖ := by
  unfold signedAverage
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ ‖f (t - h) / 2 + signedDeletionCenter (h * a) * f t‖ +
        ‖f (t + h) / 2‖ := norm_add_le _ _
    _ ≤ (‖f (t - h) / 2‖ + ‖signedDeletionCenter (h * a) * f t‖) +
        ‖f (t + h) / 2‖ := add_le_add_right (norm_add_le _ _) _
    _ = _ := by simp only [norm_div, norm_mul, norm_ofNat]

/-- Complex exponential modes diagonalize signed translation. -/
theorem signedAverage_cexp (a h : ℝ) (c w : ℂ) (t : ℝ) :
    signedAverage a h (fun u => c * Complex.exp (w * u)) t =
      c * signedDeletionFactor a h w * Complex.exp (w * t) := by
  have hl : w * ((t - h : ℝ) : ℂ) = w * t + -((h : ℂ) * w) := by push_cast; ring
  have hr : w * ((t + h : ℝ) : ℂ) = w * t + (h : ℂ) * w := by push_cast; ring
  unfold signedAverage
  rw [hl, hr, Complex.exp_add, Complex.exp_add, signedDeletionFactor, Complex.cosh]
  ring

/-- A constant plus two real exponentials bounds one signed convolution. -/
theorem norm_signedAverage_envelope (a h s t : ℝ) {f : ℝ → ℂ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ∀ u, ‖f u‖ ≤ K + C * (Real.exp (s * u) + Real.exp (-s * u))) :
    ‖signedAverage a h f t‖ ≤
      K * Real.exp (3 / 2 * (h * a) ^ 2) +
      C * Real.exp (3 / 2 * (h * a) ^ 2 + min |h * s| (s ^ 2 * h ^ 2 / 2)) *
        (Real.exp (s * t) + Real.exp (-s * t)) := by
  have hn := norm_signedAverage_le a h f t
  have hu : ‖signedAverage a h f t‖ ≤
      ((K + C * (Real.exp (s * (t - h)) + Real.exp (-s * (t - h)))) / 2 +
        ‖signedDeletionCenter (h * a)‖ * (K + C * (Real.exp (s * t) + Real.exp (-s * t))) +
        (K + C * (Real.exp (s * (t + h)) + Real.exp (-s * (t + h)))) / 2) /
        ‖1 + signedDeletionCenter (h * a)‖ := by
    apply hn.trans
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    exact add_le_add
      (add_le_add (div_le_div_of_nonneg_right (hf _) (by norm_num))
        (mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)))
      (div_le_div_of_nonneg_right (hf _) (by norm_num))
  have he :
      ((K + C * (Real.exp (s * (t - h)) + Real.exp (-s * (t - h)))) / 2 +
        ‖signedDeletionCenter (h * a)‖ * (K + C * (Real.exp (s * t) + Real.exp (-s * t))) +
        (K + C * (Real.exp (s * (t + h)) + Real.exp (-s * (t + h)))) / 2) /
        ‖1 + signedDeletionCenter (h * a)‖ =
      K * ((1 + ‖signedDeletionCenter (h * a)‖) / ‖1 + signedDeletionCenter (h * a)‖) +
      C * signedVariationMoment a h s * (Real.exp (s * t) + Real.exp (-s * t)) := by
    unfold signedVariationMoment
    rw [show s * (t - h) = s * t + -(h * s) by ring,
      show -s * (t - h) = -s * t + h * s by ring,
      show s * (t + h) = s * t + h * s by ring,
      show -s * (t + h) = -s * t + -(h * s) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.cosh_eq]
    ring
  rw [he] at hu
  exact hu.trans (add_le_add (mul_le_mul_of_nonneg_left (signedDeletion_variation_le _) hK)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (signedVariationMoment_le a h s) hC)
      (by positivity)))

/-- Finite composition of complex deletion operators. -/
def signedTailAverage : List (ℝ × ℝ) → (ℝ → ℂ) → ℝ → ℂ
  | [], f => f
  | (a, h) :: l, f => signedAverage a h (signedTailAverage l f)

/-- Quadratic total-variation exponent of a finite convolution. -/
def signedVariationCost (l : List (ℝ × ℝ)) : ℝ :=
  (l.map fun p => 3 / 2 * (p.2 * p.1) ^ 2).sum

/-- Variation and moment costs add through complex convolution. -/
theorem norm_signedTailAverage_envelope (l : List (ℝ × ℝ)) {f : ℝ → ℂ} {K C s : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ∀ u, ‖f u‖ ≤ K + C * (Real.exp (s * u) + Real.exp (-s * u))) (t : ℝ) :
    ‖signedTailAverage l f t‖ ≤
      K * Real.exp (signedVariationCost l) +
      C * Real.exp (signedVariationCost l + mixedMomentCost l s) *
        (Real.exp (s * t) + Real.exp (-s * t)) := by
  induction l generalizing t with
  | nil => simpa only [signedTailAverage, signedVariationCost, mixedMomentCost,
      List.map_nil, List.sum_nil, add_zero, Real.exp_zero, mul_one] using hf t
  | cons p l ih =>
      have hh := norm_signedAverage_envelope p.1 p.2 s t
        (mul_nonneg hK (Real.exp_pos _).le) (mul_nonneg hC (Real.exp_pos _).le) ih
      change ‖signedTailAverage (p :: l) f t‖ ≤ _ at hh
      convert hh using 1 <;>
        simp only [signedVariationCost, mixedMomentCost, List.map_cons, List.sum_cons,
          Real.exp_add] <;> ring

/-- Local norm bounds survive finite signed deletion with exponentially small leakage. -/
theorem signedTailAverage_local_norm (l : List (ℝ × ℝ)) {f : ℝ → ℂ}
    {K C D q L : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hglobal : ∀ u, ‖f u‖ ≤ C * Real.exp (D * |u|))
    (hlocal : ∀ u, |u| ≤ L → ‖f u‖ ≤ K) :
    ‖signedTailAverage l f 0‖ ≤ Real.exp (signedVariationCost l) *
      (K + 2 * C * Real.exp (-q * L + mixedMomentCost l (D + q))) := by
  let E : ℝ := C * Real.exp (-q * L)
  have hE : 0 ≤ E := mul_nonneg hC (Real.exp_pos _).le
  have hp : ∀ u, ‖f u‖ ≤ K + E *
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
      calc ‖f u‖ ≤ C * Real.exp (D * |u|) := hglobal u
        _ ≤ E * Real.exp ((D + q) * |u|) := by
          dsimp only [E]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left he hC
        _ ≤ E * (Real.exp ((D + q) * u) + Real.exp (-(D + q) * u)) :=
          mul_le_mul_of_nonneg_left habs hE
        _ ≤ K + E * (Real.exp ((D + q) * u) + Real.exp (-(D + q) * u)) :=
          le_add_of_nonneg_left hK
  have hh := norm_signedTailAverage_envelope l hK hE hp 0
  simp only [mul_zero, Real.exp_zero] at hh
  convert hh using 1 <;> simp only [E, Real.exp_add] <;> ring

#print axioms norm_signedTailAverage_envelope
#print axioms signedTailAverage_local_norm

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
