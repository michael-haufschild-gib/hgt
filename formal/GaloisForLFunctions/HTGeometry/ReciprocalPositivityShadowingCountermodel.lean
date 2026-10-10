import GaloisForLFunctions.HTGeometry.ReciprocalDoubleShadowing
import GaloisForLFunctions.HTGeometry.ReciprocalTotalPositivityRealZeros

/-!
# Reciprocal positivity at every height does not force real zeros

Let `P(z) = (z² − 1)² ((z − 1)² + 1) ((z + 1)² + 1)` (`shadowPoly`).  It is an even real
polynomial with the non-real zeros `±1 ± i`.  At a real height `t` put
`h_t(σ) = P(t+σ)P(t−σ)` (`shadowPair`) and `F_t(y) = h_t(√(−y))` (`shadowLift`).

**Theorem** (`reciprocalTPUpTo_one_shadowLift`).  For every real `t` with `P(t) ≠ 0`, the Taylor
coefficients of `1/F_t(−z)` are nonnegative.  So `F_t` is reciprocally totally positive of
order one at every height, although `P` has non-real zeros.

Each zero `z` of `P` contributes the factor `1 − σ²/(t − z)²` to `h_t`.  The double real zero `1`
shadows the pair `1 ± i` at every height, since `|t − 1| ≤ |t − 1 ∓ i|`.  The same holds for `−1`
and `−1 ± i`.  Double shadowing (`evenRecipNonneg_doubleShadow`) then gives nonnegative
reciprocal coefficients.

So finite-order zero location (`ReciprocalTPUpTo.eq_neg_of_apply_eq_zero`) cannot be upgraded to
a fixed order valid at every height.  The order must reach the number of zeros in the disk.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder Nat

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `P(z) = (z² − 1)² ((z − 1)² + 1) ((z + 1)² + 1)`. -/
def shadowPoly (z : ℂ) : ℂ := (z ^ 2 - 1) ^ 2 * ((z - 1) ^ 2 + 1) * ((z + 1) ^ 2 + 1)

theorem shadowPoly_neg (z : ℂ) : shadowPoly (-z) = shadowPoly z := by
  unfold shadowPoly
  ring

theorem shadowPoly_one_add_I : shadowPoly (1 + I) = 0 := by
  unfold shadowPoly
  have h : ((1 + I) - 1) ^ 2 + 1 = 0 := by
    rw [add_sub_cancel_left, Complex.I_sq]
    ring
  rw [h, mul_zero, zero_mul]

theorem shadowPoly_ofReal_ne_zero {t : ℝ} (h : shadowPoly t ≠ 0) : t ≠ 1 ∧ t ≠ -1 := by
  constructor <;> rintro rfl <;> apply h <;> unfold shadowPoly <;> push_cast <;> ring

/-- The pair product `h_t(σ) = P(t+σ)P(t−σ)`. -/
def shadowPair (t : ℝ) (σ : ℂ) : ℂ := shadowPoly (t + σ) * shadowPoly (t - σ)

theorem sq_add_one_eq_mul (s : ℂ) : s ^ 2 + 1 = (s - I) * (s + I) := by
  linear_combination Complex.I_sq

/-- One shadowing block: `(a² − σ²)² ((a−i)² − σ²)((a+i)² − σ²)` is `a⁴(a²+1)²` times the
doubly shadowed group with `x = y = 1/a²` and `w = 1/(a − i)²`. -/
theorem shadowBlock_eq {a : ℝ} (ha : a ≠ 0) (σ : ℂ) :
    ((a : ℂ) ^ 2 - σ ^ 2) ^ 2 * (((a : ℂ) - I) ^ 2 - σ ^ 2) * (((a : ℂ) + I) ^ 2 - σ ^ 2) =
      ((a ^ 4 * (a ^ 2 + 1) ^ 2 : ℝ) : ℂ) *
        doubleShadowGroup (1 / a ^ 2) (1 / a ^ 2) (1 / ((a : ℂ) - I) ^ 2) σ := by
  have hconj : starRingEnd ℂ (1 / ((a : ℂ) - I) ^ 2) = 1 / ((a : ℂ) + I) ^ 2 := by
    simp [Complex.conj_ofReal, Complex.conj_I, sub_neg_eq_add]
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hu : (a : ℂ) - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hv : (a : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have huv : ((a : ℂ) - I) * ((a : ℂ) + I) = ((a ^ 2 + 1 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-1 : ℂ) * Complex.I_sq
  have hK : ((a ^ 4 * (a ^ 2 + 1) ^ 2 : ℝ) : ℂ) =
      (a : ℂ) ^ 4 * (((a : ℂ) - I) * ((a : ℂ) + I)) ^ 2 := by
    rw [huv]
    push_cast
    ring
  unfold doubleShadowGroup
  rw [hconj, hK]
  push_cast
  field_simp

theorem norm_inv_sub_I_sq_le {a : ℝ} (ha : a ≠ 0) :
    ‖1 / ((a : ℂ) - I) ^ 2‖ ≤ 1 / a ^ 2 := by
  have hn : ‖(a : ℂ) - I‖ ^ 2 = a ^ 2 + 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [norm_div, norm_one, norm_pow, hn]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- `h_t` is a positive constant times two doubly shadowed groups. -/
theorem shadowPair_eq {t : ℝ} (h1 : t ≠ 1) (h2 : t ≠ -1) :
    shadowPair t = fun σ =>
      ((((t - 1) ^ 4 * ((t - 1) ^ 2 + 1) ^ 2) * ((t + 1) ^ 4 * ((t + 1) ^ 2 + 1) ^ 2) : ℝ) : ℂ) *
        (doubleShadowGroup (1 / (t - 1) ^ 2) (1 / (t - 1) ^ 2)
            (1 / (((t - 1 : ℝ) : ℂ) - I) ^ 2) σ *
          doubleShadowGroup (1 / (t + 1) ^ 2) (1 / (t + 1) ^ 2)
            (1 / (((t + 1 : ℝ) : ℂ) - I) ^ 2) σ) := by
  funext σ
  have ha : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hb : t + 1 ≠ 0 := by
    intro h
    apply h2
    linarith
  have e1 := shadowBlock_eq ha σ
  have e2 := shadowBlock_eq hb σ
  have hbr : shadowPair t σ =
      (((((t - 1 : ℝ) : ℂ)) ^ 2 - σ ^ 2) ^ 2 * ((((t - 1 : ℝ) : ℂ) - I) ^ 2 - σ ^ 2) *
        ((((t - 1 : ℝ) : ℂ) + I) ^ 2 - σ ^ 2)) *
      (((((t + 1 : ℝ) : ℂ)) ^ 2 - σ ^ 2) ^ 2 * ((((t + 1 : ℝ) : ℂ) - I) ^ 2 - σ ^ 2) *
        ((((t + 1 : ℝ) : ℂ) + I) ^ 2 - σ ^ 2)) := by
    unfold shadowPair shadowPoly
    simp only [sq_add_one_eq_mul]
    push_cast
    ring
  rw [hbr, e1, e2]
  push_cast
  ring

theorem evenRecipNonneg_shadowPair {t : ℝ} (h1 : t ≠ 1) (h2 : t ≠ -1) :
    EvenRecipNonneg (shadowPair t) := by
  have ha : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hb : t + 1 ≠ 0 := by
    intro h
    apply h2
    linarith
  have hK : 0 < ((t - 1) ^ 4 * ((t - 1) ^ 2 + 1) ^ 2) * ((t + 1) ^ 4 * ((t + 1) ^ 2 + 1) ^ 2) := by
    positivity
  have hG1 := evenRecipNonneg_doubleShadow (norm_inv_sub_I_sq_le ha) (norm_inv_sub_I_sq_le ha)
  have hG2 := evenRecipNonneg_doubleShadow (norm_inv_sub_I_sq_le hb) (norm_inv_sub_I_sq_le hb)
  rw [shadowPair_eq h1 h2]
  exact (EvenRecipNonneg.const hK).mul (hG1.mul hG2)

theorem differentiable_shadowPair (t : ℝ) : Differentiable ℂ (shadowPair t) := by
  unfold shadowPair shadowPoly
  fun_prop

theorem shadowPair_neg (t : ℝ) (σ : ℂ) : shadowPair t (-σ) = shadowPair t σ := by
  unfold shadowPair
  rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

/-- The lift `F_t(y) = h_t(√(−y))`. -/
def shadowLift (t : ℝ) (y : ℂ) : ℂ := evenSquareLift (shadowPair t) (-y)

/-- **Order-one reciprocal total positivity at every height, with non-real zeros.** -/
theorem reciprocalTPUpTo_one_shadowLift {t : ℝ} (ht : shadowPoly t ≠ 0) :
    ReciprocalTPUpTo 1 (shadowLift t) := by
  obtain ⟨h1, h2⟩ := shadowPoly_ofReal_ne_zero ht
  have hE := evenRecipNonneg_shadowPair h1 h2
  have hdiff : Differentiable ℂ (shadowLift t) :=
    (differentiable_evenSquareLift (differentiable_shadowPair t)).comp differentiable_neg
  have hsq : ∀ σ : ℂ, shadowLift t (-(σ ^ 2)) = shadowPair t σ := by
    intro σ
    unfold shadowLift
    rw [neg_neg]
    exact evenSquareLift_sq (differentiable_shadowPair t) (shadowPair_neg t) σ
  have hh0 : shadowLift t 0 ≠ 0 := by
    have h := hsq 0
    rw [show -((0 : ℂ) ^ 2) = 0 by ring] at h
    rw [h]
    unfold shadowPair
    simpa using mul_ne_zero ht ht
  set g : ℂ → ℂ := recipNeg (shadowLift t) with hg
  have hgsq : (fun σ => g (σ ^ 2)) = fun σ => (shadowPair t σ)⁻¹ := by
    funext σ
    simp only [hg, recipNeg]
    rw [hsq]
  have hgan : AnalyticAt ℂ g 0 := by
    have hne : shadowLift t (-0) ≠ 0 := by simpa using hh0
    exact ((hdiff.comp differentiable_neg).analyticAt 0).inv hne
  have hcoef : ∀ n, ((n ! : ℂ))⁻¹ * iteratedDeriv n g 0 =
      ((evenRecipCoeff (shadowPair t) n : ℝ) : ℂ) := by
    intro n
    rw [← iteratedDeriv_comp_sq hgan n, hgsq]
    exact hE.coeff_real n
  have hnn : ∀ n, 0 ≤ recipCoeff (shadowLift t) n := by
    intro n
    unfold recipCoeff
    rw [← hg, hcoef n, Complex.ofReal_re]
    exact hE.evenRecipCoeff_nonneg n
  refine ⟨hdiff, hh0, fun n => ?_, ?_⟩
  · have hD : iteratedDeriv n g 0 =
        ((n ! : ℂ)) * ((evenRecipCoeff (shadowPair t) n : ℝ) : ℂ) := by
      rw [← hcoef n]
      have : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      field_simp
    show 0 ≤ iteratedDeriv n g 0
    rw [hD]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.mpr (hE.evenRecipCoeff_nonneg n))
  · intro m hm i₀ j _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
    · simp [toeplitzMinor]
    · rw [toeplitzMinor, Matrix.det_unique]
      simp only [Matrix.of_apply, zext]
      split_ifs
      · exact hnn _
      · exact le_rfl

/-- **Fixed-order reciprocal positivity at every height does not locate zeros.**  There is an
even real polynomial with a non-real zero whose slice lifts are reciprocally totally positive of
order one at every real height where they are defined. -/
theorem exists_reciprocalTPUpTo_one_everywhere_nonreal_zero :
    ∃ P : ℂ → ℂ, (∀ z, P (-z) = P z) ∧ (∀ x : ℝ, (P x).im = 0) ∧
      (∃ z, P z = 0 ∧ z.im ≠ 0) ∧
      ∀ t : ℝ, P t ≠ 0 → ReciprocalTPUpTo 1 (fun y => evenSquareLift
        (fun σ => P (t + σ) * P (t - σ)) (-y)) := by
  refine ⟨shadowPoly, shadowPoly_neg, fun x => ?_, ⟨1 + I, shadowPoly_one_add_I, by simp⟩,
    fun t ht => reciprocalTPUpTo_one_shadowLift ht⟩
  unfold shadowPoly
  norm_cast

end

end GaloisForLFunctions.HTGeometry
