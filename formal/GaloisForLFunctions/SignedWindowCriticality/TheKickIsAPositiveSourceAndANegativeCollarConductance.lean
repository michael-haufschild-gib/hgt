import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The kick is a positive source and a negative collar conductance

On an odd test `F` the correlation at lag `ℓ` is an anti-diagonal sum,
`c_F(ℓ) = ∫F(y)F(y + ℓ)dy = −∫F(s)F(ℓ − s)ds` (`integral_mul_shift_eq_neg_antidiagonal`): every pair
at distance `ℓ` is read through the reflection `τs = ℓ − s`. When the support radius `a` of `F` is
at most `ℓ`, only pairs with `s, ℓ − s ∈ [0, a]` contribute, so the kick `−2w c_F(ℓ)` of a new prime
power is carried by the collar `[ℓ − a, a]` of the half-window.

* **Decomposition** (`kick_eq_source_sub_collarConductance`). In any gauge `F = hu`,
  `−2w c_F(ℓ) = 2w∫h(s)h(τs)u(s)² ds − w∫h(s)h(τs)(u(s) − u(τs))² ds`: a source of density
  `2w h h∘τ` and a conductance `−w h h∘τ` along the anti-diagonal.
* **Sectors of the collar reflection.** On `τ`-symmetric profiles the conductance term vanishes and
  the kick is the pure source (`kick_eq_source_of_symmetric`); on `τ`-antisymmetric profiles it is
  minus the source (`kick_eq_neg_source_of_antisymmetric`).
* **Positivity on positive profiles** (`kick_nonneg_of_nonneg_of_support`). If `F ≥ 0` on `[0, ∞)`
  and `F` vanishes beyond `a ≤ ℓ`, the kick is nonnegative: the newest prime power lifts every
  positive odd profile, in particular the Perron state of a Z-type frozen odd form.

For a positive gauge the conductance `−w h h∘τ` is the frustration of the odd sector at the stage;
it must be dominated by the Kron reduction of the archimedean light cone onto the collar.
-/

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

/-- **The correlation of an odd test is an anti-diagonal sum.** -/
theorem integral_mul_shift_eq_neg_antidiagonal {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x)
    (ℓ : ℝ) : (∫ y, F y * F (y + ℓ)) = -∫ s, F s * F (ℓ - s) := by
  have h := integral_neg_eq_self (μ := volume) (fun y => F y * F (y + ℓ))
  rw [← h, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun s => by
    simp only [hodd, show -s + ℓ = ℓ - s by ring]; ring)

variable {h u : ℝ → ℝ}

/-- **The kick in a gauge.** For an odd test `F = hu` with `h, u` continuous and `h` compactly
supported, `−2w c_F(ℓ) = 2w∫h h∘τ u² − w∫h h∘τ (u − u∘τ)²`, `τs = ℓ − s`. -/
theorem kick_eq_source_sub_collarConductance (hh : Continuous h) (hhc : HasCompactSupport h)
    (hu : Continuous u) (hodd : ∀ x, h (-x) * u (-x) = -(h x * u x)) (w ℓ : ℝ) :
    -2 * w * (∫ y, h y * u y * (h (y + ℓ) * u (y + ℓ))) =
      2 * w * (∫ s, h s * h (ℓ - s) * u s ^ 2) -
        w * ∫ s, h s * h (ℓ - s) * (u s - u (ℓ - s)) ^ 2 := by
  have hcorr := integral_mul_shift_eq_neg_antidiagonal (F := fun x => h x * u x) hodd ℓ
  have hτ : Continuous fun s => ℓ - s := continuous_const.sub continuous_id
  have hcs : HasCompactSupport fun s => h s * h (ℓ - s) := hhc.mul_right
  have hP : Integrable fun s => h s * h (ℓ - s) * u s ^ 2 :=
    ((hh.mul (hh.comp hτ)).mul (hu.pow 2)).integrable_of_hasCompactSupport hcs.mul_right
  have hQ : Integrable fun s => h s * h (ℓ - s) * u (ℓ - s) ^ 2 :=
    ((hh.mul (hh.comp hτ)).mul ((hu.comp hτ).pow 2)).integrable_of_hasCompactSupport hcs.mul_right
  have hX : Integrable fun s => h s * h (ℓ - s) * (u s * u (ℓ - s)) :=
    ((hh.mul (hh.comp hτ)).mul (hu.mul (hu.comp hτ))).integrable_of_hasCompactSupport
      hcs.mul_right
  have hQP : (∫ s, h s * h (ℓ - s) * u (ℓ - s) ^ 2) = ∫ s, h s * h (ℓ - s) * u s ^ 2 := by
    have := integral_sub_left_eq_self (μ := volume) (fun s => h s * h (ℓ - s) * u s ^ 2) ℓ
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by
      simp only [sub_sub_cancel]; ring)
  have hsq : (∫ s, h s * h (ℓ - s) * (u s - u (ℓ - s)) ^ 2) =
      (∫ s, h s * h (ℓ - s) * u s ^ 2) - 2 * (∫ s, h s * h (ℓ - s) * (u s * u (ℓ - s))) +
        ∫ s, h s * h (ℓ - s) * u (ℓ - s) ^ 2 := by
    have h1 : (∫ s, ((h s * h (ℓ - s) * u s ^ 2 - 2 * (h s * h (ℓ - s) * (u s * u (ℓ - s)))) +
        h s * h (ℓ - s) * u (ℓ - s) ^ 2)) =
        (∫ s, (h s * h (ℓ - s) * u s ^ 2 - 2 * (h s * h (ℓ - s) * (u s * u (ℓ - s))))) +
          ∫ s, h s * h (ℓ - s) * u (ℓ - s) ^ 2 :=
      integral_add (hP.sub (hX.const_mul _)) hQ
    have h2 : (∫ s, (h s * h (ℓ - s) * u s ^ 2 - 2 * (h s * h (ℓ - s) * (u s * u (ℓ - s))))) =
        (∫ s, h s * h (ℓ - s) * u s ^ 2) - ∫ s, 2 * (h s * h (ℓ - s) * (u s * u (ℓ - s))) :=
      integral_sub hP (hX.const_mul _)
    rw [integral_const_mul] at h2
    rw [← h2, ← h1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by simp only; ring)
  have hFX : (∫ s, h s * u s * (h (ℓ - s) * u (ℓ - s))) =
      ∫ s, h s * h (ℓ - s) * (u s * u (ℓ - s)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun s => by simp only; ring)
  rw [hcorr, hFX, hsq, hQP]
  ring

/-- On `τ`-symmetric profiles the kick is the pure source `2w∫h h∘τ u²`. -/
theorem kick_eq_source_of_symmetric (hh : Continuous h) (hhc : HasCompactSupport h)
    (hu : Continuous u) (hodd : ∀ x, h (-x) * u (-x) = -(h x * u x)) {w ℓ : ℝ}
    (hsym : ∀ s, u (ℓ - s) = u s) :
    -2 * w * (∫ y, h y * u y * (h (y + ℓ) * u (y + ℓ))) =
      2 * w * ∫ s, h s * h (ℓ - s) * u s ^ 2 := by
  rw [kick_eq_source_sub_collarConductance hh hhc hu hodd w ℓ]
  simp [hsym]

/-- On `τ`-antisymmetric profiles the kick is minus the source. -/
theorem kick_eq_neg_source_of_antisymmetric (hh : Continuous h) (hhc : HasCompactSupport h)
    (hu : Continuous u) (hodd : ∀ x, h (-x) * u (-x) = -(h x * u x)) {w ℓ : ℝ}
    (hanti : ∀ s, u (ℓ - s) = -u s) :
    -2 * w * (∫ y, h y * u y * (h (y + ℓ) * u (y + ℓ))) =
      -(2 * w * ∫ s, h s * h (ℓ - s) * u s ^ 2) := by
  rw [kick_eq_source_sub_collarConductance hh hhc hu hodd w ℓ]
  have : (∫ s, h s * h (ℓ - s) * (u s - u (ℓ - s)) ^ 2) =
      4 * ∫ s, h s * h (ℓ - s) * u s ^ 2 := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by simp only [hanti]; ring)
  rw [this]; ring

/-- **The kick lifts every positive odd profile.** If the odd test `F` is nonnegative on `[0, ∞)`
and vanishes beyond `a ≤ ℓ`, then `−2w c_F(ℓ) ≥ 0` for `w ≥ 0`. -/
theorem kick_nonneg_of_nonneg_of_support {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x)
    (hF0 : ∀ s, 0 ≤ s → 0 ≤ F s) {a ℓ w : ℝ} (hsupp : ∀ s, a < |s| → F s = 0) (haℓ : a ≤ ℓ)
    (hw : 0 ≤ w) : 0 ≤ -2 * w * ∫ y, F y * F (y + ℓ) := by
  rw [integral_mul_shift_eq_neg_antidiagonal hodd ℓ]
  have hpt : ∀ s, 0 ≤ F s * F (ℓ - s) := by
    intro s
    by_cases hs : s < 0
    · by_cases hsa : a < |s|
      · rw [hsupp s hsa, zero_mul]
      · have hsa' : |s| ≤ a := not_lt.mp hsa
        have hs0 := abs_nonneg s
        have : a < |ℓ - s| := by
          rw [abs_of_pos (by linarith)]
          linarith
        rw [hsupp _ this, mul_zero]
    · by_cases hsl : ℓ < s
      · have : a < |s| := by rw [abs_of_nonneg (not_lt.mp hs)]; linarith
        rw [hsupp s this, zero_mul]
      · exact mul_nonneg (hF0 s (not_lt.mp hs)) (hF0 _ (by linarith [not_lt.mp hsl]))
  have hI : 0 ≤ ∫ s, F s * F (ℓ - s) := integral_nonneg hpt
  nlinarith

end GaloisForLFunctions.SignedWindowCriticality

end
