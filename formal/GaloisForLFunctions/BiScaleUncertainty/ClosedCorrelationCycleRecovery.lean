import GaloisForLFunctions.BiScaleUncertainty.SeparatedCopyCycleCharge
import GaloisForLFunctions.BiScaleUncertainty.SignedDyadicCollarPartition

/-!
# Recovery from all closed correlation products

Two-edge products determine correlation magnitudes. Positive mass and
continuity choose a common positive sign near the origin. A closed cycle of
many equal small increments then recovers the signed correlation at any lag.
Thus the entire hierarchy determines polar balance, including zero sources.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SeparatedCycle
set_option autoImplicit false

private theorem autocorr_eq_zero_of_mass_zero (f : C_c(ℝ, ℝ))
    (h0 : autocorr f 0 = 0) (x : ℝ) : autocorr f x = 0 := by
  have h := abs_autocorr_le_zero f.hasCompactSupport f.continuous x
  rw [h0] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- The complete hierarchy of closed products is equivalent to the signed autocorrelation. -/
theorem closedProduct_eq_iff_autocorr_eq (f g : C_c(ℝ, ℝ)) :
    closedProduct f = closedProduct g ↔ autocorr f = autocorr g := by
  constructor
  · intro he
    have hm : autocorr f 0 = autocorr g 0 := by
      simpa [closedProduct, rawProduct] using congrFun he [0]
    have hsq (x : ℝ) : autocorr f x ^ 2 = autocorr g x ^ 2 := by
      simpa [closedProduct, rawProduct, autocorr_neg, pow_two] using congrFun he [x, -x]
    funext x
    by_cases h0 : autocorr f 0 = 0
    · have hg0 : autocorr g 0 = 0 := hm.symm.trans h0
      rw [autocorr_eq_zero_of_mass_zero f h0, autocorr_eq_zero_of_mass_zero g hg0]
    · have hR : 0 < autocorr f 0 :=
        lt_of_le_of_ne (autocorr_zero_nonneg f) (Ne.symm h0)
      have hc : ContinuousAt (fun y : ℝ => autocorr f y + autocorr g y) 0 :=
        ((continuous_autocorr_compact f).add (continuous_autocorr_compact g)).continuousAt
      have hp0 : 0 < autocorr f 0 + autocorr g 0 := by linarith
      obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc _ hp0
      obtain ⟨n, hn⟩ := exists_nat_gt (|x| / δ + 1)
      have hn0r : 0 < (n : ℝ) := by
        have hd := div_nonneg (abs_nonneg x) hδ.le
        linarith
      have hnne : (n : ℝ) ≠ 0 := hn0r.ne'
      have hxsmall : |x / (n : ℝ)| < δ := by
        rw [abs_div, abs_of_pos hn0r]
        apply (div_lt_iff₀ hn0r).mpr
        have hlt : |x| / δ < (n : ℝ) := by linarith
        simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hlt
      have hsumpos : 0 < autocorr f (x / n) + autocorr g (x / n) := by
        have hh := hclose (x := x / n) (by simpa only [Real.dist_eq, sub_zero] using hxsmall)
        rw [Real.dist_eq] at hh
        have hb := (abs_lt.mp hh).1
        linarith
      have hlocal : autocorr f (x / n) = autocorr g (x / n) := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq (x / n)) with hh | hh
        · exact hh
        · exfalso
          linarith
      have hgpos : 0 < autocorr g (x / n) := by linarith
      have hclosed : ((-x) :: List.replicate n (x / n)).sum = 0 := by
        simp only [List.sum_cons, List.sum_replicate, nsmul_eq_mul]
        field_simp [hnne]
        ring
      have hprod := congrFun he ((-x) :: List.replicate n (x / n))
      simp only [closedProduct, hclosed, if_true, rawProduct, List.map_cons,
        List.map_replicate, List.prod_cons, List.prod_replicate, autocorr_neg] at hprod
      rw [hlocal] at hprod
      exact mul_right_cancel₀ (pow_ne_zero n hgpos.ne') hprod
  · intro he
    funext l
    simp only [closedProduct, rawProduct, he]

/-- Equality at every finite order is complete; no uniform order is asserted. -/
theorem all_shortData_eq_iff_autocorr_eq (f g : C_c(ℝ, ℝ)) :
    (∀ m : ℕ, shortData f m = shortData g m) ↔ autocorr f = autocorr g := by
  rw [← closedProduct_eq_iff_autocorr_eq f g]
  constructor
  · intro h
    funext l
    exact congrFun (h l.length) ⟨l, le_rfl⟩
  · intro h m
    funext l
    exact congrFun h l.1

/-- Choose a source realizing the supplied closed data; unrealizable data are assigned zero. -/
def polarRecovery (p : List ℝ → ℝ) : ℝ := by
  classical
  exact if hp : ∃ f : C_c(ℝ, ℝ), closedProduct f = p then
    normalizedPolarMoment hp.choose else 0

/-- The choice of realizing source is immaterial: its signed correlation is already determined. -/
theorem polarRecovery_closedProduct (f : C_c(ℝ, ℝ)) :
    polarRecovery (closedProduct f) = normalizedPolarMoment f := by
  classical
  have hp : ∃ g : C_c(ℝ, ℝ), closedProduct g = closedProduct f := ⟨f, rfl⟩
  rw [polarRecovery, dif_pos hp]
  have he := (closedProduct_eq_iff_autocorr_eq hp.choose f).mp hp.choose_spec
  simp only [normalizedPolarMoment, he]

end GaloisForLFunctions.BiScaleUncertainty.SeparatedCycle
