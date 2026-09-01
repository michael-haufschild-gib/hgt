import GaloisForLFunctions.HTGeometry.FractionDegreeExtension
import GaloisForLFunctions.HTGeometry.WeightedDegreeSupport
import GaloisForLFunctions.HTGeometry.ProductLawFractionModel

/-!
# The weighted degree on the rational cascade model

The rational model of a cascade is the fraction field of the polynomial ring on the states, so the
weighted degree extends to it and its coordinate derivations are the extensions of the partial
derivatives.  A coordinate derivation therefore loses at least the weight of its coordinate on every
rational function: writing `x = a/b`, the quotient rule gives numerator `∂_k a · b − a · ∂_k b`, and
each of its two terms already loses the weight.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- The weighted degree on the rational cascade model. -/
def cascadeDeg (w : ℕ → ℕ) : CascadeField → WithBot ℤ := fracDeg (wdeg w)

theorem isDegree_cascadeDeg (w : ℕ → ℕ) : IsDegree (cascadeDeg w) :=
  isDegree_fracDeg (isDegree_wdeg w)

theorem cascadeDeg_algebraMap (w : ℕ → ℕ) (p : MvPolynomial ℕ ℂ) :
    cascadeDeg w (algebraMap (MvPolynomial ℕ ℂ) CascadeField p) = wdeg w p :=
  fracDeg_algebraMap (isDegree_wdeg w) p

@[simp] theorem cascadeDeg_fx (w : ℕ → ℕ) (k : ℕ) :
    cascadeDeg w (fx k) = ((w k : ℤ) : WithBot ℤ) := by
  rw [fx, cascadeDeg_algebraMap, wdeg_X]

/-- **The coordinate derivation of the rational model extends the partial derivative.** -/
theorem fpderiv_algebraMap (k : ℕ) (p : MvPolynomial ℕ ℂ) :
    fpderiv k (algebraMap (MvPolynomial ℕ ℂ) CascadeField p)
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (pderiv k p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r =>
      have h : (algebraMap (MvPolynomial ℕ ℂ) CascadeField) (MvPolynomial.C r)
          = algebraMap ℂ CascadeField r := by
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      rw [h, Derivation.map_algebraMap, MvPolynomial.pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      have hXi : (algebraMap (MvPolynomial ℕ ℂ) CascadeField) (MvPolynomial.X i) = fx i := rfl
      have hL : (pderiv k) (p * MvPolynomial.X i)
          = p * (pderiv k) (MvPolynomial.X i) + MvPolynomial.X i * (pderiv k) p := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
      rw [map_mul, hXi, Derivation.leibniz, hp, hL, map_add, map_mul, map_mul, hXi]
      simp only [smul_eq_mul]
      by_cases hik : i = k
      · subst hik
        rw [fpderiv_fx_self, MvPolynomial.pderiv_X_self, map_one]
      · rw [fpderiv_fx_of_ne hik, MvPolynomial.pderiv_X_of_ne hik, map_zero]

/-- **A coordinate derivation loses at least the weight of its coordinate.** -/
theorem cascadeDeg_fpderiv_add_le (w : ℕ → ℕ) (k : ℕ) (x : CascadeField) :
    cascadeDeg w (fpderiv k x) + ((w k : ℤ) : WithBot ℤ) ≤ cascadeDeg w x := by
  classical
  have hdC := isDegree_cascadeDeg w
  have hdW := isDegree_wdeg w
  by_cases hdx : fpderiv k x = 0
  · rw [hdx, (hdC.eq_bot 0).mpr rfl, WithBot.bot_add]
    exact bot_le
  have hx : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hdx
    exact hdx rfl
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := MvPolynomial ℕ ℂ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (MvPolynomial ℕ ℂ) CascadeField b ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero hb0
  have hxrep : x * algebraMap (MvPolynomial ℕ ℂ) CascadeField b
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField a := by
    rw [← hab]
    field_simp
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hxrep
    rcases mul_eq_zero.mp hxrep with h | h
    · exact hx h
    · exact hbK h
  set N : MvPolynomial ℕ ℂ := pderiv k a * b - a * pderiv k b with hN
  have hquot : fpderiv k x * algebraMap (MvPolynomial ℕ ℂ) CascadeField (b * b)
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField N := by
    have hlei := (fpderiv k).leibniz x (algebraMap (MvPolynomial ℕ ℂ) CascadeField b)
    rw [hxrep, fpderiv_algebraMap, fpderiv_algebraMap] at hlei
    simp only [smul_eq_mul] at hlei
    have hstep : algebraMap (MvPolynomial ℕ ℂ) CascadeField b * fpderiv k x
        = algebraMap (MvPolynomial ℕ ℂ) CascadeField (pderiv k a)
          - x * algebraMap (MvPolynomial ℕ ℂ) CascadeField (pderiv k b) := by
      linear_combination -hlei
    calc fpderiv k x * algebraMap (MvPolynomial ℕ ℂ) CascadeField (b * b)
        = (algebraMap (MvPolynomial ℕ ℂ) CascadeField b * fpderiv k x)
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField b := by rw [map_mul]; ring
      _ = (algebraMap (MvPolynomial ℕ ℂ) CascadeField (pderiv k a)
            - x * algebraMap (MvPolynomial ℕ ℂ) CascadeField (pderiv k b))
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField b := by rw [hstep]
      _ = algebraMap (MvPolynomial ℕ ℂ) CascadeField (pderiv k a)
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField b
          - (x * algebraMap (MvPolynomial ℕ ℂ) CascadeField b)
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField (pderiv k b) := by ring
      _ = algebraMap (MvPolynomial ℕ ℂ) CascadeField (pderiv k a)
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField b
          - algebraMap (MvPolynomial ℕ ℂ) CascadeField a
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField (pderiv k b) := by rw [hxrep]
      _ = algebraMap (MvPolynomial ℕ ℂ) CascadeField N := by
            rw [hN, map_sub, map_mul, map_mul]
  have hNne : N ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hquot
    rcases mul_eq_zero.mp hquot with h | h
    · exact hdx h
    · exact (algebraMap_ne_zero_of_ne_zero (mul_ne_zero hb0 hb0)) h
  -- the weighted-degree estimate on the numerator
  have hbound : wdeg w N + ((w k : ℤ) : WithBot ℤ) ≤ wdeg w a + wdeg w b := by
    have hsplit : wdeg w N ≤ max (wdeg w (pderiv k a * b)) (wdeg w (a * pderiv k b)) := by
      have h := hdW.map_add_le (pderiv k a * b) (-(a * pderiv k b))
      rw [hdW.map_neg] at h
      simpa [hN, sub_eq_add_neg] using h
    have h1 : wdeg w (pderiv k a * b) + ((w k : ℤ) : WithBot ℤ) ≤ wdeg w a + wdeg w b := by
      rw [hdW.map_mul]
      have := wdeg_pderiv_add_le w k a
      calc wdeg w (pderiv k a) + wdeg w b + ((w k : ℤ) : WithBot ℤ)
          = (wdeg w (pderiv k a) + ((w k : ℤ) : WithBot ℤ)) + wdeg w b := add_right_comm _ _ _
        _ ≤ wdeg w a + wdeg w b := add_le_add this le_rfl
    have h2 : wdeg w (a * pderiv k b) + ((w k : ℤ) : WithBot ℤ) ≤ wdeg w a + wdeg w b := by
      rw [hdW.map_mul]
      have := wdeg_pderiv_add_le w k b
      calc wdeg w a + wdeg w (pderiv k b) + ((w k : ℤ) : WithBot ℤ)
          = wdeg w a + (wdeg w (pderiv k b) + ((w k : ℤ) : WithBot ℤ)) := add_assoc _ _ _
        _ ≤ wdeg w a + wdeg w b := add_le_add le_rfl this
    refine le_trans (add_le_add hsplit le_rfl) ?_
    rcases le_total (wdeg w (pderiv k a * b)) (wdeg w (a * pderiv k b)) with hc | hc
    · rw [max_eq_right hc]; exact h2
    · rw [max_eq_left hc]; exact h1
  -- pass to integers
  have hZ : degZ (wdeg w) N + (w k : ℤ) ≤ degZ (wdeg w) a + degZ (wdeg w) b := by
    rw [← coe_degZ hdW hNne, ← coe_degZ hdW ha0, ← coe_degZ hdW hb0] at hbound
    exact_mod_cast hbound
  have hbb : degZ (wdeg w) (b * b) = degZ (wdeg w) b + degZ (wdeg w) b := degZ_mul hdW hb0 hb0
  simp only [cascadeDeg]
  rw [fracDeg_eq hdW hNne (mul_ne_zero hb0 hb0) hquot, fracDeg_eq hdW ha0 hb0 hxrep, hbb]
  exact_mod_cast (by omega : degZ (wdeg w) N - (degZ (wdeg w) b + degZ (wdeg w) b) + (w k : ℤ)
    ≤ degZ (wdeg w) a - degZ (wdeg w) b)

end GaloisForLFunctions.HTGeometry

end
