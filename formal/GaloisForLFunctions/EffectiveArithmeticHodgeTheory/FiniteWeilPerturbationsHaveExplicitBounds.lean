import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheExplicitSchedulesReachTheIndex

/-!
# Explicit two-sided motion of the complete Weil form

Applying the upper perturbation estimate in both directions bounds the
complete signed form, including both polar moments and every prime term.
The base norms in the reverse estimate are controlled explicitly.
-/

noncomputable section
open MeasureTheory
namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory
open SpacingScaleHarmonicAnalysis

/-- The reverse perturbation cost with explicit bounds on the perturbed base norms. -/
def weilPerturbationBudget (F : ℝ → ℝ) (R e V : ℝ) : ℝ :=
  weilErrBound
    (Real.sqrt (∫ u, F u ^ 2) + Real.sqrt (2 * R) * e)
    (Real.sqrt (RHTower.levyEnergy F) + Real.sqrt V)
    (|RHTower.coshHalfMoment F| + |RHTower.sinhHalfMoment F| +
      4 * R * Real.cosh (R / 2) * e) R e V

/-- A finite sup and Lipschitz error gives the stated two-sided full Weil error. -/
theorem abs_weilQuad_add_sub_le_explicit {F D : ℝ → ℝ} {R e L k : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hFR : SupportedIn R F)
    (hD : ContDiff ℝ 2 D) (hDR : SupportedIn R D) (hR : 0 ≤ R)
    (he : ∀ u, |D u| ≤ e) (hL : ∀ u v, |D u - D v| ≤ L * |u - v|)
    (hk : 1 ≤ k) :
    |weilQuad (fun u => F u + D u) - weilQuad F| ≤
      weilPerturbationBudget F R e (synthLevy R e L k) := by
  obtain ⟨hDc, hsqD, _, hLev, _, hN1⟩ := perturbation_norms hD hDR hR he hL hk
  let V := synthLevy R e L k
  have he0 : 0 ≤ e := (abs_nonneg (D 0)).trans (he 0)
  let G : ℝ → ℝ := fun u => F u + D u
  have hG : ContDiff ℝ 2 G := hF.add hD
  have hGc : HasCompactSupport G := hFc.add hDc
  have hGR : SupportedIn R G := supportedIn_add hFR hDR
  have hNDR : SupportedIn R (fun u => -D u) := fun u hu => by
    change -D u = 0
    rw [hDR u hu, neg_zero]
  have hNe : ∀ u, |-D u| ≤ e := fun u => by rw [abs_neg]; exact he u
  have hNL : ∀ u v, |-D u - -D v| ≤ L * |u - v| := by
    intro u v
    rw [show -D u - -D v = -(D u - D v) by ring, abs_neg]
    exact hL u v
  have hupper := weilQuad_add_le_of_lip hF hFc hFR hD hDR hR he hL hk
  have hlower := weilQuad_add_le_of_lip hG hGc hGR hD.neg hNDR hR hNe hNL hk
  have hcancel : (fun u => G u + -D u) = F := by funext u; dsimp only [G]; ring
  rw [hcancel] at hlower
  have hbase : weilErr F R e V ≤ weilPerturbationBudget F R e V := by
    apply weilErr_le_bound hR he0
    · have h := mul_nonneg (Real.sqrt_nonneg (2 * R)) he0
      linarith only [h]
    · have h := Real.sqrt_nonneg V
      linarith only [h]
    · have h : 0 ≤ 4 * R * Real.cosh (R / 2) * e := by positivity
      linarith only [h]
  have hpert : weilErr G R e V ≤ weilPerturbationBudget F R e V := by
    apply weilErr_le_bound hR he0
    · exact (sqrt_integral_sq_add_le hF.continuous hFc hD.continuous hDc).trans
        (add_le_add le_rfl hsqD)
    · exact (sqrt_levyEnergy_add_le hF hFc hD hDc).trans
        (add_le_add le_rfl (Real.sqrt_le_sqrt hLev))
    · have hm := moments_add_le hF.continuous hFc hD.continuous hDc hDR
      have hn := mul_le_mul_of_nonneg_left hN1
        (show 0 ≤ 2 * Real.cosh (R / 2) by positivity)
      change |RHTower.coshHalfMoment G| + |RHTower.sinhHalfMoment G| ≤ _
      nlinarith only [hm, hn]
  apply abs_le.mpr
  constructor
  · change -weilPerturbationBudget F R e V ≤ weilQuad G - weilQuad F
    linarith only [hlower, hpert]
  · change weilQuad G - weilQuad F ≤ weilPerturbationBudget F R e V
    linarith only [hupper, hbase]


/-- Polarization turns the explicit full-form error into an entry bound for
any finite real Weil family. -/
theorem norm_weilGram_add_sub_le_explicit {ι : Type*}
    (F D : ι → ℝ → ℝ) {R e L k : ℝ}
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hFR : ∀ i, SupportedIn R (F i)) (hD : ∀ i, ContDiff ℝ 2 (D i))
    (hDR : ∀ i, SupportedIn R (D i)) (hR : 0 ≤ R)
    (he : ∀ i u, |D i u| ≤ e)
    (hL : ∀ i u v, |D i u - D i v| ≤ L * |u - v|) (hk : 1 ≤ k) (i j : ι) :
    ‖ArithmeticCastelnuovoSeveri.weilGram
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (fun a => ArithmeticCastelnuovoSeveri.cx (fun u => F a u + D a u)) i j -
      ArithmeticCastelnuovoSeveri.weilGram
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (fun a => ArithmeticCastelnuovoSeveri.cx (F a)) i j‖ ≤
      (weilPerturbationBudget (fun u => F i u + F j u) R (2 * e)
          (synthLevy R (2 * e) (2 * L) k) +
        weilPerturbationBudget (fun u => F i u - F j u) R (2 * e)
          (synthLevy R (2 * e) (2 * L) k)) / 4 := by
  have hpair (s : ℝ) (hs : s = 1 ∨ s = -1) :
      |weilQuad (fun u => (F i u + s * F j u) + (D i u + s * D j u)) -
        weilQuad (fun u => F i u + s * F j u)| ≤
      weilPerturbationBudget (fun u => F i u + s * F j u) R (2 * e)
        (synthLevy R (2 * e) (2 * L) k) := by
    have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hbase : SupportedIn R (fun u => F i u + s * F j u) := fun u hu => by
      change F i u + s * F j u = 0
      rw [hFR i u hu, hFR j u hu, mul_zero, add_zero]
    have hpert : SupportedIn R (fun u => D i u + s * D j u) := fun u hu => by
      change D i u + s * D j u = 0
      rw [hDR i u hu, hDR j u hu, mul_zero, add_zero]
    apply abs_weilQuad_add_sub_le_explicit
      ((hF i).add (contDiff_const.mul (hF j)))
      (hasCompactSupport_of_vanishes hbase) hbase
      ((hD i).add (contDiff_const.mul (hD j))) hpert hR
    · intro u
      have h := abs_add_le (D i u) (s * D j u)
      rw [abs_mul, hs1, one_mul] at h
      linarith only [h, he i u, he j u]
    · intro u v
      rw [show D i u + s * D j u - (D i v + s * D j v) =
        (D i u - D i v) + s * (D j u - D j v) by ring]
      have h := abs_add_le (D i u - D i v) (s * (D j u - D j v))
      rw [abs_mul, hs1, one_mul] at h
      linarith only [h, hL i u v, hL j u v]
    · exact hk
  have hp := hpair 1 (Or.inl rfl)
  have hm := hpair (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hp hm
  have hAi : ContDiff ℝ 2 (fun u => F i u + D i u) := (hF i).add (hD i)
  have hAj : ContDiff ℝ 2 (fun u => F j u + D j u) := (hF j).add (hD j)
  have hAic := (hFc i).add (hasCompactSupport_of_vanishes (hDR i))
  have hAjc := (hFc j).add (hasCompactSupport_of_vanishes (hDR j))
  have hplus : (fun u => (F i u + D i u) + (F j u + D j u)) =
      (fun u => (F i u + F j u) + (D i u + D j u)) := by funext u; ring
  have hminus : (fun u => (F i u + D i u) - (F j u + D j u)) =
      (fun u => (F i u - F j u) + (D i u - D j u)) := by funext u; ring
  simp only [ArithmeticCastelnuovoSeveri.weilGram]
  rw [weilPair_real_eq hAi hAic hAj hAjc, weilPair_real_eq (hF i) (hFc i) (hF j) (hFc j),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hplus, hminus]
  have hid :
      (weilQuad (fun u => (F i u + F j u) + (D i u + D j u)) -
        weilQuad (fun u => (F i u - F j u) + (D i u - D j u))) / 4 -
        (weilQuad (fun u => F i u + F j u) - weilQuad (fun u => F i u - F j u)) / 4 =
      ((weilQuad (fun u => (F i u + F j u) + (D i u + D j u)) -
        weilQuad (fun u => F i u + F j u)) -
        (weilQuad (fun u => (F i u - F j u) + (D i u - D j u)) -
          weilQuad (fun u => F i u - F j u))) / 4 := by ring
  rw [hid, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
  exact (abs_sub _ _).trans (add_le_add hp hm)

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory

#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.abs_weilQuad_add_sub_le_explicit

#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.norm_weilGram_add_sub_le_explicit
