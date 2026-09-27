import GaloisForLFunctions.RHTower.ThetaPrimeFrustratedTriangle

/-!
# Shape-independent bounds on arithmetic source interactions

Small support balls control the complete coupling of arbitrary real smooth
profiles. Neither nonnegativity, equal mass, nor a fixed bump shape is needed.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem exists_thetaPrime_island_pair_bound {n : ℕ} (hn : Nat.Prime n) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (r : ℝ), 0 < r → r ≤ eps →
      ∀ (phi psi : 𝓢(ℝ, ℝ)), HasCompactSupport phi → HasCompactSupport psi →
        Function.support phi ⊆ Metric.ball 0 r →
        Function.support psi ⊆ Metric.ball (Real.log n) r →
        |thetaRealWeilPolar phi psi| ≤
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
            (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
  let d : ℝ := Real.log n
  let w : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n
  have hw : 0 < w := div_pos (ArithmeticFunction.vonMangoldt_pos_iff.mpr hn.isPrimePow)
    (Real.sqrt_pos.mpr (by exact_mod_cast hn.pos))
  obtain ⟨e, he, hegap, hisolate⟩ := exists_logNat_isolating_radius hn.two_le
  let E := Real.exp ((d + 1) / 2)
  have hE : 0 < E := Real.exp_pos _
  let eps := min (e / 4) (min (1 / 2 : ℝ) (w / (8 * E)))
  have heps : 0 < eps := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨eps, heps, fun r hr hreps phi psi hpc hqc hp hq => ?_⟩
  have hre : r ≤ e / 4 := hreps.trans (min_le_left _ _)
  have hr1 : r ≤ 1 / 2 := hreps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrw : r ≤ w / (8 * E) := hreps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hgap : screwSignThreshold < d - 2 * r := by dsimp only [d]; linarith
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y := by
    intro x hx y hy
    have hx' := hq hx
    have hy' := hp hy
    rw [Real.ball_eq_Ioo] at hx' hy'
    linarith [hx'.1, hy'.2, screwSignThreshold_pos]
  have hactive : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ m : ℕ, IsPrimePow m → x - y = Real.log m → m ∈ ({n} : Finset ℕ) := by
    intro x hx y hy m hmp hlog
    have hx' := hq hx
    have hy' := hp hy
    rw [Real.ball_eq_Ioo] at hx' hy'
    apply Finset.mem_singleton.mpr
    apply hisolate m (by have := IsPrimePow.one_lt hmp; omega)
    rw [← hlog, abs_lt]
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  have ha := abs_thetaPrimeScalingCross_difference_le_finite_mass phi psi hpc {n} hsep hactive
  rw [Finset.sum_singleton] at ha
  have hc := abs_thetaGammaPolarGroundCrossPairing_balls_le phi psi hpc hqc hr.le hp hq
    (by simpa only [sub_zero] using hgap.le)
  rw [sub_zero] at hc
  have hcoef : Real.exp ((d + 2 * r) / 2) * r ≤ w / 8 := by
    have he' : Real.exp ((d + 2 * r) / 2) ≤ E := Real.exp_le_exp.mpr (by linarith)
    have hprod := mul_le_mul_of_nonneg_right he' hr.le
    have hwr := (le_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < 8) hE)).mp hrw
    nlinarith only [hprod, hwr]
  have hm := add_nonneg (thetaGroundNormSq_nonneg (thetaComplexify phi))
    (thetaGroundNormSq_nonneg (thetaComplexify psi))
  have hb : |thetaGammaPolarGroundCrossPairing phi psi| ≤
      (w / 8) * (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) :=
    hc.trans (mul_le_mul_of_nonneg_right hcoef hm)
  have hdifference := thetaRealArithmeticQuadratic_ordered_prime_correction phi psi hsep
  obtain ⟨hal, hau⟩ := abs_le.mp ha
  obtain ⟨hcl, hcu⟩ := abs_le.mp hb
  unfold thetaRealWeilPolar
  rw [abs_le]
  constructor <;> nlinarith only [hdifference, hal, hau, hcl, hcu, mul_nonneg hw.le hm]

theorem exists_thetaAtomFree_island_pair_bound {c d eta : ℝ}
    (hgap : screwSignThreshold < d - c)
    (hatom : ∀ n : ℕ, 2 ≤ n → d - c ≠ Real.log n) (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ r : ℝ, 0 < r → r ≤ eps →
      ∀ (phi psi : 𝓢(ℝ, ℝ)), HasCompactSupport phi → HasCompactSupport psi →
        Function.support phi ⊆ Metric.ball c r → Function.support psi ⊆ Metric.ball d r →
        |thetaRealWeilPolar phi psi| ≤
          eta * (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
  obtain ⟨e, he, hefree⟩ := exists_atomFree_radius hatom
  let E := Real.exp ((d - c + 1) / 2)
  have hE : 0 < E := Real.exp_pos _
  let eps := min (e / 4) (min ((d - c - screwSignThreshold) / 4)
    (min (1 / 2 : ℝ) (eta / (2 * E))))
  have heps : 0 < eps := lt_min (by positivity)
    (lt_min (by linarith) (lt_min (by positivity) (by positivity)))
  refine ⟨eps, heps, fun r hr hreps phi psi hpc hqc hp hq => ?_⟩
  have hre : r ≤ e / 4 := hreps.trans (min_le_left _ _)
  have hrg : r ≤ (d - c - screwSignThreshold) / 4 :=
    hreps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr1 : r ≤ 1 / 2 := hreps.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hrEta : r ≤ eta / (2 * E) := hreps.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hgapr : screwSignThreshold < d - c - 2 * r := by linarith
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y := by
    intro x hx y hy
    have hx' := hq hx
    have hy' := hp hy
    rw [Real.ball_eq_Ioo] at hx' hy'
    linarith [hx'.1, hy'.2, screwSignThreshold_pos]
  have hfree : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n := by
    intro x hx y hy
    have hx' := hq hx
    have hy' := hp hy
    rw [Real.ball_eq_Ioo] at hx' hy'
    apply hefree (x - y)
    rw [abs_lt]
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  have hpolar : thetaRealWeilPolar phi psi = thetaGammaPolarGroundCrossPairing phi psi := by
    unfold thetaRealWeilPolar
    rw [thetaRealArithmeticQuadratic_disjoint_polarization phi psi hsep hfree]
    ring
  have hc := abs_thetaGammaPolarGroundCrossPairing_balls_le phi psi hpc hqc hr.le hp hq hgapr.le
  have hcoef : Real.exp ((d - c + 2 * r) / 2) * r ≤ eta := by
    have he' : Real.exp ((d - c + 2 * r) / 2) ≤ E := Real.exp_le_exp.mpr (by linarith)
    have hprod := mul_le_mul_of_nonneg_right he' hr.le
    have hsmall := (le_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < 2) hE)).mp hrEta
    nlinarith only [hprod, hsmall, heta]
  rw [hpolar]
  exact hc.trans (mul_le_mul_of_nonneg_right hcoef
    (add_nonneg (thetaGroundNormSq_nonneg _) (thetaGroundNormSq_nonneg _)))

end RHTower
