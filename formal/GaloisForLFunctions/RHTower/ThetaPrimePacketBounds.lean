import GaloisForLFunctions.RHTower.ThetaPrimeFrustratedTriangle

/-!
# Quantitative full interactions of narrow arithmetic packets

At a prime resonance the interaction is bounded by twice the actual prime
weight times physical mass. At an atom-free separation it can be made smaller
than any prescribed positive multiple of that mass. Every prime-power term
is retained in both statements.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem exists_thetaTranslatedBump_prime_bound_radius {n : ℕ} (hn : Nat.Prime n) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ eps →
      |thetaRealWeilPolar (thetaTranslatedBumpGround r hr 0)
        (thetaTranslatedBumpGround r hr (Real.log n))| ≤
      (2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n)) *
        thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr 0)) := by
  let d : ℝ := Real.log n
  let w : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n
  have hw : 0 < w := div_pos (ArithmeticFunction.vonMangoldt_pos_iff.mpr hn.isPrimePow)
    (Real.sqrt_pos.mpr (by exact_mod_cast hn.pos))
  obtain ⟨e, he, hegap, hisolate⟩ := exists_logNat_isolating_radius hn.two_le
  let E := Real.exp ((d + 1) / 2)
  have hE : 0 < E := Real.exp_pos _
  let eps := min (e / 4) (min (1 / 2 : ℝ) (w / (8 * E)))
  have heps : 0 < eps := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨eps, heps, fun r hr hreps => ?_⟩
  have hre : r ≤ e / 4 := hreps.trans (min_le_left _ _)
  have hr1 : r ≤ 1 / 2 := hreps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrw : r ≤ w / (8 * E) := hreps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hgap : screwSignThreshold < d - 2 * r := by dsimp only [d]; linarith
  let phi := thetaTranslatedBumpGround r hr 0
  let psi := thetaTranslatedBumpGround r hr d
  have hpc := compact_thetaTranslatedBumpGround r hr 0
  have hqc := compact_thetaTranslatedBumpGround r hr d
  have hps := support_thetaTranslatedBumpGround r hr 0
  have hqs := support_thetaTranslatedBumpGround r hr d
  have hm := thetaTranslatedBumpGround_mass_pos r hr 0
  have hmass : thetaGroundNormSq (thetaComplexify psi) = thetaGroundNormSq (thetaComplexify phi) :=
    thetaTranslatedBumpGround_mass r hr d
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y := by
    intro x hx y hy
    rw [hqs, Real.ball_eq_Ioo] at hx
    rw [hps, Real.ball_eq_Ioo] at hy
    linarith [hx.1, hy.2, screwSignThreshold_pos]
  have hactive : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ m : ℕ, IsPrimePow m → x - y = Real.log m → m ∈ ({n} : Finset ℕ) := by
    intro x hx y hy m hmp hlog
    rw [hqs, Real.ball_eq_Ioo] at hx
    rw [hps, Real.ball_eq_Ioo] at hy
    apply Finset.mem_singleton.mpr
    apply hisolate m (by have := IsPrimePow.one_lt hmp; omega)
    rw [← hlog, abs_lt]
    change -e < x - y - d ∧ x - y - d < e
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have ha := abs_thetaPrimeScalingCross_difference_le_finite_mass phi psi hpc {n} hsep hactive
  rw [Finset.sum_singleton, hmass] at ha
  have hc := abs_thetaGammaPolarGroundCrossPairing_balls_le phi psi hpc hqc hr.le
    hps.subset hqs.subset (by simpa only [sub_zero] using hgap.le)
  rw [sub_zero, hmass] at hc
  have hcoef : 2 * (Real.exp ((d + 2 * r) / 2) * r) ≤ w / 4 := by
    have he' : Real.exp ((d + 2 * r) / 2) ≤ E := Real.exp_le_exp.mpr (by linarith)
    have hprod := mul_le_mul_of_nonneg_right he' hr.le
    have hwr := (le_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < 8) hE)).mp hrw
    nlinarith only [hprod, hwr]
  have hb : |thetaGammaPolarGroundCrossPairing phi psi| ≤
      (w / 4) * thetaGroundNormSq (thetaComplexify phi) := by
    nlinarith only [hc, mul_le_mul_of_nonneg_right hcoef hm.le]
  have hdifference := thetaRealArithmeticQuadratic_ordered_prime_correction phi psi hsep
  obtain ⟨hal, hau⟩ := abs_le.mp ha
  obtain ⟨hcl, hcu⟩ := abs_le.mp hb
  change |thetaRealWeilPolar phi psi| ≤ (2 * w) * thetaGroundNormSq (thetaComplexify phi)
  unfold thetaRealWeilPolar
  rw [abs_le]
  constructor <;> nlinarith only [hdifference, hal, hau, hcl, hcu, mul_pos hw hm]

theorem exists_thetaTranslatedBump_atomFree_bound_radius {c d eta : ℝ}
    (hgap : screwSignThreshold < d - c)
    (hatom : ∀ n : ℕ, 2 ≤ n → d - c ≠ Real.log n) (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ eps →
      |thetaRealWeilPolar (thetaTranslatedBumpGround r hr c)
        (thetaTranslatedBumpGround r hr d)| ≤
      eta * thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr 0)) := by
  obtain ⟨e, he, hefree⟩ := exists_atomFree_radius hatom
  let E := Real.exp ((d - c + 1) / 2)
  have hE : 0 < E := Real.exp_pos _
  let eps := min (e / 4) (min ((d - c - screwSignThreshold) / 4)
    (min (1 / 2 : ℝ) (eta / (2 * E))))
  have heps : 0 < eps := lt_min (by positivity)
    (lt_min (by linarith) (lt_min (by positivity) (by positivity)))
  refine ⟨eps, heps, fun r hr hreps => ?_⟩
  have hre : r ≤ e / 4 := hreps.trans (min_le_left _ _)
  have hrg : r ≤ (d - c - screwSignThreshold) / 4 :=
    hreps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr1 : r ≤ 1 / 2 := hreps.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hrEta : r ≤ eta / (2 * E) := hreps.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let phi := thetaTranslatedBumpGround r hr c
  let psi := thetaTranslatedBumpGround r hr d
  have hps := support_thetaTranslatedBumpGround r hr c
  have hqs := support_thetaTranslatedBumpGround r hr d
  have hgapr : screwSignThreshold < d - c - 2 * r := by linarith
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y := by
    intro x hx y hy
    rw [hqs, Real.ball_eq_Ioo] at hx
    rw [hps, Real.ball_eq_Ioo] at hy
    linarith [hx.1, hy.2, screwSignThreshold_pos]
  have hfree : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n := by
    intro x hx y hy
    rw [hqs, Real.ball_eq_Ioo] at hx
    rw [hps, Real.ball_eq_Ioo] at hy
    apply hefree (x - y)
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hpolar : thetaRealWeilPolar phi psi = thetaGammaPolarGroundCrossPairing phi psi := by
    unfold thetaRealWeilPolar
    rw [thetaRealArithmeticQuadratic_disjoint_polarization phi psi hsep hfree]
    ring
  have hc := abs_thetaGammaPolarGroundCrossPairing_balls_le phi psi
    (compact_thetaTranslatedBumpGround r hr c) (compact_thetaTranslatedBumpGround r hr d) hr.le
    hps.subset hqs.subset hgapr.le
  rw [thetaTranslatedBumpGround_mass r hr c, thetaTranslatedBumpGround_mass r hr d] at hc
  have hcoef : 2 * (Real.exp ((d - c + 2 * r) / 2) * r) ≤ eta := by
    have he' : Real.exp ((d - c + 2 * r) / 2) ≤ E := Real.exp_le_exp.mpr (by linarith)
    have hprod := mul_le_mul_of_nonneg_right he' hr.le
    have hsmall := (le_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < 2) hE)).mp hrEta
    nlinarith only [hprod, hsmall]
  change |thetaRealWeilPolar phi psi| ≤ _
  rw [hpolar]
  nlinarith only [hc, mul_le_mul_of_nonneg_right hcoef
    (thetaTranslatedBumpGround_mass_pos r hr 0).le]

end RHTower
