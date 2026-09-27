import GaloisForLFunctions.RHTower.ThetaTranslatedBumpPackets
import GaloisForLFunctions.RHTower.ThetaIsolatedPrimeAtomBounds
import GaloisForLFunctions.RHTower.ThetaFarPositiveInterference

/-!
# Three genuine arithmetic couplings with incompatible minimizing signs

Equal physical bumps at zero and two prime logarithms have two negative
resonant couplings. The ratio of distinct primes is not an integer; the third
coupling can therefore be made atom-free and strictly positive. All couplings
belong to the full Weil quadratic, with every prime-power term retained.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

def thetaRealWeilPolar (phi psi : 𝓢(ℝ, ℝ)) : ℝ :=
  (thetaRealArithmeticQuadratic (phi + psi) - thetaRealArithmeticQuadratic (phi - psi)) / 4

/-- Every actual prime gives a negative full coupling at all sufficiently narrow radii. -/
theorem exists_thetaTranslatedBump_prime_negative_radius {n : ℕ} (hprime : Nat.Prime n) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ eps →
      thetaRealWeilPolar (thetaTranslatedBumpGround r hr 0)
        (thetaTranslatedBumpGround r hr (Real.log n)) < 0 := by
  let d : ℝ := Real.log n
  let w : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n
  have hw : 0 < w := div_pos (ArithmeticFunction.vonMangoldt_pos_iff.mpr hprime.isPrimePow)
    (Real.sqrt_pos.mpr (by exact_mod_cast hprime.pos))
  obtain ⟨e, he, hegap, hisolate⟩ := exists_logNat_isolating_radius hprime.two_le
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
  have hps : Function.support phi = Metric.ball 0 r := support_thetaTranslatedBumpGround r hr 0
  have hqs : Function.support psi = Metric.ball d r := support_thetaTranslatedBumpGround r hr d
  have hm := thetaTranslatedBumpGround_mass_pos r hr 0
  have hmasses : thetaGroundNormSq (thetaComplexify psi) = thetaGroundNormSq (thetaComplexify phi) :=
    thetaTranslatedBumpGround_mass r hr d
  have hcross : thetaGroundShiftCross phi psi d = thetaGroundNormSq (thetaComplexify phi) := by
    simpa only [sub_zero] using thetaTranslatedBumpGround_matched_cross r hr 0 d
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
  have hatom : thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
      thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi - psi)).toBoundedContinuousFunction =
      2 * w * thetaGroundNormSq (thetaComplexify phi) := by
    have h := thetaPrimeScalingCross_difference_eq_finite phi psi {n} hsep hactive
    rw [Finset.sum_singleton] at h
    change _ = 2 * w * thetaGroundShiftCross phi psi d at h
    rwa [hcross] at h
  have hdifference := thetaRealArithmeticQuadratic_ordered_prime_correction phi psi hsep
  rw [hatom] at hdifference
  have hcontinuous := abs_thetaGammaPolarGroundCrossPairing_balls_le phi psi hpc hqc hr.le
    hps.subset hqs.subset (by simpa only [sub_zero] using hgap.le)
  rw [sub_zero, hmasses] at hcontinuous
  have hcoef : 2 * (Real.exp ((d + 2 * r) / 2) * r) ≤ w / 4 := by
    have he' : Real.exp ((d + 2 * r) / 2) ≤ E := Real.exp_le_exp.mpr (by linarith)
    have hprod := mul_le_mul_of_nonneg_right he' hr.le
    have hwr := (le_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < 8) hE)).mp hrw
    nlinarith only [hprod, hwr]
  have hbound : |thetaGammaPolarGroundCrossPairing phi psi| ≤
      (w / 4) * thetaGroundNormSq (thetaComplexify phi) := by
    have hprod := mul_le_mul_of_nonneg_right hcoef hm.le
    nlinarith only [hcontinuous, hprod]
  have hupper := (abs_le.mp hbound).2
  have hwm := mul_pos hw hm
  change thetaRealWeilPolar phi psi < 0
  unfold thetaRealWeilPolar
  nlinarith only [hdifference, hupper, hwm]

theorem prime_log_difference_ne_log_nat {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) {n : ℕ} (hn : 2 ≤ n) :
    Real.log q - Real.log p ≠ Real.log n := by
  intro h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have heq : (q : ℝ) = (n : ℝ) * p := by
    apply Real.log_injOn_pos hq0 (mul_pos hn0 hp0)
    rw [Real.log_mul hn0.ne' hp0.ne']
    linarith
  have hnat : q = n * p := by exact_mod_cast heq
  have hdvd : p ∣ q := ⟨n, by simpa only [Nat.mul_comm] using hnat⟩
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)

/-- The positive third edge exists for all sufficiently narrow translated packets. -/
theorem exists_thetaTranslatedBump_atomFree_positive_radius {c d : ℝ}
    (hgap : screwSignThreshold < d - c)
    (hatom : ∀ n : ℕ, 2 ≤ n → d - c ≠ Real.log n) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ eps →
      0 < thetaRealWeilPolar (thetaTranslatedBumpGround r hr c)
        (thetaTranslatedBumpGround r hr d) := by
  obtain ⟨e, he, hefree⟩ := exists_atomFree_radius hatom
  let eps := min (e / 4) ((d - c - screwSignThreshold) / 4)
  have heps : 0 < eps := lt_min (by positivity) (by positivity)
  refine ⟨eps, heps, fun r hr hreps => ?_⟩
  have hre : r ≤ e / 4 := hreps.trans (min_le_left _ _)
  have hrg : r ≤ (d - c - screwSignThreshold) / 4 := hreps.trans (min_le_right _ _)
  have hgapr : screwSignThreshold < d - c - 2 * r := by linarith
  let phi := thetaTranslatedBumpGround r hr c
  let psi := thetaTranslatedBumpGround r hr d
  have hps : Function.support phi = Metric.ball c r := support_thetaTranslatedBumpGround r hr c
  have hqs : Function.support psi = Metric.ball d r := support_thetaTranslatedBumpGround r hr d
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
  have hcross : 0 < thetaGammaPolarGroundCrossPairing phi psi := by
    rw [thetaTranslatedBumpGround_continuous_cross]
    exact thetaGammaPolarGroundCrossPairing_pos_of_balls _ _ hr
      (support_thetaTranslatedBumpGround r hr 0) (support_thetaTranslatedBumpGround r hr (d - c))
      (thetaTranslatedBumpGround_nonneg r hr 0) (thetaTranslatedBumpGround_nonneg r hr (d - c)) hgapr
  change 0 < thetaRealWeilPolar phi psi
  unfold thetaRealWeilPolar
  rw [thetaRealArithmeticQuadratic_disjoint_polarization phi psi hsep hfree]
  positivity

/-- Unconditional, cofinal actual-prime construction of the three coupling signs. -/
theorem exists_cofinal_thetaPrime_frustrated_triangle (N : ℕ) :
    ∃ (p q : ℕ) (r : ℝ) (hr : 0 < r), N ≤ p ∧ Nat.Prime p ∧ Nat.Prime q ∧ 2 * p < q ∧
      thetaRealWeilPolar (thetaTranslatedBumpGround r hr 0)
        (thetaTranslatedBumpGround r hr (Real.log p)) < 0 ∧
      thetaRealWeilPolar (thetaTranslatedBumpGround r hr 0)
        (thetaTranslatedBumpGround r hr (Real.log q)) < 0 ∧
      0 < thetaRealWeilPolar (thetaTranslatedBumpGround r hr (Real.log p))
        (thetaTranslatedBumpGround r hr (Real.log q)) := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (2 * p + 1)
  have hpq : 2 * p < q := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : Real.log 2 < Real.log q - Real.log p := by
    have h := Real.log_lt_log (mul_pos (by positivity : (0 : ℝ) < 2) hp0)
      (show (2 : ℝ) * p < q by exact_mod_cast hpq)
    rw [Real.log_mul (by norm_num) hp0.ne'] at h
    linarith
  have hthreshold : screwSignThreshold < Real.log 2 := by
    exact Real.log_lt_log plasticRoot_pos plasticRoot_mem_Ioo.2
  obtain ⟨e₁, he₁, h₁⟩ := exists_thetaTranslatedBump_prime_negative_radius hp
  obtain ⟨e₂, he₂, h₂⟩ := exists_thetaTranslatedBump_prime_negative_radius hq
  obtain ⟨e₃, he₃, h₃⟩ := exists_thetaTranslatedBump_atomFree_positive_radius
    (hthreshold.trans hlog) (fun n hn => prime_log_difference_ne_log_nat hp hq (by omega) hn)
  let r := min e₁ (min e₂ e₃)
  have hr : 0 < r := lt_min he₁ (lt_min he₂ he₃)
  exact ⟨p, q, r, hr, hpN, hp, hq, hpq,
    h₁ r hr (min_le_left _ _),
    h₂ r hr ((min_le_right _ _).trans (min_le_left _ _)),
    h₃ r hr ((min_le_right _ _).trans (min_le_right _ _))⟩

end RHTower
