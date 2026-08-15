import GaloisForLFunctions.SelbergClass.MultipleStandardTwistInitialHolomorphy
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Complex-ray inverse Mellin bridge

Kaczorowski--Perelli's multiple-standard-twist continuation starts from the
Mellin--Barnes identity for `exp (-z)` with a complex ray parameter of positive
real part.  Mathlib's inverse Mellin theorem is stated on positive real rays.
This module closes that gap without an analytic-continuation axiom:

* Gamma vertical decay controls the `z`-derivative uniformly on a local sector;
* dominated differentiation makes the inverse-Mellin integral holomorphic on
  the right half-plane;
* existing real inverse Mellin inversion supplies equality on the positive ray;
* the identity theorem extends it to the whole half-plane.
-/

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GaloisForLFunctions.SelbergClass

/-- Complex inverse-Mellin integral on the fixed line `Re w = 2`. -/
noncomputable def complexMellinInvTwo (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) •
    ∫ t : ℝ, z ^ (-((2 : ℂ) + (t : ℂ) * I)) *
      F ((2 : ℂ) + (t : ℂ) * I)

theorem norm_cpow_neg_two_add_mul_I_le (z : ℂ) (hz : z ≠ 0) (t : ℝ) :
    ‖z ^ (-((2 : ℂ) + (t : ℂ) * I))‖ ≤
      ‖z‖ ^ (-2 : ℝ) * Real.exp (|Complex.arg z| * |t|) := by
  have hre : (-((2 : ℂ) + (t : ℂ) * I)).re = -2 := by norm_num
  have him : (-((2 : ℂ) + (t : ℂ) * I)).im = -t := by norm_num
  rw [Complex.norm_cpow_of_ne_zero hz, hre, him, div_eq_mul_inv, ← Real.exp_neg]
  simp only [mul_neg, neg_neg]
  have harg : Complex.arg z * t ≤ |Complex.arg z| * |t| := by
    exact le_trans (le_abs_self (Complex.arg z * t)) (by rw [abs_mul])
  have hexp : Real.exp (Complex.arg z * t) ≤
      Real.exp (|Complex.arg z| * |t|) := Real.exp_le_exp.mpr harg
  exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (norm_nonneg _) _)

theorem norm_cpow_neg_three_add_mul_I_le (z : ℂ) (hz : z ≠ 0) (t : ℝ) :
    ‖z ^ (-((3 : ℂ) + (t : ℂ) * I))‖ ≤
      ‖z‖ ^ (-3 : ℝ) * Real.exp (|Complex.arg z| * |t|) := by
  have hre : (-((3 : ℂ) + (t : ℂ) * I)).re = -3 := by norm_num
  have him : (-((3 : ℂ) + (t : ℂ) * I)).im = -t := by norm_num
  rw [Complex.norm_cpow_of_ne_zero hz, hre, him, div_eq_mul_inv, ← Real.exp_neg]
  simp only [mul_neg, neg_neg]
  have harg : Complex.arg z * t ≤ |Complex.arg z| * |t| := by
    exact le_trans (le_abs_self (Complex.arg z * t)) (by rw [abs_mul])
  have hexp : Real.exp (Complex.arg z * t) ≤
      Real.exp (|Complex.arg z| * |t|) := Real.exp_le_exp.mpr harg
  exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (norm_nonneg _) _)

theorem integrable_one_add_abs_pow_mul_exp_neg_abs (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun t : ℝ => (1 + |t|) ^ n * Real.exp (-r * |t|)) := by
  have h0 := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hr
  have hn := HTGeometry.integrable_abs_pow_mul_exp_neg_abs n hr
  have hsum : Integrable (fun t : ℝ =>
      Real.exp (-r * |t|) + |t| ^ n * Real.exp (-r * |t|)) := by
    apply (h0.add hn).congr
    exact Filter.Eventually.of_forall fun t => by simp
  apply Integrable.mono' (hsum.const_mul (2 ^ (n - 1)))
  · fun_prop
  · exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · have hp := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg t) n
        calc
          (1 + |t|) ^ n * Real.exp (-r * |t|) ≤
              (2 : ℝ) ^ (n - 1) * (1 ^ n + |t| ^ n) * Real.exp (-r * |t|) := by
            gcongr
          _ = (2 : ℝ) ^ (n - 1) *
              (Real.exp (-r * |t|) + |t| ^ n * Real.exp (-r * |t|)) := by
            rw [one_pow]
            ring
      · positivity

theorem integrable_norm_Gamma_two_mul_exp_abs_mul_linear
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi / 2) :
    Integrable (fun t : ℝ =>
      ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ * Real.exp (θ * |t|) * (2 + |t|)) := by
  obtain ⟨C, N, hC0, hC⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := (2 : ℝ)) (by norm_num) 2
  let δ : ℝ := Real.pi / 2 - θ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let B : ℝ := max (2 * C) (3 * Real.exp (Real.pi / 2) * Real.exp δ)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact le_trans (mul_nonneg (by norm_num) hC0) (le_max_left _ _)
  have hmajor : Integrable (fun t : ℝ =>
      B * ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|))) :=
    (integrable_one_add_abs_pow_mul_exp_neg_abs (N + 1) hδ).const_mul B
  apply Integrable.mono' hmajor
  · have hexpCont : Continuous (fun t : ℝ => Real.exp (θ * |t|)) := by
      fun_prop
    have hlinCont : Continuous (fun t : ℝ => 2 + |t|) := by fun_prop
    have hcont : Continuous (fun t : ℝ =>
        ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ * Real.exp (θ * |t|) * (2 + |t|)) :=
      (RHTower.Sieve.continuous_Gamma_two_line.norm.mul hexpCont).mul hlinCont
    exact hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · by_cases ht : 1 ≤ |t|
        · have hΓ := hC 2 t (by norm_num) le_rfl ht
          have hΓ' : ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ ≤
              C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) := by simpa using hΓ
          have hpow : |t| ^ N ≤ (1 + |t|) ^ N := by
            exact pow_le_pow_left₀ (abs_nonneg t) (by linarith [abs_nonneg t]) N
          have hlin : 2 + |t| ≤ 2 * (1 + |t|) := by linarith [abs_nonneg t]
          have hexp : Real.exp (-(Real.pi * |t| / 2)) * Real.exp (θ * |t|)
              = Real.exp (-δ * |t|) := by
            rw [← Real.exp_add]
            congr 1
            dsimp [δ]
            ring
          have hpoly : C * |t| ^ N * (2 + |t|) ≤
              (2 * C) * (1 + |t|) ^ (N + 1) := by
            calc
              C * |t| ^ N * (2 + |t|) ≤ C * (1 + |t|) ^ N * (2 * (1 + |t|)) := by
                exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC0) hlin
                  (by positivity) (mul_nonneg hC0 (pow_nonneg (by positivity) _))
              _ = (2 * C) * (1 + |t|) ^ (N + 1) := by
                rw [pow_succ]
                ring
          calc
            ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ * Real.exp (θ * |t|) * (2 + |t|)
                ≤ (C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2))) *
                    Real.exp (θ * |t|) * (2 + |t|) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hΓ' (Real.exp_pos _).le) (by positivity)
            _ = C * |t| ^ N * (2 + |t|) * Real.exp (-δ * |t|) := by
              rw [show C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) *
                  Real.exp (θ * |t|) = C * |t| ^ N *
                    (Real.exp (-(Real.pi * |t| / 2)) * Real.exp (θ * |t|)) by ring,
                hexp]
              ring
            _ ≤ (2 * C) * (1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|) := by
              exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
            _ ≤ B * ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|)) := by
              have hBC : 2 * C ≤ B := le_max_left _ _
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_right hBC
                (mul_nonneg (pow_nonneg (by positivity) _) (Real.exp_pos _).le)
        · have htlt : |t| < 1 := lt_of_not_ge ht
          have hΓ := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re
            (s := (2 : ℂ) + (t : ℂ) * I) (by norm_num)
          have hΓ1 : ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ ≤ 1 := by
            calc
              _ ≤ Real.Gamma 2 := by simpa using hΓ
              _ = 1 := by norm_num [Real.Gamma_nat_eq_factorial]
          have hθt : θ * |t| ≤ Real.pi / 2 := by
            have habs0 : 0 ≤ |t| := abs_nonneg t
            have habs1 : |t| ≤ 1 := htlt.le
            nlinarith [Real.pi_pos]
          have hsmall :
              ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ * Real.exp (θ * |t|) * (2 + |t|)
                ≤ 3 * Real.exp (Real.pi / 2) := by
            have he := Real.exp_le_exp.mpr hθt
            have hlin3 : 2 + |t| ≤ 3 := by linarith
            calc
              _ ≤ 1 * Real.exp (θ * |t|) * (2 + |t|) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hΓ1 (Real.exp_pos _).le) (by positivity)
              _ ≤ 1 * Real.exp (Real.pi / 2) * (2 + |t|) := by gcongr
              _ ≤ 1 * Real.exp (Real.pi / 2) * 3 := by gcongr
              _ = 3 * Real.exp (Real.pi / 2) := by ring
          have hrecover : 1 ≤ Real.exp δ * Real.exp (-δ * |t|) := by
            rw [← Real.exp_add, ← Real.exp_zero]
            apply Real.exp_le_exp.mpr
            nlinarith [abs_nonneg t]
          have hBB : 3 * Real.exp (Real.pi / 2) * Real.exp δ ≤ B := le_max_right _ _
          have hbase1 : 1 ≤ (1 + |t|) ^ (N + 1) := by
            exact one_le_pow₀ (by linarith [abs_nonneg t])
          calc
            ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ * Real.exp (θ * |t|) * (2 + |t|)
                ≤ 3 * Real.exp (Real.pi / 2) := hsmall
            _ ≤ (3 * Real.exp (Real.pi / 2) * Real.exp δ) *
                ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|)) := by
              have hnonneg : 0 ≤ 3 * Real.exp (Real.pi / 2) := by positivity
              calc
                3 * Real.exp (Real.pi / 2) = 3 * Real.exp (Real.pi / 2) * 1 := by ring
                _ ≤ 3 * Real.exp (Real.pi / 2) *
                    (Real.exp δ * Real.exp (-δ * |t|)) := by
                  exact mul_le_mul_of_nonneg_left hrecover hnonneg
                _ ≤ (3 * Real.exp (Real.pi / 2) * Real.exp δ) *
                    ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|)) := by
                  have hstep : Real.exp δ * Real.exp (-δ * |t|) ≤
                      Real.exp δ * ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|)) := by
                    exact mul_le_mul_of_nonneg_left
                      (by simpa using
                        (mul_le_mul_of_nonneg_right hbase1 (Real.exp_pos (-δ * |t|)).le))
                      (Real.exp_pos _).le
                  nlinarith [hstep, Real.exp_pos (Real.pi / 2)]
            _ ≤ B * ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|)) := by
              gcongr
      · positivity

theorem differentiableAt_complexMellinInvTwo_Gamma {z₀ : ℂ} (hz₀re : 0 < z₀.re) :
    DifferentiableAt ℂ (complexMellinInvTwo Complex.Gamma) z₀ := by
  let θ : ℝ := (|Complex.arg z₀| + Real.pi / 2) / 2
  have hz₀ne : z₀ ≠ 0 := by
    intro h
    rw [h] at hz₀re
    simpa using hz₀re
  have harg₀ : |Complex.arg z₀| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz₀re)
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    positivity
  have hargθ : |Complex.arg z₀| < θ := by
    dsimp [θ]
    linarith
  have hθ : θ < Real.pi / 2 := by
    dsimp [θ]
    linarith
  let q : ℝ := ‖z₀‖ / 2
  have hq : 0 < q := by
    dsimp [q]
    positivity
  let S : Set ℂ := {z | |Complex.arg z| < θ ∧ q < ‖z‖}
  have hslit₀ : z₀ ∈ Complex.slitPlane := Or.inl hz₀re
  have hS : S ∈ nhds z₀ := by
    have hargEv : ∀ᶠ z in nhds z₀, |Complex.arg z| < θ :=
      (Complex.continuousAt_arg hslit₀).abs.eventually_lt continuousAt_const hargθ
    have hqnorm : q < ‖z₀‖ := by
      dsimp [q]
      nlinarith [norm_pos_iff.mpr hz₀ne]
    have hnormEv : ∀ᶠ z in nhds z₀, q < ‖z‖ :=
      continuousAt_const.eventually_lt continuousAt_id.norm hqnorm
    filter_upwards [hargEv, hnormEv] with z hzarg hznorm
    exact ⟨hzarg, hznorm⟩
  let W : ℝ → ℂ := fun t => (2 : ℂ) + (t : ℂ) * I
  let F : ℂ → ℝ → ℂ := fun z t => z ^ (-W t) * Complex.Gamma (W t)
  let F' : ℂ → ℝ → ℂ := fun z t =>
    (-W t) * z ^ (-(W t) - 1) * Complex.Gamma (W t)
  let bound : ℝ → ℝ := fun t =>
    q ^ (-3 : ℝ) *
      (‖Complex.Gamma (W t)‖ * Real.exp (θ * |t|) * (2 + |t|))
  have hweighted : Integrable (fun t : ℝ =>
      ‖Complex.Gamma (W t)‖ * Real.exp (θ * |t|) * (2 + |t|)) := by
    simpa only [W] using integrable_norm_Gamma_two_mul_exp_abs_mul_linear hθ0 hθ
  have hbound : Integrable bound := by
    dsimp only [bound]
    exact hweighted.const_mul (q ^ (-3 : ℝ))
  have hFmeas : ∀ᶠ z in nhds z₀, AEStronglyMeasurable (F z) volume := by
    filter_upwards [hS] with z hzS
    change |Complex.arg z| < θ ∧ q < ‖z‖ at hzS
    have hz : z ≠ 0 := by
      intro hz0
      rw [hz0] at hzS
      simp only [norm_zero] at hzS
      linarith [hq]
    have hpow : Continuous (fun t : ℝ => z ^ (-W t)) := by
      apply Continuous.const_cpow
      · dsimp only [W]
        fun_prop
      · exact Or.inl hz
    have hgamma : Continuous (fun t : ℝ => Complex.Gamma (W t)) := by
      simpa only [W] using RHTower.Sieve.continuous_Gamma_two_line
    exact (hpow.mul hgamma).aestronglyMeasurable
  have hFint : Integrable (F z₀) := by
    apply Integrable.mono' (hweighted.const_mul (q ^ (-2 : ℝ)))
    · have hpow : Continuous (fun t : ℝ => z₀ ^ (-W t)) := by
        apply Continuous.const_cpow
        · dsimp only [W]
          fun_prop
        · exact Or.inl hz₀ne
      have hgamma : Continuous (fun t : ℝ => Complex.Gamma (W t)) := by
        simpa only [W] using RHTower.Sieve.continuous_Gamma_two_line
      exact (hpow.mul hgamma).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        have hqnorm : q ≤ ‖z₀‖ := by
          dsimp [q]
          nlinarith [norm_nonneg z₀]
        have hpowq : ‖z₀‖ ^ (-2 : ℝ) ≤ q ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hq hqnorm (by norm_num)
        have hcp := norm_cpow_neg_two_add_mul_I_le z₀ hz₀ne t
        have hone : 1 ≤ 2 + |t| := by linarith [abs_nonneg t]
        dsimp only [F, W]
        rw [norm_mul]
        calc
          ‖z₀ ^ (-((2 : ℂ) + (t : ℂ) * I))‖ *
                ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ ≤
              (‖z₀‖ ^ (-2 : ℝ) * Real.exp (|Complex.arg z₀| * |t|)) *
                ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ := by gcongr
          _ ≤ (q ^ (-2 : ℝ) * Real.exp (θ * |t|)) *
                ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ := by
              have he : Real.exp (|Complex.arg z₀| * |t|) ≤ Real.exp (θ * |t|) := by
                apply Real.exp_le_exp.mpr
                exact mul_le_mul_of_nonneg_right hargθ.le (abs_nonneg t)
              gcongr
          _ ≤ q ^ (-2 : ℝ) *
                (‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ *
                  Real.exp (θ * |t|) * (2 + |t|)) := by
              have hqpow : 0 ≤ q ^ (-2 : ℝ) := Real.rpow_nonneg hq.le _
              have hΓ0 : 0 ≤ ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ := norm_nonneg _
              have he0 : 0 ≤ Real.exp (θ * |t|) := (Real.exp_pos _).le
              calc
                q ^ (-2 : ℝ) * Real.exp (θ * |t|) *
                    ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ =
                    (q ^ (-2 : ℝ) * ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ *
                      Real.exp (θ * |t|)) * 1 := by ring
                _ ≤ (q ^ (-2 : ℝ) * ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ *
                      Real.exp (θ * |t|)) * (2 + |t|) :=
                  mul_le_mul_of_nonneg_left hone (mul_nonneg (mul_nonneg hqpow hΓ0) he0)
                _ = q ^ (-2 : ℝ) *
                    (‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ *
                      Real.exp (θ * |t|) * (2 + |t|)) := by ring
  have hF'meas : AEStronglyMeasurable (F' z₀) volume := by
    have hpow : Continuous (fun t : ℝ => z₀ ^ (-(W t) - 1)) := by
      apply Continuous.const_cpow
      · dsimp only [W]
        fun_prop
      · exact Or.inl hz₀ne
    have hw : Continuous W := by
      dsimp only [W]
      fun_prop
    have hgamma : Continuous (fun t : ℝ => Complex.Gamma (W t)) := by
      simpa only [W] using RHTower.Sieve.continuous_Gamma_two_line
    exact (((hw.neg.mul hpow).mul hgamma)).aestronglyMeasurable
  have hderivBound : ∀ᵐ t : ℝ ∂volume, ∀ z ∈ S, ‖F' z t‖ ≤ bound t := by
    exact Filter.Eventually.of_forall fun t z hzS => by
      change |Complex.arg z| < θ ∧ q < ‖z‖ at hzS
      have hz : z ≠ 0 := by
        intro hz0
        rw [hz0] at hzS
        simp only [norm_zero] at hzS
        linarith [hq]
      have hqz : q ≤ ‖z‖ := hzS.2.le
      have hpowq : ‖z‖ ^ (-3 : ℝ) ≤ q ^ (-3 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hq hqz (by norm_num)
      have hcp := norm_cpow_neg_three_add_mul_I_le z hz t
      have he : Real.exp (|Complex.arg z| * |t|) ≤ Real.exp (θ * |t|) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hzS.1.le (abs_nonneg t)
      have hwNorm : ‖W t‖ ≤ 2 + |t| := by
        dsimp only [W]
        calc
          ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
          _ = 2 + |t| := by simp
      dsimp only [F', bound]
      rw [norm_mul, norm_mul]
      have hpow : ‖z ^ (-(W t) - 1)‖ ≤ q ^ (-3 : ℝ) * Real.exp (θ * |t|) := by
        have hexpForm : -(W t) - 1 = -((3 : ℂ) + (t : ℂ) * I) := by
          dsimp only [W]
          ring
        rw [hexpForm]
        exact hcp.trans (mul_le_mul hpowq he (Real.exp_pos _).le
          (Real.rpow_nonneg hq.le _))
      calc
        ‖-W t‖ * ‖z ^ (-(W t) - 1)‖ * ‖Complex.Gamma (W t)‖ ≤
            (2 + |t|) * (q ^ (-3 : ℝ) * Real.exp (θ * |t|)) *
              ‖Complex.Gamma (W t)‖ := by
          rw [norm_neg]
          gcongr
        _ = q ^ (-3 : ℝ) *
            (‖Complex.Gamma (W t)‖ * Real.exp (θ * |t|) * (2 + |t|)) := by ring
  have hdiff : ∀ᵐ t : ℝ ∂volume, ∀ z ∈ S,
      HasDerivAt (fun z => F z t) (F' z t) z := by
    exact Filter.Eventually.of_forall fun t z hzS => by
      change |Complex.arg z| < θ ∧ q < ‖z‖ at hzS
      have hzre : 0 < z.re := by
        rcases Complex.abs_arg_lt_pi_div_two_iff.mp (hzS.1.trans hθ) with hzre | hzero
        · exact hzre
        · rw [hzero] at hzS
          simp only [norm_zero] at hzS
          linarith [hq]
      have hzslit : z ∈ Complex.slitPlane := Or.inl hzre
      have hcp := (hasDerivAt_id z).cpow_const (c := -W t) hzslit
      have hmul := hcp.mul_const (Complex.Gamma (W t))
      dsimp only [F, F']
      simpa only [id_eq, mul_one] using hmul
  have hI := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') hS hFmeas hFint hF'meas hderivBound hbound hdiff
  unfold complexMellinInvTwo
  exact hI.2.differentiableAt.const_smul (1 / (2 * Real.pi) : ℝ)

theorem coeffLaplaceProfile_delta_eq_exp_neg (x : ℝ) :
    GaloisForLFunctions.HTGeometry.coeffLaplaceProfile LSeries.delta x =
      Complex.exp (-(x : ℂ)) := by
  unfold GaloisForLFunctions.HTGeometry.coeffLaplaceProfile
  rw [tsum_eq_single 1]
  · simp [LSeries.delta]
  · intro b hb
    simp [LSeries.delta, hb]

theorem complexMellinInvTwo_Gamma_ofReal {x : ℝ} (hx : 0 < x) :
    complexMellinInvTwo Complex.Gamma (x : ℂ) = Complex.exp (-(x : ℂ)) := by
  have h := RHTower.Sieve.mellinInv_two_gamma_mul_LSeries_eq_coeffLaplaceProfile
    (f := LSeries.delta) (x := x) (by
      intro n
      by_cases hn : n = 1 <;> simp [LSeries.delta, hn])
      (by simp [LSeries.delta]) hx
  rw [LSeries_delta] at h
  rw [coeffLaplaceProfile_delta_eq_exp_neg] at h
  have hdef : complexMellinInvTwo Complex.Gamma (x : ℂ) = mellinInv 2 Complex.Gamma x := by
    unfold complexMellinInvTwo mellinInv
    congr 1
  calc
    complexMellinInvTwo Complex.Gamma (x : ℂ) = mellinInv 2 Complex.Gamma x := hdef
    _ = Complex.exp (-(x : ℂ)) := by simpa using h

theorem eqOn_rightHalfPlane_of_eq_on_pos_reals
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re})
    (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re})
    (hpos : ∀ x : ℝ, 0 < x → f (x : ℂ) = g (x : ℂ)) :
    EqOn f g {z : ℂ | 0 < z.re} := by
  refine hf.eqOn_of_preconnected_of_mem_closure hg
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (1 : ℂ)) (by norm_num) ?_
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let x : ℝ := 1 + ε / 2
  refine ⟨(x : ℂ), ?_, ?_⟩
  · refine ⟨hpos x (by dsimp [x]; linarith), ?_⟩
    dsimp [x]
    norm_num [Complex.ext_iff]
    linarith
  · rw [dist_comm, dist_eq_norm]
    change ‖(x : ℂ) - (1 : ℂ)‖ < ε
    rw [← Complex.ofReal_one, ← ofReal_sub, norm_real]
    dsimp [x]
    rw [abs_of_nonneg]
    · linarith
    · linarith

theorem complexMellinInvTwo_Gamma_eq_exp_neg {z : ℂ} (hz : 0 < z.re) :
    complexMellinInvTwo Complex.Gamma z = Complex.exp (-z) := by
  have hUopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hLdiff : DifferentiableOn ℂ (complexMellinInvTwo Complex.Gamma)
      {z : ℂ | 0 < z.re} := by
    intro w hw
    exact (differentiableAt_complexMellinInvTwo_Gamma hw).differentiableWithinAt
  have hRdiff : DifferentiableOn ℂ (fun w : ℂ => Complex.exp (-w))
      {w : ℂ | 0 < w.re} := by
    intro w _
    exact (differentiableAt_id.neg.cexp).differentiableWithinAt
  have hLan : AnalyticOnNhd ℂ (complexMellinInvTwo Complex.Gamma)
      {z : ℂ | 0 < z.re} := hLdiff.analyticOnNhd hUopen
  have hRan : AnalyticOnNhd ℂ (fun w : ℂ => Complex.exp (-w))
      {w : ℂ | 0 < w.re} := hRdiff.analyticOnNhd hUopen
  have heq := eqOn_rightHalfPlane_of_eq_on_pos_reals hLan hRan
    (fun x hx => complexMellinInvTwo_Gamma_ofReal hx)
  exact heq hz

end GaloisForLFunctions.SelbergClass
