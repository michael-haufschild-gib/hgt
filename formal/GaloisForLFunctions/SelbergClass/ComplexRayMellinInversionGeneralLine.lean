import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversion
import GaloisForLFunctions.RHTower.FiniteExponentialSumMellin

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GaloisForLFunctions.SelbergClass

theorem gamma_verticalIntegrable_of_pos {c : ℝ} (hc : 0 < c) :
    Complex.VerticalIntegrable Complex.Gamma c := by
  let r : ℝ := Real.pi / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  obtain ⟨C, N, hC0, hGamma⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := c) hc c
  let B : ℝ := max C (Real.Gamma c * Real.exp r)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact le_trans hC0 (le_max_left _ _)
  have hmajor : Integrable (fun t : ℝ =>
      B * ((1 + |t|) ^ N * Real.exp (-r * |t|))) :=
    (integrable_one_add_abs_pow_mul_exp_neg_abs N hr).const_mul B
  apply Integrable.mono' hmajor
  · have hcont : Continuous (fun t : ℝ =>
        Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      apply (Complex.continuousAt_Gamma _ ?_).comp
      · fun_prop
      · intro m hm
        have hre := congrArg Complex.re hm
        simp at hre
        have hm0 : (0 : ℝ) ≤ m := by positivity
        linarith
    exact hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      by_cases ht : 1 ≤ |t|
      · have hΓ := hGamma c t le_rfl le_rfl ht
        have hpow : |t| ^ N ≤ (1 + |t|) ^ N := by
          exact pow_le_pow_left₀ (abs_nonneg t) (by linarith [abs_nonneg t]) N
        calc
          ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖
              ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) := hΓ
          _ = C * |t| ^ N * Real.exp (-r * |t|) := by
            dsimp [r]
            congr 1
            ring_nf
          _ ≤ B * ((1 + |t|) ^ N * Real.exp (-r * |t|)) := by
            have hCB : C ≤ B := le_max_left _ _
            have hcoeff : C * |t| ^ N ≤ B * (1 + |t|) ^ N := by
              calc
                C * |t| ^ N ≤ C * (1 + |t|) ^ N :=
                  mul_le_mul_of_nonneg_left hpow hC0
                _ ≤ B * (1 + |t|) ^ N :=
                  mul_le_mul_of_nonneg_right hCB (pow_nonneg (by positivity) _)
            simpa only [mul_assoc] using
              (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le)
      · have htlt : |t| < 1 := lt_of_not_ge ht
        have hΓ := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re
          (s := (c : ℂ) + (t : ℂ) * Complex.I) (by simpa using hc)
        have hΓc : ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Real.Gamma c := by
          simpa using hΓ
        have hrecover : 1 ≤ Real.exp r * Real.exp (-r * |t|) := by
          rw [← Real.exp_add, ← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          nlinarith [abs_nonneg t]
        have hbase : 1 ≤ (1 + |t|) ^ N := by
          exact one_le_pow₀ (by linarith [abs_nonneg t])
        have hsmall : Real.Gamma c ≤
            (Real.Gamma c * Real.exp r) *
              ((1 + |t|) ^ N * Real.exp (-r * |t|)) := by
          have hgamma0 : 0 ≤ Real.Gamma c := (Real.Gamma_pos_of_pos hc).le
          calc
            Real.Gamma c = Real.Gamma c * 1 := by ring_nf
            _ ≤ Real.Gamma c * (Real.exp r * Real.exp (-r * |t|)) := by
              exact mul_le_mul_of_nonneg_left hrecover hgamma0
            _ ≤ (Real.Gamma c * Real.exp r) *
                ((1 + |t|) ^ N * Real.exp (-r * |t|)) := by
              have hstep : Real.exp r * Real.exp (-r * |t|) ≤
                  Real.exp r * ((1 + |t|) ^ N * Real.exp (-r * |t|)) := by
                exact mul_le_mul_of_nonneg_left
                  (by simpa using
                    (mul_le_mul_of_nonneg_right hbase
                      (Real.exp_pos (-r * |t|)).le))
                  (Real.exp_pos _).le
              nlinarith [hstep, Real.Gamma_pos_of_pos hc]
        calc
          ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Real.Gamma c := hΓc
          _ ≤ (Real.Gamma c * Real.exp r) *
              ((1 + |t|) ^ N * Real.exp (-r * |t|)) := hsmall
          _ ≤ B * ((1 + |t|) ^ N * Real.exp (-r * |t|)) := by
            have hBB : Real.Gamma c * Real.exp r ≤ B := le_max_right _ _
            gcongr

theorem continuous_Gamma_line_of_pos {c : ℝ} (hc : 0 < c) :
    Continuous (fun t : ℝ => Complex.Gamma ((c : ℂ) + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
  · fun_prop
  · intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith

/-- Gamma's vertical decay remains integrable after a subcritical sector weight and one
linear factor. -/
theorem integrable_norm_Gamma_line_mul_exp_abs_mul_one_add_abs
    {c θ : ℝ} (hc : 0 < c) (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi / 2) :
    Integrable (fun t : ℝ =>
      ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ *
        Real.exp (θ * |t|) * (1 + |t|)) := by
  obtain ⟨C, N, hC0, hC⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := c) hc c
  let δ : ℝ := Real.pi / 2 - θ
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  let B : ℝ := max C (2 * Real.Gamma c * Real.exp (Real.pi / 2) * Real.exp δ)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact le_trans hC0 (le_max_left _ _)
  have hmajor : Integrable (fun t : ℝ =>
      B * ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|))) :=
    (integrable_one_add_abs_pow_mul_exp_neg_abs (N + 1) hδ).const_mul B
  apply Integrable.mono' hmajor
  · have hcont : Continuous (fun t : ℝ =>
        ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ *
          Real.exp (θ * |t|) * (1 + |t|)) := by
      have hΓ : Continuous (fun t : ℝ =>
          Complex.Gamma ((c : ℂ) + (t : ℂ) * I)) := by
        rw [continuous_iff_continuousAt]
        intro t
        apply (Complex.continuousAt_Gamma _ ?_).comp
        · fun_prop
        · intro m hm
          have hre := congrArg Complex.re hm
          simp at hre
          have hm0 : (0 : ℝ) ≤ m := by positivity
          linarith
      exact (hΓ.norm.mul (by fun_prop)).mul (by fun_prop)
    exact hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · by_cases ht : 1 ≤ |t|
        · have hΓ := hC c t le_rfl le_rfl ht
          have hpow : |t| ^ N ≤ (1 + |t|) ^ N := by
            exact pow_le_pow_left₀ (abs_nonneg t) (by linarith [abs_nonneg t]) N
          have hpoly : |t| ^ N * (1 + |t|) ≤ (1 + |t|) ^ (N + 1) := by
            rw [pow_succ]
            exact mul_le_mul_of_nonneg_right hpow (by positivity)
          have hexp : Real.exp (-(Real.pi * |t| / 2)) * Real.exp (θ * |t|)
              = Real.exp (-δ * |t|) := by
            rw [← Real.exp_add]
            congr 1
            dsimp [δ]
            ring_nf
          calc
            ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ *
                Real.exp (θ * |t|) * (1 + |t|)
                ≤ (C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2))) *
                    Real.exp (θ * |t|) * (1 + |t|) := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hΓ (Real.exp_pos _).le) (by positivity)
            _ = C * (|t| ^ N * (1 + |t|)) * Real.exp (-δ * |t|) := by
              rw [show C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) *
                  Real.exp (θ * |t|) = C * |t| ^ N *
                    (Real.exp (-(Real.pi * |t| / 2)) * Real.exp (θ * |t|)) by ring_nf,
                hexp]
              ring_nf
            _ ≤ C * (1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpoly hC0) (Real.exp_pos _).le
            _ ≤ B * ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|)) := by
              have hCB : C ≤ B := le_max_left _ _
              have hfac : 0 ≤ (1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|) := by positivity
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_right hCB hfac
        · have htlt : |t| < 1 := lt_of_not_ge ht
          have hΓ := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re
            (s := (c : ℂ) + (t : ℂ) * I) (by simpa using hc)
          have hΓc : ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ ≤ Real.Gamma c := by
            simpa using hΓ
          have hθt : θ * |t| ≤ Real.pi / 2 := by
            have habs0 : 0 ≤ |t| := abs_nonneg t
            have habs1 : |t| ≤ 1 := htlt.le
            nlinarith [Real.pi_pos]
          have hsmall :
              ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ *
                  Real.exp (θ * |t|) * (1 + |t|)
                ≤ 2 * Real.Gamma c * Real.exp (Real.pi / 2) := by
            have he := Real.exp_le_exp.mpr hθt
            have hlin2 : 1 + |t| ≤ 2 := by linarith
            calc
              _ ≤ Real.Gamma c * Real.exp (θ * |t|) * (1 + |t|) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hΓc (Real.exp_pos _).le) (by positivity)
              _ ≤ Real.Gamma c * Real.exp (Real.pi / 2) * (1 + |t|) := by gcongr
              _ ≤ Real.Gamma c * Real.exp (Real.pi / 2) * 2 := by gcongr
              _ = 2 * Real.Gamma c * Real.exp (Real.pi / 2) := by ring_nf
          have hrecover : 1 ≤ Real.exp δ * Real.exp (-δ * |t|) := by
            rw [← Real.exp_add, ← Real.exp_zero]
            apply Real.exp_le_exp.mpr
            nlinarith [abs_nonneg t]
          have hbase : 1 ≤ (1 + |t|) ^ (N + 1) := by
            exact one_le_pow₀ (by linarith [abs_nonneg t])
          calc
            ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ *
                Real.exp (θ * |t|) * (1 + |t|)
                ≤ 2 * Real.Gamma c * Real.exp (Real.pi / 2) := hsmall
            _ ≤ (2 * Real.Gamma c * Real.exp (Real.pi / 2) * Real.exp δ) *
                ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|)) := by
              have hnonneg : 0 ≤ 2 * Real.Gamma c * Real.exp (Real.pi / 2) := by positivity
              calc
                2 * Real.Gamma c * Real.exp (Real.pi / 2) =
                    2 * Real.Gamma c * Real.exp (Real.pi / 2) * 1 := by ring_nf
                _ ≤ 2 * Real.Gamma c * Real.exp (Real.pi / 2) *
                    (Real.exp δ * Real.exp (-δ * |t|)) := by
                  exact mul_le_mul_of_nonneg_left hrecover hnonneg
                _ ≤ (2 * Real.Gamma c * Real.exp (Real.pi / 2) * Real.exp δ) *
                    ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|)) := by
                  have hstep : Real.exp δ * Real.exp (-δ * |t|) ≤
                      Real.exp δ * ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|)) := by
                    exact mul_le_mul_of_nonneg_left
                      (by simpa using
                        (mul_le_mul_of_nonneg_right hbase
                          (Real.exp_pos (-δ * |t|)).le))
                      (Real.exp_pos _).le
                  nlinarith [hstep, Real.exp_pos (Real.pi / 2)]
            _ ≤ B * ((1 + |t|) ^ (N + 1) * Real.exp (-δ * |t|)) := by
              have hBB : 2 * Real.Gamma c * Real.exp (Real.pi / 2) * Real.exp δ ≤ B :=
                le_max_right _ _
              gcongr
      · positivity

theorem norm_cpow_neg_line_add_mul_I_le (c : ℝ) (z : ℂ) (hz : z ≠ 0) (t : ℝ) :
    ‖z ^ (-((c : ℂ) + (t : ℂ) * I))‖ ≤
      ‖z‖ ^ (-c) * Real.exp (|Complex.arg z| * |t|) := by
  have hre : (-((c : ℂ) + (t : ℂ) * I)).re = -c := by norm_num
  have him : (-((c : ℂ) + (t : ℂ) * I)).im = -t := by norm_num
  rw [Complex.norm_cpow_of_ne_zero hz, hre, him, div_eq_mul_inv, ← Real.exp_neg]
  simp only [mul_neg, neg_neg]
  have harg : Complex.arg z * t ≤ |Complex.arg z| * |t| := by
    exact le_trans (le_abs_self (Complex.arg z * t)) (by rw [abs_mul])
  have hexp : Real.exp (Complex.arg z * t) ≤
      Real.exp (|Complex.arg z| * |t|) := Real.exp_le_exp.mpr harg
  exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (norm_nonneg _) _)

/-- Complex inverse Mellin integral on the fixed line `Re w = c`. -/
noncomputable def complexMellinInvLine (c : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) •
    ∫ t : ℝ, z ^ (-((c : ℂ) + (t : ℂ) * I)) *
      F ((c : ℂ) + (t : ℂ) * I)

theorem complexMellinInvLine_two (F : ℂ → ℂ) (z : ℂ) :
    complexMellinInvLine 2 F z = complexMellinInvTwo F z := by
  unfold complexMellinInvLine complexMellinInvTwo
  rfl

theorem differentiableAt_complexMellinInvLine_Gamma {c : ℝ} (hc : 0 < c)
    {z₀ : ℂ} (hz₀re : 0 < z₀.re) :
    DifferentiableAt ℂ (complexMellinInvLine c Complex.Gamma) z₀ := by
  let θ : ℝ := (|Complex.arg z₀| + Real.pi / 2) / 2
  have hz₀ne : z₀ ≠ 0 := by
    intro h
    rw [h] at hz₀re
    simp at hz₀re
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
  let W : ℝ → ℂ := fun t => (c : ℂ) + (t : ℂ) * I
  let F : ℂ → ℝ → ℂ := fun z t => z ^ (-W t) * Complex.Gamma (W t)
  let F' : ℂ → ℝ → ℂ := fun z t =>
    (-W t) * z ^ (-(W t) - 1) * Complex.Gamma (W t)
  let bound : ℝ → ℝ := fun t =>
    (c + 1) * q ^ (-(c + 1)) *
      (‖Complex.Gamma (W t)‖ * Real.exp (θ * |t|) * (1 + |t|))
  have hweighted : Integrable (fun t : ℝ =>
      ‖Complex.Gamma (W t)‖ * Real.exp (θ * |t|) * (1 + |t|)) := by
    simpa only [W] using
      integrable_norm_Gamma_line_mul_exp_abs_mul_one_add_abs hc hθ0 hθ
  have hbound : Integrable bound := by
    dsimp only [bound]
    exact hweighted.const_mul ((c + 1) * q ^ (-(c + 1)))
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
      simpa only [W] using continuous_Gamma_line_of_pos hc
    exact (hpow.mul hgamma).aestronglyMeasurable
  have hFint : Integrable (F z₀) := by
    apply Integrable.mono' (hweighted.const_mul (q ^ (-c)))
    · have hpow : Continuous (fun t : ℝ => z₀ ^ (-W t)) := by
        apply Continuous.const_cpow
        · dsimp only [W]
          fun_prop
        · exact Or.inl hz₀ne
      have hgamma : Continuous (fun t : ℝ => Complex.Gamma (W t)) := by
        simpa only [W] using continuous_Gamma_line_of_pos hc
      exact (hpow.mul hgamma).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        have hqnorm : q ≤ ‖z₀‖ := by
          dsimp [q]
          nlinarith [norm_nonneg z₀]
        have hpowq : ‖z₀‖ ^ (-c) ≤ q ^ (-c) :=
          Real.rpow_le_rpow_of_nonpos hq hqnorm (by linarith)
        have hcp := norm_cpow_neg_line_add_mul_I_le c z₀ hz₀ne t
        have hone : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
        dsimp only [F, W]
        rw [norm_mul]
        calc
          ‖z₀ ^ (-((c : ℂ) + (t : ℂ) * I))‖ *
                ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ ≤
              (‖z₀‖ ^ (-c) * Real.exp (|Complex.arg z₀| * |t|)) *
                ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ := by gcongr
          _ ≤ (q ^ (-c) * Real.exp (θ * |t|)) *
                ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ := by
              have he : Real.exp (|Complex.arg z₀| * |t|) ≤ Real.exp (θ * |t|) := by
                apply Real.exp_le_exp.mpr
                exact mul_le_mul_of_nonneg_right hargθ.le (abs_nonneg t)
              gcongr
          _ ≤ q ^ (-c) *
                (‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ *
                  Real.exp (θ * |t|) * (1 + |t|)) := by
              have hqpow : 0 ≤ q ^ (-c) := Real.rpow_nonneg hq.le _
              have hΓ0 : 0 ≤ ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ := norm_nonneg _
              have he0 : 0 ≤ Real.exp (θ * |t|) := (Real.exp_pos _).le
              calc
                q ^ (-c) * Real.exp (θ * |t|) *
                    ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ =
                    (q ^ (-c) * ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ *
                      Real.exp (θ * |t|)) * 1 := by ring_nf
                _ ≤ (q ^ (-c) * ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ *
                      Real.exp (θ * |t|)) * (1 + |t|) :=
                  mul_le_mul_of_nonneg_left hone (mul_nonneg (mul_nonneg hqpow hΓ0) he0)
                _ = q ^ (-c) *
                    (‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ *
                      Real.exp (θ * |t|) * (1 + |t|)) := by ring_nf
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
      simpa only [W] using continuous_Gamma_line_of_pos hc
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
      have hpowq : ‖z‖ ^ (-(c + 1)) ≤ q ^ (-(c + 1)) :=
        Real.rpow_le_rpow_of_nonpos hq hqz (by linarith)
      have hcp := norm_cpow_neg_line_add_mul_I_le (c + 1) z hz t
      have he : Real.exp (|Complex.arg z| * |t|) ≤ Real.exp (θ * |t|) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hzS.1.le (abs_nonneg t)
      have hwNorm : ‖W t‖ ≤ (c + 1) * (1 + |t|) := by
        dsimp only [W]
        calc
          ‖(c : ℂ) + (t : ℂ) * I‖ ≤ ‖(c : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
          _ = c + |t| := by simp [abs_of_pos hc]
          _ ≤ (c + 1) * (1 + |t|) := by nlinarith [abs_nonneg t]
      dsimp only [F', bound]
      rw [norm_mul, norm_mul]
      have hpow : ‖z ^ (-(W t) - 1)‖ ≤
          q ^ (-(c + 1)) * Real.exp (θ * |t|) := by
        have hexpForm : -(W t) - 1 = -(((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) := by
          dsimp only [W]
          push_cast
          ring_nf
        rw [hexpForm]
        exact hcp.trans (mul_le_mul hpowq he (Real.exp_pos _).le
          (Real.rpow_nonneg hq.le _))
      calc
        ‖-W t‖ * ‖z ^ (-(W t) - 1)‖ * ‖Complex.Gamma (W t)‖ ≤
            ((c + 1) * (1 + |t|)) *
              (q ^ (-(c + 1)) * Real.exp (θ * |t|)) *
              ‖Complex.Gamma (W t)‖ := by
          rw [norm_neg]
          gcongr
        _ = (c + 1) * q ^ (-(c + 1)) *
            (‖Complex.Gamma (W t)‖ * Real.exp (θ * |t|) * (1 + |t|)) := by ring_nf
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
  unfold complexMellinInvLine
  exact hI.2.differentiableAt.const_smul (1 / (2 * Real.pi) : ℝ)

theorem mellinInv_line_Gamma_eq_exp_neg {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    mellinInv c Complex.Gamma x = Complex.exp (-(x : ℂ)) := by
  let f : ℝ → ℂ := fun y => ((Real.exp (-y) : ℝ) : ℂ)
  have hc' : 0 < ((c : ℂ)).re := by simpa using hc
  have hconv : MellinConvergent f (c : ℂ) := by
    simpa only [f, one_mul] using
      (RHTower.mellinConvergent_exp_neg_mul (m := 1) (by norm_num) hc')
  have hmellinLine (t : ℝ) :
      mellin f ((c : ℂ) + (t : ℂ) * I) =
        Complex.Gamma ((c : ℂ) + (t : ℂ) * I) := by
    dsimp only [f]
    simp only [Complex.ofReal_exp, Complex.ofReal_neg]
    have h := RHTower.mellin_exp_neg_mul_finiteExponentialSumMellin (m := 1) (by norm_num)
      (by simpa using hc' : 0 < (((c : ℂ) + (t : ℂ) * I).re))
    simp only [one_mul] at h
    norm_num at h
    exact h
  have hvertical : Complex.VerticalIntegrable (mellin f) c := by
    apply (gamma_verticalIntegrable_of_pos hc).congr
    exact Filter.Eventually.of_forall fun t => by
      exact (hmellinLine t).symm
  have hcont : ContinuousAt f x := by
    dsimp only [f]
    fun_prop
  have hinv := mellinInv_mellin_eq c f hx hconv hvertical hcont
  calc
    mellinInv c Complex.Gamma x = mellinInv c (mellin f) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        change ((x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I))) •
            Complex.Gamma ((c : ℂ) + (t : ℂ) * I) =
          ((x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I))) •
            mellin f ((c : ℂ) + (t : ℂ) * I)
        congr 1
        exact (hmellinLine t).symm
    _ = f x := hinv
    _ = Complex.exp (-(x : ℂ)) := by
      dsimp only [f]
      rw [Complex.ofReal_exp, Complex.ofReal_neg]

theorem complexMellinInvLine_Gamma_ofReal {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    complexMellinInvLine c Complex.Gamma (x : ℂ) = Complex.exp (-(x : ℂ)) := by
  have hdef : complexMellinInvLine c Complex.Gamma (x : ℂ) =
      mellinInv c Complex.Gamma x := by
    unfold complexMellinInvLine mellinInv
    congr 1
  rw [hdef]
  exact mellinInv_line_Gamma_eq_exp_neg hc hx

theorem complexMellinInvLine_Gamma_eq_exp_neg {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : 0 < z.re) :
    complexMellinInvLine c Complex.Gamma z = Complex.exp (-z) := by
  have hUopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hLdiff : DifferentiableOn ℂ (complexMellinInvLine c Complex.Gamma)
      {z : ℂ | 0 < z.re} := by
    intro w hw
    exact (differentiableAt_complexMellinInvLine_Gamma hc hw).differentiableWithinAt
  have hRdiff : DifferentiableOn ℂ (fun w : ℂ => Complex.exp (-w))
      {w : ℂ | 0 < w.re} := by
    intro w _
    exact (differentiableAt_id.neg.cexp).differentiableWithinAt
  have hLan : AnalyticOnNhd ℂ (complexMellinInvLine c Complex.Gamma)
      {z : ℂ | 0 < z.re} := hLdiff.analyticOnNhd hUopen
  have hRan : AnalyticOnNhd ℂ (fun w : ℂ => Complex.exp (-w))
      {w : ℂ | 0 < w.re} := hRdiff.analyticOnNhd hUopen
  have heq := eqOn_rightHalfPlane_of_eq_on_pos_reals hLan hRan
    (fun x hx => complexMellinInvLine_Gamma_ofReal hc hx)
  exact heq hz

end GaloisForLFunctions.SelbergClass
