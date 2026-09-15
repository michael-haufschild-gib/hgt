import GaloisForLFunctions.HTGeometry.ExponentialSumAsymptotics
import GaloisForLFunctions.HTGeometry.RealBaseCpowPolar

/-!
# HB endpoint-counterterm uniqueness

At the physical fundamental QNM, the frequency lies in `-2 < Re w < -1`.
In this half-plane the two power counterterms and the logarithmic counterterm
form a strictly ordered divergent scale.  A finite endpoint renormalization
therefore fixes all three coefficients and the finite value itself.
-/

open Filter Topology
noncomputable section
set_option autoImplicit false

namespace RHTower.D4BMEndpointRenormalization

private theorem complex_exp_mul_nat_atTop {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun n : ℕ => Complex.exp (w * (n : ℂ))) atTop (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have hmul' : Tendsto (fun n : ℕ => (-w.re) * (-(n : ℝ))) atTop atBot :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => -w.re) atTop (𝓝 (-w.re))).pos_mul_atBot
      (by linarith) hneg
  have hmul : Tendsto (fun n : ℕ => w.re * (n : ℝ)) atTop atBot := by
    simpa only [neg_mul_neg] using hmul'
  have hexp := Real.tendsto_exp_atBot.comp hmul
  apply hexp.congr'
  filter_upwards [] with n
  simp [dist_zero_right, Complex.norm_exp, Complex.mul_re]

private theorem nat_mul_complex_exp_mul_nat_atTop {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun n : ℕ => (n : ℂ) * Complex.exp (w * (n : ℂ))) atTop (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hreal :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (-w.re) (by linarith)
  have h := hreal.comp tendsto_natCast_atTop_atTop
  convert h using 1
  all_goals
    simp [Function.comp_def, dist_zero_right, Complex.norm_exp, Complex.mul_re]

private theorem natCast_inv_complex_tendsto :
    Tendsto (fun n : ℕ => ((n : ℂ)⁻¹)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using hreal.ofReal

/-- The logarithmic sampling sequence for a two-power endpoint counterterm. -/
def renormalizationSequence (w A B C : ℂ) (n : ℕ) : ℂ :=
  A * Complex.exp (-w * (n : ℂ)) +
    B * Complex.exp (-(w + 1) * (n : ℂ)) - C * (n : ℂ)

/-- In `Re w < -1`, convergence of the sampled counterterm forces all three
coefficients to vanish. -/
theorem renormalizationSequence_coefficients_unique
    {w A B C L : ℂ} (hw : w.re < -1)
    (h : Tendsto (renormalizationSequence w A B C) atTop (𝓝 L)) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have hw0 : w.re < 0 := hw.trans (by norm_num)
  have hw1 : (w + 1).re < 0 := by
    change w.re + 1 < 0
    linarith
  have hEw := complex_exp_mul_nat_atTop hw0
  have hprod : Tendsto (fun n => renormalizationSequence w A B C n *
      Complex.exp (w * (n : ℂ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using h.mul hEw
  have hB : Tendsto (fun n : ℕ => B * Complex.exp (-(n : ℂ))) atTop (𝓝 0) := by
    have hb' := (complex_exp_mul_nat_atTop (w := (-1 : ℂ)) (by norm_num)).const_mul B
    have hb0 : Tendsto (fun n : ℕ => B * Complex.exp ((-1 : ℂ) * (n : ℂ)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hb'
    apply hb0.congr'
    filter_upwards [] with n
    congr 2
    ring
  have hC : Tendsto (fun n : ℕ => C * ((n : ℂ) * Complex.exp (w * (n : ℂ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (nat_mul_complex_exp_mul_nat_atTop hw0).const_mul C
  have hA : Tendsto (fun n : ℕ => A + B * Complex.exp (-(n : ℂ)) -
      C * ((n : ℂ) * Complex.exp (w * (n : ℂ)))) atTop (𝓝 A) := by
    simpa only [add_zero, sub_zero] using (tendsto_const_nhds.add hB).sub hC
  have hprodA : Tendsto (fun n : ℕ => A + B * Complex.exp (-(n : ℂ)) -
      C * ((n : ℂ) * Complex.exp (w * (n : ℂ)))) atTop (𝓝 0) := by
    apply hprod.congr'
    filter_upwards [] with n
    unfold renormalizationSequence
    have h0 : Complex.exp (-w * (n : ℂ)) * Complex.exp (w * (n : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      convert Complex.exp_zero using 1
      all_goals ring_nf
    have h1 : Complex.exp (-(w + 1) * (n : ℂ)) * Complex.exp (w * (n : ℂ)) =
        Complex.exp (-(n : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      (A * Complex.exp (-w * (n : ℂ)) + B * Complex.exp (-(w + 1) * (n : ℂ)) -
          C * (n : ℂ)) * Complex.exp (w * (n : ℂ)) =
          A * (Complex.exp (-w * (n : ℂ)) * Complex.exp (w * (n : ℂ))) +
          B * (Complex.exp (-(w + 1) * (n : ℂ)) * Complex.exp (w * (n : ℂ))) -
          C * ((n : ℂ) * Complex.exp (w * (n : ℂ))) := by ring
      _ = A + B * Complex.exp (-(n : ℂ)) -
          C * ((n : ℂ) * Complex.exp (w * (n : ℂ))) := by rw [h0, h1]; ring
  have hAzero : A = 0 := tendsto_nhds_unique hA hprodA
  subst A
  have hEw1 := complex_exp_mul_nat_atTop hw1
  have hprod1 : Tendsto (fun n => renormalizationSequence w 0 B C n *
      Complex.exp ((w + 1) * (n : ℂ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using h.mul hEw1
  have hC1 : Tendsto (fun n : ℕ => C * ((n : ℂ) * Complex.exp ((w + 1) * (n : ℂ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (nat_mul_complex_exp_mul_nat_atTop hw1).const_mul C
  have hBt : Tendsto (fun n : ℕ => B -
      C * ((n : ℂ) * Complex.exp ((w + 1) * (n : ℂ)))) atTop (𝓝 B) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hC1
  have hprodB : Tendsto (fun n : ℕ => B -
      C * ((n : ℂ) * Complex.exp ((w + 1) * (n : ℂ)))) atTop (𝓝 0) := by
    apply hprod1.congr'
    filter_upwards [] with n
    unfold renormalizationSequence
    have h1 : Complex.exp (-(w + 1) * (n : ℂ)) *
        Complex.exp ((w + 1) * (n : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      convert Complex.exp_zero using 1
      all_goals ring_nf
    calc
      (0 * Complex.exp (-w * (n : ℂ)) + B * Complex.exp (-(w + 1) * (n : ℂ)) -
          C * (n : ℂ)) * Complex.exp ((w + 1) * (n : ℂ)) =
          B * (Complex.exp (-(w + 1) * (n : ℂ)) *
            Complex.exp ((w + 1) * (n : ℂ))) -
          C * ((n : ℂ) * Complex.exp ((w + 1) * (n : ℂ))) := by ring
      _ = B - C * ((n : ℂ) * Complex.exp ((w + 1) * (n : ℂ))) := by rw [h1]; ring
  have hBzero : B = 0 := tendsto_nhds_unique hBt hprodB
  subst B
  have hquot : Tendsto (fun n => renormalizationSequence w 0 0 C n * ((n : ℂ)⁻¹))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using h.mul natCast_inv_complex_tendsto
  have hconst : Tendsto (fun _n : ℕ => -C) atTop (𝓝 (-C)) := tendsto_const_nhds
  have hconst0 : Tendsto (fun _n : ℕ => -C) atTop (𝓝 0) := by
    apply hquot.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    unfold renormalizationSequence
    simp only [zero_mul, zero_add]
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    field_simp
    ring
  have hCzero : C = 0 := by
    have : -C = 0 := tendsto_nhds_unique hconst hconst0
    simpa using this
  exact ⟨rfl, rfl, hCzero⟩

/-- Two power divergences and one logarithmic divergence at the positive
endpoint. -/
def endpointCounterterm (w A B C : ℂ) (e : ℝ) : ℂ :=
  A * (e : ℂ) ^ w + B * (e : ℂ) ^ (w + 1) + C * (Real.log e : ℂ)

/-- A finite positive-endpoint limit forces every coefficient in the
two-power-plus-log counterterm to vanish. -/
theorem endpointCounterterm_coefficients_unique
    {w A B C L : ℂ} (hw : w.re < -1)
    (h : Tendsto (endpointCounterterm w A B C) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have hn : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝[>] (0 : ℝ)) :=
    Real.tendsto_exp_atBot_nhdsGT.comp hn
  apply renormalizationSequence_coefficients_unique hw
  apply (h.comp he).congr'
  filter_upwards [] with n
  change A * ((Real.exp (-(n : ℝ)) : ℂ) ^ w) +
      B * ((Real.exp (-(n : ℝ)) : ℂ) ^ (w + 1)) +
      C * (Real.log (Real.exp (-(n : ℝ))) : ℂ) =
    A * Complex.exp (-w * (n : ℂ)) +
      B * Complex.exp (-(w + 1) * (n : ℂ)) - C * (n : ℂ)
  rw [GaloisForLFunctions.HTGeometry.ofReal_cpow_eq_exp (Real.exp_pos _) w,
    GaloisForLFunctions.HTGeometry.ofReal_cpow_eq_exp (Real.exp_pos _) (w + 1),
    Real.log_exp]
  push_cast
  have hp₀ : Complex.exp (-(n : ℂ) * w) = Complex.exp (-w * (n : ℂ)) := by
    congr 1
    ring
  have hp₁ : Complex.exp (-(n : ℂ) * (w + 1)) =
      Complex.exp (-(w + 1) * (n : ℂ)) := by
    congr 1
    ring
  rw [hp₀, hp₁]
  ring

/-- Two subtraction schemes for one endpoint expression cannot both have
finite limits unless their three counterterm coefficients agree. -/
theorem endpointRenormalization_data_unique
    {w c₀ c₁ d₀ c₀' c₁' d₀' L L' : ℂ} {f : ℝ → ℂ}
    (hw : w.re < -1)
    (h : Tendsto (fun e => f e -
      (c₀ * (e : ℂ) ^ w / w + c₁ * (e : ℂ) ^ (w + 1) / (w + 1) +
        d₀ * (Real.log e : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (h' : Tendsto (fun e => f e -
      (c₀' * (e : ℂ) ^ w / w + c₁' * (e : ℂ) ^ (w + 1) / (w + 1) +
        d₀' * (Real.log e : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 L')) :
    c₀ = c₀' ∧ c₁ = c₁' ∧ d₀ = d₀' := by
  have hd := h.sub h'
  have hc : Tendsto
      (endpointCounterterm w ((c₀' - c₀) / w) ((c₁' - c₁) / (w + 1)) (d₀' - d₀))
      (𝓝[>] (0 : ℝ)) (𝓝 (L - L')) := by
    apply hd.congr'
    filter_upwards [] with e
    unfold endpointCounterterm
    ring
  obtain ⟨h₀, h₁, hd₀⟩ := endpointCounterterm_coefficients_unique hw hc
  have hw₀ : w ≠ 0 := by
    intro hzero
    subst w
    norm_num at hw
  have hw₁ : w + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [Complex.add_re] at hre
    linarith
  constructor
  · exact (sub_eq_zero.mp ((div_eq_zero_iff).mp h₀ |>.resolve_right hw₀)).symm
  constructor
  · exact (sub_eq_zero.mp ((div_eq_zero_iff).mp h₁ |>.resolve_right hw₁)).symm
  · exact (sub_eq_zero.mp hd₀).symm

/-- In the physical QNM half-plane, endpoint profile determines both three
subtraction coefficients and resulting finite value. -/
theorem endpointRenormalization_unique
    {w c₀ c₁ d₀ c₀' c₁' d₀' L L' : ℂ} {f : ℝ → ℂ}
    (hw : w.re < -1)
    (h : Tendsto (fun e => f e -
      (c₀ * (e : ℂ) ^ w / w + c₁ * (e : ℂ) ^ (w + 1) / (w + 1) +
        d₀ * (Real.log e : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (h' : Tendsto (fun e => f e -
      (c₀' * (e : ℂ) ^ w / w + c₁' * (e : ℂ) ^ (w + 1) / (w + 1) +
        d₀' * (Real.log e : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 L')) :
    c₀ = c₀' ∧ c₁ = c₁' ∧ d₀ = d₀' ∧ L = L' := by
  obtain ⟨hc₀, hc₁, hd₀⟩ := endpointRenormalization_data_unique hw h h'
  subst c₀'
  subst c₁'
  subst d₀'
  exact ⟨rfl, rfl, rfl, tendsto_nhds_unique h h'⟩

end RHTower.D4BMEndpointRenormalization
