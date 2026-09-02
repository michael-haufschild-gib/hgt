import GaloisForLFunctions.RHTower.LevinsonPositiveDetectorWeight
import GaloisForLFunctions.RHTower.LevinsonProportionGate

/-!
# Levinson mean-square gate at the classical positive parameter

The detector coefficient is `1 - λ log n`, so the classical parameter at outer height `U`
is `λ = 1 / log U`.  This gate fixes that value before selecting the zero-avoiding window, rather
than carrying a sign convention or making the parameter depend circularly on an endpoint.  Its
conversion to the polar/counting gate proves nonvanishing and positivity of the archimedean weight
from the window geometry; those facts are not analytic inputs.
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

/-- Exact mean-square obligation at Levinson's classical positive reciprocal-log parameter. -/
def LevinsonReciprocalLogMeanSquareGate (R c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop, ∃ (T₁ T₂ σ₀ Mb : ℝ) (b : ℕ → ℂ) (N : ℕ),
    T₁ ∈ Set.Icc (20 : ℝ) 21 ∧ T₂ ∈ Set.Ioc (U - 1) U ∧
    1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
    (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧
    1 ≤ Mb ∧ (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb ∧
    Real.log Mb ≤ 5 * Real.log T₂ ∧
    1 / 4 ≤ σ₀ ∧ σ₀ < 1 / 2 ∧ (1 / 2 - σ₀) * Real.log T₂ = R ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      levinsonG ((((1 : ℝ) / Real.log U : ℝ)) : ℂ)
        ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      levinsonG ((((1 : ℝ) / Real.log U : ℝ)) : ℂ)
        ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
    (∫ t in T₁..T₂,
      ‖levinsonMollifiedDetector ((((1 : ℝ) / Real.log U : ℝ)) : ℂ)
        b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (c + ε) * (T₂ - T₁)

/-- Reciprocal-log windows satisfy the sign-correct gate consumed by the density theorem. -/
theorem levinsonMeanSquareGateOfYPos_of_reciprocalLogGate {R c : ℝ}
    (hgate : LevinsonReciprocalLogMeanSquareGate R c) :
    LevinsonMeanSquareGateOfYPos R c := by
  intro ε hε
  filter_upwards [hgate ε hε, eventually_ge_atTop (22 : ℝ)] with U hU hU22
  obtain ⟨T₁, T₂, σ₀, Mb, b, N, hT₁, hT₂, hN, hb1, hbn, hbreal, hMb1,
    hmass, hlogMb, hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩ := hU
  have hU20 : (20 : ℝ) ≤ U := by linarith
  have hU0 : (0 : ℝ) < U := by linarith
  have hlog : (1 : ℝ) < Real.log U := by
    rw [Real.lt_log_iff_exp_lt hU0]
    linarith [Real.exp_one_lt_d9]
  have hlog0 : (0 : ℝ) < Real.log U := by linarith
  have hlam0 : (0 : ℝ) < 1 / Real.log U := one_div_pos.mpr hlog0
  have hlam1 : |(1 : ℝ) / Real.log U| ≤ 1 := by
    rw [abs_of_pos hlam0]
    rw [div_le_iff₀ hlog0]
    linarith
  refine ⟨T₁, T₂, σ₀, 1 / Real.log U, Mb, b, N, hT₁, hT₂,
    ne_of_gt hlam0, hlam1, ?_, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb,
    hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩
  intro u hu
  exact levinsonY_line_re_pos_reciprocal_log hU20
    ⟨hT₁.1.trans hu.1, hu.2.trans hT₂.2⟩

end RHTower

end
