import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalTailShift
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalFiniteShift
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalFiniteWindowBound

/-!
# Chen--Gupta--Li Lemma 6.2: principal reflected line reassembled

The principal reflected ζ-line integral is exactly its finite Dirichlet
polynomial moved to the critical line plus its complementary tail moved to
the deep line.  Both pieces truncate symmetrically at any certified radius
with an explicit two-sided power-tail error.
-/

open Complex MeasureTheory Filter Set
open scoped Topology

namespace RHTower

noncomputable section

/-- The principal reflected line integral splits exactly into its finite and
deep-tail integrals. -/
theorem cglLemma62_principal_reflected_integral_eq_finite_add_farTail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) :
    (∫ v : ℝ, cglLemma62PrincipalReflectedLineIntegrand w N Q t v) =
      (∫ v : ℝ, cglLemma62PrincipalReflectedFiniteIntegrand w N Q t M.value v) +
        ∫ v : ℝ, cglLemma62PrincipalFarTailIntegrand w N Q t M.value d v := by
  have hfinite : Integrable (fun v : ℝ =>
      cglLemma62PrincipalReflectedFiniteIntegrand w N Q t M.value v) := by
    refine (cglLemma62_principalRegularizedFinite_vertical_integrable w N Q t M.value
      (σ := -1) (by norm_num) (by norm_num)).congr ?_
    filter_upwards with v
    simpa using cglLemma62PrincipalRegularizedFiniteContourIntegrand_eq_line w N Q t v M.value
  have htail : Integrable (fun v : ℝ =>
      cglLemma62PrincipalReflectedTailIntegrand w N Q t M.value v) := by
    refine (cglLemma62_principalTail_vertical_integrable w N Q t M d (σ := -1)
      (by have : (1 : ℝ) ≤ d.value := by exact_mod_cast d.positive
          linarith) le_rfl).congr ?_
    filter_upwards with v
    simpa using cglLemma62PrincipalTailContourIntegrand_eq_line w N Q t v M.value
  calc
    (∫ v : ℝ, cglLemma62PrincipalReflectedLineIntegrand w N Q t v) =
        ∫ v : ℝ, cglLemma62PrincipalReflectedFiniteIntegrand w N Q t M.value v +
          cglLemma62PrincipalReflectedTailIntegrand w N Q t M.value v := by
            apply integral_congr_ae
            filter_upwards with v
            exact cglLemma62_principal_reflected_eq_finite_add_tail w N Q t M.value v
    _ = (∫ v : ℝ, cglLemma62PrincipalReflectedFiniteIntegrand w N Q t M.value v) +
          ∫ v : ℝ, cglLemma62PrincipalReflectedTailIntegrand w N Q t M.value v :=
      integral_add hfinite htail
    _ = _ := by rw [cglLemma62_principalReflectedTail_integral_eq_farTail w N Q t M d]

/-- The principal reflected line integral, with its finite part on the
critical line and its tail on the deep line. -/
theorem cglLemma62_principal_reflected_integral_eq_finiteCritical_add_farTail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) :
    (∫ v : ℝ, cglLemma62PrincipalReflectedLineIntegrand w N Q t v) =
      (∫ v : ℝ, cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M.value
          ((1 / 2 : ℂ) + (v : ℂ) * I)) +
        ∫ v : ℝ, cglLemma62PrincipalFarTailIntegrand w N Q t M.value d v := by
  rw [cglLemma62_principal_reflected_integral_eq_finite_add_farTail w N Q t M d,
    cglLemma62_principalReflectedFinite_integral_eq_critical]

/-- The principal finite critical-line integral differs from a certified
symmetric window by its exact two-sided Mellin power tail. -/
theorem cglLemma62_principal_finiteCritical_integral_sub_truncation_le_power
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ)
    (U : CGLLemma62TailTruncationCertificate) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
          ((1 / 2 : ℂ) + (v : ℂ) * I)) -
          ∫ v : ℝ in -U.radius..U.radius,
            cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
              ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤
        2 * C * (U.radius ^ (1 - (U.decayRate : ℝ)) / ((U.decayRate : ℝ) - 1)) := by
  let C : ℝ := cglLemma62MellinLineDecayBudget w (1 / 2) U.decayRate *
    (N.value : ℝ) ^ (1 / 2 : ℝ) * (M + 1)
  have hbudget : 0 ≤ cglLemma62MellinLineDecayBudget w (1 / 2) U.decayRate := by
    exact le_trans (by positivity) (cglLemma62_mellinTransform_vertical_rapidDecay
      w (1 / 2) U.decayRate 0)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hN : 0 ≤ (N.value : ℝ) ^ (1 / 2 : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg hbudget hN) (by positivity)
  have hintegrable := cglLemma62PrincipalRegularizedFinite_critical_integrable w N Q t M
  have hrate : (1 : ℝ) < U.decayRate := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) U.decayRate_two)
  have hradius : 0 < U.radius := lt_of_lt_of_le zero_lt_one U.radius_one
  have hbound : ∀ v : ℝ, U.radius ≤ |v| →
      ‖cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
        ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ C * |v| ^ (-(U.decayRate : ℝ)) := by
    intro v hv
    have habspos : 0 < |v| := lt_of_lt_of_le zero_lt_one (U.radius_one.trans hv)
    have hMellin : |v| ^ U.decayRate *
        ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤
          cglLemma62MellinLineDecayBudget w (1 / 2) U.decayRate := by
      simpa using cglLemma62_mellinTransform_vertical_rapidDecay w (1 / 2) U.decayRate v
    have hMellin' : ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤
        cglLemma62MellinLineDecayBudget w (1 / 2) U.decayRate / |v| ^ U.decayRate := by
      apply (le_div_iff₀ (pow_pos habspos _)).mpr
      simpa [mul_comm] using hMellin
    have hpoint :
        ‖cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
          ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ C / |v| ^ U.decayRate := by
      refine (norm_cglLemma62PrincipalRegularizedFiniteContourIntegrand_critical_le
        w N Q t M v).trans ?_
      calc
        ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ *
            (N.value : ℝ) ^ (1 / 2 : ℝ) * ((M : ℝ) + 1) ≤
          (cglLemma62MellinLineDecayBudget w (1 / 2) U.decayRate / |v| ^ U.decayRate) *
            (N.value : ℝ) ^ (1 / 2 : ℝ) * ((M : ℝ) + 1) := by
              gcongr
        _ = C / |v| ^ U.decayRate := by
          dsimp [C]
          field_simp
    calc
      _ ≤ C / |v| ^ U.decayRate := hpoint
      _ = C * |v| ^ (-(U.decayRate : ℝ)) := by
        rw [Real.rpow_neg (abs_nonneg v), Real.rpow_natCast]
        ring
  exact ⟨C, hC, RHTower.Sieve.norm_integral_sub_interval_le_powerTail
    hintegrable hC hrate hradius hbound⟩

end

end RHTower
