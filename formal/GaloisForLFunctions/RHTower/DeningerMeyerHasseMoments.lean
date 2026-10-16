import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogOperatorContinuity
import GaloisForLFunctions.RHTower.DeningerMeyerCausalDivision
import GaloisForLFunctions.RHTower.DeningerCollarExchange

/-! # Uniform admission of all native Mellin Hasse orders

Factorial normalization pays every order using one original source weight.
One application of the actual generator then pays spectral decay uniformly
in the Hasse order. These estimates are the admission step for the full
source Hilbert realization, not a positivity or zero-location condition.
-/

noncomputable section
open Complex MeasureTheory Set

namespace RHTower

def deningerMeyerHasseMoment (g : DeningerMeyerStrongLogTarget) (j : ℕ) (s : ℂ) : ℂ :=
  deningerMeyerStrongLogMellinJetLM j s g / (j.factorial : ℂ)

def deningerMeyerHasseSourceMass (g : DeningerMeyerStrongLogTarget) : ℝ :=
  ∫ t : ℝ, Real.exp (2 * |t|) * ‖g.val t‖

theorem integrable_deningerMeyerHasseSourceMass (g : DeningerMeyerStrongLogTarget) :
    Integrable (fun t : ℝ => Real.exp (2 * |t|) * ‖g.val t‖) := by
  simpa using integrable_deningerMeyerStrongLogAbsMoment g.property 0 2

theorem deningerMeyerHasseSourceMass_nonneg (g : DeningerMeyerStrongLogTarget) :
    0 ≤ deningerMeyerHasseSourceMass g :=
  integral_nonneg fun _ => by positivity

theorem deningerMeyerHasseMoment_norm_le (g : DeningerMeyerStrongLogTarget)
    (j : ℕ) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖deningerMeyerHasseMoment g j s‖ ≤ deningerMeyerHasseSourceMass g := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hbound : ‖deningerMeyerStrongLogMellinJetLM j s g‖ ≤
      (j.factorial : ℝ) * deningerMeyerHasseSourceMass g := by
    have hi := (integrable_deningerMeyerHasseSourceMass g).const_mul (j.factorial : ℝ)
    have hb := norm_integral_le_of_norm_le hi (f := deningerMeyerStrongLogMellinJet j s g.val)
      (Filter.Eventually.of_forall fun t => by
        rw [norm_deningerMeyerStrongLogMellinJet]
        have hp := deningerPow_le_factorial_mul_exp j t
        rw [Real.norm_eq_abs] at hp
        have he : Real.exp (s.re * t) ≤ Real.exp |t| := by
          apply Real.exp_le_exp.mpr
          by_cases ht : 0 ≤ t
          · rw [abs_of_nonneg ht]
            nlinarith
          · rw [abs_of_neg (lt_of_not_ge ht)]
            nlinarith
        calc
          |t| ^ j * Real.exp (s.re * t) * ‖g.val t‖ ≤
              ((j.factorial : ℝ) * Real.exp |t|) * Real.exp |t| * ‖g.val t‖ := by
                gcongr
          _ = (j.factorial : ℝ) * (Real.exp (2 * |t|) * ‖g.val t‖) := by
            rw [show 2 * |t| = |t| + |t| by ring, Real.exp_add]
            ring)
    simpa only [deningerMeyerStrongLogMellinJetLM, LinearMap.coe_mk, AddHom.coe_mk,
      integral_const_mul, deningerMeyerHasseSourceMass] using hb
  rw [deningerMeyerHasseMoment, norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ hf).mpr (by simpa [mul_comm] using hbound)

private theorem iteratedDeriv_mul_coordinate_succ
    (g : DeningerMeyerStrongLogTarget) (j : ℕ) (s : ℂ) :
    iteratedDeriv (j + 1) ((fun z : ℂ => z) * deningerMeyerStrongLogMellin g) s =
      s * iteratedDeriv (j + 1) (deningerMeyerStrongLogMellin g) s +
        (j + 1 : ℕ) * iteratedDeriv j (deningerMeyerStrongLogMellin g) s := by
  rw [iteratedDeriv_mul (by fun_prop)
    (analyticOnNhd_deningerMeyerStrongLogMellin g.property s (mem_univ _)).contDiffAt]
  have hid (i : ℕ) : iteratedDeriv i (fun z : ℂ => z) s =
      (if i = 0 then s else 0) + (if i = 1 then 1 else 0) := by
    simp only [iteratedDeriv_fun_id]
    split_ifs <;> simp_all
  simp_rw [hid, mul_add, add_mul, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_add_distrib]
  simp

theorem deningerMeyerHasseMoment_generator_zero (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerHasseMoment (deningerMeyerStrongLogGenerator g) 0 s =
      s * deningerMeyerHasseMoment g 0 s := by
  simpa only [deningerMeyerHasseMoment, deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] using
      deningerMeyerStrongLogGenerator_mellin g s

theorem deningerMeyerHasseMoment_generator_succ (g : DeningerMeyerStrongLogTarget)
    (j : ℕ) (s : ℂ) :
    deningerMeyerHasseMoment (deningerMeyerStrongLogGenerator g) (j + 1) s =
      s * deningerMeyerHasseMoment g (j + 1) s + deningerMeyerHasseMoment g j s := by
  have hfun : deningerMeyerStrongLogMellin (deningerMeyerStrongLogGenerator g) =
      (fun z : ℂ => z) * deningerMeyerStrongLogMellin g := by
    funext z
    exact deningerMeyerStrongLogGenerator_mellin g z
  simp only [deningerMeyerHasseMoment, deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  rw [hfun, iteratedDeriv_mul_coordinate_succ, Nat.factorial_succ]
  push_cast
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  field_simp

def deningerMeyerHasseSourceCost (g : DeningerMeyerStrongLogTarget) : ℝ :=
  2 * deningerMeyerHasseSourceMass g +
    deningerMeyerHasseSourceMass (deningerMeyerStrongLogGenerator g)

theorem deningerMeyerHasseSourceCost_nonneg (g : DeningerMeyerStrongLogTarget) :
    0 ≤ deningerMeyerHasseSourceCost g := by
  unfold deningerMeyerHasseSourceCost
  exact add_nonneg (mul_nonneg (by norm_num) (deningerMeyerHasseSourceMass_nonneg g))
    (deningerMeyerHasseSourceMass_nonneg _)

theorem deningerMeyerHasseMoment_decay (g : DeningerMeyerStrongLogTarget)
    (j : ℕ) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    (1 + ‖s‖) * ‖deningerMeyerHasseMoment g j s‖ ≤ deningerMeyerHasseSourceCost g := by
  have hb := deningerMeyerHasseMoment_norm_le g j h0 h1
  have hA := deningerMeyerHasseMoment_norm_le (deningerMeyerStrongLogGenerator g) j h0 h1
  have hs : ‖s‖ * ‖deningerMeyerHasseMoment g j s‖ ≤
      deningerMeyerHasseSourceMass (deningerMeyerStrongLogGenerator g) +
        deningerMeyerHasseSourceMass g := by
    cases j with
    | zero =>
      rw [← norm_mul, ← deningerMeyerHasseMoment_generator_zero]
      linarith [deningerMeyerHasseSourceMass_nonneg g]
    | succ j =>
      have he := deningerMeyerHasseMoment_generator_succ g j s
      have hm : s * deningerMeyerHasseMoment g (j + 1) s =
          deningerMeyerHasseMoment (deningerMeyerStrongLogGenerator g) (j + 1) s -
            deningerMeyerHasseMoment g j s := by rw [he]; ring
      rw [← norm_mul, hm]
      exact (norm_sub_le _ _).trans (add_le_add hA (deningerMeyerHasseMoment_norm_le g j h0 h1))
  dsimp [deningerMeyerHasseSourceCost]
  nlinarith

end RHTower
