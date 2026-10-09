import GaloisForLFunctions.RHTower.WeilLogShiftSampledPotentialCone

/-!
# Potential inequalities for nonnegative coefficients

Nonnegative coefficients and summable excess give convergence of every deviation
potential without any positivity assumption on the log-shift tests. On this domain,
the potential inequalities alone characterize asymptotic panel positivity. Among
nonnegative minorants of von Mangoldt, they characterize von Mangoldt itself.
-/

noncomputable section

namespace RHTower

open WeilExcess

/-- Nonnegative coefficients bound the negative deviation by `log n`; summable
excess bounds the positive deviation by its total mass. -/
theorem abs_weilDeviation_le_max_log_excess_of_nonneg {lam : ℕ → ℝ}
    (hlam : ∀ n : ℕ, 2 ≤ n → 0 ≤ lam n)
    (hexc : Summable (deviationExcess lam)) (n : ℕ) :
    |weilDeviation lam n| ≤ max (Real.log n) (∑' j, deviationExcess lam j) := by
  have hup : weilDeviation lam n ≤ ∑' j, deviationExcess lam j :=
    (le_max_left (weilDeviation lam n) 0).trans
      (hexc.le_tsum n (fun j _ => deviationExcess_nonneg lam j))
  have hlow : -Real.log n ≤ weilDeviation lam n := by
    by_cases hn : 2 ≤ n
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hs1 : 1 ≤ Real.sqrt n := by
        rw [Real.one_le_sqrt]
        exact_mod_cast (show 1 ≤ n by omega)
      have hlog := Real.log_natCast_nonneg n
      have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
        ArithmeticFunction.vonMangoldt_le_log
      have hmul : Real.log n ≤ Real.log n * Real.sqrt n :=
        le_mul_of_one_le_right hlog hs1
      rw [weilDeviation, if_pos hn, le_div_iff₀ hs]
      nlinarith only [hlam n hn, hΛ, hmul]
    · rw [weilDeviation, if_neg hn]
      exact neg_nonpos.mpr (Real.log_natCast_nonneg n)
  apply abs_le.mpr
  constructor
  · have hmax := le_max_left (Real.log n) (∑' j, deviationExcess lam j)
    linarith only [hlow, hmax]
  · exact hup.trans (le_max_right _ _)

/-- Nonnegativity and finite excess make every potential series summable,
independently of the log-shift inequalities. -/
theorem summable_potential_of_nonneg_coefficients {lam : ℕ → ℝ}
    (hlam : ∀ n : ℕ, 2 ≤ n → 0 ≤ lam n)
    (hexc : Summable (deviationExcess lam)) (y : ℝ) :
    Summable (fun n => weilDeviation lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) := by
  have hE : 0 ≤ ∑' j, deviationExcess lam j :=
    tsum_nonneg (deviationExcess_nonneg lam)
  have hgrowth : ∀ n : ℕ,
      |weilDeviation lam n| ≤ 2 * Real.log n + ∑' j, deviationExcess lam j := by
    intro n
    refine (abs_weilDeviation_le_max_log_excess_of_nonneg hlam hexc n).trans ?_
    have hlog := Real.log_natCast_nonneg n
    apply max_le <;> linarith only [hlog, hE]
  obtain ⟨D, _, hD⟩ := exists_riemannAutocorr_le
  exact summable_potential_term riemannAutocorr_nonneg hD hgrowth
    (weilDeviation_zero lam) hE y

/-- For nonnegative coefficients with summable excess, no separate convergence
premise is needed in the sampled potential criterion. -/
theorem weilLogShiftAsymptoticPositive_iff_potential_of_nonneg_coefficients
    {lam : ℕ → ℝ} (hlam : ∀ n : ℕ, 2 ≤ n → 0 ≤ lam n)
    (hexc : Summable (deviationExcess lam)) :
    WeilLogShiftAsymptoticPositive lam ↔
      ∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (Real.log m) := by
  constructor
  · intro hpos m hm
    exact logShiftAsymptotic_potential_le_of_summable_excess hpos hexc m hm
  · intro hpotential
    apply (weilLogShiftAsymptoticPositive_iff_sampled_potential hexc).mpr
    intro m hm
    exact ⟨summable_potential_of_nonneg_coefficients hlam hexc _, hpotential m hm⟩

/-- Among nonnegative minorants, the potential inequalities hold exactly for
von Mangoldt. Summability need not be assumed: the excess vanishes identically. -/
theorem nonneg_minorant_potential_iff_exact {lam : ℕ → ℝ}
    (hlam : ∀ n : ℕ, 2 ≤ n → 0 ≤ lam n)
    (hminor : ∀ n : ℕ, 2 ≤ n → lam n ≤ ArithmeticFunction.vonMangoldt n) :
    (∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (Real.log m)) ↔
      ∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  constructor
  · intro hpotential
    have hezero : ∀ n : ℕ, deviationExcess lam n = 0 := by
      intro n
      apply max_eq_right
      unfold weilDeviation
      split_ifs with hn
      · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hminor n hn))
          (Real.sqrt_nonneg _)
      · exact le_rfl
    have hefun : deviationExcess lam = (fun _ : ℕ => (0 : ℝ)) := funext hezero
    have hexc : Summable (deviationExcess lam) :=
      summable_zero.congr (fun n => (hezero n).symm)
    have hpos :=
      (weilLogShiftAsymptoticPositive_iff_potential_of_nonneg_coefficients hlam hexc).mpr
        hpotential
    intro n hn
    have hab := abs_weilDeviation_le_total_excess_of_logShiftAsymptoticPositive hpos hexc n
    rw [hefun, tsum_zero, mul_zero] at hab
    have ha : weilDeviation lam n = 0 := abs_eq_zero.mp (le_antisymm hab (abs_nonneg _))
    rw [weilDeviation, if_pos hn] at ha
    have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt
      (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega)))
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp ha).resolve_right hs)
  · intro heq
    have hafun : weilDeviation lam = (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      unfold weilDeviation
      split_ifs with hn
      · rw [heq n hn, sub_self, zero_div]
      · rfl
    have hpotential : ∀ y : ℝ, deviationPotential lam y = 0 := by
      intro y
      unfold deviationPotential
      simp only [hafun, zero_mul, tsum_zero]
    intro m _
    rw [hpotential, hpotential]

end RHTower
