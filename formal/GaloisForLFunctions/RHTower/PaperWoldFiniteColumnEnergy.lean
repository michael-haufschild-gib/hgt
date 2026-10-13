import GaloisForLFunctions.RHTower.PaperWoldPrimePhaseColumn
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Continuous finite-column energy and phase-uniform boundary growth

The literal arithmetic entries are continuous in the exponent. Their finite
column energy gives a norm bound independent of all unit phases. The divergent
prime-column floor at the endpoint therefore forces large norms nearby.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

def paperWoldFiniteColumnEnergy (t : ℝ) (S : Finset ℕ) (j : ℕ) : ℝ :=
  ∑ n ∈ S, ‖paperWoldDirectedKernel t (n, j)‖ ^ 2

theorem paperWoldDirectedKernel_continuous (n j : ℕ) :
    Continuous (fun t : ℝ => paperWoldDirectedKernel t (n, j)) := by
  by_cases h : n < j
  · simp only [paperWoldDirectedKernel, if_pos h]
    exact Complex.continuous_ofReal.comp
      ((((Real.continuous_const_rpow (a := (n : ℝ) + 1) (by positivity)).comp
        (continuous_const.mul continuous_id)).mul_const
        (xiHeatCassiniWoldNatIncrement n)).mul_const (xiHeatCassiniWoldNatIncrement j))
  · simpa only [paperWoldDirectedKernel, if_neg h] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))

theorem paperWoldFiniteColumnEnergy_continuous (S : Finset ℕ) (j : ℕ) :
    Continuous (fun t => paperWoldFiniteColumnEnergy t S j) :=
  continuous_finsetSum S (fun n _ => (paperWoldDirectedKernel_continuous n j).norm.pow 2)

/-- A finite source-column budget is shared by every bounded unit-phase realization. -/
theorem paperWoldFiniteColumnEnergy_le_norm_sq (t : ℝ) (u : PaperWoldUnitPhase)
    (T : PaperWoldPhaseRealization t u) (S : Finset ℕ) (j : ℕ) :
    paperWoldFiniteColumnEnergy t S j ≤ ‖T.val‖ ^ 2 := by
  have he : paperWoldFiniteColumnEnergy t S j ≤ ‖T.val (lp.single 2 j 1)‖ ^ 2 := by
    simpa only [paperWoldFiniteColumnEnergy, ENNReal.toReal_ofNat, Real.rpow_two,
      paperWoldPhaseRealization_single_norm t u T] using
      lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
        (T.val (lp.single 2 j 1)) S
  have hb : ‖T.val (lp.single 2 j 1)‖ ≤ ‖T.val‖ := by
    simpa only [lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one, mul_one] using
      T.val.le_opNorm (lp.single 2 j 1)
  exact he.trans (pow_le_pow_left₀ (norm_nonneg _) hb 2)

theorem paperWoldPrimeColumnFloor_tendsto :
    Tendsto (fun N : ℕ => Real.log N ^ 3 / (2 * 4096 ^ 2)) atTop atTop := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3)).comp hlog).atTop_div_const
    (by norm_num : (0 : ℝ) < 2 * 4096 ^ 2)
  simpa only [Function.comp_def,
    show ∀ x : ℝ, x ^ (3 : ℝ) = x ^ 3 from fun x => Real.rpow_natCast x 3] using hp

/-- Arbitrarily large energy is already present in finite native columns at the endpoint. -/
theorem paperWoldFiniteColumnEnergy_endpoint_unbounded (C : ℝ) :
    ∃ (S : Finset ℕ) (j : ℕ), C < paperWoldFiniteColumnEnergy (3 / 4) S j := by
  obtain ⟨N, he, hN, hlarge⟩ :=
    ((paperWold_eventual_prime_column_energy ⟨3 / 4, le_rfl⟩).and
      (paperWoldPrimeIndices_eventual_pair_card.and
        (paperWoldPrimeColumnFloor_tendsto.eventually (eventually_gt_atTop C)))).exists
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcp : (0 : ℝ) < ((paperWoldPrimeIndices (2 * N)).card : ℝ) :=
    lt_of_lt_of_le (div_pos hNp (by linarith [hN.2.1])) hN.2.2.2
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < (paperWoldPrimeIndices (2 * N)).card by
    exact_mod_cast hcp)
  exact ⟨paperWoldPrimeIndices N, j, hlarge.trans_le (he j hj)⟩

/-- Approaching the endpoint forces a common norm floor for every choice of unit phases. -/
theorem paperWoldPhaseRealization_norm_eventually_large (C : ℝ) :
    ∀ᶠ t : ℝ in 𝓝 (3 / 4), ∀ (u : PaperWoldUnitPhase)
      (T : PaperWoldPhaseRealization t u), C < ‖T.val‖ := by
  obtain ⟨S, j, he⟩ := paperWoldFiniteColumnEnergy_endpoint_unbounded (C ^ 2)
  filter_upwards [(paperWoldFiniteColumnEnergy_continuous S j).continuousAt.eventually
    (Ioi_mem_nhds he)] with t ht
  intro u T
  by_contra h
  have hb := (paperWoldFiniteColumnEnergy_le_norm_sq t u T S j).trans
    (pow_le_pow_left₀ (norm_nonneg _) (le_of_not_gt h) 2)
  exact (not_lt_of_ge hb) ht

end
end RHTower
