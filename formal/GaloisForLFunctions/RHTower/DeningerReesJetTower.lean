import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The real Rees dual-conormal jet tower and its positive-time character

On the real orbifold coordinate `x = r²` the real-place flow is `x ↦ e^{-2t}x`, so the normalized
Taylor jet `j_k(f) = f^{(k)}(0)/k!` is an eigenline of weight `e^{-2kt}`: the jet tower is
diagonal for the flow.  The trace on the truncation to jets of order at most `N` is therefore the
finite geometric sum, and for positive time the full tower has character `(1 - e^{-2t})^{-1}`.

* `deningerRealJet_reesFlow` : the flow law `(6)`.
* `deningerJetTower_trace` : the finite trace `(7)`.
* `deningerJetTower_summable`, `deningerJetTower_tsum` : the character `(8)`.
-/

namespace RHTower

section ReesJetTower

/-- Deninger's real-place Rees flow on the orbifold coordinate `x = r²`. -/
noncomputable def deningerReesFlow (t x : ℝ) : ℝ := Real.exp (-2 * t) * x

/-- The normalized dual-conormal Taylor jet functional. -/
noncomputable def deningerRealJet (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  iteratedDeriv k f 0 / (Nat.factorial k : ℝ)

/-- The jet weight of the tower: the `k`-th jet is scaled by `e^{-2kt}`. -/
noncomputable def deningerJetWeight (t : ℝ) (k : ℕ) : ℝ := Real.exp (-2 * (k : ℝ) * t)

theorem deningerJetWeight_eq_pow (t : ℝ) (k : ℕ) :
    deningerJetWeight t k = (Real.exp (-2 * t)) ^ k := by
  rw [deningerJetWeight, ← Real.exp_nat_mul]
  congr 1
  ring

/-- **The flow law.**  The `k`-th dual-conormal jet is an eigenline of the Rees flow of weight
`e^{-2kt}`. -/
theorem deningerRealJet_reesFlow {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f) (t : ℝ) :
    deningerRealJet k (fun x => f (deningerReesFlow t x))
      = deningerJetWeight t k * deningerRealJet k f := by
  have hcomp : iteratedDeriv k (fun x => f (Real.exp (-2 * t) * x))
      = fun x => (Real.exp (-2 * t)) ^ k * iteratedDeriv k f (Real.exp (-2 * t) * x) :=
    iteratedDeriv_comp_const_mul hf _
  have hfun : (fun x => f (deningerReesFlow t x)) = fun x => f (Real.exp (-2 * t) * x) := rfl
  rw [deningerRealJet, hfun, hcomp]
  simp only [mul_zero]
  rw [deningerRealJet, deningerJetWeight_eq_pow]
  ring

/-- The truncated dual-conormal jet tower operator: the flow is diagonal in the jet basis. -/
noncomputable def deningerJetTowerOperator (N : ℕ) (t : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.diagonal fun k => deningerJetWeight t (k : ℕ)

/-- **The finite trace.**  On jets of order at most `N` the flow trace is the finite geometric
sum. -/
theorem deningerJetTower_trace (N : ℕ) (t : ℝ) :
    (deningerJetTowerOperator N t).trace
      = ∑ k ∈ Finset.range (N + 1), Real.exp (-2 * (k : ℝ) * t) := by
  rw [deningerJetTowerOperator, Matrix.trace_diagonal, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- The tower weights are summable for positive time. -/
theorem deningerJetTower_summable {t : ℝ} (ht : 0 < t) :
    Summable fun k : ℕ => Real.exp (-2 * (k : ℝ) * t) := by
  have hlt : Real.exp (-2 * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hnonneg : (0 : ℝ) ≤ Real.exp (-2 * t) := le_of_lt (Real.exp_pos _)
  refine (summable_geometric_of_lt_one hnonneg hlt).congr fun k => ?_
  rw [← deningerJetWeight_eq_pow, deningerJetWeight]

/-- **The positive-time character.**  The complete dual-conormal jet tower has flow character
`(1 - e^{-2t})^{-1}`. -/
theorem deningerJetTower_tsum {t : ℝ} (ht : 0 < t) :
    ∑' k : ℕ, Real.exp (-2 * (k : ℝ) * t) = (1 - Real.exp (-2 * t))⁻¹ := by
  have hlt : Real.exp (-2 * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hnonneg : (0 : ℝ) ≤ Real.exp (-2 * t) := le_of_lt (Real.exp_pos _)
  rw [← tsum_geometric_of_lt_one hnonneg hlt]
  refine tsum_congr fun k => ?_
  rw [← deningerJetWeight_eq_pow, deningerJetWeight]

/-- **The truncated traces converge to the character.** -/
theorem deningerJetTower_trace_tendsto {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun N : ℕ => (deningerJetTowerOperator N t).trace) Filter.atTop
      (nhds ((1 - Real.exp (-2 * t))⁻¹)) := by
  have hsum := deningerJetTower_summable ht
  have h : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, Real.exp (-2 * (k : ℝ) * t))
      Filter.atTop (nhds ((1 - Real.exp (-2 * t))⁻¹)) := by
    have hten := hsum.hasSum.tendsto_sum_nat
    rwa [deningerJetTower_tsum ht] at hten
  refine (h.comp (Filter.tendsto_add_atTop_nat 1)).congr fun N => ?_
  exact (deningerJetTower_trace N t).symm

/-- The complementary supported density-current tower expands in positive time: its `k`-th line has
weight `e^{2(k+1)t}`. -/
noncomputable def deningerDensityCurrentWeight (t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (2 * ((k : ℝ) + 1) * t)

theorem deningerDensityCurrentWeight_one_lt {t : ℝ} (ht : 0 < t) (k : ℕ) :
    1 < deningerDensityCurrentWeight t k := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hfac : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by linarith
  have hpos : 0 < 2 * ((k : ℝ) + 1) * t := mul_pos hfac ht
  calc (1 : ℝ) = Real.exp 0 := by simp
    _ < Real.exp (2 * ((k : ℝ) + 1) * t) := Real.exp_lt_exp.mpr hpos

end ReesJetTower

end RHTower
