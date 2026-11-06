import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheFejerBudget

/-!
# The Fejér budget at the edge of absolute convergence

The Fejér polynomial is finite, so the budget of an off-line zero extends by continuity from `a > ½`
to `a = ½`, that is to the line `Re s = 1`, where the Dirichlet coefficients are `Λ(n)/n`
(`budget_at_edge`). The left side is `2(2 − 4(1 − e^{−L/2})/L)`.
-/

open Complex MeasureTheory Set Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

open _root_.RHTower GaloisForLFunctions.HTGeometry

noncomputable section

variable {L : ℝ} {N : ℕ}

/-- Past the band only finitely many cosines remain. -/
theorem primeSum_eq_sum (hL : 0 < L) (hN : ∀ n, N ≤ n → L ≤ Real.log n) (σ γ : ℝ) :
    primeSum σ L γ = ∑ n ∈ Finset.range N,
      primeCoeff σ n * triangleFn L (Real.log n) * Real.cos (γ * Real.log n) := by
  refine tsum_eq_sum fun n hn => ?_
  have hn' : N ≤ n := by simpa using hn
  have h := hN n hn'
  rw [triangleFn_eq_zero hL (by rw [abs_of_pos (hL.trans_le h)]; exact h)]
  ring

private theorem continuousAt_primeCoeff (n : ℕ) :
    ContinuousAt (fun a : ℝ => primeCoeff (1 / 2 + a) n) (1 / 2) := by
  by_cases hn : n = 0
  · subst hn
    simp only [primeCoeff, ArithmeticFunction.map_zero, zero_mul]
    exact continuousAt_const
  · unfold primeCoeff
    refine continuousAt_const.mul ?_
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    exact (Real.continuous_const_rpow hn0).continuousAt.comp (f := fun a : ℝ => -(1 / 2 + a))
      (by fun_prop)

private theorem primeCoeff_one (n : ℕ) : primeCoeff (1 / 2 + 1 / 2) n = vonMangoldt n / n := by
  unfold primeCoeff
  rw [show -(1 / 2 + 1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one, div_eq_mul_inv]

/-- **The budget on the line `Re s = 1`.** -/
theorem budget_at_edge (hL : 0 < L) (hN : ∀ n, N ≤ n → L ≤ Real.log n) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) {γ : ℝ} (hγq : (q.1 : ℂ).im = γ) (hγ4 : 4 ≤ γ) :
    2 * (2 - 4 * (1 - Real.exp (-(L / 2))) / L) ≤
      1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 + 8 / L / γ ^ 2 +
        9 / (2 * Real.pi * L) / γ -
        ∑ n ∈ Finset.range N, vonMangoldt n / n * triangleFn L (Real.log n) *
          Real.cos (γ * Real.log n) := by
  have hπ := Real.pi_pos
  have hγ : 0 < γ := by linarith only [hγ4]
  let F : ℝ → ℝ := fun a =>
    archBudget a L γ - ∑ n ∈ Finset.range N, primeCoeff (1 / 2 + a) n *
      triangleFn L (Real.log n) * Real.cos (γ * Real.log n) -
      2 * (1 / a - (1 - Real.exp (-a * L)) / (a ^ 2 * L))
  -- Nonnegative right of the edge.
  have hF : ∀ᶠ a in 𝓝[>] (1 / 2 : ℝ), 0 ≤ F a := by
    filter_upwards [Ioo_mem_nhdsGT (show (1 / 2 : ℝ) < 1 by norm_num)] with a ha
    have ha0 : 0 < a := by linarith only [ha.1]
    have h2 : 4 * (1 + (1 / 2 + a) / 2) ^ 2 ≤ γ ^ 2 := by
      have h3 : 1 + (1 / 2 + a) / 2 ≤ 2 := by linarith only [ha.2]
      have h4 : 0 ≤ 1 + (1 / 2 + a) / 2 := by linarith only [ha0]
      nlinarith only [h3, h4, hγ4]
    have h := two_mul_fejerLaplace_le_of_offLine ha.1 hL q hoff hγq (by linarith only [hγ4]) h2
    rw [primeSum_eq_sum hL hN, fejerLaplace_eq hL ha0] at h
    simp only [F]
    linarith only [h]
  -- Continuous at the edge.
  have hcont : ContinuousAt F (1 / 2) := by
    have h1 : ContinuousAt (fun a : ℝ => archBudget a L γ) (1 / 2) := by
      unfold archBudget
      have h2 : ContinuousAt (fun a : ℝ => Real.log ((1 + (1 / 2 + a) / 2) ^ 2 + γ ^ 2 / 4)) (1 / 2) :=
        ContinuousAt.log (by fun_prop) (by positivity)
      have h3 : ContinuousAt (fun a : ℝ => 1 / (240 * (1 + (1 / 2 + a) / 2) ^ 4)) (1 / 2) :=
        ContinuousAt.div₀ continuousAt_const (by fun_prop) (by norm_num)
      have h4 : ContinuousAt (fun a : ℝ => (4 * (a - 1 / 2) + 8 / L) / γ ^ 2) (1 / 2) := by fun_prop
      exact (((((continuousAt_const.mul h2).sub continuousAt_const).add h3).add h4).add
        continuousAt_const)
    have h5 : ContinuousAt (fun a : ℝ => ∑ n ∈ Finset.range N, primeCoeff (1 / 2 + a) n *
        triangleFn L (Real.log n) * Real.cos (γ * Real.log n)) (1 / 2) := by
      refine tendsto_finsetSum _ fun n _ => ?_
      exact ((continuousAt_primeCoeff n).mul continuousAt_const).mul continuousAt_const
    have h6 : ContinuousAt (fun a : ℝ => 1 / a - (1 - Real.exp (-a * L)) / (a ^ 2 * L)) (1 / 2) := by
      refine (ContinuousAt.div₀ continuousAt_const continuousAt_id (by norm_num)).sub
        (ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by positivity))
    exact (h1.sub h5).sub (continuousAt_const.mul h6)
  have hlim := ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hF
  simp only [F] at hlim
  have e1 : archBudget (1 / 2) L γ = 1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 +
      1 / 1215 + 8 / L / γ ^ 2 + 9 / (2 * Real.pi * L) / γ := by
    unfold archBudget
    norm_num
  have e2 : 1 / (1 / 2 : ℝ) - (1 - Real.exp (-(1 / 2) * L)) / ((1 / 2) ^ 2 * L) =
      2 - 4 * (1 - Real.exp (-(L / 2))) / L := by
    rw [show -(1 / 2 : ℝ) * L = -(L / 2) by ring]
    field_simp
    ring
  rw [e1, e2] at hlim
  simp_rw [primeCoeff_one] at hlim
  linarith only [hlim]

end

end GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget
