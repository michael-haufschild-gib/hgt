import GaloisForLFunctions.HTGeometry.ClockTube

/-!
# The step operator of the clock iteration on a tube

With several coupled transverse coordinates the transverse operator is the Laplacian of the tube,

`w ↦ (∑ᵢ ∂ᵢ² w + V w)/4`.

Its estimate in the scale is the one-variable estimate applied to each coordinate: each of the `k`
second partial derivatives costs two powers of the gap, so the derivative loss is `4k/(ρ'-ρ)²` in
place of `4/(ρ'-ρ)²`, and the potential contributes its supremum as before. That is the only change
the several-variable case makes to the Ovsyannikov recursion.

The partial derivative of an analytic function is analytic, because it is the total derivative
evaluated on a fixed coordinate vector, so the step operator preserves analyticity on the tube.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- **The partial derivative is the total derivative along a coordinate vector.** -/
theorem cpartial_eq_fderiv {w : (Fin k → ℂ) → ℂ} {z : Fin k → ℂ} (h : DifferentiableAt ℂ w z)
    (i : Fin k) : cpartial i w z = fderiv ℂ w z (Pi.single i 1) := by
  have hs : HasDerivAt (fun ζ : ℂ => Function.update z i ζ) (Pi.single i 1) (z i) := by
    have hEq : (fun ζ : ℂ => Function.update z i ζ)
        = fun ζ : ℂ => z + (ζ - z i) • (Pi.single i 1 : Fin k → ℂ) := by
      funext ζ
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [Function.update_of_ne hj]
        simp [Pi.single_eq_of_ne hj]
    rw [hEq]
    simpa using ((hasDerivAt_id (z i)).sub_const (z i)).smul_const (Pi.single i 1 : Fin k → ℂ)
  have hw : HasFDerivAt w (fderiv ℂ w z) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact h.hasFDerivAt
  have hcomp := hw.comp_hasDerivAt (z i) hs
  rw [cpartial]
  exact hcomp.deriv

/-- **The partial derivative of an analytic function is analytic.** -/
theorem analyticAt_cpartial {w : (Fin k → ℂ) → ℂ} {U : Set (Fin k → ℂ)}
    (hw : AnalyticOnNhd ℂ w U) (hU : IsOpen U) (i : Fin k) {z : Fin k → ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ (cpartial i w) z := by
  have hcomp : AnalyticAt ℂ (fun y => fderiv ℂ w y (Pi.single i 1)) z := by
    have hev := (ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).analyticAt (fderiv ℂ w z)
    exact hev.comp (hw.fderiv z hz)
  refine hcomp.congr ?_
  filter_upwards [hU.mem_nhds hz] with y hy
  exact (cpartial_eq_fderiv (hw y hy).differentiableAt i).symm

theorem analyticOnNhd_cpartial {w : (Fin k → ℂ) → ℂ} {U : Set (Fin k → ℂ)}
    (hw : AnalyticOnNhd ℂ w U) (hU : IsOpen U) (i : Fin k) :
    AnalyticOnNhd ℂ (cpartial i w) U := fun _ hz => analyticAt_cpartial hw hU i hz

/-- The right-hand side of the characteristic clock equation on a tube. -/
noncomputable def tubeStep (V w : (Fin k → ℂ) → ℂ) : (Fin k → ℂ) → ℂ :=
  fun z => ((∑ i, cpartial i (cpartial i w) z) + V z * w z) / 4

/-- **The step operator preserves analyticity.** -/
theorem analyticOnNhd_tubeStep {U : Set (Fin k → ℂ)} (hU : IsOpen U) {V w : (Fin k → ℂ) → ℂ}
    (hV : AnalyticOnNhd ℂ V U) (hw : AnalyticOnNhd ℂ w U) :
    AnalyticOnNhd ℂ (tubeStep V w) U := by
  intro z hz
  have hsecond : ∀ i : Fin k, AnalyticAt ℂ (cpartial i (cpartial i w)) z := fun i =>
    analyticAt_cpartial (analyticOnNhd_cpartial hw hU i) hU i hz
  have hsum : AnalyticAt ℂ (fun y => ∑ i, cpartial i (cpartial i w) y) z := by
    have hbase := Finset.analyticAt_sum (f := fun i : Fin k => cpartial i (cpartial i w))
      Finset.univ fun i _ => hsecond i
    have heq : (∑ n : Fin k, cpartial n (cpartial n w))
        = fun y => ∑ i, cpartial i (cpartial i w) y := by
      funext y
      simp [Finset.sum_apply]
    rwa [heq] at hbase
  exact (hsum.add ((hV z hz).mul (hw z hz))).div_const

/-- **The estimate of the step operator in the scale on a tube.** Each of the `k` coordinates costs
two powers of the gap; the potential contributes its supremum. -/
theorem norm_tubeStep_le {ρ ρ' Mv Mw : ℝ} (hρ : ρ < ρ') (hMv0 : 0 ≤ Mv)
    {V w : (Fin k → ℂ) → ℂ} (hw : DifferentiableOn ℂ w (tube k ρ'))
    (hMw : ∀ z ∈ tube k ρ', ‖w z‖ ≤ Mw) (hMv : ∀ z ∈ tube k ρ', ‖V z‖ ≤ Mv)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ) :
    ‖tubeStep V w z‖ ≤ (4 * k / (ρ' - ρ) ^ (2 : ℕ) + Mv / 4) * Mw := by
  have hgap : (0 : ℝ) < ρ' - ρ := by linarith
  have hzt : z ∈ tube k ρ' := tube_mono hρ.le hz
  have hMw0 : (0 : ℝ) ≤ Mw := le_trans (norm_nonneg _) (hMw z hzt)
  have hterm : ∀ i : Fin k, ‖cpartial i (cpartial i w) z‖ ≤ 16 * Mw / (ρ' - ρ) ^ (2 : ℕ) :=
    fun i => norm_cpartial_cpartial_le_on_tube hρ hw hMw hz i
  have hsum : ‖∑ i, cpartial i (cpartial i w) z‖ ≤ k * (16 * Mw / (ρ' - ρ) ^ (2 : ℕ)) := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ i : Fin k, ‖cpartial i (cpartial i w) z‖
        ≤ ∑ _i : Fin k, 16 * Mw / (ρ' - ρ) ^ (2 : ℕ) := Finset.sum_le_sum fun i _ => hterm i
      _ = k * (16 * Mw / (ρ' - ρ) ^ (2 : ℕ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpot : ‖V z * w z‖ ≤ Mv * Mw := by
    rw [norm_mul]
    exact mul_le_mul (hMv z hzt) (hMw z hzt) (norm_nonneg _) hMv0
  have htri : ‖(∑ i, cpartial i (cpartial i w) z) + V z * w z‖
      ≤ k * (16 * Mw / (ρ' - ρ) ^ (2 : ℕ)) + Mv * Mw :=
    le_trans (norm_add_le _ _) (add_le_add hsum hpot)
  have hdiv : ‖tubeStep V w z‖
      = ‖(∑ i, cpartial i (cpartial i w) z) + V z * w z‖ / 4 := by
    rw [tubeStep, norm_div]
    norm_num
  rw [hdiv]
  have hfinal : (k * (16 * Mw / (ρ' - ρ) ^ (2 : ℕ)) + Mv * Mw) / 4
      = (4 * k / (ρ' - ρ) ^ (2 : ℕ) + Mv / 4) * Mw := by
    field_simp
    ring
  calc ‖(∑ i, cpartial i (cpartial i w) z) + V z * w z‖ / 4
      ≤ (k * (16 * Mw / (ρ' - ρ) ^ (2 : ℕ)) + Mv * Mw) / 4 := by linarith
    _ = (4 * k / (ρ' - ρ) ^ (2 : ℕ) + Mv / 4) * Mw := hfinal

end GaloisForLFunctions.HTGeometry
