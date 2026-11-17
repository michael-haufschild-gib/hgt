import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalStatesFormAnOrthogonalLadder
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheMomentsOfTheStateHaveAPoleAtTheExponentOfEveryZero
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheExplicitFormulaHoldsForTwoSidedTests

/-!
# A zero of the transform left of the line blocks the totality of the translates

The causal translates `τ_t F(u) = F(u + t)`, `t ≥ 0`, of the critical state span a dense subspace of
`L²(−∞, 0)` (`criticalHalfLineGroundState_causalCyclicSubspace_eq_top`): the transform has no zero on
`Re w ≥ 0`. The confined form at the critical ratio needs density in the stronger norm
`W₈(G) = ∫ G² e^{−8u}`, and there the half-plane of the transform moves to `Re w > −4`: the evaluation
`G ↦ L G(w₀)` is `W₈`-continuous for `Re w₀ > −4`, `(2 Re w₀ + 8) |L G(w₀)|² ≤ W₈(G)`
(`mul_norm_sq_laplace_le_of_decay`), and `L(τ_t F)(w₀) = e^{−t w₀} L F(w₀)` (`laplace_shiftProfile`).

* **Obstruction** (`mul_norm_sq_laplace_le_of_orbit`, `div_le_exponentialMass_probe_sub_orbit`). For a
  profile `F` of `H` with `L F(w₀) = 0`, `Re w₀ > −4`, every finite combination `X` of translates has
  `W₈(G − X) ≥ (2 Re w₀ + 8)|L G(w₀)|²`; for the probe `e_p`, `W₈(e_p − X) ≥ (2 Re w₀ + 8)/|p + w₀|²`.
* **Totality forces a zero-free half-plane** (`laplace_ne_zero_of_orbit_dense`). If the translates of
  `F` are dense in `H` for `W₈`, then `L F` has no zero on `Re w > −4`.

For the critical state, totality of the orbit in the energy norm (which would encode the confined form
at the critical ratio in the autocorrelation `∫ F(u) F(u + d) e^{−8u} du`) therefore implies that the
transform of the state is zero-free on `Re w > −4`, a half-plane four units beyond the one
(`Re w ≥ 0`) that `L²`-cyclicity uses.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23 Complex

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory
  HTGeometry

/-- For finite confinement mass the Laplace integrand is integrable on `Re w > −4`:
`e^{Re w·u}|G| ≤ ½(G² e^{−8u} + e^{(2 Re w + 8)u})` on `u < 0`. -/
theorem integrable_laplaceIntegrand_of_exponential {G : ℝ → ℝ} (hGm : Measurable G)
    (hs : ∀ u, 0 ≤ u → G u = 0) (h8 : Integrable fun u => G u ^ 2 * Real.exp (-(8 * u)))
    {w : ℂ} (hw : -4 < w.re) : Integrable fun u : ℝ => cexp (w * (u : ℂ)) * cx G u := by
  have hc : 0 < 2 * w.re + 8 := by linarith
  have hE : Integrable ((Iio (0 : ℝ)).indicator fun u => Real.exp ((2 * w.re + 8) * u)) :=
    (integrable_indicator_iff measurableSet_Iio).2 (integrableOn_exp_mul_Iio_zero hc)
  refine ((h8.add hE).div_const 2).mono'
    (((by fun_prop : Continuous fun u : ℝ => cexp (w * (u : ℂ))).aestronglyMeasurable).mul
      (Complex.measurable_ofReal.comp hGm).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  show ‖cexp (w * (u : ℂ)) * cx G u‖ ≤ (G u ^ 2 * Real.exp (-(8 * u)) +
    (Iio (0 : ℝ)).indicator (fun u => Real.exp ((2 * w.re + 8) * u)) u) / 2
  have hre : (w * (u : ℂ)).re = w.re * u := by simp [Complex.mul_re]
  rw [norm_mul, Complex.norm_exp, hre]
  simp only [cx, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_ge u 0 with hu | hu
  · rw [indicator_of_mem (mem_Iio.mpr hu)]
    have he : Real.exp (-(4 * u)) * Real.exp ((w.re + 4) * u) = Real.exp (w.re * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have h1 : Real.exp (w.re * u) * |G u| =
        (|G u| * Real.exp (-(4 * u))) * Real.exp ((w.re + 4) * u) := by
      rw [mul_assoc, he, mul_comm]
    have h2 : (|G u| * Real.exp (-(4 * u))) ^ 2 = G u ^ 2 * Real.exp (-(8 * u)) := by
      rw [mul_pow, sq_abs, sq (Real.exp _), ← Real.exp_add]; congr 2; ring
    have h3 : Real.exp ((w.re + 4) * u) ^ 2 = Real.exp ((2 * w.re + 8) * u) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h1]
    nlinarith [sq_nonneg (|G u| * Real.exp (-(4 * u)) - Real.exp ((w.re + 4) * u))]
  · rw [hs u hu, abs_zero, mul_zero, indicator_of_notMem (show u ∉ Iio (0 : ℝ) by simp [hu])]
    positivity

/-- The transform of the probe: `L e_p(q) = 1/(p + q)` for `Re q > −p`. -/
theorem laplace_probe {p : ℝ} {q : ℂ} (hq : -p < q.re) :
    negativeHalfLineLaplace (cx (probe p)) q = 1 / ((p : ℂ) + q) := by
  unfold negativeHalfLineLaplace cx
  have h1 : (∫ u : ℝ, cexp (q * u) * (probe p u : ℂ)) =
      ∫ u in Iio (0 : ℝ), cexp (((p : ℂ) + q) * u) := by
    rw [← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rcases lt_or_ge u 0 with hu | hu
    · rw [indicator_of_mem (mem_Iio.mpr hu), probe_of_neg hu, Complex.ofReal_exp,
        ← Complex.exp_add]
      congr 1; push_cast; ring
    · rw [indicator_of_notMem (show u ∉ Iio (0 : ℝ) by simp [hu]), probe_of_nonneg hu,
        Complex.ofReal_zero, mul_zero]
  rw [h1, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_complex_Iic (by simp; linarith) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- **A zero of the transform obstructs approximation by translates.** If `L F(w₀) = 0` with
`Re w₀ > −4`, then for every profile `G` of `H` and every finite combination of causal translates,
`(2 Re w₀ + 8) |L G(w₀)|² ≤ ∫ (G − Σ c_i τ_{t_i} F)² e^{−8u}`. -/
theorem mul_norm_sq_laplace_le_of_orbit {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {w₀ : ℂ} (hw₀ : -4 < w₀.re) (hz : negativeHalfLineLaplace (cx F) w₀ = 0)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) {n : ℕ} (t : Fin n → ℝ)
    (ht : ∀ i, 0 ≤ t i) (c : Fin n → ℝ) :
    (2 * w₀.re + 8) * ‖negativeHalfLineLaplace (cx G) w₀‖ ^ 2 ≤
      ∫ u, (G u - ∑ i, c i * F (u + t i)) ^ 2 * Real.exp (-(8 * u)) := by
  have hΦ : ∀ i, CriticalHalfLineEnergyDomain (fun u => F (u + t i)) := fun i =>
    hF.causalTranslate (ht i)
  have hY := criticalHalfLineEnergyDomain_add_sum hG hΦ (fun i => -c i) Finset.univ
  have hYe : (fun u => G u + ∑ i ∈ Finset.univ, (-c i) * F (u + t i)) =
      fun u => G u - ∑ i, c i * F (u + t i) := by
    funext u; simp only [neg_mul, Finset.sum_neg_distrib]; ring
  rw [hYe] at hY
  have h := mul_norm_sq_laplace_le_of_decay hY.meas hY.support hY.exponential (w := w₀) (b := 8)
    (by linarith)
  -- the transform of the combination at w₀ is that of G
  have hint : ∀ i, Integrable fun u : ℝ => cexp (w₀ * (u : ℂ)) * cx (fun u => F (u + t i)) u :=
    fun i => integrable_laplaceIntegrand_of_exponential (hΦ i).meas (hΦ i).support
      (hΦ i).exponential hw₀
  have hiG := integrable_laplaceIntegrand_of_exponential hG.meas hG.support hG.exponential hw₀
  have htr : ∀ i, negativeHalfLineLaplace (cx fun u => F (u + t i)) w₀ = 0 := fun i => by
    have := laplace_shiftProfile F (t i) w₀
    change negativeHalfLineLaplace (cx fun u => F (u + t i)) w₀ = _ at this
    rw [this, hz, mul_zero]
  have hL : negativeHalfLineLaplace (cx fun u => G u - ∑ i, c i * F (u + t i)) w₀ =
      negativeHalfLineLaplace (cx G) w₀ := by
    have hsplit : (fun u : ℝ => cexp (w₀ * (u : ℂ)) * cx (fun u => G u - ∑ i, c i * F (u + t i)) u) =
        fun u : ℝ => cexp (w₀ * (u : ℂ)) * cx G u -
          ∑ i, (c i : ℂ) * (cexp (w₀ * (u : ℂ)) * cx (fun v => F (v + t i)) u) := by
      funext u
      simp only [cx]
      push_cast
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    unfold negativeHalfLineLaplace at htr ⊢
    rw [hsplit, integral_sub hiG (integrable_finset_sum _ fun i _ => (hint i).const_mul _),
      integral_finset_sum _ fun i _ => (hint i).const_mul _]
    simp only [integral_const_mul, htr, mul_zero, Finset.sum_const_zero, sub_zero]
  rwa [hL] at h

/-- **The probes stay at a fixed distance from the orbit.** If `L F(w₀) = 0` with `Re w₀ > −4`,
every finite combination `X` of causal translates of `F` and every `p > 4` satisfy
`W₈(e_p − X) ≥ (2 Re w₀ + 8)/|p + w₀|²`. -/
theorem div_le_exponentialMass_probe_sub_orbit {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {w₀ : ℂ} (hw₀ : -4 < w₀.re) (hz : negativeHalfLineLaplace (cx F) w₀ = 0) {p : ℝ}
    (hp : 4 < p) {n : ℕ} (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) (c : Fin n → ℝ) :
    (2 * w₀.re + 8) / ‖(p : ℂ) + w₀‖ ^ 2 ≤
      ∫ u, (probe p u - ∑ i, c i * F (u + t i)) ^ 2 * Real.exp (-(8 * u)) := by
  have h := mul_norm_sq_laplace_le_of_orbit hF hw₀ hz (criticalHalfLineEnergyDomain_probe hp) t ht c
  rwa [laplace_probe (by linarith), norm_div, norm_one, div_pow, one_pow, mul_one_div] at h

/-- **Totality of the translates forces a zero-free half-plane.** If the causal translates of a
profile `F` of `H` approximate every profile of `H` in `W₈`, then `L F(w) ≠ 0` for `Re w > −4`. -/
theorem laplace_ne_zero_of_orbit_dense {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hdense : ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (t c : Fin n → ℝ), (∀ i, 0 ≤ t i) ∧
        ∫ u, (G u - ∑ i, c i * F (u + t i)) ^ 2 * Real.exp (-(8 * u)) < ε)
    {w : ℂ} (hw : -4 < w.re) : negativeHalfLineLaplace (cx F) w ≠ 0 := by
  intro hz
  have hne : ((5 : ℝ) : ℂ) + w ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hpos : 0 < (2 * w.re + 8) / ‖((5 : ℝ) : ℂ) + w‖ ^ 2 := by
    have : 0 < 2 * w.re + 8 := by linarith
    positivity
  obtain ⟨n, t, c, ht, hlt⟩ :=
    hdense _ (criticalHalfLineEnergyDomain_probe (by norm_num : (4 : ℝ) < 5)) _ hpos
  have := div_le_exponentialMass_probe_sub_orbit hF hw hz (by norm_num : (4 : ℝ) < 5) t ht c
  linarith

end GaloisForLFunctions.ExclusionOfTheCriticalState

#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.mul_norm_sq_laplace_le_of_orbit
#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.div_le_exponentialMass_probe_sub_orbit
#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.laplace_ne_zero_of_orbit_dense
