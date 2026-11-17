import GaloisForLFunctions.ExclusionOfTheCriticalState.TheWallAmplitudeIsTheDerivativeOfTheGroundEnergy

/-!
# The modulus of continuity of every confined ground state is carried by the wall

Let `F` minimize the confined half-line form at a ratio `R > 0`, with confinement coefficient
`a(R)`, `M = ∫ F² e^{−8u}` and amplitude `ℓ` at the wall, `ℓ² = 8 a(R) M`. As `k → 0⁺`:

* `(k⁻¹ ∫_{−k}^0 F)² log(1/k) → 8 a(R) M`
  (`halfLineEnergyMinimizer_tendsto_sq_terminalMean_mul_log`);
* `log(1/k)/k · ∫ (F(u) − F(u+k))² du → 8 a(R) M`
  (`halfLineEnergyMinimizer_tendsto_log_div_mul_sq_increment`): the `L²` modulus of continuity
  is `(8 a(R) M · k / log(1/k))^{1/2}` to leading order;
* `log(1/k)/k · ∫_{−k}^0 F² → 8 a(R) M`
  (`halfLineEnergyMinimizer_tendsto_log_div_mul_terminal_sq`), and the increments away from the
  wall are of lower order, `log(1/k)/k · ∫_{u ≤ −k} (F(u) − F(u+k))² du → 0`
  (`halfLineEnergyMinimizer_tendsto_log_div_mul_interior_sq_increment`).

Mechanism. The upper bound is the spectral bound for the increments at every ratio. The lower
bound is Cauchy–Schwarz on `(−k, 0)`, where `F(u + k) = 0`, and the law of the terminal mean
with the value `ℓ² = 8 a(R) M` of the amplitude.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- **The law of the terminal mean in the confinement mass.** At every ratio `R > 0`,
`(k⁻¹ ∫_{−k}^0 F)² log(1/k) → 8 a(R) ∫ F² e^{−8u}` as `k → 0⁺`: the terminal mean tends to
the amplitude on the scale `√log(1/k)`, and the squared amplitude is `8 a(R) M`. -/
theorem halfLineEnergyMinimizer_tendsto_sq_terminalMean_mul_log {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    Tendsto (fun k : ℝ => ((∫ u in Ioo (-k) 0, F u) / k) ^ 2 * Real.log (1 / k)) (𝓝[>] 0)
      (𝓝 (8 * criticalAliasCoefficient R * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) := by
  obtain ⟨ℓ, hℓ⟩ := halfLineEnergyMinimizer_exists_isWallAmplitude hR hF
  have h := (hℓ.tendsto_terminalMean hF.1.integrable).pow 2
  rw [hℓ.sq_eq hR hF] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk0 hk1
  have hk0' : (0 : ℝ) < k := hk0
  have hk1' : k < 1 := hk1
  have hL : 0 ≤ Real.log (1 / k) :=
    Real.log_nonneg (by rw [le_div_iff₀ hk0']; linarith only [hk1'])
  show ((∫ u in Ioo (-k) 0, F u) / k * Real.sqrt (Real.log (1 / k))) ^ 2 =
    ((∫ u in Ioo (-k) 0, F u) / k) ^ 2 * Real.log (1 / k)
  rw [mul_pow, Real.sq_sqrt hL]

/-- **The modulus of continuity of a confined ground state.** At every ratio `R > 0`,
`log(1/k)/k · ∫ (F(u) − F(u+k))² du → 8 a ∫ F² e^{−8u}` as `k → 0⁺`. -/
theorem halfLineEnergyMinimizer_tendsto_log_div_mul_sq_increment {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    Tendsto (fun k : ℝ => Real.log (1 / k) / k * ∫ u, (F u - F (u + k)) ^ 2) (𝓝[>] 0)
      (𝓝 (8 * criticalAliasCoefficient R * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) := by
  have hd := hF.1
  have hlow := halfLineEnergyMinimizer_tendsto_sq_terminalMean_mul_log hR hF
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = 8 * criticalAliasCoefficient R * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := ⟨_, rfl⟩
  have hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℝ in 𝓝[>] 0,
      Real.log (1 / k) * ∫ u, (F u - F (u + k)) ^ 2 ≤ (Q + ε) * k := fun ε hε => by
    rw [hQdef]
    exact halfLineEnergyMinimizer_eventually_log_mul_sq_increment_le hR hF hε
  rw [← hQdef] at hlow ⊢
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [(tendsto_order.1 hlow).1 b hb, self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk hk0 hk1
    have hk0' : (0 : ℝ) < k := hk0
    have hk1' : k < 1 := hk1
    have h1 := sq_terminalMean_mul_log_le hd.meas hd.sq hk0' hk1'
    have hL : 0 ≤ Real.log (1 / k) / k :=
      div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hk0']; linarith only [hk1'])) hk0'.le
    have h3 := mul_le_mul_of_nonneg_left (setIntegral_Ioo_sq_le_integral_sq_increment hd hk0') hL
    linarith only [hk, h1, h3]
  · have hε : 0 < (b - Q) / 2 := by linarith only [hb]
    filter_upwards [hup _ hε, self_mem_nhdsWithin] with k hk hk0
    have hk0' : (0 : ℝ) < k := hk0
    have e : Real.log (1 / k) / k * ∫ u, (F u - F (u + k)) ^ 2 =
        Real.log (1 / k) * (∫ u, (F u - F (u + k)) ^ 2) / k := by ring
    rw [e, div_lt_iff₀ hk0']
    have h2 : (Q + (b - Q) / 2) * k < b * k :=
      mul_lt_mul_of_pos_right (by linarith only [hb]) hk0'
    linarith only [hk, h2]

/-- **The terminal square mass at every ratio**: `log(1/k)/k · ∫_{−k}^0 F² → 8 a ∫ F² e^{−8u}` as `k → 0⁺`. -/
theorem halfLineEnergyMinimizer_tendsto_log_div_mul_terminal_sq {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    Tendsto (fun k : ℝ => Real.log (1 / k) / k * ∫ u in Ioo (-k) 0, F u ^ 2) (𝓝[>] 0)
      (𝓝 (8 * criticalAliasCoefficient R * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) := by
  have hd := hF.1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (halfLineEnergyMinimizer_tendsto_sq_terminalMean_mul_log hR hF)
    (halfLineEnergyMinimizer_tendsto_log_div_mul_sq_increment hR hF) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk0 hk1
    exact sq_terminalMean_mul_log_le hd.meas hd.sq hk0 hk1
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk0 hk1
    have hk0' : (0 : ℝ) < k := hk0
    have hk1' : k < 1 := hk1
    exact mul_le_mul_of_nonneg_left (setIntegral_Ioo_sq_le_integral_sq_increment hd hk0')
      (div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hk0']; linarith only [hk1'])) hk0'.le)

/-- **The modulus of continuity is carried by the wall at every ratio**: the increments away from the wall are of
lower order, `log(1/k)/k · ∫_{u ≤ −k} (F(u) − F(u+k))² du → 0` as `k → 0⁺`. -/
theorem halfLineEnergyMinimizer_tendsto_log_div_mul_interior_sq_increment {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    Tendsto (fun k : ℝ => Real.log (1 / k) / k * ∫ u in Iic (-k), (F u - F (u + k)) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hd := hF.1
  have h := (halfLineEnergyMinimizer_tendsto_log_div_mul_sq_increment hR hF).sub
    (halfLineEnergyMinimizer_tendsto_log_div_mul_terminal_sq hR hF)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk0
  have hk0' : (0 : ℝ) < k := hk0
  rw [integral_sq_increment_eq_interior_add_terminal hd.support hk0'
    (integrable_sq_increment hd hk0'.le)]
  ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
