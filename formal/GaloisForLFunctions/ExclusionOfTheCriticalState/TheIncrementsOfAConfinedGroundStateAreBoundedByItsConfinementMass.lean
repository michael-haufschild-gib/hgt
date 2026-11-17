import GaloisForLFunctions.ExclusionOfTheCriticalState.TheModulusOfContinuityOfTheStateIsCarriedByTheWall

/-!
# The increments of a confined ground state are bounded by its confinement mass

Let `F` minimize the confined half-line form `Q_R` at a ratio `R > 0`, with ground energy
`λ(R)`, confinement coefficient `a(R)` and `M = ∫ F² e^{−8u}`.

* The weak equation gives the energy of an increment at every ratio
  (`halfLineEnergyMinimizer_fullEnergy_increment`):
  `Q_R(F − τ_k F) = λ(R) ∫ (F − τ_k F)² + a(R) (e^{8k} − 1) M`.
* The upper bound for the `L²` modulus of continuity holds at every ratio
  (`halfLineEnergyMinimizer_eventually_log_mul_sq_increment_le`): for every `ε > 0`, eventually
  as `k → 0⁺`, `log(1/k) ∫ (F(u) − F(u+k))² du ≤ (8 a(R) M + ε) k`.

Mechanism. The full energy dominates the archimedean form up to a multiple of the square mass, so
on the frequency side, with `Φ = |F̂|²` and the Gamma bracket `γ`,
`∫ (1 − cos kr) Φ γ ≤ π a (e^{8k} − 1) M + C ∫ (1 − cos kr) Φ`. The ground energy `λ(R)` only
changes the constant `C`, and the logarithmic growth of `γ` absorbs that term.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- **The energy of an increment at every ratio.** For a minimizer `F` at ratio `R` and
`k ≥ 0`, `Q_R(F − τ_k F) = λ(R) ∫ (F − τ_k F)² + a(R) (e^{8k} − 1) ∫ F² e^{−8u}`: the weak
equation evaluates the cross term and a translation changes only the confinement term. -/
theorem halfLineEnergyMinimizer_fullEnergy_increment {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {k : ℝ} (hk : 0 ≤ k) :
    criticalHalfLineFullEnergy R (fun u => F u + (-1) * F (u + k)) =
      criticalHalfLineGroundEnergy R * (∫ u, (F u - F (u + k)) ^ 2) +
        criticalAliasCoefficient R * (Real.exp (8 * k) - 1) *
          (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
  have hT := hF.1.causalTranslate hk
  have hE := criticalHalfLineFullEnergy_add_const_mul R hF.1 hT (-1)
  have hM := criticalHalfLine_square_mass_add_const_mul hF.1 hT (-1)
  have hTe := criticalHalfLineFullEnergy_comp_add_right hF.1 k R
    (fun u hu => hF.1.support _ (add_nonneg hu hk))
  have hmT : (∫ u, F (u + k) ^ 2) = 1 := by
    rw [integral_add_right_eq_self (fun u => F u ^ 2) k, hF.2.1]
  have hMd : (∫ u, (F u - F (u + k)) ^ 2) = ∫ u, (F u + (-1) * F (u + k)) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun u => by
      show (F u - F (u + k)) ^ 2 = (F u + (-1) * F (u + k)) ^ 2
      ring)
  rw [hTe, hF.2.2, hF.weakEquation hR hT] at hE
  rw [hmT, hF.2.1] at hM
  linear_combination hE - criticalHalfLineGroundEnergy R * hM -
    criticalHalfLineGroundEnergy R * hMd

/-- **The upper bound for the modulus of continuity at every ratio.** For a minimizer `F` at
ratio `R` and every `ε > 0`, eventually as `k → 0⁺`,
`log(1/k) ∫ (F(u) − F(u+k))² du ≤ (8 a(R) M + ε) k`, `M = ∫ F² e^{−8u}`. -/
theorem halfLineEnergyMinimizer_eventually_log_mul_sq_increment_le {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℝ in 𝓝[>] 0,
      Real.log (1 / k) * ∫ u, (F u - F (u + k)) ^ 2 ≤
        (8 * criticalAliasCoefficient R * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) + ε) * k := by
  have hd := hF.1
  have ha := criticalAliasCoefficient_positive hR
  have hM : 0 < ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) :=
    lt_of_lt_of_le (by rw [hF.2.1]; exact one_pos) hd.square_mass_le_exponential_mass
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = 8 * criticalAliasCoefficient R * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := ⟨_, rfl⟩
  have hQ : 0 < Q := by
    rw [hQdef]
    exact mul_pos (mul_pos (by norm_num) ha) hM
  rw [← hQdef]
  obtain ⟨B, hB0, hB⟩ := criticalHalfLineFullEnergy_arch_coercive_remainder hR
  have hG₀ := ArithmeticPositivityTheory.factorialSpanGammaOffset_nonneg
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ,
      c₀ = ArithmeticPositivityTheory.factorialSpanGammaOffset + Real.log 2 := ⟨_, rfl⟩
  have hc₀ : 0 ≤ c₀ := by
    rw [hc₀def]
    exact add_nonneg hG₀ (Real.log_nonneg (by norm_num))
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → ℝ, Φ = fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ℝ → ℝ, Ψ = fun r : ℝ => Φ r * (EF.gammaBracket r + c₀) :=
    ⟨_, rfl⟩
  have hΦr : ∀ r, Φ r = ‖paperFT (cx F) r‖ ^ 2 := fun r => by rw [hΦdef]
  have hΨr : ∀ r, Ψ r = Φ r * (EF.gammaBracket r + c₀) := fun r => by rw [hΨdef]
  have hΦ0 : ∀ r, 0 ≤ Φ r := fun r => by
    rw [hΦr r]
    exact sq_nonneg _
  have hγ0 : ∀ r, 0 ≤ EF.gammaBracket r + c₀ := fun r => by
    have h := ArithmeticPositivityTheory.gammaBracket_ge_neg_offset r
    rw [hc₀def]
    linarith only [h]
  have hΨ0 : ∀ r, 0 ≤ Ψ r := fun r => by
    rw [hΨr r]
    exact mul_nonneg (hΦ0 r) (hγ0 r)
  have hΦi : Integrable Φ := by
    rw [hΦdef]
    exact integrable_norm_sq_paperFT_cx hd.integrable hd.sq
  have hΓi : Integrable fun r : ℝ => Φ r * EF.gammaBracket r := by
    rw [hΦdef]
    exact hd.gamma
  have hΨi : Integrable Ψ := by
    have e : Ψ = fun r : ℝ => Φ r * EF.gammaBracket r + Φ r * c₀ := by
      funext r
      rw [hΨr r]
      ring
    rw [e]
    exact hΓi.add (hΦi.mul_const c₀)
  have hlog : ∀ T : ℝ, 0 < T → ∀ r : ℝ, T ≤ |r| →
      (Real.log T - ArithmeticPositivityTheory.factorialSpanGammaOffset) * Φ r ≤ Ψ r := by
    intro T hT r hr
    have h1 := mul_le_mul_of_nonneg_right
      (ArithmeticPositivityTheory.gammaBracket_ge_log_of_le_abs hT hr) (hΦ0 r)
    have h2 := mul_nonneg (hΦ0 r) hc₀
    rw [hΨr r]
    linarith only [h1, h2]
  -- the two sides of Plancherel for the increment
  have hS1 : ∀ k : ℝ, 0 ≤ k → ∫ r, (1 - Real.cos (k * r)) * Φ r =
      Real.pi * ∫ u, (F u - F (u + k)) ^ 2 := fun k hk => by
    rw [hΦdef]
    exact integral_one_sub_cos_mul_norm_sq_paperFT hd hk
  have hS2 : ∀ k : ℝ, ∫ r, (1 - Real.cos (k * r)) * (Φ r * EF.gammaBracket r) =
      Real.pi * archForm (fun u => F u + (-1) * F (u + k)) := fun k => by
    rw [hΦdef]
    exact integral_one_sub_cos_mul_norm_sq_paperFT_mul_gammaBracket hd.integrable k
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (2 * Q) := ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hηdef]
    exact div_pos hε (mul_pos (by norm_num) hQ)
  have hQη : Q * η = ε / 2 := by
    have hQ0 : Q ≠ 0 := hQ.ne'
    rw [hηdef]
    field_simp
  have hk₀ : 0 < Real.log (1 + η) / 8 :=
    div_pos (Real.log_pos (by linarith only [hη])) (by norm_num)
  -- the weighted inequality: energy of the increment plus coercivity
  have hJ : ∀ k : ℝ, 0 < k → k ≤ Real.log (1 + η) / 8 →
      ∫ r, (1 - Real.cos (k * r)) * Ψ r ≤
        Real.pi * (Q + ε / 2) * k +
          (B + |criticalHalfLineGroundEnergy R| + c₀) * ∫ r, (1 - Real.cos (k * r)) * Φ r := by
    intro k hk hkk
    have hG := hB (criticalHalfLineEnergyDomain_increment hd hk.le)
    have hsq : (∫ u, (F u + (-1) * F (u + k)) ^ 2) = ∫ u, (F u - F (u + k)) ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun u => by
        show (F u + (-1) * F (u + k)) ^ 2 = (F u - F (u + k)) ^ 2
        ring)
    rw [halfLineEnergyMinimizer_fullEnergy_increment hR hF hk.le, hsq] at hG
    have hm : 0 ≤ criticalAliasCoefficient R / 2 *
        ∫ u, (F u + (-1) * F (u + k)) ^ 2 * Real.exp (-(8 * u)) :=
      mul_nonneg (div_nonneg ha.le (by norm_num))
        (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    have hEk : criticalAliasCoefficient R * (Real.exp (8 * k) - 1) *
        (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) ≤ (Q + ε / 2) * k := by
      have h1 := mul_le_mul_of_nonneg_left (exp_eight_mul_sub_one_le hk.le hη hkk)
        (div_nonneg hQ.le (by norm_num : (0 : ℝ) ≤ 8))
      calc criticalAliasCoefficient R * (Real.exp (8 * k) - 1) *
            (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) = Q / 8 * (Real.exp (8 * k) - 1) := by
              rw [hQdef]
              ring
        _ ≤ Q / 8 * (8 * k * (1 + η)) := h1
        _ = (Q + Q * η) * k := by ring
        _ = (Q + ε / 2) * k := by rw [hQη]
    -- the ground energy enters through a multiple of the square mass of the increment
    have hD0 : 0 ≤ ∫ u, (F u - F (u + k)) ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hgr := mul_le_mul_of_nonneg_right (le_abs_self (criticalHalfLineGroundEnergy R)) hD0
    have hA : archForm (fun u => F u + (-1) * F (u + k)) ≤
        (Q + ε / 2) * k +
          (B + |criticalHalfLineGroundEnergy R|) * ∫ u, (F u - F (u + k)) ^ 2 := by
      linarith only [hG, hm, hEk, hgr]
    have hsplit : ∫ r, (1 - Real.cos (k * r)) * Ψ r =
        (∫ r, (1 - Real.cos (k * r)) * (Φ r * EF.gammaBracket r)) +
          c₀ * ∫ r, (1 - Real.cos (k * r)) * Φ r := by
      have e : (fun r => (1 - Real.cos (k * r)) * Ψ r) = fun r =>
          (1 - Real.cos (k * r)) * (Φ r * EF.gammaBracket r) +
            c₀ * ((1 - Real.cos (k * r)) * Φ r) := by
        funext r
        rw [hΨr r]
        ring
      rw [e, integral_add (integrable_one_sub_cos_mul hΓi k)
        ((integrable_one_sub_cos_mul hΦi k).const_mul c₀), integral_const_mul]
    rw [hsplit, hS2 k, hS1 k hk.le]
    have h := mul_le_mul_of_nonneg_left hA Real.pi_pos.le
    linarith only [h]
  have hmain := eventually_log_mul_spectralModulus_le hΦ0 hΨ0 hΦi hΨi hG₀ hlog
    (mul_nonneg Real.pi_pos.le (by linarith only [hQ, hε] : (0 : ℝ) ≤ Q + ε / 2))
    (add_nonneg (add_nonneg hB0 (abs_nonneg (criticalHalfLineGroundEnergy R))) hc₀) hk₀ hJ (mul_pos Real.pi_pos (half_pos hε))
  filter_upwards [hmain, self_mem_nhdsWithin] with k hk hk0
  have hk0' : (0 : ℝ) < k := hk0
  rw [hS1 k hk0'.le, mul_left_comm (Real.log (1 / k)) Real.pi] at hk
  have e : (Real.pi * (Q + ε / 2) + Real.pi * (ε / 2)) * k = Real.pi * ((Q + ε) * k) := by ring
  rw [e] at hk
  exact le_of_mul_le_mul_left hk Real.pi_pos

end GaloisForLFunctions.ExclusionOfTheCriticalState
