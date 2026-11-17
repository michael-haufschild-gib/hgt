import GaloisForLFunctions.ExclusionOfTheCriticalState.TheSignOfTheStateAtTheWallIsTheSignOfItsHalfCharge
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyNormControlsTheValuesAtTheZeros
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineTranslationEnergy
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialSpanTestPolarPrimeGammaBudgets

/-!
# The modulus of continuity of the state is carried by the wall

Let `F` be the critical state, `a` the alias coefficient and `M = ∫ F² e^{−8u}`. As `k → 0⁺`:

* `log(1/k)/k · ∫ (F(u) − F(u+k))² du → 8aM` (`criticalState_tendsto_log_div_mul_sq_increment`):
  the `L²` modulus of continuity of the state is `(8aM · k / log(1/k))^{1/2}` to leading order;
* `log(1/k)/k · ∫_{−k}^0 F² → 8aM` (`criticalState_tendsto_log_div_mul_terminal_sq`), and the
  increments away from the wall are of lower order,
  `log(1/k)/k · ∫_{u ≤ −k} (F(u) − F(u+k))² du → 0`
  (`criticalState_tendsto_log_div_mul_interior_sq_increment`);
* the state is flat on `(−k, 0)` in mean square: with the terminal mean `μ(k)`,
  `log(1/k)/k · ∫_{−k}^0 (F − μ(k))² → 0` (`criticalState_tendsto_log_div_mul_terminal_variance`);
* the law of the wall in mean square (`criticalState_meanSquare_wall_law`): with the sign `s` of the
  state at the wall, `k⁻¹ ∫_{−k}^0 (√log(1/k) F(u) − s√(8aM))² du → 0`; hence
  `√log(1/k) F → s√(8aM)` in measure on `(−k, 0)`, and `F` has the sign `s` on a subset of
  `(−k, 0)` of density tending to one.

Mechanism. The weak equation gives the exact energy of an increment,
`E(F − τ_k F) = a (e^{8k} − 1) M`, and the full energy dominates the archimedean form up to a
multiple of the square mass. On the frequency side, with `Φ = |F̂|²` and the Gamma bracket `γ`,
`∫ (1 − cos kr) Φ γ ≤ π a (e^{8k} − 1) M + C ∫ (1 − cos kr) Φ`. Since `γ(r) ≥ log R − G₀` on
`|r| ≥ R`, the part `|r| ≥ T = 1/(Ak)` of `∫ (1 − cos kr) Φ` is at most `(log T − G₀)⁻¹` times the
left side, and the part `|r| ≤ T` is at most `k² ∫_{|r| ≤ T} r² Φ`, which the same inequality at
the scales `1/T` and `1/√T` bounds by `O(T / log T)` with a constant independent of `A`.
Letting `A → ∞` gives the upper bound with the constant `8aM`. The matching lower bound is
Cauchy–Schwarz on `(−k, 0)` and the law of the terminal mean `μ(k)² log(1/k) → 8aM`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### A logarithmic weight on the frequency side forces a logarithmic gain of the modulus -/

/-- `x²/4 ≤ 1 − cos x` for `|x| ≤ 1`. -/
theorem sq_div_four_le_one_sub_cos {x : ℝ} (hx : |x| ≤ 1) : x ^ 2 / 4 ≤ 1 - Real.cos x := by
  have h := (abs_le.mp (Real.cos_bound hx)).2
  have h4 : |x| ^ 4 ≤ x ^ 2 := by
    have h2 : |x| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
    calc |x| ^ 4 = |x| ^ 2 * |x| ^ 2 := by ring
      _ ≤ |x| ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = x ^ 2 := by rw [mul_one, sq_abs]
  nlinarith only [h, h4, sq_nonneg x]

/-- The multiplier `r²` on `|r| ≤ T`, zero beyond. -/
def lowSq (T r : ℝ) : ℝ := if |r| ≤ T then r ^ 2 else 0

theorem measurable_lowSq (T : ℝ) : Measurable (lowSq T) :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    (measurable_id.pow_const 2) measurable_const

theorem lowSq_nonneg (T r : ℝ) : 0 ≤ lowSq T r := by
  unfold lowSq
  split_ifs
  · positivity
  · exact le_rfl

theorem lowSq_le (T r : ℝ) : lowSq T r ≤ T ^ 2 := by
  unfold lowSq
  split_ifs with h
  · rw [← sq_abs r]
    exact pow_le_pow_left₀ (abs_nonneg r) h 2
  · positivity

theorem integrable_mul_of_bdd {Φ m : ℝ → ℝ} (hΦ : Integrable Φ) (hm : Measurable m) {C : ℝ}
    (hmC : ∀ r, |m r| ≤ C) : Integrable fun r => m r * Φ r := by
  refine Integrable.mono' (hΦ.norm.const_mul C)
    (hm.aestronglyMeasurable.mul hΦ.aestronglyMeasurable) (Eventually.of_forall fun r => ?_)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hmC r) (norm_nonneg _)

theorem one_sub_cos_mul_nonneg (k r : ℝ) : 0 ≤ 1 - Real.cos (k * r) :=
  sub_nonneg.mpr (Real.cos_le_one _)

theorem one_sub_cos_mul_le_sq (k r : ℝ) : 1 - Real.cos (k * r) ≤ k ^ 2 / 2 * r ^ 2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := k * r)
  have e : (k * r) ^ 2 / 2 = k ^ 2 / 2 * r ^ 2 := by ring
  linarith only [h, e]

theorem integrable_one_sub_cos_mul {Φ : ℝ → ℝ} (hΦ : Integrable Φ) (k : ℝ) :
    Integrable fun r => (1 - Real.cos (k * r)) * Φ r :=
  integrable_mul_of_bdd (C := 2) hΦ
    (measurable_const.sub (Real.measurable_cos.comp (measurable_const.mul measurable_id)))
    fun r => by
      rw [abs_of_nonneg (one_sub_cos_mul_nonneg k r)]
      linarith only [Real.neg_one_le_cos (k * r)]

theorem integrable_lowSq_mul {Φ : ℝ → ℝ} (hΦ : Integrable Φ) (T : ℝ) :
    Integrable fun r => lowSq T r * Φ r :=
  integrable_mul_of_bdd hΦ (measurable_lowSq T) fun r => by
    rw [abs_of_nonneg (lowSq_nonneg T r)]
    exact lowSq_le T r

/-- Step 1: the weighted modulus is linear in `k`, and far frequencies are paid by the weight. -/
theorem exists_weightedModulus_le_linear {Φ Ψ : ℝ → ℝ} (hΦ0 : ∀ r, 0 ≤ Φ r)
    (hΨ0 : ∀ r, 0 ≤ Ψ r) (hΦ : Integrable Φ) (hΨ : Integrable Ψ) {G₀ : ℝ}
    (hlog : ∀ R : ℝ, 0 < R → ∀ r : ℝ, R ≤ |r| → (Real.log R - G₀) * Φ r ≤ Ψ r)
    {P B k₀ : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hJ : ∀ k : ℝ, 0 < k → k ≤ k₀ →
      ∫ r, (1 - Real.cos (k * r)) * Ψ r ≤ P * k + B * ∫ r, (1 - Real.cos (k * r)) * Φ r) :
    ∃ R₀ q C₄ : ℝ, 0 < R₀ ∧ 0 < q ∧ q ≤ 1 ∧ 0 ≤ C₄ ∧ (∀ r : ℝ, R₀ ≤ |r| → Φ r ≤ q * Ψ r) ∧
      ∀ k : ℝ, 0 < k → k ≤ k₀ → k ≤ 1 → ∫ r, (1 - Real.cos (k * r)) * Ψ r ≤ C₄ * k := by
  obtain ⟨N₀, hN₀def⟩ : ∃ N₀ : ℝ, N₀ = ∫ r, Φ r := ⟨_, rfl⟩
  have hN₀ : 0 ≤ N₀ := by
    rw [hN₀def]
    exact integral_nonneg hΦ0
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = Real.exp (G₀ + 2 * B + 1) := ⟨_, rfl⟩
  have hR₀ : 0 < R₀ := by
    rw [hR₀def]
    exact Real.exp_pos _
  have hℓ₀ : Real.log R₀ - G₀ = 2 * B + 1 := by
    rw [hR₀def, Real.log_exp]
    ring
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (2 * B + 1)⁻¹ := ⟨_, rfl⟩
  have hq1 : q * (2 * B + 1) = 1 := by
    rw [hqdef]
    exact inv_mul_cancel₀ (by linarith only [hB])
  have hq0 : 0 < q := by
    rw [hqdef]
    exact inv_pos.mpr (by linarith only [hB])
  have hq1' : 2 * (q * B) + q = 1 := by
    rw [← hq1]
    ring
  have hqB0 : 0 ≤ q * B := mul_nonneg hq0.le hB
  have hqle : q ≤ 1 := by linarith only [hq1', hqB0]
  have hqB : q * B ≤ 1 / 2 := by linarith only [hq1', hq0]
  have hfar : ∀ r : ℝ, R₀ ≤ |r| → Φ r ≤ q * Ψ r := fun r hr => by
    have h1 := hlog R₀ hR₀ r hr
    rw [hℓ₀] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hq0.le
    rw [← mul_assoc, hq1, one_mul] at h2
    exact h2
  have step1 : ∀ k : ℝ, 0 < k → k ≤ k₀ → k ≤ 1 →
      ∫ r, (1 - Real.cos (k * r)) * Φ r ≤ (R₀ ^ 2 * N₀ + 2 * P) * k := by
    intro k hk hkk₀ hk1
    have hpt : ∀ r : ℝ, (1 - Real.cos (k * r)) * Φ r ≤
        k ^ 2 / 2 * R₀ ^ 2 * Φ r + q * ((1 - Real.cos (k * r)) * Ψ r) := by
      intro r
      have t1 : 0 ≤ k ^ 2 / 2 * R₀ ^ 2 * Φ r := mul_nonneg (by positivity) (hΦ0 r)
      have t2 : 0 ≤ q * ((1 - Real.cos (k * r)) * Ψ r) :=
        mul_nonneg hq0.le (mul_nonneg (one_sub_cos_mul_nonneg k r) (hΨ0 r))
      rcases lt_or_ge |r| R₀ with hr | hr
      · have hr2 : r ^ 2 ≤ R₀ ^ 2 := by
          rw [← sq_abs r]
          exact pow_le_pow_left₀ (abs_nonneg r) hr.le 2
        have h1 : 1 - Real.cos (k * r) ≤ k ^ 2 / 2 * R₀ ^ 2 :=
          (one_sub_cos_mul_le_sq k r).trans (mul_le_mul_of_nonneg_left hr2 (by positivity))
        have h2 := mul_le_mul_of_nonneg_right h1 (hΦ0 r)
        linarith only [h2, t2]
      · have h2 := mul_le_mul_of_nonneg_left (hfar r hr) (one_sub_cos_mul_nonneg k r)
        have e : (1 - Real.cos (k * r)) * (q * Ψ r) =
            q * ((1 - Real.cos (k * r)) * Ψ r) := by ring
        linarith only [h2, e, t1]
    have hbd : Integrable fun r =>
        k ^ 2 / 2 * R₀ ^ 2 * Φ r + q * ((1 - Real.cos (k * r)) * Ψ r) :=
      (hΦ.const_mul _).add ((integrable_one_sub_cos_mul hΨ k).const_mul q)
    have hint := integral_mono (integrable_one_sub_cos_mul hΦ k) hbd hpt
    rw [integral_add (hΦ.const_mul _) ((integrable_one_sub_cos_mul hΨ k).const_mul _),
      integral_const_mul, integral_const_mul, ← hN₀def] at hint
    have hJk := hJ k hk hkk₀
    have hD : 0 ≤ ∫ r, (1 - Real.cos (k * r)) * Φ r :=
      integral_nonneg fun r => mul_nonneg (one_sub_cos_mul_nonneg k r) (hΦ0 r)
    have h1 := mul_le_mul_of_nonneg_left hJk hq0.le
    have h2 : q * (P * k) ≤ P * k := by
      have := mul_le_mul_of_nonneg_right hqle (mul_nonneg hP hk.le)
      linarith only [this]
    have h3 := mul_le_mul_of_nonneg_right hqB hD
    have h4 : k ^ 2 ≤ k := by nlinarith only [hk, hk1]
    have h5 := mul_le_mul_of_nonneg_right h4 (show 0 ≤ R₀ ^ 2 * N₀ / 2 by positivity)
    linarith only [hint, h1, h2, h3, h5]
  refine ⟨R₀, q, P + B * (R₀ ^ 2 * N₀ + 2 * P), hR₀, hq0, hqle, by positivity, hfar, ?_⟩
  intro k hk hkk₀ hk1
  have h1 := hJ k hk hkk₀
  have h2 := mul_le_mul_of_nonneg_left (step1 k hk hkk₀ hk1) hB
  linarith only [h1, h2]

/-- Step 2: the weighted second moment below `T` is linear in `T`. -/
theorem integral_lowSq_mul_le {Ψ : ℝ → ℝ} (hΨ0 : ∀ r, 0 ≤ Ψ r) (hΨ : Integrable Ψ) {C₄ k₀ : ℝ}
    (hJw : ∀ k : ℝ, 0 < k → k ≤ k₀ → k ≤ 1 → ∫ r, (1 - Real.cos (k * r)) * Ψ r ≤ C₄ * k)
    {T : ℝ} (hT : 0 < T) (hTk : 1 / T ≤ k₀) (hT1 : 1 / T ≤ 1) :
    ∫ r, lowSq T r * Ψ r ≤ 4 * C₄ * T := by
  have hk : 0 < 1 / T := by positivity
  have hpt : ∀ r : ℝ, (1 / T) ^ 2 / 4 * (lowSq T r * Ψ r) ≤
      (1 - Real.cos (1 / T * r)) * Ψ r := by
    intro r
    by_cases hr : |r| ≤ T
    · have eT : lowSq T r = r ^ 2 := if_pos hr
      have hx : |1 / T * r| ≤ 1 := by
        rw [abs_mul, abs_of_pos hk]
        have := mul_le_mul_of_nonneg_left hr hk.le
        rwa [one_div_mul_cancel hT.ne'] at this
      have h := mul_le_mul_of_nonneg_right (sq_div_four_le_one_sub_cos hx) (hΨ0 r)
      have e : (1 / T) ^ 2 / 4 * (lowSq T r * Ψ r) = (1 / T * r) ^ 2 / 4 * Ψ r := by
        rw [eT]
        ring
      rw [e]
      exact h
    · have eT : lowSq T r = 0 := if_neg hr
      rw [eT, zero_mul, mul_zero]
      exact mul_nonneg (one_sub_cos_mul_nonneg _ r) (hΨ0 r)
  have hint := integral_mono ((integrable_lowSq_mul hΨ T).const_mul _)
    (integrable_one_sub_cos_mul hΨ (1 / T)) hpt
  rw [integral_const_mul] at hint
  have hJ' := hJw (1 / T) hk hTk hT1
  have hT2 : 0 < (1 / T) ^ 2 / 4 := by positivity
  have h : (1 / T) ^ 2 / 4 * ∫ r, lowSq T r * Ψ r ≤ (1 / T) ^ 2 / 4 * (4 * C₄ * T) := by
    calc (1 / T) ^ 2 / 4 * ∫ r, lowSq T r * Ψ r ≤ C₄ * (1 / T) := hint.trans hJ'
      _ = (1 / T) ^ 2 / 4 * (4 * C₄ * T) := by
        field_simp
  exact le_of_mul_le_mul_left h hT2

/-- Step 3: the plain second moment below `T` gains the logarithm of an intermediate scale. -/
theorem integral_lowSq_mul_le_log {Φ Ψ : ℝ → ℝ} (hΦ0 : ∀ r, 0 ≤ Φ r) (hΨ0 : ∀ r, 0 ≤ Ψ r)
    (hΦ : Integrable Φ) (hΨ : Integrable Ψ) {G₀ : ℝ}
    (hlog : ∀ R : ℝ, 0 < R → ∀ r : ℝ, R ≤ |r| → (Real.log R - G₀) * Φ r ≤ Ψ r)
    {R₀ q C₄ k₀ : ℝ} (hq0 : 0 < q) (hqle : q ≤ 1)
    (hfar : ∀ r : ℝ, R₀ ≤ |r| → Φ r ≤ q * Ψ r)
    (hJw : ∀ k : ℝ, 0 < k → k ≤ k₀ → k ≤ 1 → ∫ r, (1 - Real.cos (k * r)) * Ψ r ≤ C₄ * k)
    {T S : ℝ} (hS : 0 < S) (hST : S ≤ T) (hSk : 1 / S ≤ k₀) (hS1 : 1 / S ≤ 1)
    (hℓS : 0 < Real.log S - G₀) :
    ∫ r, lowSq T r * Φ r ≤
      R₀ ^ 2 * (∫ r, Φ r) + 4 * C₄ * S + 4 * C₄ * T / (Real.log S - G₀) := by
  have hT : 0 < T := hS.trans_le hST
  have hpt : ∀ r : ℝ, lowSq T r * Φ r ≤ R₀ ^ 2 * Φ r + q * (lowSq S r * Ψ r) +
      (Real.log S - G₀)⁻¹ * (lowSq T r * Ψ r) := by
    intro r
    have t1 : 0 ≤ R₀ ^ 2 * Φ r := mul_nonneg (sq_nonneg _) (hΦ0 r)
    have t2 : 0 ≤ q * (lowSq S r * Ψ r) :=
      mul_nonneg hq0.le (mul_nonneg (lowSq_nonneg S r) (hΨ0 r))
    have t3 : 0 ≤ (Real.log S - G₀)⁻¹ * (lowSq T r * Ψ r) :=
      mul_nonneg (inv_nonneg.mpr hℓS.le) (mul_nonneg (lowSq_nonneg T r) (hΨ0 r))
    by_cases hrT : |r| ≤ T
    · have eT : lowSq T r = r ^ 2 := if_pos hrT
      rcases lt_or_ge |r| R₀ with hr | hr
      · have hr2 : r ^ 2 ≤ R₀ ^ 2 := by
          rw [← sq_abs r]
          exact pow_le_pow_left₀ (abs_nonneg r) hr.le 2
        have h := mul_le_mul_of_nonneg_right hr2 (hΦ0 r)
        rw [← eT] at h
        linarith only [h, t2, t3]
      · by_cases hrS : |r| ≤ S
        · have eS : lowSq S r = r ^ 2 := if_pos hrS
          have h := mul_le_mul_of_nonneg_left (hfar r hr) (sq_nonneg r)
          have e : r ^ 2 * (q * Ψ r) = q * (lowSq S r * Ψ r) := by
            rw [eS]
            ring
          rw [e, ← eT] at h
          linarith only [h, t1, t3]
        · have h1 := hlog S hS r (not_le.mp hrS).le
          have h3 : Φ r ≤ (Real.log S - G₀)⁻¹ * Ψ r := by
            have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hℓS.le)
            rwa [← mul_assoc, inv_mul_cancel₀ hℓS.ne', one_mul] at this
          have h := mul_le_mul_of_nonneg_left h3 (sq_nonneg r)
          have e : r ^ 2 * ((Real.log S - G₀)⁻¹ * Ψ r) =
              (Real.log S - G₀)⁻¹ * (lowSq T r * Ψ r) := by
            rw [eT]
            ring
          rw [e, ← eT] at h
          linarith only [h, t1, t2]
    · have eT : lowSq T r = 0 := if_neg hrT
      have e : lowSq T r * Φ r = 0 := by rw [eT, zero_mul]
      linarith only [e, t1, t2, t3]
  have hb12 : Integrable fun r => R₀ ^ 2 * Φ r + q * (lowSq S r * Ψ r) :=
    (hΦ.const_mul _).add ((integrable_lowSq_mul hΨ S).const_mul _)
  have hbd : Integrable fun r => R₀ ^ 2 * Φ r + q * (lowSq S r * Ψ r) +
      (Real.log S - G₀)⁻¹ * (lowSq T r * Ψ r) :=
    hb12.add ((integrable_lowSq_mul hΨ T).const_mul _)
  have hint := integral_mono (integrable_lowSq_mul hΦ T) hbd hpt
  rw [integral_add hb12 ((integrable_lowSq_mul hΨ T).const_mul _),
    integral_add (hΦ.const_mul _) ((integrable_lowSq_mul hΨ S).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at hint
  have hUS := integral_lowSq_mul_le hΨ0 hΨ hJw hS hSk hS1
  have hUT := integral_lowSq_mul_le hΨ0 hΨ hJw hT ((one_div_le_one_div_of_le hS hST).trans hSk)
    ((one_div_le_one_div_of_le hS hST).trans hS1)
  have hU0 : 0 ≤ ∫ r, lowSq S r * Ψ r :=
    integral_nonneg fun r => mul_nonneg (lowSq_nonneg S r) (hΨ0 r)
  have h1 : q * ∫ r, lowSq S r * Ψ r ≤ 4 * C₄ * S := by
    have := mul_le_mul_of_nonneg_right hqle hU0
    linarith only [this, hUS]
  have h2 : (Real.log S - G₀)⁻¹ * ∫ r, lowSq T r * Ψ r ≤
      4 * C₄ * T / (Real.log S - G₀) := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hUT (inv_nonneg.mpr hℓS.le)
  linarith only [hint, h1, h2]

/-- Step 4: below `T` the modulus is a second moment, above `T` it is paid by the weight. -/
theorem spectralModulus_le_low_add_high {Φ Ψ : ℝ → ℝ} (hΦ0 : ∀ r, 0 ≤ Φ r)
    (hΨ0 : ∀ r, 0 ≤ Ψ r) (hΦ : Integrable Φ) (hΨ : Integrable Ψ) {G₀ : ℝ}
    (hlog : ∀ R : ℝ, 0 < R → ∀ r : ℝ, R ≤ |r| → (Real.log R - G₀) * Φ r ≤ Ψ r) (k : ℝ)
    {T : ℝ} (hT : 0 < T) (hℓ : 0 < Real.log T - G₀) :
    ∫ r, (1 - Real.cos (k * r)) * Φ r ≤ k ^ 2 / 2 * (∫ r, lowSq T r * Φ r) +
      (Real.log T - G₀)⁻¹ * ∫ r, (1 - Real.cos (k * r)) * Ψ r := by
  have hpt : ∀ r : ℝ, (1 - Real.cos (k * r)) * Φ r ≤ k ^ 2 / 2 * (lowSq T r * Φ r) +
      (Real.log T - G₀)⁻¹ * ((1 - Real.cos (k * r)) * Ψ r) := by
    intro r
    have t2 : 0 ≤ (Real.log T - G₀)⁻¹ * ((1 - Real.cos (k * r)) * Ψ r) :=
      mul_nonneg (inv_nonneg.mpr hℓ.le) (mul_nonneg (one_sub_cos_mul_nonneg k r) (hΨ0 r))
    by_cases hr : |r| ≤ T
    · have eT : lowSq T r = r ^ 2 := if_pos hr
      have h2 := mul_le_mul_of_nonneg_right (one_sub_cos_mul_le_sq k r) (hΦ0 r)
      have e : k ^ 2 / 2 * (lowSq T r * Φ r) = k ^ 2 / 2 * r ^ 2 * Φ r := by
        rw [eT]
        ring
      linarith only [h2, e, t2]
    · have eT : lowSq T r = 0 := if_neg hr
      have e0 : k ^ 2 / 2 * (lowSq T r * Φ r) = 0 := by rw [eT, zero_mul, mul_zero]
      have h1 := hlog T hT r (not_le.mp hr).le
      have h3 : Φ r ≤ (Real.log T - G₀)⁻¹ * Ψ r := by
        have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hℓ.le)
        rwa [← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul] at this
      have h4 := mul_le_mul_of_nonneg_left h3 (one_sub_cos_mul_nonneg k r)
      have e : (1 - Real.cos (k * r)) * ((Real.log T - G₀)⁻¹ * Ψ r) =
          (Real.log T - G₀)⁻¹ * ((1 - Real.cos (k * r)) * Ψ r) := by ring
      linarith only [h4, e, e0]
  have hbd : Integrable fun r => k ^ 2 / 2 * (lowSq T r * Φ r) +
      (Real.log T - G₀)⁻¹ * ((1 - Real.cos (k * r)) * Ψ r) :=
    ((integrable_lowSq_mul hΦ T).const_mul _).add
      ((integrable_one_sub_cos_mul hΨ k).const_mul _)
  have hint := integral_mono (integrable_one_sub_cos_mul hΦ k) hbd hpt
  rw [integral_add ((integrable_lowSq_mul hΦ T).const_mul _)
      ((integrable_one_sub_cos_mul hΨ k).const_mul _), integral_const_mul,
    integral_const_mul] at hint
  exact hint

/-- The arithmetic of the last step: with `T = 1/(Ak)`, `S² = T` and `lT = log T` large. -/
theorem log_mul_le_of_spectral_bounds {D J V k T S lT G₀ B P ε A C₄ C₇ X κ lam : ℝ}
    (hk : 0 < k) (hε : 0 < ε) (hD : 0 ≤ D) (hC₄ : 0 ≤ C₄) (hC₇ : 0 ≤ C₇) (hXdef : X = P + ε / 2)
    (hX : 0 < X) (hA1 : 1 ≤ A) (hAε : 8 * C₄ ≤ ε / 4 * A) (hkT : k * T = 1 / A) (hS : 0 < S)
    (hSS : S * S = T) (hSq : lT ^ 2 / 8 ≤ S) (hG₀ : 0 ≤ G₀) (r3 : 4 * G₀ + 4 ≤ lT)
    (r4 : 32 * C₇ / ε ≤ lT) (r5 : 2 * κ * X / ε + 1 ≤ lT - G₀ - B)
    (hlam : lam = lT - G₀ - B + κ) (hint : D ≤ k ^ 2 / 2 * V + (lT - G₀)⁻¹ * J)
    (hJk : J ≤ P * k + B * D) (hV : V ≤ C₇ * S + 4 * C₄ * T / (lT / 2 - G₀)) :
    lam * D ≤ (P + ε) * k := by
  have hA0 : 0 < A := by linarith only [hA1]
  have hlT0 : 0 < lT := by linarith only [r3, hG₀]
  have hℓ : 0 < lT - G₀ := by linarith only [r3, hG₀]
  have hℓS0 : 0 < lT / 2 - G₀ := by linarith only [r3, hG₀]
  have h1 : (lT - G₀) * D ≤ (lT - G₀) * (k ^ 2 / 2 * V) + J := by
    have := mul_le_mul_of_nonneg_left hint hℓ.le
    rw [mul_add, ← mul_assoc (lT - G₀) (lT - G₀)⁻¹, mul_inv_cancel₀ hℓ.ne', one_mul] at this
    exact this
  have hkS : k * S ≤ 8 / lT ^ 2 := by
    have h1 : k * S * S ≤ 1 := by
      rw [mul_assoc, hSS, hkT, div_le_one hA0]
      exact hA1
    have h2 : k * S ≤ 1 / S := by
      rw [le_div_iff₀ hS]
      exact h1
    have h3 : 1 / S ≤ 8 / lT ^ 2 := by
      rw [div_le_div_iff₀ hS (by positivity)]
      linarith only [hSq]
    exact h2.trans h3
  have ht1 : (lT - G₀) * (k ^ 2 / 2 * (C₇ * S)) ≤ ε / 8 * k := by
    have ha : (lT - G₀) * (k * S) ≤ lT * (8 / lT ^ 2) :=
      mul_le_mul (by linarith only [hG₀]) hkS (mul_nonneg hk.le hS.le) hlT0.le
    have hb : lT * (8 / lT ^ 2) = 8 / lT := by
      field_simp
    have hc : C₇ * (8 / lT) ≤ ε / 4 := by
      have h := (div_le_iff₀ hε).mp r4
      rw [mul_div_assoc', div_le_iff₀ hlT0]
      linarith only [h]
    have he : C₇ * ((lT - G₀) * (k * S)) ≤ ε / 4 :=
      (mul_le_mul_of_nonneg_left (ha.trans_eq hb) hC₇).trans hc
    have hd : (lT - G₀) * (k ^ 2 / 2 * (C₇ * S)) =
        k / 2 * (C₇ * ((lT - G₀) * (k * S))) := by ring
    rw [hd]
    have := mul_le_mul_of_nonneg_left he (show 0 ≤ k / 2 by positivity)
    linarith only [this]
  have ht2 : (lT - G₀) * (k ^ 2 / 2 * (4 * C₄ * T / (lT / 2 - G₀))) ≤ ε / 4 * k := by
    have ha : (lT - G₀) / (lT / 2 - G₀) ≤ 4 := by
      rw [div_le_iff₀ hℓS0]
      linarith only [r3, hG₀]
    have hb : (lT - G₀) * (k ^ 2 / 2 * (4 * C₄ * T / (lT / 2 - G₀))) =
        k * (2 * C₄ * (k * T)) * ((lT - G₀) / (lT / 2 - G₀)) := by
      field_simp
      ring
    rw [hb, hkT]
    have hc : 0 ≤ k * (2 * C₄ * (1 / A)) := by positivity
    have hd := mul_le_mul_of_nonneg_left ha hc
    have hf : 8 * C₄ / A ≤ ε / 4 := by
      rw [div_le_iff₀ hA0]
      exact hAε
    have hg := mul_le_mul_of_nonneg_left hf hk.le
    have he : k * (2 * C₄ * (1 / A)) * 4 = k * (8 * C₄ / A) := by ring
    linarith only [hd, hg, he]
  have h2 : (lT - G₀) * (k ^ 2 / 2 * V) ≤ ε / 8 * k + ε / 4 * k := by
    have := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hV (show (0 : ℝ) ≤ k ^ 2 / 2 by positivity)) hℓ.le
    have e : (lT - G₀) * (k ^ 2 / 2 * (C₇ * S + 4 * C₄ * T / (lT / 2 - G₀))) =
        (lT - G₀) * (k ^ 2 / 2 * (C₇ * S)) +
          (lT - G₀) * (k ^ 2 / 2 * (4 * C₄ * T / (lT / 2 - G₀))) := by ring
    linarith only [this, e, ht1, ht2]
  have hεk : 0 < ε * k := mul_pos hε hk
  have h3 : (lT - G₀ - B) * D ≤ X * k := by
    rw [hXdef]
    linarith only [h1, h2, hJk, hεk]
  have h5 : 2 * κ * X / ε * D ≤ X * k := by
    have := mul_le_mul_of_nonneg_right r5 hD
    linarith only [this, h3, hD]
  have h6 : 2 * κ * X * D ≤ ε * (X * k) := by
    have := mul_le_mul_of_nonneg_left h5 hε.le
    have e : ε * (2 * κ * X / ε * D) = 2 * κ * X * D := by
      field_simp
    rwa [e] at this
  have h8 : 2 * κ * D ≤ ε * k := by
    have h7 : X * (2 * κ * D) ≤ X * (ε * k) := by linarith only [h6]
    exact le_of_mul_le_mul_left h7 hX
  rw [hlam]
  rw [hXdef] at h3
  linarith only [h3, h8]

/-- **A logarithmic weight on the frequencies is a logarithmic gain in the modulus.** Let
`Φ, Ψ ≥ 0` be integrable densities with `(log R − G₀) Φ ≤ Ψ` on `|r| ≥ R`. If
`∫ (1 − cos kr) Ψ ≤ P k + B ∫ (1 − cos kr) Φ` for small `k > 0`, then for every `ε > 0`
`log(1/k) ∫ (1 − cos kr) Φ ≤ (P + ε) k` for all small `k`. Frequencies below `T = 1/(Ak)`
carry a second moment of size `T / log T`; above `T` the weight is at least `log T − G₀`. -/
theorem eventually_log_mul_spectralModulus_le {Φ Ψ : ℝ → ℝ} (hΦ0 : ∀ r, 0 ≤ Φ r)
    (hΨ0 : ∀ r, 0 ≤ Ψ r) (hΦ : Integrable Φ) (hΨ : Integrable Ψ) {G₀ : ℝ} (hG₀ : 0 ≤ G₀)
    (hlog : ∀ R : ℝ, 0 < R → ∀ r : ℝ, R ≤ |r| → (Real.log R - G₀) * Φ r ≤ Ψ r)
    {P B k₀ : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B) (hk₀ : 0 < k₀)
    (hJ : ∀ k : ℝ, 0 < k → k ≤ k₀ →
      ∫ r, (1 - Real.cos (k * r)) * Ψ r ≤ P * k + B * ∫ r, (1 - Real.cos (k * r)) * Φ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℝ in 𝓝[>] 0,
      Real.log (1 / k) * ∫ r, (1 - Real.cos (k * r)) * Φ r ≤ (P + ε) * k := by
  obtain ⟨R₀, q, C₄, hR₀, hq0, hqle, hC₄, hfar, hJw⟩ :=
    exists_weightedModulus_le_linear hΦ0 hΨ0 hΦ hΨ hlog hP hB hJ
  have hN₀ : 0 ≤ ∫ r, Φ r := integral_nonneg hΦ0
  obtain ⟨C₇, hC₇def⟩ : ∃ C₇ : ℝ, C₇ = R₀ ^ 2 * (∫ r, Φ r) + 4 * C₄ := ⟨_, rfl⟩
  have hC₇ : 0 ≤ C₇ := by
    rw [hC₇def]
    positivity
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 32 * C₄ / ε + 1 := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    have : 0 ≤ 32 * C₄ / ε := by positivity
    linarith only [this]
  have hA0 : 0 < A := by linarith only [hA1]
  have hAε : 8 * C₄ ≤ ε / 4 * A := by
    have e : ε / 4 * A = 8 * C₄ + ε / 4 := by
      rw [hAdef]
      field_simp
      ring
    rw [e]
    linarith only [hε]
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
  obtain ⟨k₁, hk₁def⟩ : ∃ k₁ : ℝ, k₁ = min k₀ 1 := ⟨_, rfl⟩
  have hk₁ : 0 < k₁ := by
    rw [hk₁def]
    exact lt_min hk₀ one_pos
  have hk₁0 : k₁ ≤ k₀ := by
    rw [hk₁def]
    exact min_le_left _ _
  have hk₁1 : k₁ ≤ 1 := by
    rw [hk₁def]
    exact min_le_right _ _
  obtain ⟨L₁, hL₁def⟩ : ∃ L₁ : ℝ, L₁ = Real.log (1 / k₁) := ⟨_, rfl⟩
  have hL₁ : 0 ≤ L₁ := by
    rw [hL₁def]
    exact Real.log_nonneg (by rw [le_div_iff₀ hk₁]; linarith only [hk₁1])
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = P + ε / 2 := ⟨_, rfl⟩
  have hX : 0 < X := by
    rw [hXdef]
    linarith only [hP, hε]
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.log A + G₀ + B := ⟨_, rfl⟩
  have hκ : 0 ≤ κ := by
    rw [hκdef]
    linarith only [hlogA, hG₀, hB]
  have h32 : 0 ≤ 32 * C₇ / ε := by positivity
  have h2κ : 0 ≤ 2 * κ * X / ε := by positivity
  have hthr := tendsto_log_one_div_nhdsGT_zero.eventually_ge_atTop
    (Real.log A + 2 * L₁ + 4 * G₀ + 4 + 32 * C₇ / ε + B + 2 * κ * X / ε + 1)
  filter_upwards [hthr, self_mem_nhdsWithin] with k hΛ hk'
  have hk : 0 < k := hk'
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 / (A * k) := ⟨_, rfl⟩
  have hT : 0 < T := by
    rw [hTdef]
    positivity
  have hkT : k * T = 1 / A := by
    rw [hTdef]
    field_simp
  obtain ⟨lT, hlTdef⟩ : ∃ lT : ℝ, lT = Real.log T := ⟨_, rfl⟩
  have hlT : lT = Real.log (1 / k) - Real.log A := by
    rw [hlTdef, hTdef, one_div, one_div, Real.log_inv, Real.log_inv,
      Real.log_mul hA0.ne' hk.ne']
    ring
  have r2 : 2 * L₁ ≤ lT := by linarith only [hΛ, hlT, hG₀, h32, hB, h2κ]
  have r3 : 4 * G₀ + 4 ≤ lT := by linarith only [hΛ, hlT, hL₁, h32, hB, h2κ]
  have r4 : 32 * C₇ / ε ≤ lT := by linarith only [hΛ, hlT, hL₁, hG₀, hB, h2κ]
  have r5 : 2 * κ * X / ε + 1 ≤ lT - G₀ - B := by linarith only [hΛ, hlT, hL₁, hG₀, h32]
  have hkk₁ : k ≤ k₁ := by
    have h1 : Real.log (1 / k₁) ≤ Real.log (1 / k) := by
      rw [← hL₁def]
      linarith only [hΛ, hlogA, hL₁, hG₀, h32, hB, h2κ]
    exact (one_div_le_one_div hk₁ hk).mp
      ((Real.log_le_log_iff (by positivity) (by positivity)).mp h1)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = Real.exp (lT / 2) := ⟨_, rfl⟩
  have hS : 0 < S := by
    rw [hSdef]
    exact Real.exp_pos _
  have hSS : S * S = T := by
    rw [hSdef, ← Real.exp_add, add_halves, hlTdef, Real.exp_log hT]
  have hlS : Real.log S = lT / 2 := by rw [hSdef, Real.log_exp]
  have hS1 : 1 ≤ S := by
    rw [hSdef]
    exact Real.one_le_exp (by linarith only [r3, hG₀])
  have hST : S ≤ T := by
    rw [← hSS]
    nlinarith only [hS1, hS]
  have hSk : 1 / S ≤ k₁ := by
    have h1 : 1 / k₁ ≤ S := by
      have e : 1 / k₁ = Real.exp L₁ := by
        rw [hL₁def, Real.exp_log (by positivity)]
      rw [e, hSdef]
      exact Real.exp_le_exp.mpr (by linarith only [r2])
    exact (one_div_le hS hk₁).mpr h1
  have hSq : lT ^ 2 / 8 ≤ S := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ lT / 2 by linarith only [r3, hG₀])
    rw [← hSdef] at h
    have e : (lT / 2) ^ 2 / 2 = lT ^ 2 / 8 := by ring
    linarith only [h, e, r3, hG₀]
  have hℓ : 0 < Real.log T - G₀ := by
    rw [← hlTdef]
    linarith only [r3, hG₀]
  have hℓS : 0 < Real.log S - G₀ := by
    rw [hlS]
    linarith only [r3, hG₀]
  have hV := integral_lowSq_mul_le_log hΦ0 hΨ0 hΦ hΨ hlog hq0 hqle hfar hJw hS hST
    (hSk.trans hk₁0) (hSk.trans hk₁1) hℓS
  rw [hlS] at hV
  have hint := spectralModulus_le_low_add_high hΦ0 hΨ0 hΦ hΨ hlog k hT hℓ
  rw [← hlTdef] at hint
  have hV' : (∫ r, lowSq T r * Φ r) ≤ C₇ * S + 4 * C₄ * T / (lT / 2 - G₀) := by
    have : R₀ ^ 2 * (∫ r, Φ r) ≤ R₀ ^ 2 * (∫ r, Φ r) * S :=
      le_mul_of_one_le_right (by positivity) hS1
    rw [hC₇def]
    linarith only [hV, this]
  exact log_mul_le_of_spectral_bounds hk hε
    (integral_nonneg fun r => mul_nonneg (one_sub_cos_mul_nonneg k r) (hΦ0 r)) hC₄ hC₇ hXdef hX
    hA1 hAε hkT hS hSS hSq hG₀ r3 r4 r5
    (by rw [hκdef]; linarith only [hlT]) hint (hJ k hk (hkk₁.trans hk₁0)) hV'

/-! ### Terminal intervals -/

/-- `‖1 − e^{iθ}‖² = 2 (1 − cos θ)`. -/
theorem norm_sq_one_sub_cexp (θ : ℝ) :
    ‖(1 : ℂ) - Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 = 2 * (1 - Real.cos θ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination Real.sin_sq_add_cos_sq θ

/-- An affine image of a profile is square integrable on a terminal interval. -/
theorem integrableOn_Ioo_sq_affine {F : ℝ → ℝ} (hFi : Integrable F)
    (hF2 : Integrable fun u => F u ^ 2) (k α β : ℝ) :
    IntegrableOn (fun u => (α * F u - β) ^ 2) (Ioo (-k) 0) := by
  have h1 : IntegrableOn (fun u => α ^ 2 * F u ^ 2) (Ioo (-k) 0) :=
    (hF2.const_mul _).integrableOn
  have h2 : IntegrableOn (fun u => 2 * α * β * F u) (Ioo (-k) 0) :=
    (hFi.const_mul _).integrableOn
  have h3 : IntegrableOn (fun _ : ℝ => β ^ 2) (Ioo (-k) 0) :=
    (continuous_const.integrableOn_Icc (a := -k) (b := 0)).mono_set Ioo_subset_Icc_self
  have e : (fun u => (α * F u - β) ^ 2) =
      fun u => α ^ 2 * F u ^ 2 - 2 * α * β * F u + β ^ 2 := by
    funext u
    ring
  rw [e]
  exact (h1.sub h2).add h3

/-- The square mass of an affine image of a profile on a terminal interval. -/
theorem setIntegral_Ioo_sq_affine {F : ℝ → ℝ} (hFi : Integrable F)
    (hF2 : Integrable fun u => F u ^ 2) {k : ℝ} (hk : 0 ≤ k) (α β : ℝ) :
    ∫ u in Ioo (-k) 0, (α * F u - β) ^ 2 =
      α ^ 2 * (∫ u in Ioo (-k) 0, F u ^ 2) - 2 * α * β * (∫ u in Ioo (-k) 0, F u) +
        β ^ 2 * k := by
  have h1 : IntegrableOn (fun u => α ^ 2 * F u ^ 2) (Ioo (-k) 0) :=
    (hF2.const_mul _).integrableOn
  have h2 : IntegrableOn (fun u => 2 * α * β * F u) (Ioo (-k) 0) :=
    (hFi.const_mul _).integrableOn
  have h3 : IntegrableOn (fun _ : ℝ => β ^ 2 * (1 : ℝ)) (Ioo (-k) 0) :=
    (continuous_const.integrableOn_Icc (a := -k) (b := 0)).mono_set Ioo_subset_Icc_self
  have h12 : IntegrableOn (fun u => α ^ 2 * F u ^ 2 - 2 * α * β * F u) (Ioo (-k) 0) :=
    h1.sub h2
  have e : ∀ u : ℝ, (α * F u - β) ^ 2 =
      α ^ 2 * F u ^ 2 - 2 * α * β * F u + β ^ 2 * (1 : ℝ) := fun u => by ring
  simp_rw [e]
  rw [integral_add h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_Ioo_one hk]

/-- The increment of a profile carried by `u < 0` splits into its interior part and the terminal
mass: `∫ (F(u) − F(u+k))² = ∫_{u ≤ −k} (F(u) − F(u+k))² + ∫_{−k}^0 F²`. -/
theorem integral_sq_increment_eq_interior_add_terminal {F : ℝ → ℝ}
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {k : ℝ} (hk : 0 < k)
    (hg : Integrable fun u => (F u - F (u + k)) ^ 2) :
    ∫ u, (F u - F (u + k)) ^ 2 =
      (∫ u in Iic (-k), (F u - F (u + k)) ^ 2) + ∫ u in Ioo (-k) 0, F u ^ 2 := by
  have h0 : ∫ u in Ici (0 : ℝ), (F u - F (u + k)) ^ 2 = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu => by
      rw [hsupp u hu, hsupp (u + k) (add_nonneg hu hk.le), sub_zero, zero_pow two_ne_zero]
  have h1 : ∫ u in Ioo (-k) 0, (F u - F (u + k)) ^ 2 = ∫ u in Ioo (-k) 0, F u ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioo fun u hu => by
      show (F u - F (u + k)) ^ 2 = F u ^ 2
      rw [hsupp (u + k) (by linarith only [hu.1]), sub_zero]
  rw [← integral_add_compl (measurableSet_Iic (a := -k)) hg, compl_Iic,
    ← Ioo_union_Ici_eq_Ioi (show -k < 0 by linarith only [hk]),
    setIntegral_union (s := Ioo (-k) 0) (t := Ici 0)
      (Set.disjoint_left.mpr fun u hu hu' => not_le.mpr hu.2 hu')
      measurableSet_Ici hg.integrableOn hg.integrableOn, h0, h1, add_zero]

/-- Cauchy–Schwarz on the terminal interval, with the logarithmic factor. -/
theorem sq_terminalMean_mul_log_le {F : ℝ → ℝ} (hFm : Measurable F)
    (hF2 : Integrable fun u => F u ^ 2) {k : ℝ} (hk : 0 < k) (hk1 : k < 1) :
    ((∫ u in Ioo (-k) 0, F u) / k) ^ 2 * Real.log (1 / k) ≤
      Real.log (1 / k) / k * ∫ u in Ioo (-k) 0, F u ^ 2 := by
  have hcs := sq_setIntegral_Ioo_le hFm hF2 hk.le
  have hL : 0 ≤ Real.log (1 / k) :=
    Real.log_nonneg (by rw [le_div_iff₀ hk]; linarith only [hk1])
  have h1 : ((∫ u in Ioo (-k) 0, F u) / k) ^ 2 ≤ (∫ u in Ioo (-k) 0, F u ^ 2) / k := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hk]
    have := mul_le_mul_of_nonneg_right hcs hk.le
    linarith only [this]
  calc ((∫ u in Ioo (-k) 0, F u) / k) ^ 2 * Real.log (1 / k)
      ≤ (∫ u in Ioo (-k) 0, F u ^ 2) / k * Real.log (1 / k) :=
        mul_le_mul_of_nonneg_right h1 hL
    _ = Real.log (1 / k) / k * ∫ u in Ioo (-k) 0, F u ^ 2 := by ring

/-- **Chebyshev on a terminal interval**: `δ² |{u ∈ (−k, 0) : |g(u)| ≥ δ}| ≤ ∫_{−k}^0 g²`. -/
theorem sq_mul_measureReal_terminal_le {g : ℝ → ℝ} (hg : Measurable g) {k δ : ℝ} (hδ : 0 ≤ δ)
    (hgi : IntegrableOn (fun u => g u ^ 2) (Ioo (-k) 0)) :
    δ ^ 2 * volume.real (Ioo (-k) 0 ∩ {u | δ ≤ |g u|}) ≤ ∫ u in Ioo (-k) 0, g u ^ 2 := by
  have hE : MeasurableSet (Ioo (-k) (0 : ℝ) ∩ {u | δ ≤ |g u|}) :=
    measurableSet_Ioo.inter (measurableSet_le measurable_const (continuous_abs.measurable.comp hg))
  have hfin : volume (Ioo (-k) (0 : ℝ) ∩ {u | δ ≤ |g u|}) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt measure_Ioo_lt_top).ne
  have h1 : δ ^ 2 * volume.real (Ioo (-k) (0 : ℝ) ∩ {u | δ ≤ |g u|}) ≤
      ∫ u in Ioo (-k) 0 ∩ {u | δ ≤ |g u|}, g u ^ 2 := by
    have h := setIntegral_ge_of_const_le (c := δ ^ 2) hE hfin (fun u hu => by
      have h : δ ≤ |g u| := hu.2
      show δ ^ 2 ≤ g u ^ 2
      rw [← sq_abs (g u)]
      exact pow_le_pow_left₀ hδ h 2) (hgi.mono_set inter_subset_left)
    rwa [smul_eq_mul, mul_comm] at h
  exact h1.trans (setIntegral_mono_set hgi (Eventually.of_forall fun u => sq_nonneg (g u))
    (LE.le.eventuallyLE
      (show Ioo (-k) (0 : ℝ) ∩ {u | δ ≤ |g u|} ≤ Ioo (-k) 0 from inter_subset_left)))

/-- `e^{8k} − 1 ≤ 8k (1 + η)` for `0 ≤ k ≤ log(1 + η)/8`. -/
theorem exp_eight_mul_sub_one_le {k η : ℝ} (hk : 0 ≤ k) (hη : 0 < η)
    (hkk : k ≤ Real.log (1 + η) / 8) : Real.exp (8 * k) - 1 ≤ 8 * k * (1 + η) := by
  have h1 := Real.add_one_le_exp (-(8 * k))
  have h2 : Real.exp (8 * k) * Real.exp (-(8 * k)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (8 * k)).le
  have h4 : Real.exp (8 * k) ≤ 1 + η := by
    calc Real.exp (8 * k) ≤ Real.exp (Real.log (1 + η)) :=
          Real.exp_le_exp.mpr (by linarith only [hkk])
      _ = 1 + η := Real.exp_log (by linarith only [hη])
  have h5 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ 8 * k by positivity)
  linarith only [h2, h3, h5]

private theorem terminal_variance_algebra {L k S J V : ℝ} (hk : 0 < k)
    (e : V = S - 2 * (J / k) * J + (J / k) ^ 2 * k) :
    L / k * S - (J / k) ^ 2 * L = L / k * V := by
  rw [e]
  field_simp
  ring

private theorem terminal_meanSquare_algebra {L k S J V c sL : ℝ} (hk : 0 < k)
    (e : V = L * S - 2 * sL * c * J + c ^ 2 * k) :
    L / k * S - 2 * c * (J / k * sL) + c ^ 2 = 1 / k * V := by
  rw [e]
  field_simp

private theorem terminal_chebyshev_algebra {m V δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k)
    (h : δ ^ 2 * m ≤ V) : m / k ≤ 1 / δ ^ 2 * (1 / k * V) := by
  have e : 1 / δ ^ 2 * (1 / k * V) = V / (δ ^ 2 * k) := by ring
  rw [e, div_le_div_iff₀ hk (by positivity)]
  linarith only [mul_le_mul_of_nonneg_right h hk.le]

/-! ### The frequency side of an increment -/

/-- The increment `u ↦ F(u) − F(u+k)`, `k ≥ 0`, of a domain profile lies in the domain. -/
theorem criticalHalfLineEnergyDomain_increment {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {k : ℝ} (hk : 0 ≤ k) : CriticalHalfLineEnergyDomain (fun u => F u + (-1) * F (u + k)) :=
  hF.add_const_mul (hF.causalTranslate hk) (-1)

theorem integrable_sq_increment {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {k : ℝ}
    (hk : 0 ≤ k) : Integrable fun u => (F u - F (u + k)) ^ 2 := by
  have e : (fun u => (F u - F (u + k)) ^ 2) = fun u => (F u + (-1) * F (u + k)) ^ 2 := by
    funext u
    ring
  rw [e]
  exact (criticalHalfLineEnergyDomain_increment hF hk).sq

/-- The terminal square mass is at most the squared increment. -/
theorem setIntegral_Ioo_sq_le_integral_sq_increment {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {k : ℝ} (hk : 0 < k) :
    ∫ u in Ioo (-k) 0, F u ^ 2 ≤ ∫ u, (F u - F (u + k)) ^ 2 := by
  rw [integral_sq_increment_eq_interior_add_terminal hF.support hk
    (integrable_sq_increment hF hk.le)]
  exact le_add_of_nonneg_left (setIntegral_nonneg measurableSet_Iic fun u _ => sq_nonneg _)

/-- `|F̂_k(r)|² = 2 (1 − cos kr) |F̂(r)|²` for the increment `F_k = F − F(· + k)`. -/
theorem norm_sq_paperFT_increment {F : ℝ → ℝ} (hFi : Integrable F) (k r : ℝ) :
    ‖paperFT (cx fun u => F u + (-1) * F (u + k)) r‖ ^ 2 =
      2 * ((1 - Real.cos (k * r)) * ‖paperFT (cx F) r‖ ^ 2) := by
  have hfun : (cx fun u => F u + (-1) * F (u + k)) = fun u => cx F u - cx F (u + k) := by
    funext u
    simp only [cx]
    push_cast
    ring
  rw [hfun, paperFT_sub_comp_add_right (g := cx F) (hFi.ofReal (𝕜 := ℂ)) k r, norm_mul, mul_pow,
    norm_sq_one_sub_cexp, Real.cos_neg, mul_comm r k]
  ring

/-- **Plancherel for an increment**:
`∫ (1 − cos kr) |F̂(r)|² dr = π ∫ (F(u) − F(u+k))² du`. -/
theorem integral_one_sub_cos_mul_norm_sq_paperFT {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {k : ℝ} (hk : 0 ≤ k) :
    ∫ r : ℝ, (1 - Real.cos (k * r)) * ‖paperFT (cx F) r‖ ^ 2 =
      Real.pi * ∫ u, (F u - F (u + k)) ^ 2 := by
  have hD := criticalHalfLineEnergyDomain_increment hF hk
  have hpl := KernelStrip.integral_norm_sq_paperFT_of_memLp
    (h := cx fun u => F u + (-1) * F (u + k)) (hD.integrable.ofReal (𝕜 := ℂ))
    (memLp_cx_of_sq hD.integrable hD.sq)
  have hL : (∫ x : ℝ, ‖paperFT (cx fun u => F u + (-1) * F (u + k)) x‖ ^ 2) =
      2 * ∫ r : ℝ, (1 - Real.cos (k * r)) * ‖paperFT (cx F) r‖ ^ 2 := by
    rw [← integral_const_mul]
    exact integral_congr_ae
      (Eventually.of_forall fun r => norm_sq_paperFT_increment hF.integrable k r)
  have hR : (∫ u : ℝ, ‖cx (fun u => F u + (-1) * F (u + k)) u‖ ^ 2) =
      ∫ u, (F u - F (u + k)) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun u => by
      show ‖((F u + (-1) * F (u + k) : ℝ) : ℂ)‖ ^ 2 = (F u - F (u + k)) ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring)
  rw [hL, hR] at hpl
  linarith only [hpl]

/-- The archimedean form of an increment on the frequency side:
`∫ (1 − cos kr) |F̂(r)|² γ(r) dr = π · archForm (F − F(· + k))`. -/
theorem integral_one_sub_cos_mul_norm_sq_paperFT_mul_gammaBracket {F : ℝ → ℝ}
    (hFi : Integrable F) (k : ℝ) :
    ∫ r : ℝ, (1 - Real.cos (k * r)) * (‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r) =
      Real.pi * archForm (fun u => F u + (-1) * F (u + k)) := by
  have hI : (∫ r : ℝ, ‖paperFT (cx fun u => F u + (-1) * F (u + k)) r‖ ^ 2 *
      EF.gammaBracket r) =
      2 * ∫ r : ℝ, (1 - Real.cos (k * r)) * (‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    show ‖paperFT (cx fun u => F u + (-1) * F (u + k)) r‖ ^ 2 * EF.gammaBracket r =
      2 * ((1 - Real.cos (k * r)) * (‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r))
    rw [norm_sq_paperFT_increment hFi k r]
    ring
  have hA : archForm (fun u => F u + (-1) * F (u + k)) =
      1 / (2 * Real.pi) *
        (2 * ∫ r : ℝ, (1 - Real.cos (k * r)) * (‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r)) := by
    rw [← hI]
    rfl
  rw [hA]
  have h : ∀ Y : ℝ, Real.pi * (1 / (2 * Real.pi) * (2 * Y)) = Y := fun Y => by
    have h' : Real.pi * (1 / (2 * Real.pi) * (2 * Y)) = Real.pi * (1 / Real.pi) * Y := by ring
    rw [h', mul_one_div_cancel Real.pi_ne_zero, one_mul]
  exact (h _).symm

/-! ### The exact modulus of continuity of the critical state -/

/-- **The exact energy of an increment of the state**: `E(F − τ_k F) = a (e^{8k} − 1) M`. -/
theorem criticalState_fullEnergy_increment {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {k : ℝ} (hk : 0 ≤ k) :
    criticalHalfLineFullEnergy W₀ (fun u => F u + (-1) * F (u + k)) =
      criticalAliasCoefficient W₀ * (Real.exp (8 * k) - 1) *
        ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hT := hd.causalTranslate hk
  rw [criticalHalfLineFullEnergy_add_const_mul W₀ hd hT (-1),
    criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hF,
    criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hT,
    criticalState_fullEnergy_translate hW hthreshold hF hk]
  ring

/-- **The upper bound for the modulus of continuity.** For every `ε > 0`, eventually as
`k → 0⁺`, `log(1/k) ∫ (F(u) − F(u+k))² du ≤ (8aM + ε) k`. The exact energy of the increment and
the coercivity of the full energy give the weighted inequality on the frequency side, with the
weight `γ + c₀ ≥ 0`. -/
theorem criticalState_eventually_log_mul_sq_increment_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℝ in 𝓝[>] 0,
      Real.log (1 / k) * ∫ u, (F u - F (u + k)) ^ 2 ≤
        (8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) + ε) * k := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hM := criticalState_exponentialMass_pos hW hF
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = 8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := ⟨_, rfl⟩
  have hQ : 0 < Q := by
    rw [hQdef]
    exact mul_pos (mul_pos (by norm_num) ha) hM
  rw [← hQdef]
  obtain ⟨B, hB0, hB⟩ := criticalHalfLineFullEnergy_arch_coercive_remainder hW
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
  have hlog : ∀ R : ℝ, 0 < R → ∀ r : ℝ, R ≤ |r| →
      (Real.log R - ArithmeticPositivityTheory.factorialSpanGammaOffset) * Φ r ≤ Ψ r := by
    intro R hR r hr
    have h1 := mul_le_mul_of_nonneg_right
      (ArithmeticPositivityTheory.gammaBracket_ge_log_of_le_abs hR hr) (hΦ0 r)
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
        Real.pi * (Q + ε / 2) * k + (B + c₀) * ∫ r, (1 - Real.cos (k * r)) * Φ r := by
    intro k hk hkk
    have hG := hB (criticalHalfLineEnergyDomain_increment hd hk.le)
    have hsq : (∫ u, (F u + (-1) * F (u + k)) ^ 2) = ∫ u, (F u - F (u + k)) ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun u => by
        show (F u + (-1) * F (u + k)) ^ 2 = (F u - F (u + k)) ^ 2
        ring)
    rw [criticalState_fullEnergy_increment hW hthreshold hF hk.le, hsq] at hG
    have hm : 0 ≤ criticalAliasCoefficient W₀ / 2 *
        ∫ u, (F u + (-1) * F (u + k)) ^ 2 * Real.exp (-(8 * u)) :=
      mul_nonneg (div_nonneg ha.le (by norm_num))
        (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    have hEk : criticalAliasCoefficient W₀ * (Real.exp (8 * k) - 1) *
        (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) ≤ (Q + ε / 2) * k := by
      have h1 := mul_le_mul_of_nonneg_left (exp_eight_mul_sub_one_le hk.le hη hkk)
        (div_nonneg hQ.le (by norm_num : (0 : ℝ) ≤ 8))
      calc criticalAliasCoefficient W₀ * (Real.exp (8 * k) - 1) *
            (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) = Q / 8 * (Real.exp (8 * k) - 1) := by
              rw [hQdef]
              ring
        _ ≤ Q / 8 * (8 * k * (1 + η)) := h1
        _ = (Q + Q * η) * k := by ring
        _ = (Q + ε / 2) * k := by rw [hQη]
    have hA : archForm (fun u => F u + (-1) * F (u + k)) ≤
        (Q + ε / 2) * k + B * ∫ u, (F u - F (u + k)) ^ 2 := by
      linarith only [hG, hm, hEk]
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
    (add_nonneg hB0 hc₀) hk₀ hJ (mul_pos Real.pi_pos (half_pos hε))
  filter_upwards [hmain, self_mem_nhdsWithin] with k hk hk0
  have hk0' : (0 : ℝ) < k := hk0
  rw [hS1 k hk0'.le, mul_left_comm (Real.log (1 / k)) Real.pi] at hk
  have e : (Real.pi * (Q + ε / 2) + Real.pi * (ε / 2)) * k = Real.pi * ((Q + ε) * k) := by ring
  rw [e] at hk
  exact le_of_mul_le_mul_left hk Real.pi_pos

/-- **The modulus of continuity of the state**:
`log(1/k)/k · ∫ (F(u) − F(u+k))² du → 8 a ∫ F² e^{−8u}` as `k → 0⁺`. -/
theorem criticalState_tendsto_log_div_mul_sq_increment {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => Real.log (1 / k) / k * ∫ u, (F u - F (u + k)) ^ 2) (𝓝[>] 0)
      (𝓝 (8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hlow := criticalState_tendsto_sq_terminalMean_mul_log hW hthreshold hF
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = 8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := ⟨_, rfl⟩
  have hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℝ in 𝓝[>] 0,
      Real.log (1 / k) * ∫ u, (F u - F (u + k)) ^ 2 ≤ (Q + ε) * k := fun ε hε => by
    rw [hQdef]
    exact criticalState_eventually_log_mul_sq_increment_le hW hthreshold hF hε
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

/-- **The terminal square mass**: `log(1/k)/k · ∫_{−k}^0 F² → 8 a ∫ F² e^{−8u}` as `k → 0⁺`. -/
theorem criticalState_tendsto_log_div_mul_terminal_sq {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => Real.log (1 / k) / k * ∫ u in Ioo (-k) 0, F u ^ 2) (𝓝[>] 0)
      (𝓝 (8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (criticalState_tendsto_sq_terminalMean_mul_log hW hthreshold hF)
    (criticalState_tendsto_log_div_mul_sq_increment hW hthreshold hF) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk0 hk1
    exact sq_terminalMean_mul_log_le hd.meas hd.sq hk0 hk1
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk0 hk1
    have hk0' : (0 : ℝ) < k := hk0
    have hk1' : k < 1 := hk1
    exact mul_le_mul_of_nonneg_left (setIntegral_Ioo_sq_le_integral_sq_increment hd hk0')
      (div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hk0']; linarith only [hk1'])) hk0'.le)

/-- **The modulus of continuity is carried by the wall**: the increments away from the wall are of
lower order, `log(1/k)/k · ∫_{u ≤ −k} (F(u) − F(u+k))² du → 0` as `k → 0⁺`. -/
theorem criticalState_tendsto_log_div_mul_interior_sq_increment {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => Real.log (1 / k) / k * ∫ u in Iic (-k), (F u - F (u + k)) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h := (criticalState_tendsto_log_div_mul_sq_increment hW hthreshold hF).sub
    (criticalState_tendsto_log_div_mul_terminal_sq hW hthreshold hF)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk0
  have hk0' : (0 : ℝ) < k := hk0
  rw [integral_sq_increment_eq_interior_add_terminal hd.support hk0'
    (integrable_sq_increment hd hk0'.le)]
  ring

/-- **The state is flat at the wall in mean square**: with the terminal mean
`μ(k) = k⁻¹ ∫_{−k}^0 F`, `log(1/k)/k · ∫_{−k}^0 (F − μ(k))² → 0` as `k → 0⁺`. -/
theorem criticalState_tendsto_log_div_mul_terminal_variance {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => Real.log (1 / k) / k *
        ∫ u in Ioo (-k) 0, (F u - (∫ v in Ioo (-k) 0, F v) / k) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h := (criticalState_tendsto_log_div_mul_terminal_sq hW hthreshold hF).sub
    (criticalState_tendsto_sq_terminalMean_mul_log hW hthreshold hF)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk0
  have hk0' : (0 : ℝ) < k := hk0
  have e := setIntegral_Ioo_sq_affine hd.integrable hd.sq hk0'.le 1
    ((∫ v in Ioo (-k) 0, F v) / k)
  simp only [one_mul, one_pow, mul_one] at e
  exact terminal_variance_algebra hk0' e

/-- **The law of the wall in mean square.** With the sign `s` of the state at the wall,
`k⁻¹ ∫_{−k}^0 (√log(1/k) F(u) − s√(8aM))² du → 0` as `k → 0⁺`. Consequently
`√log(1/k) F → s√(8aM)` in measure on `(−k, 0)`, and the subset of `(−k, 0)` on which `F` does
not have the sign `s` has density tending to zero. -/
theorem criticalState_meanSquare_wall_law {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      (∀ᶠ k : ℝ in 𝓝[>] 0, 0 < s * ∫ u in Ioo (-k) 0, F u) ∧
      Tendsto (fun k : ℝ => 1 / k * ∫ u in Ioo (-k) 0,
          (Real.sqrt (Real.log (1 / k)) * F u -
            s * Real.sqrt (8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) ^ 2) (𝓝[>] 0) (𝓝 0) ∧
      (∀ δ : ℝ, 0 < δ → Tendsto (fun k : ℝ => volume.real (Ioo (-k) 0 ∩
          {u | δ ≤ |Real.sqrt (Real.log (1 / k)) * F u -
            s * Real.sqrt (8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))|}) / k) (𝓝[>] 0) (𝓝 0)) ∧
      Tendsto (fun k : ℝ => volume.real (Ioo (-k) 0 ∩ {u | s * F u ≤ 0}) / k)
        (𝓝[>] 0) (𝓝 0) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hM := criticalState_exponentialMass_pos hW hF
  obtain ⟨s, hs, hsign, hmean, -, -⟩ := criticalState_wall_laws hW hthreshold hF
  have hT2 := criticalState_tendsto_log_div_mul_terminal_sq hW hthreshold hF
  have hQ : 0 < 8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) :=
    mul_pos (mul_pos (by norm_num) ha) hM
  refine ⟨s, hs, hsign.mono fun k hk => hk.1, ?_⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = 8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := ⟨_, rfl⟩
  rw [← hQdef] at hmean hT2 hQ ⊢
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = s * Real.sqrt Q := ⟨_, rfl⟩
  rw [← hcdef] at hmean ⊢
  have hcc : c ^ 2 = Q := by
    rw [hcdef, mul_pow, Real.sq_sqrt hQ.le]
    rcases hs with h | h <;> rw [h] <;> norm_num
  -- the mean-square law: expand the square and use the laws of the mean and of the square mass
  have hV : Tendsto (fun k : ℝ => 1 / k * ∫ u in Ioo (-k) 0,
      (Real.sqrt (Real.log (1 / k)) * F u - c) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Q - 2 * c * c + c ^ 2 = 0 := by linear_combination -hcc
    have h := (hT2.sub (hmean.const_mul (2 * c))).add_const (c ^ 2)
    rw [hlim] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk0 hk1
    have hk0' : (0 : ℝ) < k := hk0
    have hk1' : k < 1 := hk1
    have hL : 0 ≤ Real.log (1 / k) :=
      Real.log_nonneg (by rw [le_div_iff₀ hk0']; linarith only [hk1'])
    have e := setIntegral_Ioo_sq_affine hd.integrable hd.sq hk0'.le
      (Real.sqrt (Real.log (1 / k))) c
    rw [Real.sq_sqrt hL] at e
    exact terminal_meanSquare_algebra hk0' e
  -- Chebyshev: convergence in measure
  have hmeasδ : ∀ δ : ℝ, 0 < δ → Tendsto (fun k : ℝ => volume.real (Ioo (-k) 0 ∩
      {u | δ ≤ |Real.sqrt (Real.log (1 / k)) * F u - c|}) / k) (𝓝[>] 0) (𝓝 0) := by
    intro δ hδ
    have hub : Tendsto (fun k : ℝ => 1 / δ ^ 2 * (1 / k * ∫ u in Ioo (-k) 0,
        (Real.sqrt (Real.log (1 / k)) * F u - c) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have h := hV.const_mul (1 / δ ^ 2)
      rwa [mul_zero] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with k hk0
      have hk0' : (0 : ℝ) < k := hk0
      exact div_nonneg measureReal_nonneg hk0'.le
    · filter_upwards [self_mem_nhdsWithin] with k hk0
      have hk0' : (0 : ℝ) < k := hk0
      exact terminal_chebyshev_algebra hδ hk0' (sq_mul_measureReal_terminal_le (k := k)
        ((hd.meas.const_mul (Real.sqrt (Real.log (1 / k)))).sub_const c) hδ.le
        (integrableOn_Ioo_sq_affine hd.integrable hd.sq k _ c))
  refine ⟨hV, hmeasδ, ?_⟩
  -- where `s F ≤ 0`, the deviation from `s√Q` is at least `√Q`
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hmeasδ _ hsQ) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with k hk0
    have hk0' : (0 : ℝ) < k := hk0
    exact div_nonneg measureReal_nonneg hk0'.le
  · filter_upwards [self_mem_nhdsWithin] with k hk0
    have hk0' : (0 : ℝ) < k := hk0
    have hfin : volume (Ioo (-k) (0 : ℝ) ∩ {u | Real.sqrt Q ≤
        |Real.sqrt (Real.log (1 / k)) * F u - c|}) ≠ ⊤ :=
      ((measure_mono inter_subset_left).trans_lt measure_Ioo_lt_top).ne
    have hmono : volume.real (Ioo (-k) (0 : ℝ) ∩ {u | s * F u ≤ 0}) ≤
        volume.real (Ioo (-k) (0 : ℝ) ∩ {u | Real.sqrt Q ≤
          |Real.sqrt (Real.log (1 / k)) * F u - c|}) := by
      refine measureReal_mono (fun u hu => ⟨hu.1, ?_⟩) hfin
      have hu2 : s * F u ≤ 0 := hu.2
      have hx : s * (Real.sqrt (Real.log (1 / k)) * F u) ≤ 0 := by
        have h := mul_nonneg (Real.sqrt_nonneg (Real.log (1 / k))) (neg_nonneg.mpr hu2)
        linarith only [h]
      show Real.sqrt Q ≤ |Real.sqrt (Real.log (1 / k)) * F u - c|
      rcases hs with h | h
      · rw [h, one_mul] at hx
        rw [hcdef, h, one_mul]
        exact le_trans (by linarith only [hx]) (neg_le_abs _)
      · rw [h] at hx
        rw [hcdef, h]
        exact le_trans (by linarith only [hx]) (le_abs_self _)
    exact (div_le_div_iff₀ hk0' hk0').mpr (mul_le_mul_of_nonneg_right hmono hk0'.le)

end GaloisForLFunctions.ExclusionOfTheCriticalState
