import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureGaussianGrowthExponent

/-!
# Asymptotic deviation of the zeros as HCF amplification rates at large heights

At height `t`, the Gaussian-amplified HCF diagonal `𝒜(t, σ)` grows exactly at the rate of the
deepest zero cone over `t`, `M(t) = max_γ ((Im γ)² - (Re γ - t)²)`
(`criticalFeatureGaussianAmplifiedTrace_growthExponent`).  Every zero has `|Im γ| = |β - 1/2| < 1/2`,
so each `M(t) < 1/4`, but a priori not uniformly.

**Theorem** (`zeros_deviation_le_iff_amplifiedTrace_rate_le`).  For `0 ≤ Δ` and a height `H`, the
following are equivalent:

* every zero with `|γ| ≥ H` satisfies `|β - 1/2| ≤ Δ`;
* at every height `|t| ≥ H + 1/2` and for every `ε > 0`, `𝒜(t, σ) = O(e^{σ(Δ² + ε)})`.

The second condition is up to a shift of `H` by `1/2`, which is invisible asymptotically.

**Corollary** (`asymptoticQuasiRH_iff_amplifiedTrace_rates_uniformly_below_quarter`).  The asymptotic
quasi-Riemann hypothesis `Δ∞ = limsup_{|γ|→∞} |β - 1/2| < 1/2` holds iff the HCF amplification rates
at large heights are uniformly below `1/4`.  RH is the case where all rates vanish
(`riemannHypothesis_iff_forall_criticalFeatureGaussianAmplifiedTrace_bounded`).
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The rate statement: at height `t`, `𝒜(t, σ) = O(e^{κσ})`. -/
def AmplifiedTraceRateLE (t κ : ℝ) : Prop :=
  ∃ K : ℝ, ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ K * Real.exp (κ * σ)

/-- A bounded trace has every nonnegative rate. -/
theorem amplifiedTraceRateLE_of_bounded {t κ : ℝ} (hκ : 0 ≤ κ)
    (h : ∃ C : ℝ, ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ C) :
    AmplifiedTraceRateLE t κ := by
  obtain ⟨C, hC⟩ := h
  refine ⟨|C|, fun σ hσ => (hC σ hσ).trans ?_⟩
  calc C ≤ |C| := le_abs_self C
    _ = |C| * 1 := (mul_one _).symm
    _ ≤ |C| * Real.exp (κ * σ) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp (mul_nonneg hκ hσ)) (abs_nonneg C)

/-- **Rate bound from a deviation bound.**  If every copy with `|Re z| ≥ H` has `|Im z| ≤ Δ`, then at
every height `|t| ≥ H + 1/2` the amplified trace has rate at most `Δ²`. -/
theorem amplifiedTraceRateLE_of_deviation {Δ H t : ℝ}
    (hdev : ∀ q : XiZeroCopy, H ≤ |(xiSpectralPoint q).re| → |(xiSpectralPoint q).im| ≤ Δ)
    (ht : H + 1 / 2 ≤ |t|) : AmplifiedTraceRateLE t (Δ ^ 2) := by
  by_cases hoff : ∃ q₀ : XiZeroCopy, |(xiSpectralPoint q₀).re - t| < |(xiSpectralPoint q₀).im|
  · obtain ⟨M, hM, ⟨qM, hqM⟩, hMall, ⟨K, hK⟩, -⟩ :=
      criticalFeatureGaussianAmplifiedTrace_growthExponent hoff
    -- the maximizing copy lies in the cone, hence high
    have hqMcone : |(xiSpectralPoint qM).re - t| < |(xiSpectralPoint qM).im| := by
      have h1 : ((xiSpectralPoint qM).re - t) ^ 2 < (xiSpectralPoint qM).im ^ 2 := by linarith
      exact sq_lt_sq.1 h1 |>.trans_eq (by rfl)
    have hhalf := abs_xiSpectralPoint_im_lt_half qM
    have hhigh : H ≤ |(xiSpectralPoint qM).re| := by
      have := abs_sub_abs_le_abs_sub t (xiSpectralPoint qM).re
      rw [abs_sub_comm] at this
      linarith
    have hyΔ := hdev qM hhigh
    have hMΔ : M ≤ Δ ^ 2 := by
      have h1 : (xiSpectralPoint qM).im ^ 2 ≤ Δ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hyΔ 2
      nlinarith [sq_nonneg ((xiSpectralPoint qM).re - t)]
    refine ⟨|K| + criticalFeatureHermitianEnergyTrace t, fun σ hσ => (hK σ hσ).trans ?_⟩
    have hE0 : 0 ≤ criticalFeatureHermitianEnergyTrace t :=
      tsum_nonneg fun _ => Complex.normSq_nonneg _
    have he1 : 1 ≤ Real.exp (Δ ^ 2 * σ) := Real.one_le_exp (by positivity)
    have he2 : Real.exp (σ * M) ≤ Real.exp (Δ ^ 2 * σ) := Real.exp_le_exp.2 (by nlinarith)
    calc K * Real.exp (σ * M) + criticalFeatureHermitianEnergyTrace t
        ≤ |K| * Real.exp (Δ ^ 2 * σ) + criticalFeatureHermitianEnergyTrace t * Real.exp (Δ ^ 2 * σ) :=
          add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le).trans
              (mul_le_mul_of_nonneg_left he2 (abs_nonneg K))) (le_mul_of_one_le_right hE0 he1)
      _ = (|K| + criticalFeatureHermitianEnergyTrace t) * Real.exp (Δ ^ 2 * σ) := by ring
  · push Not at hoff
    exact amplifiedTraceRateLE_of_bounded (sq_nonneg Δ)
      ((criticalFeatureGaussianAmplifiedTrace_bounded_iff t).2 fun q => hoff q)

/-- **Deviation bound from rate bounds.**  If at every height `|t| ≥ H` and every `ε > 0` the amplified
trace has rate at most `Δ² + ε`, then every copy with `|Re z| ≥ H` has `|Im z| ≤ Δ`. -/
theorem deviation_le_of_amplifiedTraceRateLE {Δ H : ℝ} (hΔ : 0 ≤ Δ)
    (hrate : ∀ t : ℝ, H ≤ |t| → ∀ ε : ℝ, 0 < ε → AmplifiedTraceRateLE t (Δ ^ 2 + ε))
    (q : XiZeroCopy) (hq : H ≤ |(xiSpectralPoint q).re|) :
    |(xiSpectralPoint q).im| ≤ Δ := by
  by_contra hbig
  push Not at hbig
  set t : ℝ := (xiSpectralPoint q).re
  have hoff : ∃ q₀ : XiZeroCopy, |(xiSpectralPoint q₀).re - t| < |(xiSpectralPoint q₀).im| :=
    ⟨q, by simp only [t, sub_self, abs_zero]; linarith [abs_nonneg Δ]⟩
  obtain ⟨M, hM, -, hMall, -, hlow⟩ := criticalFeatureGaussianAmplifiedTrace_growthExponent hoff
  have hMq : (xiSpectralPoint q).im ^ 2 ≤ M := by
    have := hMall q
    simp only [t, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero] at this
    exact this
  have hgap : Δ ^ 2 < (xiSpectralPoint q).im ^ 2 := by
    rw [← sq_abs (xiSpectralPoint q).im]
    exact pow_lt_pow_left₀ hbig hΔ two_ne_zero
  set η : ℝ := ((xiSpectralPoint q).im ^ 2 - Δ ^ 2) / 3
  have hη : 0 < η := by simp only [η]; linarith
  obtain ⟨K, hK⟩ := hrate t hq η hη
  -- the lower bound at rate `M - η` beats `K e^{(Δ² + η)σ}` for large `σ`
  have hrate_gap : Δ ^ 2 + η < M - η := by simp only [η]; linarith
  set g : ℝ := (M - η) - (Δ ^ 2 + η)
  have hg : 0 < g := by simp only [g]; linarith
  obtain ⟨σ, hSσ, hσ, hlo⟩ := hlow η hη (max 0 ((Real.log (|K| + 1)) / g + 1))
  have hσbig : Real.log (|K| + 1) < g * σ := by
    have := (le_max_right _ _).trans hSσ
    rw [← div_lt_iff₀' hg]
    linarith
  have hup := hK σ hσ
  have hexp_split : Real.exp (σ * (M - η)) = Real.exp (g * σ) * Real.exp ((Δ ^ 2 + η) * σ) := by
    rw [← Real.exp_add]; congr 1; simp only [g]; ring
  have hKlt : |K| + 1 < Real.exp (g * σ) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < |K| + 1)]
    exact Real.exp_lt_exp.2 hσbig
  have hpos : 0 < Real.exp ((Δ ^ 2 + η) * σ) := Real.exp_pos _
  have : K * Real.exp ((Δ ^ 2 + η) * σ) < Real.exp (σ * (M - η)) := by
    rw [hexp_split]
    calc K * Real.exp ((Δ ^ 2 + η) * σ) ≤ |K| * Real.exp ((Δ ^ 2 + η) * σ) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) hpos.le
      _ < Real.exp (g * σ) * Real.exp ((Δ ^ 2 + η) * σ) :=
          mul_lt_mul_of_pos_right (by linarith) hpos
  linarith

/-- **Deviation ⇔ rate law.**  For `0 ≤ Δ` and height `H`: if every copy with `|Re z| ≥ H` has
`|Im z| ≤ Δ`, every height `|t| ≥ H + 1/2` has rate `≤ Δ²`; conversely, rates `≤ Δ² + ε` at all
heights `|t| ≥ H` force `|Im z| ≤ Δ` for every copy with `|Re z| ≥ H`. -/
theorem zeros_deviation_le_iff_amplifiedTrace_rate_le {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    (∃ H : ℝ, ∀ q : XiZeroCopy, H ≤ |(xiSpectralPoint q).re| → |(xiSpectralPoint q).im| ≤ Δ) ↔
      ∃ H : ℝ, ∀ t : ℝ, H ≤ |t| → ∀ ε : ℝ, 0 < ε → AmplifiedTraceRateLE t (Δ ^ 2 + ε) := by
  constructor
  · rintro ⟨H, hH⟩
    refine ⟨H + 1 / 2, fun t ht ε hε => ?_⟩
    obtain ⟨K, hK⟩ := amplifiedTraceRateLE_of_deviation hH ht
    refine ⟨|K|, fun σ hσ => (hK σ hσ).trans ?_⟩
    calc K * Real.exp (Δ ^ 2 * σ) ≤ |K| * Real.exp (Δ ^ 2 * σ) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
      _ ≤ |K| * Real.exp ((Δ ^ 2 + ε) * σ) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (abs_nonneg K)
  · rintro ⟨H, hH⟩
    exact ⟨H, fun q hq => deviation_le_of_amplifiedTraceRateLE hΔ hH q hq⟩

/-- **Asymptotic quasi-RH as uniformly sub-quarter amplification rates.**  Some `Δ < 1/2` bounds the
deviation `|β - 1/2|` of all sufficiently high zeros iff some `κ < 1/4` bounds the HCF
amplification rates at all sufficiently large heights. -/
theorem asymptoticQuasiRH_iff_amplifiedTrace_rates_uniformly_below_quarter :
    (∃ Δ : ℝ, 0 ≤ Δ ∧ Δ < 1 / 2 ∧ ∃ H : ℝ,
        ∀ q : XiZeroCopy, H ≤ |(xiSpectralPoint q).re| → |(xiSpectralPoint q).im| ≤ Δ) ↔
      ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 / 4 ∧ ∃ H : ℝ, ∀ t : ℝ, H ≤ |t| → AmplifiedTraceRateLE t κ := by
  constructor
  · rintro ⟨Δ, hΔ0, hΔ1, H, hH⟩
    refine ⟨Δ ^ 2, sq_nonneg Δ, by nlinarith, H + 1 / 2, fun t ht => ?_⟩
    exact amplifiedTraceRateLE_of_deviation hH ht
  · rintro ⟨κ, hκ0, hκ1, H, hH⟩
    set Δ : ℝ := Real.sqrt ((κ + 1 / 4) / 2)
    have hΔ0 : 0 ≤ Δ := Real.sqrt_nonneg _
    have hΔsq : Δ ^ 2 = (κ + 1 / 4) / 2 := Real.sq_sqrt (by linarith)
    have hΔ1 : Δ < 1 / 2 := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
    refine ⟨Δ, hΔ0, hΔ1, H, fun q hq => deviation_le_of_amplifiedTraceRateLE hΔ0
      (fun t ht ε hε => ?_) q hq⟩
    obtain ⟨K, hK⟩ := hH t ht
    refine ⟨|K|, fun σ hσ => (hK σ hσ).trans ?_⟩
    calc K * Real.exp (κ * σ) ≤ |K| * Real.exp (κ * σ) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
      _ ≤ |K| * Real.exp ((Δ ^ 2 + ε) * σ) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg K)
          rw [hΔsq]; nlinarith

end

end RHTower
