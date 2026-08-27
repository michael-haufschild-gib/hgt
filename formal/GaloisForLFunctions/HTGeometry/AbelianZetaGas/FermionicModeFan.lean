import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ParityShellFan

/-!
# Fermionic mode-activity fan

Bernoulli exclusion changes the activity probability from `q` to `q/(1+q)`, a factor between
`1/2` and `1` in the gas chamber.  It therefore leaves every exact-depth Borel--Cantelli wall
unchanged.  This is deliberately separate from the fermionic order organ, which matches only the
odd-depth bosonic sector.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace AbelianZetaParameters

/-- Bernoulli activity probability of a fermionic mode. -/
def fermionicActivity (θ : AbelianZetaParameters) (m : AbelianZetaMode) : ℝ :=
  θ.ratio m / (1 + θ.ratio m)

theorem fermionicActivity_nonneg (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    0 ≤ θ.fermionicActivity m := by
  rw [fermionicActivity]
  exact div_nonneg (θ.ratio_nonneg m) (by linarith [θ.ratio_nonneg m])

theorem fermionicActivity_le_one (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.fermionicActivity m ≤ 1 := by
  rw [fermionicActivity]
  have hden : 0 < 1 + θ.ratio m := by linarith [θ.ratio_nonneg m]
  rw [div_le_one hden]
  linarith

/-- Bernoulli occupation law with weights proportional to `1, q`. -/
def fermionicModeLaw (θ : AbelianZetaParameters) (m : AbelianZetaMode) : Measure ℕ :=
  ENNReal.ofReal (1 - θ.fermionicActivity m) • Measure.dirac 0 +
    ENNReal.ofReal (θ.fermionicActivity m) • Measure.dirac 1

instance fermionicModeLaw_isProbability (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    IsProbabilityMeasure (θ.fermionicModeLaw m) := by
  constructor
  rw [fermionicModeLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr (θ.fermionicActivity_le_one m))
    (θ.fermionicActivity_nonneg m)]
  simp

theorem fermionicModeLaw_occupied (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.fermionicModeLaw m {0}ᶜ = ENNReal.ofReal (θ.fermionicActivity m) := by
  rw [fermionicModeLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

/-- Full independent fermionic mode field. -/
def fermionicGasMeasure (θ : AbelianZetaParameters) : Measure (AbelianZetaMode → ℕ) :=
  Measure.infinitePi θ.fermionicModeLaw

instance fermionicGasMeasure_isProbability (θ : AbelianZetaParameters) :
    IsProbabilityMeasure θ.fermionicGasMeasure := by
  dsimp [fermionicGasMeasure]
  infer_instance

theorem fermionicModeLaw_exactDepthEvent
    (θ : AbelianZetaParameters) (g : ℕ) (m : AbelianZetaMode) :
    θ.fermionicModeLaw m (θ.exactDepthEvent g m) =
      ENNReal.ofReal
        (({m : AbelianZetaMode | AbelianZetaMode.depth m = g}.indicator θ.fermionicActivity) m) := by
  by_cases h : AbelianZetaMode.depth m = g
  · simp [exactDepthEvent, h, θ.fermionicModeLaw_occupied]
  · simp [exactDepthEvent, h]

/-- Bernoulli activity is at least half the bosonic activity throughout the gas chamber. -/
theorem ratio_le_two_mul_fermionicActivity (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.ratio m ≤ 2 * θ.fermionicActivity m := by
  rw [fermionicActivity]
  have hden : 0 < 1 + θ.ratio m := by linarith [θ.ratio_nonneg m]
  rw [show 2 * (θ.ratio m / (1 + θ.ratio m)) =
    (2 * θ.ratio m) / (1 + θ.ratio m) by ring, le_div_iff₀ hden]
  have hq0 := θ.ratio_nonneg m
  have hq1 := θ.ratio_le_one m
  nlinarith

private theorem modeLaw_exactDepthEvent_le_two_mul_fermionic
    (θ : AbelianZetaParameters) (g : ℕ) (m : AbelianZetaMode) :
    θ.modeLaw m (θ.exactDepthEvent g m) ≤
      2 * θ.fermionicModeLaw m (θ.exactDepthEvent g m) := by
  rw [θ.modeLaw_exactDepthEvent, θ.fermionicModeLaw_exactDepthEvent]
  by_cases h : AbelianZetaMode.depth m = g
  · have hm : m ∈ {m : AbelianZetaMode | AbelianZetaMode.depth m = g} := h
    simp only [Set.indicator_of_mem hm]
    calc
      ENNReal.ofReal (θ.ratio m) ≤ ENNReal.ofReal (2 * θ.fermionicActivity m) :=
        ENNReal.ofReal_le_ofReal (θ.ratio_le_two_mul_fermionicActivity m)
      _ = 2 * ENNReal.ofReal (θ.fermionicActivity m) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  · have hm : m ∉ {m : AbelianZetaMode | AbelianZetaMode.depth m = g} := h
    simp only [Set.indicator_of_notMem hm]
    simp

theorem tsum_fermionic_exactDepthEvent_eq_top
    (θ : AbelianZetaParameters) {g : ℕ} (hg : 1 ≤ g)
    (hwall : (g : ℝ) * θ.sigma + θ.tau ≤ 1) :
    (∑' m : AbelianZetaMode, θ.fermionicModeLaw m (θ.exactDepthEvent g m)) = ∞ := by
  have hboson := θ.tsum_exactDepthEvent_eq_top hg hwall
  have hle : (∞ : ℝ≥0∞) ≤
      2 * ∑' m : AbelianZetaMode, θ.fermionicModeLaw m (θ.exactDepthEvent g m) := by
    calc
      (∞ : ℝ≥0∞) = ∑' m : AbelianZetaMode, θ.modeLaw m (θ.exactDepthEvent g m) := hboson.symm
      _ ≤ ∑' m : AbelianZetaMode,
          2 * θ.fermionicModeLaw m (θ.exactDepthEvent g m) :=
        ENNReal.tsum_le_tsum fun m => modeLaw_exactDepthEvent_le_two_mul_fermionic θ g m
      _ = 2 * ∑' m : AbelianZetaMode,
          θ.fermionicModeLaw m (θ.exactDepthEvent g m) := by
        rw [ENNReal.tsum_mul_left]
  have hmul : 2 * ∑' m : AbelianZetaMode,
      θ.fermionicModeLaw m (θ.exactDepthEvent g m) = ∞ := top_unique hle
  rw [ENNReal.mul_eq_top] at hmul
  rcases hmul with hsum | htwo
  · exact hsum.2
  · norm_num at htwo

/-- Fermionic Bernoulli modes condense on every full bosonic depth wall. -/
theorem fermionic_measure_infinite_exactDepth_eq_one
    (θ : AbelianZetaParameters) {g : ℕ} (hg : 1 ≤ g)
    (hwall : (g : ℝ) * θ.sigma + θ.tau ≤ 1) :
    θ.fermionicGasMeasure
      {k | (localHitSet (θ.exactDepthEvent g) k).Infinite} = 1 := by
  exact measure_infiniteHit_eq_one θ.fermionicModeLaw (θ.exactDepthEvent g) modeEquivNat
    (θ.tsum_fermionic_exactDepthEvent_eq_top hg hwall)

/-- Temperature form: fermionic mode-activity fan is the full `{1/g}` fan. -/
theorem fermionic_temperature_infinite_exactDepth_eq_one
    {σ : ℝ} (hσ : 0 < σ) {g : ℕ} (hg : 1 ≤ g) (hwall : σ ≤ 1 / (g : ℝ)) :
    (temperatureParameters σ hσ).fermionicGasMeasure
      {k | (localHitSet ((temperatureParameters σ hσ).exactDepthEvent g) k).Infinite} = 1 := by
  apply fermionic_measure_infinite_exactDepth_eq_one _ hg
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hg)
  field_simp at hwall
  simpa [temperatureParameters, mul_comm] using hwall

end AbelianZetaParameters

end

end GaloisForLFunctions.HTGeometry
