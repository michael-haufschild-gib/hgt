import GaloisForLFunctions.SquareRootThreshold.TheContactApertureOfTheGroundEnergyPath
import GaloisForLFunctions.SquareRootThreshold.EqualDepthClusterInArbitraryBackground
import GaloisForLFunctions.RHTower.ClusterRobustHodgeExclusion
import GaloisForLFunctions.RHTower.ZetaWeilFormHeightReduction

/-!
# The Visibility Tradeoff, Excluded Depth Below a Height, and Height-Reduction Duality

This module formalizes the quantitative visibility tradeoff between aperture `R` (reading prime
powers up to arithmetic length `X = e^{2R}`), local cluster multiplicity `n`, height cutoff `T`,
and excluded off-line depth `δ`:

1. **Cluster-Robust Excluded-Depth Tradeoff `(δ(n, R), T(n, R))` and Contact-Aperture Bound
   (`clusterHorizonHeight`, `abs_re_sub_half_lt_of_hodgeIndex_of_local_count`,
   `zetaClusterHorizonHeight`, `zeta_abs_re_sub_half_lt_of_hodgeIndex`,
   `zeta_abs_re_sub_half_lt_of_zetaWindowPositive`, `zeta_abs_re_sub_half_lt_of_lt_contact`,
   `zetaContactAperture_le_of_offLine_zero`):**
   - For any configuration `Z` with local count `N(t, t+1] ≤ A₀ log(|t| + 3)`, the level-`R` Hodge
     index (`R ≥ e⁶`) excludes all zeros `ρ₀` of depth `|Re ρ₀ − ½| ≥ 1/R = 2/log X` and local
     window count `Nd(Im ρ₀ − 101, Im ρ₀ + 101) ≤ n` up to the explicit height
     `clusterHorizonHeight A₀ n R = exp(R/100 − (n + 1)(log R)²)/A₀ − 4`.
   - For `ζ` unconditionally (via the Riemann–von Mangoldt local count), `HodgeIndexAtLevel zetaZeroConfig R`
     (and hence `ZetaWindowPositive R` or `R < zetaContactAperture`) excludes all zeros of depth
     `|Re ρ − ½| ≥ 1/R` up to `zetaClusterHorizonHeight A₀ R = exp(R/(10⁵ A₀ (log R)²)) − 306`.
   - Contrapositively, **any** off-line zero `ρ` of `ζ` with `|Re ρ − ½| ≥ δ > 0` and `|Im ρ| ≥ 2`
     (with no near-top or amplitude hypothesis) bounds the contact aperture above:
     `zetaContactAperture ≤ R` for every `R ≥ max(e⁶, 1/δ)` with
     `|Im ρ| ≤ zetaClusterHorizonHeight A₀ R`.

2. **Exact Inversion of the Near-Top Visibility Lags and Equal-Depth Cluster Tradeoff
   (`nearTopNumerator`, `nearTopDrift`, `nearTopExcludedDepth`,
   `nearTopLag_le_iff_nearTopExcludedDepth_le`, `near_top_depth_lt_of_modulated_nonneg`,
   `oneParamNumerator`, `oneParamDrift`, `oneParamExcludedDepth`,
   `oneParamLag_le_iff_oneParamExcludedDepth_le`, `near_top_depth_lt_of_oneParam_nonneg`,
   `near_top_depth_lt_of_le_contactAperture`, `equalDepthClusterExcludedDepth`,
   `equalDepthCluster_visible_of_excludedDepth_le`):**
   - Both `nearTopLag w γ₀ δ₀` and `oneParamLag w η δ₀` decompose as `Numerator / δ₀ + Drift` with
     `Numerator > 0` and `Drift` independent of `δ₀`. Inverting at lag budget `V = 2(R − w) > Drift`
     gives the exact excluded-depth thresholds `nearTopExcludedDepth w γ₀ V` and
     `oneParamExcludedDepth w η V`.
   - For an `n`-pair equal-depth cluster at grid step `ℓ`, each additional pair costs `ℓ/2` of
     aperture, giving the excluded-depth bound `equalDepthClusterExcludedDepth`.

3. **Two-Way Visibility and Height-Reduction Duality at Arithmetic Length `X = e^{2R}`
   (`zeta_visibility_and_height_reduction_tradeoff`):**
   Pairs the forward aperture-to-zero depth exclusion below `zetaClusterHorizonHeight A₀ R` with
   the converse zero-to-aperture height reduction below `zetaHorizonHeight A₀ R ≤ exp(7000 e^R + O(1))`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate BigOperators

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### 1. Cluster-robust excluded-depth tradeoff `(δ(n, R), T(n, R))` and contact-aperture law -/

/-- Window positivity of `ζ` at aperture `R` implies the level-`R` Hodge index. -/
theorem hodgeIndexAtLevel_of_zetaWindowPositive {R : ℝ} (h : ZetaWindowPositive R) :
    HodgeIndexAtLevel zetaZeroConfig R :=
  fun _ hf hfs _ _ => re_W_nonneg_of_zetaWindowPositive h hf hfs

/-- Every positive aperture below `zetaContactAperture` satisfies the Hodge index. -/
theorem hodgeIndexAtLevel_of_lt_contact {R : ℝ} (h0 : 0 < R) (h : R < zetaContactAperture) :
    HodgeIndexAtLevel zetaZeroConfig R :=
  hodgeIndexAtLevel_of_zetaWindowPositive (zetaWindowPositive_of_lt_contact h0 h)

/-- The cluster-robust height cutoff `T(A₀, n, R) = exp(R/100 − (n + 1)(log R)²)/A₀ − 4` below
which a zero with at most `n` neighbours in `[γ₀ − 101, γ₀ + 101]` is visible at aperture `R`. -/
def clusterHorizonHeight (A₀ : ℝ) (n : ℕ) (R : ℝ) : ℝ :=
  Real.exp (R / 100 - ((n : ℝ) + 1) * Real.log R ^ 2) / A₀ - 4

/-- Height condition equivalence for `clusterHorizonHeight`: whenever `A₀ > 0` and
`|γ₀| ≤ clusterHorizonHeight A₀ n R`, the size bound
`100((n + 1)(log R)² + log(A₀(|γ₀| + 4))) ≤ R` holds. -/
theorem size_le_of_abs_le_clusterHorizonHeight {A₀ : ℝ} (hA₀ : 0 < A₀) (n : ℕ) (R γ₀ : ℝ)
    (hγ : |γ₀| ≤ clusterHorizonHeight A₀ n R) :
    100 * (((n : ℝ) + 1) * Real.log R ^ 2 + Real.log (A₀ * (|γ₀| + 4))) ≤ R := by
  have h1 : |γ₀| + 4 ≤ Real.exp (R / 100 - ((n : ℝ) + 1) * Real.log R ^ 2) / A₀ := by
    unfold clusterHorizonHeight at hγ
    linarith
  have h2 : A₀ * (|γ₀| + 4) ≤ Real.exp (R / 100 - ((n : ℝ) + 1) * Real.log R ^ 2) := by
    rwa [le_div_iff₀ hA₀, mul_comm] at h1
  have hpos : 0 < A₀ * (|γ₀| + 4) := mul_pos hA₀ (by linarith [abs_nonneg γ₀])
  have hlog : Real.log (A₀ * (|γ₀| + 4)) ≤ R / 100 - ((n : ℝ) + 1) * Real.log R ^ 2 := by
    calc Real.log (A₀ * (|γ₀| + 4))
        ≤ Real.log (Real.exp (R / 100 - ((n : ℝ) + 1) * Real.log R ^ 2)) :=
          Real.log_le_log hpos h2
      _ = R / 100 - ((n : ℝ) + 1) * Real.log R ^ 2 := Real.log_exp _
  linarith

/-- **Cluster-robust visibility below `clusterHorizonHeight`.** If `ρ₀ ∈ Z.carrier` has depth
`|Re ρ₀ − ½| ≥ δ ≥ 1/R`, height `2 ≤ |Im ρ₀| ≤ clusterHorizonHeight A₀ n R`, and local window
count `Z.Nd (Im ρ₀ − 101) (Im ρ₀ + 101) ≤ n`, then the level-`R` Hodge index fails (`R ≥ e⁶`). -/
theorem not_hodgeIndex_of_le_clusterHorizonHeight (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : δ ≤ |ρ₀.re - 1 / 2|)
    (hγ2 : 2 ≤ |ρ₀.im|) {R : ℝ} (hR6 : Real.exp 6 ≤ R) (hRδ : 1 / δ ≤ R) {n : ℕ}
    (hn : Z.Nd (ρ₀.im - 101) (ρ₀.im + 101) ≤ n)
    (hγT : |ρ₀.im| ≤ clusterHorizonHeight A₀ n R) :
    ¬ HodgeIndexAtLevel Z R :=
  not_hodgeIndex_below_cluster_horizon Z hA₀ hloc hρ₀ hδ hre hγ2 hR6 hRδ hn
    (size_le_of_abs_le_clusterHorizonHeight (by linarith) n R ρ₀.im hγT)

/-- **Excluded-depth law `δ(n, R) = 1/R` below `clusterHorizonHeight A₀ n R`.** Under
`HodgeIndexAtLevel Z R` (`R ≥ e⁶`), every zero `ρ₀ ∈ Z.carrier` with
`2 ≤ |Im ρ₀| ≤ clusterHorizonHeight A₀ n R` and `Z.Nd (Im ρ₀ − 101) (Im ρ₀ + 101) ≤ n` satisfies
`|Re ρ₀ − ½| < 1/R`. -/
theorem abs_re_sub_half_lt_of_hodgeIndex_of_local_count (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {R : ℝ} (hR6 : Real.exp 6 ≤ R) (hHodge : HodgeIndexAtLevel Z R)
    {n : ℕ} {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hγ2 : 2 ≤ |ρ₀.im|)
    (hn : Z.Nd (ρ₀.im - 101) (ρ₀.im + 101) ≤ n)
    (hγT : |ρ₀.im| ≤ clusterHorizonHeight A₀ n R) :
    |ρ₀.re - 1 / 2| < 1 / R := by
  by_contra hge
  push Not at hge
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos 6) hR6
  have hδ0 : 0 < 1 / R := one_div_pos.mpr hR0
  exact not_hodgeIndex_of_le_clusterHorizonHeight Z hA₀ hloc hρ₀ hδ0 hge hγ2 hR6
    (by rw [one_div_one_div]) hn hγT hHodge

/-- The unconditional cluster horizon height `T_ζ(A₀, R) = exp(R / (10⁵ A₀ (log R)²)) − 306`
for `ζ` at aperture `R`. -/
def zetaClusterHorizonHeight (A₀ R : ℝ) : ℝ :=
  Real.exp (R / (10 ^ 5 * A₀ * Real.log R ^ 2)) - 306

/-- Whenever `A₀ > 0`, `R ≥ e⁶`, and `|γ| ≤ zetaClusterHorizonHeight A₀ R`, the size condition
`10⁵ A₀ log(|γ| + 306) (log R)² ≤ R` holds. -/
theorem size_le_of_abs_le_zetaClusterHorizonHeight {A₀ R γ : ℝ} (hA₀ : 0 < A₀)
    (hR6 : Real.exp 6 ≤ R) (hγ : |γ| ≤ zetaClusterHorizonHeight A₀ R) :
    10 ^ 5 * A₀ * Real.log (|γ| + 306) * Real.log R ^ 2 ≤ R := by
  have hlogR : 6 ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 6) hR6
    rwa [Real.log_exp] at this
  have hden : 0 < 10 ^ 5 * A₀ * Real.log R ^ 2 := by positivity
  have h1 : |γ| + 306 ≤ Real.exp (R / (10 ^ 5 * A₀ * Real.log R ^ 2)) := by
    unfold zetaClusterHorizonHeight at hγ
    linarith
  have hlog : Real.log (|γ| + 306) ≤ R / (10 ^ 5 * A₀ * Real.log R ^ 2) := by
    calc Real.log (|γ| + 306)
        ≤ Real.log (Real.exp (R / (10 ^ 5 * A₀ * Real.log R ^ 2))) :=
          Real.log_le_log (by linarith [abs_nonneg γ]) h1
      _ = R / (10 ^ 5 * A₀ * Real.log R ^ 2) := Real.log_exp _
  have hmul := (le_div_iff₀ hden).mp hlog
  linarith

/-- **Unconditional excluded-depth law for `ζ` under the level-`R` Hodge index.** There is
`A₀ ≥ 1` such that for every aperture `R ≥ e⁶` with `HodgeIndexAtLevel zetaZeroConfig R`, every
zero `ρ ∈ zetaZeroConfig.carrier` with `2 ≤ |Im ρ| ≤ zetaClusterHorizonHeight A₀ R` has depth
`|Re ρ − ½| < 1/R`. -/
theorem zeta_abs_re_sub_half_lt_of_hodgeIndex :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ R : ℝ, Real.exp 6 ≤ R → HodgeIndexAtLevel zetaZeroConfig R →
      ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| → |ρ.im| ≤ zetaClusterHorizonHeight A₀ R →
        |ρ.re - 1 / 2| < 1 / R := by
  obtain ⟨A₀, hA₀, hexcl⟩ := zeta_hodge_index_cluster_horizon
  refine ⟨A₀, hA₀, fun R hR6 hHodge ρ hρ hγ2 hγT => ?_⟩
  by_contra hge
  push Not at hge
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos 6) hR6
  exact hexcl (1 / R) (one_div_pos.mpr hR0) ρ hρ hge hγ2 R hR6 (by rw [one_div_one_div])
    (size_le_of_abs_le_zetaClusterHorizonHeight (by linarith) hR6 hγT) hHodge

/-- **Excluded-depth law for `ζ` under `ZetaWindowPositive R`.** -/
theorem zeta_abs_re_sub_half_lt_of_zetaWindowPositive :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ R : ℝ, Real.exp 6 ≤ R → ZetaWindowPositive R →
      ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| → |ρ.im| ≤ zetaClusterHorizonHeight A₀ R →
        |ρ.re - 1 / 2| < 1 / R := by
  obtain ⟨A₀, hA₀, h⟩ := zeta_abs_re_sub_half_lt_of_hodgeIndex
  exact ⟨A₀, hA₀, fun R hR6 hW => h R hR6 (hodgeIndexAtLevel_of_zetaWindowPositive hW)⟩

/-- **Excluded-depth law for `ζ` below `zetaContactAperture`.** -/
theorem zeta_abs_re_sub_half_lt_of_lt_contact :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ R : ℝ, Real.exp 6 ≤ R → R < zetaContactAperture →
      ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| → |ρ.im| ≤ zetaClusterHorizonHeight A₀ R →
        |ρ.re - 1 / 2| < 1 / R := by
  obtain ⟨A₀, hA₀, h⟩ := zeta_abs_re_sub_half_lt_of_hodgeIndex
  refine ⟨A₀, hA₀, fun R hR6 hlt => h R hR6 ?_⟩
  exact hodgeIndexAtLevel_of_lt_contact (lt_of_lt_of_le (Real.exp_pos 6) hR6) hlt

/-- **Every off-line zero of `ζ` bounds `zetaContactAperture` from above, with no near-top or
amplitude hypothesis.** There is `A₀ ≥ 1` such that for any zero `ρ ∈ zetaZeroConfig.carrier` with
`0 < δ ≤ |Re ρ − ½|` and `2 ≤ |Im ρ|`, and any aperture `R ≥ max(e⁶, 1/δ)` satisfying
`|Im ρ| ≤ zetaClusterHorizonHeight A₀ R`, we have `zetaContactAperture ≤ R`. -/
theorem zetaContactAperture_le_of_offLine_zero :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (ρ : ℂ), ρ ∈ zetaZeroConfig.carrier → ∀ (δ : ℝ), 0 < δ →
      δ ≤ |ρ.re - 1 / 2| → 2 ≤ |ρ.im| → ∀ (R : ℝ), Real.exp 6 ≤ R → 1 / δ ≤ R →
        |ρ.im| ≤ zetaClusterHorizonHeight A₀ R → zetaContactAperture ≤ R := by
  obtain ⟨A₀, hA₀, h⟩ := zeta_abs_re_sub_half_lt_of_lt_contact
  refine ⟨A₀, hA₀, fun ρ hρ δ hδ hre hγ2 R hR6 hRδ hγT => ?_⟩
  by_contra hlt
  push Not at hlt
  have hlt_depth := h R hR6 hlt ρ hρ hγ2 hγT
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos 6) hR6
  have h1 : 1 / R ≤ δ := (one_div_le hR0 hδ).mpr hRδ
  linarith

/-! ### 2. Exact inversion of the near-top visibility lags and equal-depth cluster tradeoff -/

/-- The depth-independent numerator of `nearTopLag w γ₀ δ₀`. -/
def nearTopNumerator (w γ₀ : ℝ) : ℝ :=
  8 * (13 * π * nearTopOrder w γ₀ + 4 +
    |Real.log (160 * Real.log (180 * recordHeightEnvelope w γ₀) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)|)

/-- The depth-independent coherence drift of `nearTopLag w γ₀ δ₀`. -/
def nearTopDrift (w γ₀ : ℝ) : ℝ :=
  w + 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScale w γ₀

/-- The excluded near-top depth at lag budget `V` for the family modulated to height `γ₀`. -/
def nearTopExcludedDepth (w γ₀ V : ℝ) : ℝ :=
  nearTopNumerator w γ₀ / (V - nearTopDrift w γ₀)

theorem nearTopLag_eq_div_add (w γ₀ δ₀ : ℝ) :
    nearTopLag w γ₀ δ₀ = nearTopNumerator w γ₀ / δ₀ + nearTopDrift w γ₀ := by
  unfold nearTopLag nearTopNumerator nearTopDrift
  ring

theorem nearTopNumerator_pos (w γ₀ : ℝ) : 0 < nearTopNumerator w γ₀ := by
  unfold nearTopNumerator
  have h1 : 0 ≤ 13 * π * (nearTopOrder w γ₀ : ℝ) := by positivity
  have h2 : 0 ≤ |Real.log (160 * Real.log (180 * recordHeightEnvelope w γ₀) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)| := abs_nonneg _
  linarith

/-- **Exact depth-lag inversion for the modulated family.** For `δ₀ > 0` and
`nearTopDrift w γ₀ < V`, `nearTopLag w γ₀ δ₀ ≤ V` iff `nearTopExcludedDepth w γ₀ V ≤ δ₀`. -/
theorem nearTopLag_le_iff_nearTopExcludedDepth_le {w γ₀ δ₀ V : ℝ} (hδ₀ : 0 < δ₀)
    (hV : nearTopDrift w γ₀ < V) :
    nearTopLag w γ₀ δ₀ ≤ V ↔ nearTopExcludedDepth w γ₀ V ≤ δ₀ := by
  rw [nearTopLag_eq_div_add, nearTopExcludedDepth, ← le_sub_iff_add_le,
    div_le_iff₀ hδ₀, div_le_iff₀ (sub_pos.mpr hV), mul_comm]

/-- **Excluded near-top depth under modulated lag positivity.** If the difference tests modulated
to `γ₀ = Im z₀` are Weil nonnegative on `[0, V]` (`V > nearTopDrift w γ₀`) and `½ + z₀` is
`1/V`-near the top, then `Re z₀ < nearTopExcludedDepth w (Im z₀) V`. -/
theorem near_top_depth_lt_of_modulated_nonneg {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (hγ : 1280 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) * (1 + z₀.im) ^ 4)
    {V : ℝ} (hVd : nearTopDrift w z₀.im < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re) :
    z₀.re < nearTopExcludedDepth w z₀.im V := by
  by_contra hge
  push Not at hge
  have hV := (nearTopLag_le_iff_nearTopExcludedDepth_le hre₀ hVd).mpr hge
  obtain ⟨v, hv, hneg⟩ := zeta_near_top_visible_at_polylog_lag hw hz₀ hre₀ hTw hγ hV htop
  exact absurd (hpos v hv) (not_le.mpr hneg)

/-- The depth-independent numerator of `oneParamLag w η δ₀`. -/
def oneParamNumerator (w η : ℝ) : ℝ :=
  8 * (13 * π * oneParamOrder w η + 4 +
    |Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))|)

/-- The depth-independent coherence drift of `oneParamLag w η δ₀`. -/
def oneParamDrift (w η : ℝ) : ℝ :=
  w + 8 * w * Real.exp (w / 2) * bumpMass w / oneParamScale w η

/-- The excluded near-top depth at lag budget `V` for the one-parameter family `P_v`. -/
def oneParamExcludedDepth (w η V : ℝ) : ℝ :=
  oneParamNumerator w η / (V - oneParamDrift w η)

theorem oneParamLag_eq_div_add (w η δ₀ : ℝ) :
    oneParamLag w η δ₀ = oneParamNumerator w η / δ₀ + oneParamDrift w η := by
  unfold oneParamLag oneParamNumerator oneParamDrift
  ring

theorem oneParamNumerator_pos (w η : ℝ) : 0 < oneParamNumerator w η := by
  unfold oneParamNumerator
  have h1 : 0 ≤ 13 * π * (oneParamOrder w η : ℝ) := by positivity
  have h2 : 0 ≤ |Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))| := abs_nonneg _
  linarith

/-- **Exact depth-lag inversion for the one-parameter family `P_v`.** For `δ₀ > 0` and
`oneParamDrift w η < V`, `oneParamLag w η δ₀ ≤ V` iff `oneParamExcludedDepth w η V ≤ δ₀`. -/
theorem oneParamLag_le_iff_oneParamExcludedDepth_le {w η δ₀ V : ℝ} (hδ₀ : 0 < δ₀)
    (hV : oneParamDrift w η < V) :
    oneParamLag w η δ₀ ≤ V ↔ oneParamExcludedDepth w η V ≤ δ₀ := by
  rw [oneParamLag_eq_div_add, oneParamExcludedDepth, ← le_sub_iff_add_le,
    div_le_iff₀ hδ₀, div_le_iff₀ (sub_pos.mpr hV), mul_comm]

/-- **Excluded near-top depth under one-parameter lag positivity.** If `P_v ≥ 0` on `[0, V]`
(`V > oneParamDrift w η`) and `½ + z₀` is `1/V`-near the top with `0 < η ≤ |h_w(−iz₀)|`, then
`Re z₀ < oneParamExcludedDepth w η V`. -/
theorem near_top_depth_lt_of_oneParam_nonneg {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hVd : oneParamDrift w η < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re) :
    z₀.re < oneParamExcludedDepth w η V := by
  by_contra hge
  push Not at hge
  have hV := (oneParamLag_le_iff_oneParamExcludedDepth_le hre₀ hVd).mpr hge
  obtain ⟨v, hv, hneg⟩ := one_param_near_top_visible_at_explicit_lag hw hz₀ hre₀ hη hηle hV htop
  exact absurd (hpos v hv) (not_le.mpr hneg)

/-- **Excluded near-top depth at any certified aperture `R < zetaContactAperture`.** For
`V = 2(R − w) > oneParamDrift w η` with `R < zetaContactAperture`, every `1/V`-near-top zero
`½ + z₀` with `0 < η ≤ |h_w(−iz₀)|` satisfies `Re z₀ < oneParamExcludedDepth w η (2(R − w))`. -/
theorem near_top_depth_lt_of_lt_contactAperture {w R : ℝ} (hw : 0 < w)
    (hR : R < zetaContactAperture) {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier)
    (hre₀ : 0 < z₀.re) {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    (hVd : oneParamDrift w η < 2 * (R - w))
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / (2 * (R - w))) :
    z₀.re < oneParamExcludedDepth w η (2 * (R - w)) := by
  by_contra hge
  push Not at hge
  have hV := (oneParamLag_le_iff_oneParamExcludedDepth_le hre₀ hVd).mpr hge
  have hcle := zetaContactAperture_le_of_near_top_zero hw hz₀ hre₀ hη hηle hV htop
  linarith

/-- The excluded-depth threshold for an `n`-pair equal-depth cluster at grid step `ℓ` and
aperture `R > (n + 2)ℓ/2 + w`. -/
def equalDepthClusterExcludedDepth (Z : ZeroConfig) {n : ℕ} (b : ℝ → ℂ) (δ : ℝ)
    (γ : Fin n → ℝ) (c ℓ w R : ℝ) : ℝ :=
  max 0 (Real.log ((2 * onLineMassOf Z b + 3 * ∑ k, ‖pairWeight b δ (γ k)‖) / c)) /
    (2 * R - (n + 2) * ℓ - 2 * w)

/-- **Equal-depth `n`-pair cluster visibility by depth inversion.** Under the hypotheses of
`equalDepthCluster_visible`, there is `c > 0` such that for every aperture
`R > (n + 2)ℓ/2 + w`, if `equalDepthClusterExcludedDepth Z b δ γ c ℓ w R ≤ δ`, then `Z` is visible
at aperture `R`. -/
theorem equalDepthCluster_visible_of_excludedDepth_le (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {n : ℕ} (hn : 0 < n) (γ : Fin n → ℝ) (hγ : Function.Injective γ) {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ k, heightPoint δ (γ k) ∈ Z.carrier) (hm : ∀ k, heightPoint (-δ) (γ k) ∈ Z.carrier)
    (hmp : ∀ k, Z.mult (heightPoint δ (γ k)) = 1) (hmm : ∀ k, Z.mult (heightPoint (-δ) (γ k)) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨
      ∃ k, ρ = heightPoint δ (γ k) ∨ ρ = heightPoint (-δ) (γ k))
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hsep : Function.Injective fun k => cexp (I * γ k * ℓ))
    (hQ : ∀ k, pairWeight b δ (γ k) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, (n + 2) * ℓ / 2 + w < R →
      equalDepthClusterExcludedDepth Z b δ γ c ℓ w R ≤ δ →
        ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-R) R ∧ (Z.W f f).re < 0 := by
  obtain ⟨c, hc, hvis⟩ := equalDepthCluster_visible Z hZ hn γ hγ hδ hp hm hmp hmm hon hb hbs hℓ
    hsep hQ
  refine ⟨c, hc, fun R hR hdepth => hvis R ?_⟩
  unfold equalDepthClusterExcludedDepth at hdepth
  have hden : 0 < 2 * R - (n + 2) * ℓ - 2 * w := by linarith
  have hmul := (div_le_iff₀ hden).mp hdepth
  have hdiv : 1 / (2 * δ) * max 0 (Real.log ((2 * onLineMassOf Z b +
      3 * ∑ k, ‖pairWeight b δ (γ k)‖) / c)) ≤ R - (n + 2) * ℓ / 2 - w := by
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    linarith
  linarith

/-! ### 3. Two-way visibility and height-reduction duality at arithmetic length `X = e^{2R}` -/

/-- **Two-way visibility and height-reduction tradeoff at aperture `R` (arithmetic length `X = e^{2R}`).**
There exist Riemann–von Mangoldt constants `A₀, A₁ ≥ 1` such that for every aperture `R > 0`:
1. **(Archimedean horizon height scale):** `log(zetaHorizonHeight A₀ R) ≤ 7000 e^R + log A₀ + 160`.
2. **(Zero-to-aperture floor reduction):** If every zero of `ζ` up to height
   `T ≥ zetaHorizonHeight A₀ R` has depth `|Re ρ − ½| ≤ δ` (`0 ≤ δ ≤ ½`) and unit-window off-line
   multiplicity at most `D`, then every polar-constrained `C²` test on `[-R, R]` satisfies
   `Re W_ζ(f, f) ≥ −(7000(2R + 3)D e^{2δ(R + 2)} + 2) ∫ ‖f‖²`.
3. **(Aperture-to-zero depth exclusion):** If `R ≥ e⁶` and `HodgeIndexAtLevel zetaZeroConfig R`
   holds (in particular if `ZetaWindowPositive R` or `R < zetaContactAperture`), then every zero
   `ρ ∈ zetaZeroConfig.carrier` with `2 ≤ |Im ρ| ≤ zetaClusterHorizonHeight A₁ R` has depth
   `|Re ρ − ½| < 1/R`. -/
theorem zeta_visibility_and_height_reduction_tradeoff :
    ∃ A₀ A₁ : ℝ, 1 ≤ A₀ ∧ 1 ≤ A₁ ∧ ∀ R : ℝ, 0 < R →
      Real.log (zetaHorizonHeight A₀ R) ≤ 7000 * Real.exp R + Real.log A₀ + 160 ∧
      (∀ δ D T : ℝ, 0 ≤ δ → δ ≤ 1 / 2 → zetaHorizonHeight A₀ R ≤ T →
        (∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ T → |ρ.re - 1 / 2| ≤ δ) →
        OffLineDensityBoundBelow zetaZeroConfig T D →
        ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-R) R → paperFT f (I / 2) = 0 →
          paperFT f (-(I / 2)) = 0 →
          -((7000 * (2 * R + 3) * D * Real.exp (2 * δ * (R + 2)) + 2) * ∫ u, ‖f u‖ ^ 2) ≤
            (zetaZeroConfig.W f f).re) ∧
      (Real.exp 6 ≤ R → HodgeIndexAtLevel zetaZeroConfig R →
        ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| → |ρ.im| ≤ zetaClusterHorizonHeight A₁ R →
          |ρ.re - 1 / 2| < 1 / R) := by
  obtain ⟨A₀, hA₀, hred⟩ := zeta_re_W_ge_of_depth_up_to_height
  obtain ⟨A₁, hA₁, hexcl⟩ := zeta_abs_re_sub_half_lt_of_hodgeIndex
  refine ⟨A₀, A₁, hA₀, hA₁, fun R hR => ⟨log_zetaHorizonHeight_le hA₀ hR.le,
    fun δ D T hδ0 hδ2 hHT hδ hD => hred R δ D T hR hδ0 hδ2 hHT hδ hD,
    fun hR6 hHodge => hexcl R hR6 hHodge⟩⟩

end GaloisForLFunctions.SquareRootThreshold
