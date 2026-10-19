import GaloisForLFunctions.«arithmetic-positivity-theory».InghamHuxleyHeightBoxZeroMajorant
import GaloisForLFunctions.RHTower.SelbergNearLineCriticalGateDensity
import GaloisForLFunctions.RHTower.ZetaZeroDensityHypothesisFiveSixths
import GaloisForLFunctions.RHTower.ZetaZeroDensityTwelveFifths

/-!
# Selberg Exponential Near-Line Density and Uniform Four-Regime Layer-Cake Synthesis

This module connects `ArithmeticPositivityTheory` (`InghamHuxleyHeightBoxZeroMajorant.lean`) to two
further unconditional zero-densitypillars in `RHTower/`:

1. **Selberg's Exponential Near-Line Zero-Density Bounds at the Logarithmic Scale
   (`exists_selberg_criticalGate_nearLine_multiplicity_sum_le`,
   `exists_selberg_exponential_nearLine_multiplicity_sum_le`):**
   For fixed $\sigma > 1/2$, polynomial zero-density bounds carry a polylogarithmic prefactor
   $(1 + \log T)^B$ that dominates when $\sigma - 1/2 = O(1 / \log T)$.
   Connecting `SelbergNearLineCriticalGateDensity.exists_selberg_criticalGate_nearLine_zeroDensity`
   (two-length Barban–Vehov mollifier with critical-line short-window gate and twisted first moment)
   and `SelbergExponentialNearLineDensity.exists_selberg_exponential_nearLine_zeroDensity` to
   `ArithmeticPositivityTheory`, we divide out the positive Littlewood weight $2\pi (a / \log S)$
   to obtain unconditional upper bounds on the literal multiplicity-weighted zero count in the
   near-line strip $\operatorname{Re} \rho \ge 1/2 + \frac{51}{50}\frac{a}{\log S}$ with exponential
   decay $e^{-22 a / 25}$ in $a$.

2. **Uniform Hybrid Huxley + Density-Hypothesis Bound Across $[1/2, 1]$
   (`uniformHuxleyDHExponent`, `exists_zeroHeightBox_ncard_le_huxley_densityHypothesis_uniform`):**
   Whereas `InghamHuxleyHeightBoxZeroMajorant.exists_slab_zeroHeightBox_ncard_le_ingham_huxley` was
   pointwise in $\sigma \in (1/2, 1]$ (with $D, B, T_0$ depending on $\sigma$ and excluding $\sigma = 1/2$),
   combining `ZetaZeroDensityTwelveFifths.exists_zeroHeightBox_ncard_le_twelve_fifths` (uniform on
   $[1/2, 1]$) with `ZetaZeroDensityHypothesisFiveSixths.exists_zeroHeightBox_ncard_le_density_hypothesis`
   (uniform Density Hypothesis exponent $(2 + \varepsilon)(1 - \sigma)$ on $[5/6, 1]$) produces a
   single threshold $T_0(\varepsilon)$ and constant $D(\varepsilon)$ valid **uniformly** for all
   $\sigma \in [1/2, 1]$, including the critical-line slab $\sigma_0 = 1/2$.

3. **Simultaneous Unconditional Layer-Cake Discharge Across All $M$ Slabs
   (`exists_sum_rpow_re_le_huxley_densityHypothesis_routeT`):**
   Substitutes the uniform hybrid Huxley + Density-Hypothesis bound simultaneously into every term
   $0 \le m < M$ of the Route-T truncated layer-cake sum
   `exists_sum_rpow_re_le_zeroHeightBox_routeT_filter`, discharging all unestimated
   `zeroHeightBox (slabAbscissa M m) T` cardinalities with a threshold $T_0$ independent of the
   slab resolution $M$.
-/

open Complex MeasureTheory Set Filter Finset
open scoped BigOperators Topology
open _root_.RHTower _root_.RHTower.Sieve

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-! ## §1. Selberg's Exponential Near-Line Zero-Count Bounds -/

/-- **Unconditional Near-Line Zero-Multiplicity Count at Rate $22/25$
(`exists_selberg_criticalGate_nearLine_multiplicity_sum_le`):**
Dividing out the Littlewood weight $2\pi (a / \log S) > 0$ from
`RHTower.exists_selberg_criticalGate_nearLine_zeroDensity` (`SelbergNearLineCriticalGateDensity.lean:1114`)
bounds the multiplicity-weighted zero count in the near-line strip
$\operatorname{Re} \rho \ge 1/2 + \frac{51}{50}\frac{a}{\log S}$ by
$\frac{\log S}{2\pi a}\big((T_2 - T_1) A e^{-22a/25} + K \log S\big)$ for all $1 \le a \le \frac{\log S}{100}$. -/
theorem exists_selberg_criticalGate_nearLine_multiplicity_sum_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ S : ℝ in atTop,
      ∃ T₁ ∈ Ioo (2 * S / 3) (2 * S / 3 + 1), ∃ T₂ ∈ Ioo (4 * S / 3 - 1) (4 * S / 3),
        ∀ a : ℝ, 1 ≤ a → a ≤ Real.log S / 100 →
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          ∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / Real.log S) ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ) ≤
            (Real.log S / (2 * Real.pi * a)) *
              ((T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * Real.log S) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_selberg_criticalGate_nearLine_zeroDensity
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hev] with S ⟨T₁, hT₁, T₂, hT₂, hbound⟩
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha1 haL Z hZ => ?_⟩
  have hlogS : 100 ≤ Real.log S := by linarith
  have hlogS_pos : 0 < Real.log S := by linarith
  have ha_pos : 0 < a := by linarith
  have hpi_pos : 0 < 2 * Real.pi := by positivity
  have hfac_pos : 0 ≤ Real.log S / (2 * Real.pi * a) := by positivity
  have hmain := mul_le_mul_of_nonneg_left (hbound a ha1 haL Z hZ) hfac_pos
  have hlhs :
      (Real.log S / (2 * Real.pi * a)) *
        (2 * Real.pi * ((a / Real.log S) *
          ∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / Real.log S) ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ))) =
      ∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / Real.log S) ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have ha_ne : a ≠ 0 := ha_pos.ne'
    have hlog_ne : Real.log S ≠ 0 := hlogS_pos.ne'
    field_simp
  rwa [hlhs] at hmain

/-- **Unconditional Near-Line Zero-Multiplicity Count at the Critical Scale
(`exists_selberg_exponential_nearLine_multiplicity_sum_le`):**
Dividing out the Littlewood weight $2\pi (a / \log U) > 0$ from
`RHTower.exists_selberg_exponential_nearLine_zeroDensity` (`SelbergExponentialNearLineDensity.lean:656`)
bounds the multiplicity-weighted zero count in the near-line strip
$\operatorname{Re} \rho \ge 1/2 + 2a / \log U$ for all $1 \le a \le (\log U - 2)/2$. -/
theorem exists_selberg_exponential_nearLine_multiplicity_sum_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U : ℝ in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ a : ℝ, 1 ≤ a → 2 * a + 2 ≤ Real.log U →
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ) ≤
            (Real.log U / (2 * Real.pi * a)) *
              ((T₂ - T₁) * (A * Real.exp (-(a / 1200))) + K * Real.log U) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_selberg_exponential_nearLine_zeroDensity
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hev] with U ⟨T₁, hT₁, T₂, hT₂, hbound⟩
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha1 haL Z hZ => ?_⟩
  have hlogU_pos : 0 < Real.log U := by linarith
  have ha_pos : 0 < a := by linarith
  have hfac_pos : 0 ≤ Real.log U / (2 * Real.pi * a) := by positivity
  have hmain := mul_le_mul_of_nonneg_left (hbound a ha1 haL Z hZ) hfac_pos
  have hlhs :
      (Real.log U / (2 * Real.pi * a)) *
        (2 * Real.pi * ((a / Real.log U) *
          ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ))) =
      ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have ha_ne : a ≠ 0 := ha_pos.ne'
    have hlog_ne : Real.log U ≠ 0 := hlogU_pos.ne'
    field_simp
  rwa [hlhs] at hmain

/-! ## §2. Uniform Hybrid Huxley + Density-Hypothesis Bound Across `[1/2, 1]` -/

/-- Hybrid uniform height exponent combining Huxley's $(12/5 + \varepsilon)(1 - \sigma)$ on
$[1/2, 5/6)$ with the Density Hypothesis $(2 + \varepsilon)(1 - \sigma)$ on $[5/6, 1]$. -/
def uniformHuxleyDHExponent (ε σ : ℝ) : ℝ :=
  if σ < 5 / 6 then (12 / 5 + ε) * (1 - σ) else (2 + ε) * (1 - σ)

/-- On $[5/6, 1]$, `uniformHuxleyDHExponent ε σ` equals the Density Hypothesis exponent
$(2 + \varepsilon)(1 - \sigma)$ and is bounded above by Huxley's exponent $(12/5 + \varepsilon)(1 - \sigma)$. -/
theorem uniformHuxleyDHExponent_le_twelve_fifths {ε σ : ℝ} (hσ1 : σ ≤ 1) :
    uniformHuxleyDHExponent ε σ ≤ (12 / 5 + ε) * (1 - σ) := by
  unfold uniformHuxleyDHExponent
  split_ifs with h
  · exact le_rfl
  · nlinarith

/-- On $[5/6, 1]$, `uniformHuxleyDHExponent ε σ = (2 + ε) * (1 - σ)`. -/
theorem uniformHuxleyDHExponent_of_ge_five_sixths {ε σ : ℝ} (hσ : 5 / 6 ≤ σ) :
    uniformHuxleyDHExponent ε σ = (2 + ε) * (1 - σ) := by
  unfold uniformHuxleyDHExponent
  rw [if_neg (not_lt.mpr hσ)]

/-- **Uniform Hybrid Huxley + Density-Hypothesis Height-Box Bound
(`exists_zeroHeightBox_ncard_le_huxley_densityHypothesis_uniform`):**
Combines `exists_zeroHeightBox_ncard_le_twelve_fifths` (`ZetaZeroDensityTwelveFifths.lean:175`) and
`exists_zeroHeightBox_ncard_le_density_hypothesis` (`ZetaZeroDensityHypothesisFiveSixths.lean:154`)
into a single bound valid **uniformly** for all $T \ge T_0$ and all $\sigma \in [1/2, 1]$
(including $\sigma = 1/2$). -/
theorem exists_zeroHeightBox_ncard_le_huxley_densityHypothesis_uniform {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
        ((zeroHeightBox σ T).ncard : ℝ) ≤
          D * (1 + Real.log T) ^ B * T ^ uniformHuxleyDHExponent ε σ := by
  obtain ⟨D₁, hD₁, T₁, hT₁, hHux⟩ := exists_zeroHeightBox_ncard_le_twelve_fifths hε hε1
  obtain ⟨D₂, hD₂, T₂, hT₂, hDH⟩ := exists_zeroHeightBox_ncard_le_density_hypothesis hε hε1
  set B₁ : ℕ := expDetCountLogExponent + 4
  set B₂ : ℕ := dhLogExponent ε + 4
  refine ⟨D₁ + D₂, by positivity, max B₁ B₂, max T₁ T₂, le_trans hT₁ (le_max_left _ _),
    fun T hT σ hσ12 hσ1 => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have hTT₂ : T₂ ≤ T := (le_max_right _ _).trans hT
  have hT_one : 1 ≤ T := hT₁.trans hTT₁
  have hlog1 : 1 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT_one]
  have hTpow_nonneg : 0 ≤ T ^ uniformHuxleyDHExponent ε σ :=
    Real.rpow_nonneg (by linarith) _
  have hlogB_nonneg : 0 ≤ (1 + Real.log T) ^ max B₁ B₂ := by positivity
  unfold uniformHuxleyDHExponent
  split_ifs with hσ56
  · have h1 := hHux T hTT₁ σ hσ12 hσ1
    have hpow : (1 + Real.log T) ^ B₁ ≤ (1 + Real.log T) ^ max B₁ B₂ :=
      pow_le_pow_right₀ hlog1 (le_max_left _ _)
    calc ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D₁ * (1 + Real.log T) ^ B₁ * T ^ ((12 / 5 + ε) * (1 - σ)) := h1
      _ ≤ D₁ * (1 + Real.log T) ^ max B₁ B₂ * T ^ ((12 / 5 + ε) * (1 - σ)) := by gcongr
      _ ≤ (D₁ + D₂) * (1 + Real.log T) ^ max B₁ B₂ * T ^ ((12 / 5 + ε) * (1 - σ)) := by
          gcongr; linarith
  · have hσ_ge : 5 / 6 ≤ σ := not_lt.mp hσ56
    have h2 := hDH T hTT₂ σ hσ_ge hσ1
    have hpow : (1 + Real.log T) ^ B₂ ≤ (1 + Real.log T) ^ max B₁ B₂ :=
      pow_le_pow_right₀ hlog1 (le_max_right _ _)
    calc ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D₂ * (1 + Real.log T) ^ B₂ * T ^ ((2 + ε) * (1 - σ)) := h2
      _ ≤ D₂ * (1 + Real.log T) ^ max B₁ B₂ * T ^ ((2 + ε) * (1 - σ)) := by gcongr
      _ ≤ (D₁ + D₂) * (1 + Real.log T) ^ max B₁ B₂ * T ^ ((2 + ε) * (1 - σ)) := by
          gcongr; linarith

/-! ## §3. Simultaneous Unconditional Layer-Cake Discharge Across All `M` Slabs -/

/-- For every `0 < M` and `m ≤ M`, `slabAbscissa M m = 1/2 + m / (2M)` lies in `[1/2, 1]`
(including `m = 0`, where `slabAbscissa M 0 = 1/2`). -/
theorem slabAbscissa_mem_Icc {M m : ℕ} (hM : 0 < M) (hmM : m ≤ M) :
    1 / 2 ≤ slabAbscissa M m ∧ slabAbscissa M m ≤ 1 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmle : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  unfold slabAbscissa
  constructor
  · have : (0 : ℝ) ≤ (m : ℝ) / (2 * (M : ℝ)) := div_nonneg hm0 (by positivity)
    linarith
  · have : (m : ℝ) / (2 * (M : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith

/-- **Simultaneous Unconditional Layer-Cake Sum Discharge
(`exists_sum_rpow_re_le_huxley_densityHypothesis_routeT`):**
Discharges `((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ)` simultaneously across all slabs
$0 \le m < M$ inside `exists_sum_rpow_re_le_zeroHeightBox_routeT_filter`, with a threshold $T_0(\varepsilon)$
independent of the slab count $M$. Each slab receives:
- Huxley's exponent $(12/5 + \varepsilon)(1 - \sigma_m)$ for $1/2 \le \sigma_m < 5/6$,
- the Density Hypothesis exponent $(2 + \varepsilon)(1 - \sigma_m)$ for $5/6 \le \sigma_m \le 1 - \text{routeTWidth}$,
- exact Route-T zero-free annihilation for $\sigma_m > 1 - \text{routeTWidth}$. -/
theorem exists_sum_rpow_re_le_huxley_densityHypothesis_routeT {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ {T : ℝ}, T₀ ≤ T → ∀ {x : ℝ}, 1 ≤ x → ∀ {M : ℕ}, 0 < M →
      ∀ (G : Finset XiZeroCopy),
        (∀ q ∈ G, T ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * T) →
        ∑ q ∈ G, x ^ ((q.1 : ℂ).re - 1) ≤
          4 * D * (1 + Real.log T) ^ B *
            ∑ m ∈ (Finset.range M).filter
                (fun m => slabAbscissa M m ≤ 1 - routeTWidthPolylogLower A (4 * T / 3)),
              x ^ (slabAbscissa M (m + 1) - 1) *
                T ^ uniformHuxleyDHExponent ε (slabAbscissa M m) := by
  obtain ⟨A, T₁, hT₁, hfilter⟩ := exists_sum_rpow_re_le_zeroHeightBox_routeT_filter
  obtain ⟨D, hD, B, T₂, hT₂, hunif⟩ :=
    exists_zeroHeightBox_ncard_le_huxley_densityHypothesis_uniform hε hε1
  refine ⟨A, D, hD, B, max T₁ T₂, le_trans hT₁ (le_max_left _ _),
    fun {T} hT {x} hx {M} hM G hG => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have hTT₂ : T₂ ≤ T := (le_max_right _ _).trans hT
  have hT_one : 1 ≤ T := hT₁.trans hTT₁
  have hx_pos : 0 < x := by linarith
  refine (hfilter hTT₁ hx hM G hG).trans ?_
  rw [show 4 * D * (1 + Real.log T) ^ B *
        ∑ m ∈ (Finset.range M).filter
            (fun m => slabAbscissa M m ≤ 1 - routeTWidthPolylogLower A (4 * T / 3)),
          x ^ (slabAbscissa M (m + 1) - 1) *
            T ^ uniformHuxleyDHExponent ε (slabAbscissa M m) =
      4 * ∑ m ∈ (Finset.range M).filter
            (fun m => slabAbscissa M m ≤ 1 - routeTWidthPolylogLower A (4 * T / 3)),
          x ^ (slabAbscissa M (m + 1) - 1) *
            (D * (1 + Real.log T) ^ B * T ^ uniformHuxleyDHExponent ε (slabAbscissa M m)) by
      rw [mul_assoc, mul_assoc, Finset.mul_sum, Finset.mul_sum]
      refine congrArg (4 * ·) (Finset.sum_congr rfl fun m _ => by ring)]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm => ?_) (by norm_num)
  have hm_lt : m < M := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  obtain ⟨hσ12, hσ1⟩ := slabAbscissa_mem_Icc hM (Nat.le_of_lt hm_lt)
  exact mul_le_mul_of_nonneg_left (hunif T hTT₂ (slabAbscissa M m) hσ12 hσ1)
    (Real.rpow_nonneg hx_pos.le _)

end

end GaloisForLFunctions.ArithmeticPositivityTheory
