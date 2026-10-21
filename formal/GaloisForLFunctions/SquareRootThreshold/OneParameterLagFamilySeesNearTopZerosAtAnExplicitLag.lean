import GaloisForLFunctions.SquareRootThreshold.ZetaNearTopZerosAreVisibleAtAPolylogarithmicLag
import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilySeesNearTopZeros

/-!
# The one-parameter lag family sees near-top zeros at an explicit lag

The parameters of `one_param_near_top_visible` chosen explicitly, through the generic
`explicitCount`, `explicitCoherence`, `explicitGap`, `explicitRatio`, `explicitOrder` with record
bound `a = 2η²/e`, neighbour bound `D₀(η) = 80 log(180(Γ₀ + 1))(e^{w/2}B_w)²` (`oneParamMass`) and
noise constant `M₀(η)` (`oneParamNoise`); `Γ₀ = Γ₀(η) = oneParamRecordHeight w η ≥ 1`.

**Theorem** (`one_param_near_top_visible_at_explicit_lag`). Let `½ + z₀` be a zero of `ζ` right of
the line, `δ₀ = Re z₀`, `0 < η ≤ |h_w(γ₀ − iδ₀)|`, and let `½ + z₀` be `1/V`-near the top for some
`V ≥ V₀(w, η, δ₀)` (`oneParamLag`). Then `P_v = Re W(κ_w(t + v/2) − κ_w(t − v/2)) < 0` for some
`v ∈ [0, V]`. No height condition and no attainment of the top are needed, and
`V₀ ≍_w (log Γ₀)² log log Γ₀/δ₀`, `Γ₀ ≍_w η^{−2/3}`.

**Depth gap** (`one_param_depth_gap_of_lag_positivity`). If `P_v ≥ 0` on `[0, V]`, every zero
`½ + z₀` right of the line with `V₀(w, |h_w(−iz₀)|, Re z₀) ≤ V` has a zero more than `1/V` to its
right. For a width with `h_w(γ − iδ) ≠ 0` at the zeros, positivity of the single family `P_v` on
`[0, V]` thus forces every zero with `V₀ ≤ V` to lie at least `1/V` below the top. The height
enters only through `η = |h_w(γ − iδ)|`, which decays with `γ`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The coefficient bound `D₀(η) = 80 log(180(Γ₀ + 1))(e^{w/2}B_w)²` near the record. -/
def oneParamMass (w η : ℝ) : ℝ :=
  80 * Real.log (180 * (oneParamRecordHeight w η + 1)) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2

/-- The noise constant `M₀(η) = 4m₀/((e − 1)(2η²/e)) + 6144 log(180(Γ₀ + 6))`,
`m₀ = 32(e^{w/2}B_w)²(C_ξ + log 4)`, of `oneParamCollapseBound`. -/
def oneParamNoise (w η : ℝ) : ℝ :=
  4 * (32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 * (xiLineTwoLogDerivConstant + Real.log 4)) /
      ((Real.exp 1 - 1) * (2 * η ^ 2 / Real.exp 1)) +
    6144 * Real.log (180 * (oneParamRecordHeight w η + 6))

/-- The coherence product of the unmodulated family, with record bound `a = 2η²/e`. -/
def oneParamCoherence (w η : ℝ) : ℝ :=
  explicitCoherence (2 * η ^ 2 / Real.exp 1) (oneParamMass w η)
    (explicitCount (oneParamRecordHeight w η))

/-- The Fejér order of the unmodulated family. -/
def oneParamOrder (w η : ℝ) : ℕ :=
  explicitOrder (oneParamNoise w η) (oneParamCoherence w η) (explicitCount (oneParamRecordHeight w η))

/-- The phase-coherence scale `H₀ = ((2η²/e)/(80 log(180Γ₀)))^{1/2}`. -/
def oneParamScale (w η : ℝ) : ℝ :=
  Real.sqrt (2 * η ^ 2 / Real.exp 1 / (80 * Real.log (180 * oneParamRecordHeight w η)))

/-- The lag `V₀(w, η, δ₀) = (8/δ₀)(13πk + 4 + |log(80 log(180Γ₀)(e^{w/2}B_w)²/(2η²))|) + w +
8w e^{w/2} J_w/H₀`. -/
def oneParamLag (w η δ₀ : ℝ) : ℝ :=
  8 / δ₀ * (13 * π * oneParamOrder w η + 4 +
    |Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))|) +
    w + 8 * w * Real.exp (w / 2) * bumpMass w / oneParamScale w η

/-- At `κ₀ = 1` the collapse bound is `(8/3)^p(4/3)^k · 2 · (4 + 4π²(k + p)²)^{k+p} M₀(η)`. -/
theorem oneParamCollapseBound_one (w η : ℝ) (k p : ℕ) :
    oneParamCollapseBound w η 1 k p = (8 / 3) ^ p * (4 / 3) ^ k * 2 *
      (4 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) * oneParamNoise w η := by
  rw [oneParamCollapseBound, oneParamNoise]; ring

/-- `η ≤ |h_w(−iz₀)| ≤ e^{w/2}B_w` forces `Γ₀(η) ≥ 1`. -/
theorem one_le_oneParamRecordHeight {w η : ℝ} (hη : 0 < η)
    (hηB : η ≤ Real.exp (w / 2) * scaledBumpDecay w) : 1 ≤ oneParamRecordHeight w η := by
  unfold oneParamRecordHeight
  refine Real.one_le_rpow ?_ (by norm_num)
  have h1 : η ^ 2 ≤ (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := pow_le_pow_left₀ hη.le hηB 2
  have he : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : 1 ≤ 80 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2 / Real.exp 1) := by
    rw [le_div_iff₀ (by positivity), one_mul]
    have h3 : 2 * η ^ 2 / Real.exp 1 ≤ 2 * η ^ 2 := div_le_self (by positivity) he
    linarith [sq_nonneg η]
  linarith

/-- **The one-parameter family sees near-top zeros at an explicit lag.** Let `½ + z₀` be a zero of
`ζ` right of the line, `δ₀ = Re z₀`, with `η = |h_w(γ₀ − iδ₀)| > 0` (any `0 < η ≤ |h_w(−iz₀)|`),
let `V ≥ V₀(w, η, δ₀)` (`oneParamLag`) and let `½ + z₀` be `1/V`-near the top. Then
`P_v = Re W(κ_w(t + v/2) − κ_w(t − v/2)) < 0` for some lag `v ∈ [0, V]`.

`V₀(w, η, δ₀) ≍_w (log Γ₀)² log log Γ₀/δ₀` with `Γ₀ ≍_w η^{−2/3}`. -/
theorem one_param_near_top_visible_at_explicit_lag {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : oneParamLag w η z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  -- basic facts
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1 : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hB0 : 0 ≤ Real.exp (w / 2) * scaledBumpDecay w := by
    have := bumpDecayConstant_nonneg (scaledBump w); positivity
  have hηB : η ≤ Real.exp (w / 2) * scaledBumpDecay w := by
    have hx : |(-(I * z₀)).im| ≤ 1 / 2 := by
      have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
      have : |z₀.re| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
      simpa using this
    refine hηle.trans ((norm_paperFT_scaledBump_le hw hx).trans (div_le_self hB0 ?_))
    exact one_le_pow₀ (by linarith [abs_nonneg (-(I * z₀)).re])
  have hΓ1 := one_le_oneParamRecordHeight hη hηB
  have ha0 : 0 < 2 * η ^ 2 / Real.exp 1 := by positivity
  have hDm0 : 0 ≤ oneParamMass w η := by
    unfold oneParamMass
    have : 0 ≤ Real.log (180 * (oneParamRecordHeight w η + 1)) :=
      Real.log_nonneg (by linarith only [hΓ1])
    positivity
  have hM : 0 < oneParamNoise w η := by
    unfold oneParamNoise
    have hC := xiLineTwoLogDerivConstant_nonneg
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
    have hL : 0 < Real.log (180 * (oneParamRecordHeight w η + 6)) :=
      Real.log_pos (by linarith only [hΓ1])
    positivity
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = explicitCount (oneParamRecordHeight w η) := ⟨_, rfl⟩
  obtain ⟨hc0, hc1, hca, hG1, hq0, hq1, hPk, hk1, hY⟩ := explicit_parameter_facts ha0 hDm0 hM P
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = explicitCoherence (2 * η ^ 2 / Real.exp 1) (oneParamMass w η) P :=
    ⟨_, rfl⟩
  rw [← hc] at hc0 hc1 hca hG1 hq0 hq1 hPk hk1 hY
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = explicitOrder (oneParamNoise w η) c P := ⟨_, rfl⟩
  rw [← hk] at hPk hk1 hY
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = explicitGap c P := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = explicitRatio c P := ⟨_, rfl⟩
  have hqe : q = c / (2 * (P + 1) * G ^ P) := by rw [hq, explicitRatio, ← hG]
  rw [← hG] at hG1
  rw [← hq] at hq0 hq1 hY
  have hkk : oneParamOrder w η = k := by rw [hk, hc, hP]; rfl
  obtain ⟨H₀, hH₀⟩ : ∃ H₀ : ℝ, H₀ = oneParamScale w η := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2)) := ⟨_, rfl⟩
  rw [oneParamLag, hkk, ← hH₀, ← hℓ] at hV
  have hℓ₁ : 0 < Real.log (180 * oneParamRecordHeight w η) := Real.log_pos (by linarith)
  have hH₀0 : 0 < H₀ := by rw [hH₀, oneParamScale]; exact Real.sqrt_pos.mpr (by positivity)
  have hH₀sq : H₀ ^ 2 = 2 * η ^ 2 / Real.exp 1 / (80 * Real.log (180 * oneParamRecordHeight w η)) := by
    rw [hH₀, oneParamScale]; exact Real.sq_sqrt (by positivity)
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hJ'0 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w := mul_nonneg (by positivity) hJ0
  have hπk : 0 ≤ 13 * π * k := by positivity
  have hℓa := abs_nonneg ℓ
  have hT2 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / H₀ := div_nonneg hJ'0 hH₀0.le
  have h8 : 0 ≤ 8 / z₀.re * (13 * π * k + 4 + |ℓ|) := by positivity
  have hVw : w ≤ V := by linarith only [hV, h8, hT2]
  have hV0 : 0 < V := lt_of_lt_of_le hw hVw
  have hVJ : 8 * w * Real.exp (w / 2) * bumpMass w / H₀ ≤ V := by linarith only [hV, h8, hw]
  have hδV : 8 * (13 * π * k + 4 + |ℓ|) ≤ z₀.re * V := by
    have h1 : 8 / z₀.re * (13 * π * k + 4 + |ℓ|) ≤ V := by linarith only [hV, hT2, hw]
    have h2 := mul_le_mul_of_nonneg_left h1 hre₀.le
    have e : z₀.re * (8 / z₀.re * (13 * π * k + 4 + |ℓ|)) = 8 * (13 * π * k + 4 + |ℓ|) := by
      field_simp
    linarith only [h2, e]
  have hδV2 : z₀.re * V ≤ V / 2 := by nlinarith
  have hkP : ((k + P : ℕ) : ℝ) ≤ 2 * k := by
    push_cast; have : (P : ℝ) ≤ k := by exact_mod_cast hPk
    linarith
  have hπkP := mul_le_mul_of_nonneg_left hkP Real.pi_pos.le
  -- the lag conditions
  have hPceil : 80 * Real.log (180 * oneParamRecordHeight w η) ≤ P := by
    rw [hP, explicitCount]; exact Nat.le_ceil _
  have hV2 : 2 * ℓ ≤ z₀.re * V := by linarith only [hδV, le_abs_self ℓ, hπk, hℓa]
  have hκV : 2 * 1 / V ≤ z₀.re / 16 := by
    rw [div_le_div_iff₀ hV0 (by norm_num)]; linarith only [hδV, hπk, hℓa]
  have hVk : π * (k + P : ℕ) ≤ V := by linarith only [hπkP, hδV, hδV2, hℓa, hπk]
  have hVr : 4 * π * (k + P : ℕ) ≤ V * (z₀.re / 8) := by
    linarith only [hπkP, hδV, hℓa, hπk]
  -- the core conditions
  have hρ : 0 < c / V := div_pos hc0 hV0
  have hρV : c / V * V ≤ 1 := by rw [div_mul_cancel₀ c hV0.ne']; exact hc1
  have hρw : w * (c / V) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hV0]
    have := mul_le_mul_of_nonneg_left hc1 hw.le
    linarith only [this, hVw]
  have hρL : 8 * w * Real.exp (w / 2) * bumpMass w * (c / V) ≤ H₀ := by
    rw [mul_div_assoc', div_le_iff₀ hV0]
    have h1 : 8 * w * Real.exp (w / 2) * bumpMass w ≤ V * H₀ := by
      have := mul_le_mul_of_nonneg_right hVJ hH₀0.le
      rwa [div_mul_cancel₀ _ hH₀0.ne'] at this
    have h2 := mul_le_mul_of_nonneg_left hc1 hJ'0
    linarith only [h1, h2]
  have hρr : c / V ≤ z₀.re / 16 := by
    rw [div_le_div_iff₀ hV0 (by norm_num)]; linarith only [hδV, hπk, hℓa, hc1]
  have hDm : oneParamMass w η = 80 * Real.log (180 * (oneParamRecordHeight w η + 1)) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := rfl
  have hηm : ((1 + coreFactorPerturbation P 1 V (c / V) G) * (2 * (c / V * V)) +
      coreFactorPerturbation P 1 V (c / V) G) * ((P + 1) * (80 * Real.log (180 *
        (oneParamRecordHeight w η + 1)) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2)) ≤
      2 * η ^ 2 / Real.exp 1 / 2 := by
    rw [div_mul_cancel₀ c hV0.ne', ← hDm, hG]
    have hτ := coreFactorPerturbation_le hc0 hc1 hV0 P
    have h1 : coreFactorPerturbation P 1 V (c / V) (explicitGap c P) * (2 * c) ≤ 1 * (2 * c) :=
      mul_le_mul_of_nonneg_right (hτ.trans hc1) (by positivity)
    have hτ' : (1 + coreFactorPerturbation P 1 V (c / V) (explicitGap c P)) * (2 * c) +
        coreFactorPerturbation P 1 V (c / V) (explicitGap c P) ≤ 5 * c := by
      linarith only [h1, hτ]
    have hm : 0 ≤ ((P : ℝ) + 1) * oneParamMass w η := by positivity
    have h2 := mul_le_mul_of_nonneg_right hτ' hm
    linarith only [h2, hca]
  have hmain : ∀ p : ℕ, p ≤ P → 2 * oneParamCollapseBound w η 1 k p <
      (c / V * 1 / (2 * (P + 1) * G ^ P)) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1) := by
    intro p hp
    have hG0 : 0 < G := lt_of_lt_of_le one_pos hG1
    have hD0 : (2 * ((P : ℝ) + 1) * G ^ P) ≠ 0 := by positivity
    have e : (c / V * 1 / (2 * (P + 1) * G ^ P)) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1) =
        q ^ p * (V * (z₀.re / 8)) ^ (2 * k + 1) := by
      have e0 : c / V * 1 / (2 * (P + 1) * G ^ P) = c / (2 * (P + 1) * G ^ P) / V := by ring
      have hVp : V ^ p ≠ 0 := pow_ne_zero _ hV0.ne'
      rw [hqe, e0, div_pow, show 2 * k + p + 1 = (2 * k + 1) + p by ring, pow_add, mul_pow]
      field_simp
    rw [e, oneParamCollapseBound_one]
    have hX : 13 * π * k ≤ V * (z₀.re / 8) := by linarith only [hδV, hℓa]
    exact collapse_form_lt hp hPk hk1 hq0 hq1 hX hM hY
  exact one_param_near_top_visible hw hz₀ hre₀ hη hηle hV0 htop hPceil hk1 le_rfl
    (by rw [← hℓ]; exact hV2) hκV hVk hVr hH₀sq.le hρ hG1 hρV hρw hρL hρr hηm hmain

/-- **Depth gap for `P_v`.** If `P_v ≥ 0` for every lag `v ∈ [0, V]`, then every zero `½ + z₀` right
of the line with `V ≥ V₀(w, η, Re z₀)` for some `0 < η ≤ |h_w(−iz₀)|` has a zero more than `1/V`
to its right. -/
theorem one_param_depth_gap_of_lag_positivity {w : ℝ} (hw : 0 < w) {V : ℝ}
    (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    (hV : oneParamLag w η z₀.re ≤ V) :
    ∃ ρ ∈ zetaZeroConfig.carrier, z₀.re + 1 / V < ρ.re - 1 / 2 := by
  by_contra h
  push Not at h
  obtain ⟨v, hv, hneg⟩ := one_param_near_top_visible_at_explicit_lag hw hz₀ hre₀ hη hηle hV h
  exact absurd (hpos v hv) (not_le.mpr hneg)

end GaloisForLFunctions.SquareRootThreshold
