import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyHorizonLaw

/-!
# Loud records of the one-parameter family are visible at an explicit lag

`one_param_record_visible` sees the Legendre record `z*` of `P_v` at lag `V` from three numbers:
its loudness `|D(z*)| ≥ a`, its height `|Im z*| ≤ Γ` and its depth `Re z* ≥ σ`. Here the remaining
parameters are chosen from `a` and `σ` alone. No coefficient reaches `a` above
`Γ(a) = (2880 · 80(e^{w/2}B_w)²/a)^{1/3}` (`recordHeightOf`). The relative neighbour bound is
`D(a) = (125/2) log(180(Γ(a) + 1))` (`recordMass`), the coherence `c(a) = 1/(10(P + 1)D(a) + 1)`,
the noise constant `M(a) = recordNoise`, and the order is `k(a) = explicitOrder(M(a), c(a), P(a))`
with `P(a) = ⌈80 log(180Γ(a))⌉`.

**Theorem** (`one_param_record_visible_at_explicit_lag`). If the record at lag
`V ≥ V(a, σ) = (4/σ)(13πk(a) + 4) + w + 8we^{w/2}J_w/H₀(a)` (`recordLag`) has `|D(z*)| ≥ a`,
`|Im z*| ≤ Γ(a)` and `Re z* ≥ σ`, then `P_v < 0` for some `v ∈ [0, V]`.

Every near-top statement reduces to this one through a record lemma that produces `(a, σ)`.
`P(a) ≍ log Γ(a) ≍ log(1/a)`. The coherence `c(a)` does not depend on the loudness `a` (the core
mass is measured relative to the record), so `log G ≍ log P` and
`log₂ Y ≍ P² log P + log(1/a)`. Hence `V(a, σ) ≍_w (log(1/a))² log log(1/a)/σ`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The height `Γ(a) = (2880 · 80(e^{w/2}B_w)²/a)^{1/3}` above which no coefficient of the
unmodulated family reaches `a`. -/
def recordHeightOf (w a : ℝ) : ℝ :=
  (2880 * (80 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / a)) ^ ((1 : ℝ) / 3)

/-- The relative neighbour bound `D(a) = (125/2) log(180(Γ(a) + 1))`. -/
def recordMass (w a : ℝ) : ℝ := 125 / 2 * Real.log (180 * (recordHeightOf w a + 1))

/-- The noise constant `M(a) = 4m₀/((e − 1)a) + 6144 log(180(Γ(a) + 6))`. -/
def recordNoise (w a : ℝ) : ℝ :=
  4 * (32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 * (xiLineTwoLogDerivConstant + Real.log 4)) /
      ((Real.exp 1 - 1) * a) + 6144 * Real.log (180 * (recordHeightOf w a + 6))

/-- The coherence product `c = 1/(10(P + 1)D(a) + 1)`. -/
def recordCoherence (w a : ℝ) : ℝ :=
  explicitCoherence 1 (recordMass w a) (explicitCount (recordHeightOf w a))

/-- The Fejér order for a record of loudness `a`. -/
def recordOrder (w a : ℝ) : ℕ :=
  explicitOrder (recordNoise w a) (recordCoherence w a) (explicitCount (recordHeightOf w a))

/-- The phase-coherence scale `H₀(a) = (a/(80 log(180Γ(a))))^{1/2}`. -/
def recordScale (w a : ℝ) : ℝ :=
  Real.sqrt (a / (80 * Real.log (180 * recordHeightOf w a)))

/-- The lag `V(a, σ) = (4/σ)(13πk(a) + 4) + w + 8w e^{w/2}J_w/H₀(a)` for a record of loudness `a`
and depth `≥ σ`. -/
def recordLag (w a σ : ℝ) : ℝ :=
  4 / σ * (13 * π * recordOrder w a + 4) + w + 8 * w * Real.exp (w / 2) * bumpMass w / recordScale w a

theorem recordCollapseBound_one (w a : ℝ) (k p : ℕ) :
    recordCollapseBound w a (recordHeightOf w a) 1 k p = (8 / 3) ^ p * (4 / 3) ^ k * 2 *
      (4 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) * recordNoise w a := by
  rw [recordCollapseBound, recordNoise]; ring

/-- **A loud record is visible at an explicit lag.** Let `z*` be the Legendre record of the
unmodulated family at lag `V`, with `|D(z*)| ≥ a > 0`, `|Im z*| ≤ Γ(a)` and `Re z* ≥ σ`,
`0 < σ ≤ ½`. If `V ≥ V(a, σ)` (`recordLag`), then `P_v < 0` for some `v ∈ [0, V]`. -/
theorem one_param_record_visible_at_explicit_lag {w : ℝ} (hw : 0 < w) {V : ℝ} {z₁ : ℂ}
    (hz₁ : evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 2) (hre₁ : σ ≤ z₁.re) {a : ℝ} (ha : 0 < a)
    (hD₁ : a ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖) (hup : |z₁.im| ≤ recordHeightOf w a)
    (hrec : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * Real.exp (z₁.re * V))
    (hV : recordLag w a σ ≤ V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  have hΓ4 : 4 ≤ recordHeightOf w a := (four_le_abs_im_of_evenCoeff_zeta hz₁).trans hup
  have hDm0 : 0 ≤ recordMass w a := by
    unfold recordMass
    have : 0 ≤ Real.log (180 * (recordHeightOf w a + 1)) := Real.log_nonneg (by linarith only [hΓ4])
    positivity
  have hM : 0 < recordNoise w a := by
    unfold recordNoise
    have hC := xiLineTwoLogDerivConstant_nonneg
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
    have hL : 0 < Real.log (180 * (recordHeightOf w a + 6)) := Real.log_pos (by linarith only [hΓ4])
    positivity
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = explicitCount (recordHeightOf w a) := ⟨_, rfl⟩
  obtain ⟨hc0, hc1, hca, hG1, hq0, hq1, hPk, hk1, hY⟩ := explicit_parameter_facts one_pos hDm0 hM P
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = explicitCoherence 1 (recordMass w a) P := ⟨_, rfl⟩
  rw [← hc] at hc0 hc1 hca hG1 hq0 hq1 hPk hk1 hY
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = explicitOrder (recordNoise w a) c P := ⟨_, rfl⟩
  rw [← hk] at hPk hk1 hY
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = explicitGap c P := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = explicitRatio c P := ⟨_, rfl⟩
  have hqe : q = c / (2 * (P + 1) * G ^ P) := by rw [hq, explicitRatio, ← hG]
  rw [← hG] at hG1
  rw [← hq] at hq0 hq1 hY
  have hkk : recordOrder w a = k := by rw [hk, hc, hP]; rfl
  obtain ⟨H₀, hH₀⟩ : ∃ H₀ : ℝ, H₀ = recordScale w a := ⟨_, rfl⟩
  rw [recordLag, hkk, ← hH₀] at hV
  have hℓ₁ : 0 < Real.log (180 * recordHeightOf w a) := Real.log_pos (by linarith)
  have hH₀0 : 0 < H₀ := by rw [hH₀, recordScale]; exact Real.sqrt_pos.mpr (by positivity)
  have hH₀sq : H₀ ^ 2 = a / (80 * Real.log (180 * recordHeightOf w a)) := by
    rw [hH₀, recordScale]; exact Real.sq_sqrt (by positivity)
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hJ'0 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w := mul_nonneg (by positivity) hJ0
  have hπk : 0 ≤ 13 * π * k := by positivity
  have hT2 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / H₀ := div_nonneg hJ'0 hH₀0.le
  have h8 : 0 ≤ 4 / σ * (13 * π * k + 4) := by positivity
  have hVw : w ≤ V := by linarith only [hV, h8, hT2]
  have hV0 : 0 < V := lt_of_lt_of_le hw hVw
  have hVJ : 8 * w * Real.exp (w / 2) * bumpMass w / H₀ ≤ V := by linarith only [hV, h8, hw]
  have hσV : 4 * (13 * π * k + 4) ≤ σ * V := by
    have h1 : 4 / σ * (13 * π * k + 4) ≤ V := by linarith only [hV, hT2, hw]
    have h2 := mul_le_mul_of_nonneg_left h1 hσ.le
    have e : σ * (4 / σ * (13 * π * k + 4)) = 4 * (13 * π * k + 4) := by field_simp
    linarith only [h2, e]
  have hσV2 : σ * V ≤ V / 2 := by nlinarith
  have hkP : ((k + P : ℕ) : ℝ) ≤ 2 * k := by
    push_cast; have : (P : ℝ) ≤ k := by exact_mod_cast hPk
    linarith
  have hπkP := mul_le_mul_of_nonneg_left hkP Real.pi_pos.le
  -- the lag conditions
  have hPceil : 80 * Real.log (180 * recordHeightOf w a) ≤ P := by
    rw [hP, explicitCount]; exact Nat.le_ceil _
  have hκV : 2 * 1 / V ≤ σ / 8 := by
    rw [div_le_div_iff₀ hV0 (by norm_num)]; linarith only [hσV, hπk]
  have hVk : π * (k + P : ℕ) ≤ V := by linarith only [hπkP, hσV, hσV2, hπk]
  have hVr : 4 * π * (k + P : ℕ) ≤ V * (σ / 4) := by linarith only [hπkP, hσV, hπk]
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
  have hρr : c / V ≤ σ / 8 := by
    rw [div_le_div_iff₀ hV0 (by norm_num)]; linarith only [hσV, hπk, hc1]
  have hDm : recordMass w a = 125 / 2 * Real.log (180 * (recordHeightOf w a + 1)) := rfl
  have hηm : ((1 + coreFactorPerturbation P 1 V (c / V) G) * (2 * (c / V * V)) +
      coreFactorPerturbation P 1 V (c / V) G) * ((P + 1) * (125 / 2 * Real.log (180 *
        (recordHeightOf w a + 1)))) ≤ 1 / 2 := by
    rw [div_mul_cancel₀ c hV0.ne', ← hDm, hG]
    have hτ := coreFactorPerturbation_le hc0 hc1 hV0 P
    have h1 : coreFactorPerturbation P 1 V (c / V) (explicitGap c P) * (2 * c) ≤ 1 * (2 * c) :=
      mul_le_mul_of_nonneg_right (hτ.trans hc1) (by positivity)
    have hτ' : (1 + coreFactorPerturbation P 1 V (c / V) (explicitGap c P)) * (2 * c) +
        coreFactorPerturbation P 1 V (c / V) (explicitGap c P) ≤ 5 * c := by
      linarith only [h1, hτ]
    have hm : 0 ≤ ((P : ℝ) + 1) * recordMass w a := by positivity
    have h2 := mul_le_mul_of_nonneg_right hτ' hm
    linarith only [h2, hca]
  have hmain : ∀ p : ℕ, p ≤ P → 2 * recordCollapseBound w a (recordHeightOf w a) 1 k p <
      (c / V * 1 / (2 * (P + 1) * G ^ P)) ^ p * V ^ (2 * k + p + 1) * (σ / 4) ^ (2 * k + 1) := by
    intro p hp
    have hG0 : 0 < G := lt_of_lt_of_le one_pos hG1
    have hD0 : (2 * ((P : ℝ) + 1) * G ^ P) ≠ 0 := by positivity
    have e : (c / V * 1 / (2 * (P + 1) * G ^ P)) ^ p * V ^ (2 * k + p + 1) * (σ / 4) ^ (2 * k + 1) =
        q ^ p * (V * (σ / 4)) ^ (2 * k + 1) := by
      have e0 : c / V * 1 / (2 * (P + 1) * G ^ P) = c / (2 * (P + 1) * G ^ P) / V := by ring
      have hVp : V ^ p ≠ 0 := pow_ne_zero _ hV0.ne'
      rw [hqe, e0, div_pow, show 2 * k + p + 1 = (2 * k + 1) + p by ring, pow_add, mul_pow]
      field_simp
    rw [e, recordCollapseBound_one]
    have hX : 13 * π * k ≤ V * (σ / 4) := by linarith only [hσV]
    exact collapse_form_lt hp hPk hk1 hq0 hq1 hX hM hY
  exact one_param_record_visible hw hV0 hz₁ hσ hσ1 hre₁ ha hD₁ hup hrec hPceil hk1 le_rfl hκV hVk hVr
    hH₀sq.le hρ hG1 hρV hρw hρL hρr hηm hmain

end GaloisForLFunctions.SquareRootThreshold
