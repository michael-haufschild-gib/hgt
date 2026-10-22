import GaloisForLFunctions.RHTower.EisensteinLineSourceL2
import GaloisForLFunctions.RHTower.EisensteinLineSourceRatio
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSkewPlateauCovarianceKernel
import GaloisForLFunctions.RHTower.HighBlockAsymptotics

/-!
# The on-line clock sign law with the Eisenstein source

For the source `F_t ∈ L²(𝒟)` given by `g = ‖E*(·, 1/2+it)‖² − 1_{y > H} ‖c(y)‖²` (the
principal-subtraction Eisenstein source on the line), the assembled on-line clock bound

`t¹¹/2176 · |∫_𝒟 F_t|²/vol(𝒟) − t⁹ · ‖F_t − P₀F_t‖² ≤ Re ⟪(Im K̂)(C) F_t, F_t⟫`

has a positive left side for all large `t`: the mean satisfies `∫_𝒟 F_t ≥ (5/2) ‖Λ(1+2it)‖²`,
the mean square satisfies `‖F_t‖² ≤ ‖Λ‖⁴ (128 H + B t^{5/3} (log t)^{50})`, and
`t^{5/3} (log t)^{50} = o(t²)`.  Hence

`0 < Re ⟪(Im K̂)(C) F_t, F_t⟫`  for all large `t`.

The statement is unconditional; its inputs are the Bessel power saving on the imaginary axis,
the Parseval identity of the cusp tail, the constant-term mean square and the lower bound
`‖ζ(1+2it)‖ ≥ c / log(2t)^{11}`.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassCellCurvature
  GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget
open RHTower.D4BMScalarStream
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-! ## Growth versus `t²` -/

theorem growth_eq_sq_mul {t : ℝ} (ht : 0 < t) :
    growth t = t ^ 2 * (t ^ (-(1 / 3 : ℝ)) * Real.log t ^ 50) := by
  unfold growth
  have h : t ^ (5 / 3 : ℝ) = t ^ 2 * t ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht]; norm_num
  rw [h]; ring

theorem one_le_growth {t : ℝ} (ht : 3 ≤ t) : 1 ≤ growth t := by
  unfold growth
  exact one_le_mul_of_one_le_of_one_le (one_le_growthPow (by linarith))
    (one_le_pow₀ (one_le_log_of_three_le ht))

/-- `K · growth(t) < 25 t² / 17408` for all large `t`. -/
theorem eventually_mul_growth_lt (K : ℝ) :
    ∀ᶠ t in atTop, K * growth t < 25 * t ^ 2 / 17408 := by
  have h := eventually_const_mul_rpow_neg_mul_log_pow_le K (1 / 3) (by norm_num) 50
    (ε := 25 / 34816) (by norm_num)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  rw [growth_eq_sq_mul ht0]
  have hsq : 0 < t ^ 2 := by positivity
  calc K * (t ^ 2 * (t ^ (-(1 / 3 : ℝ)) * Real.log t ^ 50))
      = t ^ 2 * (K * (t ^ (-(1 / 3 : ℝ)) * Real.log t ^ 50)) := by ring
    _ ≤ t ^ 2 * (25 / 34816) := by gcongr
    _ < 25 * t ^ 2 / 17408 := by nlinarith

/-! ## Nonvanishing of `Λ(1+2it)` -/

theorem norm_sq_eisLineLambda_pos {t : ℝ} (ht : 0 ≤ t) : 0 < ‖eisLineLambda t‖ ^ 2 := by
  have hz : riemannZeta (1 + 2 * ((t : ℂ) * Complex.I)) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  have h := normSq_eisLineLambda_ge ht
  have : 0 < Real.exp (-(Real.pi * t)) * ‖riemannZeta (1 + 2 * ((t : ℂ) * Complex.I))‖ ^ 2 := by
    have := norm_pos_iff.mpr hz
    positivity
  linarith

/-! ## The sign law -/

/-- **The on-line clock sign law for the Eisenstein source.**  For all large `t`, with
`F_t ∈ L²(𝒟)` the principal-subtraction Eisenstein source on the line `1/2 + it`,
`0 < Re ⟪(Im K̂)(C) F_t, F_t⟫`. -/
theorem hb_online_sign_law_eisenstein_source :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∃ ht : 2 ≤ t,
      0 < RCLike.re ⟪cfc (skewCovKernelIm t) modularCovariance (eisSourceL2 t ht),
        eisSourceL2 t ht⟫_ℂ := by
  obtain ⟨B, T, hB, hT3, hV⟩ := exists_vBound_le_growth
  have hH : 0 < sourceHeight := Real.exp_pos 2
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (eventually_mul_growth_lt (128 * sourceHeight + B))
  refine ⟨max (max T T₂) 50, fun t ht => ?_⟩
  have htT : T ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htT₂ : T₂ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have ht50 : (50 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have ht3 : 3 ≤ t := le_trans hT3 htT
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  refine ⟨ht2, ?_⟩
  have hasm := hb_online_clock_spectral_assembly' t ht50 (eisSourceL2 t ht2)
  have hgrow := hT₂ t htT₂
  have hVb := hV t htT
  -- the mean and the Lambda value, as opaque names
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ p in fullDomain, eisSourceCoord t p.1 p.2 / p.2 ^ 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ‖eisLineLambda t‖ ^ 2 := ⟨_, rfl⟩
  have hMge : (5 / 2) * L ≤ M := by
    rw [hM, hL]; exact setIntegral_fullDomain_eisSourceCoord_div_ge ht2
  have hLpos : 0 < L := by rw [hL]; exact norm_sq_eisLineLambda_pos ht0.le
  have hMnn : 0 ≤ M := by linarith
  -- the constant mode is `M²`
  have hI : ‖∫ z in fd, modularToLp (eisSourceL2 t ht2) z ∂volume‖ ^ 2 = M ^ 2 := by
    rw [setIntegral_eisSourceL2 ht2, setIntegral_fd_eisSourceReal, ← hM, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  -- the fluctuation is at most the mean square
  have hN : ‖eisSourceL2 t ht2 - (ℂ ∙ modularOne).starProjection (eisSourceL2 t ht2)‖ ^ 2 ≤
      L ^ 2 * (128 * sourceHeight + B * growth t) := by
    calc ‖eisSourceL2 t ht2 - (ℂ ∙ modularOne).starProjection (eisSourceL2 t ht2)‖ ^ 2
        ≤ ‖eisSourceL2 t ht2‖ ^ 2 := norm_sub_starProjection_sq_le _
      _ = ∫ p in fullDomain, eisSourceCoord t p.1 p.2 ^ 2 / p.2 ^ 2 := by
          rw [norm_sq_eisSourceL2, setIntegral_fd_eisSourceReal_sq]
      _ ≤ vBound t := by
          unfold vBound; exact setIntegral_fullDomain_eisSourceCoord_sq_div_le ht2
      _ ≤ ‖eisLineLambda t‖ ^ 4 * (128 * sourceHeight + B * growth t) := hVb
      _ = L ^ 2 * (128 * sourceHeight + B * growth t) := by rw [hL]; ring
  -- volume bounds
  have hvol := volume_fd_toReal_pos
  have hvol2 := volume_fd_toReal_le_two
  -- `M²/vol ≥ (25/4) L² / 2`
  have hM2 : (25 / 4) * L ^ 2 ≤ M ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hMge 2
    nlinarith [this]
  have hq : (25 / 4) * L ^ 2 / 2 ≤ M ^ 2 / ((volume : Measure ℍ) fd).toReal := by
    rw [div_le_div_iff₀ (by norm_num) hvol]
    nlinarith [hM2, hvol2, sq_nonneg L, hvol]
  -- the growth term is small
  have hgr1 := one_le_growth ht3
  have hsmall : 128 * sourceHeight + B * growth t < 25 * t ^ 2 / 17408 := by
    have : 128 * sourceHeight + B * growth t ≤ (128 * sourceHeight + B) * growth t := by
      nlinarith [hgr1, hH]
    linarith
  -- the strict lower bound
  have key : 0 < t ^ 11 / 2176 * (M ^ 2 / ((volume : Measure ℍ) fd).toReal) -
      t ^ 9 * (L ^ 2 * (128 * sourceHeight + B * growth t)) := by
    have h1 : t ^ 11 / 2176 * ((25 / 4) * L ^ 2 / 2) ≤
        t ^ 11 / 2176 * (M ^ 2 / ((volume : Measure ℍ) fd).toReal) := by gcongr
    have h2 : t ^ 9 * (L ^ 2 * (128 * sourceHeight + B * growth t)) <
        t ^ 9 * (L ^ 2 * (25 * t ^ 2 / 17408)) := by gcongr
    have h3 : t ^ 11 / 2176 * ((25 / 4) * L ^ 2 / 2) = t ^ 9 * (L ^ 2 * (25 * t ^ 2 / 17408)) := by
      ring
    linarith
  have hfinal : 0 < t ^ 11 / 2176 *
      (‖∫ z in fd, modularToLp (eisSourceL2 t ht2) z ∂volume‖ ^ 2 /
        ((volume : Measure ℍ) fd).toReal) -
      t ^ 9 * ‖eisSourceL2 t ht2 - (ℂ ∙ modularOne).starProjection (eisSourceL2 t ht2)‖ ^ 2 := by
    rw [hI]
    have := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ t ^ 9)
    linarith
  exact lt_of_lt_of_le hfinal hasm

end

end RHTower
