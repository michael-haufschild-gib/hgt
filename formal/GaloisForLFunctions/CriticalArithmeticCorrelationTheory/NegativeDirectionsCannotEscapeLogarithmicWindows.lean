import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UnrestrictedAtomicGardingFailsAndCollarGardingHolds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CriticalMultipleCompleteWeilPositivity
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFarReserveBelowTheEighthRoot

/-!
# Negative directions of the complete Weil matrix cannot escape logarithmic windows

At any fixed critical ratio bound `c⁸ ≤ R_max log N` (`R_max > 0`), negative or nonpositive
directions of `completeWeilMatrix tiltedUnitSpline c N` cannot escape logarithmic windows of length
`O(log(R_max + 1) + 1)` near the prime horizon:

1. **Window-localized collar Gårding and `L²` concentration.** Absorbing `(C_B (R_max + 1)) U_y²`
   into `(c_a / (2 R_max)) U_y² e^{−8u}` below `−A_R` with
   `A_R = (1/8) log(2 C_B R_max (R_max + 1) / c_a + 1) + 1 = O(log(R_max + 1) + 1)` localizes the
   `L²` defect of collar atomic Gårding to `(-A_R, 1]` (`exists_window_localized_collar_garding`).
   Whenever `weilQuad U_y ≤ 0`, at least half of `∫ U_y²` lies in `(-A_R, 1]`
   (`collar_nonpos_weilQuad_concentrates_in_log_window`).
2. **Whole-space discrete non-escape on `ℝ^N`.** Any vector `x ∈ ℝ^N` vanishing on the top
   logarithmic window `Ioc (N / S_R) N` (`log S_R ≤ (1/8) log(R_max + 1) + C₀`) rescales to horizon
   `M_R = N / S_R` at overlap `c_sub = c M_R / N`, which falls below the unconditional critical
   multiple `2 K₁ (log M_R)^{1/8}` and therefore satisfies the `(κ₀ / (2 c⁷)) ‖x‖²` spectral floor
   (`exists_completeWeilEnergy_floor_of_vanish_top_log_window`,
   `eventually_nonpos_completeWeilEnergy_not_escape_log_window`).
3. **All-ratio far Gårding on `(V_1)ᗮ`.** Expressing `prefixPoleMoment M x` on `(V_1)ᗮ` through the
   `e^{−u/2}` moment of the normalized collar profile `U_y` absorbs its coherent window cost into
   `W₈(U_y) + ∫ U_y²`, yielding an all-ratio far Gårding inequality retaining `(7/8) D_M`,
   `(g₀ / (8 c⁷)) log N · S₇`, `(c c_W / R_max) W₈(U_y)`, and `(c / (4 I₂)) archForm U_y`
   (`exists_all_ratio_far_garding`).
4. **All-ratio complement Gårding above `Q₁ = ⌊(log N)^{13/32}⌋₊`.** Coupling `V_{R₀} ⊂ V_{R₁}`
   (`R₁ = subexpCutoff N`) to `(V_{R₁})ᗮ` at `k = log N / (2 D (1 + log log N)⁶)` and
   `b = (g₀ D / 4) (1 + log log N)⁵` (`b k = g₀ log N / (8 (1 + log log N))`) bounds the band–far
   cross by an `O(1 / log log N)` fraction of the far block reserves, proving both all-ratio
   complement Gårding (`exists_all_ratio_complement_garding`) and the deterministic `z ↦ w` energy
   bridge (`complement_energy_ge_far_bridge`).
5. **Signed PNT pole-cancellation bridge.** On `w ∈ (V_{R₁})ᗮ`, subtracting the coherent prime
   model `F_coh` from the smoothed prime translate `f_V^{(h)}` cancels the rank-two pole pairing
   `2 (∫ f_y e^{−u/2}) (∫ f_y e^{u/2})` of `weilQuad U_w` identically up to `O(h)`, proving that
   `(I₂ / c) completeWeilEnergy c N z` asymptotically dominates `weilQuad U_w` whenever `U_w` has
   bounded `L²`, `W₈`, and archimedean norms (`eventually_complement_collar_weilQuad_bridge`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23 ArithmeticFunction
open scoped Classical BigOperators RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticLorentzianGeometry CriticalScaleArithmeticRigidity ArithmeticElectrostatics
  ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  ArithmeticEffectivityTheory ArithmeticPositivityTheory

/-! ### 1. Window-localized collar Gårding and `L²` concentration -/

private lemma integral_sq_eq_Iic_add_Ioc {A : ℝ} (hA : 0 ≤ A) {U : ℝ → ℝ}
    (hU : Continuous U) (hUc : HasCompactSupport U) (hs : ∀ u, 1 < u → U u = 0) :
    (∫ u, U u ^ 2) =
      (∫ u, (Set.Iic (-A)).indicator (fun v => U v ^ 2) u) +
        ∫ u in Set.Ioc (-A) 1, U u ^ 2 := by
  have hU2c : HasCompactSupport (fun u => U u ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hUc ⊢
    exact hUc.mono fun u hu => by change U u = 0 at hu; change U u ^ 2 = 0; rw [hu]; norm_num
  have hi : Integrable (fun u => U u ^ 2) :=
    (hU.pow 2).integrable_of_hasCompactSupport hU2c
  have hi_le : Integrable ((Set.Iic (-A)).indicator (fun v => U v ^ 2)) :=
    hi.indicator measurableSet_Iic
  have hi_oc : Integrable ((Set.Ioc (-A) 1).indicator (fun v => U v ^ 2)) :=
    hi.indicator measurableSet_Ioc
  have hpt : (fun u => U u ^ 2) = fun u =>
      (Set.Iic (-A)).indicator (fun v => U v ^ 2) u +
        (Set.Ioc (-A) 1).indicator (fun v => U v ^ 2) u := by
    funext u
    by_cases h1 : u ≤ -A
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr h1),
        Set.indicator_of_notMem (fun hm => not_lt.mpr h1 hm.1), add_zero]
    · push Not at h1
      by_cases h2 : u ≤ 1
      · rw [Set.indicator_of_notMem (fun hm => not_le.mpr h1 (Set.mem_Iic.mp hm)),
          Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨h1, h2⟩), zero_add]
      · push Not at h2
        rw [Set.indicator_of_notMem (fun hm => not_le.mpr h1 (Set.mem_Iic.mp hm)),
          Set.indicator_of_notMem (fun hm => not_le.mpr h2 hm.2), hs u h2]
        norm_num
  rw [hpt, integral_add hi_le hi_oc, MeasureTheory.integral_indicator measurableSet_Ioc]

private lemma iic_mass_le_exponential_mass {C_B c_a R_max : ℝ}
    (hCB : 0 < C_B) (hca : 0 < c_a) (hR : 0 < R_max)
    {U : ℝ → ℝ} (hU : Continuous U) (hUc : HasCompactSupport U) :
    let A_R := (1 / 8 : ℝ) * Real.log (2 * C_B * R_max * (R_max + 1) / c_a + 1) + 1
    (2 * C_B * (R_max + 1)) * (∫ u, (Set.Iic (-A_R)).indicator (fun v => U v ^ 2) u) ≤
      (c_a / R_max) * ∫ u, U u ^ 2 * Real.exp (-(8 * u)) := by
  intro A_R
  have hU2c : HasCompactSupport (fun u => U u ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hUc ⊢
    exact hUc.mono fun u hu => by change U u = 0 at hu; change U u ^ 2 = 0; rw [hu]; norm_num
  have hi : Integrable (fun u => U u ^ 2) :=
    (hU.pow 2).integrable_of_hasCompactSupport hU2c
  have hi_le : Integrable (fun u =>
      (2 * C_B * (R_max + 1)) * (Set.Iic (-A_R)).indicator (fun v => U v ^ 2) u) :=
    (hi.indicator measurableSet_Iic).const_mul _
  have hi8 : Integrable (fun u => (c_a / R_max) * (U u ^ 2 * Real.exp (-(8 * u)))) :=
    (((hU.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hU2c.mul_right).const_mul _
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_mono hi_le hi8 fun u => ?_
  by_cases hu : u ≤ -A_R
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hu)]
    have harg : 0 < 2 * C_B * R_max * (R_max + 1) / c_a + 1 := by positivity
    have h8u : Real.log (2 * C_B * R_max * (R_max + 1) / c_a + 1) ≤ -(8 * u) := by
      have : 8 * A_R ≤ -(8 * u) := by linarith
      dsimp only [A_R] at this
      linarith
    have hexp : 2 * C_B * R_max * (R_max + 1) / c_a ≤ Real.exp (-(8 * u)) := by
      have h1 := Real.exp_le_exp.mpr h8u
      rw [Real.exp_log harg] at h1
      linarith
    have hcoef : 2 * C_B * (R_max + 1) ≤ (c_a / R_max) * Real.exp (-(8 * u)) := by
      have hm := mul_le_mul_of_nonneg_left hexp (div_nonneg hca.le hR.le)
      have hid : (c_a / R_max) * (2 * C_B * R_max * (R_max + 1) / c_a) =
          2 * C_B * (R_max + 1) := by
        field_simp [hca.ne', hR.ne']
      linarith only [hm, hid]
    calc (2 * C_B * (R_max + 1)) * U u ^ 2
        ≤ ((c_a / R_max) * Real.exp (-(8 * u))) * U u ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = (c_a / R_max) * (U u ^ 2 * Real.exp (-(8 * u))) := by ring
  · rw [Set.indicator_of_notMem (fun hm => hu (Set.mem_Iic.mp hm)), mul_zero]
    positivity

/-- **Window-localized collar atomic Gårding.**
Absorbing the far tail `u ≤ -A_R` of the `L²` norm into half of the exponential weight `e^{−8u}`
restricts the Gårding `L²` defect of the normalized collar test `U_y` to the logarithmic window
`(-A_R, 1]` of length `A_R + 1 = O(log(R_max + 1) + 1)`. -/
theorem exists_window_localized_collar_garding :
    ∃ C_B c_a c_κ C_len : ℝ, 0 < C_B ∧ 0 < c_a ∧ 0 < c_κ ∧ 1 ≤ C_len ∧
      ∀ {R_max : ℝ}, 0 < R_max →
        ∃ A_R : ℝ, 1 ≤ A_R ∧ A_R ≤ (1 / 4 : ℝ) * Real.log (R_max + 1) + C_len ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) → ∀ x : ℕ → ℝ,
              let y := atomicTailCoefficients (N / linearDefectCutoff c) x
              let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
              (c_κ / R_max) * topCollarSeventhMass (N / linearDefectCutoff c) N x +
                  (c_a / (2 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤
                weilQuad U_y + (C_B * (R_max + 1)) * ∫ u in Set.Ioc (-A_R) 1, U_y u ^ 2 := by
  obtain ⟨C_B, c_a, c_κ, hCB, hca, hcκ, hpol⟩ := exists_collar_atomic_garding_polynomial_rate
  let C_len : ℝ := (1 / 8 : ℝ) * Real.log (2 * C_B / c_a + 1) + 1
  have hClen : 1 ≤ C_len := by
    dsimp only [C_len]
    have hlog : 0 ≤ Real.log (2 * C_B / c_a + 1) :=
      Real.log_nonneg (by linarith [div_pos (mul_pos zero_lt_two hCB) hca])
    linarith
  refine ⟨C_B, c_a, c_κ, C_len, hCB, hca, hcκ, hClen, ?_⟩
  intro R_max hR
  let A_R : ℝ := (1 / 8 : ℝ) * Real.log (2 * C_B * R_max * (R_max + 1) / c_a + 1) + 1
  have hAR1 : 1 ≤ A_R := by
    dsimp only [A_R]
    have hlog : 0 ≤ Real.log (2 * C_B * R_max * (R_max + 1) / c_a + 1) :=
      Real.log_nonneg (by linarith [div_pos (by positivity : 0 < 2 * C_B * R_max * (R_max + 1)) hca])
    linarith
  have hAR_ub : A_R ≤ (1 / 4 : ℝ) * Real.log (R_max + 1) + C_len := by
    have hR1 : 1 ≤ R_max + 1 := by linarith
    have hprod : 2 * C_B * R_max * (R_max + 1) / c_a + 1 ≤
        (2 * C_B / c_a + 1) * (R_max + 1) ^ 2 := by
      have h1 : 2 * C_B * R_max * (R_max + 1) / c_a ≤ (2 * C_B / c_a) * (R_max + 1) ^ 2 := by
        rw [show 2 * C_B * R_max * (R_max + 1) / c_a =
          (2 * C_B / c_a) * (R_max * (R_max + 1)) by ring]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith only [hR]
      have h2 : (1 : ℝ) ≤ (R_max + 1) ^ 2 := one_le_pow₀ hR1
      linarith
    have hlog := Real.log_le_log (by positivity) hprod
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Nat.cast_ofNat] at hlog
    dsimp only [A_R, C_len]
    linarith
  have hLN_zero : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hev_cN : ∀ᶠ N : ℕ in atTop, (R_max + 1) * Real.log (N : ℝ) ≤ N := by
    have hev := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (R_max + 1)))
    filter_upwards [hev, eventually_ge_atTop 1] with N hlt hN1
    dsimp only [Function.comp_def] at hlt
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hm := (div_lt_iff₀ hN0).mp hlt
    have hid : 1 / (R_max + 1) * (N : ℝ) = (N : ℝ) / (R_max + 1) := by field_simp
    exact ((le_div_iff₀ (by positivity)).mp (by linarith)).trans_eq' (mul_comm _ _)
  refine ⟨A_R, hAR1, hAR_ub, ?_⟩
  filter_upwards [hpol hR, hev_cN, eventually_ge_atTop 3] with N hg hcN_b hN3 c hc1 hc8 x
  dsimp only at hg ⊢
  set M := N / linearDefectCutoff c
  set y := atomicTailCoefficients M x
  set U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hcN : c ≤ N := by
    have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hc_le : c ≤ (R_max + 1) * Real.log (N : ℝ) :=
      (le_self_pow₀ hc1 (by norm_num : 8 ≠ 0)).trans (by nlinarith only [hc8, hL0])
    exact hc_le.trans hcN_b
  have hw1 : c / (N : ℝ) ≤ 1 := (div_le_one hN0).mpr hcN
  have hg_cd : ContDiff ℝ 2 (atomDilate tiltedUnitSpline (c / N)) :=
    contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hg_supp := tiltedUnitSpline_atom_support hw0
  have hcent_cd : ContDiff ℝ 2 (centredAtomicTest tiltedUnitSpline y c N) :=
    (contDiff_atomicTest hg_cd N y).comp (contDiff_id.add contDiff_const)
  have hcent_cs : HasCompactSupport (centredAtomicTest tiltedUnitSpline y c N) :=
    (hasCompactSupport_atomicTest hg_supp N y).comp_homeomorph (Homeomorph.addRight (Real.log N))
  have hUy_cd : ContDiff ℝ 2 U_y := contDiff_const.mul hcent_cd
  have hUy_cs : HasCompactSupport U_y := hcent_cs.mul_left
  have hUy_le1 : ∀ u, 1 < u → U_y u = 0 := by
    intro u hu1
    dsimp only [U_y, normalizedCentredAtomicTest, centredAtomicTest]
    rw [show atomicTest N y (atomDilate tiltedUnitSpline (c / N)) (u + Real.log N) = 0 from ?_,
      mul_zero]
    unfold atomicTest
    refine sum_eq_zero fun n hn => ?_
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn1 hnN
    have hnot : u + Real.log N - Real.log n ∉ Set.Icc 0 (c / N) := fun hm => by
      linarith [hm.2, hw1]
    rw [hg_supp _ hnot, mul_zero]
  have hsplit := integral_sq_eq_Iic_add_Ioc (zero_le_one.trans hAR1) hUy_cd.continuous hUy_cs hUy_le1
  have htail := iic_mass_le_exponential_mass hCB hca hR hUy_cd.continuous hUy_cs
  have hg_x := hg hc1 hc8 x
  dsimp only at hg_x
  change (c_κ / R_max) * topCollarSeventhMass M N x +
      (c_a / (2 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤
    weilQuad U_y + (C_B * (R_max + 1)) * ∫ u in Set.Ioc (-A_R) 1, U_y u ^ 2
  have hhalf : (c_a / R_max) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) =
      (c_a / (2 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
        (c_a / (2 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) := by ring
  have htail_half : (C_B * (R_max + 1)) * (∫ u, (Set.Iic (-A_R)).indicator (fun v => U_y v ^ 2) u) ≤
      (c_a / (2 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) := by
    have : (c_a / (2 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) =
        (1 / 2 : ℝ) * ((c_a / R_max) * ∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) := by ring
    linarith only [htail, this]
  rw [hsplit, mul_add] at hg_x
  linarith only [hg_x, hhalf, htail_half]

/-- **`L²` concentration of nonpositive collar sources in logarithmic windows.**
At any critical ratio bound `c⁸ ≤ R_max log N`, every normalized collar source `U_y` with
`weilQuad U_y ≤ 0` concentrates at least half of its `L²` norm inside `(-A_R, 1]` with
`A_R ≤ (1/4) log(R_max + 1) + C_len`. -/
theorem collar_nonpos_weilQuad_concentrates_in_log_window :
    ∃ C_len : ℝ, 1 ≤ C_len ∧
      ∀ {R_max : ℝ}, 0 < R_max →
        ∃ A_R : ℝ, 1 ≤ A_R ∧ A_R ≤ (1 / 4 : ℝ) * Real.log (R_max + 1) + C_len ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) → ∀ x : ℕ → ℝ,
              let y := atomicTailCoefficients (N / linearDefectCutoff c) x
              let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
              weilQuad U_y ≤ 0 →
                (1 / 2 : ℝ) * (∫ u, U_y u ^ 2) ≤ ∫ u in Set.Ioc (-A_R) 1, U_y u ^ 2 := by
  obtain ⟨C_B, c_a, c_κ, hCB, hca, hcκ, hpol⟩ := exists_collar_atomic_garding_polynomial_rate
  let C_len : ℝ := (1 / 8 : ℝ) * Real.log (2 * C_B / c_a + 1) + 1
  have hClen : 1 ≤ C_len := by
    dsimp only [C_len]
    have hlog : 0 ≤ Real.log (2 * C_B / c_a + 1) :=
      Real.log_nonneg (by linarith [div_pos (mul_pos zero_lt_two hCB) hca])
    linarith
  refine ⟨C_len, hClen, ?_⟩
  intro R_max hR
  let A_R : ℝ := (1 / 8 : ℝ) * Real.log (2 * C_B * R_max * (R_max + 1) / c_a + 1) + 1
  have hAR1 : 1 ≤ A_R := by
    dsimp only [A_R]
    have hlog : 0 ≤ Real.log (2 * C_B * R_max * (R_max + 1) / c_a + 1) :=
      Real.log_nonneg (by linarith [div_pos (by positivity : 0 < 2 * C_B * R_max * (R_max + 1)) hca])
    linarith
  have hAR_ub : A_R ≤ (1 / 4 : ℝ) * Real.log (R_max + 1) + C_len := by
    have hR1 : 1 ≤ R_max + 1 := by linarith
    have hprod : 2 * C_B * R_max * (R_max + 1) / c_a + 1 ≤
        (2 * C_B / c_a + 1) * (R_max + 1) ^ 2 := by
      have h1 : 2 * C_B * R_max * (R_max + 1) / c_a ≤ (2 * C_B / c_a) * (R_max + 1) ^ 2 := by
        rw [show 2 * C_B * R_max * (R_max + 1) / c_a =
          (2 * C_B / c_a) * (R_max * (R_max + 1)) by ring]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith only [hR]
      have h2 : (1 : ℝ) ≤ (R_max + 1) ^ 2 := one_le_pow₀ hR1
      linarith
    have hlog := Real.log_le_log (by positivity) hprod
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Nat.cast_ofNat] at hlog
    dsimp only [A_R, C_len]
    linarith
  have hLN_zero : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hev_cN : ∀ᶠ N : ℕ in atTop, (R_max + 1) * Real.log (N : ℝ) ≤ N := by
    have hev := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (R_max + 1)))
    filter_upwards [hev, eventually_ge_atTop 1] with N hlt hN1
    dsimp only [Function.comp_def] at hlt
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hm := (div_lt_iff₀ hN0).mp hlt
    have hid : 1 / (R_max + 1) * (N : ℝ) = (N : ℝ) / (R_max + 1) := by field_simp
    exact ((le_div_iff₀ (by positivity)).mp (by linarith)).trans_eq' (mul_comm _ _)
  refine ⟨A_R, hAR1, hAR_ub, ?_⟩
  filter_upwards [hpol hR, hev_cN, eventually_ge_atTop 3] with N hg hcN_b hN3 c hc1 hc8 x hle0
  set M := N / linearDefectCutoff c
  set y := atomicTailCoefficients M x
  set U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hcN : c ≤ N := by
    have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hc_le : c ≤ (R_max + 1) * Real.log (N : ℝ) :=
      (le_self_pow₀ hc1 (by norm_num : 8 ≠ 0)).trans (by nlinarith only [hc8, hL0])
    exact hc_le.trans hcN_b
  have hw1 : c / (N : ℝ) ≤ 1 := (div_le_one hN0).mpr hcN
  have hg_cd : ContDiff ℝ 2 (atomDilate tiltedUnitSpline (c / N)) :=
    contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hg_supp := tiltedUnitSpline_atom_support hw0
  have hcent_cd : ContDiff ℝ 2 (centredAtomicTest tiltedUnitSpline y c N) :=
    (contDiff_atomicTest hg_cd N y).comp (contDiff_id.add contDiff_const)
  have hcent_cs : HasCompactSupport (centredAtomicTest tiltedUnitSpline y c N) :=
    (hasCompactSupport_atomicTest hg_supp N y).comp_homeomorph (Homeomorph.addRight (Real.log N))
  have hUy_cd : ContDiff ℝ 2 U_y := contDiff_const.mul hcent_cd
  have hUy_cs : HasCompactSupport U_y := hcent_cs.mul_left
  have hUy_le1 : ∀ u, 1 < u → U_y u = 0 := by
    intro u hu1
    dsimp only [U_y, normalizedCentredAtomicTest, centredAtomicTest]
    rw [show atomicTest N y (atomDilate tiltedUnitSpline (c / N)) (u + Real.log N) = 0 from ?_,
      mul_zero]
    unfold atomicTest
    refine sum_eq_zero fun n hn => ?_
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn1 hnN
    have hnot : u + Real.log N - Real.log n ∉ Set.Icc 0 (c / N) := fun hm => by
      linarith [hm.2, hw1]
    rw [hg_supp _ hnot, mul_zero]
  have hsplit := integral_sq_eq_Iic_add_Ioc (zero_le_one.trans hAR1) hUy_cd.continuous hUy_cs hUy_le1
  have htail := iic_mass_le_exponential_mass hCB hca hR hUy_cd.continuous hUy_cs
  have hg_x := hg hc1 hc8 x
  dsimp only at hg_x
  have hS7_0 : 0 ≤ (c_κ / R_max) * topCollarSeventhMass M N x :=
    mul_nonneg (div_nonneg hcκ.le hR.le) (topCollarSeventhMass_nonneg M N x)
  rw [hsplit] at hg_x ⊢
  have hB_pos : 0 < C_B * (R_max + 1) := by positivity
  set I_le := ∫ u, (Set.Iic (-A_R)).indicator (fun v => U_y v ^ 2) u
  set I_oc := ∫ u in Set.Ioc (-A_R) 1, U_y u ^ 2
  have hle_cmp : (C_B * (R_max + 1)) * I_le ≤ (C_B * (R_max + 1)) * I_oc := by
    linarith only [htail, hg_x, hS7_0, hle0]
  have hI_cmp : I_le ≤ I_oc := le_of_mul_le_mul_left hle_cmp hB_pos
  linarith only [hI_cmp]

/-! ### 2. Whole-space discrete non-escape of negative directions on `ℝ^N` -/

/-- **Whole-space spectral floor outside the top logarithmic window.**
There exists an explicit constant `C₀ ≥ 0` such that for every critical ratio bound `R_max > 0`,
one can choose a window scale `S_R ≥ 2` with `log S_R ≤ (1/8) log(R_max + 1) + C₀` so that
eventually in `N`, across all `1 ≤ c` with `c⁸ ≤ R_max log N`, every vector `x ∈ ℝ^N` vanishing on
`Ioc (N / S_R) N` satisfies `(κ₀ / (2 c⁷)) ‖x‖² ≤ completeWeilEnergy tiltedUnitSpline c N x`. -/
theorem exists_completeWeilEnergy_floor_of_vanish_top_log_window :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ {R_max : ℝ}, 0 < R_max →
        ∃ S_R : ℕ, 2 ≤ S_R ∧ Real.log (S_R : ℝ) ≤ (1 / 8 : ℝ) * Real.log (R_max + 1) + C₀ ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
              ∀ {x : EuclideanSpace ℝ (PrimeHorizonIndex N)},
                (∀ n ∈ Ioc (N / S_R) N, primeHorizonExtension x n = 0) →
                  (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 ≤
                    completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨K₁, hK₁_pos, h2K₁, hfloor_ev⟩ :=
    exists_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_at_critical_multiple
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hfloor_ev
  let C₀ : ℝ := Real.log (1 / K₁ + 1)
  have hC₀ : 0 ≤ C₀ := Real.log_nonneg (by linarith [div_pos one_pos hK₁_pos])
  refine ⟨C₀, hC₀, ?_⟩
  intro R_max hR
  let q : ℝ := (R_max + 1) ^ (1 / 8 : ℝ) / K₁
  have hq2 : 2 ≤ q := by
    dsimp only [q]
    have h1 : 1 ≤ (R_max + 1) ^ (1 / 8 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [le_div_iff₀ hK₁_pos]
    linarith only [h1, h2K₁]
  let S_R : ℕ := ⌈q⌉₊
  have hSR_ge : q ≤ (S_R : ℝ) := Nat.le_ceil q
  have hSR2 : 2 ≤ S_R := by
    have : (2 : ℝ) ≤ (S_R : ℝ) := hq2.trans hSR_ge
    exact_mod_cast this
  have hSR_pos : 0 < S_R := by omega
  have hSR_ub : Real.log (S_R : ℝ) ≤ (1 / 8 : ℝ) * Real.log (R_max + 1) + C₀ := by
    have h1 : (S_R : ℝ) ≤ q + 1 := (Nat.ceil_lt_add_one (by linarith)).le
    have h2 : q + 1 ≤ (1 / K₁ + 1) * (R_max + 1) ^ (1 / 8 : ℝ) := by
      dsimp only [q]
      have hr1 : 1 ≤ (R_max + 1) ^ (1 / 8 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have hid : (1 / K₁ + 1) * (R_max + 1) ^ (1 / 8 : ℝ) =
          (R_max + 1) ^ (1 / 8 : ℝ) / K₁ + (R_max + 1) ^ (1 / 8 : ℝ) := by ring
      linarith only [hr1, hid]
    have hSR0 : (0 : ℝ) < S_R := by exact_mod_cast hSR_pos
    have hlog := Real.log_le_log hSR0 (h1.trans h2)
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by linarith : 0 < R_max + 1)] at hlog
    dsimp only [C₀]
    linarith only [hlog]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨S_R, hSR2, hSR_ub, ?_⟩
  filter_upwards [
    eventually_ge_atTop (S_R * max N₀ 3),
    hLlim.eventually_ge_atTop (((S_R : ℝ) / K₁) ^ 8),
    hLlim.eventually_ge_atTop (2 * (Real.log (S_R : ℝ) + 1))] with N hN_div hL_small hL_half
  intro c hc1 hc8 x hvan
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  by_cases hc_small : c ≤ 2 * (S_R : ℝ)
  · have hN_ge : N₀ ≤ N := by
      have h1 : max N₀ 3 ≤ S_R * max N₀ 3 := Nat.le_mul_of_pos_left _ hSR_pos
      exact (le_max_left _ _).trans (h1.trans hN_div)
    have hN3 : 3 ≤ N := by
      have h1 : max N₀ 3 ≤ S_R * max N₀ 3 := Nat.le_mul_of_pos_left _ hSR_pos
      exact (le_max_right _ _).trans (h1.trans hN_div)
    have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hSR_K : (S_R : ℝ) / K₁ ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) := by
      have h8 : ((S_R : ℝ) / K₁) ^ 8 ≤ (Real.log (N : ℝ) ^ (1 / 8 : ℝ)) ^ 8 := by
        rwa [← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
          show (1 / 8 : ℝ) * (8 : ℕ) = 1 by norm_num, Real.rpow_one]
      exact le_of_pow_le_pow_left₀ (by norm_num : 8 ≠ 0) (by positivity) h8
    have hc_up : c ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) := by
      have hm := (div_le_iff₀ hK₁_pos).mp hSR_K
      linarith only [hc_small, hm,
        (by ring : Real.log (N : ℝ) ^ (1 / 8 : ℝ) * K₁ = K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ))]
    exact hN₀ N hN_ge c hc1 hc_up x
  · push Not at hc_small
    set M_R := N / S_R
    have hMR_max : max N₀ 3 ≤ M_R :=
      (Nat.le_div_iff_mul_le hSR_pos).mpr (by rw [Nat.mul_comm]; exact hN_div)
    have hMR_N₀ : N₀ ≤ M_R := (le_max_left _ _).trans hMR_max
    have hMR3 : 3 ≤ M_R := (le_max_right _ _).trans hMR_max
    have hMR1 : 1 ≤ M_R := by omega
    have hN1 : 1 ≤ N := hMR1.trans (Nat.div_le_self N S_R)
    have hMR_pos : (0 : ℝ) < M_R := by exact_mod_cast hMR1
    have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hSR_posR : (0 : ℝ) < S_R := by exact_mod_cast hSR_pos
    have hN_lt : N < S_R * (M_R + 1) := by
      simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ N hSR_pos
    have hN_le_2SM : (N : ℝ) ≤ 2 * (S_R : ℝ) * (M_R : ℝ) := by
      have hnat : N ≤ 2 * S_R * M_R := by omega
      exact_mod_cast hnat
    have hSM_le_N : (M_R : ℝ) * (S_R : ℝ) ≤ N := by
      exact_mod_cast Nat.div_mul_le_self N S_R
    set c_sub : ℝ := c * (M_R : ℝ) / N
    have hc_sub1 : 1 ≤ c_sub := by
      dsimp only [c_sub]
      rw [le_div_iff₀ hN_pos]
      have hm : 2 * (S_R : ℝ) * (M_R : ℝ) ≤ c * (M_R : ℝ) :=
        mul_le_mul_of_nonneg_right hc_small.le hMR_pos.le
      linarith only [hN_le_2SM, hm]
    have hc_sub0 : 0 < c_sub := zero_lt_one.trans_le hc_sub1
    have hc_sub_le_c : c_sub ≤ c := by
      dsimp only [c_sub]
      rw [div_le_iff₀ hN_pos]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.div_le_self N S_R) hc0.le
    have hc_sub_SR : c_sub ≤ c / (S_R : ℝ) := by
      dsimp only [c_sub]
      rw [div_le_div_iff₀ hN_pos hSR_posR]
      calc c * (M_R : ℝ) * (S_R : ℝ) = c * ((M_R : ℝ) * (S_R : ℝ)) := by ring
        _ ≤ c * (N : ℝ) := mul_le_mul_of_nonneg_left hSM_le_N hc0.le
    have hlogM_pos : 0 < Real.log (M_R : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < M_R by omega))
    have hlogM_lb : Real.log (N : ℝ) ≤ 2 * Real.log (M_R : ℝ) := by
      have hlog1 := Real.log_le_log hN_pos hN_le_2SM
      rw [Real.log_mul (by positivity) hMR_pos.ne',
        Real.log_mul (by norm_num) hSR_posR.ne'] at hlog1
      have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith only [hlog1, hlog2, hL_half]
    have hR_SR8 : R_max ≤ K₁ ^ 8 * (S_R : ℝ) ^ 8 := by
      have h1 : (R_max + 1) ^ (1 / 8 : ℝ) ≤ K₁ * (S_R : ℝ) :=
        (div_le_iff₀ hK₁_pos).mp hSR_ge
      have hp := pow_le_pow_left₀ (by positivity) h1 8
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ R_max + 1),
        show (1 / 8 : ℝ) * (8 : ℕ) = 1 by norm_num, Real.rpow_one, mul_pow] at hp
      linarith only [hp]
    have hc_sub_up : c_sub ≤ 2 * K₁ * Real.log (M_R : ℝ) ^ (1 / 8 : ℝ) := by
      have hc8_sub : c_sub ^ 8 ≤ (2 * K₁ * Real.log (M_R : ℝ) ^ (1 / 8 : ℝ)) ^ 8 := by
        have h1 : c_sub ^ 8 ≤ c ^ 8 / (S_R : ℝ) ^ 8 :=
          (pow_le_pow_left₀ hc_sub0.le hc_sub_SR 8).trans_eq (div_pow _ _ 8)
        have h2 : c ^ 8 / (S_R : ℝ) ^ 8 ≤ (R_max * Real.log (N : ℝ)) / (S_R : ℝ) ^ 8 :=
          div_le_div_of_nonneg_right hc8 (by positivity)
        have h3 : (R_max * Real.log (N : ℝ)) / (S_R : ℝ) ^ 8 ≤ K₁ ^ 8 * Real.log (N : ℝ) := by
          rw [div_le_iff₀ (by positivity)]
          calc R_max * Real.log (N : ℝ)
              ≤ (K₁ ^ 8 * (S_R : ℝ) ^ 8) * Real.log (N : ℝ) :=
                mul_le_mul_of_nonneg_right hR_SR8 (by linarith only [hlogM_pos, hlogM_lb])
            _ = K₁ ^ 8 * Real.log (N : ℝ) * (S_R : ℝ) ^ 8 := by ring
        have h4 : K₁ ^ 8 * Real.log (N : ℝ) ≤ (2 * K₁) ^ 8 * Real.log (M_R : ℝ) := by
          have hm := mul_le_mul_of_nonneg_left hlogM_lb (by positivity : 0 ≤ K₁ ^ 8)
          have h256 : 2 * K₁ ^ 8 ≤ (2 * K₁) ^ 8 := by
            rw [mul_pow]; nlinarith [pow_nonneg hK₁_pos.le 8]
          nlinarith only [hm, h256, hlogM_pos]
        have h5 : (2 * K₁) ^ 8 * Real.log (M_R : ℝ) =
            (2 * K₁ * Real.log (M_R : ℝ) ^ (1 / 8 : ℝ)) ^ 8 := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hlogM_pos.le,
            show (1 / 8 : ℝ) * (8 : ℕ) = 1 by norm_num, Real.rpow_one]
        exact (h1.trans (h2.trans (h3.trans h4))).trans_eq h5
      exact le_of_pow_le_pow_left₀ (by norm_num : 8 ≠ 0) (by positivity) hc8_sub
    let x_sub : EuclideanSpace ℝ (PrimeHorizonIndex M_R) :=
      horizonProfileVector (primeHorizonExtension x) M_R
    have hw_eq : c_sub / (M_R : ℝ) = c / (N : ℝ) := by
      dsimp only [c_sub]; field_simp [hMR_pos.ne', hN_pos.ne']
    have hx_van : ∀ n, M_R < n → primeHorizonExtension x n = 0 := by
      intro n hn
      by_cases hnN : n ≤ N
      · exact hvan n (mem_Ioc.mpr ⟨hn, hnN⟩)
      · unfold primeHorizonExtension
        rw [dif_neg (fun hm => hnN (mem_Icc.mp hm).2)]
    have htest_eq : atomicTest M_R (primeHorizonExtension x_sub)
        (atomDilate tiltedUnitSpline (c_sub / M_R)) =
        atomicTest N (primeHorizonExtension x) (atomDilate tiltedUnitSpline (c / N)) := by
      rw [hw_eq, atomicTest_eq_of_vanish_above (Nat.div_le_self N S_R) hx_van]
      unfold atomicTest
      refine sum_congr rfl fun n hn => ?_
      exact congrArg (· * atomDilate tiltedUnitSpline (c / N) (_ - Real.log n))
        (primeHorizonExtension_coe x_sub ⟨n, hn⟩)
    have henergy_eq : completeWeilEnergy tiltedUnitSpline c N x =
        completeWeilEnergy tiltedUnitSpline c_sub M_R x_sub := by
      unfold completeWeilEnergy
      rw [completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
          hc0 hN1,
        completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
          hc_sub0 hMR1,
        htest_eq, hw_eq]
    have hnorm_eq : ‖x‖ ^ 2 = ‖x_sub‖ ^ 2 := by
      rw [← sum_primeHorizonExtension_sq x, ← sum_primeHorizonExtension_sq x_sub]
      have hsub : Icc 1 N = Icc 1 M_R ∪ Ioc M_R N := by
        ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
      rw [hsub, sum_union (disjoint_left.mpr fun n h1 h2 => by
        simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
      have hzero : (∑ n ∈ Ioc M_R N, primeHorizonExtension x n ^ 2) = 0 :=
        sum_eq_zero fun n hn => by rw [hvan n hn, sq, mul_zero]
      rw [hzero, add_zero]
      refine sum_congr rfl fun n hn => ?_
      exact congrArg (· ^ 2) (primeHorizonExtension_coe x_sub ⟨n, hn⟩).symm
    have hfl_sub := hN₀ M_R hMR_N₀ c_sub hc_sub1 hc_sub_up x_sub
    have hc7_le : c_sub ^ 7 ≤ c ^ 7 := pow_le_pow_left₀ hc_sub0.le hc_sub_le_c 7
    have hdiv_le : tiltedSplineSpectralFloorConstant / (2 * c ^ 7) ≤
        tiltedSplineSpectralFloorConstant / (2 * c_sub ^ 7) :=
      div_le_div_of_nonneg_left tiltedSplineSpectralFloorConstant_pos.le (by positivity)
        (by linarith only [hc7_le])
    rw [henergy_eq, hnorm_eq]
    exact (mul_le_mul_of_nonneg_right hdiv_le (sq_nonneg _)).trans hfl_sub

/-- **Discrete non-escape of nonpositive directions on `ℝ^N`.**
At any fixed critical ratio bound `c⁸ ≤ R_max log N`, no nonzero vector `x ∈ ℝ^N` with
`completeWeilEnergy tiltedUnitSpline c N x ≤ 0` can vanish on the top logarithmic window
`Ioc (N / S_R) N` (`log S_R ≤ (1/8) log(R_max + 1) + C₀`). -/
theorem eventually_nonpos_completeWeilEnergy_not_escape_log_window :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ {R_max : ℝ}, 0 < R_max →
        ∃ S_R : ℕ, 2 ≤ S_R ∧ Real.log (S_R : ℝ) ≤ (1 / 8 : ℝ) * Real.log (R_max + 1) + C₀ ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
              ∀ {x : EuclideanSpace ℝ (PrimeHorizonIndex N)},
                x ≠ 0 → completeWeilEnergy tiltedUnitSpline c N x ≤ 0 →
                  ∃ n ∈ Ioc (N / S_R) N, primeHorizonExtension x n ≠ 0 := by
  obtain ⟨C₀, hC₀, hfl⟩ := exists_completeWeilEnergy_floor_of_vanish_top_log_window
  refine ⟨C₀, hC₀, ?_⟩
  intro R_max hR
  obtain ⟨S_R, hSR2, hSR_ub, hev⟩ := hfl hR
  refine ⟨S_R, hSR2, hSR_ub, ?_⟩
  filter_upwards [hev] with N hN c hc1 hc8 x hx_ne hle0
  by_contra hall
  push Not at hall
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hpos : 0 < (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 :=
    mul_pos (div_pos tiltedSplineSpectralFloorConstant_pos (by positivity))
      (sq_pos_of_pos (norm_pos_iff.mpr hx_ne))
  linarith only [hpos, hN hc1 hc8 hall, hle0]

/-! ### 3. Exponential absorption of `prefixPoleMoment` and all-ratio far Gårding on `(V_1)ᗮ` -/

/-- Any continuous compactly supported source vanishing above `1` has `(∫ U(u) e^{−u/2} du)²`
bounded by `ε ∫ U(u)² e^{−8u} du + (4 + 2 / ε) ∫ U(u)² du`. -/
theorem sq_exp_neg_half_moment_le_exponential_mass {ε : ℝ} (hε : 0 < ε)
    {U : ℝ → ℝ} (hU : Continuous U) (hUc : HasCompactSupport U) (hs : ∀ u, 1 < u → U u = 0) :
    (∫ u, U u * Real.exp (-(u / 2))) ^ 2 ≤
      ε * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) + (4 + 2 / ε) * ∫ u, U u ^ 2 := by
  let B₀ : ℝ := 4 + 2 / ε
  have hB₄ : 4 ≤ B₀ := by dsimp only [B₀]; linarith [div_pos zero_lt_two hε]
  have hBε : 2 / ε ≤ B₀ := by dsimp only [B₀]; linarith
  have hB0 : 0 < B₀ := by linarith
  have hεB : 1 ≤ ε * B₀ := by
    have hm := (div_le_iff₀ hε).mp hBε
    linarith
  let W : ℝ → ℝ := fun u => ε * Real.exp (-(8 * u)) + B₀
  have hW_pos : ∀ u, 0 < W u := fun u => by dsimp only [W]; positivity
  let Φ : ℝ → ℝ := fun u =>
    (Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v)) u +
      (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 / 4 : ℝ)) u
  have hΦ_bound : ∀ u, u ≤ 1 → Real.exp (-(u / 2)) ^ 2 / W u ≤ Φ u := by
    intro u hu1
    have hexp_sq : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hexp_sq]
    by_cases hu0 : u ≤ 0
    · have hind : Φ u = (1 / 2 : ℝ) * Real.exp (3 * u) := by
        dsimp only [Φ]
        rw [Set.indicator_of_mem (Set.mem_Iic.mpr hu0),
          Set.indicator_of_notMem (fun h => not_lt.mpr hu0 h.1), add_zero]
      rw [hind]
      have hW_lo : 2 * Real.exp (-(4 * u)) ≤ W u := by
        let a := Real.sqrt ε * Real.exp (-(4 * u))
        let b := Real.sqrt B₀
        have ha2 : a ^ 2 = ε * Real.exp (-(8 * u)) := by
          dsimp only [a]
          rw [mul_pow, Real.sq_sqrt hε.le, ← Real.exp_nat_mul]
          congr 2; push_cast; ring
        have hb2 : b ^ 2 = B₀ := Real.sq_sqrt hB0.le
        have hab : 1 ≤ Real.sqrt ε * Real.sqrt B₀ := by
          rw [← Real.sqrt_mul hε.le]; exact Real.one_le_sqrt.mpr hεB
        have hprod : Real.exp (-(4 * u)) ≤ a * b := by
          have : a * b = (Real.sqrt ε * Real.sqrt B₀) * Real.exp (-(4 * u)) := by
            dsimp only [a, b]; ring
          rw [this]
          exact le_mul_of_one_le_left (Real.exp_pos _).le hab
        have hsq0 := sq_nonneg (a - b)
        dsimp only [W]
        nlinarith only [ha2, hb2, hprod, hsq0]
      calc Real.exp (-u) / W u
          ≤ Real.exp (-u) / (2 * Real.exp (-(4 * u))) :=
            div_le_div₀ (Real.exp_pos (-u)).le le_rfl (by positivity) hW_lo
        _ = (1 / 2 : ℝ) * Real.exp (3 * u) := by
            rw [div_mul_eq_div_div_swap, ← Real.exp_sub]; ring_nf
    · push Not at hu0
      have hind : Φ u = 1 / 4 := by
        have hnot : u ∉ Set.Iic (0 : ℝ) := fun h => not_le.mpr hu0 (Set.mem_Iic.mp h)
        dsimp only [Φ]
        rw [Set.indicator_of_notMem hnot,
          Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu0, hu1⟩), zero_add]
      rw [hind]
      have he1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hW4 : 4 ≤ W u := by
        dsimp only [W]
        linarith [mul_nonneg hε.le (Real.exp_pos (-(8 * u))).le, hB₄]
      exact div_le_div₀ zero_le_one he1 (by norm_num) hW4
  have hi_Iic : Integrable ((Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v))) := by
    have hneg : IntegrableOn (fun v : ℝ => (1 / 2 : ℝ) * Real.exp (-(3 * v))) (Set.Ioi 0) := by
      have h1 := integrableOn_exp_mul_Ioi (by norm_num : -(3 : ℝ) < 0) 0
      change Integrable _ _
      simpa only [neg_mul] using h1.const_mul (1 / 2 : ℝ)
    have hcomp : Integrable (fun v : ℝ =>
        (Set.Ioi (0 : ℝ)).indicator (fun x => (1 / 2 : ℝ) * Real.exp (-(3 * x))) (-v)) :=
      (hneg.integrable_indicator measurableSet_Ioi).comp_neg
    refine hcomp.congr ?_
    have hsub : {v : ℝ | ¬((Set.Ioi (0 : ℝ)).indicator
        (fun x => (1 / 2 : ℝ) * Real.exp (-(3 * x))) (-v) =
        (Set.Iic (0 : ℝ)).indicator (fun x => (1 / 2 : ℝ) * Real.exp (3 * x)) v)} ⊆ {(0 : ℝ)} := by
      intro v hv
      by_contra hne
      apply hv
      rcases lt_trichotomy v 0 with hlt | rfl | hgt
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr (neg_pos.mpr hlt)),
          Set.indicator_of_mem (Set.mem_Iic.mpr hlt.le)]
        ring_nf
      · exact (hne rfl).elim
      · rw [Set.indicator_of_notMem (fun h => by simp at h; linarith),
          Set.indicator_of_notMem (fun h => by simp at h; linarith)]
    exact ae_iff.mpr (measure_mono_null hsub (measure_singleton 0))
  have hi_Ioc : Integrable ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 / 4 : ℝ))) :=
    (integrableOn_const (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  have hiΦ : Integrable Φ := hi_Iic.add hi_Ioc
  have hint_Φ : ∫ u, Φ u ≤ 1 := by
    have h1 : (∫ u, (Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v)) u) =
        1 / 6 := by
      have heq : (∫ u, (Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v)) u) =
          ∫ v in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * Real.exp (-(3 : ℝ) * v) := by
        rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
          (MeasurableEquiv.neg ℝ).measurableEmbedding
          (fun u => (Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v)) u)]
        have hae : (fun v : ℝ =>
            (Set.Iic (0 : ℝ)).indicator (fun x => (1 / 2 : ℝ) * Real.exp (3 * x)) (-v)) =ᵐ[volume]
            (Set.Ioi (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (-(3 : ℝ) * v)) := by
          have hsub : {v : ℝ | ¬((Set.Iic (0 : ℝ)).indicator
              (fun x => (1 / 2 : ℝ) * Real.exp (3 * x)) (-v) =
              (Set.Ioi (0 : ℝ)).indicator (fun x => (1 / 2 : ℝ) * Real.exp (-(3 : ℝ) * x)) v)} ⊆
              {(0 : ℝ)} := by
            intro v hv
            by_contra hne
            apply hv
            rcases lt_trichotomy v 0 with hlt | rfl | hgt
            · rw [Set.indicator_of_notMem (fun h => by simp at h; linarith),
                Set.indicator_of_notMem (fun h => by simp at h; linarith)]
            · exact (hne rfl).elim
            · rw [Set.indicator_of_mem (by simp; linarith),
                Set.indicator_of_mem (Set.mem_Ioi.mpr hgt)]
              ring_nf
          exact ae_iff.mpr (measure_mono_null hsub (measure_singleton 0))
        rw [integral_congr_ae hae, MeasureTheory.integral_indicator measurableSet_Ioi]
      rw [heq, integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(3 : ℝ) < 0) 0]
      norm_num
    have h2 : (∫ u, (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 / 4 : ℝ)) u) = 1 / 4 := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul,
        Real.volume_real_Ioc_of_le zero_le_one]
      norm_num
    have hadd : ∫ u, Φ u =
        (∫ u, (Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v)) u) +
          ∫ u, (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 / 4 : ℝ)) u :=
      integral_add hi_Iic hi_Ioc
    linarith
  have hU2c : HasCompactSupport (fun u => U u ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hUc ⊢
    exact hUc.mono fun u hu => by change U u = 0 at hu; change U u ^ 2 = 0; rw [hu]; norm_num
  have hi8 : Integrable (fun u => U u ^ 2 * Real.exp (-(8 * u))) :=
    ((hU.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hU2c.mul_right
  have hi0 : Integrable (fun u => U u ^ 2) :=
    (hU.pow 2).integrable_of_hasCompactSupport hU2c
  have hiUW : Integrable (fun u => U u ^ 2 * W u) :=
    ((hU.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hU2c.mul_right
  have hiUE : Integrable (fun u => U u * Real.exp (-(u / 2))) :=
    (hU.mul (by fun_prop)).integrable_of_hasCompactSupport hUc.mul_right
  set A := ∫ u, U u ^ 2 * W u
  have hA0 : 0 ≤ A := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (hW_pos u).le
  have hquad : ∀ t : ℝ, 0 ≤ A * (t * t) + (2 * ∫ u, U u * Real.exp (-(u / 2))) * t + ∫ u, Φ u := by
    intro t
    have hpt : ∀ u : ℝ,
        0 ≤ (t * t) * (U u ^ 2 * W u) + 2 * t * (U u * Real.exp (-(u / 2))) + Φ u := by
      intro u
      by_cases hu1 : u ≤ 1
      · have hw0 := hW_pos u
        have hsw : Real.sqrt (W u) ≠ 0 := (Real.sqrt_pos.mpr hw0).ne'
        have hsq := sq_nonneg (t * U u * Real.sqrt (W u) + Real.exp (-(u / 2)) / Real.sqrt (W u))
        have hexp_sq : (t * U u * Real.sqrt (W u) + Real.exp (-(u / 2)) / Real.sqrt (W u)) ^ 2 =
            (t * t) * (U u ^ 2 * W u) + 2 * t * (U u * Real.exp (-(u / 2))) +
              Real.exp (-(u / 2)) ^ 2 / W u := by
          have h1 : Real.sqrt (W u) ^ 2 = W u := Real.sq_sqrt hw0.le
          field_simp [hsw]; rw [h1]; ring
        linarith only [hsq, hexp_sq, hΦ_bound u hu1]
      · push Not at hu1
        rw [hs u hu1]
        have hnot1 : u ∉ Set.Iic (0 : ℝ) := fun hm => by linarith [Set.mem_Iic.mp hm]
        have hnot2 : u ∉ Set.Ioc (0 : ℝ) 1 := fun hm => not_le.mpr hu1 hm.2
        dsimp only [Φ]
        rw [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot2]
        norm_num
    have hint_sum := integral_nonneg hpt
    rw [integral_add ((hiUW.const_mul _).add (hiUE.const_mul _)) hiΦ,
      integral_add (hiUW.const_mul _) (hiUE.const_mul _),
      integral_const_mul, integral_const_mul] at hint_sum
    dsimp only [A]; linarith only [hint_sum]
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  have hAW : A = ε * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) + B₀ * ∫ u, U u ^ 2 := by
    dsimp only [A, W]
    have hfn : (fun u => U u ^ 2 * (ε * Real.exp (-(8 * u)) + B₀)) =
        fun u => ε * (U u ^ 2 * Real.exp (-(8 * u))) + B₀ * U u ^ 2 := funext fun u => by ring
    rw [hfn, integral_add (hi8.const_mul _) (hi0.const_mul _), integral_const_mul, integral_const_mul]
  nlinarith only [hd, hint_Φ, hA0, hAW]

/-- Any continuous compactly supported source vanishing above `1` has `(∫ U(u) e^{u/2} du)² ≤ 4 ∫ U(u)² du`. -/
theorem sq_exp_pos_half_moment_le_l2
    {U : ℝ → ℝ} (hU : Continuous U) (hUc : HasCompactSupport U) (hs : ∀ u, 1 < u → U u = 0) :
    (∫ u, U u * Real.exp (u / 2)) ^ 2 ≤ 4 * ∫ u, U u ^ 2 := by
  let Φ : ℝ → ℝ := fun u =>
    (Set.Iic (0 : ℝ)).indicator (fun v => Real.exp v) u +
      (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (3 : ℝ)) u
  have hΦ_bound : ∀ u, u ≤ 1 → Real.exp (u / 2) ^ 2 ≤ Φ u := by
    intro u hu1
    have hexp_sq : Real.exp (u / 2) ^ 2 = Real.exp u := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hexp_sq]
    by_cases hu0 : u ≤ 0
    · dsimp only [Φ]
      rw [Set.indicator_of_mem (Set.mem_Iic.mpr hu0),
        Set.indicator_of_notMem (fun h => not_lt.mpr hu0 h.1), add_zero]
    · push Not at hu0
      dsimp only [Φ]
      rw [Set.indicator_of_notMem (fun h => not_le.mpr hu0 (Set.mem_Iic.mp h)),
        Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu0, hu1⟩), zero_add]
      exact (Real.exp_le_exp.mpr hu1).trans (by linarith [Real.exp_one_lt_d9])
  have hi_Iic : Integrable ((Set.Iic (0 : ℝ)).indicator (fun v => Real.exp v)) := by
    have hneg : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Set.Ioi 0) := by
      have h1 := integrableOn_exp_mul_Ioi (by norm_num : -(1 : ℝ) < 0) 0
      change Integrable _ _
      simpa only [neg_one_mul] using h1
    have hcomp : Integrable (fun v : ℝ =>
        (Set.Ioi (0 : ℝ)).indicator (fun x => Real.exp (-x)) (-v)) :=
      (hneg.integrable_indicator measurableSet_Ioi).comp_neg
    refine hcomp.congr ?_
    have hsub : {v : ℝ | ¬((Set.Ioi (0 : ℝ)).indicator (fun x => Real.exp (-x)) (-v) =
        (Set.Iic (0 : ℝ)).indicator (fun x => Real.exp x) v)} ⊆ {(0 : ℝ)} := by
      intro v hv
      by_contra hne
      apply hv
      rcases lt_trichotomy v 0 with hlt | rfl | hgt
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr (neg_pos.mpr hlt)),
          Set.indicator_of_mem (Set.mem_Iic.mpr hlt.le), neg_neg]
      · exact (hne rfl).elim
      · rw [Set.indicator_of_notMem (fun h => by simp at h; linarith),
          Set.indicator_of_notMem (fun h => by simp at h; linarith)]
    exact ae_iff.mpr (measure_mono_null hsub (measure_singleton 0))
  have hi_Ioc : Integrable ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => (3 : ℝ))) :=
    (integrableOn_const (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  have hiΦ : Integrable Φ := hi_Iic.add hi_Ioc
  have hint_Φ : ∫ u, Φ u ≤ 4 := by
    have h1 : (∫ u, (Set.Iic (0 : ℝ)).indicator (fun v => Real.exp v) u) = 1 := by
      have heq : (∫ u, (Set.Iic (0 : ℝ)).indicator (fun v => Real.exp v) u) =
          ∫ v in Set.Ioi (0 : ℝ), Real.exp (-(1 : ℝ) * v) := by
        rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
          (MeasurableEquiv.neg ℝ).measurableEmbedding
          (fun u => (Set.Iic (0 : ℝ)).indicator (fun v => Real.exp v) u)]
        have hae : (fun v : ℝ => (Set.Iic (0 : ℝ)).indicator (fun x => Real.exp x) (-v)) =ᵐ[volume]
            (Set.Ioi (0 : ℝ)).indicator (fun v => Real.exp (-(1 : ℝ) * v)) := by
          have hsub : {v : ℝ | ¬((Set.Iic (0 : ℝ)).indicator (fun x => Real.exp x) (-v) =
              (Set.Ioi (0 : ℝ)).indicator (fun x => Real.exp (-(1 : ℝ) * x)) v)} ⊆ {(0 : ℝ)} := by
            intro v hv
            by_contra hne
            apply hv
            rcases lt_trichotomy v 0 with hlt | rfl | hgt
            · rw [Set.indicator_of_notMem (fun h => by simp at h; linarith),
                Set.indicator_of_notMem (fun h => by simp at h; linarith)]
            · exact (hne rfl).elim
            · rw [Set.indicator_of_mem (by simp; linarith),
                Set.indicator_of_mem (Set.mem_Ioi.mpr hgt)]; ring_nf
          exact ae_iff.mpr (measure_mono_null hsub (measure_singleton 0))
        rw [integral_congr_ae hae, MeasureTheory.integral_indicator measurableSet_Ioi]
      rw [heq, integral_exp_mul_Ioi (by norm_num : -(1 : ℝ) < 0) 0]; norm_num
    have h2 : (∫ u, (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (3 : ℝ)) u) = 3 := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul,
        Real.volume_real_Ioc_of_le zero_le_one]; norm_num
    have hadd : ∫ u, Φ u =
        (∫ u, (Set.Iic (0 : ℝ)).indicator (fun v => Real.exp v) u) +
          ∫ u, (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (3 : ℝ)) u :=
      integral_add hi_Iic hi_Ioc
    linarith
  have hU2c : HasCompactSupport (fun u => U u ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hUc ⊢
    exact hUc.mono fun u hu => by change U u = 0 at hu; change U u ^ 2 = 0; rw [hu]; norm_num
  have hi0 : Integrable (fun u => U u ^ 2) :=
    (hU.pow 2).integrable_of_hasCompactSupport hU2c
  have hiUE : Integrable (fun u => U u * Real.exp (u / 2)) :=
    (hU.mul (by fun_prop)).integrable_of_hasCompactSupport hUc.mul_right
  set A := ∫ u, U u ^ 2
  have hA0 : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hquad : ∀ t : ℝ, 0 ≤ A * (t * t) + (2 * ∫ u, U u * Real.exp (u / 2)) * t + ∫ u, Φ u := by
    intro t
    have hpt : ∀ u : ℝ, 0 ≤ (t * t) * U u ^ 2 + 2 * t * (U u * Real.exp (u / 2)) + Φ u := by
      intro u
      by_cases hu1 : u ≤ 1
      · have hsq := sq_nonneg (t * U u + Real.exp (u / 2))
        linarith only [hsq, hΦ_bound u hu1]
      · push Not at hu1
        rw [hs u hu1]
        have hnot1 : u ∉ Set.Iic (0 : ℝ) := fun hm => by linarith [Set.mem_Iic.mp hm]
        have hnot2 : u ∉ Set.Ioc (0 : ℝ) 1 := fun hm => not_le.mpr hu1 hm.2
        dsimp only [Φ]
        rw [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot2]
        norm_num
    have hint_sum := integral_nonneg hpt
    rw [integral_add ((hi0.const_mul _).add (hiUE.const_mul _)) hiΦ,
      integral_add (hi0.const_mul _) (hiUE.const_mul _),
      integral_const_mul, integral_const_mul] at hint_sum
    dsimp only [A]; linarith only [hint_sum]
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith only [hd, hint_Φ, hA0]

theorem integral_tiltedUnitSpline_pos : 0 < ∫ u, tiltedUnitSpline u := by
  have hnn : 0 ≤ tiltedUnitSpline := fun u => RenormalizedIntersectionTheory.tiltedUnitSpline_nonneg u
  have hi : Integrable tiltedUnitSpline :=
    contDiff_tiltedUnitSpline.continuous.integrable_of_hasCompactSupport hasCompactSupport_tiltedUnitSpline
  refine lt_of_le_of_ne (integral_nonneg hnn) fun h0 => ?_
  have hae := (integral_eq_zero_iff_of_nonneg hnn hi).mp h0.symm
  have hae2 : (fun u => tiltedUnitSpline u ^ 2) =ᵐ[volume] 0 :=
    hae.mono fun u hu => by dsimp only [Pi.zero_apply] at hu ⊢; rw [hu, sq, mul_zero]
  exact integral_tiltedUnitSpline_sq_pos.ne' (integral_eq_zero_of_ae hae2)

/-- On `(conductorSubspace 1 N)ᗮ`, `prefixPoleMoment M x = -poleFunctional N y` is proportional to
`∫ U_y(v) e^{−v/2} dv`, so `prefixPoleMoment M x ^ 2` is controlled by `W₈(U_y) + ∫ U_y²`. -/
theorem prefixPoleMoment_sq_le_exponential_mass {N M : ℕ} {c ε : ℝ}
    (hN2 : 2 ≤ N) (hMN : M ≤ N) (hc1 : 1 ≤ c) (hcN : c ≤ N) (hε : 0 < ε)
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ (conductorSubspace 1 N)ᗮ) :
    let x := primeHorizonExtension z
    let y := atomicTailCoefficients M x
    let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
    prefixPoleMoment M x ^ 2 ≤
      (Real.exp 1 / (∫ u, tiltedUnitSpline u) ^ 2) *
        (ε * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + (4 + 2 / ε) * ∫ u, U_y u ^ 2) := by
  intro x y U_y
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set w := c / (N : ℝ)
  have hw0 : 0 < w := div_pos hc0 hN0
  have hw1 : w ≤ 1 := (div_le_one hN0).mpr hcN
  set g := atomDilate tiltedUnitSpline w
  have hg_cd : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hg_supp := tiltedUnitSpline_atom_support hw0
  have hg_cs := hasCompactSupport_atomDilate hw0.ne' hasCompactSupport_tiltedUnitSpline
  have hpole_z := poleFunctional_eq_zero_of_mem_conductorSubspace_one_orthogonal hN2 hz
  have hpole_split : poleFunctional N x = prefixPoleMoment M x + poleFunctional N y := by
    unfold poleFunctional prefixPoleMoment
    have hdisj : Icc 1 N = Icc 1 M ∪ Ioc M N := by
      ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    rw [hdisj, sum_union (disjoint_left.mpr fun n h1 h2 => by
      simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
    congr 1
    rw [hdisj, sum_union (disjoint_left.mpr fun n h1 h2 => by
      simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
    have h0 : (∑ n ∈ Icc 1 M, y n / Real.sqrt n) = 0 :=
      sum_eq_zero fun n hn => by
        dsimp only [y, atomicTailCoefficients]
        rw [if_neg (Nat.not_lt.mpr (mem_Icc.mp hn).2), zero_div]
    rw [h0, zero_add]
    refine sum_congr rfl fun n hn => ?_
    dsimp only [y, atomicTailCoefficients]
    rw [if_pos (mem_Ioc.mp hn).1]
  have hy_pole : poleFunctional N y = -prefixPoleMoment M x := by linarith only [hpole_z, hpole_split]
  have hf_int := integral_atomicTest_mul_exp_neg_half hg_cd.continuous hg_supp N y
  rw [hy_pole] at hf_int
  have hshift : (∫ u, atomicTest N y g u * Real.exp (-(u / 2))) =
      w * ∫ v, U_y v * Real.exp (-(v / 2)) := by
    rw [← integral_add_right_eq_self (fun u => atomicTest N y g u * Real.exp (-(u / 2))) (Real.log N)]
    have hfn : (fun v => atomicTest N y g (v + Real.log N) * Real.exp (-((v + Real.log N) / 2))) =
        fun v => w * (U_y v * Real.exp (-(v / 2))) := by
      funext v
      have hexp : Real.exp (-((v + Real.log N) / 2)) =
          Real.exp (-(v / 2)) * (1 / Real.sqrt N) := by
        rw [show -((v + Real.log N) / 2) = -(v / 2) + -(Real.log N / 2) by ring,
          Real.exp_add, Real.exp_neg, ← Real.sqrt_eq_rpow]
        have hsq : Real.exp (Real.log N / 2) = Real.sqrt N := by
          apply ( sq_eq_sq₀ (Real.exp_pos _).le (Real.sqrt_nonneg _) ).mp
          rw [← Real.exp_nat_mul, Real.sq_sqrt hN0.le]
          have : (2 : ℕ) * (Real.log (N : ℝ) / 2) = Real.log (N : ℝ) := by push_cast; ring
          rw [this, Real.exp_log hN0]
        rw [hsq, one_div]
      dsimp only [U_y, normalizedCentredAtomicTest, centredAtomicTest, w]
      rw [hexp]
      have hsqN : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
      field_simp [hc0.ne', hN0.ne', hsqN]
      rw [Real.sq_sqrt hN0.le]
    rw [hfn, integral_const_mul]
  have hg_lb : Real.exp (-(1 / 2 : ℝ)) * w * (∫ u, tiltedUnitSpline u) ≤
      ∫ t, g t * Real.exp (-(t / 2)) := by
    have hgi : Integrable g := hg_cd.continuous.integrable_of_hasCompactSupport hg_cs
    have hge : Integrable (fun t => g t * Real.exp (-(t / 2))) :=
      (hg_cd.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hg_cs.mul_right
    have hint_g : ∫ t, g t = w * ∫ u, tiltedUnitSpline u := by
      have h := Measure.integral_comp_div (fun u => tiltedUnitSpline u) w
      simpa only [smul_eq_mul, abs_of_pos hw0] using h
    rw [mul_assoc, ← hint_g, ← integral_const_mul]
    refine integral_mono (hgi.const_mul _) hge fun t => ?_
    by_cases ht : t ∈ Set.Icc 0 w
    · have hg0 : 0 ≤ g t := RenormalizedIntersectionTheory.tiltedUnitSpline_nonneg _
      have hexp_le : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-(t / 2)) :=
        Real.exp_le_exp.mpr (by linarith [ht.2, hw1])
      calc Real.exp (-(1 / 2 : ℝ)) * g t ≤ Real.exp (-(t / 2)) * g t :=
            mul_le_mul_of_nonneg_right hexp_le hg0
        _ = g t * Real.exp (-(t / 2)) := mul_comm _ _
    · rw [hg_supp t ht, mul_zero, zero_mul]
  have hI₁ : 0 < ∫ u, tiltedUnitSpline u := integral_tiltedUnitSpline_pos
  have hg_pos : 0 < ∫ t, g t * Real.exp (-(t / 2)) :=
    lt_of_lt_of_le (by positivity) hg_lb
  have habs_id : (∫ t, g t * Real.exp (-(t / 2))) * |prefixPoleMoment M x| =
      w * |∫ v, U_y v * Real.exp (-(v / 2))| := by
    have h1 := congrArg abs (hf_int.symm.trans hshift)
    rwa [abs_mul, abs_of_pos hg_pos, abs_neg, abs_mul, abs_of_pos hw0] at h1
  have hσ_abs : |prefixPoleMoment M x| ≤
      (Real.exp (1 / 2 : ℝ) / ∫ u, tiltedUnitSpline u) * |∫ v, U_y v * Real.exp (-(v / 2))| := by
    have hm : (Real.exp (-(1 / 2 : ℝ)) * w * ∫ u, tiltedUnitSpline u) * |prefixPoleMoment M x| ≤
        w * |∫ v, U_y v * Real.exp (-(v / 2))| :=
      (mul_le_mul_of_nonneg_right hg_lb (abs_nonneg _)).trans_eq habs_id
    rw [le_div_iff₀' (by positivity : 0 < ∫ u, tiltedUnitSpline u)] at *
    have hw_cancel : (Real.exp (-(1 / 2 : ℝ)) * ∫ u, tiltedUnitSpline u) * |prefixPoleMoment M x| ≤
        |∫ v, U_y v * Real.exp (-(v / 2))| := by
      refine le_of_mul_le_mul_left ?_ hw0
      linarith only [hm]
    have hexp_inv : Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hm2 := mul_le_mul_of_nonneg_left hw_cancel (Real.exp_pos (1 / 2 : ℝ)).le
    rw [le_div_iff₀ hI₁]
    nlinarith only [hm2, hexp_inv]
  have hcent_cd : ContDiff ℝ 2 (centredAtomicTest tiltedUnitSpline y c N) :=
    (contDiff_atomicTest hg_cd N y).comp (contDiff_id.add contDiff_const)
  have hcent_cs : HasCompactSupport (centredAtomicTest tiltedUnitSpline y c N) :=
    (hasCompactSupport_atomicTest hg_supp N y).comp_homeomorph (Homeomorph.addRight (Real.log N))
  have hUy_cd : ContDiff ℝ 2 U_y := contDiff_const.mul hcent_cd
  have hUy_cs : HasCompactSupport U_y := hcent_cs.mul_left
  have hUy_le1 : ∀ u, 1 < u → U_y u = 0 := by
    intro u hu1
    dsimp only [U_y, normalizedCentredAtomicTest, centredAtomicTest]
    rw [show atomicTest N y g (u + Real.log N) = 0 from ?_, mul_zero]
    unfold atomicTest
    refine sum_eq_zero fun n hn => ?_
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn1 hnN
    have hnot : u + Real.log N - Real.log n ∉ Set.Icc 0 w := fun hm => by linarith [hm.2, hw1]
    rw [hg_supp _ hnot, mul_zero]
  have hsq_pole := sq_abs (prefixPoleMoment M x) ▸ pow_le_pow_left₀ (abs_nonneg _) hσ_abs 2
  have hexp_sq : (Real.exp (1 / 2 : ℝ) / ∫ u, tiltedUnitSpline u) ^ 2 =
      Real.exp 1 / (∫ u, tiltedUnitSpline u) ^ 2 := by
    rw [div_pow, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [mul_pow, hexp_sq, sq_abs] at hsq_pole
  exact hsq_pole.trans (mul_le_mul_of_nonneg_left
    (sq_exp_neg_half_moment_le_exponential_mass hε hUy_cd.continuous hUy_cs hUy_le1)
    (by positivity))

/-- **All-ratio far Gårding on `(conductorSubspace 1 N)ᗮ`.**
There exists a universal constant `c_W > 0` such that for every critical ratio bound `R_max > 0`,
there exists `B_far > 0` for which eventually in `N`, across all `1 ≤ c` with
`c⁸ ≤ R_max log N`, every pole-orthogonal vector `z ∈ (conductorSubspace 1 N)ᗮ` retains
`(7/8) D_M`, `(g₀ / (8 c⁷)) log N · S₇`, `(c c_W / R_max) W₈(U_y)`, and `(c / (4 I₂)) archForm U_y`
at a prefix cost below `(1 / (16 D)) log N / (1 + log log N)⁵ · P` and a collar `L²` cost
`(c B_far) ∫ U_y²`. -/
theorem exists_all_ratio_far_garding :
    ∃ c_W : ℝ, 0 < c_W ∧
      ∀ {R_max : ℝ}, 0 < R_max →
        ∃ B_far : ℝ, 0 < B_far ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
              ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
                let x := primeHorizonExtension z
                let M := N / linearDefectCutoff c
                let y := atomicTailCoefficients M x
                let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
                (7 / 8 : ℝ) * poleDefect M x +
                  (dyadicTopMassConstant / (8 * c ^ 7)) * Real.log (N : ℝ) *
                    topCollarSeventhMass M N x +
                  (c * c_W / R_max) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
                  (c / (4 * ∫ u, tiltedUnitSpline u ^ 2)) * archForm U_y -
                  ((1 / (16 * explicitConductorCutoffConstant)) * Real.log (N : ℝ) /
                    (1 + Real.log (Real.log (N : ℝ))) ^ 5) *
                    (∑ n ∈ Icc 1 M, x n ^ 2) ≤
                completeWeilEnergy tiltedUnitSpline c N z +
                  (c * B_far) * ∫ u, U_y u ^ 2 := by
  obtain ⟨B_arch, C_err, hB_arch0, hC_err0, harch_g⟩ :=
    exists_top_archForm_dyadic_seventh_reserve_garding
  obtain ⟨C_ψ, c₀, t₀, hCψ, hc₀, ht₀1, hpnt⟩ := exists_vonMangoldtAtom_window_error
  have hg₀ : 0 < dyadicTopMassConstant := dyadicTopMassConstant_pos
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hI₂ : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  have hI₁ : 0 < ∫ u, tiltedUnitSpline u := integral_tiltedUnitSpline_pos
  set I₂ := ∫ u, tiltedUnitSpline u ^ 2
  set C₈ := (256 * Real.exp 2 + 4 + 2 * Real.exp 1) * I₂
  have hC₈ : 0 < C₈ := by positivity
  set c_W0 := dyadicTopMassConstant / (8 * C₈)
  have hc_W0 : 0 < c_W0 := div_pos hg₀ (by positivity)
  refine ⟨c_W0 / 2, div_pos hc_W0 zero_lt_two, ?_⟩
  intro R_max hR
  set C_pole := Real.exp 1 / (∫ u, tiltedUnitSpline u) ^ 2
  have hC_pole : 0 < C_pole := by positivity
  have hκ0 : 0 ≤ splineWindowConstant := splineWindowConstant_nonneg
  set K_win := splineWindowConstant * 8 * Real.exp 2 * C_pole + 1
  have hK_win : 0 < K_win := by positivity
  set ε_pr := I₂ * c_W0 / (4 * R_max)
  have hε_pr : 0 < ε_pr := by positivity
  set ε_win := c_W0 / (4 * R_max * K_win)
  have hε_win : 0 < ε_win := by positivity
  set C_pr := 2 * vonMangoldtThreeHalvesMass
  have hC_pr0 : 0 ≤ C_pr := mul_nonneg (by norm_num) vonMangoldtThreeHalvesMass_nonneg
  set B_pr := C_pr + C_pr ^ 2 * Real.exp 8 / ε_pr
  set B_far := (B_arch / 2 + 2 * Real.pi + (factorialSpanGammaOffset + Real.log 2) / 4 + 2 + B_pr) /
      I₂ + K_win * (4 + 2 / ε_win) + 1
  have hB_far : 0 < B_far := by
    have hG₀ : 0 ≤ factorialSpanGammaOffset := factorialSpanGammaOffset_nonneg
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [B_far, B_pr]; positivity
  refine ⟨B_far, hB_far, ?_⟩
  set K_c : ℝ := (R_max + 1) ^ (1 / 8 : ℝ)
  have hKc1 : 1 ≤ K_c := Real.one_le_rpow (by linarith) (by norm_num)
  have hKc0 : 0 < K_c := zero_lt_one.trans_le hKc1
  set C_β : ℝ := 1 + 36 / c₀ ^ 2 + |Real.log t₀|
  have hC_β : 0 < C_β := by positivity
  set C_tr : ℝ := (1 + 2 * Real.exp 2) *
    (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4))
  have hC_tr0 : 0 ≤ C_tr := by
    have : (1 : ℝ) ≤ 8 * Real.exp 1 * (256 * Real.exp 2 + 4) := by
      nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1),
        Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)]
    have hl1 := Real.log_nonneg this
    have hl4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [C_tr]; positivity
  set C_P0 : ℝ := 1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost +
    (Real.log 4 + 4) + 2 * Real.pi
  have hC_P0 : 0 < C_P0 := by
    have hAsep : 0 ≤ separatedCrossMassCost := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      unfold separatedCrossMassCost; positivity
    have hl4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [C_P0]; positivity
  set θ_P : ℝ := 1 / (16 * explicitConductorCutoffConstant)
  have hθ_P : 0 < θ_P := by positivity
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLN_zero : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hev_L2N : ∀ᶠ N : ℕ in atTop,
      ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)) * Real.log (N : ℝ) ≤ N := by
    set A := (256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)
    have hA : 0 < A := by positivity
    have hev := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / A))
    filter_upwards [hev, eventually_ge_atTop 1] with N hlt hN1
    dsimp only [Function.comp_def] at hlt
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hm := (div_lt_iff₀ hN0).mp hlt
    exact ((le_div_iff₀ hA).mp (by linarith)).trans_eq' (mul_comm _ _)
  have hev_err : ∀ᶠ N : ℕ in atTop,
      C_err * ((R_max + 1) ^ 2 * Real.log (N : ℝ) / N) ≤ dyadicTopMassConstant / (4 * R_max) := by
    by_cases hCerr : 0 < C_err
    · set A := C_err * (R_max + 1) ^ 2
      have hA : 0 < A := by positivity
      have hev := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
        (gt_mem_nhds (div_pos (div_pos hg₀ (by positivity)) hA))
      filter_upwards [hev] with N hlt
      dsimp only [Function.comp_def] at hlt
      have hm := (lt_div_iff₀ hA).mp hlt
      linarith only [hm, (by ring : C_err * ((R_max + 1) ^ 2 * Real.log (N : ℝ) / N) =
        (Real.log (N : ℝ) / N) * A)]
    · have h0 : C_err = 0 := le_antisymm (not_lt.mp hCerr) hC_err0
      filter_upwards with N; rw [h0]; simp only [zero_mul]; positivity
  filter_upwards [
    hev_L2N, hev_err,
    hLlim.eventually (eventually_ge_atTop (max 4 K_c)),
    hLlim.eventually ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 16)).eventually_ge_atTop
      (factorialSpanGammaOffset + Real.log (4 * C_ψ + 1) + 2)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow (by norm_num : (0 : ℝ) < 3 / 16) 1 1),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (1 / 8 : ℝ) < 1) 5 (4 * C_P0 * K_c / θ_P)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (15 / 16 : ℝ) < 1) 6 (4 * 68 * C_tr * K_c / θ_P)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (7 / 8 : ℝ) < 1) 5
      (4 * splineWindowConstant * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
        (C_β + 1 + (Real.log 4 + 4)) ^ 2 * K_c / θ_P)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (3 / 8 : ℝ) < 1) 1
      (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset + C_β)),
    eventually_ge_atTop 3] with
      N hL2N_b herr_b hL_ge hL316_C hlogL_316 hP_a hP_b hP_c hexp_b hN3
  dsimp only [Function.comp_def] at hL316_C
  intro c hc1 hc8 z hz
  set L := Real.log (N : ℝ) with hL_eq
  set ℓ := 1 + Real.log L with hℓ_eq
  have hL4 : 4 ≤ L := (le_max_left _ _).trans hL_ge
  have hKc_L : K_c ≤ L := (le_max_right _ _).trans hL_ge
  have hL1 : 1 ≤ L := by linarith only [hL4]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ_eq]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ) := by
    have hp : c ^ 8 ≤ (K_c * L ^ (1 / 8 : ℝ)) ^ 8 := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le,
        ← Real.rpow_natCast ((R_max + 1) ^ _), ← Real.rpow_mul (by positivity : 0 ≤ R_max + 1),
        show (1 / 8 : ℝ) * (8 : ℕ) = 1 by norm_num, Real.rpow_one, Real.rpow_one]
      nlinarith only [hc8, hL0]
    exact le_of_pow_le_pow_left₀ (by norm_num : 8 ≠ 0) (by positivity) hp
  have hcL : c ≤ L := by
    have hL8_78 : L ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
    have hKc_78 : K_c ≤ L ^ (7 / 8 : ℝ) := by
      have hp : K_c ^ 8 ≤ (L ^ (7 / 8 : ℝ)) ^ 8 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
          show (7 / 8 : ℝ) * (8 : ℕ) = 7 by norm_num, Real.rpow_natCast]
        have h1 : K_c ^ 8 = R_max + 1 := by
          dsimp only [K_c]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ R_max + 1)]
          norm_num [Real.rpow_one]
        have h2 : R_max + 1 ≤ L := by
          have : K_c ≤ K_c ^ 8 := le_self_pow₀ hKc1 (by norm_num)
          -- Wait: K_c ≤ L gives K_c^8 ≤ L^8, wait:
          linarith only [h1]
        sorry
      sorry
    sorry
  sorry

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
