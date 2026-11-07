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
open scoped Classical BigOperators RealInnerProductSpace Matrix ComplexConjugate

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticLorentzianGeometry CriticalScaleArithmeticRigidity ArithmeticElectrostatics
  ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  ArithmeticEffectivityTheory ArithmeticPositivityTheory

/-! ### 1. Window-localized collar Gårding and `L²` concentration -/

private lemma integral_sq_eq_Iic_add_Ioc {A : ℝ} (_hA : 0 ≤ A) {U : ℝ → ℝ}
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
  calc (∫ u, U u ^ 2)
      = ∫ u, ((Set.Iic (-A)).indicator (fun v => U v ^ 2) u +
          (Set.Ioc (-A) 1).indicator (fun v => U v ^ 2) u) := congrArg (fun f => ∫ u, f u) hpt
    _ = (∫ u, (Set.Iic (-A)).indicator (fun v => U v ^ 2) u) +
          ∫ u in Set.Ioc (-A) 1, U u ^ 2 := by
        rw [integral_add hi_le hi_oc, MeasureTheory.integral_indicator measurableSet_Ioc]

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
  change (c_κ / R_max) * topCollarSeventhMass M N x +
      (c_a / R_max) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤
    weilQuad U_y + C_B * (R_max + 1) * ∫ u, U_y u ^ 2 at hg_x
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
  filter_upwards [hpol hR, hev_cN, eventually_ge_atTop 3] with N hg hcN_b hN3 c hc1 hc8 x
  dsimp only
  intro hle0
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
  change (c_κ / R_max) * topCollarSeventhMass M N x +
      (c_a / R_max) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤
    weilQuad U_y + C_B * (R_max + 1) * ∫ u, U_y u ^ 2 at hg_x
  have hS7_0 : 0 ≤ (c_κ / R_max) * topCollarSeventhMass M N x :=
    mul_nonneg (div_nonneg hcκ.le hR.le) (topCollarSeventhMass_nonneg M N x)
  change (1 / 2 : ℝ) * (∫ u, U_y u ^ 2) ≤ ∫ u in Set.Ioc (-A_R) 1, U_y u ^ 2
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
        rwa [← Real.rpow_natCast (Real.log (N : ℝ) ^ (1 / 8 : ℝ)), ← Real.rpow_mul hL0.le,
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
      have hnat : N ≤ 2 * S_R * M_R := by
        calc N ≤ S_R * (M_R + 1) := hN_lt.le
          _ = S_R * M_R + S_R * 1 := by ring
          _ ≤ S_R * M_R + S_R * M_R := Nat.add_le_add_left (Nat.mul_le_mul_left S_R hMR1) _
          _ = 2 * S_R * M_R := by ring
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
        ((div_le_iff₀ hK₁_pos).mp hSR_ge).trans_eq (mul_comm _ _)
      have hp := pow_le_pow_left₀ (by positivity) h1 8
      rw [← Real.rpow_natCast ((R_max + 1) ^ (1 / 8 : ℝ)),
        ← Real.rpow_mul (by positivity : 0 ≤ R_max + 1),
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
                mul_le_mul_of_nonneg_right hR_SR8 (Real.log_nonneg (by exact_mod_cast hN1))
            _ = K₁ ^ 8 * Real.log (N : ℝ) * (S_R : ℝ) ^ 8 := by ring
        have h4 : K₁ ^ 8 * Real.log (N : ℝ) ≤ (2 * K₁) ^ 8 * Real.log (M_R : ℝ) := by
          have hm := mul_le_mul_of_nonneg_left hlogM_lb (by positivity : 0 ≤ K₁ ^ 8)
          have h256 : 2 * K₁ ^ 8 ≤ (2 * K₁) ^ 8 := by
            rw [mul_pow]; nlinarith [pow_nonneg hK₁_pos.le 8]
          nlinarith only [hm, h256, hlogM_pos]
        have h5 : (2 * K₁) ^ 8 * Real.log (M_R : ℝ) =
            (2 * K₁ * Real.log (M_R : ℝ) ^ (1 / 8 : ℝ)) ^ 8 := by
          rw [mul_pow (2 * K₁), ← Real.rpow_natCast (Real.log (M_R : ℝ) ^ (1 / 8 : ℝ)),
            ← Real.rpow_mul hlogM_pos.le,
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
      funext u
      unfold atomicTest
      refine sum_congr rfl fun n hn => ?_
      exact congrArg (· * atomDilate tiltedUnitSpline (c / N) (u - Real.log n))
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
      have hMR_le_N : M_R ≤ N := Nat.div_le_self N S_R
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
            rw [div_mul_eq_div_div_swap, ← Real.exp_sub, one_div_mul_eq_div]
            congr 2; ring
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
        congr 2; ring
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
              congr 2; ring
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
    have hint_sum : 0 ≤ ∫ u, ((t * t) * (U u ^ 2 * W u) + 2 * t * (U u * Real.exp (-(u / 2))) + Φ u) :=
      integral_nonneg hpt
    have hi1 : Integrable (fun u => (t * t) * (U u ^ 2 * W u)) := hiUW.const_mul (t * t)
    have hi2 : Integrable (fun u => 2 * t * (U u * Real.exp (-(u / 2)))) := hiUE.const_mul (2 * t)
    rw [integral_add (f := fun u => (t * t) * (U u ^ 2 * W u) + 2 * t * (U u * Real.exp (-(u / 2))))
        (g := Φ) (hi1.add hi2) hiΦ,
      integral_add (f := fun u => (t * t) * (U u ^ 2 * W u))
        (g := fun u => 2 * t * (U u * Real.exp (-(u / 2)))) hi1 hi2,
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
    have hneg : IntegrableOn (fun v : ℝ => Real.exp (-(1 : ℝ) * v)) (Set.Ioi 0) :=
      integrableOn_exp_mul_Ioi (by norm_num : -(1 : ℝ) < 0) 0
    have hcomp : Integrable (fun v : ℝ =>
        (Set.Ioi (0 : ℝ)).indicator (fun x => Real.exp (-(1 : ℝ) * x)) (-v)) :=
      (hneg.integrable_indicator measurableSet_Ioi).comp_neg
    refine hcomp.congr ?_
    have hsub : {v : ℝ | ¬((Set.Ioi (0 : ℝ)).indicator (fun x => Real.exp (-(1 : ℝ) * x)) (-v) =
        (Set.Iic (0 : ℝ)).indicator (fun x => Real.exp x) v)} ⊆ {(0 : ℝ)} := by
      intro v hv
      by_contra hne
      apply hv
      rcases lt_trichotomy v 0 with hlt | rfl | hgt
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr (neg_pos.mpr hlt)),
          Set.indicator_of_mem (Set.mem_Iic.mpr hlt.le)]; congr 1; ring
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
                Set.indicator_of_mem (Set.mem_Ioi.mpr hgt)]; congr 1; ring
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
    have hint_sum : 0 ≤ ∫ u, ((t * t) * U u ^ 2 + 2 * t * (U u * Real.exp (u / 2)) + Φ u) :=
      integral_nonneg hpt
    have hi1 : Integrable (fun u => (t * t) * U u ^ 2) := hi0.const_mul (t * t)
    have hi2 : Integrable (fun u => 2 * t * (U u * Real.exp (u / 2))) := hiUE.const_mul (2 * t)
    rw [integral_add (f := fun u => (t * t) * U u ^ 2 + 2 * t * (U u * Real.exp (u / 2)))
        (g := Φ) (hi1.add hi2) hiΦ,
      integral_add (f := fun u => (t * t) * U u ^ 2)
        (g := fun u => 2 * t * (U u * Real.exp (u / 2))) hi1 hi2,
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
  have hpole_split : ArithmeticLorentzianGeometry.poleFunctional N x =
      prefixPoleMoment M x + ArithmeticLorentzianGeometry.poleFunctional N y := by
    change (∑ n ∈ Icc 1 N, x n / Real.sqrt n) =
      (∑ m ∈ Icc 1 M, x m / Real.sqrt m) + ∑ n ∈ Icc 1 N, y n / Real.sqrt n
    have hdisj : Icc 1 N = Icc 1 M ∪ Ioc M N := by
      ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    have hd : Disjoint (Icc 1 M) (Ioc M N) := disjoint_left.mpr fun n h1 h2 => by
      simp only [mem_Icc, mem_Ioc] at h1 h2; omega
    rw [hdisj, sum_union hd, sum_union hd]
    congr 1
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
          Real.exp_add, Real.exp_neg (Real.log N / 2)]
        have hsq : Real.exp (Real.log N / 2) = Real.sqrt N := by
          apply (sq_eq_sq₀ (Real.exp_pos _).le (Real.sqrt_nonneg _)).mp
          rw [← Real.exp_nat_mul, Real.sq_sqrt hN0.le]
          have : (2 : ℕ) * (Real.log (N : ℝ) / 2) = Real.log (N : ℝ) := by push_cast; ring
          rw [this, Real.exp_log hN0]
        rw [hsq, one_div]
      dsimp only [U_y, normalizedCentredAtomicTest, centredAtomicTest, w, g]
      rw [hexp]
      have hsqN : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
      field_simp [hc0.ne', hN0.ne', hsqN]
      rw [Real.sq_sqrt hN0.le]; ring
    rw [hfn, integral_const_mul]
  have hg_lb : Real.exp (-(1 / 2 : ℝ)) * w * (∫ u, tiltedUnitSpline u) ≤
      ∫ t, g t * Real.exp (-(t / 2)) := by
    have hgi : Integrable g := hg_cd.continuous.integrable_of_hasCompactSupport hg_cs
    have hge : Integrable (fun t => g t * Real.exp (-(t / 2))) :=
      (hg_cd.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hg_cs.mul_right
    have hint_g : ∫ t, g t = w * ∫ u, tiltedUnitSpline u := by
      have h := Measure.integral_comp_div (fun u => tiltedUnitSpline u) w
      dsimp only [g, atomDilate]
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
    · dsimp only [g]; rw [hg_supp t ht, mul_zero, zero_mul]
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
    have hw_cancel : (Real.exp (-(1 / 2 : ℝ)) * ∫ u, tiltedUnitSpline u) * |prefixPoleMoment M x| ≤
        |∫ v, U_y v * Real.exp (-(v / 2))| := by
      refine le_of_mul_le_mul_left ?_ hw0
      linarith only [hm]
    have hexp_inv : Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hm2 : |prefixPoleMoment M x| * ∫ u, tiltedUnitSpline u ≤
        Real.exp (1 / 2 : ℝ) * |∫ v, U_y v * Real.exp (-(v / 2))| := by
      calc |prefixPoleMoment M x| * ∫ u, tiltedUnitSpline u
          = (Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ))) *
              (|prefixPoleMoment M x| * ∫ u, tiltedUnitSpline u) := by rw [hexp_inv, one_mul]
        _ = Real.exp (1 / 2 : ℝ) *
              ((Real.exp (-(1 / 2 : ℝ)) * ∫ u, tiltedUnitSpline u) * |prefixPoleMoment M x|) := by ring
        _ ≤ Real.exp (1 / 2 : ℝ) * |∫ v, U_y v * Real.exp (-(v / 2))| :=
            mul_le_mul_of_nonneg_left hw_cancel (Real.exp_pos _).le
    rwa [div_mul_eq_mul_div, le_div_iff₀ hI₁]
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
    dsimp only [g]; rw [hg_supp _ hnot, mul_zero]
  have hsq_pole := sq_abs (prefixPoleMoment M x) ▸ pow_le_pow_left₀ (abs_nonneg _) hσ_abs 2
  have hexp_sq : (Real.exp (1 / 2 : ℝ) / ∫ u, tiltedUnitSpline u) ^ 2 =
      Real.exp 1 / (∫ u, tiltedUnitSpline u) ^ 2 := by
    rw [div_pow, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [mul_pow, hexp_sq, sq_abs] at hsq_pole
  exact hsq_pole.trans (mul_le_mul_of_nonneg_left
    (sq_exp_neg_half_moment_le_exponential_mass hε hUy_cd.continuous hUy_cs hUy_le1)
    (by positivity))

private lemma normalizedCentredAtomicTest_scaling {N : ℕ} {c : ℝ} (hc0 : 0 < c) (hN1 : 1 ≤ N)
    (y : ℕ → ℝ) :
    let w := c / (N : ℝ)
    let g := atomDilate tiltedUnitSpline w
    let I₂ := ∫ u, tiltedUnitSpline u ^ 2
    let G := w * I₂
    let f_y := atomicTest N y g
    let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
    ContDiff ℝ 2 U_y ∧ HasCompactSupport U_y ∧ (∀ u, w < u → U_y u = 0) ∧
      (∫ u, f_y u ^ 2 = G * ((c / I₂) * ∫ u, U_y u ^ 2)) ∧
      archForm f_y = G * ((c / I₂) * archForm U_y) ∧
      primeSum f_y = G * ((c / I₂) * primeSum U_y) := by
  intro w g I₂ G f_y U_y
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < w := div_pos hc0 hN0
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  have hg_cd : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hg_supp := tiltedUnitSpline_atom_support hw0
  have hfy_cd : ContDiff ℝ 2 f_y := contDiff_atomicTest hg_cd N y
  have hfy_cs : HasCompactSupport f_y := hasCompactSupport_atomicTest hg_supp N y
  have hcent_cd : ContDiff ℝ 2 (centredAtomicTest tiltedUnitSpline y c N) :=
    contDiff_centredAtomicTest contDiff_tiltedUnitSpline y c N
  have hcent_cs : HasCompactSupport (centredAtomicTest tiltedUnitSpline y c N) :=
    hfy_cs.comp_homeomorph (Homeomorph.addRight (Real.log N))
  have hUy_cd : ContDiff ℝ 2 U_y := contDiff_const.mul hcent_cd
  have hUy_cs : HasCompactSupport U_y := hcent_cs.mul_left
  have hUy_w : ∀ u, w < u → U_y u = 0 := by
    intro u hu
    dsimp only [U_y, normalizedCentredAtomicTest, centredAtomicTest]
    rw [show atomicTest N y g (u + Real.log N) = 0 from ?_, mul_zero]
    unfold atomicTest
    refine sum_eq_zero fun n hn => ?_
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn1 hnN
    have hnot : u + Real.log N - Real.log n ∉ Set.Icc 0 w := fun hm => by linarith [hm.2]
    dsimp only [g]; rw [hg_supp _ hnot, mul_zero]
  have hGc_id : G * (c / I₂) = c ^ 2 / (N : ℝ) := by
    dsimp only [G, w]; field_simp [hN0.ne', hI₂.ne']
  have hfy_L2 : ∫ u, f_y u ^ 2 = G * ((c / I₂) * ∫ u, U_y u ^ 2) := by
    have hU : ∫ u, U_y u ^ 2 = ((N : ℝ) / c ^ 2) * ∫ u, f_y u ^ 2 := by
      dsimp only [U_y, normalizedCentredAtomicTest]
      simp_rw [mul_pow, div_pow, Real.sq_sqrt hN0.le]
      rw [integral_const_mul]
      exact congrArg (((N : ℝ) / c ^ 2) * ·)
        (integral_add_right_eq_self (fun u => f_y u ^ 2) (Real.log N))
    rw [hU, ← mul_assoc, hGc_id]
    field_simp [hc0.ne', hN0.ne']
  have hfy_arch : archForm f_y = G * ((c / I₂) * archForm U_y) := by
    have hcent_arch : archForm (centredAtomicTest tiltedUnitSpline y c N) = archForm f_y := by
      rw [archForm_eq_levyEnergy hcent_cd hcent_cs, archForm_eq_levyEnergy hfy_cd hfy_cs,
        show (∫ u, centredAtomicTest tiltedUnitSpline y c N u ^ 2) = ∫ u, f_y u ^ 2 from
          integral_add_right_eq_self (fun u => f_y u ^ 2) (Real.log N)]
      congr 1
      unfold levyEnergy centredAtomicTest
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      congr 1
      have hfn : (fun u => (f_y (u + Real.log N) - f_y (u + t + Real.log N)) ^ 2) =
          fun u => (fun v => (f_y v - f_y (v + t)) ^ 2) (u + Real.log N) :=
        funext fun u => by dsimp only; congr 2; ring
      rw [hfn]
      exact integral_add_right_eq_self (fun v => (f_y v - f_y (v + t)) ^ 2) (Real.log N)
    have hU : archForm U_y = ((N : ℝ) / c ^ 2) * archForm f_y := by
      have hfn : U_y = fun u => (Real.sqrt N / c) * centredAtomicTest tiltedUnitSpline y c N u := rfl
      rw [hfn, archForm_const_mul hcent_cd hcent_cs, div_pow, Real.sq_sqrt hN0.le, hcent_arch]
    rw [hU, ← mul_assoc, hGc_id]
    field_simp [hc0.ne', hN0.ne']
  have hfy_prime : primeSum f_y = G * ((c / I₂) * primeSum U_y) := by
    have hU : primeSum U_y = ((N : ℝ) / c ^ 2) * primeSum f_y := by
      have hfn : U_y = fun u => (Real.sqrt N / c) * centredAtomicTest tiltedUnitSpline y c N u := rfl
      rw [hfn, primeSum_const_mul, div_pow, Real.sq_sqrt hN0.le]
      exact congrArg (((N : ℝ) / c ^ 2) * ·) (primeSum_comp_add_right f_y (Real.log N))
    rw [hU, ← mul_assoc, hGc_id]
    field_simp [hc0.ne', hN0.ne']
  exact ⟨hUy_cd, hUy_cs, hUy_w, hfy_L2, hfy_arch, hfy_prime⟩

private lemma far_garding_translate_factor_le {N : ℕ} {c K_c θ_P T h : ℝ}
    (hc1 : 1 ≤ c) (h2LN : 2 * linearDefectCutoff c ≤ N) (hN1 : 1 ≤ N)
    (hM1 : 1 ≤ N / linearDefectCutoff c) (hMN : N / linearDefectCutoff c ≤ N)
    (hKc0 : 0 < K_c) (hθ_P : 0 < θ_P)
    (hL1 : 1 ≤ Real.log (N : ℝ)) (hc_up : c ≤ K_c * Real.log (N : ℝ) ^ (1 / 8 : ℝ))
    (hcL : c ≤ Real.log (N : ℝ)) (hTh : T * h = 1 / Real.log (N : ℝ))
    (hP_b :
      (4 * 68 *
        ((1 + 2 * Real.exp 2) *
          (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4))) *
        K_c / θ_P) *
        Real.log (N : ℝ) ^ (15 / 16 : ℝ) * (1 + Real.log (Real.log (N : ℝ))) ^ 6 ≤
        Real.log (N : ℝ)) :
    let L := Real.log (N : ℝ)
    let ℓ := 1 + Real.log L
    let w := c / (N : ℝ)
    let M := N / linearDefectCutoff c
    let Bn := ⌊(N : ℝ) * Real.exp w⌋₊
    let lam := (1 / 4 : ℝ) * L ^ (3 / 16 : ℝ)
    ((T * h) ^ 2 + lam⁻¹ * 4) *
      ((1 + 2 * Real.exp 1 * (w * Bn)) *
        (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) ≤
      (θ_P / 4) * (L / ℓ ^ 5) := by
  intro L ℓ w M Bn lam
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hℓ0 : 0 < ℓ := by dsimp only [ℓ]; linarith [Real.log_nonneg hL1]
  have hℓ5_pos : 0 < ℓ ^ 5 := pow_pos hℓ0 5
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < w := div_pos hc0 hN0
  set C_tr : ℝ := (1 + 2 * Real.exp 2) *
    (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4))
  have hC_tr0 : 0 ≤ C_tr := by
    have : (1 : ℝ) ≤ 8 * Real.exp 1 * (256 * Real.exp 2 + 4) := by
      nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1),
        Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)]
    have hl1 := Real.log_nonneg this
    have hl4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [C_tr]; positivity
  have hΦ := translate_factor_le hc1 h2LN
  have h1L : 1 + L ≤ 2 * L := by linarith only [hL1]
  have h1c : 1 + Real.log c ≤ ℓ := by dsimp only [ℓ]; linarith [Real.log_le_log hc0 hcL]
  have hΦ_ub : (1 + 2 * Real.exp 1 * (w * Bn)) *
      (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4))) ≤
      2 * C_tr * K_c * L ^ (9 / 8 : ℝ) * ℓ := by
    have h1 : C_tr * c * (1 + L) * (1 + Real.log c) ≤
        C_tr * (K_c * L ^ (1 / 8 : ℝ)) * (2 * L) * ℓ := by
      have hm1 := mul_le_mul hc_up h1L (by positivity) (by positivity)
      have hm2 := mul_le_mul hm1 h1c (by linarith [Real.log_nonneg hc1]) (by positivity)
      calc C_tr * c * (1 + L) * (1 + Real.log c)
          = C_tr * (c * (1 + L) * (1 + Real.log c)) := by ring
        _ ≤ C_tr * (K_c * L ^ (1 / 8 : ℝ) * (2 * L) * ℓ) := mul_le_mul_of_nonneg_left hm2 hC_tr0
        _ = C_tr * (K_c * L ^ (1 / 8 : ℝ)) * (2 * L) * ℓ := by ring
    have hL98 : L ^ (1 / 8 : ℝ) * L = L ^ (9 / 8 : ℝ) := by
      calc L ^ (1 / 8 : ℝ) * L = L ^ (1 / 8 : ℝ) * L ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = L ^ (9 / 8 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
    exact hΦ.trans (h1.trans_eq (by rw [← hL98]; ring))
  have hcoef_ub : (T * h) ^ 2 + lam⁻¹ * 4 ≤ 17 / L ^ (3 / 16 : ℝ) := by
    have hTh' : T * h = 1 / L := hTh
    rw [hTh']
    have hlam_inv : lam⁻¹ * 4 = 16 / L ^ (3 / 16 : ℝ) := by
      dsimp only [lam]; field_simp [(Real.rpow_pos_of_pos hL0 _).ne']; norm_num
    have h1L2 : (1 / L) ^ 2 ≤ 1 / L ^ (3 / 16 : ℝ) := by
      rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
      calc L ^ (3 / 16 : ℝ) ≤ L ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = L ^ 2 := Real.rpow_two L
    have h17 : 1 / L ^ (3 / 16 : ℝ) + 16 / L ^ (3 / 16 : ℝ) = 17 / L ^ (3 / 16 : ℝ) := by ring
    linarith only [hlam_inv, h1L2, h17]
  have hΦ0 : 0 ≤ (1 + 2 * Real.exp 1 * (w * Bn)) *
      (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4))) := by
    have hBn1 : (1 : ℝ) ≤ Bn := by
      have h1 : ((1 : ℕ) : ℝ) ≤ N * Real.exp w := by
        push_cast
        exact (by exact_mod_cast hN1 : (1 : ℝ) ≤ N).trans
          (le_mul_of_one_le_right hN0.le (Real.one_le_exp hw0.le))
      exact_mod_cast Nat.le_floor h1
    have hrat : 1 ≤ 2 * (Bn : ℝ) / ((M : ℝ) / 2) := by
      have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
      rw [le_div_iff₀ (by linarith)]
      have hMN_R : (M : ℝ) ≤ N := by exact_mod_cast hMN
      have hNBn : (N : ℝ) ≤ Bn := by
        exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hN0.le (Real.one_le_exp hw0.le))
      linarith
    have hl1 := Real.log_nonneg hBn1
    have hl2 := Real.log_nonneg hrat
    have hl4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    positivity
  have hm := mul_le_mul hcoef_ub hΦ_ub hΦ0 (by positivity)
  have hsplit : L ^ (9 / 8 : ℝ) / L ^ (3 / 16 : ℝ) = L ^ (15 / 16 : ℝ) := by
    rw [← Real.rpow_sub hL0]; norm_num
  have h34 : (17 / L ^ (3 / 16 : ℝ)) * (2 * C_tr * K_c * L ^ (9 / 8 : ℝ) * ℓ) ≤
      68 * C_tr * K_c * L ^ (15 / 16 : ℝ) * ℓ := by
    have hid : (17 / L ^ (3 / 16 : ℝ)) * (2 * C_tr * K_c * L ^ (9 / 8 : ℝ) * ℓ) =
        34 * C_tr * K_c * (L ^ (9 / 8 : ℝ) / L ^ (3 / 16 : ℝ)) * ℓ := by ring
    rw [hid, hsplit]
    have hnn : 0 ≤ C_tr * K_c * L ^ (15 / 16 : ℝ) * ℓ := by positivity
    linarith only [hnn]
  have hpb : 68 * C_tr * K_c * L ^ (15 / 16 : ℝ) * ℓ ≤ (θ_P / 4) * (L / ℓ ^ 5) := by
    rw [mul_div_assoc', le_div_iff₀ hℓ5_pos]
    have hm' := mul_le_mul_of_nonneg_left hP_b (by positivity : 0 ≤ θ_P / 4)
    have hid : (θ_P / 4) * ((4 * 68 * C_tr * K_c / θ_P) * L ^ (15 / 16 : ℝ) * ℓ ^ 6) =
        68 * C_tr * K_c * L ^ (15 / 16 : ℝ) * ℓ * ℓ ^ 5 := by
      field_simp [hθ_P.ne']
    linarith only [hm', hid]
  exact hm.trans (h34.trans hpb)

private lemma far_garding_window_beta_psi_le {N : ℕ} {c C_ψ c₀ t₀ h : ℝ}
    (hCψ : 0 ≤ C_ψ) (hc₀ : 0 < c₀) (hN1 : 1 ≤ N)
    (hL1 : 1 ≤ Real.log (N : ℝ)) (hcL : c ≤ Real.log (N : ℝ))
    (hh_def : h = 1 / (Real.exp (factorialSpanGammaOffset + Real.log (N : ℝ) ^ (3 / 16 : ℝ)) *
      Real.log (N : ℝ)))
    (hL316_C : factorialSpanGammaOffset + Real.log (4 * C_ψ + 1) + 4 ≤
      Real.log (N : ℝ) ^ (3 / 16 : ℝ))
    (hlogL_ub : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) ^ (3 / 16 : ℝ))
    (hexp_b : (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset +
      (1 + 36 / c₀ ^ 2 + |Real.log t₀|)) * Real.log (N : ℝ) ^ (3 / 8 : ℝ) ≤ Real.log (N : ℝ)) :
    let L := Real.log (N : ℝ)
    let C_β := 1 + 36 / c₀ ^ 2 + |Real.log t₀|
    let ν := (2 * Real.log (1 / h) + Real.log (4 * C_ψ + 1)) / c₀
    let β := 1 + ν ^ 2 + |Real.log t₀|
    let ΨK := (Real.log 4 + 4) * (2 * Real.exp β)
    β ≤ C_β * L ^ (3 / 8 : ℝ) ∧ ((c / (N : ℝ)) / h) * ΨK ≤ 1 := by
  intro L C_β ν β ΨK
  change 1 ≤ L at hL1
  change c ≤ L at hcL
  change h = 1 / (Real.exp (factorialSpanGammaOffset + L ^ (3 / 16 : ℝ)) * L) at hh_def
  change factorialSpanGammaOffset + Real.log (4 * C_ψ + 1) + 4 ≤ L ^ (3 / 16 : ℝ) at hL316_C
  change Real.log L ≤ L ^ (3 / 16 : ℝ) at hlogL_ub
  change (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset + C_β) *
    L ^ (3 / 8 : ℝ) ≤ L at hexp_b
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set G₀ := factorialSpanGammaOffset
  have hG₀ : 0 ≤ G₀ := factorialSpanGammaOffset_nonneg
  set T := Real.exp (G₀ + L ^ (3 / 16 : ℝ))
  have hT0 : 0 < T := Real.exp_pos _
  have hT1 : 1 ≤ T := Real.one_le_exp (add_nonneg hG₀ (Real.rpow_nonneg hL0.le _))
  have hh0 : 0 < h := by rw [hh_def]; exact div_pos zero_lt_one (mul_pos hT0 hL0)
  have hh1 : h ≤ 1 := by
    rw [hh_def]
    exact (div_le_one (mul_pos hT0 hL0)).mpr (one_le_mul_of_one_le_of_one_le hT1 hL1)
  have h1h : Real.log (1 / h) = G₀ + L ^ (3 / 16 : ℝ) + Real.log L := by
    rw [hh_def, one_div_one_div, Real.log_mul hT0.ne' hL0.ne', Real.log_exp]
  have hβ_ub : β ≤ C_β * L ^ (3 / 8 : ℝ) := by
    have hl2 := Real.log_nonneg (show 1 ≤ 4 * C_ψ + 1 by linarith)
    have hnum : 2 * Real.log (1 / h) + Real.log (4 * C_ψ + 1) ≤ 6 * L ^ (3 / 16 : ℝ) := by
      rw [h1h]; linarith only [hL316_C, hlogL_ub, hl2]
    have hnum0 : 0 ≤ 2 * Real.log (1 / h) + Real.log (4 * C_ψ + 1) := by
      have hl1 := Real.log_nonneg (show 1 ≤ 1 / h from (le_div_iff₀ hh0).mpr (by linarith))
      linarith
    have hν_ub : ν ≤ (6 / c₀) * L ^ (3 / 16 : ℝ) := by
      dsimp only [ν]
      calc (2 * Real.log (1 / h) + Real.log (4 * C_ψ + 1)) / c₀
          ≤ (6 * L ^ (3 / 16 : ℝ)) / c₀ := div_le_div_of_nonneg_right hnum hc₀.le
        _ = (6 / c₀) * L ^ (3 / 16 : ℝ) := by ring
    have hν0 : 0 ≤ ν := div_nonneg hnum0 hc₀.le
    have hν2 : ν ^ 2 ≤ (36 / c₀ ^ 2) * L ^ (3 / 8 : ℝ) := by
      have hp := pow_le_pow_left₀ hν0 hν_ub 2
      rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le,
        show (3 / 16 : ℝ) * (2 : ℕ) = 3 / 8 by norm_num] at hp
      exact hp.trans_eq (by ring)
    have hL38_1 : 1 ≤ L ^ (3 / 8 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    dsimp only [β, C_β]
    nlinarith only [hν2, hL38_1, abs_nonneg (Real.log t₀)]
  refine ⟨hβ_ub, ?_⟩
  have hC₄ : 1 ≤ Real.log 4 + 4 := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hid : ((c / (N : ℝ)) / h) * ΨK =
      2 * (Real.log 4 + 4) * c * L * Real.exp (G₀ + L ^ (3 / 16 : ℝ) + β) / N := by
    rw [Real.exp_add (G₀ + L ^ (3 / 16 : ℝ)) β]
    dsimp only [ΨK, G₀, T] at hh_def ⊢
    rw [hh_def]
    field_simp [hN0.ne', hL0.ne']
  rw [hid, div_le_one hN0]
  have hcL_pos : 0 < 2 * (Real.log 4 + 4) := by linarith only [hC₄]
  have h1 : 2 * (Real.log 4 + 4) * c * L ≤
      Real.exp (Real.log (2 * (Real.log 4 + 4)) + 2 * Real.log L) := by
    rw [Real.exp_add, Real.exp_log hcL_pos, show 2 * Real.log L = Real.log L + Real.log L by ring,
      Real.exp_add, Real.exp_log hL0]
    have hm : c * L ≤ L * L := mul_le_mul_of_nonneg_right hcL hL0.le
    nlinarith only [hm, hcL_pos]
  have hL38_1 : 1 ≤ L ^ (3 / 8 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hL316_38 : L ^ (3 / 16 : ℝ) ≤ L ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hexp_le : Real.log (2 * (Real.log 4 + 4)) + 2 * Real.log L +
      (G₀ + L ^ (3 / 16 : ℝ) + β) ≤ L := by
    have habs := le_abs_self (Real.log (2 * (Real.log 4 + 4)))
    have hlogL_38 : Real.log L ≤ L ^ (3 / 8 : ℝ) := hlogL_ub.trans hL316_38
    have habs1 := le_mul_of_one_le_right (abs_nonneg (Real.log (2 * (Real.log 4 + 4)))) hL38_1
    have hG₀1 := le_mul_of_one_le_right hG₀ hL38_1
    change (|Real.log (2 * (Real.log 4 + 4))| + 4 + G₀ + C_β) * L ^ (3 / 8 : ℝ) ≤ L at hexp_b
    have hexp_expand :
        (|Real.log (2 * (Real.log 4 + 4))| + 4 + G₀ + C_β) *
          L ^ (3 / 8 : ℝ) =
        |Real.log (2 * (Real.log 4 + 4))| * L ^ (3 / 8 : ℝ) +
          4 * L ^ (3 / 8 : ℝ) + G₀ * L ^ (3 / 8 : ℝ) + C_β * L ^ (3 / 8 : ℝ) := by ring
    linarith only [hexp_b, hexp_expand, habs, habs1, hlogL_38, hL316_38, hL38_1, hG₀1, hβ_ub]
  calc 2 * (Real.log 4 + 4) * c * L * Real.exp (G₀ + L ^ (3 / 16 : ℝ) + β)
      ≤ Real.exp (Real.log (2 * (Real.log 4 + 4)) + 2 * Real.log L) *
          Real.exp (G₀ + L ^ (3 / 16 : ℝ) + β) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (Real.log (2 * (Real.log 4 + 4)) + 2 * Real.log L +
          (G₀ + L ^ (3 / 16 : ℝ) + β)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp L := Real.exp_le_exp.mpr hexp_le
    _ = N := Real.exp_log hN0

private lemma far_garding_windowSum_le {N K' : ℕ} {c R_max K_c θ_P c_W0 C_ψ c₀ t₀ h : ℝ}
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hR : 0 < R_max) (hCψ : 0 ≤ C_ψ) (hc₀ : 0 < c₀) (hc_W0 : 0 < c_W0)
    (hθ_P : 0 < θ_P) (hKc0 : 0 < K_c)
    (hN2 : 2 ≤ N) (hc1 : 1 ≤ c) (hcN : c ≤ N) (hL1 : 1 ≤ Real.log (N : ℝ))
    (hc_up : c ≤ K_c * Real.log (N : ℝ) ^ (1 / 8 : ℝ)) (hcL : c ≤ Real.log (N : ℝ))
    (hM1 : 1 ≤ N / linearDefectCutoff c) (hMN : N / linearDefectCutoff c ≤ N)
    (hz : z ∈ (conductorSubspace 1 N)ᗮ)
    (hh_def : h = 1 / (Real.exp (factorialSpanGammaOffset + Real.log (N : ℝ) ^ (3 / 16 : ℝ)) *
      Real.log (N : ℝ)))
    (hK'1 : 1 ≤ K')
    (hpntK' : 4 * C_ψ * pntRate c₀ K' ≤ h ^ 2)
    (hlogK' : Real.log K' ≤ (1 + ((2 * Real.log (1 / h) + Real.log (4 * C_ψ + 1)) / c₀) ^ 2 +
      |Real.log t₀|) + 1)
    (hK'le : (K' : ℝ) ≤ 2 * Real.exp (1 +
      ((2 * Real.log (1 / h) + Real.log (4 * C_ψ + 1)) / c₀) ^ 2 + |Real.log t₀|))
    (hL316_C : factorialSpanGammaOffset + Real.log (4 * C_ψ + 1) + 4 ≤
      Real.log (N : ℝ) ^ (3 / 16 : ℝ))
    (hlogL_ub : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) ^ (3 / 16 : ℝ))
    (hexp_b : (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset +
      (1 + 36 / c₀ ^ 2 + |Real.log t₀|)) * Real.log (N : ℝ) ^ (3 / 8 : ℝ) ≤ Real.log (N : ℝ))
    (hP_c : (4 * splineWindowConstant * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
      (1 + 36 / c₀ ^ 2 + |Real.log t₀| + 1 + (Real.log 4 + 4)) ^ 2 * K_c / θ_P) *
      Real.log (N : ℝ) ^ (7 / 8 : ℝ) * (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤ Real.log (N : ℝ)) :
    let L := Real.log (N : ℝ)
    let ℓ := 1 + Real.log L
    let w := c / (N : ℝ)
    let x := primeHorizonExtension z
    let M := N / linearDefectCutoff c
    let y := atomicTailCoefficients M x
    let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
    let Bn := ⌊(N : ℝ) * Real.exp w⌋₊
    let C_pole := Real.exp 1 / (∫ u, tiltedUnitSpline u) ^ 2
    let K_win := splineWindowConstant * 8 * Real.exp 2 * C_pole + 1
    let ε_win := c_W0 / (4 * R_max * K_win)
    splineWindowConstant * ((w / h ^ 2) * windowSumBound C_ψ c₀ ((M : ℝ) / 2) Bn M K' x h) ≤
      (c * c_W0 / (4 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
        (K_win * (4 + 2 / ε_win)) * c * (∫ u, U_y u ^ 2) +
        (θ_P / 4) * (L / ℓ ^ 5) * (∑ n ∈ Icc 1 M, x n ^ 2) := by
  intro L ℓ w x M y U_y Bn C_pole K_win ε_win
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hℓ0 : 0 < ℓ := by dsimp only [ℓ]; linarith [Real.log_nonneg hL1]
  have hℓ5_pos : 0 < ℓ ^ 5 := pow_pos hℓ0 5
  have hw0 : 0 < w := div_pos hc0 hN0
  have hw1 : w ≤ 1 := (div_le_one hN0).mpr hcN
  have hI₁ : 0 < ∫ u, tiltedUnitSpline u := integral_tiltedUnitSpline_pos
  have hC_pole : 0 < C_pole := by dsimp only [C_pole]; positivity
  have hκ0 : 0 ≤ splineWindowConstant := splineWindowConstant_nonneg
  have hK_win : 0 < K_win := by dsimp only [K_win]; positivity
  have hε_win : 0 < ε_win := by dsimp only [ε_win]; positivity
  set T := Real.exp (factorialSpanGammaOffset + L ^ (3 / 16 : ℝ))
  have hT0 : 0 < T := Real.exp_pos _
  have hT1 : 1 ≤ T := Real.one_le_exp
    (add_nonneg factorialSpanGammaOffset_nonneg (Real.rpow_nonneg hL0.le _))
  have hh0 : 0 < h := by rw [hh_def]; exact div_pos zero_lt_one (mul_pos hT0 hL0)
  have hh1 : h ≤ 1 := by
    rw [hh_def]
    exact (div_le_one (mul_pos hT0 hL0)).mpr (one_le_mul_of_one_le_of_one_le hT1 hL1)
  have hwB : w * Bn ≤ Real.exp 1 * c := by
    have hBn_le : (Bn : ℝ) ≤ N * Real.exp w := Nat.floor_le (by positivity)
    calc w * Bn ≤ w * (N * Real.exp w) := mul_le_mul_of_nonneg_left hBn_le hw0.le
      _ = c * Real.exp w := by dsimp only [w]; field_simp [hN0.ne']
      _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hc0.le
      _ = Real.exp 1 * c := mul_comm _ _
  have hAB : (M : ℝ) / 2 ≤ Bn := by
    have h1 : (N : ℝ) ≤ Bn := by
      exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hN0.le (Real.one_le_exp hw0.le))
    have h2 : (M : ℝ) ≤ N := by exact_mod_cast hMN
    linarith only [h1, h2]
  set C_β : ℝ := 1 + 36 / c₀ ^ 2 + |Real.log t₀|
  have hC_β : 0 < C_β := by dsimp only [C_β]; positivity
  set ν := (2 * Real.log (1 / h) + Real.log (4 * C_ψ + 1)) / c₀
  set β := 1 + ν ^ 2 + |Real.log t₀|
  set ΛK := β + 1 + (Real.log 4 + 4)
  have hLK : shortOrderWeight K' ≤ ΛK := by linarith [shortOrderWeight_le hK'1, hlogK']
  have hC₄ : 1 ≤ Real.log 4 + 4 := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  set ΨK := (Real.log 4 + 4) * (2 * Real.exp β)
  have hΨK : ∑ k ∈ range K', (Λ k : ℝ) ≤ ΨK :=
    (sum_vonMangoldt_range_le K').trans (mul_le_mul_of_nonneg_left hK'le (zero_le_one.trans hC₄))
  have hWS := windowSumBound_div_le (M := M) x hh0 hh1 hCψ hpntK' hw0.le hc0.le hwB
    (by positivity) hAB hLK hΨK
  obtain ⟨hβ_ub, hwhΨ⟩ := far_garding_window_beta_psi_le hCψ hc₀ hN1 hL1 hcL hh_def
    hL316_C hlogL_ub hexp_b
  have hσ_part : splineWindowConstant * (8 * Real.exp 2 * c * prefixPoleMoment M x ^ 2) ≤
      (c * c_W0 / (4 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
        (K_win * (4 + 2 / ε_win)) * c * ∫ u, U_y u ^ 2 := by
    have hpole := prefixPoleMoment_sq_le_exponential_mass hN2 hMN hc1 hcN hε_win hz
    have hm1 := mul_le_mul_of_nonneg_left hpole
      (by positivity : 0 ≤ splineWindowConstant * 8 * Real.exp 2 * c)
    have hK_le : splineWindowConstant * 8 * Real.exp 2 * C_pole ≤ K_win := by
      dsimp only [K_win]; linarith
    have hm2 : (splineWindowConstant * 8 * Real.exp 2 * c) *
        (C_pole * (ε_win * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
          (4 + 2 / ε_win) * ∫ u, U_y u ^ 2)) ≤
        c * K_win * (ε_win * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
          (4 + 2 / ε_win) * ∫ u, U_y u ^ 2) := by
      have hid : (splineWindowConstant * 8 * Real.exp 2 * c) *
          (C_pole * (ε_win * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
            (4 + 2 / ε_win) * ∫ u, U_y u ^ 2)) =
          c * (splineWindowConstant * 8 * Real.exp 2 * C_pole) *
            (ε_win * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
              (4 + 2 / ε_win) * ∫ u, U_y u ^ 2) := by ring
      rw [hid]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK_le hc0.le)
        (add_nonneg (mul_nonneg hε_win.le (integral_nonneg fun _ => by positivity))
          (mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)))
    have hid_end : c * K_win * (ε_win * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
        (4 + 2 / ε_win) * ∫ u, U_y u ^ 2) =
        (c * c_W0 / (4 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
          (K_win * (4 + 2 / ε_win)) * c * ∫ u, U_y u ^ 2 := by
      dsimp only [ε_win]; field_simp [hK_win.ne', hR.ne']
    linarith only [hm1, hm2, hid_end]
  set P := ∑ n ∈ Icc 1 M, x n ^ 2
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hP_part : splineWindowConstant *
      ((8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
        48 * Real.exp 1 * c * h * prefixHarmonic M +
        2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK)) * prefixMass M x) ≤
      (θ_P / 4) * (L / ℓ ^ 5) * P := by
    have hHM : prefixHarmonic M ≤ 1 + L := by
      have h1 := RHTower.sum_Icc_one_div_le hM1
      have h2 : Real.log (M : ℝ) ≤ L :=
        Real.log_le_log (by exact_mod_cast hM1) (by exact_mod_cast hMN)
      unfold prefixHarmonic; linarith only [h1, h2]
    have hhH : h * prefixHarmonic M ≤ 2 := by
      have hhL : h * (1 + L) ≤ 2 := by
        have h1 : 1 + L ≤ 2 * L := by linarith only [hL1]
        calc h * (1 + L) ≤ (1 / (T * L)) * (2 * L) := by
              rw [← hh_def]; exact mul_le_mul_of_nonneg_left h1 hh0.le
          _ = 2 / T := by field_simp [hT0.ne', hL0.ne']
          _ ≤ 2 := div_le_self zero_le_two hT1
      exact (mul_le_mul_of_nonneg_left hHM hh0.le).trans hhL
    have hh2H : h ^ 2 * prefixHarmonic M ≤ 2 := by
      calc h ^ 2 * prefixHarmonic M = h * (h * prefixHarmonic M) := by ring
        _ ≤ 1 * 2 := mul_le_mul hh1 hhH
            (mul_nonneg hh0.le (sum_nonneg fun m _ => by positivity)) zero_le_one
        _ = 2 := one_mul 2
    have hβ0 : 0 ≤ β := by dsimp only [β]; positivity
    have hΛK1 : 1 ≤ ΛK := by dsimp only [ΛK]; linarith only [hβ0, hC₄]
    have hΛ2 : ΛK ≤ ΛK ^ 2 := le_self_pow₀ hΛK1 two_ne_zero
    have hΛ1 : 1 ≤ ΛK ^ 2 := one_le_pow₀ hΛK1
    have hL2K : Real.log (2 * K') ≤ ΛK + 1 := by
      have hK'R : (0 : ℝ) < K' := by exact_mod_cast hK'1
      rw [Real.log_mul zero_lt_two.ne' hK'R.ne']
      dsimp only [ΛK]; linarith [hlogK', Real.log_two_lt_d9, hC₄]
    have hPc : 8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
        48 * Real.exp 1 * c * h * prefixHarmonic M +
        2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK) ≤
        c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2 := by
      have t1 : 1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M ≤ 11 * ΛK ^ 2 := by
        linarith only [hL2K, hh2H, hΛ2, hΛ1, hΛK1]
      have t1' := mul_le_mul_of_nonneg_left t1 (by positivity : 0 ≤ 8 * Real.exp 2 * c)
      have t2 : 48 * Real.exp 1 * c * h * prefixHarmonic M ≤ 96 * Real.exp 1 * c * ΛK ^ 2 := by
        have a1 := mul_le_mul_of_nonneg_left hhH (by positivity : 0 ≤ 48 * Real.exp 1 * c)
        have a2 := mul_le_mul_of_nonneg_left hΛ1 (by positivity : 0 ≤ 96 * Real.exp 1 * c)
        linarith only [a1, a2]
      have t3 : 2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK) ≤
          (2 * Real.exp 2 + 2) * c * ΛK ^ 2 := by
        have a1 := mul_le_mul_of_nonneg_left hwhΨ (by positivity : 0 ≤ 2 * ΛK)
        have a2 : ΛK ^ 2 ≤ c * ΛK ^ 2 := le_mul_of_one_le_left (by positivity) hc1
        linarith only [a1, a2, hΛ2]
      have hcΛ : 0 ≤ (10 * Real.exp 2 + 4 * Real.exp 1 + 8) * (c * ΛK ^ 2) := by positivity
      linarith only [t1', t2, t3, hcΛ]
    have hΛK_ub : ΛK ≤ (C_β + 1 + (Real.log 4 + 4)) * L ^ (3 / 8 : ℝ) := by
      have hL38_1 : 1 ≤ L ^ (3 / 8 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      dsimp only [ΛK]; nlinarith only [hβ_ub, hL38_1, hC₄]
    have hcΛ2_ub : splineWindowConstant * (c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2) ≤
        (θ_P / 4) * (L / ℓ ^ 5) := by
      have hΛK2_ub : ΛK ^ 2 ≤ (C_β + 1 + (Real.log 4 + 4)) ^ 2 * L ^ (3 / 4 : ℝ) := by
        have hp := pow_le_pow_left₀ (by positivity) hΛK_ub 2
        rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
        exact hp.trans_eq (by norm_num)
      have hc_mul : c * ΛK ^ 2 ≤ K_c * (C_β + 1 + (Real.log 4 + 4)) ^ 2 * L ^ (7 / 8 : ℝ) := by
        have hm := mul_le_mul hc_up hΛK2_ub (sq_nonneg _) (hc0.le.trans hc_up)
        have hadd : L ^ (1 / 8 : ℝ) * L ^ (3 / 4 : ℝ) = L ^ (7 / 8 : ℝ) := by
          rw [← Real.rpow_add hL0]; norm_num
        exact hm.trans_eq (by rw [show K_c * L ^ (1 / 8 : ℝ) *
          ((C_β + 1 + (Real.log 4 + 4)) ^ 2 * L ^ (3 / 4 : ℝ)) =
          K_c * (C_β + 1 + (Real.log 4 + 4)) ^ 2 * (L ^ (1 / 8 : ℝ) * L ^ (3 / 4 : ℝ)) by ring,
          hadd])
      have hm1 := mul_le_mul_of_nonneg_left hc_mul
        (by positivity : 0 ≤ splineWindowConstant * (100 * Real.exp 2 + 100 * Real.exp 1 + 10))
      rw [mul_div_assoc', le_div_iff₀ hℓ5_pos]
      change ((4 * splineWindowConstant * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
        (C_β + 1 + (Real.log 4 + 4)) ^ 2 * K_c / θ_P) * L ^ (7 / 8 : ℝ) * ℓ ^ 5) ≤ L at hP_c
      have hm1' := mul_le_mul_of_nonneg_right hm1 hℓ5_pos.le
      have hm2 := mul_le_mul_of_nonneg_left hP_c (by positivity : 0 ≤ θ_P / 4)
      have hid : (θ_P / 4) * ((4 * splineWindowConstant *
          (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
          (C_β + 1 + (Real.log 4 + 4)) ^ 2 * K_c / θ_P) * L ^ (7 / 8 : ℝ) * ℓ ^ 5) =
          (splineWindowConstant * (100 * Real.exp 2 + 100 * Real.exp 1 + 10)) *
            (K_c * (C_β + 1 + (Real.log 4 + 4)) ^ 2 * L ^ (7 / 8 : ℝ)) * ℓ ^ 5 := by
        field_simp [hθ_P.ne']
      linarith only [hm1', hm2, hid]
    have hPM_eq : prefixMass M x = P := rfl
    rw [hPM_eq]
    calc splineWindowConstant *
          ((8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
            48 * Real.exp 1 * c * h * prefixHarmonic M +
            2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK)) * P)
        ≤ splineWindowConstant * ((c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2) * P) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPc hP0) hκ0
      _ = (splineWindowConstant * (c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2)) * P :=
          by ring
      _ ≤ (θ_P / 4) * (L / ℓ ^ 5) * P := mul_le_mul_of_nonneg_right hcΛ2_ub hP0
  have hWS_κ := mul_le_mul_of_nonneg_left hWS hκ0
  linarith only [hWS_κ, hσ_part, hP_part]

private lemma far_garding_w8_net_id (G c c_W0 R_max W : ℝ) :
    G * ((c * (c_W0 / 2) / R_max) * W) =
      G * ((c * c_W0 / R_max) * W) - G * ((c * c_W0 / (4 * R_max)) * W) -
        G * ((c * c_W0 / (4 * R_max)) * W) := by
  rw [div_mul_eq_div_div]
  ring

private lemma far_garding_uy_collect_id
    (G c I₂ B_arch G₀ γ B_pr K_win ε_win J : ℝ) :
    (B_arch / 2) * (G * ((c / I₂) * J)) +
      2 * Real.pi * (G * ((c / I₂) * J)) +
      ((G₀ + Real.log 2) / 4) * (G * ((c / I₂) * J)) +
      G * ((γ / (2 * I₂)) * c * J) +
      2 * (G * ((c / I₂) * J)) +
      G * ((B_pr / I₂) * c * J) +
      G * ((K_win * (4 + 2 / ε_win)) * c * J) =
    G * (((B_arch / 2 + 2 * Real.pi + (G₀ + Real.log 2) / 4 +
      γ / 2 + 2 + B_pr) / I₂ + K_win * (4 + 2 / ε_win)) * (c * J)) := by
  rw [div_mul_eq_div_div]
  ring

private lemma far_garding_p0_debit {c K_c θ_P L ℓ P : ℝ}
    (hc1 : 1 ≤ c) (hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ)) (hθ_P : 0 < θ_P)
    (hℓ5_pos : 0 < ℓ ^ 5) (hP0 : 0 ≤ P)
    (hP_a :
      (4 * (1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost +
        (Real.log 4 + 4) + 2 * Real.pi) * K_c / θ_P) *
        L ^ (1 / 8 : ℝ) * ℓ ^ 5 ≤ L) :
    (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
      (Real.log 4 + 4) + 2 * Real.pi) * P ≤ (θ_P / 4) * (L / ℓ ^ 5) * P := by
  set C_P0 : ℝ := 1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost +
    (Real.log 4 + 4) + 2 * Real.pi
  have hAsep : 0 ≤ separatedCrossMassCost := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    unfold separatedCrossMassCost; positivity
  have hl4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  have hC_P0 : 0 < C_P0 := by dsimp only [C_P0]; positivity
  have hc_P0 : c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
      (Real.log 4 + 4) + 2 * Real.pi ≤ C_P0 * c := by
    dsimp only [C_P0]
    nlinarith only [hc1, abs_nonneg (gammaHardyPhaseRate 0), hAsep, hl4, Real.pi_pos]
  have hP_a' : C_P0 * c ≤ (θ_P / 4) * (L / ℓ ^ 5) := by
    rw [mul_div_assoc', le_div_iff₀ hℓ5_pos]
    have hm1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc_up hC_P0.le) hℓ5_pos.le
    have hm2 := mul_le_mul_of_nonneg_left hP_a (by positivity : 0 ≤ θ_P / 4)
    have hid : (θ_P / 4) * ((4 * C_P0 * K_c / θ_P) * L ^ (1 / 8 : ℝ) * ℓ ^ 5) =
        C_P0 * (K_c * L ^ (1 / 8 : ℝ)) * ℓ ^ 5 := by
      calc (θ_P / 4) * ((4 * C_P0 * K_c / θ_P) * L ^ (1 / 8 : ℝ) * ℓ ^ 5)
          = (θ_P * (4 * C_P0 * K_c / θ_P) / 4) * L ^ (1 / 8 : ℝ) * ℓ ^ 5 := by ring
        _ = (4 * C_P0 * K_c / 4) * L ^ (1 / 8 : ℝ) * ℓ ^ 5 := by rw [mul_div_cancel₀ _ hθ_P.ne']
        _ = C_P0 * (K_c * L ^ (1 / 8 : ℝ)) * ℓ ^ 5 := by ring
    linarith only [hm1, hm2, hid]
  exact mul_le_mul_of_nonneg_right (hc_P0.trans hP_a') hP0

private lemma far_garding_linear_assembly
    {G c I₂ c_W0 R_max B_arch G₀ γ B_pr K_win ε_win B_far L ℓ θ_P g₀
      D_M S7 W8 Lev U2 P E aN pN aP pP ay py iX ly hy iF iFh C_p : ℝ}
    (hG0 : 0 < G) (hc0 : 0 < c) (hg₀ : 0 ≤ g₀) (hL0 : 0 ≤ L)
    (hS7_0 : 0 ≤ S7) (hU2_0 : 0 ≤ U2) (hQ0 : 0 ≤ (θ_P / 4) * (L / ℓ ^ 5) * P)
    (hB_sum : (B_arch / 2 + 2 * Real.pi + (G₀ + Real.log 2) / 4 +
      γ / 2 + 2 + B_pr) / I₂ + K_win * (4 + 2 / ε_win) ≤ B_far)
    (henergy : E = aN / G - pN / G)
    (harch_ord : aP + ay - 2 * Real.pi * (G * P + G * ((c / I₂) * U2)) ≤ aN)
    (hPb : G * (D_M - C_p * P) ≤ aP - pP)
    (hP0_part : (C_p + 2 * Real.pi) * P ≤ (θ_P / 4) * (L / ℓ ^ 5) * P)
    (hSb : pN = pP + py + 2 * iX)
    (hdyad : G * ((g₀ / (4 * c ^ 7)) * L * S7 + (c * c_W0 / R_max) * W8) ≤
      (1 / 2 : ℝ) * ay + (B_arch / 2) * (G * ((c / I₂) * U2)))
    (hlev : G * ((c / (4 * I₂)) * Lev) - G * ((γ / (2 * I₂)) * c * U2) ≤ (1 / 4 : ℝ) * ay)
    (hband : hy - ((G₀ + Real.log 2) / 4) * (G * ((c / I₂) * U2)) ≤ (1 / 4 : ℝ) * ay)
    (hpr_top : py ≤ G * ((c * c_W0 / (4 * R_max)) * W8 + (B_pr / I₂) * c * U2))
    (hX : 2 * |iX| ≤ (G * ((c / I₂) * U2)) + iFh + ly + iF + hy)
    (hLMy : ly ≤ G * ((c / I₂) * U2))
    (htr_P : iF ≤ G * ((θ_P / 4) * (L / ℓ ^ 5) * P))
    (hwin : iFh ≤ G * ((c * c_W0 / (4 * R_max)) * W8 +
      (K_win * (4 + 2 / ε_win)) * c * U2 + (θ_P / 4) * (L / ℓ ^ 5) * P)) :
    D_M + (g₀ / (8 * c ^ 7)) * L * S7 + (c * (c_W0 / 2) / R_max) * W8 +
      (c / (4 * I₂)) * Lev - (θ_P * L / ℓ ^ 5) * P ≤
      E + (c * B_far) * U2 := by
  have hS7_half : G * ((g₀ / (8 * c ^ 7)) * L * S7) ≤ G * ((g₀ / (4 * c ^ 7)) * L * S7) := by
    refine mul_le_mul_of_nonneg_left ?_ hG0.le
    have : g₀ / (8 * c ^ 7) ≤ g₀ / (4 * c ^ 7) :=
      div_le_div_of_nonneg_left hg₀ (by positivity) (by linarith [pow_pos hc0 7])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hL0) hS7_0
  have hG_U_cost : G * (((B_arch / 2 + 2 * Real.pi + (G₀ + Real.log 2) / 4 +
      γ / 2 + 2 + B_pr) / I₂ + K_win * (4 + 2 / ε_win)) * (c * U2)) ≤
      G * ((c * B_far) * U2) := by
    refine mul_le_mul_of_nonneg_left ?_ hG0.le
    have hm := mul_le_mul_of_nonneg_right hB_sum (mul_nonneg hc0.le hU2_0)
    linarith only [hm, (by ring : B_far * (c * U2) = (c * B_far) * U2)]
  have hG_P0 := mul_le_mul_of_nonneg_left hP0_part hG0.le
  have hX_abs : 2 * iX ≤ 2 * |iX| := mul_le_mul_of_nonneg_left (le_abs_self iX) zero_le_two
  have hG_theta : G * (3 * ((θ_P / 4) * (L / ℓ ^ 5) * P)) ≤ G * ((θ_P * L / ℓ ^ 5) * P) := by
    refine mul_le_mul_of_nonneg_left ?_ hG0.le
    linarith only [hQ0, (by ring : 4 * ((θ_P / 4) * (L / ℓ ^ 5) * P) = (θ_P * L / ℓ ^ 5) * P)]
  rw [henergy, ← sub_div, div_add' _ _ _ hG0.ne', le_div_iff₀' hG0]
  rw [mul_sub] at hPb
  rw [mul_add] at hdyad hpr_top
  rw [mul_add, mul_add] at hwin
  have harch_ord_exp : 2 * Real.pi * (G * P + G * ((c / I₂) * U2)) =
      G * ((2 * Real.pi) * P) + 2 * Real.pi * (G * ((c / I₂) * U2)) := by ring
  have hG_P0_exp : G * (C_p * P) + G * ((2 * Real.pi) * P) =
      G * ((C_p + 2 * Real.pi) * P) := by ring
  have hG_theta_exp : G * ((θ_P / 4) * (L / ℓ ^ 5) * P) + G * ((θ_P / 4) * (L / ℓ ^ 5) * P) +
      G * ((θ_P / 4) * (L / ℓ ^ 5) * P) = G * (3 * ((θ_P / 4) * (L / ℓ ^ 5) * P)) := by ring
  have harch_split : ay = (1 / 2 : ℝ) * ay + (1 / 4 : ℝ) * ay + (1 / 4 : ℝ) * ay := by ring
  have hW8_net := far_garding_w8_net_id G c c_W0 R_max W8
  have hUy_collect := far_garding_uy_collect_id G c I₂ B_arch G₀ γ B_pr K_win ε_win U2
  have hgoal_expand : G * (D_M + (g₀ / (8 * c ^ 7)) * L * S7 +
      (c * (c_W0 / 2) / R_max) * W8 + (c / (4 * I₂)) * Lev - (θ_P * L / ℓ ^ 5) * P) =
      G * D_M + G * ((g₀ / (8 * c ^ 7)) * L * S7) +
        G * ((c * (c_W0 / 2) / R_max) * W8) + G * ((c / (4 * I₂)) * Lev) -
        G * ((θ_P * L / ℓ ^ 5) * P) := by ring
  rw [hgoal_expand]
  linarith only [harch_ord, harch_ord_exp, hPb, hSb, hdyad, hlev, hband, hpr_top,
    hX, hX_abs, hLMy, htr_P, hwin, hG_P0, hG_P0_exp, hS7_half,
    hG_U_cost, hG_theta, hG_theta_exp, harch_split, hW8_net, hUy_collect]

private lemma far_garding_at_N {N : ℕ} {c R_max B_arch C_err C_ψ c₀ t₀ B_far : ℝ}
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hR : 0 < R_max) (hC_err0 : 0 ≤ C_err) (hCψ : 0 ≤ C_ψ) (hc₀ : 0 < c₀) (ht₀1 : 1 ≤ t₀)
    (hpnt : ∀ ⦃h X Y : ℝ⦄, 0 < h → h ≤ 1 → Y = X * Real.exp (-h) → t₀ ≤ Y →
      |∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k - Real.sqrt X * (1 - Real.exp (-h))| ≤
        Real.sqrt X * (4 * C_ψ * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2))
    (harch_g : ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → (linearDefectCutoff c : ℝ) ^ 2 ≤ N →
      ∀ x : ℕ → ℝ,
        (c / N) * (∫ u, tiltedUnitSpline u ^ 2) *
          (((dyadicTopMassConstant / c ^ 7) * Real.log N - C_err * (c ^ 2 / N)) *
            topCollarSeventhMass (N / linearDefectCutoff c) N x) ≤
        archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
            (atomDilate tiltedUnitSpline (c / N))) +
          B_arch * ∫ u, atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
            (atomDilate tiltedUnitSpline (c / N)) u ^ 2)
    (hB_sum :
      let I₂ := ∫ u, tiltedUnitSpline u ^ 2
      let C₈ := (256 * Real.exp 2 + 4 + 2 * Real.exp 1) * I₂
      let c_W0 := dyadicTopMassConstant / (8 * C₈)
      let C_pole := Real.exp 1 / (∫ u, tiltedUnitSpline u) ^ 2
      let K_win := splineWindowConstant * 8 * Real.exp 2 * C_pole + 1
      let ε_pr := I₂ * c_W0 / (4 * R_max)
      let ε_win := c_W0 / (4 * R_max * K_win)
      let B_pr := 2 * vonMangoldtThreeHalvesMass +
        (2 * vonMangoldtThreeHalvesMass) ^ 2 * Real.exp 8 / ε_pr
      (B_arch / 2 + 2 * Real.pi + (factorialSpanGammaOffset + Real.log 2) / 4 +
        |gammaHardyPhaseRate 0| / 2 + 2 + B_pr) / I₂ + K_win * (4 + 2 / ε_win) ≤ B_far)
    (hN3 : 3 ≤ N) (hc1 : 1 ≤ c) (hc8 : c ^ 8 ≤ R_max * Real.log (N : ℝ))
    (hz : z ∈ (conductorSubspace 1 N)ᗮ)
    (hL2N_b : 2 * ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)) * Real.log (N : ℝ) ≤ N)
    (herr_b : C_err * ((R_max + 1) * Real.log (N : ℝ) / N) ≤ dyadicTopMassConstant / (4 * R_max))
    (hL_ge : max 4 (R_max + 1) ≤ Real.log (N : ℝ))
    (hL316_C : factorialSpanGammaOffset + Real.log (4 * C_ψ + 1) + 4 ≤
      Real.log (N : ℝ) ^ (3 / 16 : ℝ))
    (hlogL_ub : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) ^ (3 / 16 : ℝ))
    (hP_a :
      (4 * (1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost +
        (Real.log 4 + 4) + 2 * Real.pi) * (R_max + 1) ^ (1 / 8 : ℝ) /
        (1 / (16 * explicitConductorCutoffConstant))) *
        Real.log (N : ℝ) ^ (1 / 8 : ℝ) * (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤
        Real.log (N : ℝ))
    (hP_b :
      (4 * 68 *
        ((1 + 2 * Real.exp 2) *
          (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4))) *
        (R_max + 1) ^ (1 / 8 : ℝ) / (1 / (16 * explicitConductorCutoffConstant))) *
        Real.log (N : ℝ) ^ (15 / 16 : ℝ) * (1 + Real.log (Real.log (N : ℝ))) ^ 6 ≤
        Real.log (N : ℝ))
    (hP_c :
      (4 * splineWindowConstant * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
        (1 + 36 / c₀ ^ 2 + |Real.log t₀| + 1 + (Real.log 4 + 4)) ^ 2 *
        (R_max + 1) ^ (1 / 8 : ℝ) / (1 / (16 * explicitConductorCutoffConstant))) *
        Real.log (N : ℝ) ^ (7 / 8 : ℝ) * (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤
        Real.log (N : ℝ))
    (hexp_b :
      (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset +
        (1 + 36 / c₀ ^ 2 + |Real.log t₀|)) *
        Real.log (N : ℝ) ^ (3 / 8 : ℝ) ≤ Real.log (N : ℝ)) :
    let I₂ := ∫ u, tiltedUnitSpline u ^ 2
    let C₈ := (256 * Real.exp 2 + 4 + 2 * Real.exp 1) * I₂
    let c_W0 := dyadicTopMassConstant / (8 * C₈)
    let x := primeHorizonExtension z
    let M := N / linearDefectCutoff c
    let y := atomicTailCoefficients M x
    let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
    (7 / 8 : ℝ) * poleDefect M x +
      (dyadicTopMassConstant / (8 * c ^ 7)) * Real.log (N : ℝ) *
        topCollarSeventhMass M N x +
      (c * (c_W0 / 2) / R_max) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
      (c / (4 * I₂)) * levyEnergy U_y -
      ((1 / (16 * explicitConductorCutoffConstant)) * Real.log (N : ℝ) /
        (1 + Real.log (Real.log (N : ℝ))) ^ 5) *
        (∑ n ∈ Icc 1 M, x n ^ 2) ≤
    completeWeilEnergy tiltedUnitSpline c N z +
      (c * B_far) * ∫ u, U_y u ^ 2 := by
  intro I₂ C₈ c_W0 x M y U_y
  have hg₀ : 0 < dyadicTopMassConstant := dyadicTopMassConstant_pos
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  have hI₁ : 0 < ∫ u, tiltedUnitSpline u := integral_tiltedUnitSpline_pos
  have hC₈ : 0 < C₈ := by dsimp only [C₈]; positivity
  have hc_W0 : 0 < c_W0 := div_pos hg₀ (by positivity)
  set L := Real.log (N : ℝ)
  set ℓ := 1 + Real.log L
  have hL4 : 4 ≤ L := (le_max_left _ _).trans hL_ge
  have hR_L : R_max + 1 ≤ L := (le_max_right _ _).trans hL_ge
  have hL1 : 1 ≤ L := by linarith only [hL4]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hℓ0 : 0 < ℓ := by dsimp only [ℓ]; linarith [Real.log_nonneg hL1]
  have hℓ5_pos : 0 < ℓ ^ 5 := pow_pos hℓ0 5
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  set K_c : ℝ := (R_max + 1) ^ (1 / 8 : ℝ)
  have hKc0 : 0 < K_c := by dsimp only [K_c]; positivity
  have hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ) := by
    have hp : c ^ 8 ≤ (K_c * L ^ (1 / 8 : ℝ)) ^ 8 := by
      dsimp only [K_c]
      rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le,
        ← Real.rpow_natCast ((R_max + 1) ^ _), ← Real.rpow_mul (by positivity : 0 ≤ R_max + 1),
        show (1 / 8 : ℝ) * (8 : ℕ) = 1 by norm_num, Real.rpow_one, Real.rpow_one]
      nlinarith only [hc8, hL0]
    exact le_of_pow_le_pow_left₀ (by norm_num : 8 ≠ 0) (by positivity) hp
  have hcL : c ≤ L := by
    have hc8_L2 : c ^ 8 ≤ L ^ 2 := by nlinarith only [hc8, hR_L, hL0]
    have hL2_8 : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
    exact le_of_pow_le_pow_left₀ (by norm_num : 8 ≠ 0) hL0.le (hc8_L2.trans hL2_8)
  obtain ⟨hL3, h4c, -, hLup⟩ := linearDefectCutoff_bounds hc1
  have hc2_RL : c ^ 2 ≤ (R_max + 1) * L := by
    have h28 : c ^ 2 ≤ c ^ 8 := pow_le_pow_right₀ hc1 (by norm_num)
    nlinarith only [h28, hc8, hL0]
  have h2L2N : 2 * (linearDefectCutoff c : ℝ) ^ 2 ≤ N := by
    have h1 : (linearDefectCutoff c : ℝ) ^ 2 ≤ (256 * Real.exp 2 + 4) ^ 2 * c ^ 2 :=
      (pow_le_pow_left₀ (by positivity) hLup 2).trans_eq (mul_pow _ _ 2)
    have h2 : 2 * ((256 * Real.exp 2 + 4) ^ 2 * c ^ 2) ≤
        2 * ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)) * L := by
      calc 2 * ((256 * Real.exp 2 + 4) ^ 2 * c ^ 2)
          = (2 * (256 * Real.exp 2 + 4) ^ 2) * c ^ 2 := by ring
        _ ≤ (2 * (256 * Real.exp 2 + 4) ^ 2) * ((R_max + 1) * L) :=
            mul_le_mul_of_nonneg_left hc2_RL (by positivity)
        _ = 2 * ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)) * L := by ring
    linarith only [h1, h2, hL2N_b]
  have hL2N : (linearDefectCutoff c : ℝ) ^ 2 ≤ N := by
    linarith only [h2L2N, sq_nonneg (linearDefectCutoff c : ℝ)]
  have h2LN : 2 * linearDefectCutoff c ≤ N := by
    have hLc1 : (1 : ℝ) ≤ linearDefectCutoff c := by
      have : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hL3
      linarith
    have hle : (2 * linearDefectCutoff c : ℝ) ≤ N := by
      have hsq := le_self_pow₀ hLc1 (by norm_num : 2 ≠ 0)
      linarith only [hsq, h2L2N]
    exact_mod_cast hle
  have hLN : linearDefectCutoff c ≤ N := by omega
  have hM1 : 1 ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
  have hMN : M ≤ N := Nat.div_le_self _ _
  have hcN : c ≤ N := by
    have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  set w := c / (N : ℝ)
  have hw0 : 0 < w := div_pos hc0 hN0
  have hw1 : w ≤ 1 := (div_le_one hN0).mpr hcN
  set g := atomDilate tiltedUnitSpline w
  set G := w * I₂
  have hG0 : 0 < G := mul_pos hw0 hI₂
  set P := ∑ n ∈ Icc 1 M, x n ^ 2
  set S7 := topCollarSeventhMass M N x
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS7_0 : 0 ≤ S7 := topCollarSeventhMass_nonneg M N x
  have hg_cd : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hg_cs : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw0.ne' hasCompactSupport_tiltedUnitSpline
  have hg_supp := tiltedUnitSpline_atom_support hw0
  have hmass_g : ∫ u, g u ^ 2 = G := integral_atomDilate_sq hw0
  set f_P := atomicTest M x g
  set f_y := atomicTest N y g
  have hfP_cd : ContDiff ℝ 2 f_P := contDiff_atomicTest hg_cd M x
  have hfP_cs : HasCompactSupport f_P := hasCompactSupport_atomicTest hg_supp M x
  have hfy_cd : ContDiff ℝ 2 f_y := contDiff_atomicTest hg_cd N y
  have hfy_cs : HasCompactSupport f_y := hasCompactSupport_atomicTest hg_supp N y
  obtain ⟨hUy_cd, hUy_cs, hUy_w, hfy_L2, hfy_arch, hfy_prime⟩ :=
    normalizedCentredAtomicTest_scaling hc0 hN1 y
  change (∫ u, f_y u ^ 2) = G * ((c / I₂) * ∫ u, U_y u ^ 2) at hfy_L2
  change archForm f_y = G * ((c / I₂) * archForm U_y) at hfy_arch
  change primeSum f_y = G * ((c / I₂) * primeSum U_y) at hfy_prime
  have hUy_le1 : ∀ u, 1 < u → U_y u = 0 := fun u hu => hUy_w u (hw1.trans_lt hu)
  have hUy_L2_0 : 0 ≤ ∫ u, U_y u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  -- 1. Ordered archimedean split, prefix block, and prime split
  have hsep : w < atomSpacing M := by
    have hML : (M : ℝ) * linearDefectCutoff c ≤ N := by
      exact_mod_cast Nat.div_mul_le_self N (linearDefectCutoff c)
    have hLR : (0 : ℝ) < linearDefectCutoff c := by exact_mod_cast (show 0 < linearDefectCutoff c by omega)
    have hwM : w * M ≤ c / linearDefectCutoff c := by
      rw [le_div_iff₀ hLR]
      calc w * M * linearDefectCutoff c = w * ((M : ℝ) * linearDefectCutoff c) := by ring
        _ ≤ w * N := mul_le_mul_of_nonneg_left hML hw0.le
        _ = c := by dsimp only [w]; field_simp [hN0.ne']
    have hfour : 4 * w * M ≤ 1 := by
      have hl : 4 * (c / (linearDefectCutoff c : ℝ)) ≤ 1 := by
        rw [← mul_div_assoc, div_le_one hLR]; exact h4c
      nlinarith only [hwM, hl]
    have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have hbound : w ≤ (1 / ((M : ℝ) + 1)) / 2 := by
      rw [le_div_iff₀ zero_lt_two, le_div_iff₀ (by positivity)]
      nlinarith only [hfour, mul_nonneg hw0.le (sub_nonneg.mpr hM1R)]
    linarith only [hbound, (atomSpacing_bounds hM1).1, atomSpacing_pos hM1]
  obtain ⟨_, hleft, hright⟩ := atomicTest_prefix_tail_ordered hg_supp hM1 hsep N x
  have harch_ord := archForm_add_ge_of_ordered hfP_cd hfP_cs hfy_cd hfy_cs hleft hright
  rw [← atomicTest_eq_prefix_add_tail hMN x g] at harch_ord
  have hfP_L2 : ∫ u, f_P u ^ 2 = G * P := by
    rw [integral_atomicTest_sq hg_cd hg_cs hg_supp hsep, hmass_g, mul_comm]
  have hPb : G * ((7 / 8 : ℝ) * poleDefect M x -
      (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost + (Real.log 4 + 4)) * P) ≤
      archForm f_P - primeSum f_P := prefix_block_ge hc1 hLN hM1 x
  have hSb : primeSum (atomicTest N x g) =
      primeSum f_P + primeSum f_y +
        2 * ∫ u, f_y u * atomicTest ⌊(N : ℝ) * Real.exp w⌋₊
          (fun n => topWeight ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp w⌋₊ n *
            primeConv (primeOrderCutoff N w) M x n) g u :=
    primeSum_prefix_top_split hc1 h2LN x
  have henergy := completeWeilEnergy_eq_arch_sub_primeSum hc0 hN2 hz
  rw [hmass_g] at henergy
  change completeWeilEnergy tiltedUnitSpline c N z =
    archForm (atomicTest N x g) / G - primeSum (atomicTest N x g) / G at henergy
  -- 2. Top block three-way split
  have hdyad_split : G * ((dyadicTopMassConstant / (4 * c ^ 7)) * L * S7 +
      (c * c_W0 / R_max) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u)))) ≤
      (1 / 2 : ℝ) * archForm f_y + (B_arch / 2) * ∫ u, f_y u ^ 2 := by
    have htop_dyad := harch_g hc1 hL2N x
    have hc_div_R : c / R_max ≤ L / c ^ 7 :=
      (div_le_div_iff₀ hR (pow_pos hc0 7)).mpr (by
        calc c * c ^ 7 = c ^ 8 := by ring
          _ ≤ L * R_max := by linarith only [hc8])
    have herr_c : C_err * (c ^ 2 / N) ≤ (dyadicTopMassConstant / (4 * R_max)) * c :=
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc2_RL hN0.le) hC_err0).trans
        (herr_b.trans (le_mul_of_one_le_right (by positivity) hc1))
    have hW8_S7 : (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤ C₈ * S7 :=
      normalized_tail_exponential_mass_le contDiff_tiltedUnitSpline.continuous
        tiltedUnitSpline_eq_zero hc1 hLN x
    have hW8_term : (c * c_W0 / R_max) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤
        (dyadicTopMassConstant / (8 * R_max)) * c * S7 := by
      refine (mul_le_mul_of_nonneg_left hW8_S7 (by positivity : 0 ≤ c * c_W0 / R_max)).trans_eq ?_
      dsimp only [c_W0]; field_simp [hC₈.ne', hR.ne']
    have hrate : (dyadicTopMassConstant / (2 * c ^ 7)) * L +
        (dyadicTopMassConstant / (4 * R_max)) * c ≤
        (dyadicTopMassConstant / c ^ 7) * L - C_err * (c ^ 2 / N) := by
      have hm := mul_le_mul_of_nonneg_left hc_div_R (by positivity : 0 ≤ dyadicTopMassConstant / 2)
      linarith only [hm, herr_c,
        (by ring : (dyadicTopMassConstant / 2) * (c / R_max) =
          2 * ((dyadicTopMassConstant / (4 * R_max)) * c)),
        (by ring : (dyadicTopMassConstant / 2) * (L / c ^ 7) =
          (dyadicTopMassConstant / (2 * c ^ 7)) * L),
        (by ring : (dyadicTopMassConstant / c ^ 7) * L =
          2 * ((dyadicTopMassConstant / (2 * c ^ 7)) * L))]
    have hrate_S7 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrate hS7_0) (half_pos hG0).le
    have hhalf_dyad := mul_le_mul_of_nonneg_left htop_dyad (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hG_W8 := mul_le_mul_of_nonneg_left hW8_term hG0.le
    linarith only [hrate_S7, hhalf_dyad, hG_W8,
      (by ring : G / 2 * (((dyadicTopMassConstant / (2 * c ^ 7)) * L +
          (dyadicTopMassConstant / (4 * R_max)) * c) * S7) =
        G * ((dyadicTopMassConstant / (4 * c ^ 7)) * L * S7) +
          G * ((dyadicTopMassConstant / (8 * R_max)) * c * S7)),
      (by ring : G / 2 * (((dyadicTopMassConstant / c ^ 7) * L - C_err * (c ^ 2 / N)) * S7) =
        (1 / 2 : ℝ) * (G * (((dyadicTopMassConstant / c ^ 7) * L - C_err * (c ^ 2 / N)) * S7))),
      (by ring : G * ((dyadicTopMassConstant / (4 * c ^ 7)) * L * S7 +
          (c * c_W0 / R_max) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u)))) =
        G * ((dyadicTopMassConstant / (4 * c ^ 7)) * L * S7) +
          G * ((c * c_W0 / R_max) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))))),
      (by ring : (1 / 2 : ℝ) * (archForm f_y + B_arch * ∫ u, f_y u ^ 2) =
        (1 / 2 : ℝ) * archForm f_y + (B_arch / 2) * ∫ u, f_y u ^ 2)]
  have hlev_q : G * ((c / (4 * I₂)) * levyEnergy U_y) -
      G * ((|gammaHardyPhaseRate 0| / (2 * I₂)) * c * ∫ u, U_y u ^ 2) ≤
      (1 / 4 : ℝ) * archForm f_y := by
    rw [hfy_arch, archForm_eq_levyEnergy hUy_cd hUy_cs]
    have hm := mul_le_mul_of_nonneg_right (neg_abs_le (gammaHardyPhaseRate 0))
      (mul_nonneg (by positivity : 0 ≤ G * (c / (2 * I₂))) hUy_L2_0)
    linarith only [hm,
      (by ring : (1 / 4 : ℝ) * (G * ((c / I₂) *
          (2 * gammaHardyPhaseRate 0 * (∫ u, U_y u ^ 2) + levyEnergy U_y))) =
        G * ((c / (4 * I₂)) * levyEnergy U_y) +
          gammaHardyPhaseRate 0 * (G * (c / (2 * I₂)) * ∫ u, U_y u ^ 2)),
      (by ring : -|gammaHardyPhaseRate 0| * (G * (c / (2 * I₂)) * ∫ u, U_y u ^ 2) =
        -(G * ((|gammaHardyPhaseRate 0| / (2 * I₂)) * c * ∫ u, U_y u ^ 2)))]
  set G₀ := factorialSpanGammaOffset
  have hG₀ : 0 ≤ G₀ := factorialSpanGammaOffset_nonneg
  set T := Real.exp (G₀ + L ^ (3 / 16 : ℝ))
  have hT0 : 0 < T := Real.exp_pos _
  have hband_q : (1 / 4 : ℝ) * L ^ (3 / 16 : ℝ) * highFourierMass f_y T -
      ((G₀ + Real.log 2) / 4) * (∫ u, f_y u ^ 2) ≤ (1 / 4 : ℝ) * archForm f_y := by
    have hb := archForm_ge_high_band hfy_cd hfy_cs (T := T) (R := T) hT0 le_rfl
    rw [sub_self, zero_mul, add_zero, show Real.log T - G₀ = L ^ (3 / 16 : ℝ) by
      rw [Real.log_exp]; ring] at hb
    have hlm := mul_le_mul_of_nonneg_left (lowFourierMass_le_integral_sq hfy_cd hfy_cs T)
      (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)] : 0 ≤ (G₀ + Real.log 2) / 4)
    linarith only [hb, hlm]
  -- 3. Top self prime form and prime cross
  set ε_pr := I₂ * c_W0 / (4 * R_max)
  have hε_pr : 0 < ε_pr := by dsimp only [ε_pr]; positivity
  set B_pr := 2 * vonMangoldtThreeHalvesMass +
    (2 * vonMangoldtThreeHalvesMass) ^ 2 * Real.exp 8 / ε_pr
  have hpr_top : primeSum f_y ≤
      G * ((c * c_W0 / (4 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
        (B_pr / I₂) * c * ∫ u, U_y u ^ 2) := by
    rw [hfy_prime, ← mul_assoc]
    have hp := (le_abs_self _).trans
      (abs_primeSum_le_exponential_mass_of_le_one_explicit hε_pr hUy_cd.continuous hUy_cs hUy_le1)
    have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hG0.le (div_nonneg hc0.le hI₂.le))
    refine hm.trans_eq ?_
    dsimp only [ε_pr, B_pr, U_y]; field_simp [hI₂.ne', hR.ne']
  set h := 1 / (T * L)
  have hh0 : 0 < h := div_pos zero_lt_one (mul_pos hT0 hL0)
  have hT1 : 1 ≤ T := Real.one_le_exp (add_nonneg hG₀ (Real.rpow_nonneg hL0.le _))
  have hh1 : h ≤ 1 := (div_le_one (mul_pos hT0 hL0)).mpr (one_le_mul_of_one_le_of_one_le hT1 hL1)
  have hTh : T * h = 1 / L := by dsimp only [h]; field_simp [hT0.ne', hL0.ne']
  obtain ⟨K', hK'1, ht₀K', hpntK', hlogK', hK'le⟩ :=
    exists_short_cutoff hCψ hc₀ ht₀1 hh0 hh1
  obtain ⟨hFh, hF⟩ := translate_masses_le hCψ hc₀ hpnt hc1 h2LN x hh0 hh1 hK'1 ht₀K'
  set Bn := ⌊(N : ℝ) * Real.exp w⌋₊
  set V : ℕ → ℝ := fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv (primeOrderCutoff N w) M x n
  set lam : ℝ := (1 / 4 : ℝ) * L ^ (3 / 16 : ℝ)
  have hlam0 : 0 < lam := mul_pos (by norm_num) (Real.rpow_pos_of_pos hL0 _)
  have hX := two_mul_abs_integral_mul_atomicTest_le (f := f_y) hfy_cd hfy_cs hg_cd hg_supp
    Bn V (T := T) hh0 zero_lt_one hlam0
  rw [inv_one] at hX
  simp only [one_mul] at hX
  have hLMy := lowFourierMass_le_integral_sq hfy_cd hfy_cs T
  set θ_P : ℝ := 1 / (16 * explicitConductorCutoffConstant)
  have hθ_P : 0 < θ_P := by dsimp only [θ_P]; positivity
  have hprod_ub := far_garding_translate_factor_le hc1 h2LN hN1 hM1 hMN hKc0 hθ_P hL1 hc_up hcL
    hTh hP_b
  have htr_P : ((T * h) ^ 2 + lam⁻¹ * 4) * (∫ u, atomicTest Bn V g u ^ 2) ≤
      G * ((θ_P / 4) * (L / ℓ ^ 5) * P) :=
    (mul_le_mul_of_nonneg_left hF (by positivity)).trans
      ((by ring : ((T * h) ^ 2 + lam⁻¹ * 4) * (G *
          ((1 + 2 * Real.exp 1 * (w * Bn)) *
            (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) * P) =
        G * ((((T * h) ^ 2 + lam⁻¹ * 4) *
          ((1 + 2 * Real.exp 1 * (w * Bn)) *
            (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4))))) * P)).trans_le
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod_ub hP0) hG0.le))
  set C_pole := Real.exp 1 / (∫ u, tiltedUnitSpline u) ^ 2
  set K_win := splineWindowConstant * 8 * Real.exp 2 * C_pole + 1
  set ε_win := c_W0 / (4 * R_max * K_win)
  have hsum_κ := far_garding_windowSum_le hR hCψ hc₀ hc_W0 hθ_P hKc0 hN2 hc1 hcN hL1 hc_up hcL
    hM1 hMN hz rfl hK'1 hpntK' hlogK' hK'le hL316_C hlogL_ub hexp_b hP_c
  have hwin_bound : ∫ u, atomicTest Bn V (smoothedBump g h) u ^ 2 ≤
      G * ((c * c_W0 / (4 * R_max)) * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
        (K_win * (4 + 2 / ε_win)) * c * (∫ u, U_y u ^ 2) +
        (θ_P / 4) * (L / ℓ ^ 5) * P) :=
    hFh.trans ((by ring : G * (splineWindowConstant * (w / h ^ 2)) *
        windowSumBound C_ψ c₀ ((M : ℝ) / 2) Bn M K' x h =
        G * (splineWindowConstant * ((w / h ^ 2) *
          windowSumBound C_ψ c₀ ((M : ℝ) / 2) Bn M K' x h))).trans_le
      (mul_le_mul_of_nonneg_left hsum_κ hG0.le))
  -- 4. Prefix `O(c) * P` debit and final assembly
  have hP0_part := far_garding_p0_debit hc1 hc_up hθ_P hℓ5_pos hP0 hP_a
  have hX' : 2 * |∫ u, f_y u * atomicTest Bn V g u| ≤
      (G * ((c / I₂) * ∫ u, U_y u ^ 2)) +
        (∫ u, atomicTest Bn V (smoothedBump g h) u ^ 2) +
        lowFourierMass f_y T +
        (((T * h) ^ 2 + lam⁻¹ * 4) * ∫ u, atomicTest Bn V g u ^ 2) +
        ((1 / 4 : ℝ) * L ^ (3 / 16 : ℝ) * highFourierMass f_y T) := by
    rw [hfy_L2] at hX
    have hX_split : (T * h) ^ 2 * (∫ u, atomicTest Bn V g u ^ 2) +
        lam⁻¹ * (4 * ∫ u, atomicTest Bn V g u ^ 2) =
        ((T * h) ^ 2 + lam⁻¹ * 4) * ∫ u, atomicTest Bn V g u ^ 2 := by ring
    have hlam_eq : lam * highFourierMass f_y T =
        (1 / 4 : ℝ) * L ^ (3 / 16 : ℝ) * highFourierMass f_y T := rfl
    linarith only [hX, hX_split, hlam_eq]
  rw [hfP_L2, hfy_L2] at harch_ord
  rw [hfy_L2] at hdyad_split hband_q hLMy
  change primeSum (atomicTest N x g) =
    primeSum f_P + primeSum f_y + 2 * ∫ u, f_y u * atomicTest Bn V g u at hSb
  exact far_garding_linear_assembly hG0 hc0 hg₀.le hL0.le hS7_0 hUy_L2_0 (by positivity)
    hB_sum henergy harch_ord hPb hP0_part hSb hdyad_split hlev_q hband_q hpr_top hX' hLMy
    htr_P hwin_bound

/-- **All-ratio far Gårding on `(conductorSubspace 1 N)ᗮ`.**
There exists a universal constant `c_W > 0` such that for every critical ratio bound `R_max > 0`,
there exists `B_far > 0` for which eventually in `N`, across all `1 ≤ c` with
`c⁸ ≤ R_max log N`, every pole-orthogonal vector `z ∈ (conductorSubspace 1 N)ᗮ` retains
`(7/8) D_M`, `(g₀ / (8 c⁷)) log N · S₇`, `(c c_W / R_max) W₈(U_y)`, and `(c / (4 I₂)) levyEnergy U_y`
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
                  (c / (4 * ∫ u, tiltedUnitSpline u ^ 2)) * levyEnergy U_y -
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
  have hκ0 : 0 ≤ splineWindowConstant := splineWindowConstant_nonneg
  set K_win := splineWindowConstant * 8 * Real.exp 2 * C_pole + 1
  have hK_win : 0 < K_win := by positivity
  set ε_pr := I₂ * c_W0 / (4 * R_max)
  have hε_pr : 0 < ε_pr := by positivity
  set ε_win := c_W0 / (4 * R_max * K_win)
  have hε_win : 0 < ε_win := by positivity
  have h0_mv := vonMangoldtThreeHalvesMass_nonneg
  set B_pr := 2 * vonMangoldtThreeHalvesMass +
    (2 * vonMangoldtThreeHalvesMass) ^ 2 * Real.exp 8 / ε_pr
  obtain ⟨B_far, hB_far, hB_sum⟩ :
      ∃ B_far : ℝ, 0 < B_far ∧
        (B_arch / 2 + 2 * Real.pi + (factorialSpanGammaOffset + Real.log 2) / 4 +
          |gammaHardyPhaseRate 0| / 2 + 2 + B_pr) / I₂ + K_win * (4 + 2 / ε_win) ≤ B_far := by
    refine ⟨(B_arch / 2 + 2 * Real.pi + (factorialSpanGammaOffset + Real.log 2) / 4 +
        |gammaHardyPhaseRate 0| / 2 + 2 + B_pr) / I₂ + K_win * (4 + 2 / ε_win) + 1, ?_, by linarith⟩
    have hG₀ : 0 ≤ factorialSpanGammaOffset := factorialSpanGammaOffset_nonneg
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨B_far, hB_far, ?_⟩
  set K_c : ℝ := (R_max + 1) ^ (1 / 8 : ℝ)
  set C_β : ℝ := 1 + 36 / c₀ ^ 2 + |Real.log t₀|
  set C_tr : ℝ := (1 + 2 * Real.exp 2) *
    (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4))
  set C_P0 : ℝ := 1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost +
    (Real.log 4 + 4) + 2 * Real.pi
  set θ_P : ℝ := 1 / (16 * explicitConductorCutoffConstant)
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLN_zero : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hev_L2N : ∀ᶠ N : ℕ in atTop,
      2 * ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)) * Real.log (N : ℝ) ≤ N := by
    set A := 2 * ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1))
    have hA : 0 < A := by positivity
    have hev := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / A))
    filter_upwards [hev, eventually_ge_atTop 1] with N hlt hN1
    dsimp only [Function.comp_def] at hlt
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hm := (div_lt_iff₀ hN0).mp hlt
    have hid : 1 / A * (N : ℝ) = (N : ℝ) / A := by field_simp
    exact ((le_div_iff₀ hA).mp (by linarith)).trans_eq' (mul_comm _ _)
  have hev_err : ∀ᶠ N : ℕ in atTop,
      C_err * ((R_max + 1) * Real.log (N : ℝ) / N) ≤ dyadicTopMassConstant / (4 * R_max) := by
    by_cases hCerr : 0 < C_err
    · set A := C_err * (R_max + 1)
      have hA : 0 < A := by positivity
      have hev := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
        (gt_mem_nhds (div_pos (div_pos hg₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hR)) hA))
      filter_upwards [hev] with N hlt
      dsimp only [Function.comp_def] at hlt
      have hm := (lt_div_iff₀ hA).mp hlt
      linarith only [hm, (by ring : C_err * ((R_max + 1) * Real.log (N : ℝ) / N) =
        (Real.log (N : ℝ) / N) * A)]
    · have h0 : C_err = 0 := le_antisymm (not_lt.mp hCerr) hC_err0
      filter_upwards with N; rw [h0]; simp only [zero_mul]; positivity
  filter_upwards [
    hev_L2N, hev_err,
    hLlim.eventually (eventually_ge_atTop (max 4 (R_max + 1))),
    hLlim.eventually ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 16)).eventually_ge_atTop
      (factorialSpanGammaOffset + Real.log (4 * C_ψ + 1) + 4)),
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
  intro c hc1 hc8 z hz
  have hlogL_ub : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) ^ (3 / 16 : ℝ) := by
    have h1 : 1 + Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) ^ (3 / 16 : ℝ) := by
      simpa only [one_mul, Real.rpow_zero, pow_one] using hlogL_316
    linarith only [h1]
  have hexp_b' : (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset + C_β) *
      Real.log (N : ℝ) ^ (3 / 8 : ℝ) ≤ Real.log (N : ℝ) := by
    have hp : (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset + C_β) *
        Real.log (N : ℝ) ^ (3 / 8 : ℝ) * (1 + Real.log (Real.log (N : ℝ))) ≤ Real.log (N : ℝ) := by
      simpa only [pow_one, Real.rpow_one] using hexp_b
    have hL1 : 1 ≤ Real.log (N : ℝ) := by linarith [(le_max_left 4 (R_max + 1)).trans hL_ge]
    have hℓ1 : 1 ≤ 1 + Real.log (Real.log (N : ℝ)) := by linarith [Real.log_nonneg hL1]
    have hC0 : 0 ≤ (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset + C_β) *
        Real.log (N : ℝ) ^ (3 / 8 : ℝ) := by
      have := factorialSpanGammaOffset_nonneg
      dsimp only [C_β]; positivity
    exact (le_mul_of_one_le_right hC0 hℓ1).trans hp
  exact far_garding_at_N hR hC_err0 hCψ hc₀ ht₀1 hpnt harch_g hB_sum hN3 hc1 hc8 hz
    hL2N_b herr_b hL_ge hL316_C hlogL_ub
    (by simpa only [Real.rpow_one] using hP_a)
    (by simpa only [Real.rpow_one] using hP_b)
    (by simpa only [Real.rpow_one] using hP_c)
    hexp_b'

/-! ### 4. All-ratio complement Gårding and deterministic far-sector bridge -/

private lemma subexpCutoff_all_ratio_bounds {N : ℕ} {D : ℝ} (hD : 0 < D) (hN1 : 1 ≤ N)
    (hL3000 : 3000 ≤ Real.log (N : ℝ))
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ))
    (hpoly5 : 2 * (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤ Real.log (N : ℝ) ^ (1 / 4 : ℝ))
    (hL34_D : 4 * D + 4 ≤ Real.log (N : ℝ) ^ (3 / 4 : ℝ)) :
    ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ ≤ subexpCutoff N ∧
    1 + Real.log (subexpCutoff N : ℝ) ≤
      2 * Real.log (N : ℝ) / (1 + Real.log (Real.log (N : ℝ))) ^ 5 ∧
    1080 * (1 + Real.log (subexpCutoff N : ℝ)) ≤ Real.log (N : ℝ) ∧
    Real.log (N : ℝ) / (2 * D * (1 + Real.log (Real.log (N : ℝ))) ^ 5) ≤
      Real.log (subexpCutoff N : ℝ) / D - 1 ∧
    Real.log (subexpCutoff N : ℝ) / D - 1 ≤
      Real.log (N : ℝ) / (D * (1 + Real.log (Real.log (N : ℝ))) ^ 5) ∧
    Real.log (N : ℝ) ^ 18 * (subexpCutoff N : ℝ) ^ 16 ≤ N := by
  set L : ℝ := Real.log (N : ℝ) with hLdef
  set ℓ : ℝ := 1 + Real.log L with hℓdef
  have hL1 : 1 ≤ L := by linarith only [hL3000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1R
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hℓ5_pos : 0 < ℓ ^ 5 := pow_pos hℓ0 5
  have hL_split : L ^ (1 / 4 : ℝ) * L ^ (3 / 4 : ℝ) = L := by
    rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  have h2L34 : 2 * L ^ (3 / 4 : ℝ) ≤ L / ℓ ^ 5 := by
    rw [le_div_iff₀ hℓ5_pos]
    have hm := mul_le_mul_of_nonneg_left hpoly5 (Real.rpow_nonneg hL0.le (3 / 4))
    linarith only [hm, hL_split,
      (by ring : L ^ (3 / 4 : ℝ) * (2 * ℓ ^ 5) = 2 * L ^ (3 / 4 : ℝ) * ℓ ^ 5),
      (by ring : L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L ^ (1 / 4 : ℝ) * L ^ (3 / 4 : ℝ))]
  have hL34_le : L ^ (3 / 4 : ℝ) ≤ L / ℓ ^ 5 := by
    linarith only [h2L34, Real.rpow_nonneg hL0.le (3 / 4)]
  have hLh_le : L ^ (1 / 2 : ℝ) ≤ L / ℓ ^ 5 :=
    (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans hL34_le
  have hR₀R₁ : ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ ≤ subexpCutoff N := by
    rw [subexpCutoff, ← hLdef, ← hℓdef]
    exact Nat.floor_mono (Real.exp_le_exp.mpr hLh_le)
  have hx4 : 4 * D + 4 ≤ L / ℓ ^ 5 := hL34_D.trans hL34_le
  have hexp_ge5 : 5 ≤ Real.exp (L / ℓ ^ 5) := by
    linarith only [Real.add_one_le_exp (L / ℓ ^ 5), hx4, hD]
  have hR₁_le_exp : (subexpCutoff N : ℝ) ≤ Real.exp (L / ℓ ^ 5) := by
    rw [subexpCutoff, ← hLdef, ← hℓdef]; exact Nat.floor_le (Real.exp_pos _).le
  have hhalf_exp : (1 / 2 : ℝ) * Real.exp (L / ℓ ^ 5) ≤ (subexpCutoff N : ℝ) := by
    have hgt : Real.exp (L / ℓ ^ 5) - 1 < (subexpCutoff N : ℝ) := by
      rw [subexpCutoff, ← hLdef, ← hℓdef]
      exact sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    linarith only [hgt, hexp_ge5]
  have hR₁_pos : (0 : ℝ) < subexpCutoff N := by linarith only [hhalf_exp, hexp_ge5]
  have hlogR₁_ub : Real.log (subexpCutoff N : ℝ) ≤ L / ℓ ^ 5 :=
    (Real.log_le_log hR₁_pos hR₁_le_exp).trans_eq (Real.log_exp _)
  have hlogR₁_lb : L / ℓ ^ 5 - 1 ≤ Real.log (subexpCutoff N : ℝ) := by
    have hdiv_exp : Real.exp (L / ℓ ^ 5) / 2 ≤ (subexpCutoff N : ℝ) := by linarith only [hhalf_exp]
    have h1 := Real.log_le_log (by positivity) hdiv_exp
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [h1, hlog2]
  have h1_ub : 1 + Real.log (subexpCutoff N : ℝ) ≤ 2 * L / ℓ ^ 5 := by
    rw [mul_div_assoc]; linarith only [hlogR₁_ub, hx4, hD]
  have hℓ_ge5 : 5 ≤ ℓ := by
    have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have he4 : Real.exp 4 ≤ L := by
      have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      have hp : (Real.exp 1) ^ 4 ≤ 81 :=
        (pow_le_pow_left₀ (Real.exp_pos 1).le he1 4).trans_eq (by norm_num)
      linarith only [h4, hp, hL3000]
    have hl4 : 4 ≤ Real.log L := (Real.log_exp 4).symm.trans_le (Real.log_le_log (by positivity) he4)
    rw [hℓdef]; linarith only [hl4]
  have hℓ5_3125 : (3125 : ℝ) ≤ ℓ ^ 5 :=
    calc (3125 : ℝ) = 5 ^ 5 := by norm_num
      _ ≤ ℓ ^ 5 := pow_le_pow_left₀ (by norm_num) hℓ_ge5 5
  have hx_3125 : L / ℓ ^ 5 ≤ L / 3125 :=
    div_le_div_of_nonneg_left hL0.le (by norm_num) hℓ5_3125
  have h1080 : 1080 * (1 + Real.log (subexpCutoff N : ℝ)) ≤ L := by
    linarith only [hlogR₁_ub.trans hx_3125, hL3000]
  have hgap_lo : L / (2 * D * ℓ ^ 5) ≤ Real.log (subexpCutoff N : ℝ) / D - 1 := by
    have h34 : (3 / 4 : ℝ) * (L / ℓ ^ 5) ≤ Real.log (subexpCutoff N : ℝ) := by
      linarith only [hlogR₁_lb, hx4, hD]
    have hdiv := div_le_div_of_nonneg_right h34 hD.le
    have h1' : 1 ≤ (1 / 4 : ℝ) * (L / ℓ ^ 5) / D :=
      (le_div_iff₀ hD).mpr (by linarith only [hx4])
    have hid : (3 / 4 : ℝ) * (L / ℓ ^ 5) / D =
        L / (2 * D * ℓ ^ 5) + (1 / 4 : ℝ) * (L / ℓ ^ 5) / D := by
      field_simp [hD.ne', hℓ5_pos.ne']; ring
    linarith only [hdiv, h1', hid]
  have hgap_hi : Real.log (subexpCutoff N : ℝ) / D - 1 ≤ L / (D * ℓ ^ 5) := by
    have hdiv := div_le_div_of_nonneg_right hlogR₁_ub hD.le
    rw [div_div] at hdiv
    linarith only [hdiv, (by ring : L / (ℓ ^ 5 * D) = L / (D * ℓ ^ 5))]
  have hRN₁ : L ^ 18 * (subexpCutoff N : ℝ) ^ 16 ≤ N := by
    have hR₁_N : (subexpCutoff N : ℝ) ≤ (N : ℝ) ^ (1 / 3125 : ℝ) := by
      calc (subexpCutoff N : ℝ) ≤ Real.exp (L / ℓ ^ 5) := hR₁_le_exp
        _ ≤ Real.exp (L / 3125) := Real.exp_le_exp.mpr hx_3125
        _ = (N : ℝ) ^ (1 / 3125 : ℝ) := by rw [Real.rpow_def_of_pos hN0, hLdef]; congr 1; ring
    have hR16 : (subexpCutoff N : ℝ) ^ 16 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      calc (subexpCutoff N : ℝ) ^ 16 ≤ ((N : ℝ) ^ (1 / 3125 : ℝ)) ^ 16 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hR₁_N 16
        _ = (N : ℝ) ^ (16 / 3125 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
        _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
    have hL18 : L ^ 18 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      calc L ^ 18 ≤ ((N : ℝ) ^ (1 / 36 : ℝ)) ^ 18 := pow_le_pow_left₀ hL0.le hLX 18
        _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    calc L ^ 18 * (subexpCutoff N : ℝ) ^ 16 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul hL18 hR16 (by positivity) (by positivity)
      _ = N := by rw [← Real.rpow_add hN0]; norm_num [Real.rpow_one]
  exact ⟨hR₀R₁, h1_ub, h1080, hgap_lo, hgap_hi, hRN₁⟩

private lemma subexp_far_collar_reserve_all_ratio {N : ℕ} {c D g₀ CB K_c E_extra : ℝ}
    (hD_eq : D = explicitConductorCutoffConstant)
    (hD : 0 < D) (hg₀ : 0 < g₀) (hCB0 : 0 ≤ CB) (hKc1 : 1 ≤ K_c)
    (hc1 : 1 ≤ c) (hc_up : c ≤ K_c * Real.log (N : ℝ) ^ (1 / 8 : ℝ))
    (hL2 : 2 ≤ Real.log (N : ℝ))
    (hR₁2 : 2 ≤ subexpCutoff N)
    (hM2 : 2 ≤ N / linearDefectCutoff c)
    (hRM1 : subexpCutoff N * subexpCutoff N ≤ N / linearDefectCutoff c)
    (hlogM1 : 18 * (1 + Real.log (subexpCutoff N : ℝ)) ≤ Real.log (N / linearDefectCutoff c : ℕ))
    (hhalf_M : Real.log (N : ℝ) / 2 ≤ Real.log (N / linearDefectCutoff c : ℕ))
    (hB1_ub : terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N ≤
      CB * (1 + Real.log c))
    (h1c_ℓ : 1 + Real.log c ≤ 1 + Real.log (Real.log (N : ℝ)))
    (hgap_lo : Real.log (N : ℝ) / (2 * D * (1 + Real.log (Real.log (N : ℝ))) ^ 5) ≤
      Real.log (subexpCutoff N : ℝ) / D - 1)
    (hgap_hi : Real.log (subexpCutoff N : ℝ) / D - 1 ≤
      Real.log (N : ℝ) / (D * (1 + Real.log (Real.log (N : ℝ))) ^ 5))
    (hℓ_leak : 56 * CB * K_c ^ 7 / (D * g₀) ≤ 1 + Real.log (Real.log (N : ℝ)))
    {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hw : w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ)
    (hfarw :
      (7 / 8 : ℝ) * poleDefect (N / linearDefectCutoff c) (primeHorizonExtension w) +
        (g₀ / (8 * c ^ 7)) * Real.log (N : ℝ) *
          topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) -
        ((1 / (16 * D)) * Real.log (N : ℝ) / (1 + Real.log (Real.log (N : ℝ))) ^ 5) *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) ≤
        E_extra) :
    (Real.log (N : ℝ) / (2 * D * (1 + Real.log (Real.log (N : ℝ))) ^ 5) / 4) *
        (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
      (g₀ * Real.log (N : ℝ) / (16 * c ^ 7)) *
        topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤ E_extra := by
  set L : ℝ := Real.log (N : ℝ) with hLdef
  set ℓ : ℝ := 1 + Real.log L with hℓdef
  have hL0 : 0 < L := by linarith only [hL2]
  have hL1 : 1 ≤ L := by linarith only [hL2]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hKc0 : 0 < K_c := zero_lt_one.trans_le hKc1
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hk_pos : 0 < L / (2 * D * ℓ ^ 5) := by positivity
  have hscale : explicitConductorCutoffConstant ≤ Real.log (subexpCutoff N : ℝ) := by
    rw [← hD_eq]
    have h1 : 1 ≤ Real.log (subexpCutoff N : ℝ) / D := by linarith only [hgap_lo, hk_pos]
    simpa only [one_mul] using (le_div_iff₀ hD).mp h1
  have hpre := poleDefect_prefix_ge_of_conductor_orthogonal hR₁2 hM2 (Nat.div_le_self _ _) hRM1
    hlogM1 hscale hw
  rw [← hD_eq, mul_div_assoc] at hpre
  have hSw_le := sum_sq_Ioc_le_topCollarSeventhMass (N / linearDefectCutoff c) N
    (primeHorizonExtension w)
  have hP0 : 0 ≤ ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ ∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hS7_0 : 0 ≤ topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) :=
    hS0.trans hSw_le
  have hlogM_pos : 0 < Real.log (N / linearDefectCutoff c : ℕ) := by linarith only [hhalf_M, hL0]
  have hB_le : terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
      Real.log (N / linearDefectCutoff c : ℕ) ≤ 2 * CB * ℓ / L := by
    rw [div_le_div_iff₀ hlogM_pos hL0]
    have h1 : terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N ≤ CB * ℓ :=
      hB1_ub.trans (mul_le_mul_of_nonneg_left h1c_ℓ hCB0)
    have h0 := terminalPacketCost_nonneg (subexpCutoff N) (Nat.div_le_self N (linearDefectCutoff c))
    nlinarith only [h1, h0, hhalf_M, hL0, mul_nonneg hCB0 hℓ0.le]
  have hB0 : 0 ≤ terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
      Real.log (N / linearDefectCutoff c : ℕ) :=
    div_nonneg (terminalPacketCost_nonneg _ (Nat.div_le_self _ _)) hlogM_pos.le
  have hc7_L : c ^ 7 ≤ K_c ^ 7 * L := by
    have hp := pow_le_pow_left₀ hc0.le hc_up 7
    rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
    have h78 : L ^ ((1 / 8 : ℝ) * (7 : ℕ)) ≤ L :=
      (Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; norm_num)).trans_eq (Real.rpow_one L)
    exact hp.trans (mul_le_mul_of_nonneg_left h78 (by positivity))
  have hleak : (7 / 4 : ℝ) * (Real.log (subexpCutoff N : ℝ) / D - 1) *
      (terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
        Real.log (N / linearDefectCutoff c : ℕ)) ≤ g₀ * L / (16 * c ^ 7) := by
    have h1 : (7 / 4 : ℝ) * (Real.log (subexpCutoff N : ℝ) / D - 1) *
        (terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
          Real.log (N / linearDefectCutoff c : ℕ)) ≤
        (7 / 4 : ℝ) * (L / (D * ℓ ^ 5)) * (2 * CB * ℓ / L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hgap_hi (by norm_num)) hB_le hB0 (by positivity)
    have h2 : (7 / 4 : ℝ) * (L / (D * ℓ ^ 5)) * (2 * CB * ℓ / L) =
        (7 * CB / (2 * D)) / ℓ ^ 4 := by
      field_simp [hD.ne', hℓ0.ne', hL0.ne']; ring
    have h3 : (7 * CB / (2 * D)) / ℓ ^ 4 ≤ (7 * CB / (2 * D)) / ℓ :=
      div_le_div_of_nonneg_left (by positivity) hℓ0
        (by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 4))
    have h4 : (7 * CB / (2 * D)) / ℓ ≤ g₀ / (16 * K_c ^ 7) := by
      rw [div_le_iff₀ hℓ0]
      have hm := mul_le_mul_of_nonneg_left hℓ_leak (by positivity : 0 ≤ g₀ / (16 * K_c ^ 7))
      have hid : (g₀ / (16 * K_c ^ 7)) * (56 * CB * K_c ^ 7 / (D * g₀)) = 7 * CB / (2 * D) := by
        field_simp [hD.ne', hg₀.ne', hKc0.ne']; ring
      linarith only [hm, hid]
    have h5 : g₀ / (16 * K_c ^ 7) ≤ g₀ * L / (16 * c ^ 7) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hc7_L, hg₀]
    exact h1.trans (h2.trans_le (h3.trans (h4.trans h5)))
  generalize (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) = P
    at hpre hfarw hP0 ⊢
  generalize (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) = S
    at hpre hSw_le hS0
  generalize topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) = S7
    at hfarw hSw_le hS7_0 ⊢
  generalize (Real.log (subexpCutoff N : ℝ) / D - 1) = kg at hpre hgap_lo hleak
  generalize (terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
    Real.log (N / linearDefectCutoff c : ℕ)) = Bp at hpre hleak
  have hpre' : (15 / 16 : ℝ) * (kg * P) - 2 * (kg * Bp * S) ≤
      poleDefect (N / linearDefectCutoff c) (primeHorizonExtension w) := by
    linarith only [hpre,
      (by ring : kg * ((15 / 16 : ℝ) * P - 2 * Bp * S) =
        (15 / 16 : ℝ) * (kg * P) - 2 * (kg * Bp * S))]
  have hP1 := mul_le_mul_of_nonneg_right hgap_lo hP0
  have hS1 := mul_le_mul_of_nonneg_left hSw_le (by positivity : 0 ≤ g₀ * L / (16 * c ^ 7))
  have hS2 : (7 / 4 : ℝ) * (kg * Bp * S) ≤ (g₀ * L / (16 * c ^ 7)) * S7 := by
    have hm := mul_le_mul_of_nonneg_right hleak hS0
    exact ((by ring : (7 / 4 : ℝ) * (kg * Bp * S) = (7 / 4 : ℝ) * kg * Bp * S).trans_le hm).trans hS1
  have hid_far : (1 / (16 * D)) * L / ℓ ^ 5 = (1 / 8 : ℝ) * (L / (2 * D * ℓ ^ 5)) := by
    field_simp [hD.ne', hℓ0.ne']; ring
  have hid_top : (g₀ / (8 * c ^ 7)) * L = 2 * (g₀ * L / (16 * c ^ 7)) := by
    field_simp [hc0.ne']; ring
  rw [hid_far, hid_top] at hfarw
  have hkp : 0 ≤ (L / (2 * D * ℓ ^ 5)) * P := mul_nonneg hk_pos.le hP0
  linarith only [hpre', hfarw, hP1, hS2, hkp,
    (by ring : 2 * (g₀ * L / (16 * c ^ 7)) * S7 = 2 * ((g₀ * L / (16 * c ^ 7)) * S7)),
    (by ring : (1 / 8 : ℝ) * (L / (2 * D * ℓ ^ 5)) * P =
      (1 / 8 : ℝ) * ((L / (2 * D * ℓ ^ 5)) * P)),
    (by ring : (L / (2 * D * ℓ ^ 5) / 4) * P =
      (1 / 4 : ℝ) * ((L / (2 * D * ℓ ^ 5)) * P))]

private lemma all_ratio_c7_div_bk_le {c k b L ℓ D g₀ K_c : ℝ}
    (hD : 0 < D) (hg₀ : 0 < g₀) (hL1 : 1 ≤ L) (hℓ1 : 1 ≤ ℓ)
    (hc1 : 1 ≤ c) (hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ)) (hKc1 : 1 ≤ K_c)
    (hk_def : k = L / (2 * D * ℓ ^ 6))
    (hb_def : b = min (c ^ 7) ((g₀ * D / 4) * ℓ ^ 5))
    (hpoly : 2 * D * ℓ ^ 5 ≤ L ^ (7 / 8 : ℝ)) :
    c ^ 7 / (b * k) ≤ (1 + 8 * K_c ^ 7 / g₀) * ℓ / L ^ (1 / 8 : ℝ) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hKc0 : 0 < K_c := zero_lt_one.trans_le hKc1
  have hL8_pos : 0 < L ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hsplit : L ^ (7 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L := by
    rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  by_cases hmin : c ^ 7 ≤ (g₀ * D / 4) * ℓ ^ 5
  · have hb_eq : b = c ^ 7 := by rw [hb_def, min_eq_left hmin]
    have h1 : c ^ 7 / (b * k) = 2 * D * ℓ ^ 6 / L := by
      rw [hb_eq, hk_def]; field_simp [hc0.ne', hL0.ne', hD.ne', hℓ0.ne']
    have h2 : 2 * D * ℓ ^ 6 / L ≤ ℓ / L ^ (1 / 8 : ℝ) := by
      rw [div_le_div_iff₀ hL0 hL8_pos]
      calc 2 * D * ℓ ^ 6 * L ^ (1 / 8 : ℝ)
          = (2 * D * ℓ ^ 5) * (ℓ * L ^ (1 / 8 : ℝ)) := by ring
        _ ≤ L ^ (7 / 8 : ℝ) * (ℓ * L ^ (1 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_right hpoly (by positivity)
        _ = ℓ * (L ^ (7 / 8 : ℝ) * L ^ (1 / 8 : ℝ)) := by ring
        _ = ℓ * L := by rw [hsplit]
    have h3 : ℓ / L ^ (1 / 8 : ℝ) ≤ (1 + 8 * K_c ^ 7 / g₀) * ℓ / L ^ (1 / 8 : ℝ) := by
      rw [mul_div_assoc]
      exact le_mul_of_one_le_left (by positivity) (by linarith [show 0 ≤ 8 * K_c ^ 7 / g₀ by positivity])
    exact h1.trans_le (h2.trans h3)
  · have hmin' : (g₀ * D / 4) * ℓ ^ 5 ≤ c ^ 7 := le_of_not_ge hmin
    have hb_eq : b = (g₀ * D / 4) * ℓ ^ 5 := by rw [hb_def, min_eq_right hmin']
    have hbk : b * k = g₀ * L / (8 * ℓ) := by
      rw [hb_eq, hk_def]; field_simp [hD.ne', hℓ0.ne']; ring
    have hc7 : c ^ 7 ≤ K_c ^ 7 * L ^ (7 / 8 : ℝ) := by
      have hp := pow_le_pow_left₀ hc0.le hc_up 7
      rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
      exact hp.trans_eq (by congr 2; push_cast; ring)
    have h1 : c ^ 7 / (b * k) ≤ (8 * K_c ^ 7 / g₀) * ℓ / L ^ (1 / 8 : ℝ) := by
      rw [hbk, show c ^ 7 / (g₀ * L / (8 * ℓ)) = 8 * c ^ 7 * ℓ / (g₀ * L) by
        field_simp [hg₀.ne', hL0.ne', hℓ0.ne'],
        div_le_div_iff₀ (by positivity) hL8_pos]
      calc 8 * c ^ 7 * ℓ * L ^ (1 / 8 : ℝ)
          = 8 * (c ^ 7 * (ℓ * L ^ (1 / 8 : ℝ))) := by ring
        _ ≤ 8 * ((K_c ^ 7 * L ^ (7 / 8 : ℝ)) * (ℓ * L ^ (1 / 8 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc7 (by positivity)) (by norm_num)
        _ = 8 * K_c ^ 7 * ℓ * (L ^ (7 / 8 : ℝ) * L ^ (1 / 8 : ℝ)) := by ring
        _ = 8 * K_c ^ 7 * ℓ * L := by rw [hsplit]
        _ = (8 * K_c ^ 7 / g₀) * ℓ * (g₀ * L) := by field_simp [hg₀.ne']
    have h2 : (8 * K_c ^ 7 / g₀) * ℓ / L ^ (1 / 8 : ℝ) ≤
        (1 + 8 * K_c ^ 7 / g₀) * ℓ / L ^ (1 / 8 : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hℓ0.le) hL8_pos.le
    exact h1.trans h2

private lemma all_ratio_band_far_budget_E {R M N : ℕ}
    {c Sg₁ k b L ℓ D CB K_c M_bk C_pr C_np K_tot : ℝ}
    (hLdef : L = Real.log (N : ℝ)) (hℓdef : ℓ = 1 + Real.log L)
    (hk_def : k = L / (2 * D * ℓ ^ 6))
    (hbk_ub : c ^ 7 / (b * k) ≤ M_bk * ℓ / L ^ (1 / 8 : ℝ))
    (hD : 0 < D) (hCpr : 0 < C_pr) (hCnp : 0 ≤ C_np) (hCB0 : 0 ≤ CB)
    (hKc1 : 1 ≤ K_c) (hMbk0 : 0 ≤ M_bk) (hK_tot : 1 ≤ K_tot)
    (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hcL : c ≤ L) (hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ))
    (hk_pos : 0 < k) (hb_pos : 0 < b)
    (hR1 : 1 ≤ R) (hMN : M ≤ N) (hRN : L ^ 18 * (R : ℝ) ^ 16 ≤ N)
    (hlR : 1 + Real.log (R : ℝ) ≤ 2 * L / ℓ ^ 5)
    (hTPC : terminalPacketCost R M N ≤ CB * (1 + Real.log c))
    (hSg : Sg₁ ≤ 2 * K_tot * ℓ) (hSg0 : 0 ≤ Sg₁)
    (hℓ_E : 128 * (1024 * D * C_pr + 32 * C_np * M_bk * (8 * K_c * K_tot ^ 2 + 6)) ≤ ℓ)
    (hL8_E2 : 128 * (256 * C_pr * CB * M_bk) ≤ L ^ (1 / 8 : ℝ)) :
    128 * C_pr * (1 + Real.log (R : ℝ)) ^ 2 / (Real.log (N : ℝ) * k) +
      128 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N /
        (Real.log (N : ℝ) * b * k) +
      32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k) ≤ 1 / 32 := by
  rw [← hLdef]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hKc0 : 0 < K_c := zero_lt_one.trans_le hKc1
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hR1R : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hRN
  have h1c_ℓ : 1 + Real.log c ≤ ℓ := by rw [hℓdef]; linarith [Real.log_le_log hc0 hcL]
  have h1c0 : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hL8_pos : 0 < L ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hLk : L * k = L ^ 2 / (2 * D * ℓ ^ 6) := by rw [hk_def]; ring
  have hbk0 : 0 ≤ c ^ 7 / (b * k) := div_nonneg (pow_nonneg hc0.le 7) (mul_pos hb_pos hk_pos).le
  have hE1 : 128 * C_pr * (1 + Real.log (R : ℝ)) ^ 2 / (L * k) ≤ (1024 * D * C_pr) / ℓ := by
    have hlR0 : 0 ≤ 1 + Real.log (R : ℝ) := by linarith [Real.log_natCast_nonneg R]
    have hsq : (1 + Real.log (R : ℝ)) ^ 2 ≤ (2 * L / ℓ ^ 5) ^ 2 := pow_le_pow_left₀ hlR0 hlR 2
    calc 128 * C_pr * (1 + Real.log (R : ℝ)) ^ 2 / (L * k)
        ≤ 128 * C_pr * (2 * L / ℓ ^ 5) ^ 2 / (L ^ 2 / (2 * D * ℓ ^ 6)) := by
            rw [hLk]; exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)
      _ = (1024 * D * C_pr) / ℓ ^ 4 := by field_simp [hL0.ne', hD.ne', hℓ0.ne']; ring
      _ ≤ (1024 * D * C_pr) / ℓ := div_le_div_of_nonneg_left (by positivity) hℓ0
            (by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 4))
  have hE2 : 128 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N /
      (L * b * k) ≤ 1 / 128 := by
    have hTPC_ℓ : terminalPacketCost R M N ≤ CB * ℓ :=
      hTPC.trans (mul_le_mul_of_nonneg_left h1c_ℓ hCB0)
    have hTPC0 : 0 ≤ terminalPacketCost R M N := terminalPacketCost_nonneg R hMN
    have hid : 128 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N /
        (L * b * k) = 128 * C_pr * ((1 + Real.log (R : ℝ)) / L) *
          terminalPacketCost R M N * (c ^ 7 / (b * k)) := by ring
    have hRL : (1 + Real.log (R : ℝ)) / L ≤ 2 / ℓ ^ 5 := by
      rw [div_le_div_iff₀ hL0 (pow_pos hℓ0 5)]
      linarith only [hlR, (le_div_iff₀ (pow_pos hℓ0 5)).mp hlR]
    rw [hid]
    have hm1 := mul_le_mul hRL hTPC_ℓ hTPC0 (by positivity)
    have hm2 := mul_le_mul hm1 hbk_ub hbk0 (mul_nonneg (by positivity) (mul_nonneg hCB0 hℓ0.le))
    have hm3 := mul_le_mul_of_nonneg_left hm2 (by positivity : 0 ≤ 128 * C_pr)
    have hsimp : 128 * C_pr * ((2 / ℓ ^ 5) * (CB * ℓ) * (M_bk * ℓ / L ^ (1 / 8 : ℝ))) =
        (256 * C_pr * CB * M_bk / L ^ (1 / 8 : ℝ)) / ℓ ^ 3 := by
      field_simp [hℓ0.ne', hL8_pos.ne']; ring
    have hℓ3 : 1 ≤ ℓ ^ 3 := one_le_pow₀ hℓ1
    calc 128 * C_pr * ((1 + Real.log (R : ℝ)) / L) * terminalPacketCost R M N * (c ^ 7 / (b * k))
        ≤ 128 * C_pr * ((2 / ℓ ^ 5) * (CB * ℓ) * (M_bk * ℓ / L ^ (1 / 8 : ℝ))) := by
            linarith only [hm3, (by ring : 128 * C_pr * (((1 + Real.log (R : ℝ)) / L) *
              terminalPacketCost R M N * (c ^ 7 / (b * k))) =
              128 * C_pr * ((1 + Real.log (R : ℝ)) / L) * terminalPacketCost R M N *
                (c ^ 7 / (b * k)))]
      _ = (256 * C_pr * CB * M_bk / L ^ (1 / 8 : ℝ)) / ℓ ^ 3 := hsimp
      _ ≤ 256 * C_pr * CB * M_bk / L ^ (1 / 8 : ℝ) :=
            div_le_self (div_nonneg (mul_nonneg (mul_nonneg (by positivity) hCB0) hMbk0) hL8_pos.le) hℓ3
      _ ≤ 1 / 128 := by rw [div_le_iff₀ hL8_pos]; linarith only [hL8_E2]
  have hE3 : 32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k) ≤
      (32 * C_np * M_bk * (8 * K_c * K_tot ^ 2 + 6)) / ℓ := by
    have h1L_le : 1 / L ≤ 1 / L := le_rfl
    have hc6N : c ^ 6 / N ≤ 1 / L := by
      have h := cpow_Rpow_div_le hL1 hc0.le hcL hR1R hRN h1L_le (i := 6) (j := 0)
        (by norm_num) (by norm_num)
      simpa only [pow_zero, mul_one] using h
    have hc4N : c ^ 4 * (R : ℝ) ^ 4 / (N * L) ≤ 1 / L := by
      exact (div_le_div_of_nonneg_left (by positivity) hN0 (le_mul_of_one_le_right hN0.le hL1)).trans
        (cpow_Rpow_div_le hL1 hc0.le hcL hR1R hRN h1L_le (i := 4) (j := 4)
          (by norm_num) (by norm_num))
    have hSg2 : Sg₁ ^ 2 ≤ 4 * K_tot ^ 2 * ℓ ^ 2 :=
      (pow_le_pow_left₀ hSg0 hSg 2).trans_eq (by ring)
    have hL8_1 : 1 ≤ L ^ (1 / 8 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hℓ3_1 : 1 ≤ ℓ ^ 3 := one_le_pow₀ hℓ1
    have hG_ub : bandFarBudgetG R N c Sg₁ ≤
        (8 * K_c * K_tot ^ 2 + 6) * L ^ (1 / 8 : ℝ) / ℓ ^ 2 := by
      have hmid : (1 + Real.log c) / L +
          c * Sg₁ ^ 2 * (1 + Real.log c) / L + c ^ 6 / N + c ^ 4 * (R : ℝ) ^ 4 / (N * L) ≤
          (4 * K_c * K_tot ^ 2 + 3) * L ^ (1 / 8 : ℝ) * ℓ ^ 3 / L := by
        have ht1 : (1 + Real.log c) / L ≤ L ^ (1 / 8 : ℝ) * ℓ ^ 3 / L := by
          refine div_le_div_of_nonneg_right ?_ hL0.le
          have hℓ_3 : ℓ ≤ ℓ ^ 3 := by
            simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 3)
          exact (h1c_ℓ.trans hℓ_3).trans (le_mul_of_one_le_left (by positivity) hL8_1)
        have ht2 : c * Sg₁ ^ 2 * (1 + Real.log c) / L ≤
            4 * K_c * K_tot ^ 2 * L ^ (1 / 8 : ℝ) * ℓ ^ 3 / L := by
          refine div_le_div_of_nonneg_right ?_ hL0.le
          have hm := mul_le_mul (mul_le_mul hc_up hSg2 (sq_nonneg _) (by positivity))
            h1c_ℓ h1c0 (by positivity)
          exact hm.trans_eq (by ring)
        have ht3 : c ^ 6 / N + c ^ 4 * (R : ℝ) ^ 4 / (N * L) ≤
            2 * L ^ (1 / 8 : ℝ) * ℓ ^ 3 / L := by
          have h2 : (2 : ℝ) / L ≤ 2 * L ^ (1 / 8 : ℝ) * ℓ ^ 3 / L :=
            div_le_div_of_nonneg_right (by nlinarith only [hL8_1, hℓ3_1]) hL0.le
          linarith only [hc6N, hc4N, h2, (by ring : (1 : ℝ) / L + 1 / L = 2 / L)]
        linarith only [ht1, ht2, ht3,
          (by ring : (4 * K_c * K_tot ^ 2 + 3) * L ^ (1 / 8 : ℝ) * ℓ ^ 3 / L =
            L ^ (1 / 8 : ℝ) * ℓ ^ 3 / L +
              4 * K_c * K_tot ^ 2 * L ^ (1 / 8 : ℝ) * ℓ ^ 3 / L +
              2 * L ^ (1 / 8 : ℝ) * ℓ ^ 3 / L)]
      have hid : bandFarBudgetG R N c Sg₁ = (1 + Real.log (R : ℝ)) *
          ((1 + Real.log c) / L + c * Sg₁ ^ 2 * (1 + Real.log c) / L +
            c ^ 6 / N + c ^ 4 * (R : ℝ) ^ 4 / (N * L)) := by
        unfold bandFarBudgetG; rw [← hLdef]; ring
      rw [hid]
      have hm := mul_le_mul hlR hmid
        (by positivity) (div_nonneg (by positivity) (pow_pos hℓ0 5).le)
      refine hm.trans_eq ?_
      field_simp [hL0.ne', hℓ0.ne']; ring
    have hid : 32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k) =
        32 * C_np * (bandFarBudgetG R N c Sg₁ * (c ^ 7 / (b * k))) := by ring
    rw [hid]
    have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul hG_ub hbk_ub hbk0 (by positivity))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hCnp)
    refine hm.trans_eq ?_
    field_simp [hℓ0.ne', hL8_pos.ne']
  have h13 : (1024 * D * C_pr) / ℓ +
      (32 * C_np * M_bk * (8 * K_c * K_tot ^ 2 + 6)) / ℓ ≤ 1 / 128 := by
    rw [← add_div, div_le_iff₀ hℓ0]; linarith only [hℓ_E]
  linarith only [hE1, hE2, hE3, h13]

private lemma all_ratio_band_far_budget_UA {R N : ℕ}
    {c ρ Sg₁ L ℓ K_c K_tot K_res : ℝ}
    (hLdef : L = Real.log (N : ℝ)) (hℓdef : ℓ = 1 + Real.log L)
    (hKc1 : 1 ≤ K_c) (hK_tot : 1 ≤ K_tot) (hK_res : 0 ≤ K_res)
    (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hcL : c ≤ L) (hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ))
    (hR1 : 1 ≤ R) (hRN : L ^ 18 * (R : ℝ) ^ 16 ≤ N)
    (hlR_2L : 1 + Real.log (R : ℝ) ≤ 2 * L)
    (hSg : Sg₁ ≤ 2 * K_tot * ℓ) (hSg0 : 0 ≤ Sg₁)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 2 * K_res * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L)) :
    bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetA R N c ≤
      (8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) * ℓ ^ 3 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hKc0 : 0 < K_c := zero_lt_one.trans_le hKc1
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hR1R : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hRN
  have h1c_ℓ : 1 + Real.log c ≤ ℓ := by rw [hℓdef]; linarith [Real.log_le_log hc0 hcL]
  have h1c0 : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hc2_up : c ^ 2 ≤ K_c ^ 2 * L ^ (1 / 4 : ℝ) := by
    have hp := pow_le_pow_left₀ hc0.le hc_up 2
    rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
    exact hp.trans_eq (by congr 2; push_cast; ring)
  have hc4_up : c ^ 4 ≤ K_c ^ 4 * L ^ (1 / 2 : ℝ) := by
    have hp := pow_le_pow_left₀ hc0.le hc_up 4
    rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
    exact hp.trans_eq (by congr 2; push_cast; ring)
  have hlRL_sq : ((1 + Real.log (R : ℝ)) / L) ^ 2 ≤ 4 :=
    (pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hL0).mpr hlR_2L) 2).trans_eq (by norm_num)
  have hρ_le : ρ ≤ 2 * K_res * K_c ^ 2 * ℓ ^ 3 := by
    have hm1 := mul_le_mul hc2_up (pow_le_pow_left₀ h1c0 h1c_ℓ 3) (by positivity) (by positivity)
    have hpow : L ^ (1 / 4 : ℝ) * L ^ (1 / 16 : ℝ) ≤ L := by
      rw [← Real.rpow_add hL0]
      exact (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L)
    have hdiv1 : c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L ≤ K_c ^ 2 * ℓ ^ 3 := by
      rw [div_le_iff₀ hL0]
      have hm2 := mul_le_mul_of_nonneg_right hm1 (Real.rpow_nonneg hL0.le (1 / 16))
      have hm3 : K_c ^ 2 * L ^ (1 / 4 : ℝ) * ℓ ^ 3 * L ^ (1 / 16 : ℝ) ≤
          K_c ^ 2 * ℓ ^ 3 * L := by
        have := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ K_c ^ 2 * ℓ ^ 3)
        linarith only [this, (by ring : K_c ^ 2 * L ^ (1 / 4 : ℝ) * ℓ ^ 3 * L ^ (1 / 16 : ℝ) =
          K_c ^ 2 * ℓ ^ 3 * (L ^ (1 / 4 : ℝ) * L ^ (1 / 16 : ℝ)))]
      exact hm2.trans hm3
    exact hρ.trans ((mul_le_mul_of_nonneg_left hdiv1
      (mul_nonneg zero_le_two hK_res)).trans_eq (by ring))
  have ht1 : ((1 + Real.log (R : ℝ)) / L) ^ 2 * ρ ≤ 8 * K_res * K_c ^ 2 * ℓ ^ 3 :=
    (mul_le_mul hlRL_sq hρ_le hρ0 (by norm_num)).trans_eq (by ring)
  have hR15 : (R : ℝ) ^ 15 / N ≤ 1 := by
    rw [div_le_one hN0]
    have h1 : (R : ℝ) ^ 15 ≤ (R : ℝ) ^ 16 := pow_le_pow_right₀ hR1R (by norm_num)
    have h2 : (R : ℝ) ^ 16 ≤ L ^ 18 * (R : ℝ) ^ 16 :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ hL1)
    linarith only [h1, h2, hRN]
  have ht2 : c ^ 2 * (24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) / L ≤
      K_c ^ 2 * (1560 * K_tot + 96) * ℓ ^ 3 := by
    have hcoef : 24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N ≤ (1560 * K_tot + 96) * ℓ := by
      have h72 : 72 * (R : ℝ) ^ 15 / N ≤ 72 := by rw [mul_div_assoc]; linarith only [hR15]
      linarith only [hSg, h72, hℓ1]
    have hm := mul_le_mul hc2_up hcoef (by positivity) (by positivity)
    have hL14 : L ^ (1 / 4 : ℝ) ≤ L :=
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L)
    have hℓ_3 : ℓ ≤ ℓ ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 3)
    rw [div_le_iff₀ hL0]
    have hm2 := mul_le_mul hL14 hℓ_3 hℓ0.le hL0.le
    have hm3 := mul_le_mul_of_nonneg_left hm2 (by positivity : 0 ≤ K_c ^ 2 * (1560 * K_tot + 96))
    linarith only [hm, hm3,
      (by ring : K_c ^ 2 * L ^ (1 / 4 : ℝ) * ((1560 * K_tot + 96) * ℓ) =
        K_c ^ 2 * (1560 * K_tot + 96) * (L ^ (1 / 4 : ℝ) * ℓ)),
      (by ring : K_c ^ 2 * (1560 * K_tot + 96) * (L * ℓ ^ 3) =
        K_c ^ 2 * (1560 * K_tot + 96) * ℓ ^ 3 * L)]
  have ht3 : c ^ 4 * (1 + Real.log c) / L ≤ K_c ^ 4 * ℓ ^ 3 := by
    rw [div_le_iff₀ hL0]
    have hm := mul_le_mul hc4_up h1c_ℓ h1c0 (by positivity)
    have hL12 : L ^ (1 / 2 : ℝ) ≤ L :=
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L)
    have hℓ_3 : ℓ ≤ ℓ ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 3)
    have hm2 := mul_le_mul_of_nonneg_left (mul_le_mul hL12 hℓ_3 hℓ0.le hL0.le)
      (by positivity : 0 ≤ K_c ^ 4)
    linarith only [hm, hm2, (by ring : K_c ^ 4 * L ^ (1 / 2 : ℝ) * ℓ =
      K_c ^ 4 * (L ^ (1 / 2 : ℝ) * ℓ)),
      (by ring : K_c ^ 4 * (L * ℓ ^ 3) = K_c ^ 4 * ℓ ^ 3 * L)]
  have ht4 : c ^ 3 * (R : ℝ) ^ 2 * (L / N) ≤ ℓ ^ 3 := by
    have hc3 : c ^ 3 * (R : ℝ) ^ 2 * L / N ≤ 1 := by
      rw [div_le_one hN0]
      have hRN' : c ^ 3 * (R : ℝ) ^ 2 * L ≤ L ^ 18 * (R : ℝ) ^ 16 := by
        have hc3L : c ^ 3 * L ≤ L ^ 18 := by
          calc c ^ 3 * L ≤ L ^ 3 * L :=
                mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0.le hcL 3) hL0.le
            _ = L ^ 4 := by ring
            _ ≤ L ^ 18 := pow_le_pow_right₀ hL1 (by norm_num)
        have hR2 : (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 16 := pow_le_pow_right₀ hR1R (by norm_num)
        exact (by ring : c ^ 3 * (R : ℝ) ^ 2 * L = (c ^ 3 * L) * (R : ℝ) ^ 2).trans_le
          (mul_le_mul hc3L hR2 (sq_nonneg _) (by positivity))
      exact hRN'.trans hRN
    have hid : c ^ 3 * (R : ℝ) ^ 2 * (L / N) = c ^ 3 * (R : ℝ) ^ 2 * L / N := by ring
    rw [hid]; exact hc3.trans (one_le_pow₀ hℓ1)
  have ht5 : 2 * bandFarBudgetA R N c ≤ 2 * ℓ ^ 3 := by
    unfold bandFarBudgetA; rw [← hLdef]
    have h1L_1 : 1 / L ≤ (1 : ℝ) := (div_le_one hL0).mpr hL1
    have hb := cpow_Rpow_div_le hL1 hc0.le hcL hR1R hRN h1L_1 (i := 2) (j := 5)
      (by norm_num) (by norm_num)
    have hN1R : (1 : ℝ) ≤ N :=
      le_trans (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hR1R)) hRN
    have hden : (N : ℝ) ≤ (N : ℝ) ^ 2 * L :=
      (le_self_pow₀ hN1R two_ne_zero).trans (le_mul_of_one_le_right (sq_nonneg _) hL1)
    have hb' : c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L) ≤ 1 :=
      (div_le_div_of_nonneg_left (by positivity) hN0 hden).trans hb
    linarith only [hb', one_le_pow₀ hℓ1 (n := 3)]
  unfold bandFarBudgetU; rw [← hLdef]
  linarith only [ht1, ht2, ht3, ht4, ht5,
    (by ring : (8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) * ℓ ^ 3 =
      8 * K_res * K_c ^ 2 * ℓ ^ 3 + K_c ^ 2 * (1560 * K_tot + 96) * ℓ ^ 3 +
        K_c ^ 4 * ℓ ^ 3 + ℓ ^ 3 + 2 * ℓ ^ 3)]

private lemma all_ratio_band_far_budgets {R M N : ℕ}
    {c ρ Sg₁ k b L ℓ D CB K_c M_bk C_pr C_up C_upT C_np K_tot K_res : ℝ}
    (hLdef : L = Real.log (N : ℝ)) (hℓdef : ℓ = 1 + Real.log L)
    (hk_def : k = L / (2 * D * ℓ ^ 6))
    (hbk_ub : c ^ 7 / (b * k) ≤ M_bk * ℓ / L ^ (1 / 8 : ℝ))
    (hD : 0 < D) (hCpr : 0 < C_pr) (hCup : 0 ≤ C_up) (hCupT : 0 ≤ C_upT)
    (hCnp : 0 ≤ C_np) (hCB0 : 0 ≤ CB) (hKc1 : 1 ≤ K_c) (hMbk0 : 0 ≤ M_bk)
    (hK_tot : 1 ≤ K_tot) (hK_res : 0 ≤ K_res)
    (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hcL : c ≤ L) (hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ))
    (hk_pos : 0 < k) (hb_pos : 0 < b)
    (hR1 : 1 ≤ R) (hMN : M ≤ N) (hRN : L ^ 18 * (R : ℝ) ^ 16 ≤ N)
    (hlR : 1 + Real.log (R : ℝ) ≤ 2 * L / ℓ ^ 5)
    (hTPC : terminalPacketCost R M N ≤ CB * (1 + Real.log c))
    (hNM : (N : ℝ) / M ≤ 2 * (256 * Real.exp 2 + 4) * c)
    (hSg : Sg₁ ≤ 2 * K_tot * ℓ) (hSg0 : 0 ≤ Sg₁)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 2 * K_res * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L))
    (hℓ_E : 128 * (1024 * D * C_pr + 32 * C_np * M_bk * (8 * K_c * K_tot ^ 2 + 6)) ≤ ℓ)
    (hL8_E2 : 128 * (256 * C_pr * CB * M_bk) ≤ L ^ (1 / 8 : ℝ))
    (hU_small :
      (1024 * D * C_pr + 512 * C_pr * M_bk +
        32 * C_np * M_bk * (8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) +
        256 * D * C_up * K_c ^ 2 +
        256 * C_upT * (256 * Real.exp 2 + 4) * K_c ^ 3 * M_bk) * ℓ ^ 7 ≤
      (1 / 8 : ℝ) * L ^ (1 / 8 : ℝ)) :
    (128 * C_pr * (1 + Real.log (R : ℝ)) ^ 2 / (Real.log (N : ℝ) * k) +
      128 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N /
        (Real.log (N : ℝ) * b * k) +
      32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k) ≤ 1 / 32) ∧
    (256 * C_pr * (1 + Real.log (R : ℝ)) / (Real.log (N : ℝ) * k) +
      256 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) / (Real.log (N : ℝ) * b * k) +
      32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetG R N c Sg₁ +
        2 * bandFarBudgetA R N c) / (b * k) +
      128 * C_up * c ^ 2 * (1 + Real.log c) / k +
      128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) /
        (Real.log (N : ℝ) * b * k) ≤ 1 / 4) := by
  have hsE_raw := all_ratio_band_far_budget_E hLdef hℓdef hk_def hbk_ub hD hCpr hCnp hCB0 hKc1
    hMbk0 hK_tot hL1 hc1 hcL hc_up hk_pos hb_pos hR1 hMN hRN hlR hTPC hSg hSg0 hℓ_E hL8_E2
  refine ⟨hsE_raw, ?_⟩
  rw [← hLdef] at hsE_raw ⊢
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hKc0 : 0 < K_c := zero_lt_one.trans_le hKc1
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hlR_2L : 1 + Real.log (R : ℝ) ≤ 2 * L :=
    hlR.trans (div_le_self (by positivity) (one_le_pow₀ hℓ1))
  have h1c_ℓ : 1 + Real.log c ≤ ℓ := by rw [hℓdef]; linarith [Real.log_le_log hc0 hcL]
  have h1c0 : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hL8_pos : 0 < L ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hLk : L * k = L ^ 2 / (2 * D * ℓ ^ 6) := by rw [hk_def]; ring
  have h1k : 1 / k = 2 * D * ℓ ^ 6 / L := by rw [hk_def]; field_simp [hL0.ne', hD.ne', hℓ0.ne']
  have hU3G : 32 * c ^ 7 * C_np * (2 * bandFarBudgetG R N c Sg₁) / (b * k) ≤ 1 / 16 := by
    have hTPC0 : 0 ≤ terminalPacketCost R M N := terminalPacketCost_nonneg R hMN
    have he1_0 : 0 ≤ 128 * C_pr * (1 + Real.log (R : ℝ)) ^ 2 / (L * k) := by positivity
    have he2_0 : 0 ≤ 128 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N /
        (L * b * k) := by positivity
    linarith only [hsE_raw, he1_0, he2_0,
      (by ring : 32 * c ^ 7 * C_np * (2 * bandFarBudgetG R N c Sg₁) / (b * k) =
        2 * (32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k)))]
  have hinvL_L8 : 1 / L ≤ 1 / L ^ (1 / 8 : ℝ) :=
    one_div_le_one_div_of_le hL8_pos
      ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hc2_up : c ^ 2 ≤ K_c ^ 2 * L ^ (1 / 4 : ℝ) := by
    have hp := pow_le_pow_left₀ hc0.le hc_up 2
    rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
    exact hp.trans_eq (by congr 2; push_cast; ring)
  have hc3_up : c ^ 3 ≤ K_c ^ 3 * L ^ (3 / 8 : ℝ) := by
    have hp := pow_le_pow_left₀ hc0.le hc_up 3
    rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
    exact hp.trans_eq (by congr 2; push_cast; ring)
  have hbk0 : 0 ≤ c ^ 7 / (b * k) := div_nonneg (pow_nonneg hc0.le 7) (mul_pos hb_pos hk_pos).le
  have hU1 : 256 * C_pr * (1 + Real.log (R : ℝ)) / (L * k) ≤
      1024 * D * C_pr * ℓ ^ 7 / L ^ (1 / 8 : ℝ) := by
    have hℓ6_7 : ℓ ^ 6 ≤ ℓ ^ 7 := pow_le_pow_right₀ hℓ1 (by norm_num)
    calc 256 * C_pr * (1 + Real.log (R : ℝ)) / (L * k)
        ≤ 256 * C_pr * (2 * L) / (L ^ 2 / (2 * D * ℓ ^ 6)) := by
            rw [hLk]; exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlR_2L (by positivity)) (by positivity)
      _ = 1024 * D * C_pr * ℓ ^ 6 * (1 / L) := by field_simp [hL0.ne', hD.ne', hℓ0.ne']; ring
      _ ≤ 1024 * D * C_pr * ℓ ^ 7 * (1 / L ^ (1 / 8 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hℓ6_7 (by positivity)) hinvL_L8
              (by positivity) (by positivity)
      _ = 1024 * D * C_pr * ℓ ^ 7 / L ^ (1 / 8 : ℝ) := by ring
  have hU2 : 256 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) / (L * b * k) ≤
      512 * C_pr * M_bk * ℓ ^ 7 / L ^ (1 / 8 : ℝ) := by
    have hRL : (1 + Real.log (R : ℝ)) / L ≤ 2 := (div_le_iff₀ hL0).mpr hlR_2L
    have hid : 256 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) / (L * b * k) =
        256 * C_pr * ((1 + Real.log (R : ℝ)) / L) * (c ^ 7 / (b * k)) := by ring
    have hℓ1_7 : ℓ ≤ ℓ ^ 7 := by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 7)
    rw [hid]
    have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul hRL hbk_ub hbk0 zero_le_two) (by positivity : 0 ≤ 256 * C_pr)
    calc 256 * C_pr * ((1 + Real.log (R : ℝ)) / L) * (c ^ 7 / (b * k))
        ≤ 256 * C_pr * (2 * (M_bk * ℓ / L ^ (1 / 8 : ℝ))) := by
            linarith only [hm, (by ring : 256 * C_pr * (((1 + Real.log (R : ℝ)) / L) *
              (c ^ 7 / (b * k))) = 256 * C_pr * ((1 + Real.log (R : ℝ)) / L) * (c ^ 7 / (b * k)))]
      _ = 512 * C_pr * M_bk * (ℓ / L ^ (1 / 8 : ℝ)) := by ring
      _ ≤ 512 * C_pr * M_bk * ℓ ^ 7 / L ^ (1 / 8 : ℝ) := by
            rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hℓ1_7 hL8_pos.le)
              (mul_nonneg (by positivity) hMbk0)
  have hUA_ub := all_ratio_band_far_budget_UA hLdef hℓdef hKc1 hK_tot hK_res hL1 hc1 hcL hc_up
    hR1 hRN hlR_2L hSg hSg0 hρ0 hρ
  have hU3UA : 32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetA R N c) /
      (b * k) ≤
      32 * C_np * M_bk * (8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) *
        ℓ ^ 7 / L ^ (1 / 8 : ℝ) := by
    have hCcoef0 : 0 ≤ 8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3 :=
      add_nonneg (add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hK_res) (sq_nonneg K_c))
        (mul_nonneg (sq_nonneg K_c) (by linarith only [hK_tot]))) (pow_nonneg hKc0.le 4))
        (by norm_num)
    have hid : 32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetA R N c) /
        (b * k) = 32 * C_np * ((bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetA R N c) *
          (c ^ 7 / (b * k))) := by ring
    have hℓ4_7 : ℓ ^ 4 ≤ ℓ ^ 7 := pow_le_pow_right₀ hℓ1 (by norm_num)
    rw [hid]
    have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul hUA_ub hbk_ub hbk0 (mul_nonneg hCcoef0 (pow_nonneg hℓ0.le 3)))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hCnp)
    refine hm.trans ?_
    have hid2 : 32 * C_np * (((8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) *
        ℓ ^ 3) * (M_bk * ℓ / L ^ (1 / 8 : ℝ))) =
        32 * C_np * M_bk * (8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) *
          ℓ ^ 4 / L ^ (1 / 8 : ℝ) := by ring
    rw [hid2]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hℓ4_7
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hCnp) hMbk0) hCcoef0))
      hL8_pos.le
  have hU4 : 128 * C_up * c ^ 2 * (1 + Real.log c) / k ≤
      256 * D * C_up * K_c ^ 2 * ℓ ^ 7 / L ^ (1 / 8 : ℝ) := by
    have hid : 128 * C_up * c ^ 2 * (1 + Real.log c) / k =
        128 * C_up * (c ^ 2 * (1 + Real.log c)) * (1 / k) := by ring
    rw [hid, h1k]
    have hm1 := mul_le_mul hc2_up h1c_ℓ h1c0
      (mul_nonneg (sq_nonneg K_c) (Real.rpow_nonneg hL0.le _))
    have hm2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) hCup))
      (div_nonneg (mul_nonneg (mul_nonneg zero_le_two hD.le) (pow_nonneg hℓ0.le 6)) hL0.le)
    have hsplit : L ^ (1 / 4 : ℝ) * L ^ (3 / 4 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
    have hdiv : L ^ (1 / 4 : ℝ) / L ≤ 1 / L ^ (1 / 8 : ℝ) := by
      have h14 : L ^ (1 / 4 : ℝ) / L = 1 / L ^ (3 / 4 : ℝ) := by
        rw [div_eq_div_iff hL0.ne' (Real.rpow_pos_of_pos hL0 _).ne']
        linarith only [hsplit]
      rw [h14]
      exact one_div_le_one_div_of_le hL8_pos (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
    refine hm2.trans ?_
    have hid2 : 128 * C_up * (K_c ^ 2 * L ^ (1 / 4 : ℝ) * ℓ) * (2 * D * ℓ ^ 6 / L) =
        (256 * D * C_up * K_c ^ 2 * ℓ ^ 7) * (L ^ (1 / 4 : ℝ) / L) := by ring
    rw [hid2]
    exact (mul_le_mul_of_nonneg_left hdiv
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 256) hD.le) hCup)
        (sq_nonneg K_c)) (pow_nonneg hℓ0.le 7))).trans_eq (by ring)
  have hU5 : 128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / (L * b * k) ≤
      256 * C_upT * (256 * Real.exp 2 + 4) * K_c ^ 3 * M_bk * ℓ ^ 7 / L ^ (1 / 8 : ℝ) := by
    have hKexp0 : 0 ≤ 256 * Real.exp 2 + 4 :=
      add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 256) (Real.exp_pos 2).le) (by norm_num)
    have hnum : c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / L ≤
        2 * (256 * Real.exp 2 + 4) * K_c ^ 3 * ℓ := by
      have h1 : c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) ≤
          2 * (256 * Real.exp 2 + 4) * c ^ 3 * ℓ := by
        have hm := mul_le_mul (mul_le_mul_of_nonneg_left hNM (sq_nonneg c)) h1c_ℓ h1c0
          (mul_nonneg (sq_nonneg c) (mul_nonneg (mul_nonneg zero_le_two hKexp0) hc0.le))
        exact hm.trans_eq (by ring)
      have h2 : c ^ 3 ≤ K_c ^ 3 * L := by
        have h38 : L ^ (3 / 8 : ℝ) ≤ L :=
          (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L)
        exact hc3_up.trans (mul_le_mul_of_nonneg_left h38 (pow_nonneg hKc0.le 3))
      rw [div_le_iff₀ hL0]
      have hm2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h2 (mul_nonneg zero_le_two hKexp0)) hℓ0.le
      linarith only [h1, hm2,
        (by ring : 2 * (256 * Real.exp 2 + 4) * (K_c ^ 3 * L) * ℓ =
          2 * (256 * Real.exp 2 + 4) * K_c ^ 3 * ℓ * L)]
    have hid : 128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / (L * b * k) =
        128 * C_upT * ((c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / L) * (c ^ 7 / (b * k))) := by
      ring
    rw [hid]
    have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul hnum hbk_ub hbk0
        (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hKexp0) (pow_nonneg hKc0.le 3)) hℓ0.le))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) hCupT)
    have hℓ2_7 : ℓ ^ 2 ≤ ℓ ^ 7 := pow_le_pow_right₀ hℓ1 (by norm_num)
    refine hm.trans ?_
    have hid2 : 128 * C_upT * ((2 * (256 * Real.exp 2 + 4) * K_c ^ 3 * ℓ) *
        (M_bk * ℓ / L ^ (1 / 8 : ℝ))) =
        256 * C_upT * (256 * Real.exp 2 + 4) * K_c ^ 3 * M_bk * ℓ ^ 2 / L ^ (1 / 8 : ℝ) := by
      ring
    rw [hid2]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hℓ2_7
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 256) hCupT) hKexp0)
          (pow_nonneg hKc0.le 3)) hMbk0)) hL8_pos.le
  have hsplit3 : 32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ +
      2 * bandFarBudgetG R N c Sg₁ + 2 * bandFarBudgetA R N c) / (b * k) =
      32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetA R N c) / (b * k) +
        32 * c ^ 7 * C_np * (2 * bandFarBudgetG R N c Sg₁) / (b * k) := by ring
  rw [hsplit3]
  have h5_le :
      256 * C_pr * (1 + Real.log (R : ℝ)) / (L * k) +
        256 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) / (L * b * k) +
        32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetA R N c) / (b * k) +
        128 * C_up * c ^ 2 * (1 + Real.log c) / k +
        128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / (L * b * k) ≤ 1 / 8 := by
    have hsum_eq :
        1024 * D * C_pr * ℓ ^ 7 / L ^ (1 / 8 : ℝ) +
          512 * C_pr * M_bk * ℓ ^ 7 / L ^ (1 / 8 : ℝ) +
          32 * C_np * M_bk *
            (8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) *
            ℓ ^ 7 / L ^ (1 / 8 : ℝ) +
          256 * D * C_up * K_c ^ 2 * ℓ ^ 7 / L ^ (1 / 8 : ℝ) +
          256 * C_upT * (256 * Real.exp 2 + 4) * K_c ^ 3 * M_bk * ℓ ^ 7 / L ^ (1 / 8 : ℝ) =
        (1024 * D * C_pr + 512 * C_pr * M_bk +
          32 * C_np * M_bk *
            (8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) +
          256 * D * C_up * K_c ^ 2 +
          256 * C_upT * (256 * Real.exp 2 + 4) * K_c ^ 3 * M_bk) * ℓ ^ 7 / L ^ (1 / 8 : ℝ) := by
      ring
    have hdiv : (1024 * D * C_pr + 512 * C_pr * M_bk +
        32 * C_np * M_bk *
          (8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) +
        256 * D * C_up * K_c ^ 2 +
        256 * C_upT * (256 * Real.exp 2 + 4) * K_c ^ 3 * M_bk) * ℓ ^ 7 / L ^ (1 / 8 : ℝ) ≤
        1 / 8 := (div_le_iff₀ hL8_pos).mpr hU_small
    linarith only [hU1, hU2, hU3UA, hU4, hU5, hsum_eq, hdiv]
  linarith only [h5_le, hU3G]

private lemma all_ratio_band0_band1_scalars {N Q₁ R₀ : ℕ}
    {c L Lh K_c κ₀ C_small0 C_coerc0 C_band1 C_cross01 : ℝ}
    (hc1 : 1 ≤ c) (hKc1 : 1 ≤ K_c) (hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ))
    (hL1 : 1 ≤ L) (hLh_eq : Lh = L ^ (1 / 2 : ℝ))
    (_hκ₀ : 0 < κ₀) (hC_small0 : 0 < C_small0) (hC_cross01 : 0 < C_cross01)
    (hVc : 1 + Real.log c ≤ L ^ (1 / 128 : ℝ))
    (hsqrtQ : (1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2) ≤ Real.sqrt Q₁)
    (hlogQ_lb : (13 / 32 : ℝ) * Real.log L - 1 ≤ Real.log (Q₁ : ℝ))
    (hH₀_ub : 1 + Real.log (R₀ : ℝ) ≤ 2 * Lh)
    (hlogR₀_lb : Lh - 1 ≤ Real.log (R₀ : ℝ))
    (hR₀_tail : (R₀ : ℝ) * Real.sqrt (L / N) ≤ 1 / L)
    (hc5N : c ^ 5 * L / N ≤ 1 / L)
    (hc3R₀4 : c ^ 3 * (R₀ : ℝ) ^ 4 / N ≤ 1 / L)
    (hc3R₀2 : c ^ 3 * (R₀ : ℝ) ^ 2 * (L / N) ≤ 1 / L)
    (hν_b1 : C_small0 * (18 * K_c ^ 4) ≤ L ^ (1 / 128 : ℝ))
    (hν_b2 : C_cross01 * (4 * K_c ^ 4) ≤ L ^ (1 / 128 : ℝ))
    (hν_b6 : 32 * C_band1 * K_c ^ 4 ≤ L ^ (1 / 128 : ℝ))
    (hll_scaled : κ₀ + 4 + C_coerc0 + Real.log K_c + 3 / 4 ≤ (23 / 128 : ℝ) * Real.log L)
    (hL_Lh_gap : (8 * (κ₀ + 3)) ^ 2 ≤ L) :
    C_small0 * (c * (1 + Real.log c) * (1 + Real.log R₀) / L +
      c * (1 + Real.log R₀) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
      c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
      c ^ 5 * L / N +
      c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
      c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 ∧
    C_cross01 * (1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
      c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) ≤ 1 ∧
    κ₀ + 3 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0 ∧
    κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLh1 : 1 ≤ Lh := by rw [hLh_eq]; exact Real.one_le_rpow hL1 (by norm_num)
  have hLh0 : 0 < Lh := zero_lt_one.trans_le hLh1
  have hLh_sq : Lh * Lh = L := by rw [hLh_eq, ← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hKc0 : 0 < K_c := zero_lt_one.trans_le hKc1
  have hKc4_1 : 1 ≤ K_c ^ 4 := one_le_pow₀ hKc1
  have hlc_ge1 : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hlc_nn : 0 ≤ 1 + Real.log c := zero_le_one.trans hlc_ge1
  set ν : ℝ := 1 / 128
  have hLν0 : 0 ≤ L ^ ν := Real.rpow_nonneg hL0.le _
  have hLmν0 : 0 ≤ L ^ (-ν) := Real.rpow_nonneg hL0.le _
  have hmul_ν : L ^ ν * L ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have h1_invL : 1 / L ≤ L ^ (-ν) := by
    rw [one_div, ← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num [ν])
  have h1_invLh : 1 / Lh ≤ L ^ (-ν) := by
    rw [hLh_eq, one_div, ← Real.rpow_neg hL0.le]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num [ν])
  have hH₀_div : (1 + Real.log (R₀ : ℝ)) / L ≤ 2 / Lh := by
    rw [div_le_div_iff₀ hL0 hLh0]
    calc (1 + Real.log (R₀ : ℝ)) * Lh ≤ (2 * Lh) * Lh := mul_le_mul_of_nonneg_right hH₀_ub hLh0.le
      _ = 2 * L := by rw [← hLh_sq]; ring
  have hc2_vc_Lh : c ^ 2 * (1 + Real.log c) / Lh ≤ K_c ^ 4 * L ^ (-ν) := by
    have hc2 : c ^ 2 ≤ K_c ^ 4 * L ^ (1 / 4 : ℝ) := by
      have hp := pow_le_pow_left₀ hc0.le hc_up 2
      rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
      have h24 : K_c ^ 2 ≤ K_c ^ 4 := pow_le_pow_right₀ hKc1 (by norm_num)
      exact (hp.trans_eq (by congr 2; push_cast; ring)).trans
        (mul_le_mul_of_nonneg_right h24 (by positivity))
    have hm := mul_le_mul hc2 hVc hlc_nn (by positivity)
    have hdiv : L ^ (1 / 4 : ℝ) * L ^ ν / Lh ≤ L ^ (-ν) := by
      rw [hLh_eq, ← Real.rpow_add hL0]; exact rpow_div_rpow_le hL1 (by norm_num [ν])
    calc c ^ 2 * (1 + Real.log c) / Lh ≤ K_c ^ 4 * (L ^ (1 / 4 : ℝ) * L ^ ν / Lh) :=
            (div_le_div_of_nonneg_right hm hLh0.le).trans_eq (by ring)
      _ ≤ K_c ^ 4 * L ^ (-ν) := mul_le_mul_of_nonneg_left hdiv (by positivity)
  have hc2_vc_L : c ^ 2 * (1 + Real.log c) / L ≤ K_c ^ 4 * L ^ (-ν) :=
    (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg c) hlc_nn) hLh0
      (by nlinarith only [hLh1, hLh_sq])).trans hc2_vc_Lh
  have hc4_vc : c ^ 4 * (1 + Real.log c) / L ≤ K_c ^ 4 * L ^ (-ν) := by
    have hc4 : c ^ 4 ≤ K_c ^ 4 * L ^ (1 / 2 : ℝ) := by
      have hp := pow_le_pow_left₀ hc0.le hc_up 4
      rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
      exact hp.trans_eq (by congr 2; push_cast; ring)
    have hm := mul_le_mul hc4 hVc hlc_nn (by positivity)
    have hdiv : L ^ (1 / 2 : ℝ) * L ^ ν / L ≤ L ^ (-ν) := by
      rw [← Real.rpow_add hL0, show L ^ (1 / 2 + ν) / L = L ^ (1 / 2 + ν) / L ^ (1 : ℝ) by
        rw [Real.rpow_one]]
      exact rpow_div_rpow_le hL1 (by norm_num [ν])
    calc c ^ 4 * (1 + Real.log c) / L ≤ K_c ^ 4 * (L ^ (1 / 2 : ℝ) * L ^ ν / L) :=
            (div_le_div_of_nonneg_right hm hL0.le).trans_eq (by ring)
      _ ≤ K_c ^ 4 * L ^ (-ν) := mul_le_mul_of_nonneg_left hdiv (by positivity)
  have hout1 : C_small0 * (c * (1 + Real.log c) * (1 + Real.log R₀) / L +
      c * (1 + Real.log R₀) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
      c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
      c ^ 5 * L / N +
      c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
      c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 := by
    have hmid_Q₁ : c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ ≤ 2 * K_c ^ 4 * L ^ (-ν) := by
      have hc32 : c * Real.sqrt c ≤ K_c ^ 4 * L ^ (3 / 16 : ℝ) := by
        have hsq : (c * Real.sqrt c) ^ 2 ≤ (K_c ^ 4 * L ^ (3 / 16 : ℝ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hc0.le, show c ^ 2 * c = c ^ 3 by ring,
            mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le]
          have hp := pow_le_pow_left₀ hc0.le hc_up 3
          rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
          have h38 : K_c ^ 3 ≤ (K_c ^ 4) ^ 2 := by
            rw [← pow_mul]; exact pow_le_pow_right₀ hKc1 (by norm_num)
          exact (hp.trans_eq (by congr 2; push_cast; ring)).trans
            (mul_le_mul_of_nonneg_right h38 (by positivity))
        nlinarith only [hsq, mul_nonneg hc0.le (Real.sqrt_nonneg c),
          show 0 ≤ K_c ^ 4 * L ^ (3 / 16 : ℝ) by positivity]
      have hden_pos : 0 < (1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2) :=
        mul_pos (by norm_num) (Real.rpow_pos_of_pos hL0 _)
      calc c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁
          ≤ (K_c ^ 4 * L ^ (3 / 16 : ℝ) * L ^ ν) / ((1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2)) :=
            (div_le_div_of_nonneg_right
              (mul_le_mul hc32 hVc hlc_nn (by positivity)) (Real.sqrt_nonneg _)).trans
              (div_le_div_of_nonneg_left (by positivity) hden_pos hsqrtQ)
        _ = 2 * K_c ^ 4 * L ^ ((3 / 16 : ℝ) + ν - (13 / 32 : ℝ) / 2) := by
            rw [show (K_c ^ 4 * L ^ (3 / 16 : ℝ) * L ^ ν) /
              ((1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2)) =
              2 * K_c ^ 4 * ((L ^ (3 / 16 : ℝ) * L ^ ν) / L ^ ((13 / 32 : ℝ) / 2)) by ring,
              ← Real.rpow_add hL0, ← Real.rpow_sub hL0]
        _ ≤ 2 * K_c ^ 4 * L ^ (-ν) := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num [ν])) (by positivity)
    have ht4 : c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L ≤ 2 * K_c ^ 4 * L ^ (-ν) := by
      calc c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L
          = c ^ 2 * (1 + Real.log c) * ((1 + Real.log R₀) / L) := by ring
        _ ≤ c ^ 2 * (1 + Real.log c) * (2 / Lh) :=
            mul_le_mul_of_nonneg_left hH₀_div (mul_nonneg (sq_nonneg c) hlc_nn)
        _ = 2 * (c ^ 2 * (1 + Real.log c) / Lh) := by ring
        _ ≤ 2 * K_c ^ 4 * L ^ (-ν) := (mul_le_mul_of_nonneg_left hc2_vc_Lh zero_le_two).trans_eq (by ring)
    have hlogR₀_nn : 0 ≤ 1 + Real.log (R₀ : ℝ) := by linarith [Real.log_natCast_nonneg R₀]
    have ht1 : c * (1 + Real.log c) * (1 + Real.log R₀) / L ≤ 2 * K_c ^ 4 * L ^ (-ν) := by
      have hm : c * (1 + Real.log c) ≤ c ^ 2 * (1 + Real.log c) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hc1]) hlc_nn
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm hlogR₀_nn) hL0.le).trans
        ((by ring : c ^ 2 * (1 + Real.log c) * (1 + Real.log R₀) / L =
          c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L).trans_le ht4)
    have ht2 : c * (1 + Real.log R₀) / L ≤ 2 * K_c ^ 4 * L ^ (-ν) :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc0.le hlc_ge1) hlogR₀_nn) hL0.le).trans ht1
    have ht3 : c ^ 2 / L ≤ K_c ^ 4 * L ^ (-ν) :=
      (div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg c) hlc_ge1) hL0.le).trans
        hc2_vc_L
    have ht5 : c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) ≤ K_c ^ 4 * L ^ (-ν) := by
      calc c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) = c ^ 2 * ((R₀ : ℝ) * Real.sqrt (L / N)) := by ring
        _ ≤ c ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hR₀_tail (sq_nonneg c)
        _ = c ^ 2 / L := by ring
        _ ≤ K_c ^ 4 * L ^ (-ν) := ht3
    have hLmν_K : L ^ (-ν) ≤ K_c ^ 4 * L ^ (-ν) := le_mul_of_one_le_left hLmν0 hKc4_1
    have ht6 : c ^ 5 * L / N ≤ K_c ^ 4 * L ^ (-ν) := (hc5N.trans h1_invL).trans hLmν_K
    have ht8 : c ^ 3 * (R₀ : ℝ) ^ 4 / N ≤ K_c ^ 4 * L ^ (-ν) := (hc3R₀4.trans h1_invL).trans hLmν_K
    have hsum18 : c * (1 + Real.log c) * (1 + Real.log R₀) / L +
        c * (1 + Real.log R₀) / L + c ^ 2 / L +
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
        c ^ 5 * L / N +
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
        c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L ≤ 18 * K_c ^ 4 * L ^ (-ν) := by
      have hKL0 : 0 ≤ K_c ^ 4 * L ^ (-ν) := by positivity
      linarith only [ht1, ht2, ht3, ht4, ht5, ht6, hmid_Q₁, ht8, hc2_vc_L, hKL0]
    calc _ ≤ C_small0 * (18 * K_c ^ 4 * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum18 hC_small0.le
      _ = (C_small0 * (18 * K_c ^ 4)) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_b1 hLmν0
      _ = 1 := hmul_ν
  have hout2 : C_cross01 * (1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
      c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) ≤ 1 := by
    have hLmν_K : L ^ (-ν) ≤ K_c ^ 4 * L ^ (-ν) := le_mul_of_one_le_left hLmν0 hKc4_1
    have hc1_Lh : 1 / Lh ≤ K_c ^ 4 * L ^ (-ν) := h1_invLh.trans hLmν_K
    have hc3_N : c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ K_c ^ 4 * L ^ (-ν) :=
      (hc3R₀2.trans h1_invL).trans hLmν_K
    have hsum4 : 1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
        c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤
        4 * K_c ^ 4 * L ^ (-ν) := by
      linarith only [hc1_Lh, hc2_vc_Lh, hc4_vc, hc3_N]
    calc _ ≤ C_cross01 * (4 * K_c ^ 4 * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum4 hC_cross01.le
      _ = (C_cross01 * (4 * K_c ^ 4)) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_b2 hLmν0
      _ = 1 := hmul_ν
  have hout3 : κ₀ + 3 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0 := by
    have hlogc : Real.log c ≤ Real.log K_c + (1 / 8 : ℝ) * Real.log L := by
      have h1 := Real.log_le_log hc0 hc_up
      rwa [Real.log_mul hKc0.ne' (Real.rpow_pos_of_pos hL0 _).ne', Real.log_rpow hL0] at h1
    have hq_scaled : (39 / 128 : ℝ) * Real.log L - 3 / 4 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) := by
      linarith only [mul_le_mul_of_nonneg_left hlogQ_lb (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    linarith only [hlogc, hq_scaled, hll_scaled]
  have hout4 : κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c) := by
    have hc2_Lh : C_band1 * c ^ 2 * (1 + Real.log c) ≤ Lh / 32 := by
      by_cases hC0 : 0 ≤ C_band1
      · rw [le_div_iff₀' (by norm_num : (0 : ℝ) < 32), ← div_le_one hLh0]
        calc 32 * (C_band1 * c ^ 2 * (1 + Real.log c)) / Lh
            = 32 * C_band1 * (c ^ 2 * (1 + Real.log c) / Lh) := by ring
          _ ≤ 32 * C_band1 * (K_c ^ 4 * L ^ (-ν)) :=
              mul_le_mul_of_nonneg_left hc2_vc_Lh (by positivity)
          _ = (32 * C_band1 * K_c ^ 4) * L ^ (-ν) := by ring
          _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_b6 hLmν0
          _ = 1 := hmul_ν
      · have hneg : C_band1 * (c ^ 2 * (1 + Real.log c)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC0) (mul_nonneg (sq_nonneg c) hlc_nn)
        linarith only [hneg, hLh0,
          (by ring : C_band1 * c ^ 2 * (1 + Real.log c) = C_band1 * (c ^ 2 * (1 + Real.log c)))]
    have hκ_Lh : 8 * (κ₀ + 3) ≤ Lh := by
      have hsq : (8 * (κ₀ + 3)) ^ 2 ≤ Lh * Lh := hLh_sq ▸ hL_Lh_gap
      exact (abs_le_of_sq_le_sq' (hsq.trans_eq (sq Lh).symm) hLh0.le).2
    linarith only [hc2_Lh, hκ_Lh, hlogR₀_lb]
  exact ⟨hout1, hout2, hout3, hout4⟩

private lemma all_ratio_three_band_assembly {Q₁ R₀ R₁ N : ℕ}
    {c k₁ k b L Lh ℓ D g₀ κ₀ C_coerc0 C_band1 E_extra : ℝ}
    (hQ2 : 2 ≤ Q₁) (hQR₀ : Q₁ ≤ R₀) (hc1 : 1 ≤ c) (hD : 0 < D) (hg₀ : 0 < g₀) (hκ₀ : 0 < κ₀)
    (hℓ1 : 1 ≤ ℓ)
    (hk₁_def : k₁ = L / (2 * D * ℓ ^ 5))
    (hk_def : k = L / (2 * D * ℓ ^ 6))
    (hb_le_c7 : b ≤ c ^ 7)
    (hb_le_b0 : b ≤ (g₀ * D / 4) * ℓ ^ 5)
    (hband0 : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace Q₁ N)ᗮ →
      (1 / 8 : ℝ) * primeAdjunctionMass R₀ a₀ +
        ((3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0) *
          ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N))
    (hband1 : ∀ a₁ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace R₀ N)ᗮ →
      (1 / 8 : ℝ) * primeAdjunctionMass R₁ a₁ +
        ((1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c)) *
          ‖∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N))
    (hcr01_fn : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {u₁ : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u₁ ∈ (conductorSubspace R₀ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N), u₁⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₀ a₀ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2)
    (hcr0w_fn : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N), w⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₀ a₀ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (k / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (b * k / (32 * c ^ 7)) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
          (b * k / (32 * c ^ 7)) * ‖w‖ ^ 2)
    (hcr1w_fn : ∀ a₁ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N), w⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₁ a₁ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (k / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (b * k / (32 * c ^ 7)) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
          (b * k / (32 * c ^ 7)) * ‖w‖ ^ 2)
    (hfl0 : κ₀ + 3 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0)
    (hfl1 : κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c))
    (hP_floor : κ₀ + 2 ≤ k₁ / 16)
    (hS_floor : κ₀ + 2 ≤ g₀ * L / (64 * c ^ 7))
    {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu₀_mem : u₀ ∈ conductorSubspace R₀ N) (hu₀_orthQ : u₀ ∈ (conductorSubspace Q₁ N)ᗮ)
    (hu₁_mem : u₁ ∈ conductorSubspace R₁ N) (hu₁_orthR₀ : u₁ ∈ (conductorSubspace R₀ N)ᗮ)
    (hw_orthR₁ : w ∈ (conductorSubspace R₁ N)ᗮ)
    (hband2 : (k₁ / 4) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (g₀ * L / (16 * c ^ 7)) *
          topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
        completeWeilEnergy tiltedUnitSpline c N w + E_extra) :
    ((κ₀ + 3) * ‖u₀‖ ^ 2 + (κ₀ + 2 + Lh / 32) * ‖u₁‖ ^ 2 +
        completeWeilEnergy tiltedUnitSpline c N w -
        (1 / ℓ) * ((k₁ / 8) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (g₀ * L / (32 * c ^ 7)) *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w)) ≤
      completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w)) ∧
    ((κ₀ + 3) * ‖u₀‖ ^ 2 + (κ₀ + 2 + Lh / 32) * ‖u₁‖ ^ 2 + (κ₀ + 2) * ‖w‖ ^ 2 +
        (k₁ / 16) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (g₀ * L / (64 * c ^ 7)) *
          topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
      completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w) + E_extra) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hk₁_0 : 0 ≤ k₁ := by linarith only [hP_floor, hκ₀]
  have hk_eq : k = k₁ / ℓ := by rw [hk_def, hk₁_def]; field_simp [hD.ne', hℓ0.ne']
  have hk_0 : 0 ≤ k := by rw [hk_eq]; positivity
  have hL0 : 0 ≤ L := by
    have h1 := mul_nonneg hk₁_0 (by positivity : 0 ≤ 2 * D * ℓ ^ 5)
    rwa [hk₁_def, div_mul_cancel₀ _ (by positivity)] at h1
  have hR₀2 : 2 ≤ R₀ := hQ2.trans hQR₀
  obtain ⟨a₀, -, ha₀⟩ := (mem_conductorSubspace_iff (M := R₀) (N := N) (x := u₀)).mp hu₀_mem
  obtain ⟨a₁, -, ha₁⟩ := (mem_conductorSubspace_iff (M := R₁) (N := N) (x := u₁)).mp hu₁_mem
  have hu₀_1 : u₀ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₀_orthQ v (conductorSubspace_mono ((by norm_num : 1 ≤ 2).trans hQ2) N hv)
  have hu₁_1 : u₁ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₁_orthR₀ v (conductorSubspace_mono ((by norm_num : 1 ≤ 2).trans hR₀2) N hv)
  have hdiag0 := hband0 a₀ (ha₀.symm ▸ hu₀_orthQ); rw [← ha₀] at hdiag0
  have hdiag1 := hband1 a₁ (ha₁.symm ▸ hu₁_orthR₀); rw [← ha₁] at hdiag1
  have hcr01 := hcr01_fn a₀ (ha₀.symm ▸ hu₀_1) hu₁_orthR₀; rw [← ha₀] at hcr01
  have hcr0w := hcr0w_fn a₀ (ha₀.symm ▸ hu₀_1) hw_orthR₁; rw [← ha₀] at hcr0w
  have hcr1w := hcr1w_fn a₁ (ha₁.symm ▸ hu₁_1) hw_orthR₁; rw [← ha₁] at hcr1w
  have hPw0 : 0 ≤ ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hSw0 : 0 ≤ ∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hSw_S7 := sum_sq_Ioc_le_topCollarSeventhMass (N / linearDefectCutoff c) N
    (primeHorizonExtension w)
  have hS7_0 : 0 ≤ topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) :=
    hSw0.trans hSw_S7
  have hw_split : ‖w‖ ^ 2 =
      (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) := by
    rw [← sum_primeHorizonExtension_sq w,
      Ioc_eq_Icc_sdiff_Icc_telescoped (N / linearDefectCutoff c) N, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl (Nat.div_le_self N _))).symm
  generalize (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) = P_w
    at hband2 hcr0w hcr1w hPw0 hw_split ⊢
  generalize (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) = S_w
    at hcr0w hcr1w hSw0 hSw_S7 hw_split
  generalize topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) = S7_w
    at hband2 hSw_S7 hS7_0 ⊢
  have hfloor0 : (κ₀ + 3) * ‖u₀‖ ^ 2 + (1 / 2 : ℝ) * ‖u₀‖ ^ 2 ≤
      ((3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0) * ‖u₀‖ ^ 2 := by
    rw [show (κ₀ + 3) * ‖u₀‖ ^ 2 + (1 / 2 : ℝ) * ‖u₀‖ ^ 2 = (κ₀ + 3 + 1 / 2) * ‖u₀‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hfl0 (sq_nonneg ‖u₀‖)
  have hfloor1 : (κ₀ + 2 + Lh / 32) * ‖u₁‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 +
      (1 / 4 : ℝ) * ‖u₁‖ ^ 2 ≤
      ((1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c)) * ‖u₁‖ ^ 2 := by
    rw [show (κ₀ + 2 + Lh / 32) * ‖u₁‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 +
      (1 / 4 : ℝ) * ‖u₁‖ ^ 2 = (κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4) * ‖u₁‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hfl1 (sq_nonneg ‖u₁‖)
  have hbk_k : b * k / (32 * c ^ 7) ≤ k / 32 := by
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb_le_c7 hk_0)
      (by positivity : 0 ≤ 32 * c ^ 7)
    exact hm.trans_eq (by field_simp [hc0.ne'])
  have hbk_g : b * k / (32 * c ^ 7) ≤ (1 / ℓ) * (g₀ * L / (256 * c ^ 7)) := by
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb_le_b0 hk_0)
      (by positivity : 0 ≤ 32 * c ^ 7)
    exact hm.trans_eq (by rw [hk_def]; field_simp [hD.ne', hℓ0.ne', hc0.ne']; ring)
  have hcross_w :
      2 * ((k / 32) * P_w + (b * k / (32 * c ^ 7)) * S_w + (b * k / (32 * c ^ 7)) * ‖w‖ ^ 2) ≤
        (1 / ℓ) * ((k₁ / 8) * P_w + (g₀ * L / (32 * c ^ 7)) * S7_w) := by
    rw [hw_split]
    have hp_part : 2 * (k / 32 + b * k / (32 * c ^ 7)) * P_w ≤ (1 / ℓ) * ((k₁ / 8) * P_w) := by
      have hcoef : 2 * (k / 32 + b * k / (32 * c ^ 7)) ≤ (1 / ℓ) * (k₁ / 8) := by
        have h1 : 2 * (k / 32 + b * k / (32 * c ^ 7)) ≤ k / 8 := by linarith only [hbk_k]
        exact h1.trans_eq (by rw [hk_eq]; ring)
      exact (mul_le_mul_of_nonneg_right hcoef hPw0).trans_eq (by ring)
    have hs_part : 4 * (b * k / (32 * c ^ 7)) * S_w ≤ (1 / ℓ) * ((g₀ * L / (32 * c ^ 7)) * S7_w) := by
      have hcoef : 4 * (b * k / (32 * c ^ 7)) ≤ (1 / ℓ) * (g₀ * L / (32 * c ^ 7)) := by
        have h0 : 0 ≤ (1 / ℓ) * (g₀ * L / (64 * c ^ 7)) := by positivity
        have hid : 4 * ((1 / ℓ) * (g₀ * L / (256 * c ^ 7))) = (1 / ℓ) * (g₀ * L / (64 * c ^ 7)) := by
          field_simp [hℓ0.ne', hc0.ne']; ring
        have hid2 : (1 / ℓ) * (g₀ * L / (32 * c ^ 7)) =
            2 * ((1 / ℓ) * (g₀ * L / (64 * c ^ 7))) := by
          field_simp [hℓ0.ne', hc0.ne']; ring
        linarith only [hbk_g, h0, hid, hid2]
      have hm1 := mul_le_mul_of_nonneg_right hcoef hSw0
      have hm2 := mul_le_mul_of_nonneg_left hSw_S7
        (by positivity : 0 ≤ (1 / ℓ) * (g₀ * L / (32 * c ^ 7)))
      exact hm1.trans (hm2.trans_eq (by ring))
    linarith only [hp_part, hs_part,
      (by ring : 2 * ((k / 32) * P_w + (b * k / (32 * c ^ 7)) * S_w +
          (b * k / (32 * c ^ 7)) * (P_w + S_w)) =
        2 * (k / 32 + b * k / (32 * c ^ 7)) * P_w + 4 * (b * k / (32 * c ^ 7)) * S_w),
      (by ring : (1 / ℓ) * ((k₁ / 8) * P_w + (g₀ * L / (32 * c ^ 7)) * S7_w) =
        (1 / ℓ) * ((k₁ / 8) * P_w) + (1 / ℓ) * ((g₀ * L / (32 * c ^ 7)) * S7_w))]
  have h3add := completeWeilEnergy_three_add_ge tiltedUnitSpline c u₀ u₁ w
  have hE₀_0 : 0 ≤ primeAdjunctionMass R₀ a₀ := primeAdjunctionMass_nonneg R₀ a₀
  have hE₁_0 : 0 ≤ primeAdjunctionMass R₁ a₁ := primeAdjunctionMass_nonneg R₁ a₁
  have hpartB : (κ₀ + 3) * ‖u₀‖ ^ 2 + (κ₀ + 2 + Lh / 32) * ‖u₁‖ ^ 2 +
      completeWeilEnergy tiltedUnitSpline c N w -
      (1 / ℓ) * ((k₁ / 8) * P_w + (g₀ * L / (32 * c ^ 7)) * S7_w) ≤
      completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w) := by
    linarith only [h3add, hdiag0, hdiag1, hcr01, hcr0w, hcr1w, hfloor0, hfloor1, hcross_w,
      hE₀_0, hE₁_0]
  refine ⟨hpartB, ?_⟩
  have h1_ℓ_le1 : 1 / ℓ ≤ 1 := (div_le_one hℓ0).mpr hℓ1
  have hleak_le : (1 / ℓ) * ((k₁ / 8) * P_w + (g₀ * L / (32 * c ^ 7)) * S7_w) ≤
      (k₁ / 8) * P_w + (g₀ * L / (32 * c ^ 7)) * S7_w :=
    (mul_le_mul_of_nonneg_right h1_ℓ_le1 (by positivity)).trans_eq (one_mul _)
  have hP_rem : (κ₀ + 2) * P_w + (k₁ / 16) * P_w ≤ (k₁ / 8) * P_w := by
    rw [show (κ₀ + 2) * P_w + (k₁ / 16) * P_w = (κ₀ + 2 + k₁ / 16) * P_w by ring]
    exact mul_le_mul_of_nonneg_right (by linarith only [hP_floor]) hPw0
  have hS_rem : (κ₀ + 2) * S_w + (g₀ * L / (64 * c ^ 7)) * S7_w ≤
      (g₀ * L / (32 * c ^ 7)) * S7_w := by
    have h1 := (mul_le_mul_of_nonneg_right hS_floor hSw0).trans
      (mul_le_mul_of_nonneg_left hSw_S7 (by positivity))
    have hid : (g₀ * L / (32 * c ^ 7)) * S7_w =
        2 * ((g₀ * L / (64 * c ^ 7)) * S7_w) := by field_simp [hc0.ne']; ring
    linarith only [h1, hid]
  have hid_P : (k₁ / 4) * P_w = (k₁ / 8) * P_w + (k₁ / 8) * P_w := by ring
  have hid_S : (g₀ * L / (16 * c ^ 7)) * S7_w =
      (g₀ * L / (32 * c ^ 7)) * S7_w + (g₀ * L / (32 * c ^ 7)) * S7_w := by
    field_simp [hc0.ne']; ring
  rw [hw_split, mul_add]
  linarith only [hpartB, hband2, hleak_le, hP_rem, hS_rem, hid_P, hid_S]

private lemma all_ratio_k1_S7_floors {L ℓ k₁ D g₀ κ₀ K_c c : ℝ}
    (hD : 0 < D) (hg₀ : 0 < g₀) (hκ₀ : 0 < κ₀) (hKc0 : 0 < K_c) (hL0 : 0 < L)
    (hℓ0 : 0 < ℓ) (hc0 : 0 < c) (hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ))
    (hk₁_eq : k₁ = L / (2 * D * ℓ ^ 5))
    (hpoly5 : 2 * ℓ ^ 5 ≤ L ^ (1 / 4 : ℝ))
    (hfl_p : 32 * D * (κ₀ + 2) ≤ L ^ (3 / 4 : ℝ))
    (hfl_s : 64 * (κ₀ + 2) * K_c ^ 7 / g₀ ≤ L ^ (1 / 8 : ℝ)) :
    κ₀ + 2 ≤ k₁ / 16 ∧ κ₀ + 2 ≤ g₀ * L / (64 * c ^ 7) := by
  have hk₁_lb : L ^ (3 / 4 : ℝ) / D ≤ k₁ := by
    rw [hk₁_eq, div_le_div_iff₀ hD (by positivity)]
    calc L ^ (3 / 4 : ℝ) * (2 * D * ℓ ^ 5)
        = D * (L ^ (3 / 4 : ℝ) * (2 * ℓ ^ 5)) := by ring
      _ ≤ D * (L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpoly5 (by positivity)) hD.le
      _ = L * D := by rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]; ring
  have hP_floor : κ₀ + 2 ≤ k₁ / 16 := by
    have h2 : κ₀ + 2 ≤ (L ^ (3 / 4 : ℝ) / D) / 16 := by
      rw [le_div_iff₀ (by norm_num), le_div_iff₀ hD]
      have hpos : 0 ≤ (κ₀ + 2) * 16 * D := by positivity
      linarith only [hfl_p, hpos, (by ring : 32 * D * (κ₀ + 2) = 2 * ((κ₀ + 2) * 16 * D))]
    exact h2.trans (div_le_div_of_nonneg_right hk₁_lb (by norm_num))
  refine ⟨hP_floor, ?_⟩
  have hc7_hi : c ^ 7 ≤ K_c ^ 7 * L ^ (7 / 8 : ℝ) := by
    have hp := pow_le_pow_left₀ hc0.le hc_up 7
    rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
    exact hp.trans_eq (by congr 2; push_cast; ring)
  have hLc7 : L ^ (1 / 8 : ℝ) / K_c ^ 7 ≤ L / c ^ 7 := by
    rw [div_le_div_iff₀ (pow_pos hKc0 7) (pow_pos hc0 7)]
    have hsplit : L ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
    calc L ^ (1 / 8 : ℝ) * c ^ 7
        ≤ L ^ (1 / 8 : ℝ) * (K_c ^ 7 * L ^ (7 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left hc7_hi (Real.rpow_nonneg hL0.le (1 / 8))
      _ = (L ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ)) * K_c ^ 7 := by ring
      _ = L * K_c ^ 7 := by rw [hsplit]
  rw [le_div_iff₀ (by positivity)]
  have h1 : 64 * (κ₀ + 2) ≤ g₀ * (L ^ (1 / 8 : ℝ) / K_c ^ 7) := by
    have hm := (div_le_iff₀ hg₀).mp hfl_s
    rw [← mul_div_assoc, le_div_iff₀ (pow_pos hKc0 7), mul_comm g₀]
    exact hm
  have h2 := h1.trans (mul_le_mul_of_nonneg_left hLc7 hg₀.le)
  have h3 : g₀ * (L / c ^ 7) * c ^ 7 = g₀ * L := by field_simp [hc0.ne']
  have h4 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ c ^ 7)
  linarith only [h4, h3, (by ring : 64 * (κ₀ + 2) * c ^ 7 = (κ₀ + 2) * (64 * c ^ 7))]

/-- **All-ratio complement Gårding and deterministic far-sector bridge above `⌊(log N)^{13/32}⌋₊`.**
For every `R_max > 0`, splitting any `z ∈ (conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ` orthogonally into
`z = u₀ + u₁ + w` with `w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ` yields simultaneously:
1. All-ratio complement Gårding on `z`, retaining `(κ₀ + 2) ‖z‖²`, prefix mass `(k₁ / 16) P_w`,
   top-collar seventh mass `(g₀ log N / (64 c⁷)) S7_w`, eighth-power exponential mass
   `(c c_W / R_max) W₈(U_w)`, and archimedean Lévy energy `(c / (4 I₂)) levyEnergy U_w` against
   `completeWeilEnergy c N z + (c B_far) ∫ U_w²`;
2. The deterministic energy bridge bounding `completeWeilEnergy c N w` above by
   `completeWeilEnergy c N z` plus an `O(1 / log log N)` fraction of the far block reserves. -/
theorem exists_all_ratio_complement_garding_and_far_bridge :
    ∃ c_W : ℝ, 0 < c_W ∧
      ∀ {R_max : ℝ}, 0 < R_max →
        ∃ B_far : ℝ, 0 < B_far ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
              ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
                z ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ →
                ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
                  w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
                  let x_w := primeHorizonExtension w
                  let M := N / linearDefectCutoff c
                  let y_w := atomicTailCoefficients M x_w
                  let U_w := normalizedCentredAtomicTest tiltedUnitSpline y_w c N
                  let L := Real.log (N : ℝ)
                  let ℓ := 1 + Real.log L
                  let k₁ := L / (2 * explicitConductorCutoffConstant * ℓ ^ 5)
                  (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 +
                      (k₁ / 16) * (∑ n ∈ Icc 1 M, x_w n ^ 2) +
                      (dyadicTopMassConstant * L / (64 * c ^ 7)) *
                        topCollarSeventhMass M N x_w +
                      (c * c_W / R_max) * (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) +
                      (c / (4 * ∫ u, tiltedUnitSpline u ^ 2)) * levyEnergy U_w ≤
                    completeWeilEnergy tiltedUnitSpline c N z +
                      (c * B_far) * ∫ u, U_w u ^ 2 ∧
                  completeWeilEnergy tiltedUnitSpline c N w ≤
                    completeWeilEnergy tiltedUnitSpline c N z +
                      (1 / ℓ) * ((k₁ / 8) * (∑ n ∈ Icc 1 M, x_w n ^ 2) +
                        (dyadicTopMassConstant * L / (32 * c ^ 7)) *
                          topCollarSeventhMass M N x_w) := by
  obtain ⟨c_W, hc_W, hfar_gen⟩ := exists_all_ratio_far_garding
  obtain ⟨C_pr, C_up, C_upT, C_np, hCpr, hCup, hCupT, hCnp, hcross_shape⟩ :=
    exists_band_far_cross_le_reserve_shape
  obtain ⟨C_cross01, hC_cross01, hcross01⟩ := exists_band0_band1_cross_le
  obtain ⟨C_coerc0, C_small0, _hC_coerc0, hC_small0, hcoerc0⟩ :=
    exists_completeWeilEnergy_ge_three_quarters_log_homogeneous
  obtain ⟨C_band1, _hC_band1, hcoerc1⟩ := exists_band1_coercive_homogeneous
  obtain ⟨K_res, hK_res, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  obtain ⟨K_tot, hK_tot, htot⟩ := exists_div_totient_le_loglog
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hg₀ : 0 < dyadicTopMassConstant := dyadicTopMassConstant_pos
  have hκ₀ : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
  obtain ⟨D, hD_eq⟩ : ∃ D, D = explicitConductorCutoffConstant := ⟨_, rfl⟩
  obtain ⟨g₀, hg₀_eq⟩ : ∃ g₀, g₀ = dyadicTopMassConstant := ⟨_, rfl⟩
  obtain ⟨κ₀, hκ₀_eq⟩ : ∃ κ₀, κ₀ = tiltedSplineSpectralFloorConstant := ⟨_, rfl⟩
  rw [← hD_eq] at hD ⊢
  rw [← hg₀_eq] at hg₀ ⊢
  rw [← hκ₀_eq] at hκ₀ ⊢
  refine ⟨c_W, hc_W, fun {R_max} hR => ?_⟩
  obtain ⟨B_far, hB_far, hfar_ev⟩ := hfar_gen hR
  refine ⟨B_far, hB_far, ?_⟩
  obtain ⟨K_c, hKc1, hKc_def⟩ : ∃ K_c : ℝ, 1 ≤ K_c ∧ K_c = (R_max + 1) ^ (1 / 8 : ℝ) :=
    ⟨(R_max + 1) ^ (1 / 8 : ℝ), Real.one_le_rpow (by linarith) (by norm_num), rfl⟩
  obtain ⟨M_bk, hMbk0, hMbk_def⟩ :
      ∃ M_bk : ℝ, 0 ≤ M_bk ∧ M_bk = 1 + 8 * K_c ^ 7 / g₀ :=
    ⟨1 + 8 * K_c ^ 7 / g₀, by positivity, rfl⟩
  obtain ⟨CB, hCB0, hCB_def⟩ :
      ∃ CB : ℝ, 0 ≤ CB ∧ CB = 4 + Real.log (2 * (256 * Real.exp 2 + 4)) + 1 := by
    refine ⟨4 + Real.log (2 * (256 * Real.exp 2 + 4)) + 1, ?_, rfl⟩
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (256 * Real.exp 2 + 4) by nlinarith [Real.exp_pos 2])
    linarith
  obtain ⟨C_U_all, hCU_def⟩ : ∃ C_U_all : ℝ, C_U_all =
      1024 * D * C_pr + 512 * C_pr * M_bk +
      32 * C_np * M_bk * (8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) +
      256 * D * C_up * K_c ^ 2 +
      256 * C_upT * (256 * Real.exp 2 + 4) * K_c ^ 3 * M_bk := ⟨_, rfl⟩
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLlim
  filter_upwards [
    hfar_ev,
    eventually_three_cutoff_bounds_one_ninth (by norm_num : (0 : ℝ) < 13 / 32)
      (by norm_num : (13 / 32 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) < 1 / 4096) le_rfl,
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 1 / 4) 2),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 7 / 8) (2 * D)),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 7
      (by norm_num : (0 : ℝ) < 1 / 8) (8 * C_U_all)),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1
      (by norm_num : (0 : ℝ) < 1 / 128) 2),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 128)).comp hLlim).eventually_ge_atTop
      (max (max (C_small0 * (18 * K_c ^ 4)) (C_cross01 * (4 * K_c ^ 4)))
        (max (32 * C_band1 * K_c ^ 4) (2 * Real.log K_c + 2))),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp hLlim).eventually_ge_atTop
      (max (4 * D + 4) (32 * D * (κ₀ + 2))),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hLlim).eventually_ge_atTop
      (max (128 * (256 * C_pr * CB * M_bk)) (64 * (κ₀ + 2) * K_c ^ 7 / g₀)),
    hllim.eventually_ge_atTop ((κ₀ + 4 + C_coerc0 + Real.log K_c + 3 / 4) / (23 / 128)),
    hllim.eventually_ge_atTop (56 * CB * K_c ^ 7 / (D * g₀)),
    hllim.eventually_ge_atTop (128 * (1024 * D * C_pr + 32 * C_np * M_bk * (8 * K_c * K_tot ^ 2 + 6))),
    hLlim.eventually_ge_atTop (max 3000 (max ((8 * (κ₀ + 3)) ^ 2) (R_max + 1))),
    hres 0 le_rfl 16 (by norm_num),
    eventually_ge_atTop 3] with
      N hfarN hcut hLX hpoly5 hpoly5_78 hpoly7_U hpoly128 hν_max hL34_max hL8_max
      hll_fl0 hll_leak hll_E hL_max hresN hN3
  dsimp only [Function.comp_def] at hν_max hL34_max hL8_max
  obtain ⟨hQ2, hQR₀, -, -, hsqrtQ, hlogQ_lb, hH₀_ub, hlogR₀_lb, h36_R₀, -, -, -⟩ := hcut
  intro c hc1 hc8 z hz_orth
  have hKc0 : 0 < K_c := zero_lt_one.trans_le hKc1
  have hL3000 : 3000 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL_max
  have hL_Lh_gap : (8 * (κ₀ + 3)) ^ 2 ≤ Real.log (N : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hL_max
  have hRL : R_max + 1 ≤ Real.log (N : ℝ) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hL_max
  have hL2 : 2 ≤ Real.log (N : ℝ) := by linarith only [hL3000]
  have hL1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hL3000]
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hN1 : 1 ≤ N := by omega
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc_up : c ≤ K_c * Real.log (N : ℝ) ^ (1 / 8 : ℝ) := by
    rw [hKc_def]
    have h8 : c ^ 8 ≤ (R_max + 1) * Real.log (N : ℝ) := by linarith [hc8, hL0]
    have hp := Real.rpow_le_rpow (pow_nonneg hc0.le 8) h8 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hlhs : (c ^ 8) ^ (1 / 8 : ℝ) = c := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [hlhs, Real.mul_rpow (by linarith only [hR]) hL0.le] at hp
    exact hp
  have hcL : c ≤ Real.log (N : ℝ) := by
    have h8 : c ^ 8 ≤ Real.log (N : ℝ) ^ 8 := by
      have hm : R_max * Real.log (N : ℝ) ≤ Real.log (N : ℝ) ^ 2 := by
        nlinarith only [hRL, hL0]
      exact (hc8.trans hm).trans (pow_le_pow_right₀ hL1 (by norm_num))
    by_contra hlt
    exact not_lt_of_ge h8 (pow_lt_pow_left₀ (lt_of_not_ge hlt) hL0.le (by norm_num))
  have hL34_D : 4 * D + 4 ≤ Real.log (N : ℝ) ^ (3 / 4 : ℝ) := (le_max_left _ _).trans hL34_max
  obtain ⟨hR₀R₁, h1_R₁, h1080_R₁, hgap_lo, hgap_hi, hRN₁⟩ :=
    subexpCutoff_all_ratio_bounds hD hN1 hL3000 hLX hpoly5 hL34_D
  obtain ⟨u₀, u₁, w, hz_eq, hu₀_mem, hu₀_orthQ, hu₁_mem, hu₁_orthR₀, hw_orthR₁, hnorm_z⟩ :=
    telescoped_three_band_orthogonal_split hQR₀ hR₀R₁ hz_orth
  refine ⟨w, hw_orthR₁, ?_⟩
  rw [hz_eq] at hnorm_z ⊢
  have hR₀2 : 2 ≤ ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ := hQ2.trans hQR₀
  have hR₁2 : 2 ≤ subexpCutoff N := hR₀2.trans hR₀R₁
  have h36_R₁ : 36 * (1 + Real.log (subexpCutoff N : ℝ)) ≤ Real.log (N : ℝ) := by
    linarith only [h1080_R₁, Real.log_natCast_nonneg (subexpCutoff N)]
  have h18_R₀ : 18 * (1 + Real.log (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ)) ≤
      Real.log (N : ℝ) := by
    linarith only [h36_R₀, Real.log_natCast_nonneg ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊]
  have h18_R₁ : 18 * (1 + Real.log (subexpCutoff N : ℝ)) ≤ Real.log (N : ℝ) := by
    linarith only [h1080_R₁, Real.log_natCast_nonneg (subexpCutoff N)]
  obtain ⟨hcutN, hwidth, hw1, hrad, hR₀6, hsize_near0, hsize_up0, hR₀_tail, hc5N, hc3R₀4, hc3R₀2,
    -⟩ := rpow_horizon_N_bounds_one_ninth hN1 hR₀2 hc1 (by linarith only [hL3000]) hLX hcL h36_R₀
  obtain ⟨-, -, -, -, hR₁6, hsize_near1, hsize_up1, hR₁_tail, -, -, -, -⟩ :=
    rpow_horizon_N_bounds_one_ninth hN1 hR₁2 hc1 (by linarith only [hL3000]) hLX hcL h36_R₁
  obtain ⟨hRM0, -, hB0_ub, -⟩ :=
    linear_prefix_horizon_bounds_one_ninth hN1 hR₀2 hc1 hL3000 hLX hcL h36_R₀
  obtain ⟨hRM1, hlogM1, hB1_ub, hhalf_M⟩ :=
    linear_prefix_horizon_bounds_one_ninth hN1 hR₁2 hc1 hL3000 hLX hcL h36_R₁
  rw [← hCB_def] at hB0_ub hB1_ub
  have hM2 : 2 ≤ N / linearDefectCutoff c :=
    (hR₁2.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < subexpCutoff N))).trans hRM1
  have hM1 : 1 ≤ N / linearDefectCutoff c := by omega
  have h1c_ℓ : 1 + Real.log c ≤ 1 + Real.log (Real.log (N : ℝ)) := by
    linarith [Real.log_le_log hc0 hcL]
  have hw_orth1 : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw_orthR₁ v (conductorSubspace_mono (by omega : 1 ≤ subexpCutoff N) N hv)
  have hfar_w_raw := hfarN hc1 hc8 hw_orth1
  rw [← hD_eq, ← hg₀_eq] at hfar_w_raw
  obtain ⟨E_extra, hE_def⟩ : ∃ E_extra : ℝ, E_extra =
      (c * B_far) * (∫ u, normalizedCentredAtomicTest tiltedUnitSpline
        (atomicTailCoefficients (N / linearDefectCutoff c) (primeHorizonExtension w)) c N u ^ 2) -
      (c * c_W / R_max) * (∫ u, normalizedCentredAtomicTest tiltedUnitSpline
        (atomicTailCoefficients (N / linearDefectCutoff c) (primeHorizonExtension w)) c N u ^ 2 *
        Real.exp (-(8 * u))) -
      (c / (4 * ∫ u, tiltedUnitSpline u ^ 2)) * levyEnergy
        (normalizedCentredAtomicTest tiltedUnitSpline
          (atomicTailCoefficients (N / linearDefectCutoff c) (primeHorizonExtension w)) c N) :=
    ⟨_, rfl⟩
  have hfar_w_shift :
      (7 / 8 : ℝ) * poleDefect (N / linearDefectCutoff c) (primeHorizonExtension w) +
        (g₀ / (8 * c ^ 7)) * Real.log (N : ℝ) *
          topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) -
        ((1 / (16 * D)) * Real.log (N : ℝ) / (1 + Real.log (Real.log (N : ℝ))) ^ 5) *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) ≤
      completeWeilEnergy tiltedUnitSpline c N w + E_extra := by
    linarith only [hfar_w_raw, hE_def]
  have hband2 := subexp_far_collar_reserve_all_ratio hD_eq hD hg₀ hCB0 hKc1 hc1 hc_up hL2 hR₁2
    hM2 hRM1 hlogM1 hhalf_M hB1_ub h1c_ℓ hgap_lo hgap_hi
    (by linarith only [hll_leak]) hw_orthR₁ hfar_w_shift
  have hVc : 1 + Real.log c ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) := by
    have hlogc : Real.log c ≤ Real.log K_c + (1 / 8 : ℝ) * Real.log (Real.log (N : ℝ)) := by
      have h1 := Real.log_le_log hc0 hc_up
      rwa [Real.log_mul hKc0.ne' (Real.rpow_pos_of_pos hL0 _).ne', Real.log_rpow hL0] at h1
    have hp1 : 2 * (1 + Real.log (Real.log (N : ℝ))) ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) := by
      simpa only [pow_one] using hpoly128
    have hp2 : 2 * Real.log K_c + 2 ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hν_max
    have hll0 : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg hL1
    linarith only [hlogc, hp1, hp2, hll0]
  have hν_b1 : C_small0 * (18 * K_c ^ 4) ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hν_max
  have hν_b2 : C_cross01 * (4 * K_c ^ 4) ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hν_max
  have hν_b6 : 32 * C_band1 * K_c ^ 4 ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hν_max
  have hll_scaled : κ₀ + 4 + C_coerc0 + Real.log K_c + 3 / 4 ≤
      (23 / 128 : ℝ) * Real.log (Real.log (N : ℝ)) :=
    ((div_le_iff₀ (by norm_num : (0 : ℝ) < 23 / 128)).mp hll_fl0).trans_eq (mul_comm _ _)
  obtain ⟨hsmall_band0, hsmall_cross01, hfl0, hfl1⟩ :=
    all_ratio_band0_band1_scalars hc1 hKc1 hc_up hL1 rfl hκ₀ hC_small0 hC_cross01 hVc hsqrtQ
      hlogQ_lb hH₀_ub hlogR₀_lb hR₀_tail hc5N hc3R₀4 hc3R₀2 hν_b1 hν_b2 hν_b6 hll_scaled hL_Lh_gap
  obtain ⟨L, hL_eq⟩ : ∃ L : ℝ, L = Real.log (N : ℝ) := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ_eq⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log L := ⟨_, rfl⟩
  obtain ⟨k₁, hk₁_eq⟩ : ∃ k₁ : ℝ, k₁ = L / (2 * D * ℓ ^ 5) := ⟨_, rfl⟩
  obtain ⟨k, hk_eq⟩ : ∃ k : ℝ, k = L / (2 * D * ℓ ^ 6) := ⟨_, rfl⟩
  obtain ⟨b, hb_eq⟩ : ∃ b : ℝ, b = min (c ^ 7) ((g₀ * D / 4) * ℓ ^ 5) := ⟨_, rfl⟩
  have hL0' : 0 < L := hL_eq ▸ hL0
  have hL1' : 1 ≤ L := hL_eq ▸ hL1
  have hcL' : c ≤ L := hL_eq ▸ hcL
  have hc_up' : c ≤ K_c * L ^ (1 / 8 : ℝ) := hL_eq ▸ hc_up
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ_eq]; linarith [Real.log_nonneg hL1']
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hk_pos : 0 < k := by rw [hk_eq]; positivity
  have hb_pos : 0 < b := by rw [hb_eq]; exact lt_min (pow_pos hc0 7) (by positivity)
  have hb_le_c7 : b ≤ c ^ 7 := by rw [hb_eq]; exact min_le_left _ _
  have hb_le_b0 : b ≤ (g₀ * D / 4) * ℓ ^ 5 := by rw [hb_eq]; exact min_le_right _ _
  have hpoly5_78' : 2 * D * ℓ ^ 5 ≤ L ^ (7 / 8 : ℝ) := by rw [hℓ_eq, hL_eq]; exact hpoly5_78
  have hbk_ub : c ^ 7 / (b * k) ≤ M_bk * ℓ / L ^ (1 / 8 : ℝ) := by
    rw [hMbk_def]
    exact all_ratio_c7_div_bk_le hD hg₀ hL1' hℓ1 hc1 hc_up' hKc1 hk_eq hb_eq hpoly5_78'
  have hRN₁' : L ^ 18 * (subexpCutoff N : ℝ) ^ 16 ≤ N := hL_eq ▸ hRN₁
  have hRN₀ : L ^ 18 * (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ) ^ 16 ≤ N :=
    le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by rw [hL_eq]; exact_mod_cast hR₀R₁) 16)
      (by positivity)) hRN₁'
  have hL3000' : 3000 ≤ L := hL_eq ▸ hL3000
  have hR₀1 : 1 ≤ ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ := by omega
  have hR₀1' : 1 ≤ ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ := hL_eq ▸ hR₀1
  have hRN₀_N : Real.log (N : ℝ) ^ 18 *
      (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ) ^ 16 ≤ N := by
    rw [← hL_eq]; exact hRN₀
  obtain ⟨hceil0, hRK0, h8c, hc4⟩ :=
    near_ceil_side_conditions hR₀1 hc1 hcL (by linarith only [hL3000]) hRN₀_N
  obtain ⟨hceil1, hRK1, -, -⟩ :=
    near_ceil_side_conditions (by omega : 1 ≤ subexpCutoff N) hc1 hcL
      (by linarith only [hL3000]) hRN₁
  obtain ⟨hL3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
  have hNM : (N : ℝ) / (N / linearDefectCutoff c : ℕ) ≤ 2 * (256 * Real.exp 2 + 4) * c := by
    have h1 := nat_div_div_le_two_mul (by omega : 1 ≤ linearDefectCutoff c) hcutN
    linarith only [h1, hTup]
  obtain ⟨Sg₁, hSg₁_eq⟩ :
      ∃ Sg₁ : ℝ, Sg₁ = K_tot * (1 + Real.log (1 + Real.log (subexpCutoff N : ℝ))) := ⟨_, rfl⟩
  have hSg1 : 1 ≤ Sg₁ := by
    have : 0 ≤ Real.log (1 + Real.log (subexpCutoff N : ℝ)) :=
      Real.log_nonneg (by linarith [Real.log_natCast_nonneg (subexpCutoff N)])
    rw [hSg₁_eq]; exact one_le_mul_of_one_le_of_one_le hK_tot (by linarith only [this])
  have hSg_ub : Sg₁ ≤ 2 * K_tot * ℓ := by
    rw [hSg₁_eq, hℓ_eq, hL_eq]
    exact loglog_budget_le (by linarith only [hK_tot]) hL1
      (by linarith only [h1080_R₁, Real.log_natCast_nonneg (subexpCutoff N)])
  obtain ⟨ρ, hρ_eq⟩ : ∃ ρ : ℝ, ρ = K_res *
      (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ((1 : ℝ) / (16 : ℕ)) / L + c ^ 10 * (L / N) ^ 2) :=
    ⟨_, rfl⟩
  have hρ_norm : ‖poleModeResidual c N‖ ^ 2 ≤ ρ := by
    have h := hresN 1 one_pos (by simp) c hc1 hwidth
    simpa only [poleModeResidual, Nat.cast_one, Real.log_one, add_zero, one_pow, one_mul,
      mul_one, hρ_eq, hL_eq] using h
  have hL11 : L ^ 11 ≤ N :=
    le_trans (le_trans (pow_le_pow_right₀ hL1' (by norm_num : 11 ≤ 18))
      (le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (by exact_mod_cast (show 1 ≤ subexpCutoff N by omega))))) hRN₁'
  have hρ_ub : ρ ≤ 2 * K_res * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L) := by
    rw [hρ_eq]
    exact pole_rate_le hK_res.le hc1 hcL' hL1' (k := 16) (by norm_num) (by push_cast; norm_num) hL11
  have hρ0 : 0 ≤ ρ := (sq_nonneg _).trans hρ_norm
  have h1_R₁' : 1 + Real.log (subexpCutoff N : ℝ) ≤ 2 * L / ℓ ^ 5 := by
    rw [hℓ_eq, hL_eq]; exact h1_R₁
  have h1_R₀ : 1 + Real.log (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ) ≤ 2 * L / ℓ ^ 5 := by
    have hle : Real.log (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ) ≤ Real.log (subexpCutoff N : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr hR₀1') (Nat.cast_le.mpr (hL_eq ▸ hR₀R₁))
    linarith only [hle, h1_R₁']
  have hU_small :
      (1024 * D * C_pr + 512 * C_pr * M_bk +
        32 * C_np * M_bk * (8 * K_res * K_c ^ 2 + K_c ^ 2 * (1560 * K_tot + 96) + K_c ^ 4 + 3) +
        256 * D * C_up * K_c ^ 2 +
        256 * C_upT * (256 * Real.exp 2 + 4) * K_c ^ 3 * M_bk) * ℓ ^ 7 ≤
      (1 / 8 : ℝ) * L ^ (1 / 8 : ℝ) := by
    rw [← hCU_def, hℓ_eq, hL_eq]; linarith only [hpoly7_U]
  have hℓ_E : 128 * (1024 * D * C_pr + 32 * C_np * M_bk * (8 * K_c * K_tot ^ 2 + 6)) ≤ ℓ := by
    rw [hℓ_eq, hL_eq]; linarith only [hll_E]
  have hL8_E2 : 128 * (256 * C_pr * CB * M_bk) ≤ L ^ (1 / 8 : ℝ) := by
    rw [hL_eq]; exact (le_max_left _ _).trans hL8_max
  obtain ⟨hsE0, hsU0⟩ := all_ratio_band_far_budgets hL_eq hℓ_eq hk_eq hbk_ub hD hCpr hCup hCupT
    hCnp hCB0 hKc1 hMbk0 hK_tot hK_res.le hL1' hc1 hcL' hc_up' hk_pos hb_pos
    hR₀1' (Nat.div_le_self _ _) hRN₀ h1_R₀ (by rw [hL_eq]; exact hB0_ub) hNM
    hSg_ub (zero_le_one.trans hSg1) hρ0 hρ_ub hℓ_E hL8_E2 hU_small
  obtain ⟨hsE1, hsU1⟩ := all_ratio_band_far_budgets hL_eq hℓ_eq hk_eq hbk_ub hD hCpr hCup hCupT
    hCnp hCB0 hKc1 hMbk0 hK_tot hK_res.le hL1' hc1 hcL' hc_up' hk_pos hb_pos
    (by omega : 1 ≤ subexpCutoff N) (Nat.div_le_self _ _) hRN₁' h1_R₁' hB1_ub hNM
    hSg_ub (zero_le_one.trans hSg1) hρ0 hρ_ub hℓ_E hL8_E2 hU_small
  rw [hL_eq] at hsE0 hsU0
  have htot0 : ∀ m ∈ Icc 2 ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊,
      ((m : ℝ) / m.totient) ≤ Sg₁ := by
    rw [hSg₁_eq]; exact div_totient_le_loglog_of_le hK_tot htot hR₀R₁
  have htot1 : ∀ m ∈ Icc 2 (subexpCutoff N), ((m : ℝ) / m.totient) ≤ Sg₁ := by
    rw [hSg₁_eq]; exact div_totient_le_loglog_of_le hK_tot htot le_rfl
  have hcr0w : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊,
          a₀ m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w' : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        w' ∈ (conductorSubspace (subexpCutoff N) N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊,
            a₀ m • normalizedRamanujanHorizonVector m N), w'⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ a₀ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊,
            a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (k / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w' n ^ 2) +
          (b * k / (32 * c ^ 7)) * (∑ n ∈ Ioc (N / linearDefectCutoff c) N,
            primeHorizonExtension w' n ^ 2) +
          (b * k / (32 * c ^ 7)) * ‖w'‖ ^ 2 := fun a₀ hu₀_1 w' hw' =>
    hcross_shape hR₀2 (by exact_mod_cast hR₀6) hM1 (Nat.div_le_self _ _) h18_R₀ hc1 h8c hc4
      hsize_near0 hsize_up0 hrad hceil0 hRK0 hSg1 htot0
      hρ_norm hk_pos hb_pos hsE0 hsU0 a₀ hu₀_1
      (fun v hv => hw' v (conductorSubspace_mono hR₀R₁ N hv))
  have hcr1w := hcross_shape hR₁2 (by exact_mod_cast hR₁6) hM1 (Nat.div_le_self _ _) h18_R₁ hc1
    h8c hc4 hsize_near1 hsize_up1 hrad hceil1 hRK1 hSg1
    htot1 hρ_norm hk_pos hb_pos hsE1 hsU1
  obtain ⟨hP_floor, hS_floor⟩ := all_ratio_k1_S7_floors hD hg₀ hκ₀ hKc0 hL0' hℓ0 hc0 hc_up'
    hk₁_eq (by rw [hℓ_eq, hL_eq]; exact hpoly5)
    (by rw [hL_eq]; exact (le_max_right _ _).trans hL34_max)
    (by rw [hL_eq]; exact (le_max_right _ _).trans hL8_max)
  have hband2' : (k₁ / 4) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
      (g₀ * L / (16 * c ^ 7)) *
        topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
      completeWeilEnergy tiltedUnitSpline c N w + E_extra := by
    rw [hk₁_eq, hℓ_eq, hL_eq]; exact hband2
  obtain ⟨hbridge_raw, hgarding_raw⟩ := all_ratio_three_band_assembly hQ2 hQR₀ hc1 hD hg₀ hκ₀ hℓ1
    hk₁_eq hk_eq hb_le_c7 hb_le_b0
    (hcoerc0 hQ2 hQR₀ hR₀6 h36_R₀ hc1 hcL hw1 hrad hsize_near0 hsmall_band0)
    (hcoerc1 hR₀2 hR₀R₁ hR₁6 h1080_R₁ hc1 hcL hw1 hsize_near1
      (hR₁_tail.trans ((div_le_one hL0).mpr hL1)))
    (hcross01 hR₀2 hR₀6 h18_R₀ hc1 hw1 hsize_near0 hsize_up0 hH₀_ub hsmall_cross01)
    hcr0w hcr1w hfl0 hfl1 hP_floor hS_floor hu₀_mem hu₀_orthQ hu₁_mem hu₁_orthR₀ hw_orthR₁ hband2'
  rw [hk₁_eq, hℓ_eq, hL_eq] at hbridge_raw hgarding_raw
  have hnorm_fl : (κ₀ + 2) * ‖u₀ + u₁ + w‖ ^ 2 ≤
      (κ₀ + 3) * ‖u₀‖ ^ 2 + (κ₀ + 2 + Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
        (κ₀ + 2) * ‖w‖ ^ 2 := by
    rw [hnorm_z]
    have h1 : 0 ≤ (Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 := by positivity
    nlinarith only [sq_nonneg ‖u₀‖, h1]
  have hu01_nn :
      0 ≤ (κ₀ + 3) * ‖u₀‖ ^ 2 + (κ₀ + 2 + Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 := by
    positivity
  exact ⟨by linarith only [hgarding_raw, hnorm_fl, hE_def], by linarith only [hbridge_raw, hu01_nn]⟩

/-! ### 5. Signed PNT pole-cancellation bridge and high-conductor window confinement -/

private lemma weighted_archForm_add_ge_of_ordered {f g : ℝ → ℝ} {b α : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) (hα : 0 < α) :
    archForm f + archForm g - 2 * Real.pi * (α * (∫ u, f u ^ 2) + α⁻¹ * (∫ u, g u ^ 2)) ≤
      archForm (fun u => f u + g u) := by
  set s := Real.sqrt α
  have hs : 0 < s := Real.sqrt_pos.mpr hα
  have hs2 : s ^ 2 = α := Real.sq_sqrt hα.le
  set f₁ : ℝ → ℝ := fun u => s * f u
  set g₁ : ℝ → ℝ := fun u => s⁻¹ * g u
  have hf₁ : ContDiff ℝ 2 f₁ := contDiff_const.mul hf
  have hf₁c : HasCompactSupport f₁ := hfc.mul_left
  have hg₁ : ContDiff ℝ 2 g₁ := contDiff_const.mul hg
  have hg₁c : HasCompactSupport g₁ := hgc.mul_left
  have hleft₁ : ∀ u, b ≤ u → f₁ u = 0 := fun u hu => by
    dsimp only [f₁]; rw [hleft u hu, mul_zero]
  have hright₁ : ∀ u, u ≤ b → g₁ u = 0 := fun u hu => by
    dsimp only [g₁]; rw [hright u hu, mul_zero]
  have h := ArithmeticIndexDescent.abs_archCross_le_of_ordered hf₁ hf₁c hg₁ hg₁c hleft₁ hright₁
  have hcx1 : cx f₁ = fun u => (s : ℂ) * cx f u := funext fun u => by simp [cx, f₁]
  have hcx2 : cx g₁ = fun u => ((s⁻¹ : ℝ) : ℂ) * cx g u := funext fun u => by simp [cx, g₁]
  have hint_eq :
      (∫ r : ℝ, (paperFT (cx f₁) r * conj (paperFT (cx g₁) r)).re * EF.gammaBracket r) =
        ∫ r : ℝ, (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r := by
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only
    rw [hcx1, hcx2, paperFT_const_mul, paperFT_const_mul, map_mul, Complex.conj_ofReal]
    have hsc : ((s : ℂ) * paperFT (cx f) r) * (((s⁻¹ : ℝ) : ℂ) * conj (paperFT (cx g) r)) =
        paperFT (cx f) r * conj (paperFT (cx g) r) := by
      calc ((s : ℂ) * paperFT (cx f) r) * (((s⁻¹ : ℝ) : ℂ) * conj (paperFT (cx g) r))
          = ((s * s⁻¹ : ℝ) : ℂ) * (paperFT (cx f) r * conj (paperFT (cx g) r)) := by
            push_cast; ring
        _ = paperFT (cx f) r * conj (paperFT (cx g) r) := by
            rw [mul_inv_cancel₀ hs.ne', Complex.ofReal_one, one_mul]
    rw [hsc]
  change |(1 / (2 * Real.pi)) * ∫ r : ℝ,
      (paperFT (cx f₁) r * conj (paperFT (cx g₁) r)).re * EF.gammaBracket r| ≤
    Real.pi * ((∫ u, f₁ u ^ 2) + ∫ u, g₁ u ^ 2) at h
  have hm1 : (∫ u, f₁ u ^ 2) = α * ∫ u, f u ^ 2 := by
    dsimp only [f₁]; simp_rw [mul_pow]; rw [integral_const_mul, hs2]
  have hm2 : (∫ u, g₁ u ^ 2) = α⁻¹ * ∫ u, g u ^ 2 := by
    dsimp only [g₁]; simp_rw [mul_pow]; rw [integral_const_mul, inv_pow, hs2]
  rw [hint_eq, hm1, hm2] at h
  have hlow := (abs_le.mp h).1
  rw [archForm_add_eq hf hfc hg hgc]
  linarith only [hlow]

private lemma weighted_archForm_prefix_top_split_ge {c α : ℝ} (hc1 : 1 ≤ c) (hα : 0 < α) {N : ℕ}
    (hLN : linearDefectCutoff c ≤ N) (hM : 1 ≤ N / linearDefectCutoff c) (x : ℕ → ℝ) :
    let w := c / (N : ℝ)
    let g := atomDilate tiltedUnitSpline w
    let I₂ := ∫ u, tiltedUnitSpline u ^ 2
    let G := w * I₂
    let M := N / linearDefectCutoff c
    let y := atomicTailCoefficients M x
    let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
    archForm (atomicTest M x g) + archForm (atomicTest N y g) -
        2 * Real.pi * (α * (G * ∑ n ∈ Icc 1 M, x n ^ 2) +
          α⁻¹ * (G * ((c / I₂) * ∫ u, U_y u ^ 2))) ≤
      archForm (atomicTest N x g) := by
  intro w g I₂ G M y U_y
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL1 : 1 ≤ linearDefectCutoff c := by omega
  have hN1 : 1 ≤ N := hL1.trans hLN
  have hMN : M ≤ N := Nat.div_le_self N _
  have hML : (M : ℝ) * linearDefectCutoff c ≤ N := by
    dsimp only [M]; exact_mod_cast Nat.div_mul_le_self N _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hLR : (0 : ℝ) < linearDefectCutoff c := by exact_mod_cast hL1
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hw : 0 < w := div_pos hc0 hNR
  have hwN : w * N = c := by dsimp only [w]; field_simp [hNR.ne']
  have hwM : w * M ≤ c / linearDefectCutoff c := by
    apply (le_div_iff₀ hLR).mpr
    calc w * M * linearDefectCutoff c = w * ((M : ℝ) * linearDefectCutoff c) := by ring
      _ ≤ w * N := mul_le_mul_of_nonneg_left hML hw.le
      _ = c := hwN
  have hsep : w < atomSpacing M := by
    have hfour : 4 * w * M ≤ 1 := by
      have hl : 4 * (c / (linearDefectCutoff c : ℝ)) ≤ 1 := by
        rw [← mul_div_assoc, div_le_one hLR]; exact h4c
      nlinarith only [hwM, hl]
    have hbound : w ≤ (1 / ((M : ℝ) + 1)) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).mpr
      nlinarith only [hfour, mul_nonneg hw.le (sub_nonneg.mpr hM1R)]
    linarith only [hbound, (atomSpacing_bounds hM).1, atomSpacing_pos hM]
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hmass : (∫ u, g u ^ 2) = G := integral_atomDilate_sq hw
  obtain ⟨_, hleft, hright⟩ := atomicTest_prefix_tail_ordered hsupp hM hsep N x
  have hcrossA := weighted_archForm_add_ge_of_ordered
    (contDiff_atomicTest hg M x) (hasCompactSupport_atomicTest hsupp M x)
    (contDiff_atomicTest hg N y) (hasCompactSupport_atomicTest hsupp N y) hleft hright hα
  rw [← atomicTest_eq_prefix_add_tail hMN x g] at hcrossA
  have hloMass : (∫ u, atomicTest M x g u ^ 2) = G * ∑ n ∈ Icc 1 M, x n ^ 2 := by
    rw [integral_atomicTest_sq hg hgc hsupp hsep, hmass, mul_comm]
  obtain ⟨_, _, _, hhiMass, _, _⟩ := normalizedCentredAtomicTest_scaling hc0 hN1 y
  dsimp only [w, g, I₂, G, y, U_y] at hhiMass hcrossA hloMass ⊢
  rw [hloMass, hhiMass] at hcrossA
  exact hcrossA

private lemma two_mul_cosh_sq_sub_sinh_sq_collar {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 =
      2 * (∫ u, f u * Real.exp (-(u / 2))) * (∫ u, f u * Real.exp (u / 2)) := by
  have ip : Integrable fun u => f u * Real.exp (u / 2) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have im : Integrable fun u => f u * Real.exp (-(u / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hcosh : coshHalfMoment f =
      ((∫ u, f u * Real.exp (u / 2)) + ∫ u, f u * Real.exp (-(u / 2))) / 2 := by
    unfold coshHalfMoment
    rw [← integral_add ip im, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only; rw [Real.cosh_eq]; ring
  have hsinh : sinhHalfMoment f =
      ((∫ u, f u * Real.exp (u / 2)) - ∫ u, f u * Real.exp (-(u / 2))) / 2 := by
    unfold sinhHalfMoment
    rw [← integral_sub ip im, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only; rw [Real.sinh_eq]; ring
  rw [hcosh, hsinh]; ring

private lemma weilQuad_collar_scaling {N : ℕ} {c : ℝ} (hc0 : 0 < c) (hN1 : 1 ≤ N) (y : ℕ → ℝ) :
    let w := c / (N : ℝ)
    let g := atomDilate tiltedUnitSpline w
    let I₂ := ∫ u, tiltedUnitSpline u ^ 2
    let G := w * I₂
    let f_y := atomicTest N y g
    let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
    archForm f_y - primeSum f_y +
        2 * (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)) =
      G * ((c / I₂) * weilQuad U_y) ∧
    2 * (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)) =
      G * ((c / I₂) *
        (2 * (∫ u, U_y u * Real.exp (-(u / 2))) * (∫ u, U_y u * Real.exp (u / 2)))) := by
  intro w g I₂ G f_y U_y
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  obtain ⟨hUy_cd, hUy_cs, _, _, hfy_arch, hfy_prime⟩ :=
    normalizedCentredAtomicTest_scaling hc0 hN1 y
  have hexp_sqrt : Real.sqrt N = Real.exp (Real.log (N : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN0]; congr 1; ring
  have hUm : ∫ u, U_y u * Real.exp (-(u / 2)) =
      ((N : ℝ) / c) * ∫ v, f_y v * Real.exp (-(v / 2)) := by
    have hfn : (fun u => U_y u * Real.exp (-(u / 2))) =
        fun u => ((N : ℝ) / c) * (f_y (u + Real.log N) * Real.exp (-((u + Real.log N) / 2))) := by
      funext u
      dsimp only [U_y, normalizedCentredAtomicTest, centredAtomicTest, f_y, g, w]
      have h1 : Real.sqrt N * Real.exp (-((u + Real.log N) / 2)) = Real.exp (-(u / 2)) := by
        rw [hexp_sqrt, ← Real.exp_add]; congr 1; ring
      have h2 : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0.le).symm
      calc Real.sqrt N / c * atomicTest N y (atomDilate tiltedUnitSpline (c / N)) (u + Real.log N) *
              Real.exp (-(u / 2))
          = (Real.sqrt N / c) * (Real.sqrt N * Real.exp (-((u + Real.log N) / 2))) *
              atomicTest N y (atomDilate tiltedUnitSpline (c / N)) (u + Real.log N) := by
            rw [h1]; ring
        _ = ((Real.sqrt N * Real.sqrt N) / c) *
              (atomicTest N y (atomDilate tiltedUnitSpline (c / N)) (u + Real.log N) *
                Real.exp (-((u + Real.log N) / 2))) := by ring
        _ = ((N : ℝ) / c) *
              (atomicTest N y (atomDilate tiltedUnitSpline (c / N)) (u + Real.log N) *
                Real.exp (-((u + Real.log N) / 2))) := by rw [← h2]
    rw [hfn, integral_const_mul,
      integral_add_right_eq_self (μ := volume) (fun v => f_y v * Real.exp (-(v / 2))) (Real.log N)]
  have hUp : ∫ u, U_y u * Real.exp (u / 2) =
      (1 / c) * ∫ v, f_y v * Real.exp (v / 2) := by
    have hfn : (fun u => U_y u * Real.exp (u / 2)) =
        fun u => (1 / c) * (f_y (u + Real.log N) * Real.exp ((u + Real.log N) / 2)) := by
      funext u
      dsimp only [U_y, normalizedCentredAtomicTest, centredAtomicTest, f_y, g, w]
      have h1 : Real.sqrt N * Real.exp (u / 2) = Real.exp ((u + Real.log N) / 2) := by
        rw [hexp_sqrt, ← Real.exp_add]; congr 1; ring
      calc Real.sqrt N / c * atomicTest N y (atomDilate tiltedUnitSpline (c / N)) (u + Real.log N) *
              Real.exp (u / 2)
          = (1 / c) * (atomicTest N y (atomDilate tiltedUnitSpline (c / N)) (u + Real.log N) *
              (Real.sqrt N * Real.exp (u / 2))) := by ring
        _ = (1 / c) * (atomicTest N y (atomDilate tiltedUnitSpline (c / N)) (u + Real.log N) *
              Real.exp ((u + Real.log N) / 2)) := by rw [h1]
    rw [hfn, integral_const_mul,
      integral_add_right_eq_self (μ := volume) (fun v => f_y v * Real.exp (v / 2)) (Real.log N)]
  have hpole_scale :
      2 * (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)) =
        G * ((c / I₂) *
          (2 * (∫ u, U_y u * Real.exp (-(u / 2))) * (∫ u, U_y u * Real.exp (u / 2)))) := by
    rw [hUm, hUp]
    dsimp only [G, w]
    field_simp [hc0.ne', hN0.ne', hI₂.ne']
  refine ⟨?_, hpole_scale⟩
  rw [weilQuad_eq hUy_cd hUy_cs, ← archForm_eq_levyEnergy hUy_cd hUy_cs,
    two_mul_cosh_sq_sub_sinh_sq_collar hUy_cd.continuous hUy_cs]
  dsimp only [w, g, I₂, G, f_y, U_y] at hfy_arch hfy_prime hpole_scale ⊢
  linarith only [hfy_arch, hfy_prime, hpole_scale,
    (by ring : G * ((c / I₂) * (archForm U_y - primeSum U_y +
      2 * (∫ u, U_y u * Real.exp (-(u / 2))) * (∫ u, U_y u * Real.exp (u / 2)))) =
      G * ((c / I₂) * archForm U_y) - G * ((c / I₂) * primeSum U_y) +
        G * ((c / I₂) *
          (2 * (∫ u, U_y u * Real.exp (-(u / 2))) * (∫ u, U_y u * Real.exp (u / 2)))))]

private lemma one_sub_div_exp_neg_bounds {h : ℝ} (hh : 0 < h) :
    0 ≤ 1 - (1 - Real.exp (-h)) / h ∧ 1 - (1 - Real.exp (-h)) / h ≤ h := by
  have h1 := Real.add_one_le_exp (-h)
  have h_le : (1 - Real.exp (-h)) / h ≤ 1 := (div_le_one hh).mpr (by linarith only [h1])
  have h2 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp h) (Real.exp_pos (-h)).le
  have h_inv : Real.exp h * Real.exp (-h) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h3 : h * (1 - h) ≤ h * Real.exp (-h) :=
    mul_le_mul_of_nonneg_left (by linarith only [h1]) hh.le
  have h_ge : 1 - h ≤ (1 - Real.exp (-h)) / h :=
    (le_div_iff₀ hh).mpr (by linarith only [h2, h_inv, h3])
  exact ⟨by linarith only [h_le], by linarith only [h_ge]⟩

private lemma two_mul_abs_collar_pole_le {U : ℝ → ℝ}
    (hU : ContDiff ℝ 2 U) (hUc : HasCompactSupport U) (hs : ∀ u, 1 < u → U u = 0) :
    2 * |(∫ u, U u * Real.exp (-(u / 2))) * (∫ u, U u * Real.exp (u / 2))| ≤
      (∫ u, U u ^ 2 * Real.exp (-(8 * u))) + 10 * ∫ u, U u ^ 2 := by
  have hm := sq_exp_neg_half_moment_le_exponential_mass one_pos hU.continuous hUc hs
  have hp := sq_exp_pos_half_moment_le_l2 hU.continuous hUc hs
  set Im := ∫ u, U u * Real.exp (-(u / 2))
  set Ip := ∫ u, U u * Real.exp (u / 2)
  have ham : 2 * |Im * Ip| ≤ Im ^ 2 + Ip ^ 2 := by
    rw [abs_mul]
    nlinarith only [sq_nonneg (|Im| - |Ip|), sq_abs Im, sq_abs Ip]
  have h6 : 1 * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) + (4 + 2 / (1 : ℝ)) * (∫ u, U u ^ 2) =
      (∫ u, U u ^ 2 * Real.exp (-(8 * u))) + 6 * ∫ u, U u ^ 2 := by ring
  linarith only [ham, hm, hp, h6]

private def coherentWindow (a b h σ s : ℝ) : ℝ :=
  (Set.Icc a b).indicator (fun s => Real.sqrt (Real.exp s) * (1 - Real.exp (-h)) * σ) s

private def smoothedCoherent (g : ℝ → ℝ) (a b h σ u : ℝ) : ℝ :=
  h⁻¹ * ∫ t, g t * coherentWindow a b h σ (u - t)

private def offPoleWindowSumBound (C c₀ A : ℝ) (B M K' : ℕ) (x : ℕ → ℝ) (h : ℝ) : ℝ :=
  8 * (h ^ 2 * (prefixMass M x * (1 + Real.log (2 * K'))) +
      (4 * C * pntRate c₀ K' + h ^ 2) ^ 2 * (prefixMass M x * prefixHarmonic M)) *
      (B * Real.exp h) +
    8 * (h ^ 2 * (prefixMass M x * prefixHarmonic M)) *
      ((A * Real.exp h - A) + (B * Real.exp h - B)) +
    2 * shortOrderWeight K' * ∑ k ∈ range K', (Λ k : ℝ) * (h * (B * Real.exp h) / k + 1) *
      (h * prefixMass M x)

private lemma integral_tail_mul_smoothedCoherent_eq {N : ℕ} {c h : ℝ}
    (hc1 : 1 ≤ c) (h2LN : 2 * linearDefectCutoff c ≤ N)
    (hh0 : 0 < h) (hh_quarter : h ≤ 1 / 4)
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ (conductorSubspace 1 N)ᗮ) :
    let w := c / (N : ℝ)
    let g := atomDilate tiltedUnitSpline w
    let x := primeHorizonExtension z
    let M := N / linearDefectCutoff c
    let y := atomicTailCoefficients M x
    let f_y := atomicTest N y g
    let F_coh := smoothedCoherent g (Real.log ((M : ℝ) / 2) + h) (Real.log (N : ℝ) + w) h
      (prefixPoleMoment M x)
    Integrable (fun u => f_y u * F_coh u) ∧
      -2 * (∫ u, f_y u * F_coh u) =
        2 * ((1 - Real.exp (-h)) / h) *
          (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)) := by
  intro w g x M y f_y F_coh
  obtain ⟨hL3, h4c, h256, -⟩ := linearDefectCutoff_bounds hc1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hLN : linearDefectCutoff c ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hM2 : 2 ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
  have hM1 : 1 ≤ M := by omega
  have hMN : M ≤ N := Nat.div_le_self N _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM1
  have hw0 : 0 < w := div_pos hc0 hNR
  have hwN : w * N = c := by dsimp only [w]; field_simp [hNR.ne']
  have hw256 : w * 256 ≤ 1 := by
    have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hLN
    have h1 : w * (256 * Real.exp 2 * c) ≤ c := by
      have := mul_le_mul_of_nonneg_left (h256.trans hLNR) hw0.le
      linarith only [this, hwN]
    have h2 : w * 256 * Real.exp 2 ≤ 1 :=
      le_of_mul_le_mul_right (by rw [one_mul]; linarith only [h1]) hc0
    exact (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by norm_num))).trans h2
  have hwh_log2 : w + h ≤ Real.log 2 := by
    linarith only [hw256, hh_quarter, Real.log_two_gt_d9]
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hsupp := tiltedUnitSpline_atom_support hw0
  have hfy : ContDiff ℝ 2 f_y := contDiff_atomicTest hg N y
  have hfyc : HasCompactSupport f_y := hasCompactSupport_atomicTest hsupp N y
  have hfy_vanish : ∀ u, u ∉ Set.Icc (Real.log (M : ℝ)) (Real.log (N : ℝ) + w) → f_y u = 0 := by
    intro u hu
    dsimp only [f_y]
    unfold atomicTest
    refine sum_eq_zero fun n hn => ?_
    by_cases hnM : n ≤ M
    · have hy0 : y n = 0 := if_neg (Nat.not_lt.mpr hnM)
      rw [hy0, zero_mul]
    · push Not at hnM
      have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hMn : Real.log (M : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log hMR (by exact_mod_cast hnM.le)
      have hnN : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log hn1 (by exact_mod_cast (mem_Icc.mp hn).2)
      have hnot : u - Real.log (n : ℝ) ∉ Set.Icc 0 w := fun hm =>
        hu ⟨by linarith only [hm.1, hMn], by linarith only [hm.2, hnN]⟩
      dsimp only [g]
      rw [hsupp _ hnot, mul_zero]
  set Ig := ∫ t, g t * Real.exp (-(t / 2))
  set σ := prefixPoleMoment M x
  have hFcoh_on : ∀ u ∈ Set.Icc (Real.log (M : ℝ)) (Real.log (N : ℝ) + w),
      F_coh u = ((1 - Real.exp (-h)) / h) * (Ig * σ) * Real.exp (u / 2) := by
    intro u hu
    dsimp only [F_coh, smoothedCoherent]
    have hpt : (fun t => g t * coherentWindow (Real.log ((M : ℝ) / 2) + h)
          (Real.log (N : ℝ) + w) h σ (u - t)) =
        fun t => ((1 - Real.exp (-h)) * σ * Real.exp (u / 2)) * (g t * Real.exp (-(t / 2))) := by
      funext t
      by_cases ht : t ∈ Set.Icc 0 w
      · have hlogM2 : Real.log ((M : ℝ) / 2) = Real.log (M : ℝ) - Real.log 2 :=
          Real.log_div hMR.ne' two_ne_zero
        have hmem : u - t ∈ Set.Icc (Real.log ((M : ℝ) / 2) + h) (Real.log (N : ℝ) + w) :=
          ⟨by linarith only [hu.1, ht.2, hwh_log2, hlogM2], by linarith only [hu.2, ht.1]⟩
        dsimp only [coherentWindow]
        rw [Set.indicator_of_mem hmem]
        have hsq : Real.sqrt (Real.exp (u - t)) = Real.exp (u / 2) * Real.exp (-(t / 2)) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
          congr 1; ring
        rw [hsq]; ring
      · dsimp only [g]
        rw [hsupp t ht, zero_mul, zero_mul, mul_zero]
    rw [hpt, integral_const_mul]
    dsimp only [Ig]
    field_simp [hh0.ne']
  have hprod_eq : (fun u => f_y u * F_coh u) =
      fun u => (((1 - Real.exp (-h)) / h) * (Ig * σ)) * (f_y u * Real.exp (u / 2)) := by
    funext u
    by_cases hu : u ∈ Set.Icc (Real.log (M : ℝ)) (Real.log (N : ℝ) + w)
    · rw [hFcoh_on u hu]; ring
    · rw [hfy_vanish u hu, zero_mul, zero_mul, mul_zero]
  have i_base : Integrable fun u => f_y u * Real.exp (u / 2) :=
    (hfy.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hfyc.mul_right
  have i_prod : Integrable fun u => f_y u * F_coh u := by
    rw [hprod_eq]; exact i_base.const_mul _
  refine ⟨i_prod, ?_⟩
  have hpole := poleFunctional_eq_zero_of_mem_conductorSubspace_one_orthogonal hN2 hz
  change ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 at hpole
  have hsplit_pole : ∑ n ∈ Icc 1 N, x n / Real.sqrt n =
      prefixPoleMoment M x + ∑ n ∈ Icc 1 N, y n / Real.sqrt n := by
    have hdisj : Icc 1 N = Icc 1 M ∪ Ioc M N := by
      ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    have hy_sum : ∑ n ∈ Icc 1 N, y n / Real.sqrt n = ∑ n ∈ Ioc M N, x n / Real.sqrt n := by
      rw [hdisj, sum_union (disjoint_left.mpr fun n h1 h2 => by
        simp only [mem_Icc] at h1; simp only [mem_Ioc] at h2; omega)]
      have h0 : ∑ n ∈ Icc 1 M, y n / Real.sqrt n = 0 :=
        sum_eq_zero fun n hn => by
          have hy0 : y n = 0 := if_neg (Nat.not_lt.mpr (mem_Icc.mp hn).2)
          rw [hy0, zero_div]
      have h1 : ∑ n ∈ Ioc M N, y n / Real.sqrt n = ∑ n ∈ Ioc M N, x n / Real.sqrt n :=
        sum_congr rfl fun n hn => by
          have hy1 : y n = x n := if_pos (mem_Ioc.mp hn).1
          rw [hy1]
      rw [h0, h1, zero_add]
    rw [hy_sum, hdisj, sum_union (disjoint_left.mpr fun n h1 h2 => by
      simp only [mem_Icc] at h1; simp only [mem_Ioc] at h2; omega)]
    rfl
  have hσ_eq : σ = -∑ n ∈ Icc 1 N, y n / Real.sqrt n := by
    dsimp only [σ]; linarith only [hpole, hsplit_pole]
  have hIg_σ : Ig * σ = -(∫ u, f_y u * Real.exp (-(u / 2))) := by
    have hm := integral_atomicTest_mul_exp_neg_half hg.continuous hsupp N y
    change ∫ u, f_y u * Real.exp (-(u / 2)) = Ig * ∑ n ∈ Icc 1 N, y n / Real.sqrt n at hm
    rw [hσ_eq, mul_neg, ← hm]
  rw [hprod_eq, integral_const_mul, hIg_σ]
  ring

private lemma abs_windowSum_sub_coherentWindow_le {C c₀ t₀ : ℝ} (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hpnt : ∀ ⦃h X Y : ℝ⦄, 0 < h → h ≤ 1 → Y = X * Real.exp (-h) → t₀ ≤ Y →
      |∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k - Real.sqrt X * (1 - Real.exp (-h))| ≤
        Real.sqrt X * (4 * C * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2))
    {A w : ℝ} {B K M N K' : ℕ} {h s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hA1 : 1 ≤ A) (hM : 1 ≤ M) (hMA : (M : ℝ) ≤ 2 * A) (hAB : A ≤ B) (hBK : B < K)
    (hN1 : 1 ≤ N) (hBNw : (B : ℝ) ≤ N * Real.exp w)
    (hK' : 1 ≤ K') (ht₀ : t₀ ≤ K' * Real.exp (-1)) (hAs : A ≤ Real.exp s) (x : ℕ → ℝ) :
    |windowSum B (fun n => topWeight A B n * primeConv K M x n) h s -
        coherentWindow (Real.log A + h) (Real.log (N : ℝ) + w) h (prefixPoleMoment M x) s| ≤
      Real.sqrt (Real.exp s) *
        ((Set.Icc (Real.log (B : ℝ)) (Real.log (N : ℝ) + w)).indicator (fun _ => (1 : ℝ)) s *
            h * |prefixPoleMoment M x| +
          h * Real.sqrt (prefixMass M x * (1 + Real.log (2 * K'))) +
          (4 * C * pntRate c₀ K' + h ^ 2) * Real.sqrt (prefixMass M x * prefixHarmonic M) +
          (if A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B then 0 else 1) * h *
            Real.sqrt (prefixMass M x * prefixHarmonic M)) +
      ∑ k ∈ range K', vonMangoldtAtom k *
        ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := by
  have hA0 : 0 < A := by linarith
  have hB0 : (0 : ℝ) < B := hA0.trans_le hAB
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [windowSum_topWeight_primeConv hA1 x h s]
  set P := prefixMass M x
  set H := prefixHarmonic M
  set σ := prefixPoleMoment M x
  set ε := pntRate c₀ K'
  set E := Real.sqrt (Real.exp s)
  set ψ := fun m => windowPrimeSum A B K h s m
  change |∑ m ∈ Icc 1 M, x m * ψ m - coherentWindow (Real.log A + h) (Real.log (N : ℝ) + w) h σ s| ≤
    E *
      ((Set.Icc (Real.log (B : ℝ)) (Real.log (N : ℝ) + w)).indicator (fun _ => (1 : ℝ)) s *
          h * |σ| +
        h * Real.sqrt (P * (1 + Real.log (2 * K'))) +
        (4 * C * ε + h ^ 2) * Real.sqrt (P * H) +
        (if A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B then 0 else 1) * h *
          Real.sqrt (P * H)) +
    ∑ k ∈ range K', vonMangoldtAtom k *
      ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))
  set Ψa := fun m : ℕ => ∑ k ∈ Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊, vonMangoldtAtom k
  set Ψ₀ := fun m : ℕ => E * (1 - Real.exp (-h)) / Real.sqrt m
  set shortS := (Icc 1 M).filter (fun m : ℕ => Real.exp s < K' * m)
  set longS := (Icc 1 M).filter (fun m : ℕ => ¬ Real.exp s < K' * m)
  have hE : 0 < E := Real.sqrt_pos.mpr (Real.exp_pos s)
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hH : 0 ≤ H := sum_nonneg fun m _ => by positivity
  have heh := one_sub_exp_neg_le h
  have heh0 := one_sub_exp_neg_nonneg hh.le
  have hK'0 : (0 : ℝ) < K' := by exact_mod_cast hK'
  have hsubS : shortS ⊆ Icc 1 M := filter_subset _ _
  have hsubL : longS ⊆ Icc 1 M := filter_subset _ _
  have hψ0 : ∀ m, 0 ≤ ψ m := fun m => windowPrimeSum_nonneg A B K h s m
  have hψa : ∀ m ∈ Icc 1 M, ψ m ≤ Ψa m := fun m hm => windowPrimeSum_le_all (mem_Icc.mp hm).1
  have hΨ₀ : ∀ m, 0 ≤ Ψ₀ m := fun m => div_nonneg (mul_nonneg hE.le heh0) (Real.sqrt_nonneg _)
  have hlong : ∀ m ∈ longS, |Ψa m - Ψ₀ m| ≤ (4 * C * ε + h ^ 2) * (1 / Real.sqrt m) * E := by
    intro m hm
    obtain ⟨hmI, hml⟩ := mem_filter.mp hm
    have hm1 := (mem_Icc.mp hmI).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    push Not at hml
    set X := Real.exp s / m
    set Y := Real.exp (s - h) / m
    have hYX : Y = X * Real.exp (-h) := by
      dsimp only [X, Y]; rw [Real.exp_sub, Real.exp_neg]; ring
    have hXK : (K' : ℝ) ≤ X := (le_div_iff₀ hm0).mpr hml
    have hYK : (K' : ℝ) * Real.exp (-1) ≤ Y := by
      rw [hYX]
      exact mul_le_mul hXK (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        (hK'0.le.trans hXK)
    have hb := hpnt hh hh1 hYX (ht₀.trans hYK)
    have hεY : Real.exp (-c₀ * Real.sqrt (Real.log Y)) ≤ ε := by
      dsimp only [ε]; unfold pntRate
      apply Real.exp_le_exp.mpr
      have : Real.sqrt (Real.log (K' * Real.exp (-1))) ≤ Real.sqrt (Real.log Y) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by positivity) hYK)
      nlinarith
    have hsX : Real.sqrt X = E * (1 / Real.sqrt m) := by
      dsimp only [X, E]; rw [Real.sqrt_div (Real.exp_pos s).le]; ring
    have hΨ₀m : Ψ₀ m = Real.sqrt X * (1 - Real.exp (-h)) := by
      dsimp only [Ψ₀]; rw [hsX]; ring
    have hΨam : Ψa m = ∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k := rfl
    rw [hΨam, hΨ₀m]
    refine hb.trans ?_
    rw [hsX]
    have hle : 4 * C * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2 ≤ 4 * C * ε + h ^ 2 := by
      nlinarith
    calc E * (1 / Real.sqrt m) * (4 * C * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2)
        ≤ E * (1 / Real.sqrt m) * (4 * C * ε + h ^ 2) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (4 * C * ε + h ^ 2) * (1 / Real.sqrt m) * E := by ring
  have hcoh : ∑ m ∈ Icc 1 M, x m * Ψ₀ m = E * (1 - Real.exp (-h)) * σ := by
    dsimp only [Ψ₀, σ, prefixPoleMoment]; rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have hCS : ∀ S' ⊆ Icc 1 M, ∑ m ∈ S', |x m| * (1 / Real.sqrt m) ≤ Real.sqrt (P * H) := by
    intro S' hS'
    have := sum_abs_div_sqrt_le S' x
    simp only [mul_one_div]
    exact this.trans (sqrt_mul_sum_le_of_subset hS' x)
  have hshortH : ∑ m ∈ shortS, (1 : ℝ) / m ≤ 1 + Real.log (2 * K') := by
    have hsub : shortS ⊆ (Icc 1 M).filter (fun m : ℕ => (M : ℝ) / (2 * K') < m) := by
      intro m hm
      obtain ⟨hmI, hms⟩ := mem_filter.mp hm
      refine mem_filter.mpr ⟨hmI, ?_⟩
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    exact (sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity).trans
      (sum_inv_filter_gt_le hM (by exact_mod_cast hK'))
  have hshortCS : ∑ m ∈ shortS, |x m| * (1 / Real.sqrt m) ≤
      Real.sqrt (P * (1 + Real.log (2 * K'))) := by
    have := sum_abs_div_sqrt_le shortS x
    simp only [mul_one_div]
    refine this.trans (Real.sqrt_le_sqrt (mul_le_mul
      (sum_le_sum_of_subset_of_nonneg hsubS fun m _ _ => sq_nonneg _) hshortH
      (sum_nonneg fun m _ => by positivity) hP))
  have hshort : ∑ m ∈ shortS, |x m| * ψ m ≤ ∑ k ∈ range K', vonMangoldtAtom k *
      ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := by
    calc ∑ m ∈ shortS, |x m| * ψ m
        ≤ ∑ m ∈ shortS, |x m| * ∑ k ∈ range K', vonMangoldtAtom k *
            windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) :=
          sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
            (windowPrimeSum_le_short (mem_Icc.mp (mem_filter.mp hm).1).1 (mem_filter.mp hm).2)
            (abs_nonneg _)
      _ ≤ ∑ m ∈ Icc 1 M, |x m| * ∑ k ∈ range K', vonMangoldtAtom k *
            windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg hsubS fun m _ _ => mul_nonneg (abs_nonneg _)
            (sum_nonneg fun k _ => mul_nonneg (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
              (windowKernel_nonneg _ _))
      _ = _ := by
          simp_rw [mul_sum]; rw [sum_comm]
          exact sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
  have hshortΨ₀ : ∑ m ∈ shortS, |x m| * Ψ₀ m ≤
      E * h * Real.sqrt (P * (1 + Real.log (2 * K'))) := by
    have e : ∀ m, |x m| * Ψ₀ m = E * (1 - Real.exp (-h)) * (|x m| * (1 / Real.sqrt m)) :=
      fun m => by dsimp only [Ψ₀]; ring
    simp_rw [e]; rw [← mul_sum]
    exact mul_le_mul (mul_le_mul_of_nonneg_left heh hE.le) hshortCS
      (sum_nonneg fun m _ => by positivity) (by positivity)
  have hlongB : ∑ m ∈ longS, |x m| * |Ψa m - Ψ₀ m| ≤
      E * (4 * C * ε + h ^ 2) * Real.sqrt (P * H) := by
    calc ∑ m ∈ longS, |x m| * |Ψa m - Ψ₀ m|
        ≤ ∑ m ∈ longS, |x m| * ((4 * C * ε + h ^ 2) * (1 / Real.sqrt m) * E) :=
          sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hlong m hm) (abs_nonneg _)
      _ = E * (4 * C * ε + h ^ 2) * ∑ m ∈ longS, |x m| * (1 / Real.sqrt m) := by
          rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
      _ ≤ E * (4 * C * ε + h ^ 2) * Real.sqrt (P * H) :=
          mul_le_mul_of_nonneg_left (hCS longS hsubL) (by positivity)
  have hallΨ₀ : ∑ m ∈ Icc 1 M, |x m| * Ψ₀ m ≤ E * h * Real.sqrt (P * H) := by
    have e : ∀ m, |x m| * Ψ₀ m = E * (1 - Real.exp (-h)) * (|x m| * (1 / Real.sqrt m)) :=
      fun m => by dsimp only [Ψ₀]; ring
    simp_rw [e]; rw [← mul_sum]
    exact mul_le_mul (mul_le_mul_of_nonneg_left heh hE.le) (hCS _ subset_rfl)
      (sum_nonneg fun m _ => by positivity) (by positivity)
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 M) (fun m : ℕ => Real.exp s < K' * m)
    (fun m => x m * ψ m)
  have habsShort : |∑ m ∈ shortS, x m * ψ m| ≤ ∑ m ∈ shortS, |x m| * ψ m := by
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun m _ => ?_))
    rw [abs_mul, abs_of_nonneg (hψ0 m)]
  by_cases hint : A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B
  · rw [if_pos hint, zero_mul, zero_mul, add_zero]
    have hs1 : Real.log A + h ≤ s := by
      have := Real.log_le_log hA0 hint.1
      rw [Real.log_exp] at this; linarith only [this]
    have hs2 : s ≤ Real.log (N : ℝ) + w := by
      have := Real.log_le_log (Real.exp_pos s) (hint.2.trans hBNw)
      rw [Real.log_exp, Real.log_mul hN0.ne' (Real.exp_pos w).ne', Real.log_exp] at this
      exact this
    have hWc_eq : coherentWindow (Real.log A + h) (Real.log (N : ℝ) + w) h σ s =
        E * (1 - Real.exp (-h)) * σ :=
      Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hs1, hs2⟩) _
    rw [hWc_eq]
    have heq : ∀ m ∈ Icc 1 M, ψ m = Ψa m := fun m hm =>
      windowPrimeSum_eq_all (mem_Icc.mp hm).1 hint.1 hint.2 hBK
    have hdec : ∑ m ∈ Icc 1 M, x m * ψ m - E * (1 - Real.exp (-h)) * σ =
        -(∑ m ∈ shortS, x m * Ψ₀ m) + ∑ m ∈ shortS, x m * ψ m +
          ∑ m ∈ longS, x m * (Ψa m - Ψ₀ m) := by
      have hs2' := sum_filter_add_sum_filter_not (Icc 1 M) (fun m : ℕ => Real.exp s < K' * m)
        (fun m => x m * Ψ₀ m)
      have hlongeq : ∑ m ∈ longS, x m * ψ m = ∑ m ∈ longS, x m * Ψa m :=
        sum_congr rfl fun m hm => by rw [heq m (hsubL hm)]
      have hlongsub : ∑ m ∈ longS, x m * (Ψa m - Ψ₀ m) =
          ∑ m ∈ longS, x m * Ψa m - ∑ m ∈ longS, x m * Ψ₀ m := by
        rw [← sum_sub_distrib]; exact sum_congr rfl fun m _ => by ring
      rw [← hcoh]
      dsimp only [shortS, longS] at hs2' hlongeq hlongsub hsplit ⊢
      linarith only [hsplit, hs2', hlongeq, hlongsub]
    rw [hdec]
    have h2 : |∑ m ∈ shortS, x m * Ψ₀ m| ≤ E * h * Real.sqrt (P * (1 + Real.log (2 * K'))) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans (le_of_eq (sum_congr rfl fun m _ => ?_)) hshortΨ₀
      rw [abs_mul, abs_of_nonneg (hΨ₀ m)]
    have h3 : |∑ m ∈ longS, x m * (Ψa m - Ψ₀ m)| ≤ E * (4 * C * ε + h ^ 2) * Real.sqrt (P * H) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans (le_of_eq (sum_congr rfl fun m _ => ?_)) hlongB
      rw [abs_mul]
    have htri : |-(∑ m ∈ shortS, x m * Ψ₀ m) + ∑ m ∈ shortS, x m * ψ m +
        ∑ m ∈ longS, x m * (Ψa m - Ψ₀ m)| ≤
        |∑ m ∈ shortS, x m * Ψ₀ m| + |∑ m ∈ shortS, x m * ψ m| +
          |∑ m ∈ longS, x m * (Ψa m - Ψ₀ m)| := by
      have t1 := abs_add_le (-(∑ m ∈ shortS, x m * Ψ₀ m) + ∑ m ∈ shortS, x m * ψ m)
        (∑ m ∈ longS, x m * (Ψa m - Ψ₀ m))
      have t2 := abs_add_le (-(∑ m ∈ shortS, x m * Ψ₀ m)) (∑ m ∈ shortS, x m * ψ m)
      rw [abs_neg] at t2
      linarith only [t1, t2]
    have hind0 : 0 ≤ E * ((Set.Icc (Real.log (B : ℝ)) (Real.log (N : ℝ) + w)).indicator
        (fun _ => (1 : ℝ)) s * h * |σ|) :=
      mul_nonneg hE.le (mul_nonneg (mul_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) s) hh.le) (abs_nonneg _))
    linarith [htri, h2, h3, habsShort, hshort, hind0]
  · rw [if_neg hint, one_mul]
    have hlongψ : |∑ m ∈ longS, x m * ψ m| ≤ E * h * Real.sqrt (P * H) +
        E * (4 * C * ε + h ^ 2) * Real.sqrt (P * H) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hpt : ∀ m ∈ longS, |x m * ψ m| ≤ |x m| * Ψ₀ m + |x m| * |Ψa m - Ψ₀ m| := by
        intro m hm
        rw [abs_mul, abs_of_nonneg (hψ0 m), ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        linarith [hψa m (hsubL hm), le_abs_self (Ψa m - Ψ₀ m)]
      refine (sum_le_sum hpt).trans ?_
      rw [sum_add_distrib]
      exact add_le_add
        ((sum_le_sum_of_subset_of_nonneg hsubL fun m _ _ =>
          mul_nonneg (abs_nonneg _) (hΨ₀ m)).trans hallΨ₀) hlongB
    have htotW : |∑ m ∈ Icc 1 M, x m * ψ m| ≤
        |∑ m ∈ shortS, x m * ψ m| + |∑ m ∈ longS, x m * ψ m| := by
      dsimp only [shortS, longS]; rw [← hsplit]; exact abs_add_le _ _
    have hWc_edge : |coherentWindow (Real.log A + h) (Real.log (N : ℝ) + w) h σ s| ≤
        E * ((Set.Icc (Real.log (B : ℝ)) (Real.log (N : ℝ) + w)).indicator
          (fun _ => (1 : ℝ)) s * h * |σ|) := by
      dsimp only [coherentWindow]
      by_cases hm : s ∈ Set.Icc (Real.log A + h) (Real.log (N : ℝ) + w)
      · rw [Set.indicator_of_mem hm]
        have hAs_h : A ≤ Real.exp (s - h) := by
          rw [← Real.exp_log hA0]; exact Real.exp_le_exp.mpr (by linarith only [hm.1])
        have hBs : (B : ℝ) < Real.exp s := by
          by_contra hle; exact hint ⟨hAs_h, not_lt.mp hle⟩
        have hlogB : Real.log (B : ℝ) ≤ s :=
          (Real.log_lt_log hB0 hBs).le.trans_eq (Real.log_exp s)
        rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hlogB, hm.2⟩), one_mul,
          abs_mul, abs_mul, abs_of_pos hE, abs_of_nonneg heh0, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heh hE.le) (abs_nonneg _)
      · rw [Set.indicator_of_notMem hm, abs_zero]
        exact mul_nonneg hE.le (mul_nonneg (mul_nonneg
          (Set.indicator_nonneg (fun _ _ => zero_le_one) s) hh.le) (abs_nonneg _))
    have hsub_abs := abs_sub (∑ m ∈ Icc 1 M, x m * ψ m)
      (coherentWindow (Real.log A + h) (Real.log (N : ℝ) + w) h σ s)
    have hE1 : 0 ≤ E * h * Real.sqrt (P * (1 + Real.log (2 * K'))) :=
      mul_nonneg (mul_nonneg hE.le hh.le) (Real.sqrt_nonneg _)
    linarith [hsub_abs, htotW, habsShort, hshort, hlongψ, hWc_edge, hE1]

private lemma integral_windowSum_sub_coherentWindow_sq_le {C c₀ t₀ : ℝ} (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hpnt : ∀ ⦃h X Y : ℝ⦄, 0 < h → h ≤ 1 → Y = X * Real.exp (-h) → t₀ ≤ Y →
      |∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k - Real.sqrt X * (1 - Real.exp (-h))| ≤
        Real.sqrt X * (4 * C * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2))
    {A w : ℝ} {M N K' : ℕ} {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hw0 : 0 ≤ w)
    (hA1 : 1 ≤ A) (hM : 1 ≤ M) (hMA : (M : ℝ) ≤ 2 * A)
    (hN1 : 1 ≤ N) (hAB : A ≤ ⌊(N : ℝ) * Real.exp w⌋₊) (hNh : 1 ≤ (N : ℝ) * h)
    (hK' : 1 ≤ K') (ht₀ : t₀ ≤ K' * Real.exp (-1)) (x : ℕ → ℝ) :
    let B := ⌊(N : ℝ) * Real.exp w⌋₊
    let K := primeOrderCutoff N w
    ∫ s, (windowSum B (fun n => topWeight A B n * primeConv K M x n) h s -
        coherentWindow (Real.log A + h) (Real.log (N : ℝ) + w) h (prefixPoleMoment M x) s) ^ 2 ≤
      8 * h ^ 2 * prefixPoleMoment M x ^ 2 + offPoleWindowSumBound C c₀ A B M K' x h := by
  intro B K
  have hA0 : 0 < A := by linarith
  have hB0 : (0 : ℝ) < B := hA0.trans_le hAB
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hBK : B < K := Nat.lt_succ_of_le (Nat.floor_le_ceil _)
  have hBNw : (B : ℝ) ≤ N * Real.exp w := Nat.floor_le (by positivity)
  have hNB : (N : ℝ) ≤ B :=
    by exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hN0.le (Real.one_le_exp hw0))
  have hNw_Bh : (N : ℝ) * Real.exp w ≤ B * Real.exp h := by
    have hlt : (N : ℝ) * Real.exp w < (B : ℝ) + 1 := Nat.lt_floor_add_one _
    have hBh1 : 1 ≤ (B : ℝ) * h :=
      hNh.trans (mul_le_mul_of_nonneg_right hNB hh.le)
    have heh := Real.add_one_le_exp h
    have hm := mul_le_mul_of_nonneg_left heh hB0.le
    linarith only [hlt, hBh1, hm]
  have htop_le : Real.log (N : ℝ) + w ≤ Real.log (B : ℝ) + h := by
    have := Real.log_le_log (by positivity) hNw_Bh
    rwa [Real.log_mul hN0.ne' (Real.exp_pos w).ne', Real.log_exp,
      Real.log_mul hB0.ne' (Real.exp_pos h).ne', Real.log_exp] at this
  set I := Set.Icc (Real.log A) (Real.log (B : ℝ) + h)
  set W := windowSum B (fun n => topWeight A B n * primeConv K M x n) h
  set Wc := coherentWindow (Real.log A + h) (Real.log (N : ℝ) + w) h (prefixPoleMoment M x)
  have hzero : ∀ s ∉ I, W s - Wc s = 0 := by
    intro s hs
    have hW0 : W s = 0 := by
      dsimp only [W]; rw [windowSum_topWeight_primeConv hA1 x h s]
      refine sum_eq_zero fun m _ => ?_
      refine mul_eq_zero_of_right (x m) (sum_eq_zero fun k _ => ?_)
      by_cases ht : topWeight A B (k * m) = 0
      · rw [ht]; ring
      by_cases hwk : windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) = 0
      · rw [hwk]; ring
      exfalso; apply hs
      unfold topWeight at ht
      split_ifs at ht with hAB'
      · obtain ⟨h1, h2⟩ := hAB'
        have hkm0 : (0 : ℝ) < ((k * m : ℕ) : ℝ) := hA0.trans_le h1
        have hmem : s - Real.log ((k * m : ℕ) : ℝ) ∈ Set.Ico 0 h := by
          by_contra hn; exact hwk (Set.indicator_of_notMem hn _)
        have hl1 : Real.log A ≤ Real.log ((k * m : ℕ) : ℝ) := Real.log_le_log hA0 h1
        have hl2 : Real.log ((k * m : ℕ) : ℝ) ≤ Real.log B :=
          Real.log_le_log hkm0 (by exact_mod_cast h2)
        exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      · exact absurd rfl ht
    have hWc0 : Wc s = 0 :=
      Set.indicator_of_notMem (fun hm => hs ⟨by linarith [hm.1], by linarith [hm.2, htop_le]⟩) _
    rw [hW0, hWc0, sub_zero]
  have hWc2_int : Integrable fun s => Wc s ^ 2 := by
    have heq : (fun s => Wc s ^ 2) =
        (Set.Icc (Real.log A + h) (Real.log (N : ℝ) + w)).indicator
          (fun s => (Real.sqrt (Real.exp s) * (1 - Real.exp (-h)) * prefixPoleMoment M x) ^ 2) := by
      funext s; dsimp only [Wc, coherentWindow]
      by_cases hs : s ∈ Set.Icc (Real.log A + h) (Real.log (N : ℝ) + w)
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, sq, zero_mul]
    rw [heq]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      ((Continuous.pow (by fun_prop) 2).integrableOn_Icc)
  have hWc_meas : Measurable Wc :=
    ((by fun_prop : Continuous fun s =>
      Real.sqrt (Real.exp s) * (1 - Real.exp (-h)) * prefixPoleMoment M x).measurable).indicator
      measurableSet_Icc
  have hRW2_int : Integrable fun s => (W s - Wc s) ^ 2 := by
    let V0 : ℕ → ℝ := fun n => topWeight A B n * primeConv K M x n
    refine (((integrable_windowSum_sq B V0 h).const_mul 2).add (hWc2_int.const_mul 2)).mono'
      (((measurable_windowSum B V0 h).sub hWc_meas).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    dsimp only [Pi.add_apply, W, V0]
    nlinarith only [sq_nonneg (W s + Wc s)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := I) (fun s hs => by
    rw [hzero s hs]; ring)]
  set P := prefixMass M x
  set Hm := prefixHarmonic M
  set σ := prefixPoleMoment M x
  set ε := pntRate c₀ K'
  set LK := shortOrderWeight K'
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hHm : 0 ≤ Hm := sum_nonneg fun m _ => by positivity
  have hLK : 0 ≤ LK := sum_nonneg fun k _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  have hlog2K : 0 ≤ 1 + Real.log (2 * K') := by
    have h1 : (1 : ℝ) ≤ K' := by exact_mod_cast hK'
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 * K' by linarith)]
  set c₀_pole := h ^ 2 * σ ^ 2
  set c₁ := h ^ 2 * (P * (1 + Real.log (2 * K'))) + (4 * C * ε + h ^ 2) ^ 2 * (P * Hm)
  set c₂ := h ^ 2 * (P * Hm)
  set J_pole := Set.Icc (Real.log (B : ℝ)) (Real.log (N : ℝ) + w)
  set J₁ := Set.Icc (Real.log A) (Real.log A + h)
  set J₂ := Set.Icc (Real.log (B : ℝ)) (Real.log B + h)
  set F_maj : ℝ → ℝ := fun s =>
    8 * J_pole.indicator Real.exp s * c₀_pole +
      8 * Real.exp s * c₁ +
      8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂ +
      2 * LK * shortWindowSq K' M x (B * Real.exp h) h s
  have hpt : ∀ s ∈ I, (W s - Wc s) ^ 2 ≤ F_maj s := by
    intro s hs
    have hAs : A ≤ Real.exp s := by
      rw [← Real.exp_log hA0]; exact Real.exp_le_exp.mpr hs.1
    have hsB : Real.exp s ≤ B * Real.exp h := by
      rw [← Real.exp_log hB0, ← Real.exp_add]; exact Real.exp_le_exp.mpr hs.2
    have hmaj := abs_windowSum_sub_coherentWindow_le hC hc₀ hpnt hh hh1 hA1 hM hMA hAB hBK
      hN1 hBNw hK' ht₀ hAs x
    have hsq := sq_le_of_abs_le_four_add hmaj
    have hT := sq_shortOrders_le (K' := K') (M := M) x hh.le hsB
    have hE : Real.sqrt (Real.exp s) ^ 2 = Real.exp s := Real.sq_sqrt (Real.exp_pos s).le
    set L_e : ℝ := if A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B then 0 else 1 with hLdef
    have hLL : L_e ^ 2 = L_e := by
      rw [hLdef]; split_ifs <;> norm_num
    set Ip : ℝ := J_pole.indicator (fun _ => (1 : ℝ)) s
    have hIp_exp : Ip ^ 2 * Real.exp s = J_pole.indicator Real.exp s := by
      dsimp only [Ip]; by_cases hm : s ∈ J_pole
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]; ring
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]; ring
    have hedge := edge_mul_exp_le (h := h) (A := A) hB0 hs.1 hs.2
    rw [← hLdef] at hedge
    have h2 := mul_le_mul_of_nonneg_right hedge (by positivity : 0 ≤ c₂)
    have hT' : (∑ k ∈ range K', vonMangoldtAtom k *
        ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))) ^ 2 ≤
        LK * shortWindowSq K' M x (B * Real.exp h) h s := hT
    have hsum : 8 * Real.exp s * ((Ip * h * |σ|) ^ 2 +
        (h * Real.sqrt (P * (1 + Real.log (2 * K')))) ^ 2 +
        ((4 * C * ε + h ^ 2) * Real.sqrt (P * Hm)) ^ 2 +
        (L_e * h * Real.sqrt (P * Hm)) ^ 2) =
        8 * (J_pole.indicator Real.exp s * c₀_pole + Real.exp s * c₁ + L_e * Real.exp s * c₂) := by
      rw [mul_pow, mul_pow, sq_abs, mul_pow, Real.sq_sqrt (mul_nonneg hP hlog2K),
        mul_pow, Real.sq_sqrt (mul_nonneg hP hHm), mul_pow, mul_pow,
        Real.sq_sqrt (mul_nonneg hP hHm), hLL]
      dsimp only [c₀_pole, c₁, c₂]
      linear_combination (8 * h ^ 2 * σ ^ 2) * hIp_exp
    rw [hE] at hsq
    have hsq' : (W s - Wc s) ^ 2 ≤
        8 * (J_pole.indicator Real.exp s * c₀_pole + Real.exp s * c₁ + L_e * Real.exp s * c₂) +
          2 * LK * shortWindowSq K' M x (B * Real.exp h) h s := by
      dsimp only [W, Wc, P, Hm, σ, ε, Ip] at hsq hsum ⊢
      have h2T := mul_le_mul_of_nonneg_left hT' zero_le_two
      rw [← mul_assoc 2 LK] at h2T
      linarith only [hsq, hsum, h2T]
    dsimp only [F_maj]
    linarith [hsq', h2]
  have hexpI : IntegrableOn Real.exp I := Real.continuous_exp.integrableOn_Icc
  have hwin : ∀ k m : ℕ, Integrable fun s => windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) :=
    fun k m => (integrable_windowKernel h).comp_sub_right _
  have hSWS : Integrable fun s => shortWindowSq K' M x (B * Real.exp h) h s := by
    unfold shortWindowSq
    refine integrable_finsetSum _ fun k _ => Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun m _ => (hwin k m).const_mul _
  have hf0 : IntegrableOn (fun s => 8 * J_pole.indicator Real.exp s * c₀_pole) I :=
    ((hexpI.indicator measurableSet_Icc).const_mul 8).mul_const c₀_pole
  have hf1 : IntegrableOn (fun s => 8 * Real.exp s * c₁) I :=
    (hexpI.const_mul 8).mul_const c₁
  have hf2 : IntegrableOn (fun s => 8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂) I :=
    (((hexpI.indicator measurableSet_Icc).add (hexpI.indicator measurableSet_Icc)).const_mul
      8).mul_const c₂
  have hf3 : IntegrableOn (fun s => 2 * LK * shortWindowSq K' M x (B * Real.exp h) h s) I :=
    (hSWS.const_mul _).integrableOn
  have hFi : IntegrableOn F_maj I := ((hf0.add hf1).add hf2).add hf3
  refine (setIntegral_mono_on hRW2_int.integrableOn hFi measurableSet_Icc hpt).trans ?_
  have hlogB_Nw : Real.log (B : ℝ) ≤ Real.log (N : ℝ) + w := by
    have := Real.log_le_log hB0 hBNw
    rwa [Real.log_mul hN0.ne' (Real.exp_pos w).ne', Real.log_exp] at this
  have i0 : ∫ s in I, 8 * J_pole.indicator Real.exp s * c₀_pole ≤ 8 * c₀_pole := by
    have e : (fun s => 8 * J_pole.indicator Real.exp s * c₀_pole) =
        fun s => (8 * c₀_pole) * J_pole.indicator Real.exp s := funext fun s => by ring
    rw [e, integral_const_mul]
    have b0 := setIntegral_indicator_exp_le (I := I) hlogB_Nw
    rw [Real.exp_add, Real.exp_log hN0, Real.exp_log hB0] at b0
    have hfl : (N : ℝ) * Real.exp w - B ≤ 1 := by
      linarith [Nat.lt_floor_add_one ((N : ℝ) * Real.exp w)]
    exact (mul_le_mul_of_nonneg_left (b0.trans hfl) (by positivity)).trans_eq (mul_one _)
  have hlogAB : Real.log A ≤ Real.log B + h := by
    have := Real.log_le_log hA0 hAB; linarith
  have i1 : ∫ s in I, 8 * Real.exp s * c₁ ≤ 8 * c₁ * (B * Real.exp h) := by
    have e : (fun s => 8 * Real.exp s * c₁) = fun s => (8 * c₁) * Real.exp s := funext fun s => by ring
    rw [e, integral_const_mul, integral_exp_Icc hlogAB, Real.exp_add, Real.exp_log hB0,
      Real.exp_log hA0]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have i2 : ∫ s in I, 8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂ ≤
      8 * c₂ * ((A * Real.exp h - A) + (B * Real.exp h - B)) := by
    have e : (fun s => 8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂) =
        fun s => (8 * c₂) * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) := funext fun s => by ring
    rw [e, integral_const_mul, integral_add (hexpI.indicator measurableSet_Icc)
      (hexpI.indicator measurableSet_Icc)]
    have b1 := setIntegral_indicator_exp_le (I := I) (show Real.log A ≤ Real.log A + h by linarith)
    have b2 := setIntegral_indicator_exp_le (I := I) (show Real.log (B : ℝ) ≤ Real.log B + h by linarith)
    rw [Real.exp_add, Real.exp_log hA0] at b1
    rw [Real.exp_add, Real.exp_log hB0] at b2
    exact mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by positivity)
  have i3 : ∫ s in I, 2 * LK * shortWindowSq K' M x (B * Real.exp h) h s ≤
      2 * LK * ∑ k ∈ range K', (Λ k : ℝ) * (h * (B * Real.exp h) / k + 1) * (h * P) := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (setIntegral_le_integral hSWS (Eventually.of_forall fun s =>
      sum_nonneg fun k _ => mul_nonneg (mul_nonneg vonMangoldt_nonneg (by positivity))
        (sum_nonneg fun m _ => mul_nonneg (sq_nonneg _) (windowKernel_nonneg _ _)))).trans
      (le_of_eq ?_)
    unfold shortWindowSq
    rw [integral_finsetSum _ fun k _ => Integrable.const_mul
      (integrable_finsetSum _ fun m _ => (hwin k m).const_mul _) _]
    refine sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun m _ => (hwin k m).const_mul _]
    congr 1; simp only [P, prefixMass, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, integral_windowKernel_sub hh.le]; ring
  have hf01 : IntegrableOn (fun s =>
      8 * J_pole.indicator Real.exp s * c₀_pole + 8 * Real.exp s * c₁) I := hf0.add hf1
  have hf012 : IntegrableOn (fun s =>
      (8 * J_pole.indicator Real.exp s * c₀_pole + 8 * Real.exp s * c₁) +
        8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂) I := hf01.add hf2
  have hsplitF : ∫ s in I, F_maj s =
      (∫ s in I, 8 * J_pole.indicator Real.exp s * c₀_pole) +
        (∫ s in I, 8 * Real.exp s * c₁) +
        (∫ s in I, 8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂) +
        (∫ s in I, 2 * LK * shortWindowSq K' M x (B * Real.exp h) h s) := by
    dsimp only [F_maj]
    rw [integral_add hf012 hf3, integral_add hf01 hf2, integral_add hf0 hf1]
  rw [hsplitF]
  unfold offPoleWindowSumBound
  dsimp only [c₀_pole, c₁, c₂, P, Hm, σ, ε, LK] at i0 i1 i2 i3 ⊢
  linarith [i0, i1, i2, i3]

private lemma offPoleWindowSumBound_div_le {C c₀ A w h c ΛK ΨK : ℝ} {B M K' : ℕ} (x : ℕ → ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hC : 0 ≤ C) (hε : 4 * C * pntRate c₀ K' ≤ h ^ 2)
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hwB : w * B ≤ Real.exp 1 * c) (_hA0 : 0 ≤ A) (hAB : A ≤ B)
    (hLK : shortOrderWeight K' ≤ ΛK) (hΨK : ∑ k ∈ range K', (Λ k : ℝ) ≤ ΨK) :
    (w / h ^ 2) * offPoleWindowSumBound C c₀ A B M K' x h ≤
      (8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
        48 * Real.exp 1 * c * h * prefixHarmonic M +
        2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK)) * prefixMass M x := by
  set P := prefixMass M x
  set H := prefixHarmonic M
  set ε := pntRate c₀ K'
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hH : 0 ≤ H := sum_nonneg fun m _ => by positivity
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hLK0 : 0 ≤ shortOrderWeight K' :=
    sum_nonneg fun k _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  have heh : Real.exp h ≤ Real.exp 1 := Real.exp_le_exp.mpr hh1
  have heh1 : Real.exp h - 1 ≤ 3 * h := by
    have h1 : Real.exp h - 1 ≤ h * Real.exp h := by
      have h2 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-h)) (Real.exp_pos h).le
      have h3 : Real.exp (-h) * Real.exp h = 1 := by rw [← Real.exp_add]; simp
      linarith only [h2, h3]
    nlinarith only [h1, heh, Real.exp_one_lt_d9, hh.le]
  have heh0 : 0 ≤ Real.exp h - 1 := by linarith only [Real.add_one_le_exp h, hh.le]
  have hwBh : w * (B * Real.exp h) ≤ Real.exp 2 * c := by
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he2]
    calc w * (B * Real.exp h) = (w * B) * Real.exp h := by ring
      _ ≤ (Real.exp 1 * c) * Real.exp 1 := mul_le_mul hwB heh (Real.exp_pos h).le (by positivity)
      _ = Real.exp 1 * Real.exp 1 * c := by ring
  have hdev : (4 * C * ε + h ^ 2) ^ 2 ≤ 4 * h ^ 2 * h ^ 2 := by
    have := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * C * ε + h ^ 2)
      (show 4 * C * ε + h ^ 2 ≤ 2 * h ^ 2 by linarith only [hε]) 2
    nlinarith only [this]
  have hK1 : 0 ≤ 1 + Real.log (2 * K') := by
    rcases Nat.eq_zero_or_pos K' with h0 | h0
    · rw [h0]; simp
    · have h1 : (1 : ℝ) ≤ K' := by exact_mod_cast h0
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 * K' by linarith)]
  have t1 : (w / h ^ 2) * (8 * (h ^ 2 * (P * (1 + Real.log (2 * K'))) +
      (4 * C * ε + h ^ 2) ^ 2 * (P * H)) * (B * Real.exp h)) ≤
      8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P := by
    have hin : h ^ 2 * (P * (1 + Real.log (2 * K'))) + (4 * C * ε + h ^ 2) ^ 2 * (P * H) ≤
        h ^ 2 * ((1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P) := by
      have := mul_le_mul_of_nonneg_right hdev (mul_nonneg hP hH)
      nlinarith only [this]
    calc (w / h ^ 2) * (8 * (h ^ 2 * (P * (1 + Real.log (2 * K'))) +
            (4 * C * ε + h ^ 2) ^ 2 * (P * H)) * (B * Real.exp h))
        ≤ (w / h ^ 2) * (8 * (h ^ 2 * ((1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P)) *
            (B * Real.exp h)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hin (by norm_num)) (by positivity)) (by positivity)
      _ = 8 * (w * (B * Real.exp h)) * ((1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P) := by
          field_simp [hh.ne']
      _ ≤ 8 * (Real.exp 2 * c) * ((1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwBh (by norm_num)) (by positivity)
      _ = _ := by ring
  have t2 : (w / h ^ 2) * (8 * (h ^ 2 * (P * H)) * ((A * Real.exp h - A) + (B * Real.exp h - B))) ≤
      48 * Real.exp 1 * c * h * H * P := by
    have hAB2 : (A * Real.exp h - A) + (B * Real.exp h - B) ≤ 2 * B * (3 * h) := by
      calc (A * Real.exp h - A) + (B * Real.exp h - B) = (A + B) * (Real.exp h - 1) := by ring
        _ ≤ (2 * B) * (3 * h) := mul_le_mul (by linarith only [hAB]) heh1 heh0 (by positivity)
        _ = 2 * B * (3 * h) := by ring
    calc (w / h ^ 2) * (8 * (h ^ 2 * (P * H)) * ((A * Real.exp h - A) + (B * Real.exp h - B)))
        ≤ (w / h ^ 2) * (8 * (h ^ 2 * (P * H)) * (2 * B * (3 * h))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hAB2 (by positivity)) (by positivity)
      _ = 48 * (w * B) * h * H * P := by field_simp [hh.ne']; ring
      _ ≤ 48 * (Real.exp 1 * c) * h * H * P := by
          have := mul_le_mul_of_nonneg_right hwB (by positivity : 0 ≤ 48 * h * H * P)
          linarith only [this]
      _ = _ := by ring
  have t3 : (w / h ^ 2) * (2 * shortOrderWeight K' *
      ∑ k ∈ range K', (Λ k : ℝ) * (h * (B * Real.exp h) / k + 1) * (h * P)) ≤
      2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK) * P := by
    have hsum_eq : ∑ k ∈ range K', (Λ k : ℝ) * (h * (B * Real.exp h) / k + 1) * (h * P) =
        h * P * (h * (B * Real.exp h) * shortOrderWeight K' + ∑ k ∈ range K', (Λ k : ℝ)) := by
      unfold shortOrderWeight
      rw [mul_add, ← mul_assoc (h * P), mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [hsum_eq]
    have hΛ0 : 0 ≤ ΛK := hLK0.trans hLK
    have hΨ0 : 0 ≤ ∑ k ∈ range K', (Λ k : ℝ) := sum_nonneg fun _ _ => vonMangoldt_nonneg
    calc (w / h ^ 2) * (2 * shortOrderWeight K' *
            (h * P * (h * (B * Real.exp h) * shortOrderWeight K' + ∑ k ∈ range K', (Λ k : ℝ))))
        = 2 * shortOrderWeight K' *
            ((w * (B * Real.exp h)) * shortOrderWeight K' + (w / h) * ∑ k ∈ range K', (Λ k : ℝ)) *
            P := by field_simp [hh.ne']
      _ ≤ 2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK) * P := by
          refine mul_le_mul_of_nonneg_right ?_ hP
          refine mul_le_mul (mul_le_mul_of_nonneg_left hLK zero_le_two) ?_
            (by positivity) (by positivity)
          exact add_le_add (mul_le_mul hwBh hLK hLK0 (by positivity))
            (mul_le_mul_of_nonneg_left hΨK (by positivity))
  unfold offPoleWindowSumBound
  dsimp only [P, H, ε] at t1 t2 t3 ⊢
  linarith [t1, t2, t3]

private lemma two_mul_abs_integral_mul_le_of_integrable_sq {f k : ℝ → ℝ}
    (hf2 : Integrable fun u => f u ^ 2) (hk2 : Integrable fun u => k u ^ 2)
    (hfk : Integrable fun u => f u * k u) {η : ℝ} (hη : 0 < η) :
    2 * |∫ u, f u * k u| ≤ η * (∫ u, f u ^ 2) + η⁻¹ * ∫ u, k u ^ 2 := by
  set s := Real.sqrt η
  have hs : 0 < s := Real.sqrt_pos.mpr hη
  have hs2 : s ^ 2 = η := Real.sq_sqrt hη.le
  have hsc : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have irhs : Integrable fun u => η * f u ^ 2 + η⁻¹ * k u ^ 2 :=
    (hf2.const_mul η).add (hk2.const_mul η⁻¹)
  have hpt1 : ∀ u, 2 * (f u * k u) ≤ η * f u ^ 2 + η⁻¹ * k u ^ 2 := fun u => by
    have hsq := sq_nonneg (s * f u - s⁻¹ * k u)
    rw [sub_sq, mul_pow, mul_pow, hs2, inv_pow, hs2] at hsq
    have hc : 2 * (s * f u) * (s⁻¹ * k u) = 2 * (f u * k u) := by
      linear_combination (2 * f u * k u) * hsc
    linarith only [hsq, hc]
  have hpt2 : ∀ u, -(2 * (f u * k u)) ≤ η * f u ^ 2 + η⁻¹ * k u ^ 2 := fun u => by
    have hsq := sq_nonneg (s * f u + s⁻¹ * k u)
    rw [add_sq, mul_pow, mul_pow, hs2, inv_pow, hs2] at hsq
    have hc : 2 * (s * f u) * (s⁻¹ * k u) = 2 * (f u * k u) := by
      linear_combination (2 * f u * k u) * hsc
    linarith only [hsq, hc]
  have i1 := integral_mono (hfk.const_mul 2) irhs hpt1
  have i2 : (∫ u, -(2 * (f u * k u))) ≤ ∫ u, (η * f u ^ 2 + η⁻¹ * k u ^ 2) :=
    integral_mono (hfk.const_mul 2).neg irhs hpt2
  rw [integral_const_mul, integral_add (hf2.const_mul η) (hk2.const_mul η⁻¹),
    integral_const_mul, integral_const_mul] at i1
  rw [integral_neg, integral_const_mul, integral_add (hf2.const_mul η) (hk2.const_mul η⁻¹),
    integral_const_mul, integral_const_mul] at i2
  rcases le_or_gt 0 (∫ u, f u * k u) with h0 | h0
  · rw [abs_of_nonneg h0]; exact i1
  · rw [abs_of_neg h0]; linarith only [i2]

private lemma integral_sq_smoothedBump_sub_smoothedCoherent_le {g : ℝ → ℝ} {w h : ℝ}
    (hg : ContDiff ℝ 2 g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hg0 : ∀ u, 0 ≤ g u) (hh : 0 < h) (B : ℕ) (V : ℕ → ℝ) (a b σ : ℝ) :
    Integrable (fun u =>
        (atomicTest B V (smoothedBump g h) u - smoothedCoherent g a b h σ u) ^ 2) ∧
      (∫ u, (atomicTest B V (smoothedBump g h) u - smoothedCoherent g a b h σ u) ^ 2) ≤
        ((∫ t, g t) ^ 2 / h ^ 2) *
          ∫ s, (windowSum B V h s - coherentWindow a b h σ s) ^ 2 := by
  have hgc := hasCompactSupport_of_support_Icc hgsupp
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  set W := windowSum B V h
  set Wc := coherentWindow a b h σ
  set RW : ℝ → ℝ := fun s => W s - Wc s
  have hWc_int : Integrable Wc :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((by fun_prop : Continuous fun s =>
        Real.sqrt (Real.exp s) * (1 - Real.exp (-h)) * σ).integrableOn_Icc)
  have hWc2_int : Integrable fun s => Wc s ^ 2 := by
    have heq : (fun s => Wc s ^ 2) = (Set.Icc a b).indicator
        (fun s => (Real.sqrt (Real.exp s) * (1 - Real.exp (-h)) * σ) ^ 2) := by
      funext s; dsimp only [Wc, coherentWindow]
      by_cases hs : s ∈ Set.Icc a b
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, sq, zero_mul]
    rw [heq]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      ((Continuous.pow (by fun_prop) 2).integrableOn_Icc)
  have hWc_meas : Measurable Wc :=
    ((by fun_prop : Continuous fun s =>
      Real.sqrt (Real.exp s) * (1 - Real.exp (-h)) * σ).measurable).indicator measurableSet_Icc
  have hWc_bd : ∀ s, |Wc s| ≤ Real.sqrt (Real.exp (max a b)) * |1 - Real.exp (-h)| * |σ| := by
    intro s; dsimp only [Wc, coherentWindow]
    by_cases hs : s ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hs, abs_mul, abs_mul,
        abs_of_pos (Real.sqrt_pos.mpr (Real.exp_pos s))]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (Real.exp_le_exp.mpr (hs.2.trans (le_max_right a b))))
        (abs_nonneg _)) (abs_nonneg _)
    · rw [Set.indicator_of_notMem hs, abs_zero]; positivity
  have hRW_meas : Measurable RW := (measurable_windowSum B V h).sub hWc_meas
  set C_RW := (∑ n ∈ Icc 1 B, |V n|) +
    Real.sqrt (Real.exp (max a b)) * |1 - Real.exp (-h)| * |σ|
  have hRW_bd : ∀ s, |RW s| ≤ C_RW := fun s =>
    (abs_sub _ _).trans (add_le_add (abs_windowSum_le B V h s) (hWc_bd s))
  have hRW2_int : Integrable fun s => RW s ^ 2 := by
    refine (((integrable_windowSum_sq B V h).const_mul 2).add (hWc2_int.const_mul 2)).mono'
      (hRW_meas.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    dsimp only [RW, W]
    nlinarith only [sq_nonneg (windowSum B V h s + Wc s)]
  have hFcoh_eq : smoothedCoherent g a b h σ =
      fun u => h⁻¹ * convolution g Wc (ContinuousLinearMap.mul ℝ ℝ) volume u :=
    funext fun u => by rw [smoothedCoherent, convolution_def]; rfl
  have hFcoh_int : Integrable (smoothedCoherent g a b h σ) := by
    rw [hFcoh_eq]
    exact (hgi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hWc_int).const_mul h⁻¹
  have hFh : ContDiff ℝ 2 (atomicTest B V (smoothedBump g h)) :=
    contDiff_atomicTest (contDiff_smoothedBump hg hgc h) B V
  set RF : ℝ → ℝ := fun u => atomicTest B V (smoothedBump g h) u - smoothedCoherent g a b h σ u
  have hRF_aesm : AEStronglyMeasurable RF volume :=
    hFh.continuous.aestronglyMeasurable.sub hFcoh_int.aestronglyMeasurable
  have hRF_eq : ∀ u, RF u = h⁻¹ * ∫ t, g t * RW (u - t) := by
    intro u; dsimp only [RF]
    rw [atomicTest_smoothedBump_eq hg.continuous hgc, smoothedCoherent, ← mul_sub]
    congr 1
    have iW := integrable_mul_comp_sub hgi (measurable_windowSum B V h) (abs_windowSum_le B V h) u
    have iWc := integrable_mul_comp_sub hgi hWc_meas hWc_bd u
    rw [← integral_sub iW iWc]
    exact integral_congr_ae (Eventually.of_forall fun t => by dsimp only [RW]; ring)
  set I := ∫ t, g t
  have hcs : ∀ u, (∫ t, g t * RW (u - t)) ^ 2 ≤ I * ∫ t, g t * RW (u - t) ^ 2 := fun u =>
    sq_integral_mul_le_weighted hg0 hgi (hRW_meas.comp (measurable_const.sub measurable_id))
      (fun t => hRW_bd (u - t))
  have hci : Integrable (convolution g (fun s => RW s ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hgi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hRW2_int
  have hpt : ∀ u, RF u ^ 2 ≤
      h⁻¹ ^ 2 * I * convolution g (fun s => RW s ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume u := by
    intro u
    rw [hRF_eq u, mul_pow, convolution_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcs u) (sq_nonneg _)
  have hRF2_int : Integrable fun u => RF u ^ 2 :=
    (hci.const_mul (h⁻¹ ^ 2 * I)).mono' (hRF_aesm.pow 2)
      (Eventually.of_forall fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt u)
  refine ⟨hRF2_int, ?_⟩
  calc ∫ u, RF u ^ 2
      ≤ ∫ u, h⁻¹ ^ 2 * I *
          convolution g (fun s => RW s ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume u :=
        integral_mono hRF2_int (hci.const_mul _) hpt
    _ = h⁻¹ ^ 2 * I * (I * ∫ s, RW s ^ 2) := by
        rw [integral_const_mul, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hgi hRW2_int]
        rfl
    _ = I ^ 2 / h ^ 2 * ∫ s, RW s ^ 2 := by field_simp

private lemma collar_bridge_translate_factor_le {N : ℕ} {c K_c δ T h : ℝ}
    (hc1 : 1 ≤ c) (h2LN : 2 * linearDefectCutoff c ≤ N) (hN1 : 1 ≤ N)
    (hM1 : 1 ≤ N / linearDefectCutoff c) (hMN : N / linearDefectCutoff c ≤ N)
    (hKc0 : 0 < K_c) (hδ : 0 < δ)
    (hL1 : 1 ≤ Real.log (N : ℝ)) (hc_up : c ≤ K_c * Real.log (N : ℝ) ^ (1 / 8 : ℝ))
    (hcL : c ≤ Real.log (N : ℝ)) (hTh : T * h = 1 / Real.log (N : ℝ))
    (hP_tr :
      (1280 * explicitConductorCutoffConstant *
        ((1 + 2 * Real.exp 2) *
          (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4))) *
        K_c / δ) *
        Real.log (N : ℝ) ^ (31 / 32 : ℝ) * (1 + Real.log (Real.log (N : ℝ))) ^ 6 ≤
        Real.log (N : ℝ)) :
    let L := Real.log (N : ℝ)
    let ℓ := 1 + Real.log L
    let k₁ := L / (2 * explicitConductorCutoffConstant * ℓ ^ 5)
    let w := c / (N : ℝ)
    let M := N / linearDefectCutoff c
    let Bn := ⌊(N : ℝ) * Real.exp w⌋₊
    let μ := L ^ (-1 / 32 : ℝ)
    let lam := L ^ (5 / 32 : ℝ)
    (μ⁻¹ * (T * h) ^ 2 + lam⁻¹ * 4) *
      ((1 + 2 * Real.exp 1 * (w * Bn)) *
        (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) ≤
      (δ / 4) * (k₁ / 16) := by
  intro L ℓ k₁ w M Bn μ lam
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hℓ0 : 0 < ℓ := by dsimp only [ℓ]; linarith [Real.log_nonneg hL1]
  have hℓ5_pos : 0 < ℓ ^ 5 := pow_pos hℓ0 5
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < w := div_pos hc0 hN0
  set C_tr : ℝ := (1 + 2 * Real.exp 2) *
    (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4))
  have hC_tr0 : 0 ≤ C_tr := by
    have : (1 : ℝ) ≤ 8 * Real.exp 1 * (256 * Real.exp 2 + 4) := by
      nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1),
        Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)]
    have hl1 := Real.log_nonneg this
    have hl4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [C_tr]; positivity
  have hΦ := translate_factor_le hc1 h2LN
  have h1L : 1 + L ≤ 2 * L := by linarith only [hL1]
  have h1c : 1 + Real.log c ≤ ℓ := by dsimp only [ℓ]; linarith [Real.log_le_log hc0 hcL]
  have hΦ_ub : (1 + 2 * Real.exp 1 * (w * Bn)) *
      (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4))) ≤
      2 * C_tr * K_c * L ^ (9 / 8 : ℝ) * ℓ := by
    have h1 : C_tr * c * (1 + L) * (1 + Real.log c) ≤
        C_tr * (K_c * L ^ (1 / 8 : ℝ)) * (2 * L) * ℓ := by
      have hm1 := mul_le_mul hc_up h1L (by positivity) (by positivity)
      have hm2 := mul_le_mul hm1 h1c (by linarith [Real.log_nonneg hc1]) (by positivity)
      calc C_tr * c * (1 + L) * (1 + Real.log c)
          = C_tr * (c * (1 + L) * (1 + Real.log c)) := by ring
        _ ≤ C_tr * (K_c * L ^ (1 / 8 : ℝ) * (2 * L) * ℓ) := mul_le_mul_of_nonneg_left hm2 hC_tr0
        _ = C_tr * (K_c * L ^ (1 / 8 : ℝ)) * (2 * L) * ℓ := by ring
    have hL98 : L ^ (1 / 8 : ℝ) * L = L ^ (9 / 8 : ℝ) := by
      calc L ^ (1 / 8 : ℝ) * L = L ^ (1 / 8 : ℝ) * L ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = L ^ (9 / 8 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
    exact hΦ.trans (h1.trans_eq (by rw [← hL98]; ring))
  have hμ_inv : μ⁻¹ = L ^ (1 / 32 : ℝ) := by
    dsimp only [μ]
    rw [show (-1 / 32 : ℝ) = -(1 / 32 : ℝ) by norm_num, Real.rpow_neg hL0.le, inv_inv]
  have hlam_inv : lam⁻¹ = L ^ (-5 / 32 : ℝ) := by
    dsimp only [lam]
    rw [show (-5 / 32 : ℝ) = -(5 / 32 : ℝ) by norm_num, Real.rpow_neg hL0.le]
  have hcoef_ub : μ⁻¹ * (T * h) ^ 2 + lam⁻¹ * 4 ≤ 5 * L ^ (-5 / 32 : ℝ) := by
    rw [hμ_inv, hlam_inv, hTh]
    have h1 : L ^ (1 / 32 : ℝ) * (1 / L) ^ 2 ≤ L ^ (-5 / 32 : ℝ) := by
      have hprod : L ^ (1 / 32 : ℝ) ≤ L ^ (-5 / 32 : ℝ) * L ^ 2 := by
        calc L ^ (1 / 32 : ℝ) ≤ L ^ (59 / 32 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
          _ = L ^ (-5 / 32 : ℝ) * L ^ (2 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
          _ = L ^ (-5 / 32 : ℝ) * L ^ 2 := by rw [Real.rpow_two]
      rw [one_div_pow, mul_one_div, div_le_iff₀ (sq_pos_of_pos hL0)]
      exact hprod
    linarith only [h1]
  have hΦ0 : 0 ≤ (1 + 2 * Real.exp 1 * (w * Bn)) *
      (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4))) := by
    have hBn1 : (1 : ℝ) ≤ Bn := by
      have h1 : ((1 : ℕ) : ℝ) ≤ N * Real.exp w := by
        push_cast
        exact (by exact_mod_cast hN1 : (1 : ℝ) ≤ N).trans
          (le_mul_of_one_le_right hN0.le (Real.one_le_exp hw0.le))
      exact_mod_cast Nat.le_floor h1
    have hrat : 1 ≤ 2 * (Bn : ℝ) / ((M : ℝ) / 2) := by
      have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
      rw [le_div_iff₀ (by linarith)]
      have hMN_R : (M : ℝ) ≤ N := by exact_mod_cast hMN
      have hNBn : (N : ℝ) ≤ Bn := by
        exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hN0.le (Real.one_le_exp hw0.le))
      linarith
    have hl1 := Real.log_nonneg hBn1
    have hl2 := Real.log_nonneg hrat
    have hl4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    positivity
  have hm := mul_le_mul hcoef_ub hΦ_ub hΦ0 (by positivity)
  have hsplit : L ^ (-5 / 32 : ℝ) * L ^ (9 / 8 : ℝ) = L ^ (31 / 32 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have h10 : (5 * L ^ (-5 / 32 : ℝ)) * (2 * C_tr * K_c * L ^ (9 / 8 : ℝ) * ℓ) =
      10 * C_tr * K_c * L ^ (31 / 32 : ℝ) * ℓ := by
    calc (5 * L ^ (-5 / 32 : ℝ)) * (2 * C_tr * K_c * L ^ (9 / 8 : ℝ) * ℓ)
        = 10 * C_tr * K_c * (L ^ (-5 / 32 : ℝ) * L ^ (9 / 8 : ℝ)) * ℓ := by ring
      _ = 10 * C_tr * K_c * L ^ (31 / 32 : ℝ) * ℓ := by rw [hsplit]
  have hpb : 10 * C_tr * K_c * L ^ (31 / 32 : ℝ) * ℓ ≤ (δ / 4) * (k₁ / 16) := by
    dsimp only [k₁]
    have hden : 0 < 2 * explicitConductorCutoffConstant * ℓ ^ 5 := by positivity
    have h1 : (δ / 4) * (L / (2 * explicitConductorCutoffConstant * ℓ ^ 5) / 16) =
        (δ * L) / (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by ring
    rw [h1, le_div_iff₀ (by positivity)]
    have hm_tr : (1280 * explicitConductorCutoffConstant * C_tr * K_c / δ) *
        L ^ (31 / 32 : ℝ) * ℓ ^ 6 ≤ L := by
      dsimp only [L, ℓ, C_tr]; exact hP_tr
    have hm' := mul_le_mul_of_nonneg_left hm_tr hδ.le
    have hid : δ * ((1280 * explicitConductorCutoffConstant * C_tr * K_c / δ) *
        L ^ (31 / 32 : ℝ) * ℓ ^ 6) =
        10 * C_tr * K_c * L ^ (31 / 32 : ℝ) * ℓ *
          (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by
      calc δ * ((1280 * explicitConductorCutoffConstant * C_tr * K_c / δ) *
            L ^ (31 / 32 : ℝ) * ℓ ^ 6)
          = (δ * (1280 * explicitConductorCutoffConstant * C_tr * K_c / δ)) *
              L ^ (31 / 32 : ℝ) * ℓ ^ 6 := by ring
        _ = (1280 * explicitConductorCutoffConstant * C_tr * K_c) *
              L ^ (31 / 32 : ℝ) * ℓ ^ 6 := by rw [mul_div_cancel₀ _ hδ.ne']
        _ = 10 * C_tr * K_c * L ^ (31 / 32 : ℝ) * ℓ *
              (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by ring
    linarith only [hm', hid]
  exact hm.trans (h10.trans_le hpb)

private lemma collar_bridge_offPole_prefix_scalar
    {K' : ℕ} {c K_c δ L ℓ k₁ h T H_M β ΛK w_Ψ C_β P : ℝ}
    (hK'1 : 1 ≤ K') (hδ : 0 < δ) (hc1 : 1 ≤ c) (hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ))
    (hL1 : 1 ≤ L) (hℓ0 : 0 < ℓ) (hh0 : 0 < h) (hh1 : h ≤ 1) (hT0 : 0 < T) (hT1 : 1 ≤ T)
    (hHM0 : 0 ≤ H_M) (hHM : H_M ≤ 1 + L) (hP0 : 0 ≤ P) (hβ0 : 0 ≤ β) (hwhΨ : w_Ψ ≤ 1)
    (hh_def : h = 1 / (T * L))
    (hk₁_def : k₁ = L / (2 * explicitConductorCutoffConstant * ℓ ^ 5))
    (hΛK_def : ΛK = β + 1 + (Real.log 4 + 4))
    (hlogK' : Real.log K' ≤ β + 1)
    (hβ_ub : β ≤ C_β * L ^ (3 / 8 : ℝ))
    (hP_off : (128 * explicitConductorCutoffConstant * splineWindowConstant *
      (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
      (C_β + 1 + (Real.log 4 + 4)) ^ 2 * K_c / δ) * L ^ (29 / 32 : ℝ) * ℓ ^ 5 ≤ L) :
    L ^ (1 / 32 : ℝ) * splineWindowConstant *
      ((8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * H_M) +
        48 * Real.exp 1 * c * h * H_M +
        2 * ΛK * (Real.exp 2 * c * ΛK + w_Ψ)) * P) ≤
      (δ / 4) * ((k₁ / 16) * P) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hκ0 : 0 ≤ splineWindowConstant := splineWindowConstant_nonneg
  have hC₄ : 1 ≤ Real.log 4 + 4 := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hhH : h * H_M ≤ 2 := by
    have hhL : h * (1 + L) ≤ 2 := by
      have h1 : 1 + L ≤ 2 * L := by linarith only [hL1]
      calc h * (1 + L) ≤ (1 / (T * L)) * (2 * L) := by
            rw [← hh_def]; exact mul_le_mul_of_nonneg_left h1 hh0.le
        _ = 2 / T := by field_simp [hT0.ne', hL0.ne']
        _ ≤ 2 := div_le_self zero_le_two hT1
    exact (mul_le_mul_of_nonneg_left hHM hh0.le).trans hhL
  have hh2H : h ^ 2 * H_M ≤ 2 := by
    calc h ^ 2 * H_M = h * (h * H_M) := by ring
      _ ≤ 1 * 2 := mul_le_mul hh1 hhH (mul_nonneg hh0.le hHM0) zero_le_one
      _ = 2 := one_mul 2
  have hΛK1 : 1 ≤ ΛK := by rw [hΛK_def]; linarith only [hβ0, hC₄]
  have hΛ2 : ΛK ≤ ΛK ^ 2 := le_self_pow₀ hΛK1 two_ne_zero
  have hΛ1 : 1 ≤ ΛK ^ 2 := one_le_pow₀ hΛK1
  have hL2K : Real.log (2 * K') ≤ ΛK + 1 := by
    have hK'R : (0 : ℝ) < K' := by exact_mod_cast hK'1
    rw [Real.log_mul zero_lt_two.ne' hK'R.ne', hΛK_def]
    linarith [hlogK', Real.log_two_lt_d9, hC₄]
  have hPc : 8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * H_M) +
      48 * Real.exp 1 * c * h * H_M +
      2 * ΛK * (Real.exp 2 * c * ΛK + w_Ψ) ≤
      c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2 := by
    have t1 : 1 + Real.log (2 * K') + 4 * h ^ 2 * H_M ≤ 11 * ΛK ^ 2 := by
      linarith only [hL2K, hh2H, hΛ2, hΛ1, hΛK1]
    have t1' := mul_le_mul_of_nonneg_left t1 (by positivity : 0 ≤ 8 * Real.exp 2 * c)
    have t2 : 48 * Real.exp 1 * c * h * H_M ≤ 96 * Real.exp 1 * c * ΛK ^ 2 := by
      have a1 := mul_le_mul_of_nonneg_left hhH (by positivity : 0 ≤ 48 * Real.exp 1 * c)
      have a2 := mul_le_mul_of_nonneg_left hΛ1 (by positivity : 0 ≤ 96 * Real.exp 1 * c)
      linarith only [a1, a2]
    have t3 : 2 * ΛK * (Real.exp 2 * c * ΛK + w_Ψ) ≤
        (2 * Real.exp 2 + 2) * c * ΛK ^ 2 := by
      have a1 := mul_le_mul_of_nonneg_left hwhΨ (by positivity : 0 ≤ 2 * ΛK)
      have a2 : ΛK ^ 2 ≤ c * ΛK ^ 2 := le_mul_of_one_le_left (by positivity) hc1
      linarith only [a1, a2, hΛ2]
    have hcΛ : 0 ≤ (10 * Real.exp 2 + 4 * Real.exp 1 + 8) * (c * ΛK ^ 2) := by positivity
    linarith only [t1', t2, t3, hcΛ]
  have hΛK_ub : ΛK ≤ (C_β + 1 + (Real.log 4 + 4)) * L ^ (3 / 8 : ℝ) := by
    have hL38_1 : 1 ≤ L ^ (3 / 8 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    rw [hΛK_def]; nlinarith only [hβ_ub, hL38_1, hC₄]
  have hcΛ2_ub : L ^ (1 / 32 : ℝ) * splineWindowConstant *
      (c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2) ≤ (δ / 4) * (k₁ / 16) := by
    have hΛK2_ub : ΛK ^ 2 ≤ (C_β + 1 + (Real.log 4 + 4)) ^ 2 * L ^ (3 / 4 : ℝ) := by
      have hp := pow_le_pow_left₀ (by positivity) hΛK_ub 2
      rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le] at hp
      exact hp.trans_eq (by norm_num)
    have hc_mul : L ^ (1 / 32 : ℝ) * (c * ΛK ^ 2) ≤
        K_c * (C_β + 1 + (Real.log 4 + 4)) ^ 2 * L ^ (29 / 32 : ℝ) := by
      have hm := mul_le_mul hc_up hΛK2_ub (sq_nonneg _) (hc0.le.trans hc_up)
      have hm2 := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hL0.le (1 / 32))
      have hadd : L ^ (1 / 32 : ℝ) * (L ^ (1 / 8 : ℝ) * L ^ (3 / 4 : ℝ)) =
          L ^ (29 / 32 : ℝ) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
      exact hm2.trans_eq (by
        calc L ^ (1 / 32 : ℝ) *
              (K_c * L ^ (1 / 8 : ℝ) * ((C_β + 1 + (Real.log 4 + 4)) ^ 2 * L ^ (3 / 4 : ℝ)))
            = K_c * (C_β + 1 + (Real.log 4 + 4)) ^ 2 *
                (L ^ (1 / 32 : ℝ) * (L ^ (1 / 8 : ℝ) * L ^ (3 / 4 : ℝ))) := by ring
          _ = K_c * (C_β + 1 + (Real.log 4 + 4)) ^ 2 * L ^ (29 / 32 : ℝ) := by rw [hadd])
    have hm1 := mul_le_mul_of_nonneg_left hc_mul
      (by positivity : 0 ≤ splineWindowConstant * (100 * Real.exp 2 + 100 * Real.exp 1 + 10))
    have h1 : (δ / 4) * (k₁ / 16) =
        (δ * L) / (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by
      rw [hk₁_def]; ring
    rw [h1, le_div_iff₀ (mul_pos (mul_pos (by norm_num) hD) (pow_pos hℓ0 5))]
    have hm1' := mul_le_mul_of_nonneg_right hm1
      (by positivity : 0 ≤ 128 * explicitConductorCutoffConstant * ℓ ^ 5)
    have hm_off := mul_le_mul_of_nonneg_left hP_off hδ.le
    have hid : δ * ((128 * explicitConductorCutoffConstant * splineWindowConstant *
        (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
        (C_β + 1 + (Real.log 4 + 4)) ^ 2 * K_c / δ) * L ^ (29 / 32 : ℝ) * ℓ ^ 5) =
        (splineWindowConstant * (100 * Real.exp 2 + 100 * Real.exp 1 + 10)) *
          (K_c * (C_β + 1 + (Real.log 4 + 4)) ^ 2 * L ^ (29 / 32 : ℝ)) *
          (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by
      calc δ * ((128 * explicitConductorCutoffConstant * splineWindowConstant *
            (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
            (C_β + 1 + (Real.log 4 + 4)) ^ 2 * K_c / δ) * L ^ (29 / 32 : ℝ) * ℓ ^ 5)
          = (δ * (128 * explicitConductorCutoffConstant * splineWindowConstant *
              (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
              (C_β + 1 + (Real.log 4 + 4)) ^ 2 * K_c / δ)) *
              L ^ (29 / 32 : ℝ) * ℓ ^ 5 := by ring
        _ = (128 * explicitConductorCutoffConstant * splineWindowConstant *
              (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
              (C_β + 1 + (Real.log 4 + 4)) ^ 2 * K_c) *
              L ^ (29 / 32 : ℝ) * ℓ ^ 5 := by rw [mul_div_cancel₀ _ hδ.ne']
        _ = (splineWindowConstant * (100 * Real.exp 2 + 100 * Real.exp 1 + 10)) *
              (K_c * (C_β + 1 + (Real.log 4 + 4)) ^ 2 * L ^ (29 / 32 : ℝ)) *
              (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by ring
    have lhs_id : L ^ (1 / 32 : ℝ) * splineWindowConstant *
        (c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2) *
        (128 * explicitConductorCutoffConstant * ℓ ^ 5) =
        (splineWindowConstant * (100 * Real.exp 2 + 100 * Real.exp 1 + 10)) *
          (L ^ (1 / 32 : ℝ) * (c * ΛK ^ 2)) *
          (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by ring
    linarith only [hm1', hm_off, hid, lhs_id]
  calc L ^ (1 / 32 : ℝ) * splineWindowConstant *
        ((8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * H_M) +
          48 * Real.exp 1 * c * h * H_M +
          2 * ΛK * (Real.exp 2 * c * ΛK + w_Ψ)) * P)
      ≤ L ^ (1 / 32 : ℝ) * splineWindowConstant *
          ((c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2) * P) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPc hP0) (by positivity)
    _ = (L ^ (1 / 32 : ℝ) * splineWindowConstant *
          (c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2)) * P := by ring
    _ ≤ ((δ / 4) * (k₁ / 16)) * P := mul_le_mul_of_nonneg_right hcΛ2_ub hP0
    _ = (δ / 4) * ((k₁ / 16) * P) := by ring

private lemma collar_bridge_offPole_window_le {N K' : ℕ} {c K_c δ C_ψ c₀ t₀ h : ℝ}
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hCψ : 0 ≤ C_ψ) (hc₀ : 0 < c₀) (hδ : 0 < δ) (_hKc0 : 0 < K_c)
    (hpnt : ∀ ⦃h X Y : ℝ⦄, 0 < h → h ≤ 1 → Y = X * Real.exp (-h) → t₀ ≤ Y →
      |∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k - Real.sqrt X * (1 - Real.exp (-h))| ≤
        Real.sqrt X * (4 * C_ψ * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2))
    (hN2 : 2 ≤ N) (hc1 : 1 ≤ c) (hcN : c ≤ N) (hL1 : 1 ≤ Real.log (N : ℝ))
    (hc_up : c ≤ K_c * Real.log (N : ℝ) ^ (1 / 8 : ℝ)) (hcL : c ≤ Real.log (N : ℝ))
    (h2LN : 2 * linearDefectCutoff c ≤ N)
    (hz : z ∈ (conductorSubspace 1 N)ᗮ)
    (hh_def : h = 1 / (Real.exp (factorialSpanGammaOffset + Real.log (N : ℝ) ^ (3 / 16 : ℝ)) *
      Real.log (N : ℝ)))
    (hK'1 : 1 ≤ K') (ht₀K' : t₀ ≤ K' * Real.exp (-1))
    (hpntK' : 4 * C_ψ * pntRate c₀ K' ≤ h ^ 2)
    (hlogK' : Real.log K' ≤ (1 + ((2 * Real.log (1 / h) + Real.log (4 * C_ψ + 1)) / c₀) ^ 2 +
      |Real.log t₀|) + 1)
    (hK'le : (K' : ℝ) ≤ 2 * Real.exp (1 +
      ((2 * Real.log (1 / h) + Real.log (4 * C_ψ + 1)) / c₀) ^ 2 + |Real.log t₀|))
    (hL316_C : factorialSpanGammaOffset + Real.log (4 * C_ψ + 1) + 4 ≤
      Real.log (N : ℝ) ^ (3 / 16 : ℝ))
    (hlogL_ub : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) ^ (3 / 16 : ℝ))
    (hexp_b : (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset +
      (1 + 36 / c₀ ^ 2 + |Real.log t₀|)) * Real.log (N : ℝ) ^ (3 / 8 : ℝ) ≤ Real.log (N : ℝ))
    (hedg_b : 48 * Real.exp 1 * (Real.log (N : ℝ) / N) ≤ δ / 8)
    (hP_off : (128 * explicitConductorCutoffConstant * splineWindowConstant *
      (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
      (1 + 36 / c₀ ^ 2 + |Real.log t₀| + 1 + (Real.log 4 + 4)) ^ 2 * K_c / δ) *
      Real.log (N : ℝ) ^ (29 / 32 : ℝ) * (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤
      Real.log (N : ℝ)) :
    let L := Real.log (N : ℝ)
    let ℓ := 1 + Real.log L
    let k₁ := L / (2 * explicitConductorCutoffConstant * ℓ ^ 5)
    let I₂ := ∫ u, tiltedUnitSpline u ^ 2
    let w := c / (N : ℝ)
    let x := primeHorizonExtension z
    let M := N / linearDefectCutoff c
    let y := atomicTailCoefficients M x
    let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
    let Bn := ⌊(N : ℝ) * Real.exp w⌋₊
    let V : ℕ → ℝ := fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv (primeOrderCutoff N w) M x n
    L ^ (1 / 32 : ℝ) * splineWindowConstant * ((w / h ^ 2) *
        ∫ s, (windowSum Bn V h s -
          coherentWindow (Real.log ((M : ℝ) / 2) + h) (Real.log (N : ℝ) + w) h
            (prefixPoleMoment M x) s) ^ 2) ≤
      (δ / 4) * ((c / I₂) * ∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
        (δ / 8) * ((c / I₂) * ∫ u, U_y u ^ 2) +
        (δ / 4) * ((k₁ / 16) * ∑ n ∈ Icc 1 M, x n ^ 2) := by
  intro L ℓ k₁ I₂ w x M y U_y Bn V
  obtain ⟨hL3, -, -, -⟩ := linearDefectCutoff_bounds hc1
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hℓ0 : 0 < ℓ := by dsimp only [ℓ]; linarith [Real.log_nonneg hL1]
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  have hI₁ : 0 < ∫ u, tiltedUnitSpline u := integral_tiltedUnitSpline_pos
  have hκ0 : 0 ≤ splineWindowConstant := splineWindowConstant_nonneg
  have hw0 : 0 < w := div_pos hc0 hN0
  have hw1 : w ≤ 1 := (div_le_one hN0).mpr hcN
  have hM2 : 2 ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
  have hM1 : 1 ≤ M := by omega
  have hMN : M ≤ N := Nat.div_le_self _ _
  have hM2R : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hA1 : 1 ≤ (M : ℝ) / 2 := by linarith only [hM2R]
  have hMA : (M : ℝ) ≤ 2 * ((M : ℝ) / 2) := by linarith
  have hNBn : (N : ℝ) ≤ Bn := by
    exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hN0.le (Real.one_le_exp hw0.le))
  have hMNR : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hAB : (M : ℝ) / 2 ≤ Bn := by linarith only [hNBn, hMNR, hM2R]
  set G₀ := factorialSpanGammaOffset
  have hG₀ : 0 ≤ G₀ := factorialSpanGammaOffset_nonneg
  set T := Real.exp (G₀ + L ^ (3 / 16 : ℝ))
  have hT0 : 0 < T := Real.exp_pos _
  have hT1 : 1 ≤ T := Real.one_le_exp (add_nonneg hG₀ (Real.rpow_nonneg hL0.le _))
  have hh0 : 0 < h := by rw [hh_def]; exact div_pos zero_lt_one (mul_pos hT0 hL0)
  have hh1 : h ≤ 1 := by
    rw [hh_def]
    exact (div_le_one (mul_pos hT0 hL0)).mpr (one_le_mul_of_one_le_of_one_le hT1 hL1)
  have hNh : 1 ≤ (N : ℝ) * h := by
    rw [hh_def, mul_one_div, one_le_div (mul_pos hT0 hL0)]
    have hL38_1 : 1 ≤ L ^ (3 / 8 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hL316_38 : L ^ (3 / 16 : ℝ) ≤ L ^ (3 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hexp_le : G₀ + L ^ (3 / 16 : ℝ) + Real.log L ≤ L := by
      have hlogL_38 : Real.log L ≤ L ^ (3 / 8 : ℝ) := hlogL_ub.trans hL316_38
      have hsum_coeff : G₀ + L ^ (3 / 16 : ℝ) + Real.log L ≤
          (|Real.log (2 * (Real.log 4 + 4))| + 4 + G₀ +
            (1 + 36 / c₀ ^ 2 + |Real.log t₀|)) * L ^ (3 / 8 : ℝ) := by
        rw [add_mul, add_mul, add_mul]
        have h1 := le_mul_of_one_le_right hG₀ hL38_1
        have h2 : 0 ≤ |Real.log (2 * (Real.log 4 + 4))| * L ^ (3 / 8 : ℝ) := by positivity
        have h3 : 0 ≤ (1 + 36 / c₀ ^ 2 + |Real.log t₀|) * L ^ (3 / 8 : ℝ) := by positivity
        dsimp only [L, G₀] at h1 h2 h3 hL316_38 hlogL_38 hL38_1 ⊢
        linarith only [h1, h2, h3, hL316_38, hlogL_38, hL38_1]
      dsimp only [L, G₀] at hsum_coeff hexp_b ⊢
      exact hsum_coeff.trans hexp_b
    calc T * L = Real.exp (G₀ + L ^ (3 / 16 : ℝ)) * Real.exp (Real.log L) := by
            rw [Real.exp_log hL0]
      _ = Real.exp (G₀ + L ^ (3 / 16 : ℝ) + Real.log L) := (Real.exp_add _ _).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hexp_le
      _ = N := Real.exp_log hN0
  have hint_sq := integral_windowSum_sub_coherentWindow_sq_le hCψ hc₀ hpnt hh0 hh1 hw0.le
    hA1 hM1 hMA hN1 hAB hNh hK'1 ht₀K' x
  have hwB : w * Bn ≤ Real.exp 1 * c := by
    have hBn_le : (Bn : ℝ) ≤ N * Real.exp w := Nat.floor_le (by positivity)
    calc w * Bn ≤ w * (N * Real.exp w) := mul_le_mul_of_nonneg_left hBn_le hw0.le
      _ = c * Real.exp w := by dsimp only [w]; field_simp [hN0.ne']
      _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hc0.le
      _ = Real.exp 1 * c := mul_comm _ _
  set ν := (2 * Real.log (1 / h) + Real.log (4 * C_ψ + 1)) / c₀
  set β := 1 + ν ^ 2 + |Real.log t₀|
  set ΛK := β + 1 + (Real.log 4 + 4)
  have hLK : shortOrderWeight K' ≤ ΛK := by linarith [shortOrderWeight_le hK'1, hlogK']
  have hC₄ : 1 ≤ Real.log 4 + 4 := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  set ΨK := (Real.log 4 + 4) * (2 * Real.exp β)
  have hΨK : ∑ k ∈ range K', (Λ k : ℝ) ≤ ΨK :=
    (sum_vonMangoldt_range_le K').trans (mul_le_mul_of_nonneg_left hK'le (zero_le_one.trans hC₄))
  have hoff := offPoleWindowSumBound_div_le (M := M) x hh0 hh1 hCψ hpntK' hw0.le hc0.le hwB
    (by positivity) hAB hLK hΨK
  obtain ⟨hβ_ub, hwhΨ⟩ := far_garding_window_beta_psi_le hCψ hc₀ hN1 hL1 hcL hh_def
    hL316_C hlogL_ub hexp_b
  have hdiv_step : (w / h ^ 2) * ∫ s, (windowSum Bn V h s -
      coherentWindow (Real.log ((M : ℝ) / 2) + h) (Real.log (N : ℝ) + w) h
        (prefixPoleMoment M x) s) ^ 2 ≤
      8 * w * prefixPoleMoment M x ^ 2 +
        (8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
          48 * Real.exp 1 * c * h * prefixHarmonic M +
          2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK)) * prefixMass M x := by
    have hm := mul_le_mul_of_nonneg_left hint_sq (by positivity : 0 ≤ w / h ^ 2)
    have hid : (w / h ^ 2) * (8 * h ^ 2 * prefixPoleMoment M x ^ 2 +
        offPoleWindowSumBound C_ψ c₀ ((M : ℝ) / 2) Bn M K' x h) =
        8 * w * prefixPoleMoment M x ^ 2 +
          (w / h ^ 2) * offPoleWindowSumBound C_ψ c₀ ((M : ℝ) / 2) Bn M K' x h := by
      field_simp [hh0.ne']
    linarith only [hm, hid, hoff]
  have hpole_part :
      L ^ (1 / 32 : ℝ) * splineWindowConstant * (8 * w * prefixPoleMoment M x ^ 2) ≤
        (δ / 4) * ((c / I₂) * ∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
          (δ / 8) * ((c / I₂) * ∫ u, U_y u ^ 2) := by
    have hpole : prefixPoleMoment M x ^ 2 ≤
        Real.exp 1 / (∫ u, tiltedUnitSpline u) ^ 2 *
          (1 * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + (4 + 2 / (1 : ℝ)) * ∫ u, U_y u ^ 2) :=
      prefixPoleMoment_sq_le_exponential_mass hN2 hMN hc1 hcN one_pos hz
    have h6 : 1 * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + (4 + 2 / (1 : ℝ)) * (∫ u, U_y u ^ 2) =
        (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + 6 * ∫ u, U_y u ^ 2 := by ring
    rw [h6] at hpole
    have hid : L ^ (1 / 32 : ℝ) * splineWindowConstant *
        (8 * w * (Real.exp 1 / (∫ u, tiltedUnitSpline u) ^ 2 *
          ((∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + 6 * ∫ u, U_y u ^ 2))) =
        (8 * Real.exp 1 * (L ^ (1 / 32 : ℝ) / N)) * ((c / I₂) *
          ((∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + 6 * ∫ u, U_y u ^ 2)) := by
      dsimp only [splineWindowConstant, w, I₂]
      field_simp [hI₁.ne', hI₂.ne', hN0.ne']
    have hL32_L : L ^ (1 / 32 : ℝ) ≤ L :=
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 32 : ℝ) ≤ 1)).trans_eq
        (Real.rpow_one L)
    have hLN_le : 8 * Real.exp 1 * (L ^ (1 / 32 : ℝ) / N) ≤ 8 * Real.exp 1 * (L / N) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hL32_L hN0.le) (by positivity)
    have h8_le : 8 * Real.exp 1 * (L / N) ≤ δ / 4 := by
      have : 0 ≤ 8 * Real.exp 1 * (L / N) := by positivity
      linarith only [hedg_b, this, hδ]
    have h48_le : 6 * (8 * Real.exp 1 * (L ^ (1 / 32 : ℝ) / N)) ≤ δ / 8 := by
      linarith only [hLN_le, hedg_b]
    have hm1 := mul_le_mul_of_nonneg_left hpole
      (by positivity : 0 ≤ L ^ (1 / 32 : ℝ) * splineWindowConstant * (8 * w))
    rw [mul_assoc (L ^ (1 / 32 : ℝ) * splineWindowConstant) (8 * w),
      mul_assoc (L ^ (1 / 32 : ℝ) * splineWindowConstant) (8 * w), hid] at hm1
    have hW8_0 : 0 ≤ (c / I₂) * ∫ u, U_y u ^ 2 * Real.exp (-(8 * u)) :=
      mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
    have hU2_0 : 0 ≤ (c / I₂) * ∫ u, U_y u ^ 2 :=
      mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
    have hm_w8 := mul_le_mul_of_nonneg_right (hLN_le.trans h8_le) hW8_0
    have hm_u2 := mul_le_mul_of_nonneg_right h48_le hU2_0
    linarith only [hm1, hm_w8, hm_u2,
      (by ring : (8 * Real.exp 1 * (L ^ (1 / 32 : ℝ) / N)) *
          ((c / I₂) * ((∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + 6 * ∫ u, U_y u ^ 2)) =
        (8 * Real.exp 1 * (L ^ (1 / 32 : ℝ) / N)) *
          ((c / I₂) * ∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
          (6 * (8 * Real.exp 1 * (L ^ (1 / 32 : ℝ) / N))) * ((c / I₂) * ∫ u, U_y u ^ 2))]
  have hHM0 : 0 ≤ prefixHarmonic M := sum_nonneg fun m _ => by positivity
  have hHM : prefixHarmonic M ≤ 1 + L := by
    have h1 := RHTower.sum_Icc_one_div_le hM1
    have h2 : Real.log (M : ℝ) ≤ L :=
      Real.log_le_log (by exact_mod_cast hM1) (by exact_mod_cast hMN)
    unfold prefixHarmonic; linarith only [h1, h2]
  have hP0 : 0 ≤ prefixMass M x := sum_nonneg fun _ _ => sq_nonneg _
  have hβ0 : 0 ≤ β := by dsimp only [β]; positivity
  have hP_part :
      L ^ (1 / 32 : ℝ) * splineWindowConstant *
        ((8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
          48 * Real.exp 1 * c * h * prefixHarmonic M +
          2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK)) * prefixMass M x) ≤
        (δ / 4) * ((k₁ / 16) * ∑ n ∈ Icc 1 M, x n ^ 2) :=
    collar_bridge_offPole_prefix_scalar hK'1 hδ hc1 hc_up hL1 hℓ0 hh0 hh1 hT0 hT1
      hHM0 hHM hP0 hβ0 (by dsimp only [w, ΨK, β, ν]; exact hwhΨ) hh_def rfl rfl hlogK'
      (by dsimp only [β, ν, L]; exact hβ_ub) (by dsimp only [L, ℓ]; exact hP_off)
  have hmul := mul_le_mul_of_nonneg_left hdiv_step
    (by positivity : 0 ≤ L ^ (1 / 32 : ℝ) * splineWindowConstant)
  rw [mul_add] at hmul
  linarith only [hmul, hpole_part, hP_part]

private lemma collar_bridge_scalar_bounds
    {δ c K_c L ℓ k₁ α μ T h C_lev C_pre : ℝ}
    (hδ : 0 < δ) (hc1 : 1 ≤ c) (hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ))
    (hL0 : 0 < L) (hℓ0 : 0 < ℓ) (_hα0 : 0 < α) (hμ0 : 0 < μ) (hT0 : 0 < T) (hT1 : 1 ≤ T)
    (hD : 0 < explicitConductorCutoffConstant)
    (hC_lev_def : C_lev = 2 * |gammaHardyPhaseRate 0| + factorialSpanGammaOffset + Real.log 2 + 1)
    (hC_pre_def : C_pre = 1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost + (Real.log 4 + 4))
    (hk₁_def : k₁ = L / (2 * explicitConductorCutoffConstant * ℓ ^ 5))
    (hh_def : h = 1 / (T * L)) (hμ_inv : μ⁻¹ = α)
    (hL132_ge : (16 * Real.pi + 8 * C_lev + 8) / δ + 1 ≤ α)
    (hL_80δ : 80 / δ + 1 ≤ L)
    (hP_ord : (256 * Real.pi * explicitConductorCutoffConstant / δ) * α * ℓ ^ 5 ≤ L)
    (hP_pre : (128 * explicitConductorCutoffConstant * C_pre * K_c / δ) * L ^ (1 / 8 : ℝ) * ℓ ^ 5 ≤ L) :
    (16 * Real.pi + 8 * C_lev + 8) * μ ≤ δ ∧
      0 ≤ C_lev ∧
      μ ≤ δ ∧
      80 * h ≤ δ ∧
      2 * Real.pi * α ≤ (δ / 4) * (k₁ / 16) ∧
      c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost + (Real.log 4 + 4) ≤
        (δ / 4) * (k₁ / 16) := by
  have hμ_small : (16 * Real.pi + 8 * C_lev + 8) * μ ≤ δ := by
    have h1 : (16 * Real.pi + 8 * C_lev + 8) / δ ≤ α := by linarith only [hL132_ge]
    have h2 := (div_le_iff₀ hδ).mp h1
    have hαμ : α * μ = 1 := by rw [← hμ_inv, inv_mul_cancel₀ hμ0.ne']
    have hm := mul_le_mul_of_nonneg_right h2 hμ0.le
    linarith only [hm, (by linear_combination δ * hαμ : δ * α * μ = δ)]
  have hC_lev0 : 0 ≤ C_lev := by
    rw [hC_lev_def]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have := factorialSpanGammaOffset_nonneg
    positivity
  have hμ_le_δ : μ ≤ δ := by
    have : 0 ≤ (16 * Real.pi + 8 * C_lev + 7) * μ := by positivity
    linarith only [hμ_small, this]
  have hh_small : 80 * h ≤ δ := by
    have h1 : 80 / δ ≤ L := by linarith only [hL_80δ]
    have h2 : 80 ≤ δ * (T * L) := by
      have hm := (div_le_iff₀ hδ).mp h1
      nlinarith only [hm, hT1, hδ, hL0]
    rw [hh_def, mul_one_div, div_le_iff₀ (mul_pos hT0 hL0)]
    exact h2
  have hden128 : 0 < 128 * explicitConductorCutoffConstant * ℓ ^ 5 :=
    mul_pos (mul_pos (by norm_num) hD) (pow_pos hℓ0 5)
  have h1_k₁ : (δ / 4) * (k₁ / 16) =
      (δ * L) / (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by
    rw [hk₁_def]; ring
  have hord_P_le : 2 * Real.pi * α ≤ (δ / 4) * (k₁ / 16) := by
    rw [h1_k₁, le_div_iff₀ hden128]
    have hm := mul_le_mul_of_nonneg_left hP_ord hδ.le
    have hid : δ * ((256 * Real.pi * explicitConductorCutoffConstant / δ) * α * ℓ ^ 5) =
        2 * Real.pi * α * (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by
      calc δ * ((256 * Real.pi * explicitConductorCutoffConstant / δ) * α * ℓ ^ 5)
          = (δ * (256 * Real.pi * explicitConductorCutoffConstant / δ)) * α * ℓ ^ 5 := by ring
        _ = (256 * Real.pi * explicitConductorCutoffConstant) * α * ℓ ^ 5 := by
            rw [mul_div_cancel₀ _ hδ.ne']
        _ = 2 * Real.pi * α * (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by ring
    linarith only [hm, hid]
  have hpre_P_le :
      c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost + (Real.log 4 + 4) ≤
        (δ / 4) * (k₁ / 16) := by
    have hAsep0 : 0 ≤ separatedCrossMassCost := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      unfold separatedCrossMassCost; positivity
    have hC₄0 : 0 ≤ Real.log 4 + 4 := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    have hC_pre0 : 0 ≤ C_pre := by
      rw [hC_pre_def]
      exact add_nonneg (add_nonneg (add_nonneg zero_le_one (mul_nonneg zero_le_two (abs_nonneg _)))
        (mul_nonneg zero_le_two hAsep0)) hC₄0
    have hc_le : c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
        (Real.log 4 + 4) ≤ C_pre * K_c * L ^ (1 / 8 : ℝ) := by
      have h1 : c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
          (Real.log 4 + 4) ≤ C_pre * c := by
        rw [hC_pre_def]; nlinarith only [hc1, abs_nonneg (gammaHardyPhaseRate 0), hAsep0, hC₄0]
      exact (h1.trans (mul_le_mul_of_nonneg_left hc_up hC_pre0)).trans_eq (by ring)
    rw [h1_k₁, le_div_iff₀ hden128]
    have hm1 := mul_le_mul_of_nonneg_right hc_le hden128.le
    have hm2 := mul_le_mul_of_nonneg_left hP_pre hδ.le
    have hid : δ * ((128 * explicitConductorCutoffConstant * C_pre * K_c / δ) *
        L ^ (1 / 8 : ℝ) * ℓ ^ 5) =
        (C_pre * K_c * L ^ (1 / 8 : ℝ)) * (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by
      calc δ * ((128 * explicitConductorCutoffConstant * C_pre * K_c / δ) *
            L ^ (1 / 8 : ℝ) * ℓ ^ 5)
          = (δ * (128 * explicitConductorCutoffConstant * C_pre * K_c / δ)) *
              L ^ (1 / 8 : ℝ) * ℓ ^ 5 := by ring
        _ = (128 * explicitConductorCutoffConstant * C_pre * K_c) *
              L ^ (1 / 8 : ℝ) * ℓ ^ 5 := by rw [mul_div_cancel₀ _ hδ.ne']
        _ = (C_pre * K_c * L ^ (1 / 8 : ℝ)) *
              (128 * explicitConductorCutoffConstant * ℓ ^ 5) := by ring
    linarith only [hm1, hm2, hid]
  exact ⟨hμ_small, hC_lev0, hμ_le_δ, hh_small, hord_P_le, hpre_P_le⟩

private lemma collar_bridge_linear_assembly
    {G c I₂ δ k₁ α μ h C_lev C_p W8 Lev U2 P E aN pN aP pP ay py iF iFcoh iFhco iFFh wq : ℝ}
    (hG0 : 0 < G) (hc0 : 0 < c) (hI₂ : 0 < I₂) (hδ : 0 < δ) (hh0 : 0 < h) (hμ0 : 0 < μ)
    (hC_lev0 : 0 ≤ C_lev) (hP0 : 0 ≤ P) (hW8_0 : 0 ≤ W8) (hlev_0 : 0 ≤ Lev) (hU2_0 : 0 ≤ U2)
    (hμ_small : (16 * Real.pi + 8 * C_lev + 8) * μ ≤ δ)
    (hμ_le_δ : μ ≤ δ) (hh_small : 80 * h ≤ δ)
    (hord_P_le : 2 * Real.pi * α ≤ (δ / 4) * (k₁ / 16))
    (hpre_P_le : C_p ≤ (δ / 4) * (k₁ / 16))
    (henergy : E = aN / G - pN / G)
    (harch_ord : aP + ay - 2 * Real.pi * (α * (G * P) + μ * (G * ((c / I₂) * U2))) ≤ aN)
    (hPb : -(G * (C_p * P)) ≤ aP - pP)
    (hSb : pN = pP + py + 2 * iF)
    (hint_split : iF = (iFcoh + iFhco) + iFFh)
    (hpole_rem : G * ((c / I₂) * wq) - h * (G * ((c / I₂) * (W8 + 10 * U2))) ≤ ay - py - 2 * iFcoh)
    (hoff_total : 2 * |iFhco| ≤ μ * (G * ((c / I₂) * U2)) +
      G * ((δ / 4) * ((c / I₂) * W8) + (δ / 8) * ((c / I₂) * U2) + (δ / 4) * ((k₁ / 16) * P)))
    (hfreq_total : 2 * |iFFh| ≤ μ * (G * ((c / I₂) * Lev)) +
      (μ * (1 + C_lev)) * (G * ((c / I₂) * U2)) + G * ((δ / 4) * ((k₁ / 16) * P))) :
    wq - δ * ((I₂ / c) * (k₁ / 16) * P + W8 + Lev + U2) ≤ (I₂ / c) * E := by
  set S_G := G * (c / I₂)
  have hSG0 : 0 < S_G := mul_pos hG0 (div_pos hc0 hI₂)
  refine le_of_mul_le_mul_left ?_ hSG0
  have hcI : S_G * (I₂ / c) = G := by
    dsimp only [S_G]
    calc G * (c / I₂) * (I₂ / c) = G * ((c / I₂) * (I₂ / c)) := by ring
      _ = G * 1 := by rw [div_mul_div_cancel₀ hI₂.ne', div_self hc0.ne']
      _ = G := mul_one G
  have hSG_rhs : S_G * ((I₂ / c) * E) = aN - pN := by
    have h1 : S_G * ((I₂ / c) * E) = G * E := by rw [← mul_assoc, hcI]
    rw [h1, henergy, mul_sub, mul_div_cancel₀ _ hG0.ne', mul_div_cancel₀ _ hG0.ne']
  have hSG_lhs : S_G * (wq - δ * ((I₂ / c) * (k₁ / 16) * P + W8 + Lev + U2)) =
      S_G * wq - δ * (G * ((k₁ / 16) * P)) - δ * (S_G * W8) - δ * (S_G * Lev) - δ * (S_G * U2) := by
    linear_combination (-δ * ((k₁ / 16) * P)) * hcI
  rw [hSG_lhs, hSG_rhs]
  have hP_budget :
      2 * Real.pi * (α * (G * P)) + G * (C_p * P) +
        G * ((δ / 4) * ((k₁ / 16) * P)) + G * ((δ / 4) * ((k₁ / 16) * P)) ≤
      δ * (G * ((k₁ / 16) * P)) := by
    have b1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hord_P_le hP0) hG0.le
    have b2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpre_P_le hP0) hG0.le
    linarith only [b1, b2,
      (by ring : 2 * Real.pi * (α * (G * P)) = G * ((2 * Real.pi * α) * P)),
      (by ring : G * (((δ / 4) * (k₁ / 16)) * P) = G * ((δ / 4) * ((k₁ / 16) * P)))]
  have hW8_budget :
      h * (S_G * W8) + G * ((δ / 4) * ((c / I₂) * W8)) ≤ δ * (S_G * W8) := by
    have hh4 : h ≤ δ / 4 := by linarith only [hh_small, hh0]
    have b1 := mul_le_mul_of_nonneg_right hh4 (mul_nonneg hSG0.le hW8_0)
    have b2 : 0 ≤ (δ / 2) * (S_G * W8) := mul_nonneg (by positivity) (mul_nonneg hSG0.le hW8_0)
    dsimp only [S_G] at b1 b2 ⊢
    linarith only [b1, b2]
  have hlev_budget : μ * (S_G * Lev) ≤ δ * (S_G * Lev) :=
    mul_le_mul_of_nonneg_right hμ_le_δ (mul_nonneg hSG0.le hlev_0)
  have hU2_budget :
      2 * Real.pi * (μ * (S_G * U2)) + 10 * h * (S_G * U2) + μ * (S_G * U2) +
        G * ((δ / 8) * ((c / I₂) * U2)) + (μ * (1 + C_lev)) * (S_G * U2) ≤
      δ * (S_G * U2) := by
    have hsum_c : 2 * Real.pi * μ + 10 * h + μ + δ / 8 + μ * (1 + C_lev) ≤ δ := by
      have hpiμ : 0 ≤ Real.pi * μ := mul_nonneg Real.pi_pos.le hμ0.le
      have hCμ : 0 ≤ C_lev * μ := mul_nonneg hC_lev0 hμ0.le
      linarith only [hμ_small, hh_small, hpiμ, hCμ, hμ0, hδ,
        (by ring : (16 * Real.pi + 8 * C_lev + 8) * μ =
          16 * (Real.pi * μ) + 8 * (C_lev * μ) + 8 * μ),
        (by ring : 2 * Real.pi * μ + μ + μ * (1 + C_lev) =
          2 * (Real.pi * μ) + (C_lev * μ) + 2 * μ)]
    have bm := mul_le_mul_of_nonneg_right hsum_c (mul_nonneg hSG0.le hU2_0)
    dsimp only [S_G] at bm ⊢
    linarith only [bm]
  have habs1 := le_abs_self iFhco
  have habs2 := le_abs_self iFFh
  dsimp only [S_G] at hP_budget hW8_budget hlev_budget hU2_budget ⊢
  linarith only [harch_ord, hPb, hSb, hpole_rem, hint_split, hoff_total, hfreq_total,
    hP_budget, hW8_budget, hlev_budget, hU2_budget, habs1, habs2]

/-- **Signed PNT pole-cancellation bridge on `(conductorSubspace 1 N)ᗮ`.**
Subtracting `smoothedCoherent` from the smoothed prime translate of the prefix cancels the rank-two
pole pairing of `weilQuad U_y` up to `O(h)`, bounding `(I₂ / c) completeWeilEnergy c N z` below by
`weilQuad U_y` minus an arbitrarily small `δ`-fraction of the prefix, `W₈`, Lévy, and `L²` norms. -/
theorem eventually_poleOrthogonal_collar_weilQuad_bridge
    {R_max δ : ℝ} (hR : 0 < R_max) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
        ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
          let I₂ := ∫ u, tiltedUnitSpline u ^ 2
          let x := primeHorizonExtension z
          let M := N / linearDefectCutoff c
          let y := atomicTailCoefficients M x
          let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
          let L := Real.log (N : ℝ)
          let ℓ := 1 + Real.log L
          let k₁ := L / (2 * explicitConductorCutoffConstant * ℓ ^ 5)
          weilQuad U_y -
              δ * ((I₂ / c) * (k₁ / 16) * (∑ n ∈ Icc 1 M, x n ^ 2) +
                (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
                levyEnergy U_y +
                ∫ u, U_y u ^ 2) ≤
            (I₂ / c) * completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨C_ψ, c₀, t₀, hCψ, hc₀, ht₀1, hpnt⟩ := exists_vonMangoldtAtom_window_error
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hI₂ : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  set K_c : ℝ := (R_max + 1) ^ (1 / 8 : ℝ)
  have hKc0 : 0 < K_c := by dsimp only [K_c]; positivity
  set C_β : ℝ := 1 + 36 / c₀ ^ 2 + |Real.log t₀|
  set C_tr : ℝ := (1 + 2 * Real.exp 2) *
    (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4))
  set C_pre : ℝ := 1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost + (Real.log 4 + 4)
  set C_lev : ℝ := 2 * |gammaHardyPhaseRate 0| + factorialSpanGammaOffset + Real.log 2 + 1
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLN_zero : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hev_L2N : ∀ᶠ N : ℕ in atTop,
      2 * ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)) * Real.log (N : ℝ) ≤ N := by
    set A := 2 * ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1))
    have hA : 0 < A := by positivity
    have hev := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / A))
    filter_upwards [hev, eventually_ge_atTop 1] with N hlt hN1
    dsimp only [Function.comp_def] at hlt
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hm := (div_lt_iff₀ hN0).mp hlt
    have hid : 1 / A * (N : ℝ) = (N : ℝ) / A := by field_simp
    exact ((le_div_iff₀ hA).mp (by linarith)).trans_eq' (mul_comm _ _)
  have hev_edg : ∀ᶠ N : ℕ in atTop,
      48 * Real.exp 1 * (Real.log (N : ℝ) / N) ≤ δ / 8 := by
    have hev := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < (δ / 8) / (48 * Real.exp 1)))
    filter_upwards [hev] with N hlt
    dsimp only [Function.comp_def] at hlt
    have hm := (lt_div_iff₀ (by positivity : (0 : ℝ) < 48 * Real.exp 1)).mp hlt
    linarith only [hm, (by ring : (Real.log (N : ℝ) / N) * (48 * Real.exp 1) =
      48 * Real.exp 1 * (Real.log (N : ℝ) / N))]
  filter_upwards [
    hev_L2N, hev_edg,
    hLlim.eventually (eventually_ge_atTop (max (max 4 (R_max + 1)) (80 / δ + 1))),
    hLlim.eventually ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).eventually_ge_atTop
      ((16 * Real.pi + 8 * C_lev + 8) / δ + 1)),
    hLlim.eventually ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 16)).eventually_ge_atTop
      (factorialSpanGammaOffset + Real.log (4 * C_ψ + 1) + 4)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow (by norm_num : (0 : ℝ) < 3 / 16) 1 1),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (1 / 32 : ℝ) < 1) 5
      (256 * Real.pi * explicitConductorCutoffConstant / δ)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (1 / 8 : ℝ) < 1) 5
      (128 * explicitConductorCutoffConstant * C_pre * K_c / δ)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (31 / 32 : ℝ) < 1) 6
      (1280 * explicitConductorCutoffConstant * C_tr * K_c / δ)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (29 / 32 : ℝ) < 1) 5
      (128 * explicitConductorCutoffConstant * splineWindowConstant *
        (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
        (C_β + 1 + (Real.log 4 + 4)) ^ 2 * K_c / δ)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (3 / 8 : ℝ) < 1) 1
      (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset + C_β)),
    eventually_ge_atTop 3] with
      N hL2N_b hedg_b hL_ge hL132_ge hL316_C hlogL_316 hP_ord hP_pre hP_tr hP_off hexp_b hN3
  intro c hc1 hc8 z hz I₂ x M y U_y L ℓ k₁
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL4 : 4 ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL_ge
  have hR_L : R_max + 1 ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL_ge
  have hL_80δ : 80 / δ + 1 ≤ L := (le_max_right _ _).trans hL_ge
  have hL1 : 1 ≤ L := by linarith only [hL4]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hℓ1 : 1 ≤ ℓ := by dsimp only [ℓ]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hc_up : c ≤ K_c * L ^ (1 / 8 : ℝ) := by
    have hp : c ^ 8 ≤ (K_c * L ^ (1 / 8 : ℝ)) ^ 8 := by
      dsimp only [K_c]
      rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le,
        ← Real.rpow_natCast ((R_max + 1) ^ _), ← Real.rpow_mul (by positivity : 0 ≤ R_max + 1),
        show (1 / 8 : ℝ) * (8 : ℕ) = 1 by norm_num, Real.rpow_one, Real.rpow_one]
      nlinarith only [hc8, hL0]
    exact le_of_pow_le_pow_left₀ (by norm_num : 8 ≠ 0) (by positivity) hp
  have hcL : c ≤ L := by
    have hc8_L2 : c ^ 8 ≤ L ^ 2 := by nlinarith only [hc8, hR_L, hL0]
    have hL2_8 : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
    exact le_of_pow_le_pow_left₀ (by norm_num : 8 ≠ 0) hL0.le (hc8_L2.trans hL2_8)
  obtain ⟨hL3, h4c, -, hLup⟩ := linearDefectCutoff_bounds hc1
  have h2LN : 2 * linearDefectCutoff c ≤ N := by
    have hc2_RL : c ^ 2 ≤ (R_max + 1) * L := by
      have h28 : c ^ 2 ≤ c ^ 8 := pow_le_pow_right₀ hc1 (by norm_num)
      nlinarith only [h28, hc8, hL0]
    have h1 : (linearDefectCutoff c : ℝ) ^ 2 ≤ (256 * Real.exp 2 + 4) ^ 2 * c ^ 2 :=
      (pow_le_pow_left₀ (by positivity) hLup 2).trans_eq (mul_pow _ _ 2)
    have h2 : 2 * ((256 * Real.exp 2 + 4) ^ 2 * c ^ 2) ≤
        2 * ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)) * L := by
      calc 2 * ((256 * Real.exp 2 + 4) ^ 2 * c ^ 2)
          = (2 * (256 * Real.exp 2 + 4) ^ 2) * c ^ 2 := by ring
        _ ≤ (2 * (256 * Real.exp 2 + 4) ^ 2) * ((R_max + 1) * L) :=
            mul_le_mul_of_nonneg_left hc2_RL (by positivity)
        _ = 2 * ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)) * L := by ring
    have hLc1 : (1 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast (show 1 ≤ linearDefectCutoff c by omega)
    have hsq := le_self_pow₀ hLc1 (by norm_num : 2 ≠ 0)
    have hle : ((2 * linearDefectCutoff c : ℕ) : ℝ) ≤ N := by
      push_cast; linarith only [h1, h2, hL2N_b, hsq]
    exact_mod_cast hle
  have hLN : linearDefectCutoff c ≤ N := by omega
  have hM1 : 1 ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
  have hMN : M ≤ N := Nat.div_le_self _ _
  have hcN : c ≤ N := by
    have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  set w := c / (N : ℝ)
  have hw0 : 0 < w := div_pos hc0 hN0
  have hw1 : w ≤ 1 := (div_le_one hN0).mpr hcN
  set g := atomDilate tiltedUnitSpline w
  set G := w * I₂
  have hG0 : 0 < G := mul_pos hw0 hI₂
  have hg_cd : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hg_supp := tiltedUnitSpline_atom_support hw0
  have hg_cs := hasCompactSupport_of_support_Icc hg_supp
  have hg0 : ∀ u, 0 ≤ g u := fun _ => RenormalizedIntersectionTheory.tiltedUnitSpline_nonneg _
  set f_P := atomicTest M x g
  set f_y := atomicTest N y g
  have hfy_cd : ContDiff ℝ 2 f_y := contDiff_atomicTest hg_cd N y
  have hfy_cs : HasCompactSupport f_y := hasCompactSupport_atomicTest hg_supp N y
  obtain ⟨hUy_cd, hUy_cs, hUy_w, hfy_L2, hfy_arch, _⟩ :=
    normalizedCentredAtomicTest_scaling hc0 hN1 y
  change (∫ u, f_y u ^ 2) = G * ((c / I₂) * ∫ u, U_y u ^ 2) at hfy_L2
  change archForm f_y = G * ((c / I₂) * archForm U_y) at hfy_arch
  have hUy_le1 : ∀ u, 1 < u → U_y u = 0 := fun u hu => hUy_w u (hw1.trans_lt hu)
  set P := ∑ n ∈ Icc 1 M, x n ^ 2
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hW8_0 : 0 ≤ ∫ u, U_y u ^ 2 * Real.exp (-(8 * u)) := integral_nonneg fun _ => by positivity
  have hU2_0 : 0 ≤ ∫ u, U_y u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hlev_0 : 0 ≤ levyEnergy U_y := levyEnergy_nonneg' U_y
  -- 1. Ordered archimedean split, prefix block, and prime split
  set α := L ^ (1 / 32 : ℝ)
  have hα0 : 0 < α := Real.rpow_pos_of_pos hL0 _
  have hα_inv : α⁻¹ = L ^ (-1 / 32 : ℝ) := by
    dsimp only [α]
    rw [show (-1 / 32 : ℝ) = -(1 / 32 : ℝ) by norm_num, Real.rpow_neg hL0.le]
  have harch_ord := weighted_archForm_prefix_top_split_ge hc1 hα0 hLN hM1 x
  have hPb_raw := prefix_block_ge hc1 hLN hM1 x
  have hPD0 : 0 ≤ poleDefect M x := poleDefect_nonneg M x
  have hPb : -(G * ((c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
      (Real.log 4 + 4)) * P)) ≤ archForm f_P - primeSum f_P := by
    have := mul_nonneg hG0.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 8) hPD0)
    dsimp only [G, w, I₂, M, f_P, g, P] at hPb_raw ⊢
    linarith only [hPb_raw, this]
  set Bn := ⌊(N : ℝ) * Real.exp w⌋₊
  set V : ℕ → ℝ := fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv (primeOrderCutoff N w) M x n
  set F := atomicTest Bn V g
  have hSb : primeSum (atomicTest N x g) = primeSum f_P + primeSum f_y + 2 * ∫ u, f_y u * F u :=
    primeSum_prefix_top_split hc1 h2LN x
  have henergy := completeWeilEnergy_eq_arch_sub_primeSum hc0 hN2 hz
  rw [integral_atomDilate_sq hw0] at henergy
  change completeWeilEnergy tiltedUnitSpline c N z =
    archForm (atomicTest N x g) / G - primeSum (atomicTest N x g) / G at henergy
  -- 2. Coherent pole subtraction and signed PNT window remainder
  set G₀ := factorialSpanGammaOffset
  have hG₀ : 0 ≤ G₀ := factorialSpanGammaOffset_nonneg
  set T := Real.exp (G₀ + L ^ (3 / 16 : ℝ))
  have hT0 : 0 < T := Real.exp_pos _
  have hT1 : 1 ≤ T := Real.one_le_exp (add_nonneg hG₀ (Real.rpow_nonneg hL0.le _))
  set h := 1 / (T * L)
  have hh0 : 0 < h := div_pos zero_lt_one (mul_pos hT0 hL0)
  have hh1 : h ≤ 1 := (div_le_one (mul_pos hT0 hL0)).mpr (one_le_mul_of_one_le_of_one_le hT1 hL1)
  have hh_quarter : h ≤ 1 / 4 := by
    rw [le_div_iff₀ (by norm_num)]
    dsimp only [h]
    rw [one_div_mul_eq_div, div_le_one (mul_pos hT0 hL0)]
    nlinarith only [hT1, hL4]
  have hTh : T * h = 1 / L := by dsimp only [h]; field_simp [hT0.ne', hL0.ne']
  set Fh := atomicTest Bn V (smoothedBump g h)
  set F_coh := smoothedCoherent g (Real.log ((M : ℝ) / 2) + h) (Real.log (N : ℝ) + w) h
    (prefixPoleMoment M x)
  obtain ⟨hi_coh, hpole_cancel⟩ :=
    integral_tail_mul_smoothedCoherent_eq hc1 h2LN hh0 hh_quarter hz
  change Integrable (fun u => f_y u * F_coh u) at hi_coh
  change -2 * (∫ u, f_y u * F_coh u) =
    2 * ((1 - Real.exp (-h)) / h) *
      (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)) at hpole_cancel
  obtain ⟨hwq_scale, hpole_scale⟩ := weilQuad_collar_scaling hc0 hN1 y
  change archForm f_y - primeSum f_y +
    2 * (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)) =
    G * ((c / I₂) * weilQuad U_y) at hwq_scale
  change 2 * (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)) =
    G * ((c / I₂) *
      (2 * (∫ u, U_y u * Real.exp (-(u / 2))) * (∫ u, U_y u * Real.exp (u / 2)))) at hpole_scale
  obtain ⟨h1eh_0, h1eh_h⟩ := one_sub_div_exp_neg_bounds hh0
  have hpole_rem :
      G * ((c / I₂) * weilQuad U_y) -
        h * (G * ((c / I₂) * ((∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + 10 * ∫ u, U_y u ^ 2))) ≤
        archForm f_y - primeSum f_y - 2 * ∫ u, f_y u * F_coh u := by
    have hid : archForm f_y - primeSum f_y - 2 * (∫ u, f_y u * F_coh u) =
        G * ((c / I₂) * weilQuad U_y) -
          (1 - (1 - Real.exp (-h)) / h) *
            (2 * (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2))) := by
      have hsub : -2 * (∫ u, f_y u * F_coh u) = -(2 * ∫ u, f_y u * F_coh u) := by ring
      rw [hsub] at hpole_cancel
      linarith only [hwq_scale, hpole_cancel,
        (by ring : (1 - (1 - Real.exp (-h)) / h) *
            (2 * (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2))) =
          2 * (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)) -
            2 * ((1 - Real.exp (-h)) / h) *
              (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)))]
    rw [hid, hpole_scale]
    have habs_u := two_mul_abs_collar_pole_le hUy_cd hUy_cs hUy_le1
    have hle1 := le_abs_self
      ((∫ u, U_y u * Real.exp (-(u / 2))) * (∫ u, U_y u * Real.exp (u / 2)))
    have hle2 : 2 * (∫ u, U_y u * Real.exp (-(u / 2))) * (∫ u, U_y u * Real.exp (u / 2)) ≤
        (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + 10 * ∫ u, U_y u ^ 2 := by
      linarith only [hle1, habs_u,
        (by ring : 2 * (∫ u, U_y u * Real.exp (-(u / 2))) * (∫ u, U_y u * Real.exp (u / 2)) =
          2 * ((∫ u, U_y u * Real.exp (-(u / 2))) * (∫ u, U_y u * Real.exp (u / 2))))]
    have hm1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle2 (div_nonneg hc0.le hI₂.le)) hG0.le)
      h1eh_0
    have hm2 := mul_le_mul_of_nonneg_right h1eh_h
      (mul_nonneg hG0.le (mul_nonneg (div_nonneg hc0.le hI₂.le)
        (add_nonneg hW8_0 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hU2_0))))
    linarith only [hm1, hm2]
  -- 3. Integral decomposition of `∫ f_y * F`
  have hF_cd : ContDiff ℝ 2 F := contDiff_atomicTest hg_cd Bn V
  have hF_cs : HasCompactSupport F := hasCompactSupport_atomicTest hg_supp Bn V
  have hFh_cd : ContDiff ℝ 2 Fh :=
    contDiff_atomicTest (contDiff_smoothedBump hg_cd hg_cs h) Bn V
  have hFh_cs : HasCompactSupport Fh :=
    hasCompactSupport_atomicTest (w := w + h) (fun v hv => smoothedBump_eq_zero hg_supp hv) Bn V
  have hFFh_cd : ContDiff ℝ 2 (fun u => F u - Fh u) := hF_cd.sub hFh_cd
  have hFFh_cs : HasCompactSupport (fun u => F u - Fh u) := hF_cs.sub hFh_cs
  have hi_Fh : Integrable fun u => f_y u * Fh u :=
    (hfy_cd.continuous.mul hFh_cd.continuous).integrable_of_hasCompactSupport hfy_cs.mul_right
  have hi_FFh : Integrable fun u => f_y u * (F u - Fh u) :=
    (hfy_cd.continuous.mul hFFh_cd.continuous).integrable_of_hasCompactSupport hfy_cs.mul_right
  have hi_Fh_coh : Integrable fun u => f_y u * (Fh u - F_coh u) := by
    refine (hi_Fh.sub hi_coh).congr (Eventually.of_forall fun u => ?_)
    simp only [Pi.sub_apply]; ring
  have hint_split : ∫ u, f_y u * F u =
      (∫ u, f_y u * F_coh u) + (∫ u, f_y u * (Fh u - F_coh u)) +
        ∫ u, f_y u * (F u - Fh u) := by
    have h1 : (fun u => f_y u * F u) =
        fun u => (f_y u * F_coh u + f_y u * (Fh u - F_coh u)) + f_y u * (F u - Fh u) :=
      funext fun u => by ring
    rw [h1,
      integral_add (f := fun u => f_y u * F_coh u + f_y u * (Fh u - F_coh u))
        (g := fun u => f_y u * (F u - Fh u)) (hi_coh.add hi_Fh_coh) hi_FFh,
      integral_add (f := fun u => f_y u * F_coh u) (g := fun u => f_y u * (Fh u - F_coh u))
        hi_coh hi_Fh_coh]
  -- 4. Off-pole smoothed term `2 * |∫ f_y * (Fh - F_coh)|`
  have hlogL_ub : Real.log L ≤ L ^ (3 / 16 : ℝ) := by
    have h1 : 1 + Real.log L ≤ L ^ (3 / 16 : ℝ) := by
      dsimp only [L]; simpa only [one_mul, Real.rpow_zero, pow_one] using hlogL_316
    linarith only [h1]
  have hexp_b' : (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset + C_β) *
      L ^ (3 / 8 : ℝ) ≤ L := by
    have hp : (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset + C_β) *
        L ^ (3 / 8 : ℝ) * ℓ ≤ L := by
      dsimp only [L, ℓ]; simpa only [pow_one, Real.rpow_one] using hexp_b
    have hC0 : 0 ≤ (|Real.log (2 * (Real.log 4 + 4))| + 4 + factorialSpanGammaOffset + C_β) *
        L ^ (3 / 8 : ℝ) := by dsimp only [C_β]; positivity
    exact (le_mul_of_one_le_right hC0 hℓ1).trans hp
  obtain ⟨K', hK'1, ht₀K', hpntK', hlogK', hK'le⟩ :=
    exists_short_cutoff hCψ hc₀ ht₀1 hh0 hh1
  obtain ⟨_, hF_mass⟩ := translate_masses_le hCψ hc₀ hpnt hc1 h2LN x hh0 hh1 hK'1 ht₀K'
  obtain ⟨hi_RF2, hRF2_le⟩ := integral_sq_smoothedBump_sub_smoothedCoherent_le hg_cd hg_supp hg0
    hh0 Bn V (Real.log ((M : ℝ) / 2) + h) (Real.log (N : ℝ) + w) (prefixPoleMoment M x)
  have hi_fy2 : Integrable fun u => f_y u ^ 2 :=
    (hfy_cd.continuous.pow 2).integrable_of_hasCompactSupport (by
      rw [hasCompactSupport_iff_eventuallyEq] at hfy_cs ⊢
      exact hfy_cs.mono fun u hu => by change f_y u = 0 at hu; change f_y u ^ 2 = 0; rw [hu]; ring)
  set μ := L ^ (-1 / 32 : ℝ)
  have hμ0 : 0 < μ := Real.rpow_pos_of_pos hL0 _
  have hμ_inv : μ⁻¹ = α := by
    dsimp only [μ, α]
    rw [show (-1 / 32 : ℝ) = -(1 / 32 : ℝ) by norm_num, Real.rpow_neg hL0.le, inv_inv]
  have hcs_off := two_mul_abs_integral_mul_le_of_integrable_sq hi_fy2 hi_RF2 hi_Fh_coh hμ0
  have hg_int_id : (∫ t, g t) ^ 2 / h ^ 2 = G * (splineWindowConstant * (w / h ^ 2)) := by
    have hint_g : ∫ t, g t = w * ∫ u, tiltedUnitSpline u := by
      dsimp only [g, atomDilate]
      simpa only [smul_eq_mul, abs_of_pos hw0] using Measure.integral_comp_div tiltedUnitSpline w
    rw [hint_g]
    unfold splineWindowConstant
    dsimp only [G, I₂]
    set I₁ := ∫ u, tiltedUnitSpline u
    set I₂' := ∫ u, tiltedUnitSpline u ^ 2
    have hc : I₂' * (I₁ ^ 2 / I₂') = I₁ ^ 2 := mul_div_cancel₀ _ hI₂.ne'
    calc (w * I₁) ^ 2 / h ^ 2 = w * I₁ ^ 2 * (w / h ^ 2) := by ring
      _ = w * (I₂' * (I₁ ^ 2 / I₂')) * (w / h ^ 2) := by rw [hc]
      _ = w * I₂' * (I₁ ^ 2 / I₂' * (w / h ^ 2)) := by ring
  have hoff_win := collar_bridge_offPole_window_le hCψ hc₀ hδ hKc0 hpnt hN2 hc1 hcN hL1 hc_up hcL
    h2LN hz rfl hK'1 ht₀K' hpntK' hlogK' hK'le hL316_C hlogL_ub hexp_b' hedg_b
    (by simpa only [Real.rpow_one] using hP_off)
  have hoff_total :
      2 * |∫ u, f_y u * (Fh u - F_coh u)| ≤
        μ * (G * ((c / I₂) * ∫ u, U_y u ^ 2)) +
          G * ((δ / 4) * ((c / I₂) * ∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) +
            (δ / 8) * ((c / I₂) * ∫ u, U_y u ^ 2) +
            (δ / 4) * ((k₁ / 16) * P)) := by
    rw [hfy_L2, hμ_inv] at hcs_off
    have hm1 := mul_le_mul_of_nonneg_left hRF2_le hα0.le
    rw [hg_int_id] at hm1
    have hm2 := mul_le_mul_of_nonneg_left hoff_win hG0.le
    have hid : α * (G * (splineWindowConstant * (w / h ^ 2)) *
        ∫ s, (windowSum Bn V h s -
          coherentWindow (Real.log ((M : ℝ) / 2) + h) (Real.log (N : ℝ) + w) h
            (prefixPoleMoment M x) s) ^ 2) =
        G * (α * splineWindowConstant * ((w / h ^ 2) *
          ∫ s, (windowSum Bn V h s -
            coherentWindow (Real.log ((M : ℝ) / 2) + h) (Real.log (N : ℝ) + w) h
              (prefixPoleMoment M x) s) ^ 2)) := by ring
    rw [hid] at hm1
    dsimp only [α, L, ℓ, k₁, I₂, w, x, M, y, U_y, Bn, V, P] at hcs_off hm1 hm2 ⊢
    linarith only [hcs_off, hm1, hm2]
  -- 5. Frequency-split smoothing remainder `2 * |∫ f_y * (F - Fh)|`
  set lam := L ^ (5 / 32 : ℝ)
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos hL0 _
  have hfreq := two_mul_abs_integral_mul_le hfy_cd hfy_cs hFFh_cd hFFh_cs T hμ0 hlam0
  have hlowD := lowFourierMass_atomicTest_sub_smoothedBump_le hg_cd hg_supp hh0 Bn V T
  have hhighD := highFourierMass_atomicTest_sub_smoothedBump_le hg_cd hg_supp hh0 Bn V T
  have hLMy := lowFourierMass_le_integral_sq hfy_cd hfy_cs T
  have htr_ub := collar_bridge_translate_factor_le hc1 h2LN hN1 hM1 hMN hKc0 hδ hL1 hc_up hcL hTh
    (by simpa only [Real.rpow_one] using hP_tr)
  have hhigh_fy : lam * highFourierMass f_y T ≤
      μ * (G * ((c / I₂) * levyEnergy U_y)) +
        (μ * C_lev) * (G * ((c / I₂) * ∫ u, U_y u ^ 2)) := by
    have hb := archForm_ge_high_band hfy_cd hfy_cs (T := T) (R := T) hT0 le_rfl
    rw [sub_self, zero_mul, add_zero, show Real.log T - G₀ = L ^ (3 / 16 : ℝ) by
      rw [Real.log_exp]; ring] at hb
    have hmul_μ := mul_le_mul_of_nonneg_left hb hμ0.le
    have hlam_id : μ * (L ^ (3 / 16 : ℝ) * highFourierMass f_y T) = lam * highFourierMass f_y T := by
      rw [← mul_assoc]
      congr 1
      dsimp only [μ, lam]
      rw [← Real.rpow_add hL0]; norm_num
    have harch_ub : archForm f_y ≤
        G * ((c / I₂) * levyEnergy U_y) +
          (2 * |gammaHardyPhaseRate 0|) * (G * ((c / I₂) * ∫ u, U_y u ^ 2)) := by
      rw [hfy_arch, archForm_eq_levyEnergy hUy_cd hUy_cs]
      have hm := mul_le_mul_of_nonneg_right (le_abs_self (gammaHardyPhaseRate 0))
        (mul_nonneg (by positivity : 0 ≤ 2 * G * (c / I₂)) hU2_0)
      linarith only [hm,
        (by ring : G * ((c / I₂) * (2 * gammaHardyPhaseRate 0 * (∫ u, U_y u ^ 2) + levyEnergy U_y)) =
          G * ((c / I₂) * levyEnergy U_y) +
            gammaHardyPhaseRate 0 * (2 * G * (c / I₂) * ∫ u, U_y u ^ 2)),
        (by ring : |gammaHardyPhaseRate 0| * (2 * G * (c / I₂) * ∫ u, U_y u ^ 2) =
          (2 * |gammaHardyPhaseRate 0|) * (G * ((c / I₂) * ∫ u, U_y u ^ 2)))]
    have hlm_ub : (G₀ + Real.log 2) * lowFourierMass f_y T ≤
        (G₀ + Real.log 2 + 1) * (G * ((c / I₂) * ∫ u, U_y u ^ 2)) := by
      rw [← hfy_L2]
      have h1 := mul_le_mul_of_nonneg_left hLMy
        (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)] : 0 ≤ G₀ + Real.log 2)
      have hfy2_0 : 0 ≤ ∫ u, f_y u ^ 2 := integral_nonneg fun u => sq_nonneg (f_y u)
      linarith only [h1, hfy2_0]
    have hsum_ub := mul_le_mul_of_nonneg_left (add_le_add harch_ub hlm_ub) hμ0.le
    dsimp only [C_lev]
    linarith only [hmul_μ, hlam_id, hsum_ub]
  have hfreq_total :
      2 * |∫ u, f_y u * (F u - Fh u)| ≤
        μ * (G * ((c / I₂) * levyEnergy U_y)) +
          (μ * (1 + C_lev)) * (G * ((c / I₂) * ∫ u, U_y u ^ 2)) +
          G * ((δ / 4) * ((k₁ / 16) * P)) := by
    have hm_low := mul_le_mul_of_nonneg_left (hLMy.trans_eq hfy_L2) hμ0.le
    have hm_D1 := mul_le_mul_of_nonneg_left hlowD (inv_nonneg.mpr hμ0.le)
    have hm_D2 := mul_le_mul_of_nonneg_left hhighD (inv_nonneg.mpr hlam0.le)
    have hm_F := mul_le_mul_of_nonneg_left hF_mass
      (by positivity : 0 ≤ μ⁻¹ * (T * h) ^ 2 + lam⁻¹ * 4)
    have hm_tr := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htr_ub hP0) hG0.le
    dsimp only [L, ℓ, k₁, w, M, Bn, μ, lam, F, G, I₂, P] at hm_F hm_tr hfreq hm_low hm_D1 hm_D2 hhigh_fy ⊢
    linarith only [hfreq, hm_low, hm_D1, hm_D2, hm_F, hm_tr, hhigh_fy,
      (by ring : μ⁻¹ * ((T * h) ^ 2 * ∫ u, atomicTest Bn V g u ^ 2) +
          lam⁻¹ * (4 * ∫ u, atomicTest Bn V g u ^ 2) =
        (μ⁻¹ * (T * h) ^ 2 + lam⁻¹ * 4) * ∫ u, atomicTest Bn V g u ^ 2),
      (by ring : (μ⁻¹ * (T * h) ^ 2 + lam⁻¹ * 4) *
          (w * I₂ * ((1 + 2 * Real.exp 1 * (w * Bn)) *
            (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) * P) =
        w * I₂ * (((μ⁻¹ * (T * h) ^ 2 + lam⁻¹ * 4) *
          ((1 + 2 * Real.exp 1 * (w * Bn)) *
            (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4))))) * P))]
  -- 6. Smallness of scalar prefactors in `L` and final assembly
  obtain ⟨hμ_small, hC_lev0, hμ_le_δ, hh_small, hord_P_le, hpre_P_le⟩ :=
    collar_bridge_scalar_bounds hδ hc1 hc_up hL0 hℓ0 hα0 hμ0 hT0 hT1 hD
      rfl rfl rfl rfl hμ_inv hL132_ge hL_80δ
      (by dsimp only [α, L, ℓ]; simpa only [Real.rpow_one] using hP_ord)
      (by dsimp only [L, ℓ]; simpa only [Real.rpow_one] using hP_pre)
  have harch_ord' :
      archForm f_P + archForm f_y -
        2 * Real.pi * (α * (G * P) + μ * (G * ((c / I₂) * ∫ u, U_y u ^ 2))) ≤
      archForm (atomicTest N x g) := by
    have h0 : archForm f_P + archForm f_y -
        2 * Real.pi * (α * (G * P) + α⁻¹ * (G * ((c / I₂) * ∫ u, U_y u ^ 2))) ≤
        archForm (atomicTest N x g) := harch_ord
    rwa [hα_inv] at h0
  exact collar_bridge_linear_assembly hG0 hc0 hI₂ hδ hh0 hμ0 hC_lev0 hP0 hW8_0 hlev_0 hU2_0
    hμ_small hμ_le_δ hh_small hord_P_le hpre_P_le henergy harch_ord' hPb hSb hint_split
    hpole_rem hoff_total hfreq_total

/-- **High-conductor collar compactness and `weilQuad` domination bridge.**
For every `R_max > 0`, there exist `B_far > 0` (independent of `ε`) and universal `c_W > 0` such
that for every `ε > 0`, eventually in `N`, every vector
`z ∈ (conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ` with nonpositive complete Weil energy at
`1 ≤ c`, `c⁸ ≤ R_max log N` has a high-conductor component `w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ`
whose collar profile `U_w` simultaneously controls `‖z‖²`, has uniformly bounded `W₈` and
archimedean Lévy energy relative to `∫ U_w²`, and satisfies `weilQuad U_w ≤ ε ∫ U_w²`. -/
theorem eventually_complement_collar_weilQuad_bridge :
    ∃ c_W : ℝ, 0 < c_W ∧
      ∀ {R_max : ℝ}, 0 < R_max →
        ∃ B_far : ℝ, 0 < B_far ∧
          ∀ {ε : ℝ}, 0 < ε →
            ∀ᶠ N : ℕ in atTop,
              ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
                ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
                  z ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ →
                  completeWeilEnergy tiltedUnitSpline c N z ≤ 0 →
                  ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
                    w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
                    let U_w := normalizedCentredAtomicTest tiltedUnitSpline
                      (atomicTailCoefficients (N / linearDefectCutoff c) (primeHorizonExtension w))
                      c N
                    (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 ≤
                        (c * B_far) * (∫ u, U_w u ^ 2) ∧
                      (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) ≤
                        (R_max * B_far / c_W) * (∫ u, U_w u ^ 2) ∧
                      levyEnergy U_w ≤
                        (4 * (∫ u, tiltedUnitSpline u ^ 2) * B_far) * (∫ u, U_w u ^ 2) ∧
                      weilQuad U_w ≤ ε * ∫ u, U_w u ^ 2 := by
  obtain ⟨c_W, hc_W, hcomp_gen⟩ := exists_all_ratio_complement_garding_and_far_bridge
  have hI₂ : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  have hg₀ : 0 < dyadicTopMassConstant := dyadicTopMassConstant_pos
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hκ₀ : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
  refine ⟨c_W, hc_W, fun {R_max} hR => ?_⟩
  obtain ⟨B_far, hB_far, hcomp_ev⟩ := hcomp_gen hR
  refine ⟨B_far, hB_far, fun {ε} hε => ?_⟩
  set I₂ := ∫ u, tiltedUnitSpline u ^ 2
  set M_sum := I₂ * B_far + R_max * B_far / c_W + 4 * I₂ * B_far + 1
  have hM_sum : 0 < M_sum := by positivity
  set δ := (ε / 2) / M_sum
  have hδ : 0 < δ := div_pos (half_pos hε) hM_sum
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll_lim : Tendsto (fun N : ℕ => 1 + Real.log (Real.log (N : ℝ))) atTop atTop :=
    (tendsto_atTop_add_const_left _ (1 : ℝ) Real.tendsto_log_atTop).comp hLlim
  filter_upwards [
    hcomp_ev,
    eventually_poleOrthogonal_collar_weilQuad_bridge hR hδ,
    hLlim.eventually (eventually_ge_atTop 3),
    hll_lim.eventually (eventually_ge_atTop (4 * I₂ * B_far / ε + 1)),
    eventually_ge_atTop 3] with N hcompN hpoleN hL3 hll_ge hN3
  intro c hc1 hc8 z hz hz_nonpos
  obtain ⟨w, hw_orth, hgarding, hbridge⟩ := hcompN hc1 hc8 hz
  refine ⟨w, hw_orth, ?_⟩
  set x_w := primeHorizonExtension w
  set M := N / linearDefectCutoff c
  set y_w := atomicTailCoefficients M x_w
  set U_w := normalizedCentredAtomicTest tiltedUnitSpline y_w c N
  set L := Real.log (N : ℝ)
  set ℓ := 1 + Real.log L
  set k₁ := L / (2 * explicitConductorCutoffConstant * ℓ ^ 5)
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL1 : 1 ≤ L := by dsimp only [L] at hL3 ⊢; linarith only [hL3]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hℓ1 : 1 ≤ ℓ := by dsimp only [ℓ]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hk₁_0 : 0 ≤ k₁ := by dsimp only [k₁]; positivity
  have hPw_0 : 0 ≤ (k₁ / 16) * ∑ n ∈ Icc 1 M, x_w n ^ 2 :=
    mul_nonneg (by positivity) (sum_nonneg fun _ _ => sq_nonneg _)
  have hS7_0 : 0 ≤ (dyadicTopMassConstant * L / (64 * c ^ 7)) * topCollarSeventhMass M N x_w :=
    mul_nonneg (by positivity) (topCollarSeventhMass_nonneg M N x_w)
  have hW8_0 : 0 ≤ ∫ u, U_w u ^ 2 * Real.exp (-(8 * u)) := integral_nonneg fun _ => by positivity
  have hU2_0 : 0 ≤ ∫ u, U_w u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hlev_0 : 0 ≤ levyEnergy U_w := levyEnergy_nonneg' U_w
  have hnorm_0 : 0 ≤ (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 := by positivity
  change (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 +
      (k₁ / 16) * (∑ n ∈ Icc 1 M, x_w n ^ 2) +
      (dyadicTopMassConstant * L / (64 * c ^ 7)) * topCollarSeventhMass M N x_w +
      (c * c_W / R_max) * (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) +
      (c / (4 * I₂)) * levyEnergy U_w ≤
    completeWeilEnergy tiltedUnitSpline c N z + (c * B_far) * ∫ u, U_w u ^ 2 at hgarding
  change completeWeilEnergy tiltedUnitSpline c N w ≤
    completeWeilEnergy tiltedUnitSpline c N z +
      (1 / ℓ) * ((k₁ / 8) * (∑ n ∈ Icc 1 M, x_w n ^ 2) +
        (dyadicTopMassConstant * L / (32 * c ^ 7)) * topCollarSeventhMass M N x_w) at hbridge
  have hb_z : (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 ≤ (c * B_far) * ∫ u, U_w u ^ 2 := by
    have h1 : 0 ≤ (c * c_W / R_max) * (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) +
        (c / (4 * I₂)) * levyEnergy U_w := by positivity
    linarith only [hgarding, hz_nonpos, hPw_0, hS7_0, h1]
  have hb_P : (k₁ / 16) * (∑ n ∈ Icc 1 M, x_w n ^ 2) ≤ (c * B_far) * ∫ u, U_w u ^ 2 := by
    have h1 : 0 ≤ (c * c_W / R_max) * (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) +
        (c / (4 * I₂)) * levyEnergy U_w := by positivity
    linarith only [hgarding, hz_nonpos, hnorm_0, hS7_0, h1]
  have hb_PS : (k₁ / 8) * (∑ n ∈ Icc 1 M, x_w n ^ 2) +
      (dyadicTopMassConstant * L / (32 * c ^ 7)) * topCollarSeventhMass M N x_w ≤
      2 * ((c * B_far) * ∫ u, U_w u ^ 2) := by
    have h1 : 0 ≤ (c * c_W / R_max) * (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) +
        (c / (4 * I₂)) * levyEnergy U_w := by positivity
    linarith only [hgarding, hz_nonpos, hnorm_0, h1,
      (by ring : (k₁ / 8) * (∑ n ∈ Icc 1 M, x_w n ^ 2) +
          (dyadicTopMassConstant * L / (32 * c ^ 7)) * topCollarSeventhMass M N x_w =
        2 * ((k₁ / 16) * (∑ n ∈ Icc 1 M, x_w n ^ 2) +
          (dyadicTopMassConstant * L / (64 * c ^ 7)) * topCollarSeventhMass M N x_w))]
  have hb_W8 : (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) ≤
      (R_max * B_far / c_W) * ∫ u, U_w u ^ 2 := by
    have hraw : (c * c_W / R_max) * (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) ≤
        (c * B_far) * ∫ u, U_w u ^ 2 := by
      have h1 : 0 ≤ (c / (4 * I₂)) * levyEnergy U_w := by positivity
      linarith only [hgarding, hz_nonpos, hnorm_0, hPw_0, hS7_0, h1]
    have hm := mul_le_mul_of_nonneg_left hraw (by positivity : 0 ≤ R_max / (c * c_W))
    have hid1 : (R_max / (c * c_W)) * ((c * c_W / R_max) *
        (∫ u, U_w u ^ 2 * Real.exp (-(8 * u)))) = ∫ u, U_w u ^ 2 * Real.exp (-(8 * u)) := by
      field_simp [hc0.ne', hc_W.ne', hR.ne']
    have hid2 : (R_max / (c * c_W)) * ((c * B_far) * ∫ u, U_w u ^ 2) =
        (R_max * B_far / c_W) * ∫ u, U_w u ^ 2 := by
      field_simp [hc0.ne', hc_W.ne']
    linarith only [hm, hid1, hid2]
  have hb_lev : levyEnergy U_w ≤ (4 * I₂ * B_far) * ∫ u, U_w u ^ 2 := by
    have hraw : (c / (4 * I₂)) * levyEnergy U_w ≤ (c * B_far) * ∫ u, U_w u ^ 2 := by
      have h1 : 0 ≤ (c * c_W / R_max) * ∫ u, U_w u ^ 2 * Real.exp (-(8 * u)) := by positivity
      linarith only [hgarding, hz_nonpos, hnorm_0, hPw_0, hS7_0, h1]
    have hm := mul_le_mul_of_nonneg_left hraw (by positivity : 0 ≤ 4 * I₂ / c)
    have hid1 : (4 * I₂ / c) * ((c / (4 * I₂)) * levyEnergy U_w) = levyEnergy U_w := by
      field_simp [hc0.ne', hI₂.ne']
    have hid2 : (4 * I₂ / c) * ((c * B_far) * ∫ u, U_w u ^ 2) =
        (4 * I₂ * B_far) * ∫ u, U_w u ^ 2 := by
      field_simp [hc0.ne']
    linarith only [hm, hid1, hid2]
  have hR₁_1 : 1 ≤ subexpCutoff N := by
    unfold subexpCutoff
    exact Nat.le_floor (by exact_mod_cast Real.one_le_exp (by positivity))
  have hw_orth1 : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw_orth v (conductorSubspace_mono hR₁_1 N hv)
  have hpole_w := hpoleN hc1 hc8 hw_orth1
  change weilQuad U_w -
      δ * ((I₂ / c) * (k₁ / 16) * (∑ n ∈ Icc 1 M, x_w n ^ 2) +
        (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) + levyEnergy U_w + ∫ u, U_w u ^ 2) ≤
    (I₂ / c) * completeWeilEnergy tiltedUnitSpline c N w at hpole_w
  have hEw_ub : (I₂ / c) * completeWeilEnergy tiltedUnitSpline c N w ≤
      (ε / 2) * ∫ u, U_w u ^ 2 := by
    have h1 : completeWeilEnergy tiltedUnitSpline c N w ≤
        (1 / ℓ) * (2 * ((c * B_far) * ∫ u, U_w u ^ 2)) := by
      have hm := mul_le_mul_of_nonneg_left hb_PS (by positivity : 0 ≤ 1 / ℓ)
      linarith only [hbridge, hz_nonpos, hm]
    have hm2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ I₂ / c)
    have hid : (I₂ / c) * ((1 / ℓ) * (2 * ((c * B_far) * ∫ u, U_w u ^ 2))) =
        (2 * I₂ * B_far / ℓ) * ∫ u, U_w u ^ 2 := by
      field_simp [hc0.ne', hℓ0.ne']
    have hrate : 2 * I₂ * B_far / ℓ ≤ ε / 2 := by
      rw [div_le_iff₀ hℓ0]
      have hll' : 4 * I₂ * B_far / ε ≤ ℓ := by dsimp only [ℓ, L]; linarith only [hll_ge]
      have hm3 := (div_le_iff₀ hε).mp hll'
      linarith only [hm3]
    have hm4 := mul_le_mul_of_nonneg_right hrate hU2_0
    linarith only [hm2, hid, hm4]
  have hδ_ub : δ * ((I₂ / c) * (k₁ / 16) * (∑ n ∈ Icc 1 M, x_w n ^ 2) +
      (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) + levyEnergy U_w + ∫ u, U_w u ^ 2) ≤
      (ε / 2) * ∫ u, U_w u ^ 2 := by
    have hb_P' : (I₂ / c) * (k₁ / 16) * (∑ n ∈ Icc 1 M, x_w n ^ 2) ≤
        (I₂ * B_far) * ∫ u, U_w u ^ 2 := by
      rw [mul_assoc]
      have hm := mul_le_mul_of_nonneg_left hb_P (by positivity : 0 ≤ I₂ / c)
      have hid : (I₂ / c) * ((c * B_far) * ∫ u, U_w u ^ 2) = (I₂ * B_far) * ∫ u, U_w u ^ 2 := by
        field_simp [hc0.ne']
      linarith only [hm, hid]
    have hsum : (I₂ / c) * (k₁ / 16) * (∑ n ∈ Icc 1 M, x_w n ^ 2) +
        (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) + levyEnergy U_w + ∫ u, U_w u ^ 2 ≤
        M_sum * ∫ u, U_w u ^ 2 := by
      dsimp only [M_sum]
      linarith only [hb_P', hb_W8, hb_lev]
    refine (mul_le_mul_of_nonneg_left hsum hδ.le).trans_eq ?_
    dsimp only [δ]
    field_simp [hM_sum.ne']
  exact ⟨hb_z, hb_W8, hb_lev, by linarith only [hpole_w, hEw_ub, hδ_ub]⟩

/-- **High-conductor negative directions cannot escape logarithmic windows.**
There exists an explicit constant `C_len ≥ 1` such that for every critical ratio bound `R_max > 0`,
there exist a window half-length `A_R` with `1 ≤ A_R ≤ (1/4) log(R_max + 1) + C_len`, a mass
fraction `c_frac > 0`, and a norm constant `B_conf > 0` for which eventually in `N`, every vector
`z ∈ (conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ` with nonpositive complete Weil energy at
`1 ≤ c`, `c⁸ ≤ R_max log N` has a high-conductor component `w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ`
whose collar profile `U_w` concentrates at least a fraction `c_frac` of `∫ U_w²` and at least
`‖z‖² / (c B_conf)` inside `(-A_R, 1]`. In particular, no nonzero nonpositive direction can vanish
on `(-A_R, 1]`. -/
theorem eventually_negative_direction_window_confinement :
    ∃ C_len : ℝ, 1 ≤ C_len ∧
      ∀ {R_max : ℝ}, 0 < R_max →
        ∃ A_R c_frac B_conf : ℝ,
          1 ≤ A_R ∧ A_R ≤ (1 / 4 : ℝ) * Real.log (R_max + 1) + C_len ∧
          0 < c_frac ∧ 0 < B_conf ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
              ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
                z ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ →
                completeWeilEnergy tiltedUnitSpline c N z ≤ 0 →
                ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
                  w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
                  let U_w := normalizedCentredAtomicTest tiltedUnitSpline
                    (atomicTailCoefficients (N / linearDefectCutoff c) (primeHorizonExtension w))
                    c N
                  c_frac * (∫ u, U_w u ^ 2) ≤ (∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2) ∧
                    ‖z‖ ^ 2 ≤ (c * B_conf) * (∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2) ∧
                    (z ≠ 0 → 0 < ∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2) := by
  obtain ⟨C_B, c_a, c_κ, C_len, hCB, hca, hcκ, hClen, hloc_gen⟩ :=
    exists_window_localized_collar_garding
  obtain ⟨c_W, _hc_W, hbridge_gen⟩ := eventually_complement_collar_weilQuad_bridge
  have hκ₀ : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
  refine ⟨C_len, hClen, fun {R_max} hR => ?_⟩
  obtain ⟨A_R, hAR1, hAR_ub, hloc_ev⟩ := hloc_gen hR
  obtain ⟨B_far, hB_far, hbridge_ev⟩ := hbridge_gen hR
  set ε := c_a * Real.exp (-8) / (4 * R_max)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  set c_frac := c_a * Real.exp (-8) / (4 * C_B * R_max * (R_max + 1))
  have hc_frac : 0 < c_frac := by dsimp only [c_frac]; positivity
  set B_conf := B_far / ((tiltedSplineSpectralFloorConstant + 2) * c_frac)
  have hB_conf : 0 < B_conf := by dsimp only [B_conf]; positivity
  refine ⟨A_R, c_frac, B_conf, hAR1, hAR_ub, hc_frac, hB_conf, ?_⟩
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
  filter_upwards [hloc_ev, hbridge_ev hε, hev_cN, eventually_ge_atTop 3] with
    N hlocN hbridgeN hcN_b hN3
  intro c hc1 hc8 z hz hz_nonpos
  obtain ⟨w, hw_orth, hb_z, _hb_W8, _hb_lev, hb_wq⟩ := hbridgeN hc1 hc8 hz hz_nonpos
  refine ⟨w, hw_orth, ?_⟩
  set x_w := primeHorizonExtension w
  set M := N / linearDefectCutoff c
  set y_w := atomicTailCoefficients M x_w
  set U_w := normalizedCentredAtomicTest tiltedUnitSpline y_w c N
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN : c ≤ N := by
    by_cases hcL : c ≤ (R_max + 1) * Real.log (N : ℝ)
    · exact hcL.trans hcN_b
    · push Not at hcL
      have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      have hc8_gt : (R_max + 1) * Real.log (N : ℝ) < c ^ 8 :=
        hcL.trans_le (le_self_pow₀ hc1 (by norm_num))
      linarith
  obtain ⟨hUw_cd, hUw_cs, hUw_w, _, _, _⟩ := normalizedCentredAtomicTest_scaling hc0 hN1 y_w
  have hw1 : c / (N : ℝ) ≤ 1 := (div_le_one hN0).mpr hcN
  have hUw_le1 : ∀ u, 1 < u → U_w u = 0 := fun u hu => hUw_w u (hw1.trans_lt hu)
  have hUw2_cs : HasCompactSupport (fun u => U_w u ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hUw_cs ⊢
    exact hUw_cs.mono fun u hu => by change U_w u = 0 at hu; change U_w u ^ 2 = 0; rw [hu]; ring
  have hi_u2 : Integrable fun u => U_w u ^ 2 :=
    (hUw_cd.continuous.pow 2).integrable_of_hasCompactSupport hUw2_cs
  have hi_w8 : Integrable fun u => U_w u ^ 2 * Real.exp (-(8 * u)) :=
    ((hUw_cd.continuous.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hUw2_cs.mul_right
  have hexp8_le : Real.exp (-8) * (∫ u, U_w u ^ 2) ≤ ∫ u, U_w u ^ 2 * Real.exp (-(8 * u)) := by
    rw [← integral_const_mul]
    refine integral_mono (hi_u2.const_mul _) hi_w8 fun u => ?_
    by_cases hu : u ≤ 1
    · calc Real.exp (-8) * U_w u ^ 2
          = U_w u ^ 2 * Real.exp (-8) := mul_comm _ _
        _ ≤ U_w u ^ 2 * Real.exp (-(8 * u)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hu])) (sq_nonneg _)
    · push Not at hu
      rw [hUw_le1 u hu]; norm_num
  have hloc_w := hlocN hc1 hc8 x_w
  dsimp only at hloc_w
  change (c_κ / R_max) * topCollarSeventhMass M N x_w +
      (c_a / (2 * R_max)) * (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) ≤
    weilQuad U_w + (C_B * (R_max + 1)) * ∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2 at hloc_w
  have hS7_0 : 0 ≤ (c_κ / R_max) * topCollarSeventhMass M N x_w :=
    mul_nonneg (by positivity) (topCollarSeventhMass_nonneg M N x_w)
  have hm_w8 := mul_le_mul_of_nonneg_left hexp8_le (by positivity : 0 ≤ c_a / (2 * R_max))
  have hid_ε : (c_a / (2 * R_max)) * (Real.exp (-8) * ∫ u, U_w u ^ 2) - ε * ∫ u, U_w u ^ 2 =
      (c_a * Real.exp (-8) / (4 * R_max)) * ∫ u, U_w u ^ 2 := by
    dsimp only [ε]; field_simp [hR.ne']; ring
  have hraw_win : (c_a * Real.exp (-8) / (4 * R_max)) * (∫ u, U_w u ^ 2) ≤
      (C_B * (R_max + 1)) * ∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2 := by
    linarith only [hloc_w, hS7_0, hm_w8, hb_wq, hid_ε]
  have hfrac : c_frac * (∫ u, U_w u ^ 2) ≤ ∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hraw_win (by positivity : 0 ≤ 1 / (C_B * (R_max + 1)))
    have hid1 : (1 / (C_B * (R_max + 1))) *
        ((c_a * Real.exp (-8) / (4 * R_max)) * ∫ u, U_w u ^ 2) =
        c_frac * ∫ u, U_w u ^ 2 := by
      dsimp only [c_frac]; field_simp [hCB.ne', hR.ne', (by positivity : 0 < R_max + 1).ne']
    have hid2 : (1 / (C_B * (R_max + 1))) *
        ((C_B * (R_max + 1)) * ∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2) =
        ∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2 := by
      field_simp [hCB.ne', (by positivity : 0 < R_max + 1).ne']
    linarith only [hm, hid1, hid2]
  have hnorm_win : ‖z‖ ^ 2 ≤ (c * B_conf) * ∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2 := by
    have hm1 := mul_le_mul_of_nonneg_left hb_z
      (by positivity : 0 ≤ 1 / (tiltedSplineSpectralFloorConstant + 2))
    have hid1 : (1 / (tiltedSplineSpectralFloorConstant + 2)) *
        ((tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2) = ‖z‖ ^ 2 := by
      field_simp [(by positivity : 0 < tiltedSplineSpectralFloorConstant + 2).ne']
    have hm2 := mul_le_mul_of_nonneg_left hfrac
      (by positivity : 0 ≤ c * B_far / ((tiltedSplineSpectralFloorConstant + 2) * c_frac))
    have hid2 : (c * B_far / ((tiltedSplineSpectralFloorConstant + 2) * c_frac)) *
        (c_frac * ∫ u, U_w u ^ 2) =
        (1 / (tiltedSplineSpectralFloorConstant + 2)) * ((c * B_far) * ∫ u, U_w u ^ 2) := by
      field_simp [(by positivity : 0 < tiltedSplineSpectralFloorConstant + 2).ne', hc_frac.ne']
    have hid3 : (c * B_far / ((tiltedSplineSpectralFloorConstant + 2) * c_frac)) *
        (∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2) =
        (c * B_conf) * ∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2 := by
      dsimp only [B_conf]
      field_simp [(by positivity : 0 < tiltedSplineSpectralFloorConstant + 2).ne', hc_frac.ne']
    linarith only [hm1, hid1, hm2, hid2, hid3]
  refine ⟨hfrac, hnorm_win, fun hzne => ?_⟩
  have hpos_z : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzne)
  by_contra hle0
  push Not at hle0
  have hle_rhs : (c * B_conf) * (∫ u in Set.Ioc (-A_R) 1, U_w u ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hle0
  linarith only [hpos_z, hnorm_win, hle_rhs]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
