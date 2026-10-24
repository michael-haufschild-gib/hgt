import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSelectivityBatteryOfOrientation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface
import GaloisForLFunctions.HTGeometry.PowerSumTuranLowerBound

/-!
# Quantitative readings on curve orbits

The self-upgrade of orientation is qualitative: a seen deep zero eventually makes the orbit
correlation leave the Hasse–Weil envelope, at an unspecified scale. Over `𝔽_q` the scale and the
size of the violation are explicit, with a precision cost exponential only in the genus.

* **The tower reads the Frobenius traces** (`curve_orbitCorr_tower`). For a real test supported in
  an interval shorter than `log q`, the orbit correlation at the scale `ν log q` is
  `log q · ‖f‖² · Σ_i Re β_i^ν`: the orbit along the `q`-tower is the Frobenius span
  (`W_curveConfig_translate_narrow`).
* **Turán's reading** (`exists_orbitCorr_ge_turan`). If some eigenvalue has `|β_i| ≥ Z₀ > 0`, every
  window `M + 1 ≤ ν ≤ M + 2g` contains a scale with
  `|c_f(ν log q)| ≥ log q · ‖f‖² · Z₀^ν / C(2g, M)`, `C(N, M) = 2eN(6(N + 1)(M + 2N + 2))^N`
  (Turán's second main theorem, `HTGeometry.exists_norm_powerSum_ge_scaled`). No separation of the
  eigenvalues is needed.
* **An explicit violating scale** (`exists_not_hasseWeilAt_window`). If `Z₀ ≥ 1` and
  `2g · C(2g, M) < Z₀^{M+1}`, the Hasse–Weil bound fails at a scale `ν log q`, `M < ν ≤ M + 2g`, for
  every nonzero narrow test.
* **Violations recur in every late window** (`eventually_exists_not_hasseWeilAt`). For an impure
  curve (`|β_i| > 1` for some `i`) every window of `2g` consecutive tower scales beyond some point
  contains a violation; for the golden datum every pair of consecutive powers of `5` does
  (`golden_eventually_exists_not_hasseWeilAt`).

The cost is governed by the number `2g` of eigenvalues, the number of terms of the exponential sum.
-/

noncomputable section

open Finset Filter Topology
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

/-- Turán's constant `C(N, M) = 2eN(6(N + 1)(M + 2N + 2))^N`. -/
def turanConstant (N M : ℕ) : ℝ :=
  2 * (Real.exp 1 * N * (6 * (N + 1) * ((M : ℝ) + 2 * N + 2)) ^ N)

theorem turanConstant_pos {N : ℕ} (hN : 1 ≤ N) (M : ℕ) : 0 < turanConstant N M := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold turanConstant
  positivity

section Curve

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- **The orbit along the `q`-tower reads the Frobenius traces.** For a real test supported in an
interval shorter than `log q`, `c_f(ν log q) = log q · ‖f‖² · Re Σ_i β_i^ν`. -/
theorem curve_orbitCorr_tower {x : ScalingCycle} {A : ℝ}
    (hs : tsupport (cx x.2.2) ⊆ Set.Icc (-(A / 2)) (A / 2)) (hA : A < Real.log D.q) (ν : ℕ) :
    (configScalingDatum (D.curveConfig hD) (D.temperedConfig_curveConfig hD)).orbitCorr x
        (ν * Real.log D.q) = (Real.log D.q * ∫ u, ‖cx x.2.2 u‖ ^ 2) * D.trace ν := by
  rw [configScalingDatum_orbitCorr_eq, tsum_exp_Wsummand_eq_W]
  have h := D.W_curveConfig_translate_narrow hD (cx_contDiff x.2.2.2.1) hs hA ν 0
  have h0 : ArithmeticCastelnuovoSeveri.translate (((0 : ℕ) : ℝ) * Real.log D.q) (cx x.2.2) =
      cx x.2.2 := by
    funext u
    simp [ArithmeticCastelnuovoSeveri.translate]
  rw [h0, Nat.dist_zero_right] at h
  have hc : cx (scaleShift (ν * Real.log D.q) x.2.2) =
      ArithmeticCastelnuovoSeveri.translate ((ν : ℝ) * Real.log D.q) (cx x.2.2) := rfl
  rw [hc, h, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Turán's reading over `𝔽_q`.** If some eigenvalue has `|β_i| ≥ Z₀ > 0`, then every window
`[M + 1, M + 2g]` of the tower contains a scale `ν` with
`|c_f(ν log q)| ≥ log q · ‖f‖² · Z₀^ν / C(2g, M)`. -/
theorem exists_orbitCorr_ge_turan {x : ScalingCycle} {A : ℝ}
    (hs : tsupport (cx x.2.2) ⊆ Set.Icc (-(A / 2)) (A / 2)) (hA : A < Real.log D.q) {Z₀ : ℝ}
    (hZ : 0 < Z₀) (htop : ∃ i, Z₀ ≤ ‖D.β i‖) (M : ℕ) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + Fintype.card ι ∧
      (Real.log D.q * ∫ u, ‖cx x.2.2 u‖ ^ 2) * (Z₀ ^ ν / turanConstant (Fintype.card ι) M) ≤
        |(configScalingDatum _ (D.temperedConfig_curveConfig hD)).orbitCorr x
          (ν * Real.log D.q)| := by
  obtain ⟨i, hi⟩ := htop
  obtain ⟨ν, h1, h2, h3⟩ := GaloisForLFunctions.HTGeometry.exists_norm_powerSum_ge_scaled
    Finset.univ D.β hZ ⟨i, Finset.mem_univ _, hi⟩ M
  rw [Finset.card_univ] at h2 h3
  refine ⟨ν, h1, h2, ?_⟩
  have hc : 0 ≤ Real.log D.q * ∫ u, ‖cx x.2.2 u‖ ^ 2 :=
    mul_nonneg D.log_q_pos.le (MeasureTheory.integral_nonneg fun _ => sq_nonneg _)
  rw [curve_orbitCorr_tower D hD hs hA ν, abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have hps : ‖∑ i, D.β i ^ ν‖ = |D.trace ν| := by
    rw [show ∑ i, D.β i ^ ν = D.powerSum ν from rfl, D.powerSum_eq_trace, Complex.norm_real,
      Real.norm_eq_abs]
  rw [← hps]
  exact h3

/-- The energy of a narrow test: `c_f(0) = log q · ‖f‖² · 2g`. -/
theorem curve_orbitCorr_zero {x : ScalingCycle} {A : ℝ}
    (hs : tsupport (cx x.2.2) ⊆ Set.Icc (-(A / 2)) (A / 2)) (hA : A < Real.log D.q) :
    (configScalingDatum (D.curveConfig hD) (D.temperedConfig_curveConfig hD)).orbitCorr x 0 =
      (Real.log D.q * ∫ u, ‖cx x.2.2 u‖ ^ 2) * Fintype.card ι := by
  have h := curve_orbitCorr_tower D hD hs hA 0
  rwa [Nat.cast_zero, zero_mul, D.trace_zero] at h

/-- **An explicit violating scale.** If `|β_i| ≥ Z₀ ≥ 1` for some `i` and
`2g · C(2g, M) < Z₀^{M+1}`, the Hasse–Weil bound fails, for every nonzero narrow test, at some scale
`ν log q` with `M + 1 ≤ ν ≤ M + 2g`. -/
theorem exists_not_hasseWeilAt_window {x : ScalingCycle} {A : ℝ}
    (hs : tsupport (cx x.2.2) ⊆ Set.Icc (-(A / 2)) (A / 2)) (hA : A < Real.log D.q)
    (hf0 : 0 < ∫ u, ‖cx x.2.2 u‖ ^ 2) {Z₀ : ℝ} (hZ : 1 ≤ Z₀) (htop : ∃ i, Z₀ ≤ ‖D.β i‖) {M : ℕ}
    (hM : (Fintype.card ι : ℝ) * turanConstant (Fintype.card ι) M < Z₀ ^ (M + 1)) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + Fintype.card ι ∧
      ¬ (configScalingDatum _ (D.temperedConfig_curveConfig hD)).HasseWeilAt x
        (ν * Real.log D.q) := by
  obtain ⟨i, hi⟩ := htop
  have hN : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨ν, h1, h2, h3⟩ := exists_orbitCorr_ge_turan D hD hs hA (by linarith) ⟨i, hi⟩ M
  refine ⟨ν, h1, h2, fun hHW => ?_⟩
  have hc : 0 < Real.log D.q * ∫ u, ‖cx x.2.2 u‖ ^ 2 := mul_pos D.log_q_pos hf0
  have hT := turanConstant_pos hN M
  have hle : (Real.log D.q * ∫ u, ‖cx x.2.2 u‖ ^ 2) * (Z₀ ^ ν / turanConstant (Fintype.card ι) M) ≤
      (Real.log D.q * ∫ u, ‖cx x.2.2 u‖ ^ 2) * Fintype.card ι := by
    have := h3.trans hHW
    rwa [curve_orbitCorr_zero D hD hs hA] at this
  have h4 : Z₀ ^ ν / turanConstant (Fintype.card ι) M ≤ Fintype.card ι :=
    le_of_mul_le_mul_left hle hc
  rw [div_le_iff₀ hT] at h4
  have h5 : Z₀ ^ (M + 1) ≤ Z₀ ^ ν := pow_le_pow_right₀ hZ h1
  linarith

/-- **Violations recur in every late window.** If some eigenvalue lies outside the unit circle,
then for every nonzero narrow test, every window of `2g` consecutive tower scales beyond some point
contains a scale at which the Hasse–Weil bound fails. -/
theorem eventually_exists_not_hasseWeilAt {x : ScalingCycle} {A : ℝ}
    (hs : tsupport (cx x.2.2) ⊆ Set.Icc (-(A / 2)) (A / 2)) (hA : A < Real.log D.q)
    (hf0 : 0 < ∫ u, ‖cx x.2.2 u‖ ^ 2) {Z₀ : ℝ} (hZ : 1 < Z₀) (htop : ∃ i, Z₀ ≤ ‖D.β i‖) :
    ∀ᶠ M in atTop, ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + Fintype.card ι ∧
      ¬ (configScalingDatum _ (D.temperedConfig_curveConfig hD)).HasseWeilAt x
        (ν * Real.log D.q) := by
  set N := Fintype.card ι with hNdef
  set c : ℕ := 2 * N + 2 with hc
  set K : ℝ := 2 * (Real.exp 1 * N * (6 * (N + 1))) ^ N with hK
  have hZ0 : 0 < Z₀ := by linarith
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hNK : 0 ≤ (N : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK0
  -- `C(N, M) = K (M + c)^N`
  have hT : ∀ M : ℕ, turanConstant N M = K * (((M + c : ℕ) : ℝ)) ^ N := fun M => by
    have e1 : turanConstant N M =
        2 * ((Real.exp 1 * N * (6 * (N + 1))) * (((M + c : ℕ) : ℝ))) ^ N := by
      unfold turanConstant
      congr 2
      rw [hc]; push_cast; ring
    rw [e1, mul_pow, hK]
    ring
  -- `(M + c)^N / Z₀^{M+c} → 0`
  have hlim : Tendsto (fun M : ℕ => (((M + c : ℕ) : ℝ)) ^ N / Z₀ ^ (M + c)) atTop (𝓝 0) :=
    (tendsto_pow_const_div_const_pow_of_one_lt N hZ).comp (tendsto_add_atTop_nat c)
  have hden : 0 < Z₀ ^ c * ((N : ℝ) * K + 1) := mul_pos (pow_pos hZ0 c) (by linarith)
  have hpos : 0 < Z₀ ^ (1 : ℕ) / (Z₀ ^ c * ((N : ℝ) * K + 1)) := div_pos (pow_pos hZ0 1) hden
  filter_upwards [(tendsto_order.1 hlim).2 _ hpos] with M hM
  refine exists_not_hasseWeilAt_window D hD hs hA hf0 hZ.le htop ?_
  have hZc : 0 < Z₀ ^ (M + c) := pow_pos hZ0 _
  rw [div_lt_div_iff₀ hZc hden] at hM
  have hZc' : 0 < Z₀ ^ c := pow_pos hZ0 _
  have hP : 0 ≤ (((M + c : ℕ) : ℝ)) ^ N := by positivity
  -- divide `P · Z₀^c (NK + 1) < Z₀ · Z₀^M Z₀^c` by `Z₀^c`
  have key : (((M + c : ℕ) : ℝ)) ^ N * ((N : ℝ) * K + 1) < Z₀ ^ M * Z₀ ^ 1 := by
    refine lt_of_mul_lt_mul_right ?_ hZc'.le
    calc (((M + c : ℕ) : ℝ)) ^ N * ((N : ℝ) * K + 1) * Z₀ ^ c
        = (((M + c : ℕ) : ℝ)) ^ N * (Z₀ ^ c * ((N : ℝ) * K + 1)) := by ring
      _ < Z₀ ^ (1 : ℕ) * Z₀ ^ (M + c) := hM
      _ = Z₀ ^ M * Z₀ ^ 1 * Z₀ ^ c := by rw [pow_add]; ring
  rw [hT M, pow_add]
  nlinarith [mul_nonneg hNK hP]

end Curve

/-- **The golden datum violates the bound in every late pair of consecutive powers of `5`.** -/
theorem golden_eventually_exists_not_hasseWeilAt {x : ScalingCycle} {A : ℝ}
    (hs : tsupport (cx x.2.2) ⊆ Set.Icc (-(A / 2)) (A / 2)) (hA : A < Real.log goldenDatum.q)
    (hf0 : 0 < ∫ u, ‖cx x.2.2 u‖ ^ 2) :
    ∀ᶠ M in atTop, ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + 2 ∧
      ¬ (configScalingDatum goldenConfig temperedConfig_goldenConfig).HasseWeilAt x
        (ν * Real.log goldenDatum.q) := by
  have hφ : Real.goldenRatio ≤ ‖goldenDatum.β 0‖ := by
    show Real.goldenRatio ≤ ‖((Real.goldenRatio : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg Real.goldenRatio_pos.le]
  have h := eventually_exists_not_hasseWeilAt goldenDatum goldenDatum_strip hs hA hf0
    Real.one_lt_goldenRatio ⟨0, hφ⟩
  simpa using h

end GaloisForLFunctions.ArithmeticOrientationGeometry
