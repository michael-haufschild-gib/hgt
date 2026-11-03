import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRescaledLimitOfACurveIsTheHurwitzFormOfItsAngles
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFirstNegativeLagOfACurve
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity

/-!
# Degeneration selects the pure curves

Over `ℤ` complete degeneration selects `ζ`: its limiting structure tends to zero with a polarized
rescaled limit, while a prime flip leaves an indefinite residue (ADT `primeFlip_degenerates_indefinitely`).
This file is the `𝔽_q` calibration of that selection, along the dilation of the atoms of a curve
(width `w`, overlap `a = w/log q`).

* **A pure curve degenerates completely** (`tendsto_W_curveLatticeTest_pure`): if `|β_i| = 1` and
  `β_i ≠ 1`, Weil's form of every lattice test tends to `0` as `w → ∞`. By the density form
  `W = w² Σ_i |Σ_k x_k β_i^k|² (D_{u_i} + D_{1−u_i})(w/log q)` and the decay
  `D_u(s) ≤ C (2πsu)^{−4}` of the shifted densities of a `C²` profile.
* **One atom on any curve** (`W_curveConfig_atom`): `W(g_w, g_w) = log q Σ_m w G(m log q/w) t_{|m|}`,
  a finite sum over the lags `|m| < w/log q`; with a nonnegative profile and nonnegative traces each
  lag is a lower bound (`le_curveAtomEnergy`).
* **The golden fake explodes** (`goldenDatum_curveAtomEnergy_ge`, `tendsto_goldenDatum_W_div_pow`):
  for `β = φ, φ⁻¹` over `𝔽₅` (traces the Lucas numbers), `W(g_w, g_w) ≥ c w e^{εw}`, so
  `W/w^k → ∞` for every `k`: the family has exponential monodromy and no rescaled limit at any
  polynomial rate.

So the type of degeneration separates the curve from the fake: polynomial (here complete) for
the pure curve, as Borel's monodromy theorem demands of a geometric family, exponential for the
fake, whose outer eigenvalue `φ` is the growth rate of the monodromy.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) {φ : ℝ → ℝ}

/-! ### Complete degeneration of a pure curve -/

/-- A `C²` profile on `[0, 1]` has `|φ̂(ξ)|² ≤ C (1 + |ξ|)^{−4}`. -/
theorem exists_paperFT_decay_four (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ C * (1 + |u|) ^ (-(4 : ℝ)) := by
  have hc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨N, -, hb⟩ := _root_.RHTower.exists_normSq_paperFT_le hφ hc
  refine ⟨N ^ 2, sq_nonneg _, fun u => ?_⟩
  have h1 : (0 : ℝ) < 1 + |u| := by positivity
  rw [Real.rpow_neg h1.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ‖paperFT (cx φ) u‖ ^ 2 ≤ N ^ 2 / ((1 + |u|) ^ 2) ^ 2 := hb u
    _ = N ^ 2 * ((1 + |u|) ^ 4)⁻¹ := by rw [div_eq_mul_inv, ← pow_mul]

/-- The shifted density decays like `s^{−4}`: `D_u(s) ≤ C (2πsu)^{−4} Σ_n (n + 1)^{−4}`. -/
theorem twistDensity_le_rpow {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ C * (1 + |u|) ^ (-(4 : ℝ)))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {s : ℝ} (hs : 0 < s) :
    twistDensity φ u s ≤
      C * (2 * Real.pi * (s * u)) ^ (-(4 : ℝ)) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(4 : ℝ)) := by
  have hsb : Summable fun n : ℕ =>
      C * (2 * Real.pi * (s * u)) ^ (-(4 : ℝ)) * ((n : ℝ) + 1) ^ (-(4 : ℝ)) :=
    (summable_succ_rpow (by norm_num)).mul_left _
  have hbd : ∀ n : ℕ, shellSpectrum φ (s * ((n : ℝ) + u)) ≤
      C * (2 * Real.pi * (s * u)) ^ (-(4 : ℝ)) * ((n : ℝ) + 1) ^ (-(4 : ℝ)) :=
    fun n => shellSpectrum_shift_le (by norm_num) hC hdecay hu0 hu1 hs le_rfl n
  unfold twistDensity
  rw [← tsum_mul_left]
  exact (hsb.of_nonneg_of_le (fun n => shellSpectrum_nonneg _) hbd).tsum_le_tsum hbd hsb

/-- `w² D_u(w/L) → 0`: the shifted densities vanish faster than the atom energy grows. -/
theorem tendsto_sq_mul_twistDensity (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {L : ℝ}
    (hL : 0 < L) :
    Tendsto (fun w => w ^ 2 * twistDensity φ u (w / L)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hdecay⟩ := exists_paperFT_decay_four hφ hφsupp
  set Z := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(4 : ℝ)) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  set c₀ := 2 * Real.pi * u / L with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  have hup : ∀ w : ℝ, 0 < w →
      w ^ 2 * twistDensity φ u (w / L) ≤ C * c₀ ^ (-(4 : ℝ)) * Z * w ^ (-(2 : ℝ)) := by
    intro w hw
    have h := twistDensity_le_rpow hC hdecay hu0 hu1 (div_pos hw hL)
    have e : 2 * Real.pi * (w / L * u) = c₀ * w := by rw [hc₀def]; field_simp
    rw [e, Real.mul_rpow hc₀.le hw.le] at h
    have hw2 : w ^ 2 * w ^ (-(4 : ℝ)) = w ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hw]; norm_num
    calc w ^ 2 * twistDensity φ u (w / L) ≤
          w ^ 2 * (C * (c₀ ^ (-(4 : ℝ)) * w ^ (-(4 : ℝ))) * Z) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = C * c₀ ^ (-(4 : ℝ)) * Z * (w ^ 2 * w ^ (-(4 : ℝ))) := by ring
      _ = _ := by rw [hw2]
  have hlim : Tendsto (fun w : ℝ => C * c₀ ^ (-(4 : ℝ)) * Z * w ^ (-(2 : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul
      (C * c₀ ^ (-(4 : ℝ)) * Z)
    rwa [mul_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards with w
    exact mul_nonneg (sq_nonneg _) (tsum_nonneg fun n => shellSpectrum_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with w hw
    exact hup w hw

/-- **A pure curve degenerates completely.** For a pure curve without the eigenvalue `1`, Weil's
form of every lattice test tends to `0` as the atoms widen. -/
theorem tendsto_W_curveLatticeTest_pure (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) (hpure : ∀ i, ‖D.β i‖ = 1)
    (hne : ∀ i, D.β i ≠ 1) (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (n : ℕ) (x : ℕ → ℝ) :
    Tendsto (fun w => (D.curveConfig hD).W (curveLatticeTest D φ w n x)
      (curveLatticeTest D φ w n x)) atTop (𝓝 0) := by
  have hL : 0 < Real.log D.q := D.log_q_pos
  have hterm : ∀ i, Tendsto (fun w : ℝ => w ^ 2 * (‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2 *
      (twistDensity φ (frobeniusShift (D.β i)) (w / Real.log D.q) +
        twistDensity φ (1 - frobeniusShift (D.β i)) (w / Real.log D.q)))) atTop (𝓝 0) := by
    intro i
    obtain ⟨h0, h1⟩ := frobeniusShift_mem (hpure i) (hne i)
    have t1 := tendsto_sq_mul_twistDensity hφ hφsupp h0 h1.le hL
    have t2 := tendsto_sq_mul_twistDensity hφ hφsupp
      (by linarith : 0 < 1 - frobeniusShift (D.β i))
      (by linarith : 1 - frobeniusShift (D.β i) ≤ 1) hL
    have := (t1.add t2).const_mul (‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2)
    rw [add_zero, mul_zero] at this
    refine this.congr' (Eventually.of_forall fun w => ?_)
    ring
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => hterm i)
  simp only [Finset.sum_const_zero] at hsum
  have hreal : Tendsto (fun w : ℝ => w ^ 2 * ∑ i, ‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2 *
      (twistDensity φ (frobeniusShift (D.β i)) (w / Real.log D.q) +
        twistDensity φ (1 - frobeniusShift (D.β i)) (w / Real.log D.q))) atTop (𝓝 0) := by
    refine hsum.congr' (Eventually.of_forall fun w => ?_)
    exact (Finset.mul_sum _ _ _).symm
  have hc := (Complex.continuous_ofReal.tendsto 0).comp hreal
  rw [Complex.ofReal_zero] at hc
  refine hc.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with w hw
  exact (W_curveLatticeTest_eq_density D hD hpure hφ hφsupp hw n x).symm

/-! ### One atom on any curve -/

/-- The energy of one atom of width `w`: `log q Σ_m w G(m log q/w) t_{|m|}`. -/
def curveAtomEnergy (φ : ℝ → ℝ) (w : ℝ) : ℝ :=
  Real.log D.q * ∑' m : ℤ, w * shellAutocorr φ (m * Real.log D.q / w) * D.trace m.natAbs

/-- **Weil's form of one atom on a curve** (any datum, pure or not). -/
theorem W_curveConfig_atom (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ} (hw : 0 < w) :
    (D.curveConfig hD).W (cx (atomDilate φ w)) (cx (atomDilate φ w)) =
      (curveAtomEnergy D φ w : ℂ) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hg2 : ContDiff ℝ 2 (cx (atomDilate φ w)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp (contDiff_id.div_const w))
  have hgc : HasCompactSupport (cx (atomDilate φ w)) :=
    (hasCompactSupport_atomDilate hw.ne' hφc).comp_left Complex.ofReal_zero
  rw [D.W_curveConfig_lagFormula hD hg2 hgc, curveAtomEnergy, Complex.ofReal_mul,
    Complex.ofReal_tsum]
  congr 1
  refine tsum_congr fun m => ?_
  rw [weilTest_atom hw]
  push_cast
  ring

/-- Only the lags `|m| < w/log q` contribute. -/
theorem summable_curveAtom (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {w : ℝ} (hw : 0 < w) :
    Summable fun m : ℤ => w * shellAutocorr φ (m * Real.log D.q / w) * D.trace m.natAbs := by
  have hL : 0 < Real.log D.q := D.log_q_pos
  set K : ℕ := ⌈w / Real.log D.q⌉₊ with hK
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) K) fun m hm => ?_
  have hKw : w / Real.log D.q ≤ K := Nat.le_ceil _
  have hmK : (K : ℝ) < |(m : ℝ)| := by
    rw [Finset.mem_Icc, not_and_or] at hm
    rcases hm with h | h
    · push Not at h
      have : (m : ℝ) < -K := by exact_mod_cast h
      rw [abs_of_neg (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])]; linarith
    · push Not at h
      have : (K : ℝ) < m := by exact_mod_cast h
      rw [abs_of_pos (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])]; linarith
  rw [shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp, mul_zero, zero_mul]
  rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos hw, le_div_iff₀ hw, one_mul]
  have := (div_le_iff₀ hL).mp (hKw.trans hmK.le)
  linarith

/-- With a nonnegative profile and nonnegative traces every lag bounds the atom energy below. -/
theorem le_curveAtomEnergy (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : ∀ u, 0 ≤ φ u) (htr : ∀ m, 0 ≤ D.trace m) {w : ℝ} (hw : 0 < w) (m : ℕ) :
    Real.log D.q * (w * shellAutocorr φ (m * Real.log D.q / w) * D.trace m) ≤
      curveAtomEnergy D φ w := by
  unfold curveAtomEnergy
  refine mul_le_mul_of_nonneg_left ?_ D.log_q_pos.le
  have hG : ∀ t, 0 ≤ shellAutocorr φ t := fun t =>
    integral_nonneg fun u => mul_nonneg (hφ0 _) (hφ0 _)
  have h := (summable_curveAtom D hφ hφsupp hw).le_tsum (m : ℤ)
    fun j _ => mul_nonneg (mul_nonneg hw.le (hG _)) (htr _)
  simpa using h

/-! ### The golden fake -/

open Real in
/-- **The golden fake explodes**: for a nonnegative nonzero profile there are `c, ε > 0` with
`W(g_w, g_w) ≥ c w e^{εw}` for every width `w > 0`. -/
theorem goldenDatum_curveAtomEnergy_ge (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : ∀ u, 0 ≤ φ u) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ w : ℝ, 0 < w →
      c * w * Real.exp (ε * w) ≤ curveAtomEnergy goldenDatum φ w := by
  set L := Real.log goldenDatum.q with hLdef
  have hL : 0 < L := goldenDatum.log_q_pos
  set M := ∫ u, φ u ^ 2 with hMdef
  -- `G > M/2` near the origin
  have hG := (continuous_shellAutocorr hφ hφsupp).tendsto 0
  rw [shellAutocorr_zero] at hG
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), M / 2 < shellAutocorr φ t :=
    hG.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hg1 : 1 < goldenRatio := one_lt_goldenRatio
  have hg0 : 0 < goldenRatio := goldenRatio_pos
  have hlg : 0 < Real.log goldenRatio := Real.log_pos hg1
  refine ⟨L * (M / 2) / goldenRatio, δ / 2 / L * Real.log goldenRatio, by positivity,
    by positivity, fun w hw => ?_⟩
  set m : ℕ := ⌊δ / 2 * w / L⌋₊ with hm
  have hm0 : 0 ≤ δ / 2 * w / L := by positivity
  have hmle : (m : ℝ) ≤ δ / 2 * w / L := Nat.floor_le hm0
  have hmgt : δ / 2 * w / L - 1 < m := by have := Nat.lt_floor_add_one (δ / 2 * w / L); linarith
  -- the lag `m` sits where `G > M/2`
  have hGm : M / 2 < shellAutocorr φ (m * L / w) := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hw]
    have := (le_div_iff₀ hL).mp hmle
    nlinarith
  -- the trace `t_m = φ^m + φ^{−m} ≥ φ^m ≥ e^{(m+1) log φ}/φ`
  have htr : ∀ j, 0 ≤ goldenDatum.trace j := fun j => by
    rw [goldenDatum_trace]; positivity
  have htm : Real.exp (δ / 2 / L * Real.log goldenRatio * w) / goldenRatio ≤ goldenDatum.trace m := by
    rw [goldenDatum_trace]
    have h1 : Real.exp (δ / 2 / L * Real.log goldenRatio * w) / goldenRatio ≤ goldenRatio ^ m := by
      rw [div_le_iff₀ hg0, ← pow_succ, ← Real.rpow_natCast, Real.rpow_def_of_pos hg0]
      refine Real.exp_le_exp.mpr ?_
      have : δ / 2 / L * w ≤ ((m + 1 : ℕ) : ℝ) := by
        push_cast
        have : δ / 2 / L * w = δ / 2 * w / L := by ring
        linarith
      nlinarith
    have h2 : 0 ≤ (goldenRatio⁻¹) ^ m := by positivity
    linarith
  have hle := le_curveAtomEnergy goldenDatum hφ hφsupp hφ0 htr hw m
  rw [← hLdef] at hle
  have hpos : 0 < Real.exp (δ / 2 / L * Real.log goldenRatio * w) / goldenRatio := by positivity
  calc L * (M / 2) / goldenRatio * w * Real.exp (δ / 2 / L * Real.log goldenRatio * w)
      = L * (w * (M / 2) * (Real.exp (δ / 2 / L * Real.log goldenRatio * w) / goldenRatio)) := by
        ring
    _ ≤ L * (w * shellAutocorr φ (m * L / w) * goldenDatum.trace m) := by
        refine mul_le_mul_of_nonneg_left ?_ hL.le
        refine mul_le_mul (mul_le_mul_of_nonneg_left hGm.le hw.le) htm hpos.le ?_
        exact mul_nonneg hw.le (by linarith)
    _ ≤ _ := hle

/-- **No rescaled limit at any polynomial rate**: for the golden fake, `W(g_w, g_w)/w^k → ∞` for
every `k`. -/
theorem tendsto_goldenDatum_W_div_pow (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : ∀ u, 0 ≤ φ u) (hM : 0 < ∫ u, φ u ^ 2)
    (k : ℝ) :
    Tendsto (fun w => ((goldenDatum.curveConfig goldenDatum_strip).W (cx (atomDilate φ w))
      (cx (atomDilate φ w))).re / w ^ k) atTop atTop := by
  obtain ⟨c, ε, hc, hε, hge⟩ := goldenDatum_curveAtomEnergy_ge hφ hφsupp hφ0 hM
  have hlim : Tendsto (fun w : ℝ => c * (Real.exp (ε * w) / w ^ (k - 1))) atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop (k - 1) ε hε).const_mul_atTop hc
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with w hw
  rw [W_curveConfig_atom goldenDatum goldenDatum_strip hφ hφsupp hw, Complex.ofReal_re]
  have hwk : 0 < w ^ k := Real.rpow_pos_of_pos hw k
  have e : c * (Real.exp (ε * w) / w ^ (k - 1)) = c * w * Real.exp (ε * w) / w ^ k := by
    rw [Real.rpow_sub hw, Real.rpow_one]
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right (hge w hw) hwk.le

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
