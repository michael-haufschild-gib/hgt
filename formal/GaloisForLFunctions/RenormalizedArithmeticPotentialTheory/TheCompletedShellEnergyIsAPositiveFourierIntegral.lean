import GaloisForLFunctions.BiScaleUncertainty.PairingRecurrenceLaw
import GaloisForLFunctions.RHTower.ZeroLatticeDepthNyquistLaw
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilTrialEnergiesAreSimpleAndProper
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The completed shell energy is a positive Fourier integral

Fix a `C²` profile `φ` supported in `[0,1]`, with `M = ∫φ²`, autocorrelation
`G(x) = ∫ φ(u) φ(u+x) du` and spectrum `P(t) = |φ̂(2πt)|²`. Below touching the complete Weil
energy of the conductor-one Ramanujan mode is `log(1/(2πc)) + β(φ)/M + c q`, `q = (∫φ)²/M`;
it grows linearly in the overlap ratio `c` through the pole charge. Past touching the successor
shells `1 ≤ h < c` enter. The **completed shell energy**

`E(c) = log(1/(2πc)) + β(φ)/M + c q − (2/M) Σ_{1≤h<c} ∫_{h/c}^1 G(u)/u du`

subtracts them. This file proves:

* **Increment law** (`completedShellEnergy_sub_eq`): for `0 < c ≤ C`,
  `E(c) − E(C) = (2/M) Σ_{k≥1} (1/k) ∫_{kc}^{kC} P(t) dt`.
  It is Poisson summation of `G` on the lattice `ℤ/s`, integrated over `s ∈ [c, C]`; the shell
  sum is exactly the lattice part of Poisson's formula.
* **Marginality** (`tendsto_completedShellEnergy_atTop`): `E(c) → 0` as `c → ∞`. This is
  Stirling's formula: the archimedean finite part `−log 2π` is Stirling's constant.
* **Positive Fourier integral** (`hasSum_completedShellEnergy`):
  `E(c) = (2/M) Σ_{k≥1} (1/k) ∫_{kc}^∞ P(t) dt`. Hence `E ≥ 0` and `E` is antitone.
* **Below touching** (`completedShellEnergy_eq_adjunction`): for `0 < c ≤ 1` the shell range is
  empty and `E(c)` is the conductor-one complete-Weil energy `completeWeilAdjunctionEnergy φ c 1`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset intervalIntegral
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.CompletedShell

open SpacingScaleHarmonicAnalysis

variable {φ : ℝ → ℝ}

/-- The autocorrelation `G(x) = ∫ φ(u) φ(u + x) du` of the profile. -/
abbrev shellAutocorr (φ : ℝ → ℝ) : ℝ → ℝ := RHTower.ArchimedeanAnomaly.autocorr φ

/-- The spectrum `P(t) = |φ̂(2πt)|²` of the profile. -/
def shellSpectrum (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ‖Zeta23.paperFT (fun u => (φ u : ℂ)) ((2 * π * t : ℝ) : ℂ)‖ ^ 2

/-- The successor-shell sum `S(c) = Σ_{1≤h<c} ∫_{h/c}^1 G(u)/u du`. -/
def shellSum (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∑ h ∈ Finset.Ico 1 ⌈c⌉₊, ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u

/-- The **completed shell energy** of the conductor-one mode at overlap ratio `c`. -/
def completedShellEnergy (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  completeWeilSelfFinitePart φ c + completeWeilPoleShift φ c -
    2 * shellSum φ c / ∫ u, φ u ^ 2

/-! ### The autocorrelation -/

section Autocorrelation

variable (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

omit hφ in
theorem hasCompactSupport_profile : HasCompactSupport φ :=
  HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu

theorem profile_zero : φ 0 = 0 := by
  have hc : ContinuousAt φ 0 := hφ.continuous.continuousAt
  have hlim : Tendsto φ (𝓝[<] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hsupp u fun h => absurd h.1 (not_le.mpr hu)).symm
  exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hlim

theorem profile_one : φ 1 = 0 := by
  have hc : ContinuousAt φ 1 := hφ.continuous.continuousAt
  have hlim : Tendsto φ (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hsupp u fun h => absurd h.2 (not_le.mpr hu)).symm
  exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hlim

/-- The autocorrelation vanishes from overlap one on. -/
theorem shellAutocorr_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : shellAutocorr φ x = 0 := by
  have h0 := profile_zero hφ hsupp
  have h1 := profile_one hφ hsupp
  have hpt : ∀ u, φ u * φ (u + x) = 0 := by
    intro u
    by_cases hu : u ∈ Set.Ioo (0 : ℝ) 1
    · rw [hsupp (u + x) fun h => by linarith [h.2, hu.1], mul_zero]
    · have : φ u = 0 := by
        by_cases hu' : u ∈ Set.Icc (0 : ℝ) 1
        · rcases eq_or_lt_of_le hu'.1 with h | h
          · rw [← h, h0]
          · have : u = 1 := by
              by_contra hne
              exact hu ⟨h, lt_of_le_of_ne hu'.2 hne⟩
            rw [this, h1]
        · exact hsupp u hu'
      rw [this, zero_mul]
  simp only [shellAutocorr, RHTower.ArchimedeanAnomaly.autocorr, hpt, integral_zero]

omit hφ hsupp in
theorem shellAutocorr_neg (x : ℝ) : shellAutocorr φ (-x) = shellAutocorr φ x :=
  RHTower.ArchimedeanExactForm.autocorr_neg φ x

theorem shellAutocorr_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : shellAutocorr φ x = 0 := by
  rcases le_abs'.mp hx with h | h
  · rw [← neg_neg x, shellAutocorr_neg]
    exact shellAutocorr_eq_zero_of_one_le hφ hsupp (by linarith)
  · exact shellAutocorr_eq_zero_of_one_le hφ hsupp h

theorem contDiff_shellAutocorr : ContDiff ℝ 2 (shellAutocorr φ) :=
  BiScaleUncertainty.ChebyshevGauge.contDiff_autocorr hφ (hasCompactSupport_profile hsupp)

theorem continuous_shellAutocorr : Continuous (shellAutocorr φ) :=
  (contDiff_shellAutocorr hφ hsupp).continuous

omit hφ hsupp in
theorem shellAutocorr_zero : shellAutocorr φ 0 = ∫ u, φ u ^ 2 := by
  simp only [shellAutocorr, RHTower.ArchimedeanAnomaly.autocorr, add_zero, pow_two]

/-- On the real axis the transform of `G` is the spectrum. -/
theorem paperFT_shellAutocorr (t : ℝ) :
    Zeta23.paperFT (fun u => ((shellAutocorr φ u : ℝ) : ℂ)) ((2 * π * t : ℝ) : ℂ) =
      ((shellSpectrum φ t : ℝ) : ℂ) := by
  rw [BiScaleUncertainty.ChebyshevGauge.paperFT_autocorr hφ.continuous
    (hasCompactSupport_profile hsupp), Complex.conj_ofReal, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, shellSpectrum]

end Autocorrelation

/-! ### The spectrum -/

theorem shellSpectrum_nonneg (t : ℝ) : 0 ≤ shellSpectrum φ t := by
  unfold shellSpectrum; positivity

theorem shellSpectrum_neg (t : ℝ) : shellSpectrum φ (-t) = shellSpectrum φ t := by
  unfold shellSpectrum
  have h : Zeta23.paperFT (fun u => (φ u : ℂ)) ((2 * π * -t : ℝ) : ℂ) =
      (starRingEnd ℂ) (Zeta23.paperFT (fun u => (φ u : ℂ)) ((2 * π * t : ℝ) : ℂ)) := by
    rw [Zeta23.paperFT_def, Zeta23.paperFT_def, ← integral_conj]
    congr 1
    funext u
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [h, Complex.norm_conj]

/-- The spectrum at the origin is the squared charge. -/
theorem shellSpectrum_zero : shellSpectrum φ 0 = (∫ u, φ u) ^ 2 := by
  unfold shellSpectrum
  rw [Zeta23.paperFT_def]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Quartic decay of the spectrum. -/
theorem exists_shellSpectrum_le (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ t : ℝ, shellSpectrum φ t ≤ N ^ 2 / ((1 + |2 * π * t|) ^ 2) ^ 2 := by
  obtain ⟨N, hN0, hN⟩ := RHTower.exists_normSq_paperFT_le hφ hφc
  exact ⟨N, hN0, fun t => hN (2 * π * t)⟩

theorem continuous_shellSpectrum (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Continuous (shellSpectrum φ) := by
  have hi : Integrable fun u => (φ u : ℂ) :=
    (Complex.continuous_ofReal.comp hφ).integrable_of_hasCompactSupport
      (hφc.comp_left Complex.ofReal_zero)
  exact ((RHTower.continuous_paperFT_real_of_integrable hi).comp
    (continuous_const.mul continuous_id)).norm.pow 2

/-! ### Poisson summation on the lattice `ℤ/s` -/

section Poisson

variable (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- Poisson summation for the autocorrelation: `Σ_k P(ks) = s⁻¹ Σ_m G(m/s)`. -/
theorem hasSum_shellSpectrum_int {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : ℤ => shellSpectrum φ (k * s))
      (s⁻¹ * ∑' m : ℤ, shellAutocorr φ (m * s⁻¹)) := by
  have hG : ContDiff ℝ 2 (fun u => ((shellAutocorr φ u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_shellAutocorr hφ hsupp)
  have hGs : ∀ u, ((shellAutocorr φ u : ℝ) : ℂ) ≠ 0 → |u| ≤ 1 := by
    intro u hu
    by_contra h
    exact hu (by rw [shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (le_of_lt (not_le.mp h)),
      Complex.ofReal_zero])
  have h := RHTower.hasSum_paperFT_lattice (inv_pos.mpr hs) hG hGs
  have harg : ∀ k : ℤ, ((k : ℝ) * (2 * π / s⁻¹)) = 2 * π * ((k : ℝ) * s) := fun k => by
    rw [div_inv_eq_mul]; ring
  simp_rw [harg, paperFT_shellAutocorr hφ hsupp] at h
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_mul] at h
  exact Complex.hasSum_ofReal.mp h

/-- The lattice side is a finite shell sum: `Σ_m G(m/s) = M + 2 Σ_{1≤j<K} G(j/s)` for `s ≤ K`. -/
theorem tsum_shellAutocorr_lattice {s : ℝ} (hs : 0 < s) {K : ℕ} (hK : s ≤ K) :
    ∑' m : ℤ, shellAutocorr φ (m * s⁻¹) =
      (∫ u, φ u ^ 2) + 2 * ∑ j ∈ Finset.Ico 1 K, shellAutocorr φ (j * s⁻¹) := by
  have hzero : ∀ m : ℤ, (K : ℝ) ≤ |(m : ℝ)| → shellAutocorr φ (m * s⁻¹) = 0 := by
    intro m hm
    apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
    rw [abs_mul, abs_inv, abs_of_pos hs, le_mul_inv_iff₀ hs, one_mul]
    exact hK.trans hm
  have hsum : Summable fun m : ℤ => shellAutocorr φ (m * s⁻¹) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) K) fun m hm => hzero m ?_
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hm
    rcases hm with hm | hm
    · have : (m : ℝ) < -(K : ℝ) := by exact_mod_cast hm
      rw [abs_of_neg (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])]
      linarith
    · have : (K : ℝ) < m := by exact_mod_cast hm
      rw [abs_of_pos (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])]
      linarith
  have h1 := hsum.hasSum.nat_add_neg
  have hev : ∀ n : ℕ, shellAutocorr φ ((n : ℤ) * s⁻¹) + shellAutocorr φ (((-(n : ℤ) : ℤ) : ℝ) * s⁻¹) =
      2 * shellAutocorr φ (n * s⁻¹) := by
    intro n
    rw [Int.cast_neg, neg_mul, shellAutocorr_neg, Int.cast_natCast]
    ring
  simp_rw [hev] at h1
  have h2 : HasSum (fun n : ℕ => 2 * shellAutocorr φ (n * s⁻¹))
      (∑ n ∈ Finset.range K, 2 * shellAutocorr φ (n * s⁻¹)) := by
    refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    have h0 := hzero n (by rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]; exact_mod_cast hn)
    rw [Int.cast_natCast] at h0
    rw [h0, mul_zero]
  have hK1 : 0 < K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le hs hK
    exact_mod_cast this
  have h3 := h1.unique h2
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hK1, Int.cast_zero, zero_mul,
    shellAutocorr_zero, ← Finset.mul_sum] at h3
  rw [Nat.cast_zero, zero_mul, shellAutocorr_zero] at h3
  linarith

/-- One-sided Poisson formula: `Σ_{n≥1} P(ns) = (s⁻¹(M + 2Σ_{1≤j<K} G(j/s)) − (∫φ)²)/2`. -/
theorem hasSum_shellSpectrum_nat {s : ℝ} (hs : 0 < s) {K : ℕ} (hK : s ≤ K) :
    HasSum (fun n : ℕ => shellSpectrum φ ((n + 1) * s))
      ((s⁻¹ * ((∫ u, φ u ^ 2) + 2 * ∑ j ∈ Finset.Ico 1 K, shellAutocorr φ (j * s⁻¹)) -
        (∫ u, φ u) ^ 2) / 2) := by
  have h1 := (hasSum_shellSpectrum_int hφ hsupp hs).nat_add_neg
  have hev : ∀ n : ℕ, shellSpectrum φ ((n : ℤ) * s) + shellSpectrum φ (((-(n : ℤ) : ℤ) : ℝ) * s) =
      2 * shellSpectrum φ (n * s) := by
    intro n
    rw [Int.cast_neg, neg_mul, shellSpectrum_neg, Int.cast_natCast]
    ring
  simp_rw [hev] at h1
  rw [Int.cast_zero, zero_mul, shellSpectrum_zero, tsum_shellAutocorr_lattice hφ hsupp hs hK] at h1
  have h2 := h1.div_const 2
  simp_rw [mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at h2
  have h3 := (hasSum_nat_add_iff' 1).mpr h2
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul,
    shellSpectrum_zero, Nat.cast_add, Nat.cast_one] at h3
  set X := s⁻¹ * ((∫ u, φ u ^ 2) + 2 * ∑ j ∈ Finset.Ico 1 K, shellAutocorr φ (j * s⁻¹)) with hX
  have e : (X + (∫ u, φ u) ^ 2) / 2 - (∫ u, φ u) ^ 2 = (X - (∫ u, φ u) ^ 2) / 2 := by ring
  rw [e] at h3
  exact h3

end Poisson

/-! ### The increment law -/

section Increment

variable (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

theorem continuousOn_shellAutocorr_div : ContinuousOn (fun u => shellAutocorr φ u / u) (Ioi 0) :=
  (continuous_shellAutocorr hφ hsupp).continuousOn.div continuousOn_id fun _ hu => ne_of_gt hu

theorem intervalIntegrable_shellAutocorr_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u => shellAutocorr φ u / u) volume a b :=
  ((continuousOn_shellAutocorr_div hφ hsupp).mono fun x hx => by
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hx; exact lt_of_lt_of_le ha hx.1
    · rw [uIcc_of_ge h] at hx; exact lt_of_lt_of_le hb hx.1).intervalIntegrable

/-- The change of variables `u = j/s` of a shell: `∫_c^C G(j/s) ds/s = ∫_{j/C}^{j/c} G(u)/u du`. -/
theorem integral_shell_change {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C) {j : ℕ} (hj : 1 ≤ j) :
    ∫ s in c..C, s⁻¹ * shellAutocorr φ (j * s⁻¹) =
      ∫ u in ((j : ℝ) / C)..((j : ℝ) / c), shellAutocorr φ u / u := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hpos : ∀ x ∈ uIcc c C, 0 < x := fun x hx => by
    rw [uIcc_of_le hcC] at hx; exact lt_of_lt_of_le hc hx.1
  have hderiv : ∀ x ∈ uIcc c C, HasDerivAt (fun y => (j : ℝ) * y⁻¹) (-((j : ℝ) * (x ^ 2)⁻¹)) x := by
    intro x hx
    exact ((hasDerivAt_inv (ne_of_gt (hpos x hx))).const_mul (j : ℝ)).congr_deriv (by ring)
  have hcont : ContinuousOn (fun x => -((j : ℝ) * (x ^ 2)⁻¹)) (uIcc c C) :=
    (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun x hx =>
      pow_ne_zero 2 (ne_of_gt (hpos x hx)))).neg
  have hgcont : ContinuousOn (fun u => shellAutocorr φ u / u) ((fun y => (j : ℝ) * y⁻¹) '' uIcc c C) :=
    (continuousOn_shellAutocorr_div hφ hsupp).mono fun _ ⟨x, hx, hxu⟩ => by
      rw [← hxu]; exact mul_pos hj0 (inv_pos.mpr (hpos x hx))
  have key := intervalIntegral.integral_comp_mul_deriv' hderiv hcont hgcont
  have hcongr : ∫ s in c..C, s⁻¹ * shellAutocorr φ (j * s⁻¹) =
      -∫ x in c..C, ((fun u => shellAutocorr φ u / u) ∘ fun y => (j : ℝ) * y⁻¹) x *
        -((j : ℝ) * (x ^ 2)⁻¹) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 := ne_of_gt (hpos x hx)
    have hj0' : (j : ℝ) ≠ 0 := hj0.ne'
    simp only [Function.comp_apply]
    field_simp
  rw [hcongr, key, intervalIntegral.integral_symm, neg_neg, div_eq_mul_inv, div_eq_mul_inv]

/-- The integrand vanishes past overlap one, so `∫_{x}^1 G/u = 0` for `x ≥ 1`. -/
theorem integral_shell_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    ∫ u in x..1, shellAutocorr φ u / u = 0 := by
  rw [intervalIntegral.integral_symm, neg_eq_zero]
  have : ∫ u in (1 : ℝ)..x, shellAutocorr φ u / u = ∫ u in (1 : ℝ)..x, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hx] at hu
    simp only [shellAutocorr_eq_zero_of_one_le hφ hsupp hu.1, zero_div]
  rw [this, intervalIntegral.integral_zero]

/-- Summing the shells: `Σ_{1≤j<⌈C⌉} ∫_{j/C}^{j/c} G/u = S(C) − S(c)`. -/
theorem sum_integral_shell_eq {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C) :
    ∑ j ∈ Finset.Ico 1 ⌈C⌉₊, ∫ u in ((j : ℝ) / C)..((j : ℝ) / c), shellAutocorr φ u / u =
      shellSum φ C - shellSum φ c := by
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hsplit : ∀ j ∈ Finset.Ico 1 ⌈C⌉₊,
      ∫ u in ((j : ℝ) / C)..((j : ℝ) / c), shellAutocorr φ u / u =
        (∫ u in ((j : ℝ) / C)..1, shellAutocorr φ u / u) -
          ∫ u in ((j : ℝ) / c)..1, shellAutocorr φ u / u := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_shellAutocorr_div hφ hsupp (div_pos hj0 hC) one_pos)
        (intervalIntegrable_shellAutocorr_div hφ hsupp one_pos (div_pos hj0 hc)),
      intervalIntegral.integral_symm ((j : ℝ) / c) 1]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  congr 1
  symm
  refine Finset.sum_subset (Finset.Ico_subset_Ico_right (Nat.ceil_mono hcC)) fun j hj hjc => ?_
  have hjc' : ⌈c⌉₊ ≤ j := by
    simp only [Finset.mem_Ico, not_and, not_lt] at hjc
    exact hjc (Finset.mem_Ico.mp hj).1
  apply integral_shell_eq_zero_of_one_le hφ hsupp
  rw [le_div_iff₀ hc, one_mul]
  exact (Nat.le_ceil c).trans (by exact_mod_cast hjc')

variable (hM : 0 < ∫ u, φ u ^ 2)
include hM

/-- **The increment law.** For `0 < c ≤ C`,
`E(c) − E(C) = (2/M) Σ_{n≥0} (n+1)⁻¹ ∫_{(n+1)c}^{(n+1)C} P(t) dt`. -/
theorem hasSum_completedShellEnergy_sub {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C) :
    HasSum (fun n : ℕ => 2 / (∫ u, φ u ^ 2) *
        (((n : ℝ) + 1)⁻¹ * ∫ t in ((n : ℝ) + 1) * c..((n : ℝ) + 1) * C, shellSpectrum φ t))
      (completedShellEnergy φ c - completedShellEnergy φ C) := by
  set M := ∫ u, φ u ^ 2 with hMdef
  set Q := (∫ u, φ u) ^ 2 with hQdef
  set K := ⌈C⌉₊ with hKdef
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hK : C ≤ K := Nat.le_ceil C
  have hφc := hasCompactSupport_profile hsupp
  obtain ⟨N, -, hN⟩ := exists_shellSpectrum_le hφ hφc
  have hpos : ∀ x ∈ uIcc c C, 0 < x := fun x hx => by
    rw [uIcc_of_le hcC] at hx; exact lt_of_lt_of_le hc hx.1
  set f : ℝ → ℝ := fun s =>
    (s⁻¹ * (M + 2 * ∑ j ∈ Finset.Ico 1 K, shellAutocorr φ (j * s⁻¹)) - Q) / 2 with hf
  have hP := continuous_shellSpectrum (φ := φ) hφ.continuous hφc
  have hint : HasSum (fun n : ℕ => ∫ s in c..C, shellSpectrum φ ((n + 1) * s)) (∫ s in c..C, f s) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => N ^ 2 / (2 * π * ((n : ℝ) + 1) * c) ^ 4)
      (fun n => (hP.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
      (fun n => Eventually.of_forall fun t ht => ?_) ?_ intervalIntegrable_const
      (Eventually.of_forall fun t ht => ?_)
    · rw [uIoc_of_le hcC] at ht
      have ht0 : 0 < t := lt_trans hc ht.1
      have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (shellSpectrum_nonneg _)]
      refine (hN _).trans ?_
      have hx : 2 * π * ((n : ℝ) + 1) * c ≤ |2 * π * (((n : ℝ) + 1) * t)| := by
        rw [abs_of_pos (by positivity)]
        have := mul_le_mul_of_nonneg_left ht.1.le (by positivity : (0 : ℝ) ≤ 2 * π * ((n : ℝ) + 1))
        linarith
      have hx0 : 0 < 2 * π * ((n : ℝ) + 1) * c := by positivity
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      calc (2 * π * ((n : ℝ) + 1) * c) ^ 4 ≤ (1 + |2 * π * (((n : ℝ) + 1) * t)|) ^ 4 :=
            pow_le_pow_left₀ hx0.le (by linarith) 4
        _ = ((1 + |2 * π * (((n : ℝ) + 1) * t)|) ^ 2) ^ 2 := by ring
    · refine Eventually.of_forall fun t _ => ?_
      have : Summable fun n : ℕ => N ^ 2 / (2 * π * c) ^ 4 * (1 / ((n : ℝ) + 1) ^ 4) := by
        refine Summable.mul_left _ ?_
        have := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4))
        exact (summable_nat_add_iff 1).mpr this |>.congr fun n => by push_cast; ring
      refine this.congr fun n => ?_
      field_simp
    · rw [uIoc_of_le hcC] at ht
      have ht0 : 0 < t := lt_trans hc ht.1
      exact hasSum_shellSpectrum_nat hφ hsupp ht0 (ht.2.trans hK)
  -- evaluate both sides
  have hlhs : ∀ n : ℕ, ∫ s in c..C, shellSpectrum φ ((n + 1) * s) =
      ((n : ℝ) + 1)⁻¹ * ∫ t in ((n : ℝ) + 1) * c..((n : ℝ) + 1) * C, shellSpectrum φ t := by
    intro n
    rw [intervalIntegral.integral_comp_mul_left (f := shellSpectrum φ) (by positivity), smul_eq_mul]
  have hinv : IntervalIntegrable (fun s : ℝ => s⁻¹) volume c C :=
    (continuousOn_inv₀.mono fun x hx => ne_of_gt (hpos x hx)).intervalIntegrable
  have hshellC : ∀ j ∈ Finset.Ico 1 K, ContinuousOn
      (fun s : ℝ => s⁻¹ * shellAutocorr φ (j * s⁻¹)) (uIcc c C) := by
    intro j _
    refine (continuousOn_inv₀.mono fun x hx => ne_of_gt (hpos x hx)).mul ?_
    exact (continuous_shellAutocorr hφ hsupp).comp_continuousOn
      (continuousOn_const.mul (continuousOn_inv₀.mono fun x hx => ne_of_gt (hpos x hx)))
  have hshell : ∀ j ∈ Finset.Ico 1 K, IntervalIntegrable
      (fun s : ℝ => s⁻¹ * shellAutocorr φ (j * s⁻¹)) volume c C :=
    fun j hj => (hshellC j hj).intervalIntegrable
  have hsumI : IntervalIntegrable
      (fun s : ℝ => ∑ j ∈ Finset.Ico 1 K, s⁻¹ * shellAutocorr φ (j * s⁻¹)) volume c C :=
    (continuousOn_finsetSum _ hshellC).intervalIntegrable
  have hrhs : ∫ s in c..C, f s =
      (M * Real.log (C / c) + 2 * (shellSum φ C - shellSum φ c) - Q * (C - c)) / 2 := by
    have hfe : f = fun s => (M / 2) * s⁻¹ +
        ∑ j ∈ Finset.Ico 1 K, s⁻¹ * shellAutocorr φ (j * s⁻¹) - Q / 2 := by
      funext s
      rw [hf, ← Finset.mul_sum]
      ring
    rw [hfe]
    beta_reduce
    rw [intervalIntegral.integral_sub ((hinv.const_mul _).add hsumI) intervalIntegrable_const,
      intervalIntegral.integral_add (hinv.const_mul _) hsumI,
      intervalIntegral.integral_const_mul, integral_inv_of_pos hc hC,
      intervalIntegral.integral_finsetSum hshell, intervalIntegral.integral_const, smul_eq_mul]
    rw [Finset.sum_congr rfl fun j hj => integral_shell_change hφ hsupp hc hcC
      (Finset.mem_Ico.mp hj).1, sum_integral_shell_eq hφ hsupp hc hcC]
    ring
  have hE : completedShellEnergy φ c - completedShellEnergy φ C =
      2 / M * ((M * Real.log (C / c) + 2 * (shellSum φ C - shellSum φ c) - Q * (C - c)) / 2) := by
    have hlog : Real.log (1 / (2 * π * c)) - Real.log (1 / (2 * π * C)) = Real.log (C / c) := by
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul (by positivity) hc.ne',
        Real.log_mul (by positivity) hC.ne', Real.log_div hC.ne' hc.ne']
      ring
    unfold completedShellEnergy completeWeilSelfFinitePart completeWeilPoleShift
    rw [← hMdef, ← hQdef]
    field_simp
    rw [← hlog]
    ring
  rw [hE]
  simp_rw [← hlhs]
  rw [← hrhs]
  exact hint.mul_left (2 / M)

/-- The completed shell energy is antitone in the overlap ratio. -/
theorem completedShellEnergy_antitone {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C) :
    completedShellEnergy φ C ≤ completedShellEnergy φ c := by
  have h := hasSum_completedShellEnergy_sub hφ hsupp hM hc hcC
  have h0 := h.nonneg fun n => by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine mul_nonneg (div_nonneg zero_le_two hM.le) (mul_nonneg (inv_nonneg.mpr hn.le) ?_)
    exact intervalIntegral.integral_nonneg (mul_le_mul_of_nonneg_left hcC hn.le)
      fun t _ => shellSpectrum_nonneg t
  linarith

end Increment

/-! ### Cell averages of a continuous function -/

/-- **Cell averaging.** For continuous `H`,
`n ∫_0^1 u H(u) du − Σ_{1≤h<n} ∫_{h/n}^1 H → ½ ∫_0^1 H`: on each cell `[j/n, (j+1)/n]` the
weight `nu − j − ½` has mean zero, and uniform continuity pays the rest. -/
theorem tendsto_cell_average {H : ℝ → ℝ} (hH : Continuous H) :
    Tendsto (fun n : ℕ => (n : ℝ) * (∫ u in (0 : ℝ)..1, u * H u) -
        ∑ h ∈ Finset.Ico 1 n, ∫ u in ((h : ℝ) / n)..1, H u)
      atTop (𝓝 ((1 / 2) * ∫ u in (0 : ℝ)..1, H u)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδH⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous hH.continuousOn) (ε / 2) (half_pos hε)
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hδ
  refine ⟨n₀ + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 n₀) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnδ : 1 / (n : ℝ) < δ := by
    refine lt_of_le_of_lt ?_ hn₀
    apply one_div_le_one_div_of_le (by positivity)
    have : (n₀ : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith
  set a : ℕ → ℝ := fun j => (j : ℝ) / n with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have han : a n = 1 := by simp [ha, div_self hn0.ne']
  have hII : ∀ (F : ℝ → ℝ), Continuous F → ∀ k, IntervalIntegrable F volume (a k) (a (k + 1)) :=
    fun F hF k => hF.intervalIntegrable _ _
  have hcont1 : Continuous fun u : ℝ => u * H u := continuous_id.mul hH
  -- cell decompositions
  have hsplit1 : (∫ u in (0 : ℝ)..1, u * H u) = ∑ j ∈ Finset.range n, ∫ u in a j..a (j + 1), u * H u := by
    rw [intervalIntegral.sum_integral_adjacent_intervals fun k _ => hII _ hcont1 k, ha0, han]
  have hsplit2 : (∫ u in (0 : ℝ)..1, H u) = ∑ j ∈ Finset.range n, ∫ u in a j..a (j + 1), H u := by
    rw [intervalIntegral.sum_integral_adjacent_intervals fun k _ => hII _ hH k, ha0, han]
  have hsplit3 : ∑ h ∈ Finset.Ico 1 n, ∫ u in ((h : ℝ) / n)..1, H u =
      ∑ j ∈ Finset.range n, (j : ℝ) * ∫ u in a j..a (j + 1), H u := by
    have hh : ∀ h ∈ Finset.Ico 1 n, ∫ u in ((h : ℝ) / n)..1, H u =
        ∑ j ∈ Finset.Ico h n, ∫ u in a j..a (j + 1), H u := by
      intro h hh
      rw [intervalIntegral.sum_integral_adjacent_intervals_Ico (Finset.mem_Ico.mp hh).2.le
        fun k _ => hII _ hH k, han]
    rw [Finset.sum_congr rfl hh, Finset.sum_Ico_Ico_comm, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot hn1]
    simp only [Nat.cast_zero, zero_mul, zero_add, Finset.sum_const, Nat.card_Ico,
      Nat.add_sub_cancel, nsmul_eq_mul]
  -- per-cell identity with the mean-zero weight
  have hcell : ∀ j : ℕ, (n : ℝ) * (∫ u in a j..a (j + 1), u * H u) -
      (j : ℝ) * (∫ u in a j..a (j + 1), H u) - (1 / 2) * ∫ u in a j..a (j + 1), H u =
        ∫ u in a j..a (j + 1), ((n : ℝ) * u - j - 1 / 2) * (H u - H (a j)) := by
    intro j
    have hw : ∫ u in a j..a (j + 1), ((n : ℝ) * u - j - 1 / 2) = 0 := by
      rw [intervalIntegral.integral_sub (hII _ (by fun_prop) j) intervalIntegrable_const,
        intervalIntegral.integral_sub (hII _ (by fun_prop) j) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
        intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
      simp only [ha]
      push_cast
      field_simp
      ring
    have hexp : (fun u => ((n : ℝ) * u - j - 1 / 2) * (H u - H (a j))) =
        fun u => ((n : ℝ) * (u * H u) - ((j : ℝ) + 1 / 2) * H u) -
          H (a j) * ((n : ℝ) * u - j - 1 / 2) := by
      funext u; ring
    have hi1 : IntervalIntegrable (fun u => (n : ℝ) * (u * H u)) volume (a j) (a (j + 1)) :=
      (hII _ hcont1 j).const_mul _
    have hi2 : IntervalIntegrable (fun u => ((j : ℝ) + 1 / 2) * H u) volume (a j) (a (j + 1)) :=
      (hII _ hH j).const_mul _
    rw [hexp, intervalIntegral.integral_sub (hi1.sub hi2) (hII _ (by fun_prop) j),
      intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hw]
    ring
  have hident : (n : ℝ) * (∫ u in (0 : ℝ)..1, u * H u) -
      (∑ h ∈ Finset.Ico 1 n, ∫ u in ((h : ℝ) / n)..1, H u) - (1 / 2) * ∫ u in (0 : ℝ)..1, H u =
        ∑ j ∈ Finset.range n, ∫ u in a j..a (j + 1), ((n : ℝ) * u - j - 1 / 2) * (H u - H (a j)) := by
    rw [hsplit1, hsplit2, hsplit3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hcell j
  -- each cell costs at most `ε/(2n)`
  have hbound : ∀ j ∈ Finset.range n,
      ‖∫ u in a j..a (j + 1), ((n : ℝ) * u - j - 1 / 2) * (H u - H (a j))‖ ≤ ε / 2 * (1 / n) := by
    intro j hj
    have hj : j < n := Finset.mem_range.mp hj
    have hlen : a (j + 1) - a j = 1 / n := by simp only [ha]; push_cast; field_simp; ring
    have hle : a j ≤ a (j + 1) := by linarith [show (0 : ℝ) < 1 / n by positivity]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a j) (b := a (j + 1))
      (C := ε / 2) (f := fun u => ((n : ℝ) * u - j - 1 / 2) * (H u - H (a j))) ?_
    · rwa [abs_of_nonneg (by linarith), hlen] at h
    intro u hu
    rw [uIoc_of_le hle] at hu
    have hu0 : 0 ≤ a j := by simp only [ha]; positivity
    have hu1 : a (j + 1) ≤ 1 := by
      simp only [ha]; rw [div_le_one hn0]; exact_mod_cast hj
    have hw : |(n : ℝ) * u - j - 1 / 2| ≤ 1 / 2 := by
      have h1 : (n : ℝ) * a j = j := by simp only [ha]; field_simp
      have h2 : (n : ℝ) * a (j + 1) = j + 1 := by simp only [ha]; push_cast; field_simp
      have h3 := mul_le_mul_of_nonneg_left hu.1.le hn0.le
      have h4 := mul_le_mul_of_nonneg_left hu.2 hn0.le
      rw [abs_le]; constructor <;> linarith
    have hd : dist u (a j) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
      linarith [hu.2]
    have hHd := hδH u ⟨by linarith [hu.1], by linarith [hu.2]⟩ (a j) ⟨hu0, by linarith⟩ hd
    rw [Real.dist_eq] at hHd
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |(n : ℝ) * u - j - 1 / 2| * |H u - H (a j)| ≤ 1 / 2 * (ε / 2) :=
          mul_le_mul hw hHd.le (abs_nonneg _) (by norm_num)
      _ ≤ ε / 2 := by linarith
  rw [Real.dist_eq, hident]
  calc |∑ j ∈ Finset.range n, ∫ u in a j..a (j + 1), ((n : ℝ) * u - j - 1 / 2) * (H u - H (a j))|
      ≤ ∑ j ∈ Finset.range n, ‖∫ u in a j..a (j + 1), ((n : ℝ) * u - j - 1 / 2) * (H u - H (a j))‖ :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, ε / 2 * (1 / n) := Finset.sum_le_sum hbound
    _ = ε / 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := half_lt_self hε

/-! ### Marginality: the limit at infinite overlap -/

/-- The regular part `H(u) = (G(0) − G(u))/u` of the shell integrand, with `H(0) = 0`. -/
def shellRegular (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  if u = 0 then 0 else (shellAutocorr φ 0 - shellAutocorr φ u) / u

theorem shellAutocorr_eq_sub_mul (u : ℝ) :
    shellAutocorr φ u = shellAutocorr φ 0 - u * shellRegular φ u := by
  unfold shellRegular
  split_ifs with h
  · subst h; ring
  · field_simp; ring

section Limit

variable (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- An even `C²` function has zero slope at the origin. -/
theorem hasDerivAt_shellAutocorr_zero : HasDerivAt (shellAutocorr φ) 0 0 := by
  have hd : DifferentiableAt ℝ (shellAutocorr φ) 0 :=
    (contDiff_shellAutocorr hφ hsupp).differentiable (by norm_num) 0
  have h1 := hd.hasDerivAt
  have h1' : HasDerivAt (shellAutocorr φ) (deriv (shellAutocorr φ) 0) (-(0 : ℝ)) := by
    rw [neg_zero]; exact h1
  have h2 := h1'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have h3 : (shellAutocorr φ ∘ fun x : ℝ => -x) = shellAutocorr φ :=
    funext fun x => shellAutocorr_neg x
  rw [h3] at h2
  have h4 := h1.unique h2
  have h0 : deriv (shellAutocorr φ) 0 = 0 := by linarith
  rwa [h0] at h1

theorem continuous_shellRegular : Continuous (shellRegular φ) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    rw [← continuousWithinAt_compl_self]
    have h := ((hasDerivAt_shellAutocorr_zero hφ hsupp).tendsto_slope_zero).neg
    rw [neg_zero] at h
    show Tendsto (shellRegular φ) (𝓝[≠] 0) (𝓝 (shellRegular φ 0))
    rw [show shellRegular φ 0 = 0 from if_pos rfl]
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    simp only [shellRegular, if_neg ht', zero_add, smul_eq_mul]
    field_simp
    ring
  · have hc : ContinuousAt (fun v => (shellAutocorr φ 0 - shellAutocorr φ v) / v) u :=
      ((continuous_const.sub (continuous_shellAutocorr hφ hsupp)).continuousAt).div
        continuousAt_id hu
    refine hc.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hu] with v hv
    rw [shellRegular, if_neg hv]

/-- The Robin shape term is the integral of the regular part: `β(φ) = ∫_0^1 H`. -/
theorem bumpRobin_eq_integral_shellRegular :
    bumpRobin φ 1 = ∫ u in (0 : ℝ)..1, shellRegular φ u := by
  rw [intervalIntegral.integral_of_le zero_le_one, bumpRobin]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have hy0 : y ≠ 0 := ne_of_gt hy.1
  rw [RHTower.ArchimedeanAnomaly.integral_sub_shift_sq (hasCompactSupport_profile hsupp)
    hφ.continuous y, shellRegular, if_neg hy0]
  field_simp

/-- The total mass of the autocorrelation is the squared charge, `∫ G = 2 ∫_0^1 G = (∫φ)²`. -/
theorem two_mul_integral_shellAutocorr :
    2 * ∫ u in (0 : ℝ)..1, shellAutocorr φ u = (∫ u, φ u) ^ 2 := by
  have hG := continuous_shellAutocorr hφ hsupp
  have htot : ∫ u, shellAutocorr φ u = (∫ u, φ u) ^ 2 := by
    have h := paperFT_shellAutocorr hφ hsupp 0
    rw [mul_zero, Complex.ofReal_zero, Zeta23.paperFT_def, shellSpectrum_zero] at h
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one] at h
    rw [integral_complex_ofReal] at h
    exact_mod_cast h
  have hsupp' : ∫ u in Set.Ioc (-1 : ℝ) 1, shellAutocorr φ u = ∫ u, shellAutocorr φ u := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hneg : ∫ u in (-1 : ℝ)..0, shellAutocorr φ u = ∫ u in (0 : ℝ)..1, shellAutocorr φ u := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (shellAutocorr φ)
    rw [neg_zero] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun x _ => shellAutocorr_neg x
  rw [← htot, ← hsupp', ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable (-1) 0)
      (hG.intervalIntegrable 0 1), hneg]
  ring

/-- Each shell integral splits into its logarithm and its regular part. -/
theorem integral_shell_eq_log_sub {a : ℝ} (ha : 0 < a) :
    ∫ u in a..1, shellAutocorr φ u / u =
      shellAutocorr φ 0 * Real.log (1 / a) - ∫ u in a..1, shellRegular φ u := by
  have hpos : ∀ x ∈ uIcc a 1, 0 < x := fun x hx => by
    rcases le_total a 1 with h | h
    · rw [uIcc_of_le h] at hx; exact lt_of_lt_of_le ha hx.1
    · rw [uIcc_of_ge h] at hx; exact lt_of_lt_of_le one_pos hx.1
  have hinv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume a 1 :=
    (continuousOn_inv₀.mono fun x hx => ne_of_gt (hpos x hx)).intervalIntegrable
  have hcongr : ∫ u in a..1, shellAutocorr φ u / u =
      ∫ u in a..1, (shellAutocorr φ 0 * u⁻¹ - shellRegular φ u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 := ne_of_gt (hpos u hu)
    rw [shellAutocorr_eq_sub_mul u]
    field_simp
  rw [hcongr, intervalIntegral.integral_sub (hinv.const_mul _)
    ((continuous_shellRegular hφ hsupp).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_inv_of_pos ha one_pos]

variable (hM : 0 < ∫ u, φ u ^ 2)
include hM

/-- **Exact Stirling form at integer overlap.** With `H = (G(0) − G)/u`,
`E(m+1) = 2 log(stirlingSeq (m+1)) − log π − (2/M)(R_{m+1} − ½∫_0^1 H)`, where
`R_n = n∫_0^1 uH − Σ_{1≤h<n} ∫_{h/n}^1 H` is the cell average of `H`. -/
theorem completedShellEnergy_natCast_succ (m : ℕ) :
    completedShellEnergy φ ((m : ℝ) + 1) =
      2 * Real.log (Stirling.stirlingSeq (m + 1)) - Real.log π -
        2 / (∫ u, φ u ^ 2) * ((((m : ℝ) + 1) * (∫ u in (0 : ℝ)..1, u * shellRegular φ u) -
          ∑ h ∈ Finset.Ico 1 (m + 1), ∫ u in ((h : ℝ) / ((m : ℝ) + 1))..1, shellRegular φ u) -
            (1 / 2) * ∫ u in (0 : ℝ)..1, shellRegular φ u) := by
  set M := ∫ u, φ u ^ 2 with hMdef
  set n : ℝ := (m : ℝ) + 1 with hn
  have hn0 : 0 < n := by positivity
  have hG0 : shellAutocorr φ 0 = M := shellAutocorr_zero
  have hHc := continuous_shellRegular hφ hsupp
  -- the charge term
  have hQ : (∫ u, φ u) ^ 2 = 2 * (M - ∫ u in (0 : ℝ)..1, u * shellRegular φ u) := by
    rw [← two_mul_integral_shellAutocorr hφ hsupp]
    have : ∫ u in (0 : ℝ)..1, shellAutocorr φ u =
        ∫ u in (0 : ℝ)..1, (M - u * shellRegular φ u) := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [shellAutocorr_eq_sub_mul u, hG0]
    rw [this, intervalIntegral.integral_sub (f := fun _ => M) (g := fun u => u * shellRegular φ u)
      intervalIntegrable_const
      ((continuous_id.mul hHc).intervalIntegrable _ _), intervalIntegral.integral_const,
      smul_eq_mul]
    ring
  -- the shell sum
  have hceil : ⌈n⌉₊ = m + 1 := by
    rw [hn]; exact_mod_cast Nat.ceil_natCast (m + 1)
  have hS : shellSum φ n = M * ((m : ℝ) * Real.log n - Real.log (Nat.factorial m : ℝ)) -
      ∑ h ∈ Finset.Ico 1 (m + 1), ∫ u in ((h : ℝ) / n)..1, shellRegular φ u := by
    have hterm : ∀ h ∈ Finset.Ico 1 (m + 1), ∫ u in ((h : ℝ) / n)..1, shellAutocorr φ u / u =
        M * (Real.log n - Real.log h) - ∫ u in ((h : ℝ) / n)..1, shellRegular φ u := by
      intro h hh
      have hh0 : (0 : ℝ) < h := by exact_mod_cast (Finset.mem_Ico.mp hh).1
      rw [integral_shell_eq_log_sub hφ hsupp (div_pos hh0 hn0), hG0, one_div_div,
        Real.log_div hn0.ne' hh0.ne']
    rw [shellSum, hceil, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul]
    have hfact : ∑ h ∈ Finset.Ico 1 (m + 1), Real.log (h : ℝ) = Real.log (Nat.factorial m : ℝ) := by
      rw [← Real.log_prod (fun h hh => by
        have : (1 : ℕ) ≤ h := (Finset.mem_Ico.mp hh).1
        positivity), ← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod]
    rw [hfact]
  -- Stirling's sequence
  have hstir : 2 * Real.log (Stirling.stirlingSeq (m + 1)) - Real.log π =
      Real.log (1 / (2 * π * n)) + 2 * n - 2 * (m : ℝ) * Real.log n + 2 * Real.log (Nat.factorial m : ℝ) := by
    have hf : (Nat.factorial (m + 1) : ℝ) = n * (Nat.factorial m : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, hn]; push_cast; ring
    have hm0 : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
    rw [Stirling.stirlingSeq, Nat.cast_add, Nat.cast_one, ← hn, hf,
      Real.log_div (by positivity) (by positivity), Real.log_mul hn0.ne' hm0.ne',
      Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity), Real.log_pow,
      Real.log_div hn0.ne' (Real.exp_pos 1).ne', Real.log_exp,
      one_div, Real.log_inv, Real.log_mul (by positivity) hn0.ne',
      Real.log_mul (by positivity) hn0.ne', Real.log_mul two_ne_zero Real.pi_ne_zero]
    push_cast
    rw [hn]
    ring
  unfold completedShellEnergy completeWeilSelfFinitePart completeWeilPoleShift
  rw [← hMdef, hQ, hS, bumpRobin_eq_integral_shellRegular hφ hsupp, hstir]
  field_simp
  ring

/-- **Marginality.** The completed shell energy tends to zero at infinite overlap. -/
theorem tendsto_completedShellEnergy_atTop :
    Tendsto (completedShellEnergy φ) atTop (𝓝 0) := by
  set M := ∫ u, φ u ^ 2 with hMdef
  have hHc := continuous_shellRegular hφ hsupp
  -- along the integers
  have hstir : Tendsto (fun m : ℕ => 2 * Real.log (Stirling.stirlingSeq (m + 1)) - Real.log π)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => Stirling.stirlingSeq (m + 1)) atTop (𝓝 (√π)) :=
      (tendsto_add_atTop_iff_nat 1).mpr Stirling.tendsto_stirlingSeq_sqrt_pi
    have h2 := (h1.log (Real.sqrt_pos.mpr Real.pi_pos).ne').const_mul 2 |>.sub_const (Real.log π)
    rwa [Real.log_sqrt Real.pi_pos.le, show 2 * (Real.log π / 2) - Real.log π = 0 by ring] at h2
  have havg := (tendsto_cell_average hHc).comp (tendsto_add_atTop_nat 1)
  have havg' : Tendsto (fun m : ℕ => ((((m : ℝ) + 1) * (∫ u in (0 : ℝ)..1, u * shellRegular φ u) -
      ∑ h ∈ Finset.Ico 1 (m + 1), ∫ u in ((h : ℝ) / ((m : ℝ) + 1))..1, shellRegular φ u) -
        (1 / 2) * ∫ u in (0 : ℝ)..1, shellRegular φ u)) atTop (𝓝 0) := by
    have := havg.sub_const ((1 / 2) * ∫ u in (0 : ℝ)..1, shellRegular φ u)
    rw [sub_self] at this
    refine this.congr fun m => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hnat : Tendsto (fun m : ℕ => completedShellEnergy φ ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have := hstir.sub (havg'.const_mul (2 / M))
    rw [mul_zero, sub_zero] at this
    exact this.congr fun m => (completedShellEnergy_natCast_succ hφ hsupp hM m).symm
  -- squeeze along the reals using monotonicity
  have hlow : Tendsto (fun c : ℝ => completedShellEnergy φ (((⌈c⌉₊ - 1 : ℕ) : ℝ) + 1))
      atTop (𝓝 0) :=
    hnat.comp ((tendsto_sub_atTop_nat 1).comp tendsto_nat_ceil_atTop)
  have hup : Tendsto (fun c : ℝ => completedShellEnergy φ (((⌊c⌋₊ - 1 : ℕ) : ℝ) + 1))
      atTop (𝓝 0) :=
    hnat.comp ((tendsto_sub_atTop_nat 1).comp tendsto_nat_floor_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
    have h1 : 1 ≤ ⌈c⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
    have : ((⌈c⌉₊ - 1 : ℕ) : ℝ) + 1 = ⌈c⌉₊ := by
      rw [Nat.cast_sub h1, Nat.cast_one]; ring
    rw [this]
    exact completedShellEnergy_antitone hφ hsupp hM (by linarith) (Nat.le_ceil c)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
    have h1 : 1 ≤ ⌊c⌋₊ := Nat.le_floor (by exact_mod_cast hc)
    have : ((⌊c⌋₊ - 1 : ℕ) : ℝ) + 1 = ⌊c⌋₊ := by
      rw [Nat.cast_sub h1, Nat.cast_one]; ring
    rw [this]
    exact completedShellEnergy_antitone hφ hsupp hM (by exact_mod_cast h1) (Nat.floor_le (by linarith))

/-- **Positivity.** The completed shell energy is nonnegative at every overlap ratio. -/
theorem completedShellEnergy_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ completedShellEnergy φ c := by
  refine le_of_tendsto (tendsto_completedShellEnergy_atTop hφ hsupp hM) ?_
  filter_upwards [eventually_ge_atTop c] with C hC
  exact completedShellEnergy_antitone hφ hsupp hM hc hC

/-- **The completed shell energy is a positive Fourier integral.** For every `c > 0`,
`E(c) = (2/M) Σ_{n≥0} (n+1)⁻¹ ∫_{(n+1)c}^∞ P(t) dt`, i.e. the harmonic-number multiplier
`(2/M) ∫_0^∞ P(t) H_{⌊t/c⌋} dt` of the profile's spectrum. -/
theorem hasSum_completedShellEnergy {c : ℝ} (hc : 0 < c) :
    HasSum (fun n : ℕ => 2 / (∫ u, φ u ^ 2) *
        (((n : ℝ) + 1)⁻¹ * ∫ t in Ioi (((n : ℝ) + 1) * c), shellSpectrum φ t))
      (completedShellEnergy φ c) := by
  set M := ∫ u, φ u ^ 2 with hMdef
  have hφc := hasCompactSupport_profile hsupp
  have hPi : Integrable (shellSpectrum φ) := by
    have h := (RHTower.integrable_normSq_paperFT_ofReal hφ hφc).comp_mul_left'
      (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [shellSpectrum]
  set g : ℕ → ℝ := fun n => 2 / M * (((n : ℝ) + 1)⁻¹ * ∫ t in Ioi (((n : ℝ) + 1) * c), shellSpectrum φ t)
    with hg
  set F : ℕ → ℕ → ℝ := fun m n => 2 / M *
    (((n : ℝ) + 1)⁻¹ * ∫ t in ((n : ℝ) + 1) * c..((n : ℝ) + 1) * m, shellSpectrum φ t) with hF
  have hcoef : ∀ n : ℕ, 0 ≤ 2 / M * ((n : ℝ) + 1)⁻¹ := fun n =>
    mul_nonneg (div_nonneg zero_le_two hM.le) (inv_nonneg.mpr (by positivity))
  have hlim : ∀ n : ℕ, Tendsto (F · n) atTop (𝓝 (g n)) := by
    intro n
    have hb : Tendsto (fun m : ℕ => ((n : ℝ) + 1) * m) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
    have h := (intervalIntegral_tendsto_integral_Ioi (((n : ℝ) + 1) * c) hPi.integrableOn hb).const_mul
      (2 / M * ((n : ℝ) + 1)⁻¹)
    simpa only [hF, hg, mul_assoc] using h
  have hle : ∀ n : ℕ, ∀ m : ℕ, c ≤ m → F m n ≤ g n := by
    intro n m hm
    simp only [hF, hg, ← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hcoef n)
    have hab : ((n : ℝ) + 1) * c ≤ ((n : ℝ) + 1) * m :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_mono_set hPi.integrableOn
      (Eventually.of_forall fun t => shellSpectrum_nonneg t) Ioc_subset_Ioi_self.eventuallyLE
  have hF0 : ∀ m : ℕ, c ≤ m → ∀ n : ℕ, 0 ≤ F m n := by
    intro m hm n
    simp only [hF, ← mul_assoc]
    exact mul_nonneg (hcoef n) (intervalIntegral.integral_nonneg
      (mul_le_mul_of_nonneg_left hm (by positivity)) fun t _ => shellSpectrum_nonneg t)
  have hsumF : ∀ m : ℕ, c ≤ m →
      HasSum (F m) (completedShellEnergy φ c - completedShellEnergy φ m) :=
    fun m hm => hasSum_completedShellEnergy_sub hφ hsupp hM hc hm
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    simp only [hg, ← mul_assoc]
    exact mul_nonneg (hcoef n) (setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t)
  -- the partial sums of `g` are bounded by `E(c)`
  have hpart : ∀ K : ℕ, ∑ n ∈ Finset.range K, g n ≤ completedShellEnergy φ c := by
    intro K
    have ht : Tendsto (fun m : ℕ => ∑ n ∈ Finset.range K, F m n) atTop
        (𝓝 (∑ n ∈ Finset.range K, g n)) := tendsto_finsetSum _ fun n _ => hlim n
    refine le_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop ⌈c⌉₊] with m hm
    have hcm : c ≤ m := (Nat.le_ceil c).trans (by exact_mod_cast hm)
    calc ∑ n ∈ Finset.range K, F m n ≤ completedShellEnergy φ c - completedShellEnergy φ m :=
          sum_le_hasSum _ (fun n _ => hF0 m hcm n) (hsumF m hcm)
      _ ≤ completedShellEnergy φ c := by
          linarith [completedShellEnergy_nonneg hφ hsupp hM (lt_of_lt_of_le hc hcm)]
  have hgs : Summable g := summable_of_sum_range_le hg0 hpart
  -- dominated convergence for the series
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hgs hlim (by
    filter_upwards [eventually_ge_atTop ⌈c⌉₊] with m hm n
    have hcm : c ≤ m := (Nat.le_ceil c).trans (by exact_mod_cast hm)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 m hcm n)]
    exact hle n m hcm)
  have hE : Tendsto (fun m : ℕ => ∑' n, F m n) atTop (𝓝 (completedShellEnergy φ c)) := by
    have h := ((tendsto_completedShellEnergy_atTop hφ hsupp hM).comp
      tendsto_natCast_atTop_atTop).const_sub (completedShellEnergy φ c)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈c⌉₊] with m hm
    have hcm : c ≤ m := (Nat.le_ceil c).trans (by exact_mod_cast hm)
    exact ((hsumF m hcm).tsum_eq).symm
  have heq := tendsto_nhds_unique hT hE
  rw [← heq]
  exact hgs.hasSum

omit hφ hsupp hM in
/-- Below touching the shell range is empty: the completed shell energy is the conductor-one
complete-Weil energy, the proved limit of the conductor-one Ramanujan mode for `0 < c < 1`. -/
theorem completedShellEnergy_eq_adjunction {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    completedShellEnergy φ c = completeWeilAdjunctionEnergy φ c 1 := by
  have hceil : ⌈c⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff one_ne_zero]; norm_num; exact ⟨hc, hc1⟩
  unfold completedShellEnergy completeWeilAdjunctionEnergy shellSum ramanujanAdjunctionEnergy
  rw [hceil]
  simp [ArithmeticIntersectionTheory.tameDifferent]

end Limit

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.CompletedShell
