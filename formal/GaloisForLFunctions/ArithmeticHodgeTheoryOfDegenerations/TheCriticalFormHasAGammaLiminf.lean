import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHighAliasingHasItsPhysicalDualFloor
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundedWeilEnergyUpgradesL1LimitsToStrongLimits

/-!
# The critical Weil form has a Γ-liminf along `L¹` limits

Let `U_N` be the normalized synthesized sources of the tilted spline on a critical schedule
`c⁸ / log N → R`, with `‖U_N‖₂ ≤ 1` and bounded eighth exponential mass. If `U_N → F` in `L¹`, then

`liminf Q(U_N) ≥ Q_T(F) + (7 (∫φ²) J(1) / ((∫φ)² R)) ∫_{y<0} F² e^{−8y}`

for every `T ≥ e^{G₀}`, where `Q_T` is Weil's form with its Gamma part truncated to `|r| < T`.

The mechanism: a bounded form has uniformly small high frequencies, so the `L¹` limit is strong
(`CriticalArithmeticCorrelationTheory.eventually_integral_sq_sub_le_of_high_tails`), and the prime
sum and the pole moments converge. The Gamma form is convex: its low part converges, and its part
at the grid frequency `N e^{−A}` pays the aliasing floor with the weight `log N ≈ c⁸ / R`.

Every `Q_T` is a lower bound, so a limit of finite energy has `sup_T Q_T(F)` finite. The recovery
vectors `horizonWeights` attain the same value on smooth profiles.
-/

set_option autoImplicit false
noncomputable section
open Finset Filter Topology MeasureTheory Zeta23 RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticDegenerationTheory ArithmeticPositivityTheory

/-- Weil's form of an `L¹ ∩ L²` profile, with its Gamma part truncated to `|r| < T`. -/
def truncatedWeilForm (F : ℝ → ℝ) (T : ℝ) : ℝ :=
  lowGammaForm F T - primeSum F + (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2)

/-- The coefficient of the aliasing mass at critical ratio `R`. -/
def criticalAliasCoefficient (R : ℝ) : ℝ :=
  7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne / ((∫ u, tiltedUnitSpline u) ^ 2 * R)

private theorem contDiff_source (x : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    ContDiff ℝ 2 (normalizedCentredAtomicTest tiltedUnitSpline x c N) :=
  contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline x c N)

private theorem hasCompactSupport_source (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    HasCompactSupport (normalizedCentredAtomicTest tiltedUnitSpline x c N) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have hzero : normalizedCentredAtomicTest tiltedUnitSpline x c 0 = 0 := by
      funext y
      simp only [normalizedCentredAtomicTest, Nat.cast_zero, Real.sqrt_zero, zero_div, zero_mul,
        Pi.zero_apply]
    rw [hzero]
    exact HasCompactSupport.zero
  · exact (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero x hc
      (Nat.one_le_iff_ne_zero.mpr hN)).mul_left

/-- A source of overlap `c ≤ N` vanishes above the width `c / N ≤ 1`. -/
private theorem source_eq_zero_above (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hcN : c / N ≤ 1) {y : ℝ} (hy : 1 < y) :
    normalizedCentredAtomicTest tiltedUnitSpline x c N y = 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / (N : ℝ) := div_pos hc hN0
  have hsupp := tiltedUnitSpline_atom_support hw
  simp only [normalizedCentredAtomicTest, centredAtomicTest, atomicTest]
  rw [mul_eq_zero]
  right
  refine sum_eq_zero fun n hn => ?_
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hnN)
  rw [hsupp _ fun hmem => by linarith only [hmem.2, hy, hcN, hlog], mul_zero]

/-- The masses of an `L¹` limit of bounded sources. -/
private theorem limit_masses {l : Filter ℕ} [NeBot l] [IsCountablyGenerated l]
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {M : ℝ} (hM : ∀ N, (∫ y, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y ^ 2 *
      Real.exp (-(8 * y))) ≤ M)
    {F : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0)) :
    Integrable (fun y => F y ^ 2) ∧ Integrable (fun y => F y ^ 2 * Real.exp (-(8 * y))) := by
  let U := fun N => normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N
  have hUd (N : ℕ) : ContDiff ℝ 2 (U N) := contDiff_source _ _ _
  have hUc (N : ℕ) : HasCompactSupport (U N) :=
    hasCompactSupport_source _ (zero_lt_one.trans_le (hc1 N)) _
  have hUi (N : ℕ) : Integrable (U N) := (hUd N).continuous.integrable_of_hasCompactSupport (hUc N)
  have hM0 : 0 ≤ M := (integral_nonneg fun y =>
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le).trans (hM 0)
  constructor
  · have hw := weighted_sq_of_L1_limit (w := fun _ => (1 : ℝ)) hUi hF hL1 continuous_const
      (fun N => by
        simpa only [one_mul] using (hUd N).continuous.memLp_of_hasCompactSupport (hUc N))
      zero_le_one (fun N => by simpa only [one_mul] using hmass N)
    simpa only [one_mul] using hw.1.integrable_sq
  · let w : ℝ → ℝ := fun y => Real.exp (-(4 * y))
    have hwc : Continuous w := by fun_prop
    have hsq (a y : ℝ) : (w y * a) ^ 2 = a ^ 2 * Real.exp (-(8 * y)) := by
      have he : w y ^ 2 = Real.exp (-(8 * y)) := by
        simp only [w]
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [mul_pow, he, mul_comm]
    have hw8 := weighted_sq_of_L1_limit hUi hF hL1 hwc
      (fun N => (hwc.mul (hUd N).continuous).memLp_of_hasCompactSupport (hUc N).mul_left)
      hM0 (fun N => by simpa only [hsq] using hM N)
    simpa only [hsq] using hw8.1.integrable_sq

/-- **The Γ-liminf at a finite aperture.** -/
theorem eventually_lt_weilQuad_of_L1_limit {l : Filter ℕ} [NeBot l] [IsCountablyGenerated l]
    (hl : l ≤ atTop) {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {M : ℝ} (hM : ∀ N, (∫ y, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y ^ 2 *
      Real.exp (-(8 * y))) ≤ M)
    {F : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0))
    {A T b : ℝ} (hA : 0 < A) (hT : Real.exp factorialSpanGammaOffset ≤ T)
    (hb : b < truncatedWeilForm F T + criticalAliasCoefficient R *
      ∫ y in Set.Ioo (-A) 0, F y ^ 2 * Real.exp (-(8 * y))) :
    ∀ᶠ N in l, b < weilQuad (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N) := by
  let U := fun N => normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N
  let G₀ := factorialSpanGammaOffset
  have hUd (N : ℕ) : ContDiff ℝ 2 (U N) := contDiff_source _ _ _
  have hUc (N : ℕ) : HasCompactSupport (U N) :=
    hasCompactSupport_source _ (zero_lt_one.trans_le (hc1 N)) _
  have hUi (N : ℕ) : Integrable (U N) := (hUd N).continuous.integrable_of_hasCompactSupport (hUc N)
  obtain ⟨hF2, hF8⟩ := limit_masses hc1 hmass hM hF hL1
  -- sources vanish above the unit width
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hR hcrit 1 0
  have hsupp : ∀ᶠ N in atTop, ∀ y, 1 < y → U N y = 0 := by
    filter_upwards [hcN.eventually (ge_mem_nhds zero_lt_one), eventually_ge_atTop 1]
      with N hN hN1 y hy
    exact source_eq_zero_above _ (zero_lt_one.trans_le (hc1 N)) hN1 hN hy
  have hFs := ae_eq_zero_above_of_L1_limit hUi hF hL1 (hsupp.filter_mono hl)
  have hFW : WeightedTwo F := (exponentialSourceMass_le_of_support zero_le_one
    hF.aestronglyMeasurable hF2 hF8 hFs).1
  -- pass to the sublevel set of the form
  by_contra hnot
  have hfreq : ∃ᶠ N in l, N ∈ {N | weilQuad (U N) ≤ b} := by
    simpa only [Filter.not_eventually, not_lt, Set.mem_setOf_eq] using hnot
  let l' : Filter ℕ := l ⊓ 𝓟 {N | weilQuad (U N) ≤ b}
  haveI : NeBot l' := Filter.frequently_mem_iff_neBot.mp hfreq
  have hl' : l' ≤ atTop := inf_le_left.trans hl
  have hL1' : Tendsto (fun N => ∫ y, ‖U N y - F y‖) l' (𝓝 0) := hL1.mono_left inf_le_left
  have hb' : ∀ᶠ N in l', weilQuad (U N) ≤ b :=
    eventually_inf_principal.mpr (Eventually.of_forall fun N hN => hN)
  have hsupp' := hsupp.filter_mono hl'
  -- bounded energy makes the limit strong, and the prime and pole parts converge
  have htail := high_tails_of_bounded_weilQuad hUd hUc hmass hM hsupp' hb'
  have hstrong : ∀ ε > 0, ∀ᶠ N in l', (∫ y, (U N y - F y) ^ 2) ≤ ε := fun ε hε =>
    (eventually_integral_sq_sub_le_of_high_tails hUd hUc hF hL1' htail hε).mono fun N h => h.2
  have hd := tendsto_exponentialSourceMass_sub (fun N => (hUd N).continuous) hUc
    hF.aestronglyMeasurable hF2 hF8 hM hsupp' hFs hstrong
  obtain ⟨hP, hC, hS⟩ := tendsto_prime_and_pole_of_strong_limit (fun N => (hUd N).continuous) hUc
    hFW hmass hM hsupp' hd
  have hLow := tendsto_lowGammaForm hUi hF hL1' T
  -- the aliasing floor at the grid frequency
  let m : ℝ := ∫ u, tiltedUnitSpline u
  have hm2 : 0 < m ^ 2 :=
    lt_of_le_of_ne (sq_nonneg m) (pow_ne_zero 2 integral_tiltedUnitSpline_ne_zero).symm
  let κ : ℝ := 1 / (m ^ 2 * R)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  let I : ℝ := ∫ y in Set.Ioo (-A) 0, F y ^ 2 * Real.exp (-(8 * y))
  let α₀ : ℝ := 7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne * I
  have hcoef : criticalAliasCoefficient R * I = α₀ * κ := by
    dsimp only [criticalAliasCoefficient, α₀, κ, m]
    field_simp
  let X := truncatedWeilForm F T
  have hgap : 0 < X + α₀ * κ - b := by
    have hb2 := hb
    change b < X + criticalAliasCoefficient R * I at hb2
    rw [hcoef] at hb2
    linarith only [hb2]
  obtain ⟨b', hb'def⟩ : ∃ b', b' = α₀ - (X + α₀ * κ - b) / (2 * κ) := ⟨_, rfl⟩
  have hb'lt : b' < α₀ := by
    rw [hb'def]
    have : 0 < (X + α₀ * κ - b) / (2 * κ) := by positivity
    linarith only [this]
  have hb'κ : b < X + b' * κ := by
    have e : b' * κ = α₀ * κ - (X + α₀ * κ - b) / 2 := by
      rw [hb'def]
      field_simp
    rw [e]
    linarith only [hgap]
  have hfloor := eventually_criticalCurve_highFourierMass_gt_weighted_floor_along_filter hl'
    hc1 hR hcrit hmass hF hL1' hA (b := b') hb'lt
  -- the logarithmic weight at the grid frequency
  have hcinf := (criticalCurve_facts hc1 hR hcrit).1
  have hratio : Tendsto (fun N : ℕ => Real.log N / c N ^ 8) atTop (𝓝 R⁻¹) := by
    have h := hcrit.inv₀ hR.ne'
    refine h.congr fun N => ?_
    rw [inv_div]
  have hc8 : Tendsto (fun N : ℕ => (A + G₀) / c N ^ 8) atTop (𝓝 0) :=
    Tendsto.const_div_atTop ((tendsto_pow_atTop (by norm_num : 8 ≠ 0)).comp hcinf) _
  have hΛ : Tendsto (fun N : ℕ => (Real.log N / c N ^ 8 - (A + G₀) / c N ^ 8) / m ^ 2) atTop
      (𝓝 κ) := by
    have h := (hratio.sub hc8).div_const (m ^ 2)
    have e : (R⁻¹ - 0) / m ^ 2 = κ := by
      dsimp only [κ]
      field_simp
    rwa [e] at h
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- combine the three parts of the form
  have hlim : Tendsto (fun N => lowGammaForm (U N) T +
      ((Real.log N / c N ^ 8 - (A + G₀) / c N ^ 8) / m ^ 2) * b' - primeSum (U N) +
      (2 * coshHalfMoment (U N) ^ 2 - 2 * sinhHalfMoment (U N) ^ 2)) l'
      (𝓝 (lowGammaForm F T + κ * b' - primeSum F +
        (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2))) :=
    ((hLow.add ((hΛ.mono_left hl').mul_const b')).sub hP).add
      (((hC.pow 2).const_mul 2).sub ((hS.pow 2).const_mul 2))
  have hlimb : b < lowGammaForm F T + κ * b' - primeSum F +
      (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2) := by
    have e : X = lowGammaForm F T - primeSum F +
        (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2) := rfl
    rw [e] at hb'κ
    linarith only [hb'κ, mul_comm κ b']
  have hgt := hlim.eventually (lt_mem_nhds hlimb)
  have hgrid : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ T ≤ (N : ℝ) * Real.exp (-A) ∧
      0 ≤ Real.log N - A - G₀ := by
    have hgrow : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-A)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos _)
    filter_upwards [eventually_ge_atTop 1, hgrow.eventually_ge_atTop T,
      hlogN.eventually_ge_atTop (A + G₀)] with N h1 h2 h3
    exact ⟨h1, h2, by linarith only [h3]⟩
  have hpos : ∀ᶠ N in l', b < weilQuad (U N) := by
    filter_upwards [hgt, hfloor, hgrid.filter_mono hl'] with N hN1 hN2 hN3
    obtain ⟨hN1', hTN, hlog⟩ := hN3
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1'
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc1 N)
    have hc8pos : 0 < c N ^ 8 := pow_pos hc0 8
    have hlogT : Real.log ((N : ℝ) * Real.exp (-A)) = Real.log N - A := by
      rw [Real.log_mul hN0.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    have harch := lowGammaForm_add_high_le_archForm (hUd N) (hUc N) hT hTN
    rw [hlogT] at harch
    have hweil := weilQuad_eq_arch_sub_prime_add_pole (hUd N) (hUc N)
    -- the Gamma weight pays the floor
    have hΛN : ((Real.log N / c N ^ 8 - (A + G₀) / c N ^ 8) / m ^ 2) =
        (Real.log N - A - G₀) / (m ^ 2 * c N ^ 8) := by
      field_simp
      ring
    have hhigh : ((Real.log N / c N ^ 8 - (A + G₀) / c N ^ 8) / m ^ 2) * b' ≤
        (Real.log N - A - factorialSpanGammaOffset) * highFourierMass (U N)
          ((N : ℝ) * Real.exp (-A)) := by
      rw [hΛN]
      have hquot : 0 ≤ (Real.log N - A - G₀) / (m ^ 2 * c N ^ 8) :=
        div_nonneg hlog (mul_pos hm2 hc8pos).le
      have h := mul_le_mul_of_nonneg_left hN2.le hquot
      refine h.trans_eq ?_
      have hne : m ^ 2 * c N ^ 8 ≠ 0 := (mul_pos hm2 hc8pos).ne'
      change (Real.log N - A - G₀) / (m ^ 2 * c N ^ 8) *
        (m ^ 2 * c N ^ 8 * highFourierMass (U N) ((N : ℝ) * Real.exp (-A))) = _
      field_simp
      rfl
    have hgtN := hN1
    rw [Set.mem_setOf_eq] at hgtN
    linarith only [hgtN, harch, hweil, hhigh]
  obtain ⟨N, h1, h2⟩ := (hpos.and hb').exists
  exact (not_lt.mpr h2) h1

/-- **The Γ-liminf.** The full eighth exponential mass of the limit on the negative half-line is
paid: for every `T ≥ e^{G₀}` and every `b` below `Q_T(F) + α_R ∫_{y<0} F² e^{−8y}`, the Weil form
of the sources is eventually above `b`. -/
theorem eventually_lt_weilQuad_of_L1_limit_full {l : Filter ℕ} [NeBot l] [IsCountablyGenerated l]
    (hl : l ≤ atTop) {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {M : ℝ} (hM : ∀ N, (∫ y, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y ^ 2 *
      Real.exp (-(8 * y))) ≤ M)
    {F : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0))
    {T b : ℝ} (hT : Real.exp factorialSpanGammaOffset ≤ T)
    (hb : b < truncatedWeilForm F T + criticalAliasCoefficient R *
      ∫ y in Set.Iio 0, F y ^ 2 * Real.exp (-(8 * y))) :
    ∀ᶠ N in l, b < weilQuad (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N) := by
  obtain ⟨-, hF8⟩ := limit_masses hc1 hmass hM hF hL1
  let s : ℕ → Set ℝ := fun n => Set.Ioo (-((n : ℝ) + 1)) 0
  have hunion : (⋃ n, s n) = Set.Iio 0 := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_Ioo, Set.mem_Iio, s]
    constructor
    · rintro ⟨n, -, hy⟩
      exact hy
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_gt (-y)
      exact ⟨n, by linarith only [hn], hy⟩
  have hmono : Monotone s := fun i j hij y hy =>
    ⟨by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith only [hy.1, this], hy.2⟩
  have hlim := tendsto_setIntegral_of_monotone (μ := volume)
    (f := fun y => F y ^ 2 * Real.exp (-(8 * y))) (fun n => measurableSet_Ioo) hmono
    (hF8.integrableOn)
  rw [hunion] at hlim
  have hmul := (hlim.const_mul (criticalAliasCoefficient R)).const_add (truncatedWeilForm F T)
  obtain ⟨n, hn⟩ := (hmul.eventually (lt_mem_nhds hb)).exists
  exact eventually_lt_weilQuad_of_L1_limit hl hc1 hR hcrit hmass hM hF hL1
    (A := (n : ℝ) + 1) (by positivity) hT hn

/-- **Bounded energy makes the `L¹` limit strong.** Along a sublevel set of Weil's form, a source of
bounded eighth mass converging in `L¹` converges in `L²`. -/
theorem tendsto_integral_sq_sub_of_bounded_weilQuad {l : Filter ℕ} [NeBot l]
    [IsCountablyGenerated l] (hl : l ≤ atTop) {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {M : ℝ} (hM : ∀ N, (∫ y, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y ^ 2 *
      Real.exp (-(8 * y))) ≤ M)
    {F : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0))
    {b : ℝ} (hb : ∀ᶠ N in l,
      weilQuad (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N) ≤ b) :
    Tendsto (fun N => ∫ y,
      (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y) ^ 2) l (𝓝 0) := by
  let U := fun N => normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N
  have hUd (N : ℕ) : ContDiff ℝ 2 (U N) := contDiff_source _ _ _
  have hUc (N : ℕ) : HasCompactSupport (U N) :=
    hasCompactSupport_source _ (zero_lt_one.trans_le (hc1 N)) _
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hR hcrit 1 0
  have hsupp : ∀ᶠ N in atTop, ∀ y, 1 < y → U N y = 0 := by
    filter_upwards [hcN.eventually (ge_mem_nhds zero_lt_one), eventually_ge_atTop 1]
      with N hN hN1 y hy
    exact source_eq_zero_above _ (zero_lt_one.trans_le (hc1 N)) hN1 hN hy
  have htail := high_tails_of_bounded_weilQuad hUd hUc hmass hM (hsupp.filter_mono hl) hb
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_integral_sq_sub_le_of_high_tails hUd hUc hF hL1 htail
    (half_pos hε)] with N hN
  have h0 : 0 ≤ ∫ y, (U N y - F y) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  exact hN.2.trans_lt (half_lt_self hε)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
