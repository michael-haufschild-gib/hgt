import GaloisForLFunctions.BiScaleUncertainty.CombinationSpectralDensity
import GaloisForLFunctions.BiScaleUncertainty.SquareRootDensityPoleInvisibility
import GaloisForLFunctions.BiScaleUncertainty.BroadSpectralCostRealization

/-!
# The single-integer bathtub is exact, and the pole does not move it

Fix an integer `q ≥ 2`, put `ℓ = log q`, and let `m_q = (ℓ/π) ∫_0^{π/ℓ} γ` be the mean of the
archimedean symbol `γ = EF.gammaBracket` over one period `[−π/ℓ, π/ℓ]`. Consider nonnegative
combinations of Weil tests blind only at the powers `q^j`, `j ≥ 1`.

* **Lower bound** (`symbolPeriodMean_mul_massOf_le`). Blindness at every `q^j` makes the phase
  `r ℓ mod 2π` of the spectral measure uniform, and `γ` dominates its fold onto one period, so the
  archimedean part without the pole is at least `m_q` times the mass. For `q = 2` this is the
  corpus bathtub, here with blindness required only at the powers of `2`.
* **Attainment** (`exists_blindOn_powers_archOnly_le`). Midpoint atoms `ω_k = (k + 1/2)π/(Nℓ)`,
  `k < N`, have `Σ_k cos(ω_k jℓ) = 0` for `1 ≤ j < 2N` (the telescoping
  `2 sin(θ/2) cos((k+1/2)θ) = sin((k+1)θ) − sin(kθ)` closes at `Nθ = πj`). Cosine/sine
  modulations of an envelope whose correlation vanishes beyond `2Nℓ` are then blind at every
  `q^j`; their symbol is `h(0) Σ_k γ(ω_k)` up to the envelope energy (uniform in frequency), the
  midpoint sum is at most `N m_q + γ(π/ℓ) − γ(0)` by monotonicity, and a stretched envelope has
  normalized energy `O(1/N)`. So `m_q` is attained at rate `O(1/N)`.
* **The pole is invisible** (`exists_blindOn_poleMass_eq_small`). On the gapped powers of `q` a
  distant pair carries any pole mass at arbitrarily small archimedean cost *and mass*.

Hence (`zeroPoleBlindSymbolSlackOn_powers_iff`) the zero-pole blind symbol slack on the powers of
`q` is exactly `−m_q`, the same as without the pole constraint
(`zeroPoleBlindSymbolSlackOn_powers_iff_blind`). On the full integer grid the zero-pole slack is
`0` at every positive level exactly under RH; one integer's powers leave the whole gap `−m_q`, and
`q = 2` leaves the smallest one (`symbolPeriodMean_le_two`).
-/

open MeasureTheory Set Filter Topology Complex Finsupp
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
open Real (pi)
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. Slack on a node set -/

/-- Symbol slack `M` with blindness imposed only on `𝒩`. -/
def BlindSymbolSlackOn (𝒩 : Set ℕ) (M : ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → BlindOn 𝒩 c → 0 ≤ nodeArchOnly c + M * massOf c

/-- Zero-pole symbol slack `M` with blindness imposed only on `𝒩`. -/
def ZeroPoleBlindSymbolSlackOn (𝒩 : Set ℕ) (M : ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → BlindOn 𝒩 c → nodePoleMass c = 0 →
    0 ≤ nodeArchEnergy c + M * massOf c

theorem BlindSymbolSlackOn.mono {𝒩 : Set ℕ} {M M' : ℝ} (hMM' : M ≤ M')
    (h : BlindSymbolSlackOn 𝒩 M) : BlindSymbolSlackOn 𝒩 M' := fun c hc hb => by
  have := h c hc hb
  have := massOf_nonneg hc
  nlinarith

theorem BlindSymbolSlackOn.zeroPole {𝒩 : Set ℕ} {M : ℝ} (h : BlindSymbolSlackOn 𝒩 M) :
    ZeroPoleBlindSymbolSlackOn 𝒩 M := fun c hc hb hp => by
  have := h c hc hb
  rwa [nodeArchOnly, hp, sub_zero] at this

/-- The mean of `γ` over one period `[−π/log q, π/log q]` of `q`. -/
def symbolPeriodMean (q : ℕ) : ℝ :=
  Real.log q / π * ∫ v in (0 : ℝ)..π / Real.log q, EF.gammaBracket v

theorem symbolPeriodMean_two : symbolPeriodMean 2 = twoPeriodMean := by
  simp only [symbolPeriodMean, twoPeriodMean, Nat.cast_ofNat]

/-! ### 2. The lower bound -/

/-- **The single-integer bathtub.** A nonnegative combination blind at every `q^j` has archimedean
part without the pole at least `m_q` times its mass. -/
theorem symbolPeriodMean_mul_massOf_le {q : ℕ} (hq : 2 ≤ q) (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, 0 ≤ c f) (hb : BlindOn (powerNodes q) c) :
    symbolPeriodMean q * massOf c ≤ nodeArchOnly c := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hper := integral_combinationSpectralDensity_mul_periodic hq hc hb
    (continuous_foldedSymbol (Real.log q)) (foldedSymbol_neg (Real.log q))
  rw [integral_foldedSymbol hℓ, integral_combinationSpectralDensity] at hper
  have hGf : Integrable fun r =>
      combinationSpectralDensity c r * foldedSymbol (Real.log q) (phase (Real.log q) r) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_foldedSymbol (Real.log q)).continuousOn
    exact integrable_mul_bounded (integrable_combinationSpectralDensity c)
      ((continuous_foldedSymbol _).comp (continuous_phase _)) (C := C) fun r => by
        rw [← Real.norm_eq_abs]; exact hC _ (Set.mem_univ _)
  have hmono := integral_mono hGf (integrable_combinationSpectralDensity_mul_gammaBracket c)
    fun r => mul_le_mul_of_nonneg_left (foldedSymbol_phase_le hℓ r)
      (combinationSpectralDensity_nonneg hc r)
  rw [hper, integral_combinationSpectralDensity_mul_gammaBracket] at hmono
  have hpi : 0 < 2 * π := by positivity
  rw [symbolPeriodMean]
  nlinarith

theorem blindSymbolSlackOn_powers {q : ℕ} (hq : 2 ≤ q) :
    BlindSymbolSlackOn (powerNodes q) (-symbolPeriodMean q) := fun c hc hb => by
  have := symbolPeriodMean_mul_massOf_le hq c hc hb
  linarith

/-! ### 3. Midpoint cosine atoms -/

/-- **Midpoint cancellation:** `Σ_{k<N} cos((k + 1/2)πj/N) = 0` for `1 ≤ j < 2N`. -/
theorem sum_cos_midpoint_eq_zero {N j : ℕ} (hj1 : 1 ≤ j) (hj : j < 2 * N) :
    ∑ k ∈ Finset.range N, Real.cos (((k : ℝ) + 1 / 2) * (π * j / N)) = 0 := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  set θ : ℝ := π * j / N with hθ
  have hsin : Real.sin (θ / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < j := by exact_mod_cast hj1
      rw [hθ]; positivity
    · rw [hθ, show π * j / N / 2 = π * (j / (2 * N)) by ring]
      have : (j : ℝ) / (2 * N) < 1 := by
        rw [div_lt_one (by positivity)]; exact_mod_cast hj
      nlinarith [Real.pi_pos]
  have htel : ∀ k : ℕ, 2 * Real.sin (θ / 2) * Real.cos (((k : ℝ) + 1 / 2) * θ) =
      Real.sin (((k + 1 : ℕ) : ℝ) * θ) - Real.sin ((k : ℝ) * θ) := by
    intro k
    rw [Real.sin_sub_sin]
    push_cast
    ring_nf
  have hsum : 2 * Real.sin (θ / 2) *
      ∑ k ∈ Finset.range N, Real.cos (((k : ℝ) + 1 / 2) * θ) = 0 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => htel k,
      Finset.sum_range_sub (fun k : ℕ => Real.sin ((k : ℝ) * θ))]
    have hNθ : (N : ℝ) * θ = (j : ℕ) * π := by rw [hθ]; field_simp
    simp only [Nat.cast_zero, zero_mul, Real.sin_zero, sub_zero]
    rw [hNθ, Real.sin_nat_mul_pi]
  exact (mul_eq_zero.mp hsum).resolve_left (mul_ne_zero two_ne_zero hsin)

/-- Midpoint sums of `γ` exceed the period mean by at most the oscillation `γ(π/ℓ) − γ(0)`. -/
theorem sum_gammaBracket_midpoint_le {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N, EF.gammaBracket (((k : ℝ) + 1 / 2) * (π / (N * ℓ))) ≤
      N * (ℓ / π * ∫ v in (0 : ℝ)..π / ℓ, EF.gammaBracket v) +
        (EF.gammaBracket (π / ℓ) - EF.gammaBracket 0) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < π / (N * ℓ) := by positivity
  have h1 : ∀ k : ℕ, EF.gammaBracket (((k : ℝ) + 1 / 2) * (π / (N * ℓ))) ≤
      EF.gammaBracket (((k + 1 : ℕ) : ℝ) * (π / (N * ℓ))) := by
    intro k
    apply gammaBracket_le_of_abs_le
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    push_cast
    exact mul_le_mul_of_nonneg_right (by linarith) hc.le
  have h2 := Finset.sum_le_sum fun k (_ : k ∈ Finset.range N) => h1 k
  have h3 := Finset.sum_range_succ (fun k : ℕ => EF.gammaBracket ((k : ℝ) * (π / (N * ℓ)))) N
  have h4 := Finset.sum_range_succ' (fun k : ℕ => EF.gammaBracket ((k : ℝ) * (π / (N * ℓ)))) N
  have h5 := sum_le_mean_gammaBracket hℓ hN
  have hend : (N : ℝ) * (π / (N * ℓ)) = π / ℓ := by field_simp
  rw [hend] at h3
  simp only [Nat.cast_zero, zero_mul] at h4
  rw [div_le_iff₀ hNpos] at h5
  linarith

/-! ### 4. Real modulated tests -/

theorem logValue_realTest {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (n : ℕ) :
    logValue (realTest g hg hgc).1 n = 2 * autocorr g (Real.log n) / Real.sqrt n := by
  change (EF.weilTest (fun u => ((g u : ℝ) : ℂ)) (fun u => ((g u : ℝ) : ℂ)) (Real.log n) +
    EF.weilTest (fun u => ((g u : ℝ) : ℂ)) (fun u => ((g u : ℝ) : ℂ)) (-Real.log n)).re /
      Real.sqrt n = _
  rw [RHTower.AutocorrelationKrein.weilTest_eq, RHTower.AutocorrelationKrein.weilTest_eq,
    autocorr_neg]
  simp only [Complex.add_re, Complex.ofReal_re]
  ring

theorem archOnly_realTest {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    weilArchRe (EF.weilTest (realTest g hg hgc).1 (realTest g hg hgc).1) -
        (weilPoleTerm (EF.weilTest (realTest g hg hgc).1 (realTest g hg hgc).1)).re =
      EF.gammaBracket 0 * autocorr g 0 + biScaleLevyEnergy g := by
  change WeilOneSided.weilArchRe (EF.weilTest (fun u => ((g u : ℝ) : ℂ))
      (fun u => ((g u : ℝ) : ℂ))) -
    (weilPoleTerm (EF.weilTest (fun u => ((g u : ℝ) : ℂ)) (fun u => ((g u : ℝ) : ℂ)))).re = _
  rw [weilArchRe_ofReal_eq_pole_add_gamma_add_biScaleLevyEnergy hg hgc]
  ring

theorem integral_norm_sq_ofReal (g : ℝ → ℝ) :
    ∫ x, ‖((g x : ℝ) : ℂ)‖ ^ 2 = autocorr g 0 := by
  unfold autocorr
  simp only [Complex.norm_real, Real.norm_eq_abs, add_zero, sq, abs_mul_abs_self]

theorem massOf_eq_linearCombination (c : WeilTestFn →₀ ℝ) :
    massOf c = linearCombination ℝ (fun f : WeilTestFn => ∫ x, ‖f.1 x‖ ^ 2) c := by
  rw [massOf, linearCombination_apply]
  simp only [smul_eq_mul]

theorem nodeVector_apply_eq_linearCombination (c : WeilTestFn →₀ ℝ) (j : LogIndex) :
    nodeVector c j = linearCombination ℝ (fun f : WeilTestFn => logValue f.1 j) c := by
  rw [nodeVector_eq, linearCombination_logVector_apply, linearCombination_apply]
  simp only [smul_eq_mul]

theorem linearCombination_pairSum (φ : WeilTestFn → ℝ) (a b : ℕ → WeilTestFn) (N : ℕ) :
    linearCombination ℝ φ
        (∑ k ∈ Finset.range N, (Finsupp.single (a k) (1 : ℝ) + Finsupp.single (b k) 1)) =
      ∑ k ∈ Finset.range N, (φ (a k) + φ (b k)) := by
  simp only [map_sum, map_add, linearCombination_single, one_smul]

/-- The cosine modulation `f(u) cos(ωu)` as a Weil test. -/
def cosTest {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (ω : ℝ) : WeilTestFn :=
  realTest (cosineSource f ω) (contDiff_cosineSource hf ω) hfc.mul_right

/-- The sine modulation `f(u) sin(ωu)` as a Weil test. -/
def sinTest {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (ω : ℝ) : WeilTestFn :=
  realTest (sineSource f ω) (contDiff_sineSource hf ω) hfc.mul_right

/-- Unit cosine/sine pairs at the frequencies `ω k`, `k < N`: the spectral measure
`Σ_k |f̂(· − ω_k)|²` symmetrized. -/
def pairCombination {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ω : ℕ → ℝ) (N : ℕ) : WeilTestFn →₀ ℝ :=
  ∑ k ∈ Finset.range N, (Finsupp.single (cosTest hf hfc (ω k)) 1 +
    Finsupp.single (sinTest hf hfc (ω k)) 1)

theorem pairCombination_nonneg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ω : ℕ → ℝ) (N : ℕ) (g : WeilTestFn) : 0 ≤ pairCombination hf hfc ω N g := by
  classical
  rw [pairCombination, Finsupp.finsetSum_apply]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> norm_num

theorem autocorr_cos_add_sin_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ω : ℝ) : autocorr (cosineSource f ω) 0 + autocorr (sineSource f ω) 0 = autocorr f 0 := by
  simpa only [mul_zero, Real.cos_zero, mul_one] using
    autocorr_cosineSource_add_sineSource hf.continuous hfc ω 0

theorem massOf_pairCombination {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ω : ℕ → ℝ) (N : ℕ) : massOf (pairCombination hf hfc ω N) = N * autocorr f 0 := by
  rw [massOf_eq_linearCombination, pairCombination, linearCombination_pairSum]
  simp only [cosTest, sinTest, realTest, integral_norm_sq_ofReal, autocorr_cos_add_sin_zero hf hfc,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem nodeVector_pairCombination {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ω : ℕ → ℝ) (N : ℕ) (j : LogIndex) :
    nodeVector (pairCombination hf hfc ω N) j =
      2 * autocorr f (Real.log (j : ℕ)) / Real.sqrt (j : ℕ) *
        ∑ k ∈ Finset.range N, Real.cos (ω k * Real.log (j : ℕ)) := by
  rw [nodeVector_apply_eq_linearCombination, pairCombination, linearCombination_pairSum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [cosTest, sinTest, logValue_realTest]
  have h := autocorr_cosineSource_add_sineSource hf.continuous hfc (ω k) (Real.log (j : ℕ))
  linear_combination (2 / Real.sqrt (j : ℕ)) * h

/-- The symbol of the pair combination is `h(0) Σ_k γ(ω_k)` up to the envelope energy per atom. -/
theorem nodeArchOnly_pairCombination_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (ω : ℕ → ℝ) (N : ℕ) :
    nodeArchOnly (pairCombination hf hfc ω N) ≤
      autocorr f 0 * ∑ k ∈ Finset.range N, EF.gammaBracket (ω k) + N * biScaleLevyEnergy f := by
  rw [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, pairCombination, linearCombination_pairSum,
    linearCombination_pairSum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  have hN : (N : ℝ) * biScaleLevyEnergy f =
      ∑ _k ∈ Finset.range N, biScaleLevyEnergy f := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hN, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 := archOnly_realTest (contDiff_cosineSource hf (ω k)) (hfc.mul_right (f' :=
    fun u => Real.cos (ω k * u)))
  have h2 := archOnly_realTest (contDiff_sineSource hf (ω k)) (hfc.mul_right (f' :=
    fun u => Real.sin (ω k * u)))
  have h3 := biScaleLevyEnergy_cosine_sine_eq hf hfc (ω k)
  have h4 : EF.gammaBracket 0 * autocorr (cosineSource f (ω k)) 0 +
      EF.gammaBracket 0 * autocorr (sineSource f (ω k)) 0 =
      EF.gammaBracket 0 * autocorr f 0 := by
    rw [← mul_add, autocorr_cos_add_sin_zero hf hfc]
  have h5 : autocorr f 0 * archFrequencyCost (ω k) =
      autocorr f 0 * EF.gammaBracket (ω k) - EF.gammaBracket 0 * autocorr f 0 := by
    rw [archFrequencyCost_eq_gammaBracket_sub_zero]; ring
  have h6 := (le_abs_self _).trans (abs_archEnvelopeError_le hf hfc (ω k))
  simp only [cosTest, sinTest] at *
  linarith

/-! ### 5. Attainment -/

/-- A uniform linear correlation increment bounds the energy of every dilation. -/
theorem biScaleLevyEnergy_sourceRescale_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {M : ℝ} (hM : ∀ x, autocorr f 0 - autocorr f x ≤ M * |x|)
    {δ : ℝ} (hδ : 0 < δ) : biScaleLevyEnergy (sourceRescale f δ) ≤ M * archWeightFirstMoment := by
  have hreg := contDiff_sourceRescale hf δ
  have hcomp := hasCompactSupport_sourceRescale hfc hδ
  have hmass : autocorr (sourceRescale f δ) 0 = δ⁻¹ * autocorr f 0 := by
    simpa only [mul_zero] using autocorr_sourceRescale f hδ 0
  unfold biScaleLevyEnergy archWeightFirstMoment
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_biScaleLevyIntegrand hreg hcomp)
    (integrableOn_mul_archLevySinhWeight.const_mul M) measurableSet_Ioi (fun x hx => ?_)
  rw [hmass, autocorr_sourceRescale f hδ]
  have hb := hM (δ * x)
  rw [abs_of_pos (mul_pos hδ hx)] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hδ).le
  have heq : δ⁻¹ * (M * (δ * x)) = M * x := by field_simp
  rw [heq] at hmul
  have hi : δ⁻¹ * autocorr f 0 - δ⁻¹ * autocorr f (δ * x) ≤ M * x := by
    simpa only [mul_sub] using hmul
  calc
    _ ≤ (M * x) * archLevySinhWeight x :=
      mul_le_mul_of_nonneg_right hi (archLevySinhWeight_pos hx).le
    _ = _ := by ring

/-- **The single-integer bathtub is attained at rate `O(1/N)`.** -/
theorem exists_blindOn_powers_archOnly_le {q : ℕ} (hq : 2 ≤ q) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N : ℕ, 1 ≤ N → ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      BlindOn (powerNodes q) c ∧ 0 < massOf c ∧
      nodeArchOnly c ≤ (symbolPeriodMean q + E / N) * massOf c := by
  set ℓ : ℝ := Real.log q with hℓdef
  have hℓ : 0 < ℓ := Real.log_pos (by exact_mod_cast hq)
  obtain ⟨Mb, hMb, hinc⟩ := exists_autocorr_increment_linear_bound contDiff_pairBump
    hasCompactSupport_pairBump
  have hb0 := autocorr_pairBump_zero_pos
  have hK0 : 0 ≤ Mb * archWeightFirstMoment := mul_nonneg hMb archWeightFirstMoment_nonneg
  have hγ : 0 ≤ EF.gammaBracket (π / ℓ) - EF.gammaBracket 0 := by
    have := gammaBracket_le_of_abs_le (s := 0) (r := π / ℓ)
      (by rw [abs_zero]; exact abs_nonneg _)
    linarith
  refine ⟨EF.gammaBracket (π / ℓ) - EF.gammaBracket 0 +
    Mb * archWeightFirstMoment / (8 * ℓ * autocorr pairBump 0), by positivity, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set δ : ℝ := 1 / (8 * N * ℓ) with hδdef
  have hδ : 0 < δ := by positivity
  have hf := contDiff_compressedBump δ
  have hfc := hasCompactSupport_compressedBump hδ
  have hf0 : autocorr (compressedBump δ) 0 = 8 * N * ℓ * autocorr pairBump 0 := by
    rw [autocorr_compressedBump_zero hδ, hδdef]; field_simp
  have hJ : biScaleLevyEnergy (compressedBump δ) ≤ Mb * archWeightFirstMoment :=
    biScaleLevyEnergy_sourceRescale_le contDiff_pairBump hasCompactSupport_pairBump hinc hδ
  set ω : ℕ → ℝ := fun k => ((k : ℝ) + 1 / 2) * (π / (N * ℓ)) with hω
  refine ⟨pairCombination hf hfc ω N, pairCombination_nonneg hf hfc ω N, fun j hj => ?_, ?_, ?_⟩
  · -- blindness at every power of `q`
    obtain ⟨i, hi1, hji⟩ := hj
    rw [nodeVector_pairCombination]
    have hlog : Real.log ((j : ℕ) : ℝ) = (i : ℝ) * ℓ := by
      rw [hji, Nat.cast_pow, Real.log_pow]
    rw [hlog]
    rcases lt_or_ge i (2 * N) with hiN | hiN
    · have e : ∀ k : ℕ, ω k * ((i : ℝ) * ℓ) = ((k : ℝ) + 1 / 2) * (π * i / N) := fun k => by
        rw [hω]; field_simp
      simp only [e]
      rw [sum_cos_midpoint_eq_zero hi1 hiN, mul_zero]
    · have hfar : 1 / (5 * δ) < |(i : ℝ) * ℓ| := by
        rw [abs_of_nonneg (by positivity), hδdef]
        have : (2 * N : ℝ) ≤ i := by exact_mod_cast hiN
        rw [show 1 / (5 * (1 / (8 * (N : ℝ) * ℓ))) = 8 / 5 * N * ℓ by field_simp]
        nlinarith
      rw [autocorr_compressedBump_eq_zero hδ hfar]
      simp
  · rw [massOf_pairCombination, hf0]; positivity
  · have harch := nodeArchOnly_pairCombination_le hf hfc ω N
    have hsum := sum_gammaBracket_midpoint_le hℓ hN
    rw [massOf_pairCombination]
    have hsum' : autocorr (compressedBump δ) 0 * ∑ k ∈ Finset.range N, EF.gammaBracket (ω k) ≤
        autocorr (compressedBump δ) 0 * (N * symbolPeriodMean q +
          (EF.gammaBracket (π / ℓ) - EF.gammaBracket 0)) :=
      mul_le_mul_of_nonneg_left hsum (autocorr_zero_nonneg _)
    have hJN := mul_le_mul_of_nonneg_left hJ hNpos.le
    have e : (symbolPeriodMean q + (EF.gammaBracket (π / ℓ) - EF.gammaBracket 0 +
        Mb * archWeightFirstMoment / (8 * ℓ * autocorr pairBump 0)) / N) *
          (N * autocorr (compressedBump δ) 0) =
        autocorr (compressedBump δ) 0 * (N * symbolPeriodMean q +
          (EF.gammaBracket (π / ℓ) - EF.gammaBracket 0)) + N * (Mb * archWeightFirstMoment) := by
      rw [hf0]; field_simp; ring
    rw [e]
    linarith

/-! ### 6. Pole mass at small cost and small mass -/

theorem massOf_single (f : WeilTestFn) (t : ℝ) :
    massOf (Finsupp.single f t) = t * ∫ x, ‖f.1 x‖ ^ 2 := by
  rw [massOf_eq_linearCombination, linearCombination_single, smul_eq_mul]

theorem massOf_add (c d : WeilTestFn →₀ ℝ) : massOf (c + d) = massOf c + massOf d := by
  simp only [massOf_eq_linearCombination, map_add]

theorem integral_norm_sq_distantPairTest {σ T : ℝ} (hσ : σ ^ 2 = 1) (hT : 1 ≤ T) :
    ∫ x, ‖(distantPairTest σ T).1 x‖ ^ 2 = 2 * autocorr pairBump 0 := by
  change ∫ x, ‖((distantPair σ T x : ℝ) : ℂ)‖ ^ 2 = _
  rw [integral_norm_sq_ofReal, autocorr_subtractCopy contDiff_pairBump.continuous
    hasCompactSupport_pairBump, zero_sub, zero_add, autocorr_neg,
    autocorr_pairBump_eq_zero (x := T) (by rw [abs_of_pos (by linarith)]; linarith), hσ]
  ring

/-- **Pole mass is free, with small mass.** On a gapped node set every pole mass `p` is carried
by a nonnegative `𝒩`-blind combination whose archimedean part without the pole and whose mass are
both at most `ε`. -/
theorem exists_blindOn_poleMass_eq_small {𝒩 : Set ℕ} (h𝒩 : GappedNodeSet 𝒩) (p : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ d f) ∧ BlindOn 𝒩 d ∧ nodePoleMass d = p ∧
      |nodeArchOnly d| ≤ ε ∧ massOf d ≤ ε := by
  classical
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, fun _ => le_rfl, fun j _ => by simp [nodeVector_eq], by simp [nodePoleMass],
      by simp [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, hε.le],
      by simp [massOf_eq_linearCombination, hε.le]⟩
  set σ : ℝ := if 0 < p then -1 else 1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by rw [hσdef]; split_ifs <;> simp
  have hσsq : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  set m : ℝ := pairMoment (1 / 2) * pairMoment (-(1 / 2)) with hmdef
  have hm : 0 < m := mul_pos (pairMoment_pos _) (pairMoment_pos _)
  set κ : ℝ := 2 * (1 - Real.exp (-(1 / 2))) * m with hκ
  have hκpos : 0 < κ := by
    have : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    rw [hκ]; nlinarith
  have hb0 := autocorr_pairBump_zero_pos
  set B : ℝ := pairArchBound + 2 * autocorr pairBump 0 with hB
  have hA0 : 0 ≤ pairArchBound :=
    (abs_nonneg _).trans (abs_archOnly_distantPairTest_le (σ := 1) (T := 2) (by norm_num) le_rfl)
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  set R : ℝ := 2 * Real.log (1 + (|p| * B / ε + 1) / κ) + 2 with hR
  obtain ⟨T, hRT, hgap⟩ := h𝒩 R
  have hq0 : 0 ≤ (|p| * B / ε + 1) / κ := by positivity
  have hlogpos : 0 ≤ Real.log (1 + (|p| * B / ε + 1) / κ) := Real.log_nonneg (by linarith)
  have hT2 : 2 ≤ T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hexp : 1 + (|p| * B / ε + 1) / κ ≤ Real.exp ((1 / 2) * T) := by
    rw [← Real.exp_log (show 0 < 1 + (|p| * B / ε + 1) / κ by positivity)]
    exact Real.exp_le_exp.mpr (by linarith)
  set P : ℝ := (weilPoleTerm (EF.weilTest (distantPairTest σ T).1 (distantPairTest σ T).1)).re
    with hPdef
  have hPabs : |p| * B / ε + 1 ≤ |P| := by
    have h1 := abs_pole_distantPairTest_ge hσ hT1
    have h1' : κ * (Real.exp ((1 / 2) * T) - 1) ≤ |P| := by
      have e : κ * (Real.exp ((1 / 2) * T) - 1) = 2 * (1 - Real.exp (-(1 / 2))) *
          (Real.exp ((1 / 2) * T) - 1) * (pairMoment (1 / 2) * pairMoment (-(1 / 2))) := by
        rw [hκ, hmdef]; ring
      rw [e]; exact h1
    have h3 : (|p| * B / ε + 1) / κ ≤ Real.exp ((1 / 2) * T) - 1 := by linarith
    have h2 := (div_le_iff₀ hκpos).mp h3
    linarith
  have hPpos : 0 < |P| := by
    have : 0 ≤ |p| * B / ε := by positivity
    linarith
  have hP0 : P ≠ 0 := abs_pos.mp hPpos
  have hsign : 0 < p / P := by
    rcases lt_or_gt_of_ne hp with hneg | hpos
    · have hσ1 : σ = 1 := by rw [hσdef, if_neg (not_lt.mpr hneg.le)]
      have hPneg : P < 0 := by rw [hPdef, hσ1]; exact pole_distantPairTest_neg (by linarith)
      exact div_pos_of_neg_of_neg hneg hPneg
    · have hσ1 : σ = -1 := by rw [hσdef, if_pos hpos]
      have hPpos' : 0 < P := by rw [hPdef, hσ1]; exact pole_distantPairTest_pos T
      exact div_pos hpos hPpos'
  -- the weight times `B` is at most `ε`
  have htB : p / P * B ≤ ε := by
    have habs : p / P = |p| / |P| := by rw [← abs_div, abs_of_pos hsign]
    rw [habs, div_mul_eq_mul_div, div_le_iff₀ hPpos]
    have := mul_le_mul_of_nonneg_left hPabs hε.le
    have hB' : |p| * B = ε * (|p| * B / ε) := by field_simp
    nlinarith
  refine ⟨Finsupp.single (distantPairTest σ T) (p / P), fun f => ?_, fun j hj => ?_, ?_, ?_, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> [exact hsign.le; exact le_rfl]
  · rw [nodeVector_single_apply, logValue_distantPair_eq_zero σ hT1 j.2 (hgap j hj j.2), mul_zero]
  · rw [nodePoleMass_single, ← hPdef, div_mul_cancel₀ _ hP0]
  · rw [nodeArchOnly_single, abs_mul, abs_of_pos hsign]
    have hA := abs_archOnly_distantPairTest_le hσsq hT2
    calc
      _ ≤ p / P * pairArchBound := mul_le_mul_of_nonneg_left hA hsign.le
      _ ≤ p / P * B := mul_le_mul_of_nonneg_left (by rw [hB]; linarith) hsign.le
      _ ≤ ε := htB
  · rw [massOf_single, integral_norm_sq_distantPairTest hσsq hT1]
    calc
      _ ≤ p / P * B := mul_le_mul_of_nonneg_left (by rw [hB]; linarith) hsign.le
      _ ≤ ε := htB

/-! ### 7. The exact slack -/

/-- Below `−m_q` the zero-pole slack fails on the powers of `q`. -/
theorem le_of_zeroPoleBlindSymbolSlackOn_powers {q : ℕ} (hq : 2 ≤ q) {M : ℝ}
    (h : ZeroPoleBlindSymbolSlackOn (powerNodes q) M) : -symbolPeriodMean q ≤ M := by
  by_contra hlt
  rw [not_le] at hlt
  set g : ℝ := -symbolPeriodMean q - M with hg
  have hgpos : 0 < g := by linarith
  obtain ⟨E, hE, hup⟩ := exists_blindOn_powers_archOnly_le hq
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * E / g)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hN1 : 1 ≤ N := by exact_mod_cast hN0
  obtain ⟨c₁, hc₁, hb₁, hm₁, ha₁⟩ := hup N hN1
  have hEN : E / N ≤ g / 2 := by
    rw [div_le_iff₀ hN0]
    rw [div_lt_iff₀ hgpos] at hN
    linarith
  set η : ℝ := g / 2 * massOf c₁ / (4 * (1 + |M|)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨d, hd, hbd, hpd, had, hmd⟩ :=
    exists_blindOn_poleMass_eq_small (gappedNodeSet_powers hq) (-nodePoleMass c₁) hηpos
  have hcd : ∀ f, 0 ≤ (c₁ + d) f := fun f => by
    rw [Finsupp.add_apply]; exact add_nonneg (hc₁ f) (hd f)
  have hbcd : BlindOn (powerNodes q) (c₁ + d) := fun j hj => by
    rw [nodeVector_add, Finsupp.add_apply, hb₁ j hj, hbd j hj, add_zero]
  have hpcd : nodePoleMass (c₁ + d) = 0 := by rw [nodePoleMass_add, hpd, add_neg_cancel]
  have hpos := h (c₁ + d) hcd hbcd hpcd
  have hE' : nodeArchEnergy (c₁ + d) = nodeArchOnly c₁ + nodeArchOnly d := by
    rw [← nodeArchOnly_add, nodeArchOnly, hpcd, sub_zero]
  rw [hE', massOf_add] at hpos
  have hmd0 : 0 ≤ massOf d := massOf_nonneg hd
  have h1 : nodeArchOnly c₁ ≤ (symbolPeriodMean q + g / 2) * massOf c₁ :=
    ha₁.trans (mul_le_mul_of_nonneg_right (by linarith) hm₁.le)
  have h2 : nodeArchOnly d ≤ η := (le_abs_self _).trans had
  have h3 : M * massOf d ≤ |M| * η :=
    (mul_le_mul_of_nonneg_right (le_abs_self M) hmd0).trans
      (mul_le_mul_of_nonneg_left hmd (abs_nonneg M))
  have h4 : (1 + |M|) * η = g / 2 * massOf c₁ / 4 := by
    rw [hη]; field_simp
  have hMg : M = -symbolPeriodMean q - g := by rw [hg]; ring
  have : nodeArchOnly c₁ + nodeArchOnly d + M * (massOf c₁ + massOf d) ≤
      -(g / 2) * massOf c₁ + g / 2 * massOf c₁ / 4 := by
    rw [mul_add]
    have : M * massOf c₁ = (-symbolPeriodMean q - g) * massOf c₁ := by rw [hMg]
    nlinarith
  have hneg : -(g / 2) * massOf c₁ + g / 2 * massOf c₁ / 4 < 0 := by
    have := mul_pos hgpos hm₁
    nlinarith
  linarith

/-- **The zero-pole blind symbol slack on the powers of `q` is exactly `−m_q`.** -/
theorem zeroPoleBlindSymbolSlackOn_powers_iff {q : ℕ} (hq : 2 ≤ q) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn (powerNodes q) M ↔ -symbolPeriodMean q ≤ M :=
  ⟨le_of_zeroPoleBlindSymbolSlackOn_powers hq,
    fun h => ((blindSymbolSlackOn_powers hq).mono h).zeroPole⟩

/-- **The blind symbol slack on the powers of `q` is exactly `−m_q`.** -/
theorem blindSymbolSlackOn_powers_iff {q : ℕ} (hq : 2 ≤ q) (M : ℝ) :
    BlindSymbolSlackOn (powerNodes q) M ↔ -symbolPeriodMean q ≤ M :=
  ⟨fun h => le_of_zeroPoleBlindSymbolSlackOn_powers hq h.zeroPole,
    fun h => (blindSymbolSlackOn_powers hq).mono h⟩

/-- **The pole constraint does not improve a single-integer bathtub.** -/
theorem zeroPoleBlindSymbolSlackOn_powers_iff_blind {q : ℕ} (hq : 2 ≤ q) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn (powerNodes q) M ↔ BlindSymbolSlackOn (powerNodes q) M := by
  rw [zeroPoleBlindSymbolSlackOn_powers_iff hq, blindSymbolSlackOn_powers_iff hq]

/-- The corpus dyadic constant `m₂` is the exact zero-pole slack on the powers of `2`. -/
theorem zeroPoleBlindSymbolSlackOn_two_powers_iff (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn (powerNodes 2) M ↔ -twoPeriodMean ≤ M := by
  rw [zeroPoleBlindSymbolSlackOn_powers_iff le_rfl, symbolPeriodMean_two]

/-! ### 8. The prime `2` leaves the smallest gap -/

/-- The mean of `γ` over `[0, a]` increases with `a`. -/
theorem mean_gammaBracket_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a⁻¹ * ∫ v in (0 : ℝ)..a, EF.gammaBracket v ≤ b⁻¹ * ∫ v in (0 : ℝ)..b, EF.gammaBracket v := by
  have hb : 0 < b := ha.trans_le hab
  have hs : ∀ c : ℝ, 0 < c →
      c⁻¹ * ∫ v in (0 : ℝ)..c, EF.gammaBracket v = ∫ t in (0 : ℝ)..1, EF.gammaBracket (c * t) := by
    intro c hc
    rw [intervalIntegral.integral_comp_mul_left (fun v => EF.gammaBracket v) hc.ne', mul_zero,
      mul_one, smul_eq_mul]
  rw [hs a ha, hs b hb]
  refine intervalIntegral.integral_mono_on zero_le_one
    ((WeilHerglotz.continuous_gammaBracket.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    ((WeilHerglotz.continuous_gammaBracket.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    fun t ht => gammaBracket_le_of_abs_le ?_
  rw [abs_of_nonneg (mul_nonneg ha.le ht.1), abs_of_nonneg (mul_nonneg hb.le ht.1)]
  exact mul_le_mul_of_nonneg_right hab ht.1

/-- `m_q ≤ m₂`: the powers of `2` give the smallest single-integer slack `−m₂`. -/
theorem symbolPeriodMean_le_two {q : ℕ} (hq : 2 ≤ q) : symbolPeriodMean q ≤ symbolPeriodMean 2 := by
  have hℓ2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hℓq : Real.log 2 ≤ Real.log q :=
    Real.log_le_log two_pos (by exact_mod_cast hq)
  have hℓ : 0 < Real.log q := hℓ2.trans_le hℓq
  have hmono := mean_gammaBracket_mono (a := π / Real.log q) (b := π / Real.log 2)
    (by positivity) (div_le_div_of_nonneg_left Real.pi_pos.le hℓ2 hℓq)
  rw [inv_div, inv_div] at hmono
  simp only [symbolPeriodMean, Nat.cast_ofNat]
  exact hmono

end

end GaloisForLFunctions.BiScaleUncertainty
