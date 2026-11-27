import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Classification
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SignedPartialSumClassificationAndReflectedSieve
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubFarkasZeroFreeHalfPlane
import GaloisForLFunctions.RHTower.ThetaNaturalScheduleEulerOscillation
import GaloisForLFunctions.RHTower.PrimeHigherMertensRate
import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation
import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.FermiMellinPhaseProperness
import GaloisForLFunctions.InfiniteRankPurityTheory.TheZerosContainNoClassOfOneFrobenius

/-!
# Off-Critical Fourier Rigidity of `bornLaw`, Second-Order Logarithmic Dispersion, Zero-Blind Smooth Approximation, and Sharp Sub-Lorentzian Equivalence Above Height `184`

For `σ, t ∈ ℝ` and `k ∈ ℤ`, let `bornCoefficient σ t k N` be the `k`-th circle Fourier mode
`circleMeasureMomentZ (bornLaw σ t N : MeasureTheory.Measure Circle) k` of the `p^{-2σ}`-weighted
prime-phase ensemble `bornLaw σ t N`. While `CriticalBorn.nonzero_mode` gives
`bornCoefficient (1 / 2) t k N → 0` for `t ≠ 0`, `k ≠ 0`, attacking off-critical single-mode
suppression at a hypothetical left-hand zero `ρ` above height `184` (`0 < Re ρ < 1 / 2`,
`184 < |Im ρ|`, `riemannZeta ρ = 0`) exposes an exact phase-transition hierarchy:

1. **Exact subcritical rotating-phasor and Lorentzian modulus law (`0 < σ < 1 / 2`, all `k ∈ ℤ`)**:
   `subcritical_bornCoefficient_rotating_phasor` proves
   `bornCoefficient σ t k N - ((1 - 2σ) / ((1 - 2σ) + i k t)) · (phase t (N + 2))^{-k} → 0`
   as `N → ∞`, so `‖bornCoefficient σ t k N‖` converges unconditionally
   (`subcritical_norm_bornCoefficient_tendsto`) to the positive Lorentzian
   `bornLorentzianLimit σ t k = (1 - 2σ) / √((1 - 2σ)² + (k t)²) > 0`, and no mode can vanish
   along any unbounded cutoff subsequence (`subcritical_no_subseq_zero_mode`).
2. **Super-polylogarithmic zero-blind smooth approximation and exact second-order logarithmic
   dispersion (`0 < σ < 1 / 2`)**:
   * `subcritical_bornCoefficient_sub_smooth_superPolyLog` proves that for **every** `A : ℕ`,
     `(log(N + 2))^A · ‖bornCoefficient σ t k N - smoothBornCoefficient σ t k N‖ → 0`, where
     `smoothBornCoefficient` depends only on `p = 2` and deterministic logarithmic integrals (and
     is completely independent of primes `> 2` and all zeros of `riemannZeta`): every explicit-formula
     zero contribution is trapped inside `o((log N)^{-A})`.
   * `subcritical_norm_bornCoefficient_log_deficit` proves unconditionally that
     `log(N + 2) · (bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖)` converges to the exact
     dispersion constant `bornLogDispersionCoeff σ t k = (k t)² / √((1 - 2σ)² + (k t)²)³`.
   * Consequently, whenever `t ≠ 0` and `k ≠ 0`, `subcritical_eventually_norm_lt_lorentzian` shows
     that `‖bornCoefficient σ t k N‖ < bornLorentzianLimit σ t k` holds **at all sufficiently large
     cutoffs `N`** (with deficit `≥ (bornLogDispersionCoeff σ t k / 2) / log(N + 2) > 0`) **without**
     `riemannZeta ρ = 0`, whereas `subcritical_no_subseq_superDispersion_deficit` proves that **no**
     unbounded cutoff sequence `φ` can achieve a deficit `C / log(φ j + 2)` for any
     `C > bornLogDispersionCoeff σ t k`.
3. **Supercritical prime-Dirichlet limit and Dirichlet-pigeonhole Bohr recurrence (`σ > 1 / 2`)**:
   `supercritical_bornCoefficient_tendsto` and `supercritical_exists_high_mode_re_gt` establish
   convergence to `supercriticalModeLimit σ t k` and existence of arbitrarily high modes `k > K₀`
   with `1 - ε < (supercriticalModeLimit σ t k).re` at every `t ∈ ℝ`.
4. **Unconditional zero exclusion on `(0, 2401 / 19200)` and sharp critical-constant equivalence
   with `RiemannHypothesis` above height `184`**:
   * `unconditional_bornCoefficient_zero_through_oneHundredEightyFour_and_sub_farkas` establishes
     unconditional vanishing of every nonzero `bornCoefficient` at all strip zeros through height
     `184` (`|Im ρ| ≤ 184`) and unconditional zero-freeness of `riemannZeta` across **all** heights
     on `0 < Re s < 2401 / 19200` and `16799 / 19200 < Re s` (excluding left-hand zeros below
     `2401 / 19200` above height `184`).
   * `rh_iff_single_mode_subLorentzian_above_oneHundredEightyFour` proves that for any fixed
     `k₀ ≠ 0`, `RiemannHypothesis` is unconditionally equivalent to: (i) full-sequence cancellation
     of all nonzero modes at strip zeros, (ii) subsequential cancellation of the single mode `k₀`
     at each zero's self-clock `t = ρ.im`, (iii) a uniform sub-Lorentzian bound `≤ c < L` along
     arbitrarily large cutoffs on `2401 / 19200 ≤ Re ρ < 1 / 2`, `184 < |Im ρ|`, and (iv) a
     super-dispersion logarithmic deficit `≤ L - C / log(φ j + 2)` (`C > bornLogDispersionCoeff`)
     along arbitrarily large cutoffs on `2401 / 19200 ≤ Re ρ < 1 / 2`, `184 < |Im ρ|`.
   * `fermiMellin_fundamental_cancels_but_overtones_survive` contrasts this with the pole-cancelled
     Fermi–Mellin observer law, where `riemannZeta ρ = 0` genuinely annihilates `k = ±1` at
     arbitrary `Re ρ ∈ (0, 1)` while leaving infinitely many overtones `|k| > K₀` nonzero.
-/

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset MeasureTheory Real
open GaloisForLFunctions.HTGeometry
open scoped Topology BigOperators

attribute [-instance]
  GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.HeckeTauberian.instMeasurableSpace

private theorem re_ofReal_add_ofReal_mul_I (a b : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by simp

private theorem im_ofReal_add_ofReal_mul_I (a b : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by simp

/-! ### Part 1: Fourier modes of `bornLaw` across general real exponents `σ` -/

private theorem bornWeight_nonneg' (σ : ℝ) (p : ℕ) : 0 ≤ bornWeight σ p :=
  Real.rpow_nonneg (Nat.cast_nonneg p) _

private theorem bornMass_pos' (σ : ℝ) (N : ℕ) : 0 < bornMass σ N := by
  apply sum_pos' (fun p _ => bornWeight_nonneg' σ p)
  exact ⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩,
    Real.rpow_pos_of_pos (by norm_num) _⟩

/-- The `k`-th circle Fourier mode `∫ z^{-k} d(bornLaw σ t N)` of the `p^{-2σ}`-weighted prime
phase ensemble at clock height `t` and cutoff index `N`. -/
def bornCoefficient (σ t : ℝ) (k : ℤ) (N : ℕ) : ℂ :=
  circleMeasureMomentZ (bornLaw σ t N).toMeasure k

/-- Explicit normalized prime-sum representation of `bornCoefficient σ t k N`. -/
theorem bornCoefficient_eq_sum (σ t : ℝ) (k : ℤ) (N : ℕ) :
    bornCoefficient σ t k N =
      (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) / (bornMass σ N : ℂ) := by
  rw [bornCoefficient, circleMeasureMomentZ]
  change (∫ z : Circle, (z : ℂ) ^ (-k) ∂(∑ p ∈ primes N,
    (Real.toNNReal (bornWeight σ p / bornMass σ N)) • MeasureTheory.Measure.dirac (phase t p))) = _
  rw [integral_finsetSum_measure (fun _ _ =>
    (integrable_dirac (by finiteness)).smul_measure_nnreal), Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_nnreal_measure, integral_dirac]
  change ((Real.toNNReal (bornWeight σ p / bornMass σ N) : ℝ) : ℂ) * (phase t p : ℂ) ^ (-k) = _
  rw [Real.coe_toNNReal _ (div_nonneg (bornWeight_nonneg' σ p) (bornMass_pos' σ N).le),
    Complex.ofReal_div]
  ring

theorem bornCoefficient_zero_mode (σ t : ℝ) (N : ℕ) : bornCoefficient σ t 0 N = 1 :=
  circleMeasureMomentZ_zero (bornLaw σ t N).toMeasure

theorem bornCoefficient_half (t : ℝ) (k : ℤ) (N : ℕ) :
    bornCoefficient (1 / 2) t k N = coefficient t k N := by
  rw [bornCoefficient, bornLaw_half]
  exact moment t N k

/-- Weak convergence of `bornLaw σ t` to `uniform` is equivalent to cancellation of every nonzero
Fourier mode `k ≠ 0`. -/
theorem tendsto_bornLaw_uniform_iff_forall_nonzero_mode (σ t : ℝ) :
    Tendsto (bornLaw σ t) atTop (𝓝 uniform) ↔
      ∀ k : ℤ, k ≠ 0 → Tendsto (bornCoefficient σ t k) atTop (𝓝 0) := by
  rw [isClosedEmbedding_completeCircleMomentSequence.isEmbedding.tendsto_nhds_iff, tendsto_pi_nhds]
  have haar : ∀ k : ℤ,
      circleMeasureMomentZ uniform.toMeasure k = if k = 0 then 1 else 0 := by
    intro k
    change circleMeasureMomentZ circleLebesgue k = _
    simp only [circleMeasureMomentZ, integral_circleLebesgue_coe_zpow, neg_eq_zero]
  constructor
  · intro h k hk
    have hk_lim := h k
    change Tendsto (bornCoefficient σ t k) atTop
      (𝓝 (circleMeasureMomentZ uniform.toMeasure k)) at hk_lim
    rwa [haar k, if_neg hk] at hk_lim
  · intro h k
    change Tendsto (bornCoefficient σ t k) atTop
      (𝓝 (circleMeasureMomentZ uniform.toMeasure k))
    rw [haar k]
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, show bornCoefficient σ t 0 = fun _ => (1 : ℂ) from
        funext (bornCoefficient_zero_mode σ t)]
      exact tendsto_const_nhds
    · rw [if_neg hk]
      exact h k hk

/-! ### Part 2: Subcritical rotating-phasor law, zero-blind super-polylogarithmic smooth approximation, and exact second-order logarithmic dispersion (`0 < σ < 1 / 2`) -/

/-- Positive Lorentzian limiting modulus `(1 - 2σ) / √((1 - 2σ)² + (k t)²)` for `0 < σ < 1 / 2`. -/
def bornLorentzianLimit (σ t : ℝ) (k : ℤ) : ℝ :=
  (1 - 2 * σ) / Real.sqrt ((1 - 2 * σ) ^ 2 + ((k : ℝ) * t) ^ 2)

/-- Exact second-order logarithmic dispersion deficit coefficient
`(k t)² / √((1 - 2σ)² + (k t)²)³` governing `bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖`. -/
def bornLogDispersionCoeff (σ t : ℝ) (k : ℤ) : ℝ :=
  ((k : ℝ) * t) ^ 2 / Real.sqrt ((1 - 2 * σ) ^ 2 + ((k : ℝ) * t) ^ 2) ^ 3

/-- Zero-blind smooth analytic approximation to `∑_{p < N+3} p^{-s}`, built solely from `p = 2`
and continuous logarithmic integrals (independent of primes `> 2` and all zeros of `riemannZeta`). -/
def smoothPrimeSum (s : ℂ) (x : ℝ) : ℂ :=
  (2 : ℂ) ^ (-s) + (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ)) -
    _root_.RHTower.primeCpowAbelWeight s 2 * (Chebyshev.theta 2 : ℂ) -
    s / (1 - s) * _root_.RHTower.primeCpowAbelPrimitive s 2 +
    1 / (1 - s) * _root_.RHTower.primeCpowLogSqIntegral s x

/-- Zero-blind smooth analytic counterpart of `bornCoefficient σ t k N`. -/
def smoothBornCoefficient (σ t : ℝ) (k : ℤ) (N : ℕ) : ℂ :=
  smoothPrimeSum (((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * Complex.I) ((N + 2 : ℕ) : ℝ) /
    smoothPrimeSum ((2 * σ : ℝ) : ℂ) ((N + 2 : ℕ) : ℝ)

private theorem bornSummand_eq_cpow (σ t : ℝ) (k : ℤ) {p : ℕ} (hp : 0 < p) :
    (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k) =
      (p : ℂ) ^ (-(((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)) := by
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [bornWeight, Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp, phase, Circle.coe_exp,
    ← Complex.exp_int_mul, ← Complex.exp_add, Complex.cpow_def_of_ne_zero hp_ne]
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hp_pos.le]
  rw [hlog]
  congr 1
  push_cast
  ring

private theorem primes_eq_insert_two_Ioc (N : ℕ) :
    primes N = insert 2 ((Finset.Ioc 2 (N + 2)).filter Nat.Prime) := by
  ext p
  simp only [primes, Nat.mem_primesBelow, mem_insert, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨hlt, hp⟩
    by_cases h2 : p = 2
    · exact Or.inl h2
    · exact Or.inr ⟨⟨by have := hp.two_le; omega, by omega⟩, hp⟩
  · rintro (rfl | ⟨⟨_, hle⟩, hp⟩)
    · exact ⟨by omega, Nat.prime_two⟩
    · exact ⟨by omega, hp⟩

private theorem primeSum_eq_two_add_primeCpowSumIoc (σ t : ℝ) (k : ℤ) (N : ℕ) :
    (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) =
      (2 : ℂ) ^ (-(((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)) +
        _root_.RHTower.primeCpowSumIoc
          (((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * Complex.I) ((N + 2 : ℕ) : ℝ) := by
  rw [primes_eq_insert_two_Ioc N, Finset.sum_insert (by simp)]
  congr 1
  · exact bornSummand_eq_cpow σ t k (by norm_num)
  · rw [_root_.RHTower.primeCpowSumIoc, Nat.floor_natCast, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.Prime
    · rw [if_pos hp, if_pos hp]
      exact bornSummand_eq_cpow σ t k hp.pos
    · rw [if_neg hp, if_neg hp]

private theorem cpow_one_sub_div_rpow (a t : ℝ) (k : ℤ) (N : ℕ) :
    (((N + 2 : ℕ) : ℝ) : ℂ) ^ ((a : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I) =
      ((((N + 2 : ℕ) : ℝ) ^ a : ℝ) : ℂ) * (phase t (N + 2) : ℂ) ^ (-k) := by
  set x : ℝ := ((N + 2 : ℕ) : ℝ)
  have hx_pos : 0 < x := by positivity
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  rw [Complex.cpow_def_of_ne_zero hx_ne, ← Complex.ofReal_log hx_pos.le,
    Real.rpow_def_of_pos hx_pos, Complex.ofReal_exp, phase, Circle.coe_exp,
    ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  dsimp only [x]
  push_cast
  ring

/-- **Exact subcritical rotating-phasor asymptotic:** for every `0 < σ < 1 / 2`, every clock `t ∈ ℝ`,
and every Fourier index `k ∈ ℤ`, `bornCoefficient σ t k N` tracks the rotating terminal cutoff phase
`((1 - 2σ) / ((1 - 2σ) + i k t)) · (phase t (N + 2))^{-k}` up to `o(1)` as `N → ∞`. -/
theorem subcritical_bornCoefficient_rotating_phasor {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (t : ℝ) (k : ℤ) :
    Tendsto (fun N : ℕ =>
      bornCoefficient σ t k N -
        (((1 - 2 * σ : ℝ) : ℂ) /
          (((1 - 2 * σ : ℝ) : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)) *
          (phase t (N + 2) : ℂ) ^ (-k)) atTop (𝓝 0) := by
  set a : ℝ := 1 - 2 * σ with ha_def
  have ha0 : 0 < a := by linarith only [ha_def, hσ1]
  have ha1 : a < 1 := by linarith only [ha_def, hσ0]
  set s : ℂ := ((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * Complex.I with hs_def
  have hs_re : s.re = 2 * σ := by
    simp only [hs_def, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    ring
  have hs0 : 0 < s.re := by linarith only [hs_re, hσ0]
  have hs1 : s.re < 1 := by linarith only [hs_re, hσ1]
  have h1s_eq : (1 : ℂ) - s = (a : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I := by
    rw [hs_def, ha_def]; push_cast; ring
  have h1s_re : 1 - s.re = a := by linarith only [hs_re, ha_def]
  set c : ℂ := (a : ℂ) / (1 - s)
  let x : ℕ → ℝ := fun N => ((N + 2 : ℕ) : ℝ)
  have hx_top : Tendsto x atTop atTop := by
    simpa only [x, Nat.cast_add, Nat.cast_ofNat] using
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hmain_ioc : Tendsto (fun N : ℕ =>
      ‖_root_.RHTower.primeCpowSumIoc s (x N) -
          (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ))‖ *
        (a * Real.log (x N)) / (x N) ^ a) atTop (𝓝 0) := by
    have h0 := (_root_.RHTower.tendsto_primeCpowSumIoc_sub_main hs0 hs1).comp hx_top
    have hm := h0.const_mul a
    rw [mul_zero] at hm
    refine hm.congr fun N => ?_
    dsimp only [Function.comp_apply]
    rw [h1s_re]
    ring
  have htwo_tiny : Tendsto (fun N : ℕ =>
      ‖(2 : ℂ) ^ (-s)‖ * (a * Real.log (x N)) / (x N) ^ a) atTop (𝓝 0) := by
    have hlog := ((isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero).comp hx_top
    have hm := hlog.const_mul (‖(2 : ℂ) ^ (-s)‖ * a)
    rw [mul_zero] at hm
    exact hm.congr fun N => by dsimp only [Function.comp_apply]; ring
  let A : ℕ → ℂ := fun N =>
    (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) *
      (((a * Real.log (x N) / (x N) ^ a : ℝ) : ℂ))
  let u : ℕ → ℂ := fun N => c * (phase t (N + 2) : ℂ) ^ (-k)
  let R : ℕ → ℝ := fun N => bornMass σ N * (a * Real.log (x N)) / (x N) ^ a
  have hR_lim : Tendsto R atTop (𝓝 1) := by
    have hm := (powerMass_asymptotic ha0 ha1).comp hx_top
    refine hm.congr fun N => ?_
    dsimp only [Function.comp_apply, R, x]
    have hcut : cutoff ((N + 2 : ℕ) : ℝ) = N := by
      unfold cutoff; rw [Nat.floor_natCast]; omega
    rw [powerMass, hcut, bornMass]
    have hsum_eq : (∑ p ∈ primes N, (p : ℝ) ^ (a - 1)) = ∑ p ∈ primes N, bornWeight σ p :=
      Finset.sum_congr rfl fun p _ => by
        rw [bornWeight, show a - 1 = -(2 * σ) by linarith only [ha_def]]
    rw [hsum_eq]
  have hA_sub_u : Tendsto (fun N : ℕ => ‖A N - u N‖) atTop (𝓝 0) := by
    have hsum_lim := htwo_tiny.add hmain_ioc
    rw [add_zero] at hsum_lim
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hsum_lim
    have hx_gt1 : 1 < x N := by dsimp only [x]; exact_mod_cast (by omega : 1 < N + 2)
    have hlog_pos : 0 < Real.log (x N) := Real.log_pos hx_gt1
    have hlog_ne : (Real.log (x N) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog_pos.ne'
    have hxa_pos : 0 < (x N) ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans hx_gt1) a
    have hxa_ne : (((x N) ^ a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxa_pos.ne'
    have hscale_pos : 0 ≤ a * Real.log (x N) / (x N) ^ a := by positivity
    have h1s_ne : (1 : ℂ) - s ≠ 0 := by
      rw [h1s_eq]; intro h0
      have hr := congrArg Complex.re h0
      rw [re_ofReal_add_ofReal_mul_I, Complex.zero_re] at hr
      exact ha0.ne' hr
    have hu_eq : u N = ((x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ))) *
        (((a * Real.log (x N) / (x N) ^ a : ℝ) : ℂ)) := by
      dsimp only [u, c, x]
      rw [h1s_eq, cpow_one_sub_div_rpow a t k N, ← h1s_eq, Complex.ofReal_div, Complex.ofReal_mul]
      set P_a : ℂ := (((((N + 2 : ℕ) : ℝ) ^ a : ℝ) : ℂ))
      set L_c : ℂ := (Real.log ((N + 2 : ℕ) : ℝ) : ℂ)
      set ph : ℂ := (phase t (N + 2) : ℂ) ^ (-k)
      set w_c : ℂ := 1 - s
      field_simp [hlog_ne, hxa_ne, h1s_ne]
    have hdiff : A N - u N =
        ((2 : ℂ) ^ (-s) +
          (_root_.RHTower.primeCpowSumIoc s (x N) -
            (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ)))) *
          (((a * Real.log (x N) / (x N) ^ a : ℝ) : ℂ)) := by
      dsimp only [A, x]
      rw [primeSum_eq_two_add_primeCpowSumIoc, ← hs_def]
      dsimp only [x] at hu_eq
      rw [hu_eq]
      ring
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hscale_pos]
    calc ‖(2 : ℂ) ^ (-s) + (_root_.RHTower.primeCpowSumIoc s (x N) -
            (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ)))‖ *
            (a * Real.log (x N) / (x N) ^ a)
        ≤ (‖(2 : ℂ) ^ (-s)‖ + ‖_root_.RHTower.primeCpowSumIoc s (x N) -
            (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ))‖) *
            (a * Real.log (x N) / (x N) ^ a) :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hscale_pos
      _ = ‖(2 : ℂ) ^ (-s)‖ * (a * Real.log (x N)) / (x N) ^ a +
          ‖_root_.RHTower.primeCpowSumIoc s (x N) -
            (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ))‖ *
            (a * Real.log (x N)) / (x N) ^ a := by ring
  have hmaj : Tendsto (fun N : ℕ => (‖A N - u N‖ + ‖c‖ * |1 - R N|) / |R N|) atTop (𝓝 0) := by
    have h1R : Tendsto (fun N => |1 - R N|) atTop (𝓝 0) := by
      have hs1 := ((tendsto_const_nhds (x := (1 : ℝ))).sub hR_lim).abs
      rwa [sub_self, abs_zero] at hs1
    have hnum := hA_sub_u.add (h1R.const_mul ‖c‖)
    rw [mul_zero, add_zero] at hnum
    have hden : Tendsto (fun N => |R N|) atTop (𝓝 1) := by
      have ha1 := hR_lim.abs
      rwa [abs_one] at ha1
    have hq := hnum.div hden one_ne_zero
    rw [zero_div] at hq
    exact hq
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmaj
  have hx_gt1 : 1 < x N := by dsimp only [x]; exact_mod_cast (by omega : 1 < N + 2)
  have hlog_pos : 0 < Real.log (x N) := Real.log_pos hx_gt1
  have hxa_pos : 0 < (x N) ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans hx_gt1) a
  have hsc_ne : (((a * Real.log (x N) / (x N) ^ a : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos (mul_pos ha0 hlog_pos) hxa_pos).ne'
  have hbm_pos := bornMass_pos' σ N
  have hR_pos : 0 < R N := div_pos (mul_pos hbm_pos (mul_pos ha0 hlog_pos)) hxa_pos
  have hR_ne : (R N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR_pos.ne'
  have hquot : bornCoefficient σ t k N = A N / (R N : ℂ) := by
    rw [bornCoefficient_eq_sum]
    dsimp only [A, R]
    have hR_eq : (((bornMass σ N * (a * Real.log (x N)) / (x N) ^ a : ℝ) : ℂ)) =
        (bornMass σ N : ℂ) * (((a * Real.log (x N) / (x N) ^ a : ℝ) : ℂ)) := by
      push_cast; ring
    rw [hR_eq, mul_div_mul_right _ _ hsc_ne]
  have hc_eq : (((1 - 2 * σ : ℝ) : ℂ) /
      (((1 - 2 * σ : ℝ) : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)) *
      (phase t (N + 2) : ℂ) ^ (-k) = u N := by
    dsimp only [u, c]; rw [h1s_eq, ha_def]
  rw [hquot, hc_eq]
  have halg : A N / (R N : ℂ) - u N = ((A N - u N) + u N * (1 - (R N : ℂ))) / (R N : ℂ) := by
    set an := A N; set un := u N; set rn : ℂ := (R N : ℂ)
    field_simp [hR_ne]; ring
  have hu_norm : ‖u N‖ = ‖c‖ := by
    dsimp only [u]
    rw [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one]
  rw [halg, norm_div, Complex.norm_real]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  calc ‖(A N - u N) + u N * (1 - (R N : ℂ))‖
      ≤ ‖A N - u N‖ + ‖u N * (1 - (R N : ℂ))‖ := norm_add_le _ _
    _ = ‖A N - u N‖ + ‖c‖ * |1 - R N| := by
        rw [norm_mul, hu_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]

/-- **Exact subcritical Lorentzian modulus law:** for every `0 < σ < 1 / 2`, every `t ∈ ℝ`, and
every `k ∈ ℤ`, `‖bornCoefficient σ t k N‖` converges as `N → ∞` to `bornLorentzianLimit σ t k`. -/
theorem subcritical_norm_bornCoefficient_tendsto {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (t : ℝ) (k : ℤ) :
    Tendsto (fun N : ℕ => ‖bornCoefficient σ t k N‖) atTop
      (𝓝 (bornLorentzianLimit σ t k)) := by
  set a : ℝ := 1 - 2 * σ with ha_def
  set ω : ℝ := (k : ℝ) * t with hω_def
  have ha0 : 0 < a := by linarith only [ha_def, hσ1]
  set c : ℂ := (a : ℂ) / ((a : ℂ) + (ω : ℂ) * Complex.I)
  have hc_norm : ‖c‖ = bornLorentzianLimit σ t k := by
    dsimp only [c]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha0.le,
      Complex.norm_eq_sqrt_sq_add_sq, re_ofReal_add_ofReal_mul_I, im_ofReal_add_ofReal_mul_I,
      bornLorentzianLimit, ← ha_def, ← hω_def]
  have hphasor := (subcritical_bornCoefficient_rotating_phasor hσ0 hσ1 t k).norm
  rw [norm_zero] at hphasor
  rw [← hc_norm, ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun N => ?_) hphasor
  have hu_norm : ‖c * (phase t (N + 2) : ℂ) ^ (-k)‖ = ‖c‖ := by
    rw [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one]
  rw [Real.norm_eq_abs, ← hu_norm]
  exact abs_norm_sub_norm_le (bornCoefficient σ t k N) (c * (phase t (N + 2) : ℂ) ^ (-k))

/-- Below `σ = 1 / 2`, no Fourier mode `k ∈ ℤ` can vanish along **any** unbounded subsequence of
cutoffs `φ : ℕ → ℕ`. -/
theorem subcritical_no_subseq_zero_mode {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (t : ℝ) (k : ℤ) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    ¬ Tendsto (fun j : ℕ => bornCoefficient σ t k (φ j)) atTop (𝓝 0) := by
  intro hzero
  have hnorm0 : Tendsto (fun j : ℕ => ‖bornCoefficient σ t k (φ j)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hzero.norm
  have hnormL := (subcritical_norm_bornCoefficient_tendsto hσ0 hσ1 t k).comp hφ
  have heq := tendsto_nhds_unique hnorm0 hnormL
  have hpos : 0 < bornLorentzianLimit σ t k :=
    div_pos (by linarith only [hσ1])
      (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith only [hσ1]))
        (sq_nonneg _)))
  linarith only [heq, hpos]

private theorem tendsto_log_pow_mul_abs_thetaError (A : ℕ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A * |_root_.RHTower.thetaError x|) atTop (𝓝 0) := by
  obtain ⟨D, c, T, hc0, _, hT4, _, herr⟩ := _root_.RHTower.exists_pntErrorEnvelope
  have hsqrt_top : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop := by
    have hsqrt_id : Tendsto Real.sqrt atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨(max b 0) ^ 2, fun u hu => ?_⟩
      have hb0 : 0 ≤ max b 0 := le_max_right b 0
      calc b ≤ max b 0 := le_max_left b 0
        _ = Real.sqrt ((max b 0) ^ 2) := (Real.sqrt_sq hb0).symm
        _ ≤ Real.sqrt u := Real.sqrt_le_sqrt hu
    exact hsqrt_id.comp Real.tendsto_log_atTop
  have hpow_exp : Tendsto (fun x : ℝ =>
      D * ((Real.sqrt (Real.log x)) ^ ((2 * A : ℕ) : ℝ) *
        Real.exp (-c * Real.sqrt (Real.log x)))) atTop (𝓝 0) := by
    have h0 := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2 * A : ℕ) : ℝ) c hc0).comp
      hsqrt_top).const_mul D
    rw [mul_zero] at h0
    exact h0
  have h_nonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ (Real.log x) ^ A * |_root_.RHTower.thetaError x| := by
    filter_upwards [eventually_ge_atTop T] with x hx
    exact mul_nonneg (pow_nonneg (Real.log_nonneg (by linarith only [hT4, hx])) _) (abs_nonneg _)
  refine squeeze_zero' h_nonneg ?_ hpow_exp
  filter_upwards [eventually_ge_atTop T] with x hx
  have hlog_pos : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hT4, hx])
  have hpow_eq : (Real.log x) ^ A = (Real.sqrt (Real.log x)) ^ ((2 * A : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, pow_mul, Real.sq_sqrt hlog_pos]
  rw [hpow_eq]
  have hb := herr x hx
  calc (Real.sqrt (Real.log x)) ^ ((2 * A : ℕ) : ℝ) * |_root_.RHTower.thetaError x|
      ≤ (Real.sqrt (Real.log x)) ^ ((2 * A : ℕ) : ℝ) *
          (D * Real.exp (-c * Real.sqrt (Real.log x))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = D * ((Real.sqrt (Real.log x)) ^ ((2 * A : ℕ) : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log x))) := by ring

private theorem tendsto_log_pow_div_rpow_atTop (B : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => (Real.log x) ^ B / x ^ a) atTop (𝓝 0) := by
  by_cases hB : B = 0
  · subst hB
    have h0 := tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop ha)
    exact h0.congr fun x => by dsimp only [Function.comp_apply]; rw [pow_zero, one_div]
  · have hB_pos : 0 < (B : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hB)
    have hbase := _root_.RHTower.tendsto_log_div_rpow_atTop (ha := div_pos ha hB_pos)
    have hpow := hbase.pow B
    rw [zero_pow hB] at hpow
    refine hpow.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_pow, ← Real.rpow_natCast (x ^ (a / (B : ℝ))) B, ← Real.rpow_mul hx.le,
      div_mul_cancel₀ a hB_pos.ne']

private theorem rpow_integral_le {a : ℝ} (ha : 0 < a) {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (IntervalIntegrable (fun t : ℝ => t ^ (a - 1)) volume u v) ∧
      (∫ t in u..v, t ^ (a - 1)) ≤ v ^ a / a := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (a - 1)) volume u v :=
    (ContinuousOn.rpow_const (fun _ _ => continuousWithinAt_id) fun t ht =>
      Or.inl (by rw [Set.mem_Icc] at ht; change t ≠ 0; linarith only [hu, ht.1])).intervalIntegrable_of_Icc huv
  refine ⟨hint, ?_⟩
  have hderiv : ∀ t ∈ Set.uIcc u v, HasDerivAt (fun y : ℝ => y ^ a / a) (t ^ (a - 1)) t := by
    intro t ht
    rw [Set.uIcc_of_le huv] at ht
    have ht0 : 0 < t := by linarith only [hu, ht.1]
    have hd := (Real.hasDerivAt_rpow_const (p := a) (Or.inl ht0.ne')).div_const a
    rwa [mul_div_cancel_left₀ _ ha.ne'] at hd
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hu_pos : 0 ≤ u ^ a / a := div_nonneg (Real.rpow_nonneg (by linarith only [hu]) a) ha.le
  linarith only [hu_pos]

private theorem tendsto_thetaRemainder_superPolyLog {s : ℂ} (_hσ0 : 0 < s.re) (hσ1 : s.re < 1)
    (A : ℕ) :
    Tendsto (fun x : ℝ =>
      ‖_root_.RHTower.primeCpowAbelPrimitive s x * (_root_.RHTower.thetaError x : ℂ) -
        ∫ t in (2 : ℝ)..x, (_root_.RHTower.thetaError t : ℂ) *
          _root_.RHTower.primeCpowAbelKernel s t‖ *
        (Real.log x) ^ (A + 1) / x ^ (1 - s.re)) atTop (𝓝 0) := by
  set a : ℝ := 1 - s.re with ha_def
  have ha : 0 < a := by linarith only [ha_def, hσ1]
  set Cs : ℝ := ‖s‖ + 1 / Real.log 2
  have hCs : 0 < Cs := add_pos_of_nonneg_of_pos (norm_nonneg _)
    (div_pos zero_lt_one (Real.log_pos (by norm_num)))
  have hterm1 : Tendsto (fun x : ℝ =>
      ‖_root_.RHTower.primeCpowAbelPrimitive s x * (_root_.RHTower.thetaError x : ℂ)‖ *
        (Real.log x) ^ (A + 1) / x ^ a) atTop (𝓝 0) := by
    refine (tendsto_log_pow_mul_abs_thetaError A).congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hx1 : 1 < x := by linarith only [hx]
    have hlog_ne : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    have hxa_ne : x ^ a ≠ 0 := (Real.rpow_pos_of_pos (by linarith only [hx]) a).ne'
    rw [norm_mul, _root_.RHTower.norm_primeCpowAbelPrimitive hx1, Complex.norm_real,
      Real.norm_eq_abs, ← ha_def, pow_succ]
    set L : ℝ := Real.log x
    set P : ℝ := x ^ a
    set E : ℝ := |_root_.RHTower.thetaError x|
    field_simp [hlog_ne, hxa_ne]
  have he_small := (tendsto_log_pow_mul_abs_thetaError (A + 1)).eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp he_small
  set T : ℝ := max T₀ 4
  have hT4 : 4 ≤ T := le_max_right T₀ 4
  have hT2 : 2 ≤ T := by linarith only [hT4]
  have hT_pos : 0 < T := by linarith only [hT4]
  have hT_sq_ge16 : 16 ≤ T ^ 2 := by
    have : (4 : ℝ) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by norm_num) hT4 2
    linarith only [this]
  have hT_bound : ∀ t : ℝ, T ≤ t → |_root_.RHTower.thetaError t| ≤ 1 / (Real.log t) ^ (A + 1) := by
    intro t ht
    have ht0 : T₀ ≤ t := (le_max_left T₀ 4).trans ht
    have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith only [hT4, ht])
    exact (le_div_iff₀' (pow_pos hlog_pos _)).mpr (hT₀ t ht0).le
  set I_init : ℝ := ∫ t in (2 : ℝ)..T,
    ‖(_root_.RHTower.thetaError t : ℂ) * _root_.RHTower.primeCpowAbelKernel s t‖
  set C_top_const : ℝ := (2 : ℝ) ^ (A + 2) * Cs / a
  have hmaj2 : Tendsto (fun x : ℝ =>
      |I_init| * ((Real.log x) ^ (A + 1) / x ^ a) +
        (Cs / a) * ((Real.log x) ^ (A + 1) / x ^ (a / 2)) +
        C_top_const * (1 / Real.log x)) atTop (𝓝 0) := by
    have h1 := (tendsto_log_pow_div_rpow_atTop (A + 1) ha).const_mul |I_init|
    have h2 := (tendsto_log_pow_div_rpow_atTop (A + 1) (half_pos ha)).const_mul (Cs / a)
    have h3 : Tendsto (fun x : ℝ => C_top_const * (1 / Real.log x)) atTop (𝓝 0) := by
      have h0 := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul C_top_const
      rw [mul_zero] at h0
      exact h0.congr fun x => by dsimp only [Function.comp_apply]; rw [one_div]
    have hsum := (h1.add h2).add h3
    simpa only [mul_zero, add_zero] using hsum
  have hterm2_nonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ ‖∫ t in (2 : ℝ)..x, (_root_.RHTower.thetaError t : ℂ) *
          _root_.RHTower.primeCpowAbelKernel s t‖ *
        (Real.log x) ^ (A + 1) / x ^ a := by
    filter_upwards [eventually_ge_atTop (T ^ 2)] with x hx
    have hx16 : 16 ≤ x := hT_sq_ge16.trans hx
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx16])
    have hx0 : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith only [hx16]) a
    exact div_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hlog0 _)) hx0
  have hterm2 : Tendsto (fun x : ℝ =>
      ‖∫ t in (2 : ℝ)..x, (_root_.RHTower.thetaError t : ℂ) *
          _root_.RHTower.primeCpowAbelKernel s t‖ *
        (Real.log x) ^ (A + 1) / x ^ a) atTop (𝓝 0) := by
    refine squeeze_zero' hterm2_nonneg ?_ hmaj2
    filter_upwards [eventually_ge_atTop (T ^ 2)] with x hx
    have hx_ge16 : 16 ≤ x := hT_sq_ge16.trans hx
    have hx_pos : 0 < x := by linarith only [hx_ge16]
    have hsqrt_ge_T : T ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq hT_pos.le]; exact Real.sqrt_le_sqrt hx
    have hsqrt_le_x : Real.sqrt x ≤ x := by
      have h1 : 1 ≤ Real.sqrt x := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith only [hx_ge16])
      calc Real.sqrt x = 1 * Real.sqrt x := (one_mul _).symm
        _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg x)
        _ = x := Real.mul_self_sqrt hx_pos.le
    have hx2 : 2 ≤ x := by linarith only [hx_ge16]
    have hsqrt2 : 2 ≤ Real.sqrt x := hT2.trans hsqrt_ge_T
    have hint_norm : ∀ b : ℝ, 2 ≤ b →
        IntervalIntegrable (fun t : ℝ =>
          ‖(_root_.RHTower.thetaError t : ℂ) * _root_.RHTower.primeCpowAbelKernel s t‖) volume 2 b :=
      fun b hb => (_root_.RHTower.intervalIntegrable_thetaError_mul_primeCpowAbelKernel s hb).norm
    have hint_T_sqrt : IntervalIntegrable (fun t : ℝ =>
        ‖(_root_.RHTower.thetaError t : ℂ) * _root_.RHTower.primeCpowAbelKernel s t‖)
        volume T (Real.sqrt x) :=
      (hint_norm x hx2).mono_set (by
        rw [Set.uIcc_of_le hsqrt_ge_T, Set.uIcc_of_le hx2]
        exact Set.Icc_subset_Icc hT2 hsqrt_le_x)
    have hint_sqrt_x : IntervalIntegrable (fun t : ℝ =>
        ‖(_root_.RHTower.thetaError t : ℂ) * _root_.RHTower.primeCpowAbelKernel s t‖)
        volume (Real.sqrt x) x :=
      (hint_norm x hx2).mono_set (by
        rw [Set.uIcc_of_le hsqrt_le_x, Set.uIcc_of_le hx2]
        exact Set.Icc_subset_Icc hsqrt2 le_rfl)
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals (hint_norm T hT2) hint_T_sqrt
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hint_norm (Real.sqrt x) hsqrt2)
      hint_sqrt_x
    obtain ⟨hrpow_mid_int, hrpow_mid_le⟩ := rpow_integral_le ha hT2 hsqrt_ge_T
    obtain ⟨hrpow_top_int, hrpow_top_le⟩ := rpow_integral_le ha hsqrt2 hsqrt_le_x
    have hmid_le : (∫ t in T..(Real.sqrt x),
        ‖(_root_.RHTower.thetaError t : ℂ) * _root_.RHTower.primeCpowAbelKernel s t‖) ≤
        Cs * (x ^ (a / 2) / a) := by
      have hmono := intervalIntegral.integral_mono_on hsqrt_ge_T hint_T_sqrt
        (hrpow_mid_int.const_mul Cs)
        (fun t ht => by
          have ht2 : 2 ≤ t := hT2.trans ht.1
          have hlog1 : 1 ≤ Real.log t := by
            have hexp4 : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; linarith
            have := Real.log_le_log (Real.exp_pos 1) (hexp4.trans (hT4.trans ht.1))
            rwa [Real.log_exp] at this
          have he1 : |_root_.RHTower.thetaError t| ≤ 1 :=
            (hT_bound t ht.1).trans (div_le_one_of_le₀ (one_le_pow₀ hlog1) (by positivity))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hK := _root_.RHTower.norm_primeCpowAbelKernel_le s ht2
          rw [show -s.re = a - 1 by linarith only [ha_def]] at hK
          have hdiv_le : t ^ (a - 1) / Real.log t ≤ t ^ (a - 1) :=
            div_le_self (Real.rpow_nonneg (by linarith only [ht2]) _) hlog1
          calc |_root_.RHTower.thetaError t| * ‖_root_.RHTower.primeCpowAbelKernel s t‖
              ≤ 1 * (Cs * (t ^ (a - 1) / Real.log t)) :=
                mul_le_mul he1 hK (norm_nonneg _) zero_le_one
            _ ≤ Cs * t ^ (a - 1) := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hdiv_le hCs.le)
      rw [intervalIntegral.integral_const_mul] at hmono
      have hsq_pow : (Real.sqrt x) ^ a = x ^ (a / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx_pos.le, show (1 / 2 : ℝ) * a = a / 2 by ring]
      exact hmono.trans (mul_le_mul_of_nonneg_left (hsq_pow ▸ hrpow_mid_le) hCs.le)
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith only [hx_ge16])
    have htop_le : (∫ t in (Real.sqrt x)..x,
        ‖(_root_.RHTower.thetaError t : ℂ) * _root_.RHTower.primeCpowAbelKernel s t‖) ≤
        ((2 : ℝ) ^ (A + 2) * Cs / (Real.log x) ^ (A + 2)) * (x ^ a / a) := by
      set K_top : ℝ := (2 : ℝ) ^ (A + 2) * Cs / (Real.log x) ^ (A + 2)
      have hK_top_nonneg : 0 ≤ K_top :=
        div_nonneg (mul_nonneg (pow_nonneg zero_le_two _) hCs.le) (pow_nonneg hlogx_pos.le _)
      have hmono := intervalIntegral.integral_mono_on hsqrt_le_x hint_sqrt_x
        (hrpow_top_int.const_mul K_top)
        (fun t ht => by
          have htT : T ≤ t := hsqrt_ge_T.trans ht.1
          have ht2 : 2 ≤ t := hT2.trans htT
          have hlog_half : Real.log x / 2 ≤ Real.log t := by
            have h1 := Real.log_le_log (Real.sqrt_pos.mpr hx_pos) ht.1
            rwa [Real.log_sqrt hx_pos.le] at h1
          have hlogt_pos : 0 < Real.log t := lt_of_lt_of_le (half_pos hlogx_pos) hlog_half
          have he_t := hT_bound t htT
          have hK := _root_.RHTower.norm_primeCpowAbelKernel_le s ht2
          rw [show -s.re = a - 1 by linarith only [ha_def]] at hK
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hpow_le : (Real.log x / 2) ^ (A + 2) ≤ (Real.log t) ^ (A + 2) :=
            pow_le_pow_left₀ (half_pos hlogx_pos).le hlog_half (A + 2)
          have hinv_le : 1 / (Real.log t) ^ (A + 2) ≤ (2 : ℝ) ^ (A + 2) / (Real.log x) ^ (A + 2) := by
            have h1 := one_div_le_one_div_of_le (pow_pos (half_pos hlogx_pos) (A + 2)) hpow_le
            rwa [div_pow, one_div_div] at h1
          calc |_root_.RHTower.thetaError t| * ‖_root_.RHTower.primeCpowAbelKernel s t‖
              ≤ (1 / (Real.log t) ^ (A + 1)) * (Cs * (t ^ (a - 1) / Real.log t)) :=
                mul_le_mul he_t hK (norm_nonneg _)
                  (div_nonneg zero_le_one (pow_nonneg hlogt_pos.le _))
            _ = Cs * (1 / (Real.log t) ^ (A + 2)) * t ^ (a - 1) := by
                rw [pow_succ]; ring
            _ ≤ Cs * ((2 : ℝ) ^ (A + 2) / (Real.log x) ^ (A + 2)) * t ^ (a - 1) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv_le hCs.le)
                  (Real.rpow_nonneg (by linarith only [ht2]) _)
            _ = K_top * t ^ (a - 1) := by dsimp only [K_top]; ring)
      rw [intervalIntegral.integral_const_mul] at hmono
      exact hmono.trans (mul_le_mul_of_nonneg_left hrpow_top_le hK_top_nonneg)
    have htotal_int : ‖∫ t in (2 : ℝ)..x, (_root_.RHTower.thetaError t : ℂ) *
        _root_.RHTower.primeCpowAbelKernel s t‖ ≤
        |I_init| + Cs * (x ^ (a / 2) / a) +
          ((2 : ℝ) ^ (A + 2) * Cs / (Real.log x) ^ (A + 2)) * (x ^ a / a) := by
      calc ‖∫ t in (2 : ℝ)..x, (_root_.RHTower.thetaError t : ℂ) *
              _root_.RHTower.primeCpowAbelKernel s t‖
          ≤ ∫ t in (2 : ℝ)..x, ‖(_root_.RHTower.thetaError t : ℂ) *
              _root_.RHTower.primeCpowAbelKernel s t‖ :=
            intervalIntegral.norm_integral_le_integral_norm hx2
        _ = I_init + (∫ t in T..(Real.sqrt x),
              ‖(_root_.RHTower.thetaError t : ℂ) * _root_.RHTower.primeCpowAbelKernel s t‖) +
            (∫ t in (Real.sqrt x)..x,
              ‖(_root_.RHTower.thetaError t : ℂ) * _root_.RHTower.primeCpowAbelKernel s t‖) := by
            rw [← hsplit2, ← hsplit1]
        _ ≤ |I_init| + Cs * (x ^ (a / 2) / a) +
              ((2 : ℝ) ^ (A + 2) * Cs / (Real.log x) ^ (A + 2)) * (x ^ a / a) := by
            linarith only [le_abs_self I_init, hmid_le, htop_le]
    have hxa_pos : 0 < x ^ a := Real.rpow_pos_of_pos hx_pos a
    have hx_half_eq : x ^ (a / 2) / x ^ a = 1 / x ^ (a / 2) := by
      rw [div_eq_iff hxa_pos.ne', div_mul_eq_mul_div, one_mul,
        eq_div_iff (Real.rpow_pos_of_pos hx_pos _).ne', ← Real.rpow_add hx_pos, add_halves]
    have hlog_div : (Real.log x) ^ (A + 1) / (Real.log x) ^ (A + 2) = 1 / Real.log x := by
      rw [pow_succ (Real.log x) (A + 1), ← div_div, div_self (pow_pos hlogx_pos _).ne']
    have hscale_nonneg : 0 ≤ (Real.log x) ^ (A + 1) / x ^ a :=
      div_nonneg (pow_nonneg hlogx_pos.le _) hxa_pos.le
    set J_norm : ℝ := ‖∫ t in (2 : ℝ)..x, (_root_.RHTower.thetaError t : ℂ) *
      _root_.RHTower.primeCpowAbelKernel s t‖
    set L1 : ℝ := (Real.log x) ^ (A + 1)
    set L2 : ℝ := (Real.log x) ^ (A + 2)
    set P1 : ℝ := x ^ a
    set P_half : ℝ := x ^ (a / 2)
    set P2_pow : ℝ := (2 : ℝ) ^ (A + 2)
    have hstep1 : J_norm * L1 / P1 ≤
        (|I_init| + Cs * (P_half / a) + (P2_pow * Cs / L2) * (P1 / a)) * (L1 / P1) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right htotal_int hscale_nonneg
    have hstep2 : (|I_init| + Cs * (P_half / a) + (P2_pow * Cs / L2) * (P1 / a)) * (L1 / P1) =
        |I_init| * (L1 / P1) + (Cs / a) * (L1 * (P_half / P1)) +
          (P2_pow * Cs / a) * (L1 / L2) * (P1 / P1) := by ring
    rw [hstep2, hx_half_eq, hlog_div, div_self hxa_pos.ne', mul_one, mul_one_div] at hstep1
    exact hstep1
  have h_final_nonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ ‖_root_.RHTower.primeCpowAbelPrimitive s x * (_root_.RHTower.thetaError x : ℂ) -
        ∫ t in (2 : ℝ)..x, (_root_.RHTower.thetaError t : ℂ) *
          _root_.RHTower.primeCpowAbelKernel s t‖ *
        (Real.log x) ^ (A + 1) / x ^ (1 - s.re) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
    have hx0 : 0 ≤ x ^ (1 - s.re) := Real.rpow_nonneg (by linarith only [hx]) _
    exact div_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hlog0 _)) hx0
  have hsum_zero : Tendsto (fun x : ℝ =>
      ‖_root_.RHTower.primeCpowAbelPrimitive s x * (_root_.RHTower.thetaError x : ℂ)‖ *
        (Real.log x) ^ (A + 1) / x ^ a +
      ‖∫ t in (2 : ℝ)..x, (_root_.RHTower.thetaError t : ℂ) *
          _root_.RHTower.primeCpowAbelKernel s t‖ *
        (Real.log x) ^ (A + 1) / x ^ a) atTop (𝓝 0) := by
    simpa only [add_zero] using hterm1.add hterm2
  refine squeeze_zero' h_final_nonneg ?_ hsum_zero
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hlog0 : 0 ≤ (Real.log x) ^ (A + 1) := pow_nonneg (Real.log_nonneg (by linarith only [hx])) _
  have hxa0 : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith only [hx]) a
  calc ‖_root_.RHTower.primeCpowAbelPrimitive s x * (_root_.RHTower.thetaError x : ℂ) -
          ∫ t in (2 : ℝ)..x, (_root_.RHTower.thetaError t : ℂ) *
            _root_.RHTower.primeCpowAbelKernel s t‖ * (Real.log x) ^ (A + 1) / x ^ a
      ≤ (‖_root_.RHTower.primeCpowAbelPrimitive s x * (_root_.RHTower.thetaError x : ℂ)‖ +
          ‖∫ t in (2 : ℝ)..x, (_root_.RHTower.thetaError t : ℂ) *
            _root_.RHTower.primeCpowAbelKernel s t‖) * (Real.log x) ^ (A + 1) / x ^ a :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (norm_sub_le _ _) hlog0) hxa0
    _ = _ := by ring

private theorem tendsto_primeCpowLogSqIntegral_sub_main {s : ℂ} (_hσ0 : 0 < s.re) (hσ1 : s.re < 1) :
    Tendsto (fun x : ℝ =>
      ‖_root_.RHTower.primeCpowLogSqIntegral s x -
        (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ) ^ 2)‖ *
        (Real.log x) ^ 2 / x ^ (1 - s.re)) atTop (𝓝 0) := by
  set a : ℝ := 1 - s.re with ha_def
  have ha : 0 < a := by linarith only [ha_def, hσ1]
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hσ1; exact lt_irrefl 1 hσ1
  have h1s_ne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  let P2 : ℝ → ℂ := fun t => _root_.RHTower.primeCpowAbelPrimitive s t / (Real.log t : ℂ)
  have hP2_eq : ∀ t : ℝ, P2 t = (t : ℂ) ^ (1 - s) / (Real.log t : ℂ) ^ 2 := fun t => by
    dsimp only [P2, _root_.RHTower.primeCpowAbelPrimitive]; rw [div_div, sq]
  have hP2_deriv : ∀ t : ℝ, 1 < t →
      HasDerivAt P2
        ((1 - s) * ((t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2) -
          2 * ((t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3)) t := by
    intro t ht1
    have ht0 : 0 < t := zero_lt_one.trans ht1
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hlog_ne : (Real.log t : ℂ) ≠ 0 := _root_.RHTower.ofReal_log_ne_zero_of_one_lt ht1
    have hd1 := _root_.RHTower.hasDerivAt_primeCpowAbelPrimitive hs1 ht1
    have hd2 : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((t⁻¹ : ℝ) : ℂ) t :=
      (Real.hasDerivAt_log ht0.ne').ofReal_comp
    refine (hd1.div hd2 hlog_ne).congr_deriv ?_
    have hprim_t : _root_.RHTower.primeCpowAbelPrimitive s t * ((t⁻¹ : ℝ) : ℂ) =
        (t : ℂ) ^ (-s) / (Real.log t : ℂ) := by
      rw [_root_.RHTower.primeCpowAbelPrimitive, show (1 : ℂ) - s = -s + 1 by ring,
        Complex.cpow_add _ _ htc, Complex.cpow_one, div_mul_eq_mul_div, mul_assoc,
        ← Complex.ofReal_mul, mul_inv_cancel₀ ht0.ne', Complex.ofReal_one, mul_one]
    rw [hprim_t]
    set z : ℂ := (t : ℂ) ^ (-s)
    set L : ℂ := (Real.log t : ℂ)
    field_simp [hlog_ne]
    ring
  have hcont3 : ∀ x : ℝ, ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3)
      (Set.Icc 2 x) := fun x =>
    (_root_.RHTower.continuousOn_ofReal_cpow_Icc (-s)).div
      (_root_.RHTower.continuousOn_ofReal_log_Icc.pow 3)
      (fun _ ht => pow_ne_zero 3 (_root_.RHTower.log_ne_zero_of_mem_Icc ht))
  have hibp : ∀ x : ℝ, 2 ≤ x →
      _root_.RHTower.primeCpowLogSqIntegral s x -
        (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ) ^ 2) =
        -(P2 2 / (1 - s)) +
          (2 / (1 - s)) * ∫ t in (2 : ℝ)..x, (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3 := by
    intro x hx2
    have hI2 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2) volume 2 x :=
      _root_.RHTower.continuousOn_cpow_div_log_sq.intervalIntegrable_of_Icc hx2
    have hI3 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3) volume 2 x :=
      (hcont3 x).intervalIntegrable_of_Icc hx2
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hP2_deriv t (by rw [Set.uIcc_of_le hx2] at ht; linarith only [ht.1]))
      ((hI2.const_mul (1 - s)).sub (hI3.const_mul 2))
    rw [intervalIntegral.integral_sub (hI2.const_mul (1 - s)) (hI3.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
    change (1 - s) * _root_.RHTower.primeCpowLogSqIntegral s x -
      2 * (∫ t in (2 : ℝ)..x, (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3) = P2 x - P2 2 at hftc
    have hx_term : P2 x / (1 - s) = (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ) ^ 2) := by
      rw [hP2_eq x, div_div, mul_comm ((Real.log x : ℂ) ^ 2) (1 - s)]
    rw [← hx_term]
    set J2 : ℂ := _root_.RHTower.primeCpowLogSqIntegral s x
    set J3 : ℂ := ∫ t in (2 : ℝ)..x, (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3
    set p2x : ℂ := P2 x
    set p22 : ℂ := P2 2
    set w : ℂ := 1 - s
    have hw : w ≠ 0 := h1s_ne
    field_simp [hw]
    linear_combination hftc
  have hmaj : Tendsto (fun x : ℝ =>
      ‖P2 2 / (1 - s)‖ * ((Real.log x) ^ 2 / x ^ a) +
        (‖2 / (1 - s)‖ / (a * (Real.log 2) ^ 3)) * ((Real.log x) ^ 2 / x ^ (a / 2)) +
        (8 * ‖2 / (1 - s)‖ / a) * (1 / Real.log x)) atTop (𝓝 0) := by
    have h1 := (tendsto_log_pow_div_rpow_atTop 2 ha).const_mul ‖P2 2 / (1 - s)‖
    have h2 := (tendsto_log_pow_div_rpow_atTop 2 (half_pos ha)).const_mul
      (‖2 / (1 - s)‖ / (a * (Real.log 2) ^ 3))
    have h3 : Tendsto (fun x : ℝ => (8 * ‖2 / (1 - s)‖ / a) * (1 / Real.log x)) atTop (𝓝 0) := by
      have h0 := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (8 * ‖2 / (1 - s)‖ / a)
      rw [mul_zero] at h0
      exact h0.congr fun x => by dsimp only [Function.comp_apply]; rw [one_div]
    simpa only [mul_zero, add_zero] using (h1.add h2).add h3
  have h_nonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ ‖_root_.RHTower.primeCpowLogSqIntegral s x -
        (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ) ^ 2)‖ *
        (Real.log x) ^ 2 / x ^ (1 - s.re) := by
    filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
    have hxpos : 0 ≤ x ^ (1 - s.re) := Real.rpow_nonneg (by linarith only [hx]) _
    exact div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) hxpos
  refine squeeze_zero' h_nonneg ?_ hmaj
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
  have hx_pos : 0 < x := by linarith only [hx]
  have hx2 : 2 ≤ x := by linarith only [hx]
  have hsqrt_ge2 : 2 ≤ Real.sqrt x := by
    have h4 : (2 : ℝ) = Real.sqrt 4 := by norm_num
    rw [h4]; exact Real.sqrt_le_sqrt (by linarith only [hx])
  have hsqrt_le_x : Real.sqrt x ≤ x := by
    have h1 : 1 ≤ Real.sqrt x := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith only [hx])
    calc Real.sqrt x = 1 * Real.sqrt x := (one_mul _).symm
      _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg x)
      _ = x := Real.mul_self_sqrt hx_pos.le
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  obtain ⟨hrpow_low_int, hrpow_low_le⟩ := rpow_integral_le ha le_rfl hsqrt_ge2
  obtain ⟨hrpow_high_int, hrpow_high_le⟩ := rpow_integral_le ha hsqrt_ge2 hsqrt_le_x
  have hnorm3 : ∀ t : ℝ, 2 ≤ t →
      ‖(t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖ = t ^ (a - 1) / (Real.log t) ^ 3 := by
    intro t ht2
    have ht1 : 1 < t := by linarith only [ht2]
    rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht1),
      Complex.norm_real, Real.norm_of_nonneg (Real.log_pos ht1).le, Complex.neg_re,
      show -s.re = a - 1 by linarith only [ha_def]]
  have hint_all : ∀ u v : ℝ, 2 ≤ u → u ≤ v →
      IntervalIntegrable (fun t : ℝ => ‖(t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖) volume u v :=
    fun u v hu huv => ((hcont3 v).norm.mono (Set.Icc_subset_Icc hu le_rfl)).intervalIntegrable_of_Icc huv
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint_all 2 (Real.sqrt x) le_rfl hsqrt_ge2) (hint_all (Real.sqrt x) x hsqrt_ge2 hsqrt_le_x)
  have hlow_int : (∫ t in (2 : ℝ)..(Real.sqrt x), ‖(t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖) ≤
      (1 / (Real.log 2) ^ 3) * (x ^ (a / 2) / a) := by
    have hmono := intervalIntegral.integral_mono_on hsqrt_ge2
      (hint_all 2 (Real.sqrt x) le_rfl hsqrt_ge2)
      (hrpow_low_int.const_mul (1 / (Real.log 2) ^ 3))
      (fun t ht => by
        rw [hnorm3 t ht.1]
        have hlog_ge : (Real.log 2) ^ 3 ≤ (Real.log t) ^ 3 :=
          pow_le_pow_left₀ hlog2_pos.le (Real.log_le_log zero_lt_two ht.1) 3
        calc t ^ (a - 1) / (Real.log t) ^ 3
            ≤ t ^ (a - 1) / (Real.log 2) ^ 3 :=
              div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith only [ht.1]) _)
                (pow_pos hlog2_pos 3) hlog_ge
          _ = (1 / (Real.log 2) ^ 3) * t ^ (a - 1) := by ring)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hsq_pow : (Real.sqrt x) ^ a = x ^ (a / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx_pos.le, show (1 / 2 : ℝ) * a = a / 2 by ring]
    exact hmono.trans (mul_le_mul_of_nonneg_left (hsq_pow ▸ hrpow_low_le) (by positivity))
  have hhigh_int : (∫ t in (Real.sqrt x)..x, ‖(t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖) ≤
      (8 / (Real.log x) ^ 3) * (x ^ a / a) := by
    have hmono := intervalIntegral.integral_mono_on hsqrt_le_x
      (hint_all (Real.sqrt x) x hsqrt_ge2 hsqrt_le_x)
      (hrpow_high_int.const_mul (8 / (Real.log x) ^ 3))
      (fun t ht => by
        have ht2 : 2 ≤ t := hsqrt_ge2.trans ht.1
        rw [hnorm3 t ht2]
        have hlog_half : Real.log x / 2 ≤ Real.log t := by
          have h1 := Real.log_le_log (Real.sqrt_pos.mpr hx_pos) ht.1
          rwa [Real.log_sqrt hx_pos.le] at h1
        have hpow_le : (Real.log x / 2) ^ 3 ≤ (Real.log t) ^ 3 :=
          pow_le_pow_left₀ (half_pos hlogx_pos).le hlog_half 3
        have hinv : 1 / (Real.log t) ^ 3 ≤ 8 / (Real.log x) ^ 3 := by
          have h1 := one_div_le_one_div_of_le (pow_pos (half_pos hlogx_pos) 3) hpow_le
          rwa [div_pow, show (2 : ℝ) ^ 3 = 8 by norm_num, one_div_div] at h1
        calc t ^ (a - 1) / (Real.log t) ^ 3
            = (1 / (Real.log t) ^ 3) * t ^ (a - 1) := by ring
          _ ≤ (8 / (Real.log x) ^ 3) * t ^ (a - 1) :=
              mul_le_mul_of_nonneg_right hinv (Real.rpow_nonneg (by linarith only [ht2]) _))
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hrpow_high_le (by positivity))
  have hint3_bound : ‖∫ t in (2 : ℝ)..x, (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖ ≤
      (1 / (Real.log 2) ^ 3) * (x ^ (a / 2) / a) + (8 / (Real.log x) ^ 3) * (x ^ a / a) := by
    calc ‖∫ t in (2 : ℝ)..x, (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖
        ≤ ∫ t in (2 : ℝ)..x, ‖(t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx2
      _ = (∫ t in (2 : ℝ)..(Real.sqrt x), ‖(t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖) +
            ∫ t in (Real.sqrt x)..x, ‖(t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖ := hsplit.symm
      _ ≤ _ := add_le_add hlow_int hhigh_int
  have hxa_pos : 0 < x ^ a := Real.rpow_pos_of_pos hx_pos a
  have hx_half_eq : x ^ (a / 2) / x ^ a = 1 / x ^ (a / 2) := by
    rw [div_eq_iff hxa_pos.ne', div_mul_eq_mul_div, one_mul,
      eq_div_iff (Real.rpow_pos_of_pos hx_pos _).ne', ← Real.rpow_add hx_pos, add_halves]
  have hlog_div : (Real.log x) ^ 2 / (Real.log x) ^ 3 = 1 / Real.log x := by
    rw [pow_succ (Real.log x) 2, ← div_div, div_self (pow_pos hlogx_pos 2).ne']
  rw [hibp x hx2]
  set E_lhs : ℝ := ‖-(P2 2 / (1 - s)) +
    2 / (1 - s) * ∫ t in (2 : ℝ)..x, (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖
  set c_init : ℝ := ‖P2 2 / (1 - s)‖
  set c_two : ℝ := ‖2 / (1 - s)‖
  set L_log : ℝ := Real.log x
  set P1 : ℝ := x ^ a
  set P_half : ℝ := x ^ (a / 2)
  set L2_3 : ℝ := (Real.log 2) ^ 3
  have htri : E_lhs ≤ c_init + c_two * ((1 / L2_3) * (P_half / a) + (8 / L_log ^ 3) * (P1 / a)) := by
    dsimp only [E_lhs, c_init, c_two, L2_3, P_half, L_log, P1]
    calc ‖-(P2 2 / (1 - s)) +
            2 / (1 - s) * ∫ t in (2 : ℝ)..x, (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖
        ≤ ‖-(P2 2 / (1 - s))‖ +
            ‖2 / (1 - s) * ∫ t in (2 : ℝ)..x, (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖ :=
          norm_add_le _ _
      _ = ‖P2 2 / (1 - s)‖ +
            ‖2 / (1 - s)‖ * ‖∫ t in (2 : ℝ)..x, (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 3‖ := by
          rw [norm_neg, norm_mul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hint3_bound (norm_nonneg _))
  have hstep1 : E_lhs * L_log ^ 2 / P1 ≤
      (c_init + c_two * ((1 / L2_3) * (P_half / a) + (8 / L_log ^ 3) * (P1 / a))) *
        (L_log ^ 2 / P1) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right htri (div_nonneg (sq_nonneg _) hxa_pos.le)
  have hstep2 : (c_init + c_two * ((1 / L2_3) * (P_half / a) + (8 / L_log ^ 3) * (P1 / a))) *
      (L_log ^ 2 / P1) =
      c_init * (L_log ^ 2 / P1) + (c_two / (a * L2_3)) * (L_log ^ 2 * (P_half / P1)) +
        (8 * c_two / a) * (L_log ^ 2 / L_log ^ 3) * (P1 / P1) := by ring
  rw [hstep2] at hstep1
  dsimp only [L_log, P1, P_half, L2_3] at hstep1
  rw [hx_half_eq, hlog_div, div_self hxa_pos.ne', mul_one, mul_one_div] at hstep1
  exact hstep1

private theorem tendsto_log_mul_primeSum_div_main_sub_one {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (t : ℝ) (k : ℤ) :
    let s : ℂ := ((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * Complex.I
    Tendsto (fun N : ℕ =>
      (Real.log ((N + 2 : ℕ) : ℝ) : ℂ) *
        (((∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) /
          ((((N + 2 : ℕ) : ℝ) : ℂ) ^ (1 - s) /
            ((1 - s) * (Real.log ((N + 2 : ℕ) : ℝ) : ℂ)))) - 1))
      atTop (𝓝 (1 / (1 - (((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)))) := by
  set s : ℂ := ((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * Complex.I with hs_def
  have hs_re : s.re = 2 * σ := by
    simp only [hs_def, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    ring
  have hs0 : 0 < s.re := by linarith only [hs_re, hσ0]
  have hs1 : s.re < 1 := by linarith only [hs_re, hσ1]
  have hs_ne0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs1; exact lt_irrefl 1 hs1
  have h1s_ne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs_ne1.symm
  set a : ℝ := 1 - s.re with ha_def
  have ha : 0 < a := by linarith only [ha_def, hs1]
  let x : ℕ → ℝ := fun N => ((N + 2 : ℕ) : ℝ)
  have hx_top : Tendsto x atTop atTop := by
    simpa only [x, Nat.cast_add, Nat.cast_ofNat] using
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  set C0 : ℂ := (2 : ℂ) ^ (-s) -
    _root_.RHTower.primeCpowAbelWeight s 2 * (Chebyshev.theta 2 : ℂ) -
    s / (1 - s) * _root_.RHTower.primeCpowAbelPrimitive s 2
  have hC0_lim : Tendsto (fun N : ℕ =>
      ‖1 - s‖ * ‖C0‖ * ((Real.log (x N)) ^ 2 / (x N) ^ a)) atTop (𝓝 0) := by
    have h0 := ((tendsto_log_pow_div_rpow_atTop 2 ha).comp hx_top).const_mul (‖1 - s‖ * ‖C0‖)
    rw [mul_zero] at h0
    exact h0
  have hlogSq_lim : Tendsto (fun N : ℕ =>
      ‖_root_.RHTower.primeCpowLogSqIntegral s (x N) -
        (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ) ^ 2)‖ *
        (Real.log (x N)) ^ 2 / (x N) ^ a) atTop (𝓝 0) :=
    (tendsto_primeCpowLogSqIntegral_sub_main hs0 hs1).comp hx_top
  have htheta_lim : Tendsto (fun N : ℕ =>
      ‖1 - s‖ * (‖_root_.RHTower.primeCpowAbelPrimitive s (x N) *
          (_root_.RHTower.thetaError (x N) : ℂ) -
        ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
          _root_.RHTower.primeCpowAbelKernel s u‖ *
        (Real.log (x N)) ^ 2 / (x N) ^ a)) atTop (𝓝 0) := by
    have h0 := ((tendsto_thetaRemainder_superPolyLog hs0 hs1 1).comp hx_top).const_mul ‖1 - s‖
    rw [mul_zero] at h0
    exact h0
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  have hmaj_sum := (hC0_lim.add hlogSq_lim).add htheta_lim
  rw [add_zero, add_zero] at hmaj_sum
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmaj_sum
  have hx2 : 2 ≤ x N := by dsimp only [x]; exact_mod_cast (by omega : 2 ≤ N + 2)
  have hx1 : 1 < x N := by linarith only [hx2]
  have hx_pos : 0 < x N := zero_lt_one.trans hx1
  have hlog_pos : 0 < Real.log (x N) := Real.log_pos hx1
  have hlog_ne : (Real.log (x N) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog_pos.ne'
  have hcpow_ne : (x N : ℂ) ^ (1 - s) ≠ 0 := by
    intro h0; have hn := congrArg norm h0
    rw [norm_zero, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos] at hn
    exact (Real.rpow_pos_of_pos hx_pos _).ne' hn
  have hdecomp : (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) -
      (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ)) =
      (x N : ℂ) ^ (1 - s) / ((1 - s) ^ 2 * (Real.log (x N) : ℂ) ^ 2) +
        C0 +
        (1 / (1 - s)) * (_root_.RHTower.primeCpowLogSqIntegral s (x N) -
          (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ) ^ 2)) +
        (_root_.RHTower.primeCpowAbelPrimitive s (x N) *
          (_root_.RHTower.thetaError (x N) : ℂ) -
          ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
            _root_.RHTower.primeCpowAbelKernel s u) := by
    rw [primeSum_eq_two_add_primeCpowSumIoc, ← hs_def]
    have hmain := _root_.RHTower.primeCpowSumIoc_sub_main hs_ne0 hs_ne1 hx2
    have hsq_div : 1 / (1 - s) *
        ((x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ) ^ 2)) =
        (x N : ℂ) ^ (1 - s) / ((1 - s) ^ 2 * (Real.log (x N) : ℂ) ^ 2) := by
      rw [one_div_mul_eq_div, div_div, mul_comm ((1 - s) * _) (1 - s), ← mul_assoc, ← sq]
    dsimp only [x, C0] at hmain hsq_div ⊢
    linear_combination hmain + hsq_div
  set Rem : ℂ := C0 +
    (1 / (1 - s)) * (_root_.RHTower.primeCpowLogSqIntegral s (x N) -
      (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ) ^ 2)) +
    (_root_.RHTower.primeCpowAbelPrimitive s (x N) *
      (_root_.RHTower.thetaError (x N) : ℂ) -
      ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
        _root_.RHTower.primeCpowAbelKernel s u)
  set P_c : ℂ := (x N : ℂ) ^ (1 - s)
  set L_c : ℂ := (Real.log (x N) : ℂ)
  set w_c : ℂ := 1 - s
  have halg : L_c *
      (((∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) /
        (P_c / (w_c * L_c))) - 1) - 1 / w_c =
      Rem * (w_c * L_c ^ 2 / P_c) := by
    have hnum_eq : (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) =
        P_c / (w_c * L_c) + P_c / (w_c ^ 2 * L_c ^ 2) + Rem := by
      dsimp only [Rem, P_c, L_c, w_c] at hdecomp ⊢; linear_combination hdecomp
    rw [hnum_eq]
    field_simp [h1s_ne, hlog_ne, hcpow_ne]
    ring
  change ‖L_c * (((∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) /
      (P_c / (w_c * L_c))) - 1) - 1 / w_c‖ ≤ _
  rw [halg, norm_mul, norm_div, norm_mul, norm_pow]
  have hLc_norm : ‖L_c‖ = Real.log (x N) := by
    dsimp only [L_c]; rw [Complex.norm_real, Real.norm_of_nonneg hlog_pos.le]
  have hPc_norm : ‖P_c‖ = (x N) ^ a := by
    dsimp only [P_c]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos, show (1 - s).re = a by simp [ha_def]]
  rw [hLc_norm, hPc_norm]
  have hRem_le : ‖Rem‖ ≤ ‖C0‖ +
      ‖1 / (1 - s)‖ * ‖_root_.RHTower.primeCpowLogSqIntegral s (x N) -
        (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ) ^ 2)‖ +
      ‖_root_.RHTower.primeCpowAbelPrimitive s (x N) *
        (_root_.RHTower.thetaError (x N) : ℂ) -
        ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
          _root_.RHTower.primeCpowAbelKernel s u‖ := by
    dsimp only [Rem]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul _ _).le)
  have h1s_cancel : ‖1 / (1 - s)‖ * ‖w_c‖ = 1 := by
    dsimp only [w_c]; rw [← norm_mul, one_div_mul_cancel h1s_ne, norm_one]
  set E_logSq : ℝ := ‖_root_.RHTower.primeCpowLogSqIntegral s (x N) -
    (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ) ^ 2)‖
  set E_th : ℝ := ‖_root_.RHTower.primeCpowAbelPrimitive s (x N) *
    (_root_.RHTower.thetaError (x N) : ℂ) -
    ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
      _root_.RHTower.primeCpowAbelKernel s u‖
  calc ‖Rem‖ * (‖w_c‖ * (Real.log (x N)) ^ 2 / (x N) ^ a)
      ≤ (‖C0‖ + ‖1 / (1 - s)‖ * E_logSq + E_th) *
          (‖w_c‖ * (Real.log (x N)) ^ 2 / (x N) ^ a) :=
        mul_le_mul_of_nonneg_right hRem_le (by positivity)
    _ = ‖w_c‖ * ‖C0‖ * ((Real.log (x N)) ^ 2 / (x N) ^ a) +
          (‖1 / (1 - s)‖ * ‖w_c‖) * (E_logSq * (Real.log (x N)) ^ 2 / (x N) ^ a) +
          ‖w_c‖ * (E_th * (Real.log (x N)) ^ 2 / (x N) ^ a) := by ring
    _ = _ := by rw [h1s_cancel, one_mul]

/-- **Exact second-order logarithmic sub-limit law (`0 < σ < 1 / 2`):**
`log(N + 2) · (bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖)` converges unconditionally
as `N → ∞` to `bornLogDispersionCoeff σ t k = (k t)² / √((1 - 2σ)² + (k t)²)³`. -/
theorem subcritical_norm_bornCoefficient_log_deficit {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (t : ℝ) (k : ℤ) :
    Tendsto (fun N : ℕ =>
      Real.log ((N + 2 : ℕ) : ℝ) * (bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖))
      atTop (𝓝 (bornLogDispersionCoeff σ t k)) := by
  set a : ℝ := 1 - 2 * σ with ha_def
  set ω : ℝ := (k : ℝ) * t with hω_def
  have ha0 : 0 < a := by linarith only [ha_def, hσ1]
  set s : ℂ := ((2 * σ : ℝ) : ℂ) - (ω : ℂ) * Complex.I
  set s₀ : ℂ := ((2 * σ : ℝ) : ℂ)
  have h1s : 1 - s = (a : ℂ) + (ω : ℂ) * Complex.I := by
    dsimp only [s]; rw [ha_def]; push_cast; ring
  have h1s0 : 1 - s₀ = (a : ℂ) := by
    dsimp only [s₀]; rw [ha_def]; push_cast; ring
  let x : ℕ → ℝ := fun N => ((N + 2 : ℕ) : ℝ)
  let M_num : ℕ → ℂ := fun N => (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ))
  let M_den : ℕ → ℂ := fun N => (x N : ℂ) ^ (1 - s₀) / ((1 - s₀) * (Real.log (x N) : ℂ))
  let Q_num : ℕ → ℂ := fun N =>
    (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) / M_num N
  let Q_den : ℕ → ℂ := fun N => (bornMass σ N : ℂ) / M_den N
  let W : ℕ → ℂ := fun N => Q_num N / Q_den N
  have hQ_num_log : Tendsto (fun N : ℕ => (Real.log (x N) : ℂ) * (Q_num N - 1))
      atTop (𝓝 (1 / (1 - s))) :=
    tendsto_log_mul_primeSum_div_main_sub_one hσ0 hσ1 t k
  have hQ_den_log : Tendsto (fun N : ℕ => (Real.log (x N) : ℂ) * (Q_den N - 1))
      atTop (𝓝 (1 / (1 - s₀))) := by
    have h0 := tendsto_log_mul_primeSum_div_main_sub_one hσ0 hσ1 0 0
    have hs0_eq : ((2 * σ : ℝ) : ℂ) - (((0 : ℤ) : ℝ) * (0 : ℝ) : ℝ) * Complex.I = s₀ := by
      dsimp only [s₀]; simp
    change Tendsto (fun N : ℕ =>
      (Real.log ((N + 2 : ℕ) : ℝ) : ℂ) *
        (((∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase 0 p : ℂ) ^ (-(0 : ℤ))) /
          ((((N + 2 : ℕ) : ℝ) : ℂ) ^ (1 - (((2 * σ : ℝ) : ℂ) - (((0 : ℤ) : ℝ) * (0 : ℝ) : ℝ) * Complex.I)) /
            ((1 - (((2 * σ : ℝ) : ℂ) - (((0 : ℤ) : ℝ) * (0 : ℝ) : ℝ) * Complex.I)) *
              (Real.log ((N + 2 : ℕ) : ℝ) : ℂ)))) - 1))
      atTop (𝓝 (1 / (1 - (((2 * σ : ℝ) : ℂ) - (((0 : ℤ) : ℝ) * (0 : ℝ) : ℝ) * Complex.I)))) at h0
    rw [hs0_eq] at h0
    refine h0.congr fun N => ?_
    have hsum0 : (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase 0 p : ℂ) ^ (-(0 : ℤ))) =
        (bornMass σ N : ℂ) := by
      rw [bornMass, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [neg_zero, zpow_zero, mul_one]
    rw [hsum0]
  have hinv_log : Tendsto (fun N : ℕ => ((Real.log (x N) : ℂ))⁻¹) atTop (𝓝 0) := by
    have hx_top : Tendsto x atTop atTop := by
      simpa only [x, Nat.cast_add, Nat.cast_ofNat] using
        tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    have hr := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hx_top)
    have hc := (Complex.continuous_ofReal.tendsto 0).comp hr
    rw [Complex.ofReal_zero] at hc
    exact hc.congr fun N => by dsimp only [Function.comp_apply]; rw [Complex.ofReal_inv]
  have hQ_num_1 : Tendsto Q_num atTop (𝓝 1) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have hm := hQ_num_log.mul hinv_log
    rw [mul_zero] at hm
    refine hm.congr fun N => ?_
    set L_c : ℂ := (Real.log (x N) : ℂ)
    have hlog_ne : L_c ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.log_pos (by dsimp only [x]; exact_mod_cast (by omega : 1 < N + 2))).ne'
    set q_c : ℂ := Q_num N - 1
    calc L_c * q_c * L_c⁻¹ = q_c * (L_c * L_c⁻¹) := by ring
      _ = q_c := by rw [mul_inv_cancel₀ hlog_ne, mul_one]
  have hQ_den_1 : Tendsto Q_den atTop (𝓝 1) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have hm := hQ_den_log.mul hinv_log
    rw [mul_zero] at hm
    refine hm.congr fun N => ?_
    set L_c : ℂ := (Real.log (x N) : ℂ)
    have hlog_ne : L_c ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.log_pos (by dsimp only [x]; exact_mod_cast (by omega : 1 < N + 2))).ne'
    set q_c : ℂ := Q_den N - 1
    calc L_c * q_c * L_c⁻¹ = q_c * (L_c * L_c⁻¹) := by ring
      _ = q_c := by rw [mul_inv_cancel₀ hlog_ne, mul_one]
  set α : ℂ := 1 / (1 - s) - 1 / (1 - s₀)
  have hW_log : Tendsto (fun N : ℕ => (Real.log (x N) : ℂ) * (W N - 1)) atTop (𝓝 α) := by
    have hq := (hQ_num_log.sub hQ_den_log).div hQ_den_1 one_ne_zero
    rw [div_one] at hq
    refine hq.congr' ?_
    filter_upwards [hQ_den_1.eventually_ne one_ne_zero] with N hQd_ne
    dsimp only [Pi.div_apply, W]
    set L_c : ℂ := (Real.log (x N) : ℂ)
    set qn : ℂ := Q_num N
    set qd : ℂ := Q_den N
    field_simp [hQd_ne]
    ring
  have hW_1 : Tendsto W atTop (𝓝 1) := by
    have h0 := hQ_num_1.div hQ_den_1 one_ne_zero
    rw [div_one] at h0
    exact h0
  have hW_re_log : Tendsto (fun N : ℕ => Real.log (x N) * (W N - 1).re) atTop (𝓝 α.re) := by
    have hr := (Complex.continuous_re.tendsto α).comp hW_log
    refine hr.congr fun N => ?_
    dsimp only [Function.comp_apply]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hW_sq_log : Tendsto (fun N : ℕ => Real.log (x N) * ‖W N - 1‖ ^ 2) atTop (𝓝 0) := by
    have hn1 := hW_log.norm
    have hn2 : Tendsto (fun N : ℕ => ‖W N - 1‖) atTop (𝓝 0) := by
      have hs1 := (hW_1.sub (tendsto_const_nhds (x := (1 : ℂ)))).norm
      rwa [sub_self, norm_zero] at hs1
    have hm := hn1.mul hn2
    rw [mul_zero] at hm
    refine hm.congr fun N => ?_
    have hlog0 : 0 ≤ Real.log (x N) :=
      Real.log_nonneg (by dsimp only [x]; exact_mod_cast (by omega : 1 ≤ N + 2))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog0, sq, mul_assoc]
  have h1_normW : Tendsto (fun N : ℕ => Real.log (x N) * (1 - ‖W N‖)) atTop (𝓝 (-α.re)) := by
    have hnum := ((hW_re_log.const_mul (-2)).sub hW_sq_log)
    have hden : Tendsto (fun N : ℕ => 1 + ‖W N‖) atTop (𝓝 2) := by
      have ha1 := (tendsto_const_nhds (x := (1 : ℝ))).add hW_1.norm
      rwa [norm_one, one_add_one_eq_two] at ha1
    have hq := hnum.div hden two_ne_zero
    have hlim_eq : (-2 * α.re - 0) / 2 = -α.re := by ring
    rw [hlim_eq] at hq
    refine hq.congr fun N => ?_
    dsimp only [Pi.div_apply]
    have hpos_den : 1 + ‖W N‖ ≠ 0 := by positivity
    have hsq_id : 1 - ‖W N‖ ^ 2 = -2 * (W N - 1).re - ‖W N - 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
      ring
    apply mul_right_cancel₀ hpos_den
    rw [div_mul_cancel₀ _ hpos_den]
    symm
    calc Real.log (x N) * (1 - ‖W N‖) * (1 + ‖W N‖)
        = Real.log (x N) * (1 - ‖W N‖ ^ 2) := by ring
      _ = Real.log (x N) * (-2 * (W N - 1).re - ‖W N - 1‖ ^ 2) := by rw [hsq_id]
      _ = -2 * (Real.log (x N) * (W N - 1).re) - Real.log (x N) * ‖W N - 1‖ ^ 2 := by ring
  have hL_eq : ‖(a : ℂ) / (1 - s)‖ = bornLorentzianLimit σ t k := by
    rw [h1s, norm_div, Complex.norm_real, Real.norm_of_nonneg ha0.le,
      Complex.norm_eq_sqrt_sq_add_sq, re_ofReal_add_ofReal_mul_I, im_ofReal_add_ofReal_mul_I,
      bornLorentzianLimit, ← ha_def, ← hω_def]
  have hα_re : bornLorentzianLimit σ t k * (-α.re) = bornLogDispersionCoeff σ t k := by
    have hα_calc : α.re = a / (a ^ 2 + ω ^ 2) - 1 / a := by
      dsimp only [α]
      rw [h1s, h1s0, Complex.sub_re]
      have h1 : (1 / ((a : ℂ) + (ω : ℂ) * Complex.I)).re = a / (a ^ 2 + ω ^ 2) := by
        rw [one_div, Complex.inv_re, Complex.normSq_apply, re_ofReal_add_ofReal_mul_I,
          im_ofReal_add_ofReal_mul_I]
        ring
      have h2 : (1 / (a : ℂ)).re = 1 / a := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      rw [h1, h2]
    rw [hα_calc, bornLorentzianLimit, bornLogDispersionCoeff, ← ha_def, ← hω_def]
    set S : ℝ := a ^ 2 + ω ^ 2 with hS_def
    have hS_pos : 0 < S := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha0) (sq_nonneg _)
    set R_sq : ℝ := Real.sqrt S
    have hR_ne : R_sq ≠ 0 := (Real.sqrt_pos.mpr hS_pos).ne'
    have hpow3 : R_sq ^ 3 = S * R_sq := by
      rw [pow_succ, show R_sq ^ 2 = S by exact Real.sq_sqrt hS_pos.le, mul_comm]
    rw [hpow3]
    field_simp [ha0.ne', hS_pos.ne', hR_ne]
    rw [hS_def]
    ring
  rw [← hα_re]
  have hm := h1_normW.const_mul (bornLorentzianLimit σ t k)
  refine hm.congr fun N => ?_
  have hx2 : 2 ≤ x N := by dsimp only [x]; exact_mod_cast (by omega : 2 ≤ N + 2)
  have hx1 : 1 < x N := by linarith only [hx2]
  have hx_pos : 0 < x N := zero_lt_one.trans hx1
  have hlog_ne : (Real.log (x N) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hx1).ne'
  have h1s_ne : (1 : ℂ) - s ≠ 0 := by
    rw [h1s]; intro h0
    have hr := congrArg Complex.re h0
    rw [re_ofReal_add_ofReal_mul_I, Complex.zero_re] at hr
    exact ha0.ne' hr
  have h1s0_ne : (1 : ℂ) - s₀ ≠ 0 := by
    rw [h1s0]; exact Complex.ofReal_ne_zero.mpr ha0.ne'
  have hcpow_s_ne : (x N : ℂ) ^ (1 - s) ≠ 0 := by
    intro h0; have hn := congrArg norm h0
    rw [norm_zero, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos] at hn
    exact (Real.rpow_pos_of_pos hx_pos _).ne' hn
  have hcpow_s0_ne : (x N : ℂ) ^ (1 - s₀) ≠ 0 := by
    intro h0; have hn := congrArg norm h0
    rw [norm_zero, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos] at hn
    exact (Real.rpow_pos_of_pos hx_pos _).ne' hn
  have hM_num_ne : M_num N ≠ 0 := div_ne_zero hcpow_s_ne (mul_ne_zero h1s_ne hlog_ne)
  have hM_den_ne : M_den N ≠ 0 := div_ne_zero hcpow_s0_ne (mul_ne_zero h1s0_ne hlog_ne)
  have hbm_ne : (bornMass σ N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (bornMass_pos' σ N).ne'
  have hM_ratio : M_num N / M_den N = ((a : ℂ) / (1 - s)) * (phase t (N + 2) : ℂ) ^ (-k) := by
    have hcp0 : (((N + 2 : ℕ) : ℝ) : ℂ) ^ (a : ℂ) = ((((N + 2 : ℕ) : ℝ) ^ a : ℝ) : ℂ) := by
      have h0 := cpow_one_sub_div_rpow a 0 0 N
      simp only [Int.cast_zero, zero_mul, Complex.ofReal_zero, add_zero, neg_zero, zpow_zero,
        mul_one] at h0
      exact h0
    dsimp only [M_num, M_den, x]
    rw [h1s, h1s0, cpow_one_sub_div_rpow a t k N, hcp0, ← h1s]
    set P_a : ℂ := (((((N + 2 : ℕ) : ℝ) ^ a : ℝ) : ℂ))
    set ph : ℂ := (phase t (N + 2) : ℂ) ^ (-k)
    set L_c : ℂ := (Real.log ((N + 2 : ℕ) : ℝ) : ℂ)
    set w_c : ℂ := 1 - s
    set a_c : ℂ := (a : ℂ)
    have hxa_ne : P_a ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx_pos a).ne'
    have ha_c_ne : a_c ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
    field_simp [h1s_ne, hlog_ne, hxa_ne, ha_c_ne]
  have hbc_eq : bornCoefficient σ t k N = (M_num N / M_den N) * W N := by
    rw [bornCoefficient_eq_sum]
    dsimp only [W, Q_num, Q_den]
    set num_c : ℂ := ∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)
    set den_c : ℂ := (bornMass σ N : ℂ)
    set mn : ℂ := M_num N
    set md : ℂ := M_den N
    field_simp [hM_num_ne, hM_den_ne, hbm_ne]
  have hbc_norm : ‖bornCoefficient σ t k N‖ = bornLorentzianLimit σ t k * ‖W N‖ := by
    rw [hbc_eq, hM_ratio, norm_mul, norm_mul, hL_eq, norm_zpow, Circle.norm_coe, one_zpow, mul_one]
  rw [hbc_norm]
  ring

/-- **Super-polylogarithmic zero-blind smooth approximation (`0 < σ < 1 / 2`):**
for every `0 < σ < 1 / 2`, `t ∈ ℝ`, `k ∈ ℤ`, and **every** `A : ℕ`,
`(log(N + 2))^A · ‖bornCoefficient σ t k N - smoothBornCoefficient σ t k N‖ → 0` as `N → ∞`. -/
theorem subcritical_bornCoefficient_sub_smooth_superPolyLog {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (t : ℝ) (k : ℤ) (A : ℕ) :
    Tendsto (fun N : ℕ =>
      (Real.log ((N + 2 : ℕ) : ℝ)) ^ A *
        ‖bornCoefficient σ t k N - smoothBornCoefficient σ t k N‖)
      atTop (𝓝 0) := by
  set a : ℝ := 1 - 2 * σ with ha_def
  have ha0 : 0 < a := by linarith only [ha_def, hσ1]
  have ha1 : a < 1 := by linarith only [ha_def, hσ0]
  let x : ℕ → ℝ := fun N => ((N + 2 : ℕ) : ℝ)
  have hx_top : Tendsto x atTop atTop := by
    simpa only [x, Nat.cast_add, Nat.cast_ofNat] using
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  let sc : ℕ → ℝ := fun N => a * Real.log (x N) / (x N) ^ a
  let s : ℂ := ((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * Complex.I
  let s₀ : ℂ := ((2 * σ : ℝ) : ℂ)
  have hs_re : s.re = 2 * σ := by
    simp only [s, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    ring
  have hs0_re : s₀.re = 2 * σ := by simp [s₀]
  have hs_ne0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp [hs_re] at this; linarith
  have hs_ne1 : s ≠ 1 := fun h => by have := congrArg Complex.re h; simp [hs_re] at this; linarith
  have hs0_ne0 : s₀ ≠ 0 := fun h => by have := congrArg Complex.re h; simp [hs0_re] at this; linarith
  have hs0_ne1 : s₀ ≠ 1 := fun h => by have := congrArg Complex.re h; simp [hs0_re] at this; linarith
  let U : ℕ → ℂ := fun N =>
    (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) * (sc N : ℂ)
  let U_sm : ℕ → ℂ := fun N => smoothPrimeSum s (x N) * (sc N : ℂ)
  let V : ℕ → ℂ := fun N => (bornMass σ N : ℂ) * (sc N : ℂ)
  let V_sm : ℕ → ℂ := fun N => smoothPrimeSum s₀ (x N) * (sc N : ℂ)
  have hU_diff : ∀ B : ℕ, Tendsto (fun N : ℕ => (Real.log (x N)) ^ B * ‖U N - U_sm N‖)
      atTop (𝓝 0) := by
    intro B
    have hth := ((tendsto_thetaRemainder_superPolyLog
      (by linarith only [hs_re, hσ0] : 0 < s.re) (by linarith only [hs_re, hσ1] : s.re < 1) B).comp
      hx_top).const_mul a
    rw [mul_zero] at hth
    refine hth.congr fun N => ?_
    dsimp only [Function.comp_apply, U, U_sm, sc, smoothPrimeSum]
    have hx2 : 2 ≤ x N := by dsimp only [x]; exact_mod_cast (by omega : 2 ≤ N + 2)
    have hlog_pos : 0 < Real.log (x N) := Real.log_pos (by linarith only [hx2])
    have hxa_pos : 0 < (x N) ^ a := Real.rpow_pos_of_pos (by linarith only [hx2]) a
    have hsc_pos : 0 ≤ a * Real.log (x N) / (x N) ^ a := by positivity
    have hid : (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) -
        ((2 : ℂ) ^ (-s) + (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ)) -
          _root_.RHTower.primeCpowAbelWeight s 2 * (Chebyshev.theta 2 : ℂ) -
          s / (1 - s) * _root_.RHTower.primeCpowAbelPrimitive s 2 +
          1 / (1 - s) * _root_.RHTower.primeCpowLogSqIntegral s (x N)) =
        _root_.RHTower.primeCpowAbelPrimitive s (x N) * (_root_.RHTower.thetaError (x N) : ℂ) -
          ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
            _root_.RHTower.primeCpowAbelKernel s u := by
      rw [primeSum_eq_two_add_primeCpowSumIoc]
      have hm := _root_.RHTower.primeCpowSumIoc_sub_main hs_ne0 hs_ne1 hx2
      dsimp only [x, s] at hm ⊢
      linear_combination hm
    rw [← sub_mul, hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsc_pos,
      show 1 - s.re = a by linarith only [hs_re, ha_def], pow_succ]
    ring
  have hV_diff : ∀ B : ℕ, Tendsto (fun N : ℕ => (Real.log (x N)) ^ B * ‖V N - V_sm N‖)
      atTop (𝓝 0) := by
    intro B
    have hth := ((tendsto_thetaRemainder_superPolyLog
      (by linarith only [hs0_re, hσ0] : 0 < s₀.re) (by linarith only [hs0_re, hσ1] : s₀.re < 1) B).comp
      hx_top).const_mul a
    rw [mul_zero] at hth
    refine hth.congr fun N => ?_
    dsimp only [Function.comp_apply, V, V_sm, sc, smoothPrimeSum]
    have hx2 : 2 ≤ x N := by dsimp only [x]; exact_mod_cast (by omega : 2 ≤ N + 2)
    have hsc_pos : 0 ≤ a * Real.log (x N) / (x N) ^ a := by
      have : 0 < Real.log (x N) := Real.log_pos (by linarith only [hx2])
      have : 0 < (x N) ^ a := Real.rpow_pos_of_pos (by linarith only [hx2]) a
      positivity
    have hbm_sum : (bornMass σ N : ℂ) =
        ∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase 0 p : ℂ) ^ (-(0 : ℤ)) := by
      rw [bornMass, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [neg_zero, zpow_zero, mul_one]
    have hid : (bornMass σ N : ℂ) -
        ((2 : ℂ) ^ (-s₀) + (x N : ℂ) ^ (1 - s₀) / ((1 - s₀) * (Real.log (x N) : ℂ)) -
          _root_.RHTower.primeCpowAbelWeight s₀ 2 * (Chebyshev.theta 2 : ℂ) -
          s₀ / (1 - s₀) * _root_.RHTower.primeCpowAbelPrimitive s₀ 2 +
          1 / (1 - s₀) * _root_.RHTower.primeCpowLogSqIntegral s₀ (x N)) =
        _root_.RHTower.primeCpowAbelPrimitive s₀ (x N) * (_root_.RHTower.thetaError (x N) : ℂ) -
          ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
            _root_.RHTower.primeCpowAbelKernel s₀ u := by
      rw [hbm_sum, primeSum_eq_two_add_primeCpowSumIoc]
      have hs0_eq : ((2 * σ : ℝ) : ℂ) - (((0 : ℤ) : ℝ) * (0 : ℝ) : ℝ) * Complex.I = s₀ := by
        dsimp only [s₀]; simp
      rw [hs0_eq]
      have hm := _root_.RHTower.primeCpowSumIoc_sub_main hs0_ne0 hs0_ne1 hx2
      dsimp only [x] at hm ⊢
      linear_combination hm
    rw [← sub_mul, hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsc_pos,
      show 1 - s₀.re = a by linarith only [hs0_re, ha_def], pow_succ]
    ring
  have hV_lim : Tendsto V atTop (𝓝 1) := by
    have hm := (powerMass_asymptotic ha0 ha1).comp hx_top
    have hc := (Complex.continuous_ofReal.tendsto 1).comp hm
    rw [Complex.ofReal_one] at hc
    refine hc.congr fun N => ?_
    dsimp only [Function.comp_apply, V, sc, x]
    have hcut : cutoff ((N + 2 : ℕ) : ℝ) = N := by unfold cutoff; rw [Nat.floor_natCast]; omega
    rw [powerMass, hcut, bornMass, ← Complex.ofReal_mul, mul_div_assoc]
    have hsum_eq : (∑ p ∈ primes N, (p : ℝ) ^ (a - 1)) = ∑ p ∈ primes N, bornWeight σ p :=
      Finset.sum_congr rfl fun p _ => by
        rw [bornWeight, show a - 1 = -(2 * σ) by linarith only [ha_def]]
    rw [hsum_eq]
  have hV_sm_lim : Tendsto V_sm atTop (𝓝 1) := by
    have h0 : Tendsto (fun N => V N - V_sm N) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hd := hV_diff 0
      simpa only [pow_zero, one_mul] using hd
    have hsub := hV_lim.sub h0
    rw [sub_zero] at hsub
    exact hsub.congr fun N => sub_sub_cancel (V N) (V_sm N)
  have hU_bdd : ∀ N : ℕ, ‖U N‖ ≤ ‖V N‖ := by
    intro N
    dsimp only [U, V]
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [bornMass, Complex.ofReal_sum]
    refine (norm_sum_le _ _).trans ?_
    have hpos_sum : 0 ≤ ∑ p ∈ primes N, bornWeight σ p := (bornMass_pos' σ N).le
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg hpos_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bornWeight_nonneg' σ p),
      norm_zpow, Circle.norm_coe, one_zpow, mul_one]
  have hmaj : Tendsto (fun N : ℕ =>
      ((Real.log (x N)) ^ A * ‖U N - U_sm N‖ * ‖V N‖ +
        ‖V N‖ * ((Real.log (x N)) ^ A * ‖V N - V_sm N‖)) /
        (‖V N‖ * ‖V_sm N‖)) atTop (𝓝 0) := by
    have hnum := ((hU_diff A).mul hV_lim.norm).add (hV_lim.norm.mul (hV_diff A))
    have hden := hV_lim.norm.mul hV_sm_lim.norm
    rw [norm_one, mul_one, mul_zero, add_zero] at hnum
    rw [norm_one, mul_one] at hden
    have hq := hnum.div hden one_ne_zero
    rw [zero_div] at hq
    exact hq
  have h_nonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ (Real.log ((N + 2 : ℕ) : ℝ)) ^ A *
        ‖bornCoefficient σ t k N - smoothBornCoefficient σ t k N‖ := by
    filter_upwards [eventually_ge_atTop 0] with N _
    have hlog0 : 0 ≤ Real.log ((N + 2 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + 2))
    exact mul_nonneg (pow_nonneg hlog0 _) (norm_nonneg _)
  refine squeeze_zero' h_nonneg ?_ hmaj
  filter_upwards [hV_sm_lim.eventually_ne one_ne_zero] with N hVsm_ne
  have hx1 : 1 < x N := by dsimp only [x]; exact_mod_cast (by omega : 1 < N + 2)
  have hlog_pos : 0 < Real.log (x N) := Real.log_pos hx1
  have hxa_pos : 0 < (x N) ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) a
  have hsc_ne : (sc N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos (mul_pos ha0 hlog_pos) hxa_pos).ne'
  have hV_ne : V N ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (bornMass_pos' σ N).ne') hsc_ne
  have hbc_quot : bornCoefficient σ t k N = U N / V N := by
    rw [bornCoefficient_eq_sum]; dsimp only [U, V]; rw [mul_div_mul_right _ _ hsc_ne]
  have hsm_quot : smoothBornCoefficient σ t k N = U_sm N / V_sm N := by
    rw [smoothBornCoefficient]; dsimp only [U_sm, V_sm, s, s₀, x]
    rw [mul_div_mul_right _ _ hsc_ne]
  have hdiff_quot : U N / V N - U_sm N / V_sm N =
      ((U N - U_sm N) * V N + U N * (V_sm N - V N)) / (V N * V_sm N) := by
    set u1 := U N; set u2 := U_sm N; set v1 := V N; set v2 := V_sm N
    field_simp [hV_ne, hVsm_ne]; ring
  rw [hbc_quot, hsm_quot, hdiff_quot, norm_div, norm_mul, mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hlog_nn : 0 ≤ (Real.log ((N + 2 : ℕ) : ℝ)) ^ A := pow_nonneg hlog_pos.le _
  calc (Real.log ((N + 2 : ℕ) : ℝ)) ^ A * ‖(U N - U_sm N) * V N + U N * (V_sm N - V N)‖
      ≤ (Real.log ((N + 2 : ℕ) : ℝ)) ^ A *
          (‖(U N - U_sm N) * V N‖ + ‖U N * (V_sm N - V N)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hlog_nn
    _ ≤ (Real.log ((N + 2 : ℕ) : ℝ)) ^ A *
          (‖U N - U_sm N‖ * ‖V N‖ + ‖V N‖ * ‖V N - V_sm N‖) := by
        rw [norm_mul (U N - U_sm N), norm_mul (U N), norm_sub_rev (V_sm N) (V N)]
        exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hU_bdd N) (norm_nonneg _)))
          hlog_nn
    _ = _ := by ring

/-- **Eventual strict pointwise sub-Lorentzian inequality (`0 < σ < 1 / 2`, `t ≠ 0`, `k ≠ 0`):**
at **every** sufficiently large cutoff `N`, `‖bornCoefficient σ t k N‖` lies strictly below
`bornLorentzianLimit σ t k` by at least `(bornLogDispersionCoeff σ t k / 2) / log(N + 2) > 0`,
without assuming `riemannZeta ρ = 0`. -/
theorem subcritical_eventually_norm_lt_lorentzian {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    {t : ℝ} (ht : t ≠ 0) {k : ℤ} (hk : k ≠ 0) :
    0 < bornLogDispersionCoeff σ t k ∧
      ∀ᶠ N : ℕ in atTop,
        ‖bornCoefficient σ t k N‖ ≤
          bornLorentzianLimit σ t k -
            (bornLogDispersionCoeff σ t k / 2) / Real.log ((N + 2 : ℕ) : ℝ) ∧
        ‖bornCoefficient σ t k N‖ < bornLorentzianLimit σ t k := by
  have hω_ne : (k : ℝ) * t ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hk) ht
  have hS_pos : 0 < (1 - 2 * σ) ^ 2 + ((k : ℝ) * t) ^ 2 :=
    add_pos (sq_pos_of_pos (by linarith only [hσ1])) (sq_pos_of_ne_zero hω_ne)
  have hΔ_pos : 0 < bornLogDispersionCoeff σ t k :=
    div_pos (sq_pos_of_ne_zero hω_ne) (pow_pos (Real.sqrt_pos.mpr hS_pos) 3)
  refine ⟨hΔ_pos, ?_⟩
  have hlim := subcritical_norm_bornCoefficient_log_deficit hσ0 hσ1 t k
  filter_upwards [hlim.eventually (lt_mem_nhds (half_lt_self hΔ_pos))] with N hN
  have hlog_pos : 0 < Real.log ((N + 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N + 2))
  have hdiv : (bornLogDispersionCoeff σ t k / 2) / Real.log ((N + 2 : ℕ) : ℝ) <
      bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖ :=
    (div_lt_iff₀' hlog_pos).mpr hN
  have hgap_pos : 0 < (bornLogDispersionCoeff σ t k / 2) / Real.log ((N + 2 : ℕ) : ℝ) :=
    div_pos (half_pos hΔ_pos) hlog_pos
  exact ⟨by linarith only [hdiv], by linarith only [hdiv, hgap_pos]⟩

/-- **Super-dispersion cutoff barrier (`0 < σ < 1 / 2`):** no unbounded cutoff subsequence
`φ : ℕ → ℕ` can push `‖bornCoefficient σ t k (φ j)‖` below
`bornLorentzianLimit σ t k - C / log(φ j + 2)` for any `C > bornLogDispersionCoeff σ t k`. -/
theorem subcritical_no_subseq_superDispersion_deficit {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (t : ℝ) (k : ℤ) {C : ℝ} (hC : bornLogDispersionCoeff σ t k < C)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    ¬ (∀ᶠ j : ℕ in atTop,
        ‖bornCoefficient σ t k (φ j)‖ ≤
          bornLorentzianLimit σ t k - C / Real.log ((φ j + 2 : ℕ) : ℝ)) := by
  intro hev
  have hlim := (subcritical_norm_bornCoefficient_log_deficit hσ0 hσ1 t k).comp hφ
  obtain ⟨j, hj_le, hj_lt⟩ := (hev.and (hlim.eventually (gt_mem_nhds hC))).exists
  dsimp only [Function.comp_apply] at hj_lt
  have hlog_pos : 0 < Real.log ((φ j + 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < φ j + 2))
  have hC_le : C ≤ Real.log ((φ j + 2 : ℕ) : ℝ) *
      (bornLorentzianLimit σ t k - ‖bornCoefficient σ t k (φ j)‖) := by
    have h1 : C / Real.log ((φ j + 2 : ℕ) : ℝ) ≤
        bornLorentzianLimit σ t k - ‖bornCoefficient σ t k (φ j)‖ := by linarith only [hj_le]
    exact (div_le_iff₀' hlog_pos).mp h1
  linarith only [hC_le, hj_lt]

/-! ### Part 3: Supercritical prime-Dirichlet limit and high-mode Bohr recurrence (`σ > 1 / 2`) -/

/-- Prime-Dirichlet numerator `∑_{p prime} p^{-2σ} (phase t p)^{-k}` in the convergent regime `σ > 1 / 2`. -/
def supercriticalPrimeSum (σ t : ℝ) (k : ℤ) : ℂ :=
  ∑' n : ℕ, if n.Prime then (bornWeight σ n : ℂ) * (phase t n : ℂ) ^ (-k) else 0

/-- Total prime Born mass `P(2σ) = ∑_{p prime} p^{-2σ}` for `σ > 1 / 2`. -/
def supercriticalPrimeMass (σ : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime then bornWeight σ n else 0

/-- Limiting `k`-th Fourier mode `P(2σ - i k t) / P(2σ)` of `bornLaw σ t` for `σ > 1 / 2`. -/
def supercriticalModeLimit (σ t : ℝ) (k : ℤ) : ℂ :=
  supercriticalPrimeSum σ t k / (supercriticalPrimeMass σ : ℂ)

private theorem summable_supercritical_weight {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ => if n.Prime then bornWeight σ n else 0) := by
  have hs : Summable (bornWeight σ) := Real.summable_nat_rpow.mpr (by linarith only [hσ])
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · split_ifs <;> [exact bornWeight_nonneg' σ n; exact le_rfl]
  · split_ifs <;> [exact le_rfl; exact bornWeight_nonneg' σ n]

private theorem supercriticalPrimeMass_pos {σ : ℝ} (hσ : 1 / 2 < σ) :
    0 < supercriticalPrimeMass σ := by
  have hs := summable_supercritical_weight hσ
  have h2 : 0 < (if Nat.Prime 2 then bornWeight σ 2 else 0) := by
    rw [if_pos Nat.prime_two]; exact Real.rpow_pos_of_pos (by norm_num) _
  exact hs.tsum_pos (fun n => by split_ifs <;> [exact bornWeight_nonneg' σ n; exact le_rfl]) 2 h2

private theorem summable_supercritical_term {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) (k : ℤ) :
    Summable (fun n : ℕ => if n.Prime then (bornWeight σ n : ℂ) * (phase t n : ℂ) ^ (-k) else 0) := by
  refine Summable.of_norm_bounded (summable_supercritical_weight hσ) fun n => ?_
  split_ifs with hp
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bornWeight_nonneg' σ n),
      norm_zpow, Circle.norm_coe, one_zpow, mul_one]
  · rw [norm_zero]

/-- Above `σ = 1 / 2`, every Fourier mode `bornCoefficient σ t k N` converges as `N → ∞` to the
prime-Dirichlet quotient `supercriticalModeLimit σ t k`. -/
theorem supercritical_bornCoefficient_tendsto {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) (k : ℤ) :
    Tendsto (bornCoefficient σ t k) atTop (𝓝 (supercriticalModeLimit σ t k)) := by
  have hnum_lim := (summable_supercritical_term hσ t k).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 3)
  have hden_lim := (Complex.continuous_ofReal.tendsto (supercriticalPrimeMass σ)).comp
    ((summable_supercritical_weight hσ).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 3))
  have hquot := hnum_lim.div hden_lim
    (Complex.ofReal_ne_zero.mpr (supercriticalPrimeMass_pos hσ).ne')
  refine hquot.congr fun N => ?_
  have hprimes_range : primes N = (Finset.range (N + 3)).filter Nat.Prime := by
    ext p; simp [primes, Nat.mem_primesBelow]
  have hnum_eq : (∑ n ∈ Finset.range (N + 3),
      if n.Prime then (bornWeight σ n : ℂ) * (phase t n : ℂ) ^ (-k) else 0) =
      ∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k) := by
    rw [hprimes_range, Finset.sum_filter]
  have hden_eq : (((∑ n ∈ Finset.range (N + 3),
      if n.Prime then bornWeight σ n else 0 : ℝ) : ℂ)) = (bornMass σ N : ℂ) := by
    rw [bornMass, hprimes_range, Finset.sum_filter]
  change (∑ n ∈ Finset.range (N + 3),
      if n.Prime then (bornWeight σ n : ℂ) * (phase t n : ℂ) ^ (-k) else 0) /
    (((∑ n ∈ Finset.range (N + 3),
      if n.Prime then bornWeight σ n else 0 : ℝ) : ℂ)) = bornCoefficient σ t k N
  rw [bornCoefficient_eq_sum, hnum_eq, hden_eq]

/-- **Supercritical high-mode Bohr recurrence:** for every `σ > 1 / 2`, **every** `t ∈ ℝ`
(with no irrationality hypothesis), every `ε > 0`, and every threshold `K₀ : ℕ`, there exists an
integer mode `k > K₀` whose limiting Fourier coefficient satisfies
`1 - ε < (supercriticalModeLimit σ t k).re` and `‖supercriticalModeLimit σ t k‖ ≤ 1`. -/
theorem supercritical_exists_high_mode_re_gt {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) (K₀ : ℕ) :
    ∃ k : ℕ, K₀ < k ∧
      1 - ε < (supercriticalModeLimit σ t (k : ℤ)).re ∧
      ‖supercriticalModeLimit σ t (k : ℤ)‖ ≤ 1 := by
  let w : ℕ → ℝ := fun n => if n.Prime then bornWeight σ n else 0
  have hw_nonneg : ∀ n, 0 ≤ w n := fun n => by
    dsimp only [w]; split_ifs <;> [exact bornWeight_nonneg' σ n; exact le_rfl]
  have hw_sum : Summable w := summable_supercritical_weight hσ
  have hM_pos : 0 < supercriticalPrimeMass σ := supercriticalPrimeMass_pos hσ
  set δ : ℝ := min (ε / 2) (1 / 2)
  have hδ_pos : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have h2δ_le : 2 * δ ≤ ε := by
    have h1 : δ ≤ ε / 2 := min_le_left _ _
    linarith only [h1]
  have htail_lim : Tendsto (fun R : ℕ => supercriticalPrimeMass σ - ∑ n ∈ Finset.range R, w n)
      atTop (𝓝 0) := by
    have hsub := (tendsto_const_nhds (x := supercriticalPrimeMass σ)).sub
      hw_sum.hasSum.tendsto_sum_nat
    change Tendsto (fun R : ℕ => supercriticalPrimeMass σ - ∑ n ∈ Finset.range R, w n) atTop
      (𝓝 (supercriticalPrimeMass σ - supercriticalPrimeMass σ)) at hsub
    rwa [sub_self] at hsub
  obtain ⟨R, hR_tail⟩ := (htail_lim.eventually (gt_mem_nhds (mul_pos (half_pos hδ_pos) hM_pos))).exists
  let Q : ℕ := ⌈Real.sqrt (2 * Real.pi ^ 2 / δ)⌉₊ + 1
  have hQ1 : 1 ≤ Q := by dsimp only [Q]; omega
  have hQ_bound : 2 * Real.pi ^ 2 / (Q : ℝ) ^ 2 < δ := by
    have hsq_pos : 0 < 2 * Real.pi ^ 2 / δ := div_pos (by positivity) hδ_pos
    have hlt_Q : Real.sqrt (2 * Real.pi ^ 2 / δ) < (Q : ℝ) := by
      dsimp only [Q]
      push_cast
      linarith only [Nat.le_ceil (Real.sqrt (2 * Real.pi ^ 2 / δ))]
    have hsq_lt : 2 * Real.pi ^ 2 / δ < (Q : ℝ) ^ 2 := by
      have h := pow_lt_pow_left₀ hlt_Q (Real.sqrt_nonneg _) two_ne_zero
      rwa [Real.sq_sqrt hsq_pos.le] at h
    have hQ2_pos : 0 < (Q : ℝ) ^ 2 := by positivity
    exact (div_lt_iff₀ hQ2_pos).mpr ((div_lt_iff₀ hδ_pos).mp hsq_lt |>.trans_eq (mul_comm _ _))
  obtain ⟨q, hq1, _, hcos⟩ := exists_dirichlet_phase (ι := Fin R)
    (fun i => Real.log (i.val : ℝ)) (((K₀ + 1 : ℕ) : ℝ) * t) Q hQ1
  let k : ℕ := q * (K₀ + 1)
  have hk_gt : K₀ < k := by
    have h1 : 1 * (K₀ + 1) ≤ q * (K₀ + 1) := Nat.mul_le_mul_right (K₀ + 1) hq1
    dsimp only [k]; omega
  refine ⟨k, hk_gt, ?_, ?_⟩
  · let f : ℕ → ℂ := fun n => if n.Prime then (bornWeight σ n : ℂ) * (phase t n : ℂ) ^ (-(k : ℤ)) else 0
    have hf_sum : Summable f := summable_supercritical_term hσ t (k : ℤ)
    have hf_re : ∀ n : ℕ, (f n).re =
        w n * Real.cos (Real.log (n : ℝ) * ((q : ℝ) * (((K₀ + 1 : ℕ) : ℝ) * t))) := by
      intro n
      dsimp only [f, w]
      split_ifs with hp
      · have hph : (phase t n : ℂ) ^ (-(k : ℤ)) =
            Complex.exp (((Real.log (n : ℝ) * ((q : ℝ) * (((K₀ + 1 : ℕ) : ℝ) * t)) : ℝ) : ℂ) *
              Complex.I) := by
          rw [phase, Circle.coe_exp, ← Complex.exp_int_mul]
          congr 1
          dsimp only [k]
          push_cast
          ring
        rw [hph, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.exp_ofReal_mul_I_re]
      · simp
    have hre_sum : (supercriticalPrimeSum σ t (k : ℤ)).re = ∑' n : ℕ, (f n).re :=
      Complex.re_tsum hf_sum
    have hf_re_summable : Summable (fun n => (f n).re) := Complex.reCLM.summable hf_sum
    have hsplit_f := (hf_re_summable.sum_add_tsum_nat_add R).symm
    have hsplit_w := (hw_sum.sum_add_tsum_nat_add R).symm
    have htail_eq : (∑' n : ℕ, w (n + R)) = supercriticalPrimeMass σ - ∑ n ∈ Finset.range R, w n := by
      change _ = (∑' n : ℕ, w n) - _
      linarith only [hsplit_w]
    have hhead_ge : (1 - δ) * (∑ n ∈ Finset.range R, w n) ≤ ∑ n ∈ Finset.range R, (f n).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [hf_re n, mul_comm (1 - δ)]
      refine mul_le_mul_of_nonneg_left ?_ (hw_nonneg n)
      have hc := (hcos ⟨n, Finset.mem_range.mp hn⟩).1
      linarith only [hc, hQ_bound]
    have htail_ge : -(∑' n : ℕ, w (n + R)) ≤ ∑' n : ℕ, (f (n + R)).re := by
      rw [← tsum_neg]
      refine (hw_sum.comp_injective (add_left_injective R)).neg.tsum_le_tsum (fun n => ?_)
        (hf_re_summable.comp_injective (add_left_injective R))
      rw [hf_re (n + R)]
      have hc := Real.neg_one_le_cos
        (Real.log ((n + R : ℕ) : ℝ) * ((q : ℝ) * (((K₀ + 1 : ℕ) : ℝ) * t)))
      have hm := mul_le_mul_of_nonneg_left hc (hw_nonneg (n + R))
      linarith only [hm]
    set T_rem : ℝ := supercriticalPrimeMass σ - ∑ n ∈ Finset.range R, w n
    have hnum_gt : (1 - ε) * supercriticalPrimeMass σ < (supercriticalPrimeSum σ t (k : ℤ)).re := by
      rw [hre_sum, hsplit_f]
      have hhead_T : (∑ n ∈ Finset.range R, w n) = supercriticalPrimeMass σ - T_rem := by
        dsimp only [T_rem]; ring
      have hT_nonneg : 0 ≤ T_rem := by
        rw [← htail_eq]
        exact tsum_nonneg fun n => hw_nonneg (n + R)
      calc (1 - ε) * supercriticalPrimeMass σ
          ≤ (1 - 2 * δ) * supercriticalPrimeMass σ :=
            mul_le_mul_of_nonneg_right (by linarith only [h2δ_le]) hM_pos.le
        _ < (1 - δ) * (supercriticalPrimeMass σ - T_rem) - T_rem := by
            have h2T : (2 - δ) * T_rem < δ * supercriticalPrimeMass σ := by
              calc (2 - δ) * T_rem ≤ 2 * T_rem :=
                    mul_le_mul_of_nonneg_right (by linarith only [hδ_pos]) hT_nonneg
                _ < 2 * (δ / 2 * supercriticalPrimeMass σ) :=
                    mul_lt_mul_of_pos_left hR_tail zero_lt_two
                _ = δ * supercriticalPrimeMass σ := by ring
            linarith only [h2T]
        _ ≤ (∑ n ∈ Finset.range R, (f n).re) + ∑' n : ℕ, (f (n + R)).re := by
            rw [← hhead_T, ← htail_eq] at *
            linarith only [hhead_ge, htail_ge]
    rw [supercriticalModeLimit, Complex.div_ofReal_re, lt_div_iff₀ hM_pos]
    exact hnum_gt
  · rw [supercriticalModeLimit, norm_div, Complex.norm_real, Real.norm_of_nonneg hM_pos.le,
      div_le_one hM_pos]
    refine tsum_of_norm_bounded hw_sum.hasSum fun n => ?_
    dsimp only [w]
    split_ifs with hp
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bornWeight_nonneg' σ n),
        norm_zpow, Circle.norm_coe, one_zpow, mul_one]
    · rw [norm_zero]

/-! ### Part 4: Self-clocked strip zeros, unconditional exclusion below `2401 / 19200` above height `184`, and sharp critical-constant equivalence with `RiemannHypothesis` -/

/-- Every zero of `riemannZeta` in the open critical strip `0 < Re ρ < 1` has nonzero ordinate
`ρ.im ≠ 0`, supplying a canonical nonzero self-clock `t = ρ.im`. -/
theorem openStrip_zeta_zero_im_ne_zero (ρ : OpenStrip) (hζ : riemannZeta ρ.val = 0) :
    ρ.val.im ≠ 0 := by
  intro him0
  have hreal : ρ.val = (ρ.val.re : ℂ) := by
    apply Complex.ext <;> simp [him0]
  rw [hreal] at hζ
  exact _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo ρ.property.1 ρ.property.2 hζ

/-- **Unconditional Fourier-mode cancellation through height `184` and Sub-Farkas zero exclusion
across all heights:**
1. Every open-strip zero `ρ` of `riemannZeta` with `|Im ρ| ≤ 184` unconditionally cancels **every**
   nonzero Fourier mode `bornCoefficient ρ.val.re t k` (`k ≠ 0`) at **every** nonzero clock `t ≠ 0`
   (including the self-clock `t = ρ.val.im`), without assuming `Re ρ = 1 / 2`;
2. Unconditionally across **all** heights `Im s ∈ ℝ` (in particular for every hypothetical left-hand
   point above height `184` with `0 < Re s < 2401 / 19200`), `riemannZeta s ≠ 0` whenever
   `0 < Re s < 2401 / 19200` or `16799 / 19200 < Re s`. -/
theorem unconditional_bornCoefficient_zero_through_oneHundredEightyFour_and_sub_farkas :
    (∀ ρ : OpenStrip, |ρ.val.im| ≤ 184 → riemannZeta ρ.val = 0 →
      ρ.val.im ≠ 0 ∧
      ∀ {t : ℝ}, t ≠ 0 → ∀ {k : ℤ}, k ≠ 0 →
        Tendsto (bornCoefficient ρ.val.re t k) atTop (𝓝 0)) ∧
    (∀ s : ℂ, 0 < s.re → (s.re < 2401 / 19200 ∨ 16799 / 19200 < s.re) → riemannZeta s ≠ 0) := by
  refine ⟨fun ρ him hζ => ?_, fun s hs0 hout => ?_⟩
  · have him_ne := openStrip_zeta_zero_im_ne_zero ρ hζ
    have hre_half : ρ.val.re = 1 / 2 := by
      by_contra hne
      exact (GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
        ρ.property.1 ρ.property.2 hne him).1 hζ
    refine ⟨him_ne, fun {t} ht {k} hk => ?_⟩
    rw [hre_half, show bornCoefficient (1 / 2) t k = coefficient t k from
      funext (bornCoefficient_half t k)]
    exact nonzero_mode t ht k hk
  · rcases hout with hlt | hgt
    · exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_sub_farkas_left hs0 hlt
    · exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_farkas_lt_re hgt

/-- **Functional-equation single-mode bootstrap and sharp super-dispersion equivalence above
height `184`:** for **any single** nonzero Fourier mode `k₀ ∈ ℤ \ {0}`, the following four
statements are unconditionally equivalent:
1. `RiemannHypothesis`;
2. **All-mode full-sequence cancellation at every strip zero's self-clock `t = ρ.im`:**
   `∀ ρ : OpenStrip, riemannZeta ρ.val = 0 → ∀ k ≠ 0, Tendsto (bornCoefficient ρ.val.re ρ.val.im k) atTop (𝓝 0)`;
3. **Single-mode subsequential cancellation at every strip zero's self-clock `t = ρ.im`:**
   `∀ ρ : OpenStrip, riemannZeta ρ.val = 0 → ∃ φ → ∞, Tendsto (fun j => bornCoefficient ρ.val.re ρ.val.im k₀ (φ j)) atTop (𝓝 0)`;
4. **Uniform sub-Lorentzian bound above height `184` on `[2401 / 19200, 1 / 2)`:**
   for every `ρ` with `2401 / 19200 ≤ Re ρ < 1 / 2`, `184 < |Im ρ|`, and `riemannZeta ρ = 0`,
   some unbounded cutoff sequence `φ` satisfies `‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤ c` for a
   fixed `c < bornLorentzianLimit ρ.re ρ.im k₀`;
5. **Super-dispersion logarithmic bound above height `184` on `[2401 / 19200, 1 / 2)`:**
   for every `ρ` with `2401 / 19200 ≤ Re ρ < 1 / 2`, `184 < |Im ρ|`, and `riemannZeta ρ = 0`,
   some unbounded cutoff sequence `φ` and constant `C > bornLogDispersionCoeff ρ.re ρ.im k₀`
   satisfy `‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤ bornLorentzianLimit ρ.re ρ.im k₀ - C / log(φ j + 2)`. -/
theorem rh_iff_single_mode_subLorentzian_above_oneHundredEightyFour {k₀ : ℤ} (hk₀ : k₀ ≠ 0) :
    (RiemannHypothesis ↔
      ∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∀ k : ℤ, k ≠ 0 → Tendsto (bornCoefficient ρ.val.re ρ.val.im k) atTop (𝓝 0)) ∧
    (RiemannHypothesis ↔
      ∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          Tendsto (fun j : ℕ => bornCoefficient ρ.val.re ρ.val.im k₀ (φ j)) atTop (𝓝 0)) ∧
    (RiemannHypothesis ↔
      ∀ ρ : ℂ, 2401 / 19200 ≤ ρ.re → ρ.re < 1 / 2 → 184 < |ρ.im| → riemannZeta ρ = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          ∃ c : ℝ, c < bornLorentzianLimit ρ.re ρ.im k₀ ∧
            ∀ᶠ j : ℕ in atTop, ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤ c) ∧
    (RiemannHypothesis ↔
      ∀ ρ : ℂ, 2401 / 19200 ≤ ρ.re → ρ.re < 1 / 2 → 184 < |ρ.im| → riemannZeta ρ = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          ∃ C : ℝ, bornLogDispersionCoeff ρ.re ρ.im k₀ < C ∧
            ∀ᶠ j : ℕ in atTop,
              ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤
                bornLorentzianLimit ρ.re ρ.im k₀ - C / Real.log ((φ j + 2 : ℕ) : ℝ)) := by
  have h12 : RiemannHypothesis →
      ∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∀ k : ℤ, k ≠ 0 → Tendsto (bornCoefficient ρ.val.re ρ.val.im k) atTop (𝓝 0) := by
    intro hRH ρ hζ k hk
    have him_ne := openStrip_zeta_zero_im_ne_zero ρ hζ
    have hhaar1 := (rh_iff_unit_clock.mp hRH) ρ hζ
    have hre_half : ρ.val.re = 1 / 2 := (haar_iff_half ρ.val.re one_ne_zero).mp hhaar1
    rw [hre_half, show bornCoefficient (1 / 2) ρ.val.im k = coefficient ρ.val.im k from
      funext (bornCoefficient_half ρ.val.im k)]
    exact nonzero_mode ρ.val.im him_ne k hk
  have h23 : (∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∀ k : ℤ, k ≠ 0 → Tendsto (bornCoefficient ρ.val.re ρ.val.im k) atTop (𝓝 0)) →
      (∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          Tendsto (fun j : ℕ => bornCoefficient ρ.val.re ρ.val.im k₀ (φ j)) atTop (𝓝 0)) :=
    fun hall ρ hζ => ⟨id, tendsto_id, hall ρ hζ k₀ hk₀⟩
  have h34 : (∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          Tendsto (fun j : ℕ => bornCoefficient ρ.val.re ρ.val.im k₀ (φ j)) atTop (𝓝 0)) →
      (∀ ρ : ℂ, 2401 / 19200 ≤ ρ.re → ρ.re < 1 / 2 → 184 < |ρ.im| → riemannZeta ρ = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          ∃ c : ℝ, c < bornLorentzianLimit ρ.re ρ.im k₀ ∧
            ∀ᶠ j : ℕ in atTop, ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤ c) := by
    intro hsub ρ hlo hhi _ hζ
    obtain ⟨φ, hφ, hlim⟩ := hsub ⟨ρ, by linarith only [hlo], by linarith only [hhi]⟩ hζ
    have hL_pos : 0 < bornLorentzianLimit ρ.re ρ.im k₀ :=
      div_pos (by linarith only [hhi])
        (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith only [hhi]))
          (sq_nonneg _)))
    have hnorm0 : Tendsto (fun j => ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hlim.norm
    refine ⟨φ, hφ, bornLorentzianLimit ρ.re ρ.im k₀ / 2, half_lt_self hL_pos, ?_⟩
    filter_upwards [hnorm0.eventually (gt_mem_nhds (half_pos hL_pos))] with j hj
    exact hj.le
  have h45 : (∀ ρ : ℂ, 2401 / 19200 ≤ ρ.re → ρ.re < 1 / 2 → 184 < |ρ.im| → riemannZeta ρ = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          ∃ c : ℝ, c < bornLorentzianLimit ρ.re ρ.im k₀ ∧
            ∀ᶠ j : ℕ in atTop, ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤ c) →
      (∀ ρ : ℂ, 2401 / 19200 ≤ ρ.re → ρ.re < 1 / 2 → 184 < |ρ.im| → riemannZeta ρ = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          ∃ C : ℝ, bornLogDispersionCoeff ρ.re ρ.im k₀ < C ∧
            ∀ᶠ j : ℕ in atTop,
              ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤
                bornLorentzianLimit ρ.re ρ.im k₀ - C / Real.log ((φ j + 2 : ℕ) : ℝ)) := by
    intro hunif ρ hlo hhi him hζ
    obtain ⟨φ, hφ, c, hc_lt, hev_c⟩ := hunif ρ hlo hhi him hζ
    set C : ℝ := bornLogDispersionCoeff ρ.re ρ.im k₀ + 1
    have hC_gt : bornLogDispersionCoeff ρ.re ρ.im k₀ < C := by dsimp only [C]; linarith
    have hφ_real : Tendsto (fun j : ℕ => ((φ j + 2 : ℕ) : ℝ)) atTop atTop := by
      refine (tendsto_atTop_add_const_right atTop (2 : ℝ)
        (tendsto_natCast_atTop_atTop.comp hφ)).congr fun j => ?_
      dsimp only [Function.comp_apply]
      push_cast
      rfl
    have hdiv_zero : Tendsto (fun j : ℕ => C / Real.log ((φ j + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h0 := (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hφ_real)).const_mul C
      rw [mul_zero] at h0
      exact h0.congr fun j => by dsimp only [Function.comp_apply]; rw [div_eq_mul_inv]
    refine ⟨φ, hφ, C, hC_gt, ?_⟩
    have hgap : 0 < bornLorentzianLimit ρ.re ρ.im k₀ - c := sub_pos.mpr hc_lt
    filter_upwards [hev_c, hdiv_zero.eventually (gt_mem_nhds hgap)] with j hj_c hj_div
    linarith only [hj_c, hj_div]
  have h51 : (∀ ρ : ℂ, 2401 / 19200 ≤ ρ.re → ρ.re < 1 / 2 → 184 < |ρ.im| → riemannZeta ρ = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          ∃ C : ℝ, bornLogDispersionCoeff ρ.re ρ.im k₀ < C ∧
            ∀ᶠ j : ℕ in atTop,
              ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤
                bornLorentzianLimit ρ.re ρ.im k₀ - C / Real.log ((φ j + 2 : ℕ) : ℝ)) →
      RiemannHypothesis := by
    intro hsuper
    rw [_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
    intro w hw_half hw_one hζw
    have hw_pos : 0 < w.re := by linarith only [hw_half]
    by_cases him_le : |w.im| ≤ 184
    · exact (GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
        hw_pos hw_one hw_half.ne' him_le).1 hζw
    · have him_gt : 184 < |w.im| := lt_of_not_ge him_le
      have hstrip := MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_farkas_strip
        hw_pos hζw
      set ρ : ℂ := 1 - w
      have hρ_re : ρ.re = 1 - w.re := by simp [ρ]
      have hρ_im : |ρ.im| = |w.im| := by
        simp only [ρ, Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      have hρ_pos : 0 < ρ.re := by linarith only [hρ_re, hw_one]
      have hρ_lo : 2401 / 19200 ≤ ρ.re := by linarith only [hρ_re, hstrip.2]
      have hρ_hi : ρ.re < 1 / 2 := by linarith only [hρ_re, hw_half]
      have hρ_im_gt : 184 < |ρ.im| := by rwa [hρ_im]
      have hζρ : riemannZeta ρ = 0 :=
        _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζw hw_pos hw_one
      obtain ⟨φ, hφ, C, hC_gt, hev_le⟩ := hsuper ρ hρ_lo hρ_hi hρ_im_gt hζρ
      exact subcritical_no_subseq_superDispersion_deficit hρ_pos hρ_hi ρ.im k₀ hC_gt hφ hev_le
  exact ⟨⟨h12, fun h => h51 (h45 (h34 (h23 h)))⟩,
    ⟨fun h => h23 (h12 h), fun h => h51 (h45 (h34 h))⟩,
    ⟨fun h => h34 (h23 (h12 h)), fun h => h51 (h45 h)⟩,
    ⟨fun h => h45 (h34 (h23 (h12 h))), h51⟩⟩

/-! ### Part 5: Pole-cancelled Fermi–Mellin overtone contrast at an arbitrary strip zero -/

/-- **Additive Fermi–Mellin vs. multiplicative prime-Born contrast at an arbitrary strip zero
(without setting `Re ρ = 1 / 2`):** for **every** `ρ : OpenStrip` with `riemannZeta ρ.val = 0`
(at arbitrary height), in the Fermi–Mellin observer law `fermiMellinMeasure ρ.val.re`:
1. Both fundamental modes `k = 1` and `k = -1` at the self-clock `ρ.val.im` vanish unconditionally;
2. Infinitely many higher harmonic overtones `k ∈ ℤ` (`|k| > K₀`) are strictly nonzero. -/
theorem fermiMellin_fundamental_cancels_but_overtones_survive
    (ρ : OpenStrip) (hζ : riemannZeta ρ.val = 0) :
    (∫ t : ℝ, Complex.exp (((1 : ℤ) * ρ.val.im : ℂ) * (Real.log t : ℂ) * Complex.I)
        ∂(_root_.RHTower.fermiMellinMeasure ρ.val.re)) = 0 ∧
    (∫ t : ℝ, Complex.exp (((-1 : ℤ) * ρ.val.im : ℂ) * (Real.log t : ℂ) * Complex.I)
        ∂(_root_.RHTower.fermiMellinMeasure ρ.val.re)) = 0 ∧
    ∀ K₀ : ℕ, ∃ k : ℤ, (K₀ : ℤ) < |k| ∧
      (∫ t : ℝ, Complex.exp (((k : ℝ) * ρ.val.im : ℝ) * (Real.log t : ℂ) * Complex.I)
        ∂(_root_.RHTower.fermiMellinMeasure ρ.val.re)) ≠ 0 := by
  have hσ0 : 0 < ρ.val.re := ρ.property.1
  have hσ1 : ρ.val.re < 1 := ρ.property.2
  have him_ne : ρ.val.im ≠ 0 := openStrip_zeta_zero_im_ne_zero ρ hζ
  have hρ_eq : (ρ.val.re : ℂ) + (ρ.val.im : ℂ) * Complex.I = ρ.val := Complex.re_add_im ρ.val
  have hs1_pos : (ρ.val.re : ℂ) + (ρ.val.im : ℂ) * Complex.I ≠ 1 := by
    rw [hρ_eq]; exact fun he => hσ1.ne (by rw [he, Complex.one_re])
  have hs1_neg : (ρ.val.re : ℂ) + ((-ρ.val.im : ℝ) : ℂ) * Complex.I ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    rw [re_ofReal_add_ofReal_mul_I, Complex.one_re] at hre
    exact hσ1.ne hre
  have hζ_conj : riemannZeta ((ρ.val.re : ℂ) + ((-ρ.val.im : ℝ) : ℂ) * Complex.I) = 0 := by
    have hc : (ρ.val.re : ℂ) + ((-ρ.val.im : ℝ) : ℂ) * Complex.I = starRingEnd ℂ ρ.val := by
      apply Complex.ext
      · rw [re_ofReal_add_ofReal_mul_I, Complex.conj_re]
      · rw [im_ofReal_add_ofReal_mul_I, Complex.conj_im]
    rw [hc, riemannZeta_conj, hζ, map_zero]
  refine ⟨?_, ?_, fun K₀ => ?_⟩
  · have h1 := _root_.RHTower.integral_phase_fermiMellinMeasure_eq_zero hσ0 hs1_pos
      (by rwa [hρ_eq])
    simpa only [Int.cast_one, one_mul] using h1
  · have h2 := _root_.RHTower.integral_phase_fermiMellinMeasure_eq_zero hσ0 hs1_neg hζ_conj
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, Complex.ofReal_neg] using h2
  · have habs_pos : 0 < |ρ.val.im| := abs_pos.mpr him_ne
    have hbase_re0 : 0 < ((ρ.val.re : ℂ)).re := by simpa using hσ0
    have hbase_re1 : ((ρ.val.re : ℂ)).re < 1 := by simpa using hσ1
    obtain ⟨n, hn_ge, hζ_ne⟩ :=
      InfiniteRankPurityTheory.exists_riemannZeta_ne_zero_progression
        hbase_re0 hbase_re1 habs_pos (K₀ + 1)
    let k : ℤ := if 0 ≤ ρ.val.im then n else -n
    have hk_abs : |k| = |n| := by
      dsimp only [k]; split_ifs <;> [rfl; exact abs_neg n]
    have hk_gt : (K₀ : ℤ) < |k| := by
      rw [hk_abs]
      have hcast : ((K₀ + 1 : ℕ) : ℤ) = (K₀ : ℤ) + 1 := by push_cast; rfl
      omega
    have hk_mul : (k : ℝ) * ρ.val.im = (n : ℝ) * |ρ.val.im| := by
      dsimp only [k]
      split_ifs with hnonneg
      · rw [abs_of_nonneg hnonneg]
      · rw [abs_of_neg (lt_of_not_ge hnonneg), Int.cast_neg]; ring
    let s_k : ℂ := (ρ.val.re : ℂ) + (((k : ℝ) * ρ.val.im : ℝ) : ℂ) * Complex.I
    have hsk_eq : s_k = (ρ.val.re : ℂ) + (((n : ℝ) * |ρ.val.im| : ℝ) : ℂ) * Complex.I := by
      dsimp only [s_k]; rw [hk_mul]
    have hsk_ne1 : (ρ.val.re : ℂ) + (((k : ℝ) * ρ.val.im : ℝ) : ℂ) * Complex.I ≠ 1 := by
      intro he
      have hre := congrArg Complex.re he
      rw [re_ofReal_add_ofReal_mul_I, Complex.one_re] at hre
      exact hσ1.ne hre
    refine ⟨k, hk_gt, ?_⟩
    have hint_eq := _root_.RHTower.integral_phase_fermiMellinMeasure (σ := ρ.val.re)
      (τ := (k : ℝ) * ρ.val.im) hσ0 hsk_ne1
    rw [hint_eq]
    change (Complex.Gamma s_k * (1 - (2 : ℂ) ^ (1 - s_k)) * riemannZeta s_k) /
        ((_root_.RHTower.fermiMellinNormalizer ρ.val.re : ℝ) : ℂ) ≠ 0
    have hsk_re : s_k.re = ρ.val.re := re_ofReal_add_ofReal_mul_I _ _
    have hΓ_ne : Complex.Gamma s_k ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by rw [hsk_re]; exact hσ0)
    have htwo_ne : (1 : ℂ) - (2 : ℂ) ^ (1 - s_k) ≠ 0 := by
      intro h0
      have h2eq : ((2 : ℝ) : ℂ) ^ (1 - s_k) = 1 := by
        have := (sub_eq_zero.mp h0).symm
        simpa using this
      have hnorm := congrArg norm h2eq
      rw [norm_one, Complex.norm_cpow_eq_rpow_re_of_pos zero_lt_two] at hnorm
      have hre_pos : 0 < (1 - s_k).re := by
        rw [Complex.sub_re, Complex.one_re, hsk_re]; linarith only [hσ1]
      have hgt1 : (1 : ℝ) < (2 : ℝ) ^ (1 - s_k).re := Real.one_lt_rpow (by norm_num) hre_pos
      linarith only [hnorm, hgt1]
    have hζk_ne : riemannZeta s_k ≠ 0 := by rwa [hsk_eq]
    have hZ_ne : ((_root_.RHTower.fermiMellinNormalizer ρ.val.re : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (_root_.RHTower.fermiMellinNormalizer_pos hσ0).ne'
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hΓ_ne htwo_ne) hζk_ne) hZ_ne

#print axioms bornCoefficient_eq_sum
#print axioms tendsto_bornLaw_uniform_iff_forall_nonzero_mode
#print axioms subcritical_bornCoefficient_rotating_phasor
#print axioms subcritical_norm_bornCoefficient_tendsto
#print axioms subcritical_no_subseq_zero_mode
#print axioms subcritical_norm_bornCoefficient_log_deficit
#print axioms subcritical_bornCoefficient_sub_smooth_superPolyLog
#print axioms subcritical_eventually_norm_lt_lorentzian
#print axioms subcritical_no_subseq_superDispersion_deficit
#print axioms supercritical_bornCoefficient_tendsto
#print axioms supercritical_exists_high_mode_re_gt
#print axioms openStrip_zeta_zero_im_ne_zero
#print axioms unconditional_bornCoefficient_zero_through_oneHundredEightyFour_and_sub_farkas
#print axioms rh_iff_single_mode_subLorentzian_above_oneHundredEightyFour
#print axioms fermiMellin_fundamental_cancels_but_overtones_survive

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
