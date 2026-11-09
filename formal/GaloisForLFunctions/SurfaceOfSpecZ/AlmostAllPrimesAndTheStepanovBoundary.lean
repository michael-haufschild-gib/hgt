import GaloisForLFunctions.SurfaceOfSpecZ.ConfigurationsNeedAnAttainedTopAtAlmostAllPrimes
import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates
import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovBoundIsAPrimeCount
import GaloisForLFunctions.SurfaceOfSpecZ.StepanovBoundsProduceTheAbscissaLaw
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRayleighFloor

/-!
# Almost all primes and the Stepanov boundary

`AlmostAllPrimesSuffice` proves that a crude one-sided bound `2 Re S_Z(log p) ≥ −K` outside a prime
set `E` of relative logarithmic density zero puts every zero of a real-zero-free tempered
configuration `Z` on the critical line *provided* `sup Re ρ` is attained, while
`ConfigurationsNeedAnAttainedTopAtAlmostAllPrimes` refutes the unattained implication for every
half-width `0 < Θ ≤ ½` (including `sup Re ρ = 1`). This module completes the `ζ` consequences at
relative logarithmic density zero and establishes the sharp sparse-exception threshold below which
neither attainment nor `ZerosApproachLine` is needed:

* **At relative logarithmic density zero (`ζ` form):**
  `primeWindow p ≤ archPoleWindow p + K` for primes `p ∉ E` implies
  `RHTower.AsymptoticAbscissaLaw` (`asymptoticAbscissaLaw_of_primeWindow_le_primes_off_null`), and
  together with `ZerosApproachLine` is unconditionally equivalent to `RiemannHypothesis` both for a
  fixed `E` (`riemannHypothesis_iff_zerosApproachLine_and_primeWindow_le_primes_off_null`) and
  existentially over all sets `E` of relative logarithmic density zero
  (`riemannHypothesis_iff_zerosApproachLine_and_exists_primeWindow_le_primes_off_null`), while
  `not_forall_onLine_of_bddBelow_primes_off_null` shows `ZerosApproachLine` is
  configuration-theoretically irremovable.
* **Sharp positive threshold (`ShortPrimeSparse` / any power-saving `α < 1`):**
  Whenever the exceptional primes carry `< c x^θ` logarithmic mass in every short window
  `(x, x + x^θ]` for some `7/12 < θ < 1` and `c < 1` (`ShortPrimeSparse θ E`) — in particular
  whenever `#{p ≤ X : p ∈ E} ≤ C X^α` with `α < 1` (`shortPrimeSparse_of_card_le_rpow`) — Huxley's
  short-interval prime number theorem (`tendsto_theta_short_window_div_seven_twelfths`) gives
  `PowGaps θ {p | p.Prime ∧ p ∉ E}` (`powGaps_primes_diff_of_shortPrimeSparse`), so the iterated gap
  method forces every zero of *any* real-zero-free tempered configuration onto `Re s = ½` without
  attainment (`onLine_of_bddBelow_primes_off_shortPrimeSparse`,
  `onLine_of_bddBelow_primes_off_card_rpow`) and makes `primeWindow p ≤ archPoleWindow p + K`
  (`p ∉ E`) unconditionally equivalent to `RiemannHypothesis` without `ZerosApproachLine`
  (`riemannHypothesis_iff_primeWindow_le_primes_off_shortPrimeSparse`,
  `riemannHypothesis_iff_primeWindow_le_primes_off_card_rpow`).
* `prime_stepanov_phase_transition`: unified statement of the phase transition between relative
  logarithmic density zero (`α = 1 − o(1)`) and any power-saving sparsity (`α < 1`).
-/

open Complex Filter Topology Set
open scoped Chebyshev Classical

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-! ### `ζ` consequences at relative logarithmic density zero -/

/-- **Arithmetic Stepanov bound off a null prime set gives the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_primeWindow_le_primes_off_null (E : Set ℕ)
    [DecidablePred (· ∈ E)]
    (hE : Tendsto (fun σ : ℝ => wSum (fun j => primeWeight j - primeOffWeight E j) σ /
      wSum primeWeight σ) (𝓝[>] 1) (𝓝 0)) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → p ∉ E → primeWindow p ≤ archPoleWindow p + K) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_bddBelow_primes_off_null E hE (K := 2 * K) fun p hp hpE => ?_
  have h := hK p hp hpE
  rw [← orbitCorr_eq_re_lagStructure_spline]
  have := orbitCorr_log_eq_archPoleWindow_sub_primeWindow p
  linarith

/-- **At a fixed prime set `E` of relative logarithmic density zero, RH is `ZerosApproachLine` plus
the arithmetic Stepanov bound `P(p) ≤ A(p) + K` off `E`.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_primeWindow_le_primes_off_null (E : Set ℕ)
    [DecidablePred (· ∈ E)]
    (hE : Tendsto (fun σ : ℝ => wSum (fun j => primeWeight j - primeOffWeight E j) σ /
      wSum primeWeight σ) (𝓝[>] 1) (𝓝 0)) :
    RiemannHypothesis ↔ _root_.RHTower.BacklundConverse.ZerosApproachLine ∧
      ∃ K : ℝ, ∀ p : ℕ, p.Prime → p ∉ E → primeWindow p ≤ archPoleWindow p + K := by
  rw [_root_.RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw]
  refine ⟨fun ⟨hZ, hA⟩ => ⟨hZ, ?_⟩, fun ⟨hZ, K, hK⟩ =>
    ⟨hZ, asymptoticAbscissaLaw_of_primeWindow_le_primes_off_null E hE hK⟩⟩
  have hRH :=
    _root_.RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr ⟨hZ, hA⟩
  refine ⟨zetaScalingDatum.orbitCorr splineCycle 0, fun p _ _ => ?_⟩
  have h := (riemannHypothesis_iff_splineOrbit_hasseWeil.mp hRH) (Real.log p)
  rw [ScalingDatum.HasseWeilAt] at h
  have h1 := (abs_le.mp h).1
  rw [orbitCorr_log_eq_archPoleWindow_sub_primeWindow] at h1
  linarith

/-- The empty prime set has relative logarithmic density zero. -/
theorem tendsto_relLogDensity_empty :
    Tendsto (fun σ : ℝ => wSum (fun j => primeWeight j - primeOffWeight (∅ : Set ℕ) j) σ /
      wSum primeWeight σ) (𝓝[>] 1) (𝓝 0) := by
  have hzero : ∀ σ : ℝ,
      wSum (fun j => primeWeight j - primeOffWeight (∅ : Set ℕ) j) σ / wSum primeWeight σ = 0 := by
    intro σ
    have hdiff : (fun j => primeWeight j - primeOffWeight (∅ : Set ℕ) j) = fun _ => 0 := by
      ext j
      unfold primeWeight primeOffWeight
      simp
    simp [wSum, hdiff]
  simpa [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 1) (𝓝 0))

/-- **Existential `ζ` characterization at relative logarithmic density zero:** `RiemannHypothesis`
is equivalent to `ZerosApproachLine` together with the existence of a prime set `E` of relative
logarithmic density zero off which `P(p) ≤ A(p) + K`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_exists_primeWindow_le_primes_off_null :
    RiemannHypothesis ↔ _root_.RHTower.BacklundConverse.ZerosApproachLine ∧
      ∃ (E : Set ℕ) (_ : DecidablePred (· ∈ E)) (K : ℝ),
        Tendsto (fun σ : ℝ => wSum (fun j => primeWeight j - primeOffWeight E j) σ /
          wSum primeWeight σ) (𝓝[>] 1) (𝓝 0) ∧
        ∀ p : ℕ, p.Prime → p ∉ E → primeWindow p ≤ archPoleWindow p + K := by
  constructor
  · intro hRH
    obtain ⟨hZ, K, hK⟩ :=
      (riemannHypothesis_iff_zerosApproachLine_and_primeWindow_le_primes_off_null
        (∅ : Set ℕ) tendsto_relLogDensity_empty).mp hRH
    exact ⟨hZ, ∅, inferInstance, K, tendsto_relLogDensity_empty, hK⟩
  · rintro ⟨hZ, E, hdec, K, hE, hK⟩
    exact (@riemannHypothesis_iff_zerosApproachLine_and_primeWindow_le_primes_off_null
      E hdec hE).mpr ⟨hZ, K, hK⟩

/-! ### Huxley's prime number theorem in short `θ`-windows and sparse prime exceptions -/

/-- **Huxley's prime number theorem in short `θ`-windows:** for every `7/12 < θ < 1`,
`(θ(x + x^θ) − θ(x)) / x^θ → 1` as `x → ∞`. -/
theorem tendsto_theta_short_window_div_seven_twelfths {θ : ℝ} (hθ : 7 / 12 < θ) (hθ1 : θ < 1) :
    Tendsto (fun x : ℝ => (Chebyshev.theta (x + x ^ θ) - Chebyshev.theta x) / x ^ θ)
      atTop (𝓝 1) := by
  have hpsi := RHTower.tendsto_psi_short_window_div_seven_twelfths hθ hθ1
  suffices herr : Tendsto (fun x : ℝ =>
      ((Chebyshev.psi (x + x ^ θ) - Chebyshev.psi x) -
        (Chebyshev.theta (x + x ^ θ) - Chebyshev.theta x)) / x ^ θ) atTop (𝓝 0) by
    simpa [sub_div, sub_sub_cancel] using hpsi.sub herr
  have hlo := isLittleO_log_rpow_rpow_atTop (1 : ℝ) (show (0 : ℝ) < θ - 1 / 2 by linarith)
  have hlim0 : Tendsto (fun x : ℝ => 8 * (Real.log x / x ^ (θ - 1 / 2))) atTop (𝓝 0) := by
    simpa [Real.rpow_one, mul_zero] using hlo.tendsto_div_nhds_zero.const_mul 8
  refine squeeze_zero' ?_ ?_ hlim0
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 θ
    have hle : Chebyshev.theta (x + x ^ θ) - Chebyshev.theta x ≤
        Chebyshev.psi (x + x ^ θ) - Chebyshev.psi x := by
      rw [RHTower.Sieve.theta_sub_eq_sum_Ioc (by linarith)]
      exact PeriodicClusterTower.sum_prime_log_Ioc_le_psi_sub (by linarith)
    exact div_nonneg (by linarith) hxθ.le
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    set h := x ^ θ
    have hh0 : 0 < h := Real.rpow_pos_of_pos hx0 θ
    have hhx : h ≤ x := by
      calc h ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hθ1.le
        _ = x := Real.rpow_one x
    have hpt := Chebyshev.psi_sub_theta_le (x := x + h) (by linarith)
    have htp := Chebyshev.theta_le_psi x
    have hsqrt : √(x + h) ≤ 2 * x ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc (x + h) ^ (1 / 2 : ℝ) ≤ (4 * x) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ = 2 * x ^ (1 / 2 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) hx0.le]
            congr 1
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
    have hlog2 : Real.log (x + h) ≤ 2 * Real.log x := by
      have h1 : Real.log (x + h) ≤ Real.log (x * x) :=
        Real.log_le_log (by linarith) (by nlinarith)
      rw [Real.log_mul hx0.ne' hx0.ne'] at h1
      linarith
    have hsplit : h = x ^ (1 / 2 : ℝ) * x ^ (θ - 1 / 2) := by
      dsimp only [h]
      rw [← Real.rpow_add hx0]
      ring_nf
    have hdiff_le : (Chebyshev.psi (x + h) - Chebyshev.psi x) -
        (Chebyshev.theta (x + h) - Chebyshev.theta x) ≤
        8 * (x ^ (1 / 2 : ℝ) * Real.log x) := by
      have hl0 : 0 ≤ Real.log (x + h) := Real.log_nonneg (by linarith)
      have hsq0 : 0 ≤ √(x + h) := Real.sqrt_nonneg _
      have hpp : 2 * √(x + h) * Real.log (x + h) ≤ 8 * (x ^ (1 / 2 : ℝ) * Real.log x) := by
        calc 2 * √(x + h) * Real.log (x + h)
            ≤ 2 * (2 * x ^ (1 / 2 : ℝ)) * (2 * Real.log x) := by gcongr
          _ = 8 * (x ^ (1 / 2 : ℝ) * Real.log x) := by ring
      linarith
    calc ((Chebyshev.psi (x + h) - Chebyshev.psi x) -
            (Chebyshev.theta (x + h) - Chebyshev.theta x)) / h
        ≤ (8 * (x ^ (1 / 2 : ℝ) * Real.log x)) / h :=
          div_le_div_of_nonneg_right hdiff_le hh0.le
      _ = 8 * (Real.log x / x ^ (θ - 1 / 2)) := by
          have hx_half_ne : x ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
          have hx_rem_ne : x ^ (θ - 1 / 2) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
          rw [hsplit]
          field_simp

/-- Short-interval sparsity at exponent `θ`: the primes in `E ∩ (x, x + x^θ]` carry logarithmic
mass at most `c x^θ` for some `c < 1` and all large `x`. -/
def ShortPrimeSparse (θ : ℝ) (E : Set ℕ) : Prop :=
  ∃ c < (1 : ℝ), ∀ᶠ x : ℝ in atTop,
    (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E),
      Real.log (p : ℝ)) ≤ c * x ^ θ

/-- **Primes outside a `ShortPrimeSparse` set retain `O(x^θ)` gaps (`7/12 < θ < 1`).** -/
theorem powGaps_primes_diff_of_shortPrimeSparse {θ : ℝ} (hθ : 7 / 12 < θ) (hθ1 : θ < 1)
    {E : Set ℕ} (hE : ShortPrimeSparse θ E) :
    PowGaps θ {p : ℕ | p.Prime ∧ p ∉ E} := by
  refine ⟨fun p hp => hp.1.pos, ?_⟩
  obtain ⟨c, hc1, hc_ev⟩ := hE
  have hmid : (c + 1) / 2 < 1 := by linarith
  have htheta_ev := (tendsto_theta_short_window_div_seven_twelfths hθ hθ1).eventually
    (Ioi_mem_nhds hmid)
  have hex_short : ∀ᶠ y : ℝ in atTop,
      ∃ p : ℕ, (p.Prime ∧ p ∉ E) ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ := by
    filter_upwards [htheta_ev, hc_ev, eventually_gt_atTop (1 : ℝ)] with y hth hc hy1
    have hy0 : 0 < y := by linarith
    have hyθ : 0 < y ^ θ := Real.rpow_pos_of_pos hy0 θ
    rw [Set.mem_Ioi, lt_div_iff₀ hyθ] at hth
    have htot : (c + 1) / 2 * y ^ θ <
        ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊y + y ^ θ⌋₊).filter Nat.Prime, Real.log (p : ℝ) := by
      rwa [← RHTower.Sieve.theta_sub_eq_sum_Ioc (by linarith)]
    by_contra hnone
    push Not at hnone
    have hsub : (Finset.Ioc ⌊y⌋₊ ⌊y + y ^ θ⌋₊).filter Nat.Prime ⊆
        (Finset.Ioc ⌊y⌋₊ ⌊y + y ^ θ⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨hp.1, hp.2, ?_⟩
      by_contra hpE
      rw [Finset.mem_Ioc] at hp
      have hyp : y < p := (Nat.floor_lt hy0.le).mp hp.1.1
      have hpy : (p : ℝ) ≤ y + y ^ θ :=
        (Nat.cast_le.mpr hp.1.2).trans (Nat.floor_le (by positivity))
      exact absurd hpy (not_le.mpr (hnone p ⟨hp.2, hpE⟩ hyp))
    have hsum_le : (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊y + y ^ θ⌋₊).filter Nat.Prime, Real.log (p : ℝ)) ≤
        ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊y + y ^ θ⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E),
          Real.log (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt.le)
    have : (c + 1) / 2 * y ^ θ < c * y ^ θ := htot.trans_le (hsum_le.trans hc)
    have : c * y ^ θ < (c + 1) / 2 * y ^ θ :=
      mul_lt_mul_of_pos_right (by linarith) hyθ
    linarith
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hex_short
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < 1 - θ by linarith)).eventually_ge_atTop 2).and
      ((eventually_ge_atTop (2 * max Y 0)).and (eventually_gt_atTop (0 : ℝ))))
  refine ⟨1, X, zero_le_one, fun x hx => ?_⟩
  obtain ⟨hx2, hxY, hx0⟩ := hX x hx
  have hsplit : x = x ^ θ * x ^ (1 - θ) := by
    rw [← Real.rpow_add hx0, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  have hxθ0 : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  have hxθ : 2 * x ^ θ ≤ x := by
    calc 2 * x ^ θ ≤ x ^ (1 - θ) * x ^ θ := mul_le_mul_of_nonneg_right hx2 hxθ0.le
      _ = x := by rw [mul_comm, ← hsplit]
  set y := x - x ^ θ
  have hyY : Y ≤ y := by linarith [le_max_left Y 0]
  have hy0 : 0 ≤ y := by linarith [le_max_right Y 0]
  obtain ⟨p, hp, hyp, hpy⟩ := hY y hyY
  have hyθ : y ^ θ ≤ x ^ θ := Real.rpow_le_rpow hy0 (by linarith) (by linarith)
  exact ⟨p, hp, by linarith, by linarith⟩

/-- **Any power-saving global prime count `#{p ≤ X : p ∈ E} ≤ C X^α` (`α < 1`) implies
`ShortPrimeSparse (max ((α + 1) / 2) (2 / 3)) E`.** -/
theorem shortPrimeSparse_of_card_le_rpow {α C : ℝ} (hα1 : α < 1) {E : Set ℕ}
    (hE : ∀ᶠ X : ℝ in atTop,
      (((Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E)).card : ℝ) ≤ C * X ^ α) :
    ShortPrimeSparse (max ((α + 1) / 2) (2 / 3)) E := by
  set θ : ℝ := max ((α + 1) / 2) (2 / 3)
  have hθ_gt_α : α < θ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hθ_lt_1 : θ < 1 := max_lt (by linarith) (by norm_num)
  have hθ_pos : 0 < θ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨1 / 2, by norm_num, ?_⟩
  have h2x_ev : ∀ᶠ x : ℝ in atTop,
      (((Finset.Icc 1 ⌊2 * x⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E)).card : ℝ) ≤
        C * (2 * x) ^ α :=
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually hE
  have hlo := isLittleO_log_rpow_rpow_atTop (1 : ℝ) (show 0 < θ - α by linarith)
  set K : ℝ := max C 0 * (2 : ℝ) ^ α * 2
  have hlim : Tendsto (fun x : ℝ => K * (Real.log x / x ^ (θ - α))) atTop (𝓝 0) := by
    simpa [Real.rpow_one, mul_zero] using hlo.tendsto_div_nhds_zero.const_mul K
  filter_upwards [h2x_ev, hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (2 : ℝ)] with x hcard hsmall hx2
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxθ_le_x : x ^ θ ≤ x := by
    calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hθ_lt_1.le
      _ = x := Real.rpow_one x
  have hsub : (Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E) ⊆
      (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hp.2.1.pos, ?_⟩, hp.2⟩
    exact hp.1.2.trans (Nat.floor_le_floor (by linarith))
  have hlog_bound : ∀ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E),
      Real.log (p : ℝ) ≤ 2 * Real.log x := by
    intro p hp
    have hp2 := hsub hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp2
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp2.2.1.pos
    have hp_le_2x : (p : ℝ) ≤ 2 * x :=
      (Nat.cast_le.mpr hp2.1.2).trans (Nat.floor_le (by linarith))
    calc Real.log (p : ℝ) ≤ Real.log (x * x) := Real.log_le_log hp_pos (by nlinarith)
      _ = 2 * Real.log x := by rw [Real.log_mul hx0.ne' hx0.ne']; ring
  have hcard_le :
      (((Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E)).card : ℝ) ≤
        max C 0 * (2 : ℝ) ^ α * x ^ α := by
    calc (((Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E)).card : ℝ)
        ≤ (((Finset.Icc 1 ⌊2 * x⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E)).card : ℝ) :=
          by exact_mod_cast Finset.card_le_card hsub
      _ ≤ C * (2 * x) ^ α := hcard
      _ ≤ max C 0 * (2 * x) ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (by linarith) α)
      _ = max C 0 * (2 : ℝ) ^ α * x ^ α := by
          rw [Real.mul_rpow (by norm_num) hx0.le]; ring
  have hxθ_pos : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  have hsplit : x ^ α * x ^ (θ - α) = x ^ θ := by
    rw [← Real.rpow_add hx0]; ring_nf
  calc (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E),
          Real.log (p : ℝ))
      ≤ ∑ _p ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E),
          (2 * Real.log x) := Finset.sum_le_sum hlog_bound
    _ = (((Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E)).card : ℝ) *
          (2 * Real.log x) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (max C 0 * (2 : ℝ) ^ α * x ^ α) * (2 * Real.log x) :=
        mul_le_mul_of_nonneg_right hcard_le (mul_nonneg (by norm_num) (Real.log_nonneg hx1))
    _ = (K * (Real.log x / x ^ (θ - α))) * x ^ θ := by
        have hx_rem_ne : x ^ (θ - α) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
        rw [← hsplit]
        dsimp only [K]
        field_simp
    _ ≤ 1 / 2 * x ^ θ := mul_le_mul_of_nonneg_right hsmall.le hxθ_pos.le

/-! ### Unconditional configuration rigidity and `ζ` equivalences below the threshold -/

/-- **Unattained configuration rigidity off a `ShortPrimeSparse` set (`7/12 < θ < 1`).** -/
theorem onLine_of_bddBelow_primes_off_shortPrimeSparse {θ : ℝ} (hθ : 7 / 12 < θ) (hθ1 : θ < 1)
    {E : Set ℕ} (hE : ShortPrimeSparse θ E)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → p ∉ E → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_bddBelow_of_powGaps Z hZ hnoreal hθ1
    (powGaps_primes_diff_of_shortPrimeSparse hθ hθ1 hE) fun p hp => hK p hp.1 hp.2

/-- **Unattained configuration rigidity off any power-saving prime exception set (`α < 1`).** -/
theorem onLine_of_bddBelow_primes_off_card_rpow {α C : ℝ} (hα1 : α < 1) {E : Set ℕ}
    (hE : ∀ᶠ X : ℝ in atTop,
      (((Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E)).card : ℝ) ≤ C * X ^ α)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → p ∉ E → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_bddBelow_primes_off_shortPrimeSparse
    (lt_of_lt_of_le (by norm_num : (7 : ℝ) / 12 < 2 / 3) (le_max_right _ _))
    (max_lt (by linarith) (by norm_num))
    (shortPrimeSparse_of_card_le_rpow hα1 hE) Z hZ hnoreal hK

/-- **Unconditional RH equivalence off a `ShortPrimeSparse` prime set (`7/12 < θ < 1`), with no
`ZerosApproachLine` hypothesis.** -/
theorem riemannHypothesis_iff_primeWindow_le_primes_off_shortPrimeSparse {θ : ℝ}
    (hθ : 7 / 12 < θ) (hθ1 : θ < 1) {E : Set ℕ} (hE : ShortPrimeSparse θ E) :
    RiemannHypothesis ↔
      ∃ K : ℝ, ∀ p : ℕ, p.Prime → p ∉ E → primeWindow p ≤ archPoleWindow p + K := by
  rw [riemannHypothesis_iff_primeWindow_le_of_powGaps hθ1
    (powGaps_primes_diff_of_shortPrimeSparse hθ hθ1 hE)]
  exact ⟨fun ⟨K, hK⟩ => ⟨K, fun p hp hpE => hK p ⟨hp, hpE⟩⟩,
    fun ⟨K, hK⟩ => ⟨K, fun p hp => hK p hp.1 hp.2⟩⟩

/-- **Unconditional RH equivalence off any power-saving prime exception set (`α < 1`), with no
`ZerosApproachLine` hypothesis.** -/
theorem riemannHypothesis_iff_primeWindow_le_primes_off_card_rpow {α C : ℝ} (hα1 : α < 1)
    {E : Set ℕ}
    (hE : ∀ᶠ X : ℝ in atTop,
      (((Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E)).card : ℝ) ≤ C * X ^ α) :
    RiemannHypothesis ↔
      ∃ K : ℝ, ∀ p : ℕ, p.Prime → p ∉ E → primeWindow p ≤ archPoleWindow p + K :=
  riemannHypothesis_iff_primeWindow_le_primes_off_shortPrimeSparse
    (lt_of_lt_of_le (by norm_num : (7 : ℝ) / 12 < 2 / 3) (le_max_right _ _))
    (max_lt (by linarith) (by norm_num))
    (shortPrimeSparse_of_card_le_rpow hα1 hE)

/-- **Phase transition for one-sided Stepanov bounds at primes.**
1. *Failure at relative logarithmic density zero (`α = 1 − o(1)`):* there exist a real-zero-free
   tempered configuration `Z` with `sup Re ρ = 1` and a prime set `E` of relative logarithmic
   density zero with `2 Re S_Z(log p) ≥ −5` for all primes `p ∉ E`.
2. *Unconditional rigidity at every power-saving sparsity (`α < 1`):* if
   `#{p ≤ X : p ∈ E} ≤ C X^α` with `α < 1`, then `2 Re S_Z(log p) ≥ −K` (`p ∉ E`) puts every zero
   of any real-zero-free tempered configuration `Z` on `Re s = ½` without attainment, and
   `P(p) ≤ A(p) + K` (`p ∉ E`) is unconditionally equivalent to `RiemannHypothesis`. -/
theorem prime_stepanov_phase_transition :
    (∃ (Z : ZeroConfig) (E : Set ℕ) (_ : DecidablePred (· ∈ E)),
      TemperedConfig Z ∧
      (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      (∀ β < (1 : ℝ), ∃ ρ ∈ Z.carrier, β < ρ.re) ∧
      Tendsto
        (fun σ : ℝ => wSum (fun j => primeWeight j - primeOffWeight E j) σ / wSum primeWeight σ)
        (𝓝[>] 1) (𝓝 0) ∧
      (∀ p : ℕ, p.Prime → p ∉ E → -5 ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re)) ∧
    (∀ {α C : ℝ}, α < 1 → ∀ {E : Set ℕ},
      (∀ᶠ X : ℝ in atTop,
        (((Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E)).card : ℝ) ≤ C * X ^ α) →
      (∀ (Z : ZeroConfig), TemperedConfig Z → (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) →
        ∀ {K : ℝ}, (∀ p : ℕ, p.Prime → p ∉ E →
          -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) →
        ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ∧
      (RiemannHypothesis ↔
        ∃ K : ℝ, ∀ p : ℕ, p.Prime → p ∉ E → primeWindow p ≤ archPoleWindow p + K)) :=
  ⟨exists_zeroConfig_primes_off_null_bddBelow_sup_eq_one,
    fun hα1 hE => ⟨fun Z hZ hnoreal {_} hK => onLine_of_bddBelow_primes_off_card_rpow hα1 hE Z hZ
      hnoreal hK, riemannHypothesis_iff_primeWindow_le_primes_off_card_rpow hα1 hE⟩⟩

end GaloisForLFunctions.SurfaceOfSpecZ
