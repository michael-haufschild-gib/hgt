import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.EveryFlippedPrimeIsSeenAtLargeOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheOverlapGramHasBoundedRows

/-!
# No fixed overlap sees every flip

Flipping the odd powers of a prime `p` moves Weil's form on a test `f` by at most
`Σ_{k odd} (4 log p/p^{k/2}) ∫ f² ≤ (8 log p/√p) ∫ f²`, since each lag pairing is bounded by the
`L²` mass (Cauchy–Schwarz). At a fixed overlap `c` the `L²` mass of an atomic test is at most
`(1 + 2c e^c) ‖g‖² Σ x_n²`, while the complete form of `ζ` is eventually at least
`(E(c)/2) ‖g‖² Σ x_n²`, `E(c) > 0` the completed shell energy (the bottom of the spectrum). Hence
for every `p` with `8(1 + 2c e^c) log p/√p < E(c)/2` the flipped form stays positive definite on
the atomic families at overlap `c` (`eventually_flip_posDef_of_large_prime`).

Together with `exists_flip_negative_at_every_large_overlap`, the threshold `c*(p)` of the `p`-flip
is finite for every prime and tends to infinity with `p`: selectivity at bounded overlap holds
for each single-prime twin but is not uniform in the prime.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticLorentzianGeometry CompletedShell
  CriticalArithmeticCorrelationTheory
open _root_.RHTower (vonMangoldtAtom)

/-- Each lag pairing is at most twice the `L²` mass. -/
theorem abs_pairing_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (k : ℕ) :
    |pairing f k| ≤ 2 * ∫ t, f t ^ 2 := by
  have h1 := abs_integral_mul_shift_le hf hfc hf hfc (-Real.log k)
  have h2 := abs_integral_mul_shift_le hf hfc hf hfc (Real.log k)
  have hs : Real.sqrt (∫ t, f t ^ 2) * Real.sqrt (∫ t, f t ^ 2) = ∫ t, f t ^ 2 :=
    Real.mul_self_sqrt (integral_nonneg fun t => sq_nonneg _)
  rw [hs] at h1 h2
  simp only [← sub_eq_add_neg] at h1
  rw [pairing]
  linarith [abs_add_le (∫ t, f t * f (t - Real.log k)) (∫ t, f t * f (t + Real.log k))]

open Classical in
/-- The square-root mass of the prime powers of `p ≥ 4` is at most `2/√p`. -/
theorem sum_primePow_inv_sqrt_le {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) (K : ℕ) :
    ∑ k ∈ range K, (if ∃ j, k = p ^ (j + 1) then 1 / Real.sqrt k else 0) ≤
      2 / Real.sqrt p := by
  have hp2 := hp.two_le
  have hsp : 2 ≤ Real.sqrt p := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hp4)
  set r := 1 / Real.sqrt p with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ≤ 1 / 2 := by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hsp
  have hsub : (range K).filter (fun k => ∃ j, k = p ^ (j + 1)) ⊆
      (range K).image (fun j => p ^ (j + 1)) := by
    intro k hk
    obtain ⟨hkK, j, rfl⟩ := mem_filter.mp hk
    refine mem_image.mpr ⟨j, mem_range.mpr ?_, rfl⟩
    exact ((Nat.lt_succ_self j).trans (Nat.lt_pow_self (by omega : 1 < p))).trans (mem_range.mp hkK)
  have hinj : Set.InjOn (fun j => p ^ (j + 1)) (range K) := fun i _ j _ hij =>
    by simpa using Nat.pow_right_injective hp2 hij
  rw [← sum_filter]
  calc ∑ k ∈ (range K).filter (fun k => ∃ j, k = p ^ (j + 1)), 1 / Real.sqrt k
      ≤ ∑ k ∈ (range K).image (fun j => p ^ (j + 1)), 1 / Real.sqrt k :=
        sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity
    _ = ∑ j ∈ range K, 1 / Real.sqrt ((p ^ (j + 1) : ℕ) : ℝ) := sum_image hinj
    _ = ∑ j ∈ range K, r * r ^ j := sum_congr rfl fun j _ => by
        rw [Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p),
          mul_comm, Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast, ← Real.sqrt_eq_rpow, hr,
          ← pow_succ', one_div_pow]
    _ ≤ ∑ j ∈ range K, r * (1 / 2 : ℝ) ^ j := sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr2 j) hr0
    _ = r * ∑ j ∈ range K, (1 / 2 : ℝ) ^ j := by rw [mul_sum]
    _ ≤ r * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le K) hr0
    _ = 2 / Real.sqrt p := by rw [hr]; ring

open Classical in
/-- **The flip is a small perturbation for large primes**: it moves Weil's form on a test by at
most `(8 log p/√p) ∫ f²`. -/
theorem abs_weilQuadTw_flip_sub_le {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) (N : ℕ) (x : ℕ → ℝ) :
    |weilQuadTw (ArithmeticCountingPositivity.primeFlipWeight p) (atomicTest N x g) -
        weilQuad (atomicTest N x g)| ≤
      8 * Real.log p / Real.sqrt p * ∫ t, atomicTest N x g t ^ 2 := by
  set f := atomicTest N x g
  have hf := (contDiff_atomicTest hg N x).continuous
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  set M := ∫ t, f t ^ 2
  have hM0 : 0 ≤ M := integral_nonneg fun t => sq_nonneg _
  rw [weilQuadTw_eq _ (supportedIn_atomicTest hgsupp hw N x), add_sub_cancel_left,
    Finset.sum_congr rfl fun k _ => by rw [vonMangoldtAtom_sub_twistCoeff_flip]]
  have hterm : ∀ k ∈ range (lagRange (Real.log N + w + 1)),
      |(1 - finiteFlip {p} k) * vonMangoldtAtom k * pairing f k| ≤
        4 * Real.log p * M * (if ∃ j, k = p ^ (j + 1) then 1 / Real.sqrt k else 0) := by
    intro k _
    rcases flip_coeff_cases hp k with h0 | ⟨j, hkj, hc⟩
    · rw [h0, zero_mul, abs_zero]
      exact mul_nonneg (by positivity) (by split_ifs <;> positivity)
    · rw [if_pos ⟨j, hkj⟩, abs_mul]
      calc |(1 - finiteFlip {p} k) * vonMangoldtAtom k| * |pairing f k|
          ≤ (2 * Real.log p / Real.sqrt k) * (2 * M) :=
            mul_le_mul hc (abs_pairing_le hf hfc k) (abs_nonneg _) (by positivity)
        _ = 4 * Real.log p * M * (1 / Real.sqrt k) := by ring
  calc |∑ k ∈ range (lagRange (Real.log N + w + 1)), (1 - finiteFlip {p} k) * vonMangoldtAtom k *
        pairing f k|
      ≤ ∑ k ∈ range (lagRange (Real.log N + w + 1)),
        4 * Real.log p * M * (if ∃ j, k = p ^ (j + 1) then 1 / Real.sqrt k else 0) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = 4 * Real.log p * M * ∑ k ∈ range (lagRange (Real.log N + w + 1)),
        (if ∃ j, k = p ^ (j + 1) then 1 / Real.sqrt k else 0) := by rw [mul_sum]
    _ ≤ 4 * Real.log p * M * (2 / Real.sqrt p) :=
        mul_le_mul_of_nonneg_left (sum_primePow_inv_sqrt_le hp hp4 _)
          (mul_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg p)) hM0)
    _ = 8 * Real.log p / Real.sqrt p * M := by ring

/-- `log p/√p → 0`. -/
theorem tendsto_log_div_sqrt_natCast :
    Tendsto (fun p : ℕ => Real.log p / Real.sqrt p) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h' := h.comp tendsto_natCast_atTop_atTop
  refine h'.congr fun p => ?_
  simp only [Function.comp_apply, Real.sqrt_eq_rpow]

/-- **No fixed overlap sees every flip.** At every overlap `c > 0`, for all sufficiently large
primes `p` the `p`-flipped Weil form is eventually positive on every nonzero atomic test of the
tilted unit spline at width `c/N`. -/
theorem eventually_flip_posDef_of_large_prime {c : ℝ} (hc : 0 < c) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      (∃ n ∈ Icc 1 N, x n ≠ 0) →
        0 < weilQuadTw (ArithmeticCountingPositivity.primeFlipWeight p)
          (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) := by
  -- the margin of `ζ`: the completed shell energy is positive
  obtain ⟨e, he, hfloor⟩ := exists_tiltedUnitSpline_conductor_floor hc
  set E := completedShellEnergy tiltedUnitSpline c with hEdef
  have hE : e ≤ E := by
    have := hfloor 1 one_pos
    rwa [completedConductorEnergy_one] at this
  have hE0 : 0 < E := he.trans_le hE
  set B := 1 + 2 * c * Real.exp c with hB
  have hB0 : 0 < B := by positivity
  -- large primes perturb by less than half the margin
  have hsmall := (tendsto_log_div_sqrt_natCast.const_mul (8 * B)).eventually
    (gt_mem_nhds (show 8 * B * 0 < E / 2 by rw [mul_zero]; exact half_pos hE0))
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.mp hsmall
  refine ⟨max p₁ 4, fun p hp hpp => ?_⟩
  have hp4 : 4 ≤ p := (le_max_right _ _).trans hpp
  have hpert := hp₁ p ((le_max_left _ _).trans hpp)
  filter_upwards [tiltedUnitSpline_spectrum_bottom hc (half_pos hE0), eventually_ge_atTop 1]
    with N hN hN1 x hx
  obtain ⟨hbot, -⟩ := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc hN0
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw0
  set g := atomDilate tiltedUnitSpline (c / N) with hgdef
  set G0 := ∫ u, g u ^ 2 with hG0def
  have hG0 : 0 < G0 := by
    rw [hG0def, hgdef, integral_atomDilate_sq hw0]; exact mul_pos hw0 integral_tiltedUnitSpline_sq_pos
  set S := ∑ n ∈ Icc 1 N, x n ^ 2 with hSdef
  have hS : 0 < S := by
    obtain ⟨n, hn, hxn⟩ := hx
    exact lt_of_lt_of_le (pow_pos (abs_pos.mpr hxn) 2 |>.trans_eq (sq_abs _))
      (single_le_sum (fun m _ => sq_nonneg (x m)) hn)
  -- `ζ`'s form is at least half the margin
  set xv : EuclideanSpace ℝ (PrimeHorizonIndex N) := WithLp.toLp 2 (fun n => x n) with hxv
  have hnorm : ‖xv‖ ^ 2 = S := by
    rw [EuclideanSpace.real_norm_sq_eq, hSdef, ← Finset.sum_coe_sort (Icc 1 N)]
  have hzeta : G0 * (E / 2 * S) ≤ weilQuad (atomicTest N x g) := by
    have h := completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero hc hN1 xv
    rw [← atomicTest_restrict] at h
    have hlow : E / 2 * ‖xv‖ ^ 2 ≤
        inner ℝ (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) xv) xv := by
      rw [HTGeometry.hermitianEnergy_eq_sum (completeWeilMatrix_isHermitian tiltedUnitSpline c N),
        ← (completeWeilMatrix_isHermitian tiltedUnitSpline c N).eigenvectorBasis.sum_sq_inner_left xv,
        mul_sum]
      refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have := hbot i
      rw [completeWeilEigenvalue] at this
      linarith
    rw [h, hnorm] at hlow
    rw [← hgdef, ← hG0def] at hlow
    rw [le_div_iff₀ hG0] at hlow
    linarith
  -- the flip perturbation
  have hmass := integral_atomicTest_sq_le_fixed_overlap hg.continuous hgc hc hN1 hgsupp x
  have hdiff := abs_weilQuadTw_flip_sub_le hg hgsupp hw0.le hp hp4 N x
  have hlp : 0 ≤ 8 * Real.log p / Real.sqrt p :=
    div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg p)) (Real.sqrt_nonneg _)
  have hpertG : 8 * Real.log p / Real.sqrt p * ∫ t, atomicTest N x g t ^ 2 ≤
      8 * Real.log p / Real.sqrt p * (G0 * B * S) :=
    mul_le_mul_of_nonneg_left hmass hlp
  have hsmallG : 8 * Real.log p / Real.sqrt p * (G0 * B * S) < G0 * (E / 2 * S) := by
    have h1 : 8 * B * (Real.log p / Real.sqrt p) < E / 2 := hpert
    have : 8 * Real.log p / Real.sqrt p * (G0 * B * S) =
        G0 * S * (8 * B * (Real.log p / Real.sqrt p)) := by ring
    rw [this, show G0 * (E / 2 * S) = G0 * S * (E / 2) by ring]
    exact mul_lt_mul_of_pos_left h1 (mul_pos hG0 hS)
  linarith [(abs_le.mp hdiff).1]

/-- **The flip threshold is finite and unbounded.** For the tilted unit spline every prime `p`
is seen at every overlap beyond some `c₀(p)`, while at every fixed overlap all sufficiently large
flipped primes remain positive. -/
theorem tiltedUnitSpline_flip_threshold_finite_and_unbounded :
    (∀ p : ℕ, p.Prime → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c, c₀ ≤ c → ∀ᶠ N : ℕ in atTop,
      weilQuadTw (ArithmeticCountingPositivity.primeFlipWeight p)
        (atomicTest N (fun n => TransMetzlerWeilPositivity.BoundedOverlap.primeSquareTrial p n /
          Real.sqrt n) (atomDilate tiltedUnitSpline (c / N))) < 0) ∧
    ∀ c : ℝ, 0 < c → ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      (∃ n ∈ Icc 1 N, x n ≠ 0) →
        0 < weilQuadTw (ArithmeticCountingPositivity.primeFlipWeight p)
          (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) :=
  ⟨fun _ hp => exists_flip_negative_at_every_large_overlap contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hp,
   fun _ hc => eventually_flip_posDef_of_large_prime hc⟩

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
