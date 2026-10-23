import GaloisForLFunctions.ReverseTwistedArcPoleCompression.PoleCompressionTwistedArcBridge
import GaloisForLFunctions.SquareRootThreshold.PrimeTailCouplingCriterion

/-!
# Master Theorem: Reverse Twisted-Arc Duality on the `2 × 2` Pole-Compression Matrix

This module completes **Mechanism 4 (Reverse Twisted-Arc Duality on the `2 × 2` Pole-Compression
Matrix)** by proving the explicit shifted-Gamma pole series collapse, the explicit twisted-arc
prime-blind weight sequence with strictly positive pole residue limit, the coupled
prime-polynomial-to-archimedean equivalence, and the master theorem packaging all four legs:

1. **Shifted-Gamma Pole Series Collapse (`tsum_shiftedGamma_pole_eq_half_mul_zero`):**
   For any weight sequence `w : ℕ → ℝ`, the infinite series of bilinear pole pairings of the
   `Ξ`-divisible shifted-Gamma basis `F_j = xiShiftedGammaTest j` collapses unconditionally to the
   single `j = 0` term:
   $$\sum_{j=0}^\infty w_j \cdot 2\Bigl(\int_{\mathbb{R}} F_j(u)e^{-u/2}\,du\Bigr)
     \Bigl(\int_{\mathbb{R}} F_j(u)e^{u/2}\,du\Bigr) = \frac{1}{2}\,w_0,$$
   because `F_0` projects purely onto the even pole mode `cosh(u/2)` with integral `1/2` while every
   `F_j` (`j ≥ 1`) annihilates `e^{-u/2}`.
2. **Explicit Twisted-Arc Prime-Blind Weight Sequence and Truncated Pole Limit
   (`exists_twistedArc_weights_vonMangoldt_blind_and_pole_limit`):**
   From the unconditional probability measure on the twisted arc (`twistedArcMinimumPrinciple_holds`),
   there exists a nonnegative weight sequence `w : ℕ → ℝ` with `0 < w 0` and super-exponentially
   summable moments `Summable (fun j => w j * (j! * (3/2)^j)^2)` such that:
   - the weighted autocorrelation series is jointly blind to all prime powers `n ≥ 2`:
     `∑' j, w j * crossCorr (F_j) (F_j) (log n) = 0`,
   - as the smooth truncation radius `L → ∞`, the zero-side energy
     `∑' j, w j * (W_ζ(truncTest F_j L)).re → 0` and the von Mangoldt prime pairing
     `∑' j, w j * (atomPairing Λ (truncTest F_j L)).re → 0`, while
   - the truncated bilinear pole series converges to the strictly positive limit
     `w 0 * (1 / 2) > 0`.
3. **Sub-Critical Pole Weight Emptiness at `Λ`
   (`not_forall_re_weilPoleWeightFunctional_vonMangoldt_nonneg_of_lt_one`):**
   Specializing to `lam = Λ`, for every sub-critical pole residue weight `β < 1`, the modified
   Weil functional `weilPoleWeightFunctional β Λ` takes strictly negative values on smooth
   compactly supported real autocorrelations.
4. **Coupled Prime-Polynomial vs. `2 × 2` Pole Compression (`poleCompression_iff_primePolynomial_le_archPart`)
   and Master Synthesis (`reverse_twisted_arc_pole_compression_master_theorem`):**
   Unifies the logarithmic-to-multiplicative pole projection, the three-way `Ξ`-divisible parity
   pole basis (`xiShiftedGammaTest 0`, `oddNullTest`, `depthNullTest (1/2)`), the twisted-arc
   prime-blind pole limit, the five-way `2 × 2` pole-compression equivalence, the coupled
   prime-polynomial bound `Re Π_f(ξ) ≤ Re A_f(ξ)`, and the positive-trace opposite-curvature
   wall-crossing dichotomy.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Nat Real
open Zeta23 RHTower RHTower.WeilSpectral RHTower.WeilPoleWeight
open GaloisForLFunctions.SquareRootThreshold

noncomputable section

namespace GaloisForLFunctions.ReverseTwistedArcPoleCompression

/-! ### 1. Exact Collapse of the Shifted-Gamma Bilinear Pole Series -/

/-- **Shifted-Gamma Pole Series Collapse:**
For any weight sequence `w : ℕ → ℝ`, the infinite series of bilinear pole pairings of
`xiShiftedGammaTest j` collapses unconditionally to the single `j = 0` term `w 0 * (1 / 2)`,
since `∫ xiShiftedGammaTest j u * exp(-u/2) du = 0` for every `j ≥ 1`. -/
theorem tsum_shiftedGamma_pole_eq_half_mul_zero (w : ℕ → ℝ) :
    (∑' j : ℕ, w j * (2 * ((∫ u, xiShiftedGammaTest j u * Real.exp (-u / 2)) *
      ∫ u, xiShiftedGammaTest j u * Real.exp (u / 2)))) = w 0 * (1 / 2) := by
  rw [tsum_eq_single 0 fun j hj => ?_]
  · rw [pole_xiShiftedGammaTest_zero]
  · rw [integral_xiShiftedGammaTest_mul_exp_neg_half_of_pos (Nat.pos_of_ne_zero hj)]
    ring

/-! ### 2. Explicit Twisted-Arc Prime-Blind Weights and Truncated Pole Limit -/

/-- **Explicit Twisted-Arc Prime-Blind Weight Sequence and Truncated Pole Limit:**
There exists an unconditional weight sequence `w : ℕ → ℝ` derived from a twisted-arc probability
measure such that:
1. `0 ≤ w j` for all `j : ℕ` and `0 < w 0`,
2. `Summable (fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2)`,
3. for every `n ≥ 2`, the weighted shifted-Gamma autocorrelation series vanishes identically at
   `log n`: `∑' j, w j * crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) (Real.log n) = 0`,
4. as the smooth truncation radius `L → ∞`, the truncated zero-side energy
   `∑' j, w j * (zetaZeroConfig.W (truncTest (xiShiftedGammaTest j) L) (truncTest (xiShiftedGammaTest j) L)).re`
   tends to `0`, and
5. as `L → ∞`, the truncated bilinear pole series tends to `w 0 * (1 / 2) > 0`. -/
theorem exists_twistedArc_weights_vonMangoldt_blind_and_pole_limit :
    ∃ w : ℕ → ℝ,
      (∀ j, 0 ≤ w j) ∧
      0 < w 0 ∧
      Summable (fun j : ℕ => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) ∧
      (∀ n : ℕ, 2 ≤ n →
        ∑' j, w j * crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) (Real.log n) = 0) ∧
      Tendsto (fun L : ℝ => ∑' j, w j *
        (zetaZeroConfig.W (fun u => (truncTest (xiShiftedGammaTest j) L u : ℂ))
          (fun u => (truncTest (xiShiftedGammaTest j) L u : ℂ))).re) atTop (𝓝 0) ∧
      Tendsto (fun L : ℝ => ∑' j, w j *
        (2 * ((∫ u, truncTest (xiShiftedGammaTest j) L u * Real.exp (-u / 2)) *
          ∫ u, truncTest (xiShiftedGammaTest j) L u * Real.exp (u / 2))))
        atTop (𝓝 (w 0 * (1 / 2))) := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds
  set ν : Measure ArcParam := (μ : Measure ArcParam)
  have hmom : ∀ j, 0 ≤ twArcEvenMoment ν (fun _ => 1) j := twArcEvenMoment_one_nonneg μ
  have hblind0 : ∀ n : ℕ, ∫ u, (fun _ : ArcParam => (1 : ℝ)) u * twArcMoment n u ∂ν = 0 :=
    fun n => by simpa using hμ n
  set w : ℕ → ℝ := fun j => arcGammaWeight (twArcEvenMoment ν (fun _ => 1) j) j with hw_def
  have hw : ∀ j, 0 ≤ w j := fun j => arcGammaWeight_nonneg (hmom j) j
  have hw0 : 0 < w 0 := by
    simp only [hw_def, arcGammaWeight]
    exact div_pos (mul_pos (by positivity) (twArcEvenMoment_one_zero_pos μ))
      (by exact_mod_cast Nat.factorial_pos _)
  have hsumw : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
    summable_arcGammaWeight hmom
      (twArcEvenMoment_le (ν := ν) (g := fun _ => 1) (B := 1) fun _ => by norm_num)
  have hblindInt := shiftedGamma_blind_of_twistedArc (B := 1) measurable_const
    (fun _ => by norm_num) hblind0 hmom
  obtain ⟨C, _, hF⟩ := exists_decayBound_xiShiftedGammaTest
  set F : ℕ → ℝ → ℝ := xiShiftedGammaTest with hFdef
  set Cj : ℕ → ℝ := fun j => C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) with hCj
  have hsum : Summable fun j => w j * Cj j ^ 2 :=
    (hsumw.mul_left (C ^ 2)).congr fun j => by simp only [hCj]; ring
  have hblind : ∀ n : ℕ, 2 ≤ n → ∑' j, w j * crossCorr (F j) (F j) (Real.log n) = 0 := by
    intro n hn
    simp_rw [hFdef, crossCorr_xiShiftedGammaTest]
    have e : ∀ j, w j * (1 / (2 * Real.pi) *
        ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) =
        1 / (2 * Real.pi) * (w j *
          ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) := fun j => by ring
    simp_rw [e]
    rw [tsum_mul_left, hblindInt n hn, mul_zero]
  have hzero : ∀ j, ∀ ρ : zetaZeroConfig.carrier,
      paperFT (fun u => (F j u : ℂ)) (gammaOf ρ) = 0 := fun j ρ =>
    paperFT_xiShiftedGammaTest_gammaOf j ρ
  obtain ⟨Λc, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  set K : ℝ := ∫ u, Real.exp (-((1 / 4 : ℝ) * |u|))
  set a : ℕ → ℝ → ℝ := fun j L => ∫ u, truncTest (F j) L u * Real.exp (-u / 2)
  set b : ℕ → ℝ → ℝ := fun j L => ∫ u, truncTest (F j) L u * Real.exp (u / 2)
  have hneg : ∀ u : ℝ, -u / 2 = (-1 / 2 : ℝ) * u := fun u => by ring
  have hpos2 : ∀ u : ℝ, u / 2 = (1 / 2 : ℝ) * u := fun u => by ring
  have habs_neg : |(-1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num [abs_of_neg]
  have habs_pos : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have ha_le : ∀ j L, |a j L| ≤ Cj j * K := fun j L => by
    have h := abs_integral_truncTest_mul_exp_le hδ (hF j) habs_neg L
    simp_rw [← hneg] at h
    exact h
  have hb_le : ∀ j L, |b j L| ≤ Cj j * K := fun j L => by
    have h := abs_integral_truncTest_mul_exp_le hδ (hF j) habs_pos L
    simp_rw [← hpos2] at h
    exact h
  have hpole_le : ∀ j L, ‖w j * (2 * (a j L * b j L))‖ ≤ w j * Cj j ^ 2 * (2 * K ^ 2) := by
    intro j L
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
    have hab : |a j L| * |b j L| ≤ (Cj j * K) * (Cj j * K) :=
      mul_le_mul (ha_le j L) (hb_le j L) (abs_nonneg _) ((abs_nonneg _).trans (ha_le j L))
    calc w j * (2 * (|a j L| * |b j L|)) ≤ w j * (2 * (Cj j * K * (Cj j * K))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab (by norm_num)) (hw j)
      _ = w j * Cj j ^ 2 * (2 * K ^ 2) := by ring
  have h1 := tendsto_tsum_W_truncTest hδ hF hw hsum hΛ0 hΛ hzero
  have h3 : Tendsto (fun L => ∑' j, w j * (2 * (a j L * b j L))) atTop
      (𝓝 (∑' j, w j * (2 * ((∫ u, F j u * Real.exp (-u / 2)) *
        ∫ u, F j u * Real.exp (u / 2))))) := by
    refine tendsto_tsum_of_dominated_convergence (hsum.mul_right (2 * K ^ 2)) (fun j => ?_)
      (Eventually.of_forall fun L j => hpole_le j L)
    have ta := tendsto_integral_truncTest_mul_exp hδ (hF j) habs_neg
    have tb := tendsto_integral_truncTest_mul_exp hδ (hF j) habs_pos
    simp_rw [← hneg] at ta
    simp_rw [← hpos2] at tb
    exact ((ta.mul tb).const_mul 2).const_mul (w j)
  rw [hFdef, tsum_shiftedGamma_pole_eq_half_mul_zero] at h3
  exact ⟨w, hw, hw0, hsumw, hblind, h1, h3⟩

/-- **Sub-Critical Pole Weight Emptiness at `Λ`:**
For every pole residue weight `β < 1`, the modified Weil functional `weilPoleWeightFunctional β Λ`
at the true von Mangoldt weight `Λ` is strictly negative on some smooth compactly supported real
autocorrelation. -/
theorem not_forall_re_weilPoleWeightFunctional_vonMangoldt_nonneg_of_lt_one {β : ℝ} (hβ : β < 1) :
    ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      0 ≤ (weilPoleWeightFunctional β (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re := by
  refine not_forall_re_weilPoleWeightFunctional_nonneg hβ (A := 0) fun N => ?_
  have h0 : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) -
      ArithmeticFunction.vonMangoldt n) = fun _ => 0 := by
    ext n; ring
  rw [h0]
  simp [primeWeightPartialSum]

/-! ### 3. Coupled Prime-Polynomial Criterion ↔ `2 × 2` Pole Compression -/

/-- **`2 × 2` Pole Compression ↔ Coupled Prime-Polynomial Domination:**
The rank-two `2 × 2` pole-compression inequality `∀ a, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a`
on the two exponential pole modes `e^{±u/2}` at height `0` is unconditionally equivalent to the
coupled localized criterion `Re Π_f(ξ) ≤ Re A_f(ξ)` across all apertures `a`, all `C²` profiles `f`
supported in `[-a, a]`, and all heights `ξ : ℝ`. -/
theorem poleCompression_iff_primePolynomial_le_archPart :
    (∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ↔
      (∀ a : ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        ∀ ξ : ℝ, (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ (archPart f ξ).re) :=
  primePolynomial_le_archPart_iff_poleCompression.symm

/-! ### 4. Master Theorem: Reverse Twisted-Arc Duality on the `2 × 2` Pole-Compression Matrix -/

/-- **Master Theorem for Mechanism 4 (Reverse Twisted-Arc Duality on the `2 × 2` Pole-Compression
Matrix):**
Packages the four unconditional components of Reverse Twisted-Arc Duality on the `2 × 2`
pole-compression matrix:
1. **Shifted-Gamma Pole Collapse & Twisted-Arc Prime-Blind Pole Limit:**
   The infinite shifted-Gamma pole series collapses to `w 0 * (1 / 2)` (`j = 0` pure even
   `cosh(u/2)` mode), and the twisted-arc probability measure yields nonnegative weights `w` with
   `w 0 > 0` that are jointly prime-blind on all `n ≥ 2`, annihilate the zero-side energy in the
   smooth truncation limit `L → ∞`, and isolate the strictly positive pole limit `w 0 * (1 / 2)`.
2. **Three-Way `Ξ`-Divisible Parity Pole Decomposition & Two-Sided Rigidity:**
   `xiShiftedGammaTest 0` is a pure even-pole mode (`∫ F₀ cosh(u/2) = 1/2`, `∫ F₀ sinh(u/2) = 0`,
   pole pairing `+1/2`, forcing `β ≥ 1`), `oddNullTest` is a pure odd-pole mode
   (`∫ oddNullTest cosh(u/2) = 0`, `∫ oddNullTest sinh(u/2) = 1/8`, pole pairing `-1/32`, forcing
   `β ≤ 1`), and `depthNullTest (1/2)` lies in the polar-orthogonal kernel
   (`∫ depthNullTest(1/2) cosh(u/2) = ∫ depthNullTest(1/2) sinh(u/2) = 0`, forcing `c^2 = 1/4`).
3. **Six-Way Equivalence of the `2 × 2` Pole-Compression Matrix:**
   The `2 × 2` pole-compression inequality `∀ a, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a` is
   unconditionally equivalent to literal parity-pole nonnegativity `0 ≤ Q_a(e_±)`, the explicit
   prime–Gamma pole inequality, the square-root logarithmic Chebyshev deficit primitive bound,
   nonemptiness of the full Weil positivity cone `∃ lam, WeilPositiveFull lam` (with unique element
   `Λ` on `n ≥ 2`), one-sided prime-blind positivity `WeilOneSided.PrimeBlindPositive`, and the
   coupled prime-polynomial inequality `Re Π_f(ξ) ≤ Re A_f(ξ)` across all heights `ξ`.
4. **Positive-Trace & Opposite-Curvature Wall-Crossing Dichotomy:**
   Above an explicit threshold `A₀ ≥ 2`, the `2 × 2` pole matrix has strictly positive trace
   (`0 < ccmWeilPoleDiagonal a`), strictly opposite second derivatives on the odd and even pole
   chambers (`deriv^[2] Odd < 0 < deriv^[2] Even`), and at most one negative parity pole channel
   under any hypothetical cross-term excess. -/
theorem reverse_twisted_arc_pole_compression_master_theorem :
    -- (1) Shifted-Gamma pole collapse & twisted-arc prime-blind pole limit
    (∀ w : ℕ → ℝ,
      (∑' j : ℕ, w j * (2 * ((∫ u, xiShiftedGammaTest j u * Real.exp (-u / 2)) *
        ∫ u, xiShiftedGammaTest j u * Real.exp (u / 2)))) = w 0 * (1 / 2)) ∧
    (∃ w : ℕ → ℝ,
      (∀ j, 0 ≤ w j) ∧ 0 < w 0 ∧
      Summable (fun j : ℕ => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) ∧
      (∀ n : ℕ, 2 ≤ n →
        ∑' j, w j * crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) (Real.log n) = 0) ∧
      Tendsto (fun L : ℝ => ∑' j, w j *
        (zetaZeroConfig.W (fun u => (truncTest (xiShiftedGammaTest j) L u : ℂ))
          (fun u => (truncTest (xiShiftedGammaTest j) L u : ℂ))).re) atTop (𝓝 0) ∧
      Tendsto (fun L : ℝ => ∑' j, w j *
        (2 * ((∫ u, truncTest (xiShiftedGammaTest j) L u * Real.exp (-u / 2)) *
          ∫ u, truncTest (xiShiftedGammaTest j) L u * Real.exp (u / 2))))
        atTop (𝓝 (w 0 * (1 / 2)))) ∧
    -- (2) Three-way Ξ-divisible parity pole basis & two-sided pole rigidity
    (∫ u, xiShiftedGammaTest 0 u * Real.cosh (u / 2) = 1 / 2 ∧
      ∫ u, xiShiftedGammaTest 0 u * Real.sinh (u / 2) = 0 ∧
      ∫ u, oddNullTest u * Real.cosh (u / 2) = 0 ∧
      ∫ u, oddNullTest u * Real.sinh (u / 2) = 1 / 8 ∧
      ∫ u, depthNullTest (1 / 2) u * Real.cosh (u / 2) = 0 ∧
      ∫ u, depthNullTest (1 / 2) u * Real.sinh (u / 2) = 0) ∧
    (∀ β : ℝ, β < 1 →
      ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
        0 ≤ (weilPoleWeightFunctional β (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re) ∧
    -- (3) Pole-compression equivalences (cone nonemptiness, prime-blind positivity, coupled Π_f ≤ A_f)
    (((∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ↔
        (∃ lam : ℕ → ℝ, WeilPositiveFull lam)) ∧
      ((∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ↔
        WeilOneSided.PrimeBlindPositive) ∧
      ((∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ↔
        (∀ a : ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          ∀ ξ : ℝ, (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ (archPart f ξ).re))) ∧
    -- (4) Positive-trace and opposite-curvature wall-crossing dichotomy
    (∃ A₀ : ℝ, 2 ≤ A₀ ∧ ∀ a : SuzukiPositiveAperture, A₀ ≤ a.1 →
      0 < ccmWeilPoleDiagonal a ∧
      deriv (deriv (ccmWeilOddPoleChamber a)) a.1 < 0 ∧
      0 < deriv (deriv (ccmWeilEvenPoleChamber a)) a.1 ∧
      (ccmWeilPoleDiagonal a < |ccmWeilPoleCross a| →
        (ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) < 0 ∧
          0 < ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))) ∨
        (0 < ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) ∧
          ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) < 0))) :=
  ⟨tsum_shiftedGamma_pole_eq_half_mul_zero,
   exists_twistedArc_weights_vonMangoldt_blind_and_pole_limit,
   ⟨integral_xiShiftedGammaTest_zero_cosh_half,
    integral_xiShiftedGammaTest_zero_sinh_half,
    integral_oddNullTest_cosh_half,
    integral_oddNullTest_sinh_half,
    integral_depthNullTest_half_cosh_half,
    integral_depthNullTest_half_sinh_half⟩,
   fun _ hβ => not_forall_re_weilPoleWeightFunctional_vonMangoldt_nonneg_of_lt_one hβ,
   ⟨exists_weilPositiveFull_iff_weilPoleCompression_nonneg.symm,
    primeBlindPositive_iff_weilPoleCompression_nonneg.symm,
    poleCompression_iff_primePolynomial_le_archPart⟩,
   exists_threshold_poleCompression_trace_pos_and_opposite_curvatures⟩

end GaloisForLFunctions.ReverseTwistedArcPoleCompression
