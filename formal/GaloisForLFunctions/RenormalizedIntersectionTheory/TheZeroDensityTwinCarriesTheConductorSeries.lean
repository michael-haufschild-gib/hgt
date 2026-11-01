import GaloisForLFunctions.RenormalizedIntersectionTheory.TheExcitedResolventOfAFiniteFlip
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRoughMeanAtAFixedScale
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheConductorSeriesSeparatesTheZeroDensityTwins
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanPlacePaysTheTowerDeficit

/-!
# The zero-density twin carries the conductor series

Let `P` be a set of primes of relative logarithmic density `κ ∈ (0, 1/4)`, `ω = ω_P` its flip twin,
`v = v_P` the normalized horizon vector (`primeSetHorizonVector`), `c_N` the harmonic correlation and
`W_P(s) = Σ_{m≥2} w_P(m)/(E_m − γ − s)` the conductor series.

**Spectral weight at precision `c_N²`** (`eventually_inner_sq_le_conductorSeries`): if every partial sum
of `W_P(s)` is at most `W`, then for every `ε > 0`, eventually, for the ground eigenvector `e_0` and every
`w ⊥ e_0`,
`⟨w, v⟩² ≤ c_N² (W + ε)(Q_N(w) − s|w|²)`,
i.e. the excited resolvent of `v` is at most `c_N² (W_P(s) + o(1))`. The proof splits
`ω⃗ = μ ω⃗_F + P_T(ω⃗ − μ ω⃗_F) + (ω⃗ − P_T ω⃗)` with `F` the flipped primes below `T`, `μ = c_N/δ_F`:
* the finite flip carries `δ_F² W_F(s) ≤ δ_F² W` (`eventually_excitedResolvent_finiteFlip_le`);
* the fixed-scale defect is `o(c_N)` (`eventually_fixedScaleDefect_le`);
* the rough fluctuations cost `(log T)^{2κ − 1/2} c_N + O((log N)^{−1/2})`
  (`exists_abs_inner_twin_sub_starProjection_le`), with `c_N ≍ (log N)^{−2κ}`
  (`exists_pos_mul_rpow_le_gaugeHarmonicSum_primeSetFlip`) and `D_N ≤ C (Q_N − s)` off the ground.

**Maximal margin** (`primeSetFlip_hasHyperplaneGap_of_conductorSeries`): if every partial sum of
`W_P(s)` is at most `1/s` on `(0, 2 log 2)`, the twin has margin `2 log 2`. The ground coordinate of `v`
is `c_N (1 + o(1))` (the estimate applied to the excited part of the pole vector, whose energy tends to
`0`), and a vector `u ⊥ v` with ground coordinate `a` has `a² ≤ (W + ε) G/(1 − o(1))²`.

**Classification** (`hodgeSeparates_primeSetFlip_iff_packet`): a flip twin of relative log density
`κ ∈ (0, 1/4)` is separated from `ζ` by the atomic Hodge index iff some finite packet of conductors has
`Σ w_P(m)/(E_m − γ − s) > 1/s` for some `s ∈ (0, 2 log 2)`.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (PrimeHorizonIndex fullPrimeMatrix
  fullPrimeMatrix_isHermitian fullPrimeEnergyEigenvalue poleDefect poleDefect_nonneg finiteFlip
  smoothSet roughHarmonic roughInterval mem_smoothSet mem_roughInterval one_le_roughHarmonic
  ramanujanAdjunctionEnergy truncPole poleVector atomicWeilForm_congr)
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (gaugeHarmonicSum horizonExtend
  sum_horizonExtend atomicWeilForm_horizonExtend HasHyperplaneGap gaugeHarmonicSum_one_pos)
open GaloisForLFunctions.ArithmeticElectrostatics (atomicWeilForm)

local notation "γ" => Real.eulerMascheroniConstant

section Plumbing

/-- A finite flip only sees the prime factors of `n`. -/
theorem finiteFlip_eq_of_primeFactors {F F' : Finset ℕ} {n : ℕ}
    (h : ∀ p ∈ n.primeFactors, p ∈ F ↔ p ∈ F') : finiteFlip F n = finiteFlip F' n := by
  classical
  have key : ∀ G : Finset ℕ, finiteFlip G n =
      ∏ p ∈ G.filter (· ∈ n.primeFactors), (-1 : ℝ) ^ (n.factorization p) := by
    intro G
    unfold finiteFlip
    rw [prod_filter]
    refine prod_congr rfl fun p _ => ?_
    split_ifs with hp
    · rfl
    · rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero]
  rw [key, key]
  congr 1
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(h p h2).mp h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(h p h2).mpr h1, h2⟩

/-- On `T`-smooth `n` the twin is the finite flip of the flipped primes below `T`. -/
theorem primeSetFlip_eq_finiteFlip_of_smooth (P : Set ℕ) {T n : ℕ}
    (hs : ∀ p ∈ n.primeFactors, p < T) :
    primeSetFlip P n = finiteFlip (primeSetCutoff P (T - 1)) n := by
  rw [primeSetFlip_eq_finiteFlip_of_le P (le_refl n)]
  refine finiteFlip_eq_of_primeFactors fun p hp => ?_
  rw [mem_primeSetCutoff, mem_primeSetCutoff]
  have hpn := Nat.le_of_mem_primeFactors hp
  have hpT := hs p hp
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
  · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨⟨hpn, h2⟩, h3⟩

theorem finiteFlip_eq_one_of_rough {F : Finset ℕ} {T b : ℕ} (hF : ∀ p ∈ F, p < T)
    (hb : ∀ p ∈ b.primeFactors, T ≤ p) : finiteFlip F b = 1 := by
  unfold finiteFlip
  refine prod_eq_one fun p hp => ?_
  have : b.factorization p = 0 := by
    by_contra h
    have := hb p (by rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr h)
    have := hF p hp
    omega
  rw [this, pow_zero]

theorem finiteFlip_smoothPart {F : Finset ℕ} {T : ℕ} (hF : ∀ p ∈ F, p < T) (n : ℕ) :
    finiteFlip F (smoothPart T n) = finiteFlip F n := by
  unfold finiteFlip
  refine prod_congr rfl fun p hp => ?_
  rw [factorization_smoothPart, Finsupp.filter_apply, if_pos (hF p hp)]

/-- The finite flip below `T` lies in the `T`-smooth fibre space. -/
theorem gaugeVector_finiteFlip_mem {F : Finset ℕ} {T : ℕ} (hF : ∀ p ∈ F, p < T) (N : ℕ) :
    gaugeVector N (finiteFlip F) ∈ smoothFibreSpace T N := by
  intro i j hij
  have hi0 : (0 : ℝ) < (i : ℕ) := by exact_mod_cast (mem_Icc.mp i.2).1
  have hj0 : (0 : ℝ) < (j : ℕ) := by exact_mod_cast (mem_Icc.mp j.2).1
  simp only [gaugeVector, WithLp.ofLp_toLp]
  rw [mul_div_cancel₀ _ (Real.sqrt_pos.mpr hi0).ne', mul_div_cancel₀ _ (Real.sqrt_pos.mpr hj0).ne',
    ← finiteFlip_smoothPart hF i, hij, finiteFlip_smoothPart hF j]

theorem primeSetCutoff_lt (P : Set ℕ) {T : ℕ} (hT : 1 ≤ T) :
    ∀ p ∈ primeSetCutoff P (T - 1), p < T := fun p hp => by
  have := (mem_primeSetCutoff.mp hp).1.1; omega

theorem primeSetCutoff_prime' (P : Set ℕ) (X : ℕ) : ∀ p ∈ primeSetCutoff P X, p.Prime :=
  fun _ hp => (mem_primeSetCutoff.mp hp).1.2

/-- The Euler density below `T` is the finite-flip density of the flipped primes below `T`. -/
theorem flipDensityBelow_eq (P : Set ℕ) {T : ℕ} (hT : 1 ≤ T) :
    flipDensityBelow (primeSetFlip P) T = finiteFlipHarmonicDensity (primeSetCutoff P (T - 1)) := by
  classical
  unfold flipDensityBelow finiteFlipHarmonicDensity
  rw [← prod_filter_mul_prod_filter_not (Nat.primesBelow T) (· ∈ P)]
  have h1 : ∏ p ∈ (Nat.primesBelow T).filter (· ∉ P),
      (1 - 1 / (p : ℝ)) / (1 - primeSetFlip P p / p) = 1 := by
    refine prod_eq_one fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    rw [primeSetFlip_prime_of_notMem P (Nat.mem_primesBelow.mp hp1).2 hp2]
    have hp0 : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp1).2.two_le
      have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
      linarith
    exact div_self hp0.ne'
  have h2 : (Nat.primesBelow T).filter (· ∈ P) = primeSetCutoff P (T - 1) := by
    ext p
    simp only [mem_filter, Nat.mem_primesBelow, mem_primeSetCutoff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
  rw [h1, mul_one, h2]
  refine prod_congr rfl fun p hp => ?_
  obtain ⟨⟨-, hpp⟩, hpP⟩ := mem_primeSetCutoff.mp hp
  rw [primeSetFlip_prime_of_mem P hpp hpP]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  field_simp
  ring

/-- `v_F = H^{−1/2} (finiteFlip F(n)/√n)`. -/
theorem finiteFlipHorizonVector_eq (F : Finset ℕ) (N : ℕ) :
    finiteFlipHorizonVector F N =
      (1 / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) • gaugeVector N (finiteFlip F) := by
  ext i
  simp only [finiteFlipHorizonVector, gaugeVector, PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul]
  ring

/-- `v_P = H^{−1/2} (ω_P(n)/√n)`. -/
theorem primeSetHorizonVector_eq (P : Set ℕ) (N : ℕ) :
    primeSetHorizonVector P N =
      (1 / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) • gaugeVector N (primeSetFlip P) := by
  ext i
  simp only [primeSetHorizonVector, finiteFlipHorizonVector, gaugeVector, PiLp.smul_apply,
    WithLp.ofLp_toLp, smul_eq_mul]
  rw [← primeSetFlip_eq_finiteFlip_of_le P (mem_Icc.mp i.2).2]
  ring

/-- The Euclidean quadratic form is the atomic Weil form of the extension. -/
theorem atomicWeilForm_horizonExtend_eq_inner {N : ℕ}
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    atomicWeilForm N (horizonExtend u) = ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫ := by
  rw [atomicWeilForm_horizonExtend, EuclideanSpace.inner_eq_star_dotProduct]
  rfl

theorem sum_sq_horizonExtend {N : ℕ} (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ∑ n ∈ Icc 1 N, horizonExtend u n ^ 2 = ‖u‖ ^ 2 := by
  rw [sum_horizonExtend u (fun _ t => t ^ 2), EuclideanSpace.real_norm_sq_eq]

/-- **Defect against energy**: eventually `D_N(w) ≤ 2 Q_N(w) + |w|²`. -/
theorem eventually_poleDefect_le_primeEnergy :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
      poleDefect N (horizonExtend w) ≤ 2 * primeEnergy N w + ‖w‖ ^ 2 := by
  obtain ⟨N₀, hN₀⟩ :=
    RenormalizedArithmeticPotentialTheory.eventually_atomicWeilForm_add_poleDefect_le
      (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨N₀, fun N hN w => ?_⟩
  have h := hN₀ N hN (horizonExtend w)
  rw [atomicWeilForm_horizonExtend_eq_inner, sum_sq_horizonExtend] at h
  unfold primeEnergy
  linarith

/-- The pole vector `b̂ = v_∅`. -/
abbrev poleUnit (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) := finiteFlipHorizonVector ∅ N

theorem finiteFlip_empty (n : ℕ) : finiteFlip ∅ n = 1 := by simp [finiteFlip]

theorem inner_gaugeVector_gaugeVector (N : ℕ) (h g : ℕ → ℝ) :
    ⟪gaugeVector N h, gaugeVector N g⟫ = ∑ n ∈ Icc 1 N, h n * g n / n := by
  rw [inner_gaugeVector_eq]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  simp only [horizonExtend, dif_pos hn, gaugeVector, WithLp.ofLp_toLp]
  rw [mul_div_cancel₀ _ (Real.sqrt_pos.mpr hn0).ne']

/-- `⟨b̂, v_P⟩ = c_N`. -/
theorem inner_poleUnit_primeSetHorizonVector (P : Set ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ⟪poleUnit N, primeSetHorizonVector P N⟫ = harmonicCorrelation (primeSetFlip P) N := by
  have hH := gaugeHarmonicSum_one_pos hN
  rw [poleUnit, finiteFlipHorizonVector_eq, primeSetHorizonVector_eq, real_inner_smul_left,
    real_inner_smul_right, inner_gaugeVector_gaugeVector, harmonicCorrelation]
  have hs := Real.mul_self_sqrt hH.le
  have hs0 := (Real.sqrt_pos.mpr hH).ne'
  have e : ∑ n ∈ Icc 1 N, finiteFlip ∅ n * primeSetFlip P n / n = gaugeHarmonicSum (primeSetFlip P) N := by
    unfold gaugeHarmonicSum
    exact sum_congr rfl fun n _ => by rw [finiteFlip_empty, one_mul]
  rw [e]
  field_simp
  rw [Real.sq_sqrt hH.le]; ring

/-- **The pole is asymptotically the ground**: `Q_N(b̂) ≤ ε` eventually. -/
theorem eventually_primeEnergy_poleUnit_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, primeEnergy N (poleUnit N) ≤ ε := by
  obtain ⟨M₀, hM₀⟩ := RenormalizedArithmeticPotentialTheory.eventually_atomicWeilForm_truncPole_ge hε
  filter_upwards [eventually_ge_atTop (max M₀ 1)] with N hN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have h := hM₀ N ((le_max_left _ _).trans hN)
  have hH := gaugeHarmonicSum_one_pos hN1
  -- `b̂ = H^{−1/2}(1/√n)` and `truncPole N = 1/√n` on `[1, N]`
  have hext : ∀ n ∈ Icc 1 N, horizonExtend (gaugeVector N (finiteFlip ∅)) n = truncPole N n := by
    intro n hn
    simp only [horizonExtend, dif_pos hn, gaugeVector, WithLp.ofLp_toLp, finiteFlip_empty,
      truncPole, if_pos (mem_Icc.mp hn).2, poleVector]
  have hform : ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (gaugeVector N (finiteFlip ∅)),
      gaugeVector N (finiteFlip ∅)⟫ = atomicWeilForm N (truncPole N) := by
    rw [← atomicWeilForm_horizonExtend_eq_inner]; exact atomicWeilForm_congr hext
  have hmass : ∑ n ∈ Icc 1 N, truncPole N n ^ 2 = gaugeHarmonicSum (fun _ => (1 : ℝ)) N := by
    unfold gaugeHarmonicSum
    refine sum_congr rfl fun n hn => ?_
    rw [truncPole, if_pos (mem_Icc.mp hn).2, RenormalizedArithmeticPotentialTheory.poleVector_sq]
  have hnorm : ‖poleUnit N‖ ^ 2 = 1 := finiteFlipHorizonVector_norm_sq ∅ hN1
  rw [hmass] at h
  have hscale : ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (poleUnit N), poleUnit N⟫ =
      atomicWeilForm N (truncPole N) / gaugeHarmonicSum (fun _ => (1 : ℝ)) N := by
    rw [poleUnit, finiteFlipHorizonVector_eq, map_smul, real_inner_smul_left, real_inner_smul_right,
      hform, ← mul_assoc, one_div_mul_one_div, Real.mul_self_sqrt hH.le, one_div_mul_eq_div]
  have hle : Real.log N - γ - ε ≤
      atomicWeilForm N (truncPole N) / gaugeHarmonicSum (fun _ => (1 : ℝ)) N :=
    (le_div_iff₀ hH).mpr h
  unfold primeEnergy
  rw [hnorm, hscale]
  linarith

end Plumbing

section SpectralWeight

open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (ramanujanAdjunctionEnergy_one
  ramanujanAdjunctionEnergy_sub_one_ge)

open private finite_weight_le_primeSet_weight from
  GaloisForLFunctions.ArithmeticCountingPositivity.InfinitePrimeCountsHaveAZeroOrUnitConductorMass

theorem conductorEnergy_gap {m : ℕ} (hm : 2 ≤ m) : 2 * Real.log 2 ≤ ramanujanAdjunctionEnergy m - γ := by
  have h := (ramanujanAdjunctionEnergy_sub_one_ge hm).1
  rwa [ramanujanAdjunctionEnergy_one] at h

/-- The finite-cutoff conductor series is dominated by any bound on the partial sums of `W_P(s)`. -/
theorem finiteFlipSecular_add_le (P : Set ℕ) {s W : ℝ} (hs : 0 < s) (hs2 : s < 2 * Real.log 2)
    (hW : ∀ K, ∑ k ∈ range K, primeSetSpectralWeight P (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s) ≤ W) (Q : ℕ) :
    finiteFlipSecular (primeSetCutoff P Q) s + 1 / s ≤ W := by
  have hsum := summable_finiteFlipSecularTail (primeSetCutoff P Q) (primeSetCutoff_prime' P Q) hs hs2
  have e : finiteFlipSecular (primeSetCutoff P Q) s + 1 / s = ∑' k : ℕ,
      finiteFlipSpectralWeight (primeSetCutoff P Q) (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s) := by
    unfold finiteFlipSecular; ring
  rw [e]
  refine le_of_tendsto' hsum.hasSum.tendsto_sum_nat fun K => (sum_le_sum fun k _ => ?_).trans (hW K)
  have hden : 0 < ramanujanAdjunctionEnergy (k + 2) - γ - s := by
    have := conductorEnergy_gap (m := k + 2) (by omega); linarith
  exact div_le_div_of_nonneg_right (finite_weight_le_primeSet_weight P Q _) hden.le

theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The fibre sums of `ω − μ ω_F` over a `T`-smooth `a`: `ω(a)(S_T(N/a) − μ F_T(N/a))`. -/
theorem fibreSum_twin_sub_finiteFlip (P : Set ℕ) {T N a : ℕ} (hT : 1 ≤ T) (μ : ℝ)
    (ha : a ∈ smoothSet T N) :
    ∑ b ∈ roughInterval T (N / a),
        (primeSetFlip P (a * b) - μ * finiteFlip (primeSetCutoff P (T - 1)) (a * b)) / b =
      primeSetFlip P a * (gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
        μ * roughHarmonic T (N / a)) := by
  obtain ⟨ha1, -, hap⟩ := mem_smoothSet.mp ha
  have hFa : finiteFlip (primeSetCutoff P (T - 1)) a = primeSetFlip P a :=
    (primeSetFlip_eq_finiteFlip_of_smooth P hap).symm
  rw [← sum_roughInterval_eq_gaugeHarmonicSum, RenormalizedArithmeticPotentialTheory.roughHarmonic,
    mul_sub, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun b hb => ?_
  obtain ⟨hb1, -, hbp⟩ := mem_roughInterval.mp hb
  have hbr : ∀ p ∈ b.primeFactors, T ≤ p := fun p hp =>
    hbp p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  rw [(primeSetFlip_isSignGauge P).mul (by omega) (by omega),
    (RenormalizedArithmeticPotentialTheory.finiteFlip_isSignGauge _).mul (by omega) (by omega),
    finiteFlip_eq_one_of_rough (primeSetCutoff_lt P hT) hbr, hFa]
  ring

end SpectralWeight


section MainEstimate

open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (ramanujanAdjunctionEnergy_one)

/-- The real form of the finite-flip term: `|μ y| ≤ c (√W + θ/4) √G`. -/
theorem abs_mul_le_term1 {y μ δ c W θ G : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hW : 0 ≤ W) (hθ : 0 ≤ θ)
    (hμ : μ = c / δ) (hy : y ^ 2 ≤ (δ ^ 2 * W + (δ * θ / 4) ^ 2) * G) :
    |μ * y| ≤ c * (Real.sqrt W + θ / 4) * Real.sqrt G := by
  have h1 : |y| ≤ Real.sqrt ((δ ^ 2 * W + (δ * θ / 4) ^ 2) * G) := Real.abs_le_sqrt hy
  have h2 : Real.sqrt ((δ ^ 2 * W + (δ * θ / 4) ^ 2) * G) ≤ δ * (Real.sqrt W + θ / 4) * Real.sqrt G := by
    rw [Real.sqrt_mul (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    refine (sqrt_add_le_add_sqrt (by positivity) (by positivity)).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le, Real.sqrt_sq (by positivity)]
    ring
  rw [abs_mul, hμ, abs_of_nonneg (div_nonneg hc hδ.le)]
  calc c / δ * |y| ≤ c / δ * (δ * (Real.sqrt W + θ / 4) * Real.sqrt G) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (div_nonneg hc hδ.le)
    _ = c * (Real.sqrt W + θ / 4) * Real.sqrt G := by field_simp

/-- The real form of the fixed-scale term: `|⟨w, P z⟩|/√H ≤ c (θ/4) √G`. -/
theorem abs_div_le_term2 {x a b c G H θ d : ℝ} (hH : 0 < H) (hc : 0 ≤ c) (hd : 0 < d) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hx : |x| ≤ a * b) (ha2 : a ^ 2 ≤ G / d)
    (hb2 : b ^ 2 ≤ (θ / 4) ^ 2 * d * c ^ 2 * H) :
    |1 / Real.sqrt H * x| ≤ c * (θ / 4) * Real.sqrt G := by
  have hsH := Real.sqrt_pos.mpr hH
  have hG : 0 ≤ G := by have := sq_nonneg a; have : 0 ≤ G / d := le_trans (sq_nonneg a) ha2
                        exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hd))
  have hab : (a * b) ^ 2 ≤ ((θ / 4) * c * Real.sqrt H * Real.sqrt G) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hH.le, Real.sq_sqrt hG]
    calc a ^ 2 * b ^ 2 ≤ G / d * ((θ / 4) ^ 2 * d * c ^ 2 * H) :=
          mul_le_mul ha2 hb2 (sq_nonneg _) (by positivity)
      _ = (θ / 4) ^ 2 * c ^ 2 * H * G := by field_simp
  have hab' : a * b ≤ (θ / 4) * c * Real.sqrt H * Real.sqrt G :=
    (pow_le_pow_iff_left₀ (mul_nonneg ha hb) (by positivity) two_ne_zero).mp hab
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hsH)]
  calc 1 / Real.sqrt H * |x| ≤ 1 / Real.sqrt H * ((θ / 4) * c * Real.sqrt H * Real.sqrt G) :=
        mul_le_mul_of_nonneg_left (hx.trans hab') (by positivity)
    _ = c * (θ / 4) * Real.sqrt G := by field_simp

/-- The real form of the rough term: `|X|/√H ≤ c (θ/2) √G`. -/
theorem abs_div_le_term3 {X L H K₁ K₂ LT CD G c c'' θ κ : ℝ} (hL1 : 1 ≤ L) (hHL : L ≤ H)
    (hθ : 0 ≤ θ) (hc'' : 0 ≤ c'') (hCD : 0 ≤ CD)
    (hX : |X| ≤ (K₁ * L ^ (1 / 2 - 2 * κ) * LT + K₂) * Real.sqrt (CD * G))
    (hT : K₁ * LT * Real.sqrt CD ≤ θ / 4 * c'')
    (hK : K₂ * Real.sqrt CD ≤ θ / 4 * c'' * L ^ (1 / 2 - 2 * κ))
    (hc : c'' * L ^ (-(2 * κ)) ≤ c) :
    |1 / Real.sqrt H * X| ≤ c * (θ / 2) * Real.sqrt G := by
  have hL0 : 0 < L := by linarith
  have hsL := Real.sqrt_pos.mpr hL0
  have hsH : Real.sqrt L ≤ Real.sqrt H := Real.sqrt_le_sqrt hHL
  have hsH0 := hsL.trans_le hsH
  have hLa : L ^ (1 / 2 - 2 * κ) = Real.sqrt L * L ^ (-(2 * κ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL0]; ring_nf
  have hLa0 : 0 ≤ L ^ (1 / 2 - 2 * κ) := Real.rpow_nonneg hL0.le _
  have hbound : (K₁ * L ^ (1 / 2 - 2 * κ) * LT + K₂) * Real.sqrt CD ≤
      θ / 2 * c'' * L ^ (1 / 2 - 2 * κ) := by
    have := mul_le_mul_of_nonneg_left hT hLa0
    nlinarith
  have hR0 : 0 ≤ θ / 2 * c'' * L ^ (1 / 2 - 2 * κ) := by positivity
  rw [Real.sqrt_mul hCD] at hX
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hsH0)]
  calc 1 / Real.sqrt H * |X| ≤ 1 / Real.sqrt H *
        ((K₁ * L ^ (1 / 2 - 2 * κ) * LT + K₂) * (Real.sqrt CD * Real.sqrt G)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 1 / Real.sqrt H * ((K₁ * L ^ (1 / 2 - 2 * κ) * LT + K₂) * Real.sqrt CD) * Real.sqrt G := by
        ring
    _ ≤ 1 / Real.sqrt L * (θ / 2 * c'' * L ^ (1 / 2 - 2 * κ)) * Real.sqrt G := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        rcases le_or_gt 0 ((K₁ * L ^ (1 / 2 - 2 * κ) * LT + K₂) * Real.sqrt CD) with h0 | h0
        · exact mul_le_mul (one_div_le_one_div_of_le hsL hsH) hbound h0 (by positivity)
        · have : 1 / Real.sqrt H * ((K₁ * L ^ (1 / 2 - 2 * κ) * LT + K₂) * Real.sqrt CD) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le
          exact this.trans (by positivity)
    _ = θ / 2 * (c'' * L ^ (-(2 * κ))) * Real.sqrt G := by
        rw [hLa]; field_simp
    _ ≤ θ / 2 * c * Real.sqrt G :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity))
          (Real.sqrt_nonneg _)
    _ = c * (θ / 2) * Real.sqrt G := by ring

/-- The three-term decomposition of `⟨w, v⟩` for `v = c ω`, `v_F = c ω_F`, `P ω_F = ω_F`. -/
theorem inner_decomp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w v vF ω ωF : E) (PT : E →L[ℝ] E) (c μ : ℝ) (hv : v = c • ω) (hvF : vF = c • ωF)
    (hPF : PT ωF = ωF) :
    ⟪w, v⟫ = μ * ⟪w, vF⟫ + c * ⟪w, PT (ω - μ • ωF)⟫ + c * ⟪w, ω - PT ω⟫ := by
  rw [hv, hvF, map_sub, map_smul, hPF, real_inner_smul_right, real_inner_smul_right,
    inner_sub_right, inner_sub_right, real_inner_smul_right]
  ring

/-- **The fixed-scale term.** If the fixed-scale defect at horizon `N` is at most `ε₂ δ² H S²`, then
the `T`-smooth projection of `ω⃗ − μ ω⃗_F`, `μ = S/(H δ)`, has `|P_T(·)|² ≤ ε₂ S²/H`. -/
theorem norm_starProjection_twin_sub_sq_le (P : Set ℕ) {T N : ℕ} (hT : 1 ≤ T) {δ ε₂ : ℝ}
    (hδ : 0 < δ) (hH : 0 < gaugeHarmonicSum (fun _ => (1 : ℝ)) N)
    (hdef : ∑ a ∈ smoothSet T N, (δ * gaugeHarmonicSum (fun _ => (1 : ℝ)) N *
        gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
        gaugeHarmonicSum (primeSetFlip P) N * roughHarmonic T (N / a)) ^ 2 /
          (a * roughHarmonic T (N / a)) ≤
      ε₂ * δ ^ 2 * gaugeHarmonicSum (fun _ => (1 : ℝ)) N * gaugeHarmonicSum (primeSetFlip P) N ^ 2) :
    ‖(smoothFibreSpace T N).starProjection (gaugeVector N (fun n => primeSetFlip P n -
        gaugeHarmonicSum (primeSetFlip P) N / (gaugeHarmonicSum (fun _ => (1 : ℝ)) N * δ) *
          finiteFlip (primeSetCutoff P (T - 1)) n))‖ ^ 2 ≤
      ε₂ * gaugeHarmonicSum (primeSetFlip P) N ^ 2 / gaugeHarmonicSum (fun _ => (1 : ℝ)) N := by
  set H := gaugeHarmonicSum (fun _ => (1 : ℝ)) N
  set S := gaugeHarmonicSum (primeSetFlip P) N
  set μ := S / (H * δ)
  have hδH : 0 < δ * H := by positivity
  set M := ∑ a ∈ smoothSet T N, (∑ b ∈ roughInterval T (N / a),
    (primeSetFlip P (a * b) - μ * finiteFlip (primeSetCutoff P (T - 1)) (a * b)) / b) ^ 2 /
      (a * roughHarmonic T (N / a))
  have hR : ∀ a ∈ smoothSet T N, 1 ≤ roughHarmonic T (N / a) := fun a ha => by
    obtain ⟨ha1, haN, -⟩ := mem_smoothSet.mp ha
    exact one_le_roughHarmonic T ((Nat.le_div_iff_mul_le (by omega)).mpr (by omega))
  have e : M = (∑ a ∈ smoothSet T N, (δ * H * gaugeHarmonicSum (roughGauge T (primeSetFlip P))
      (N / a) - S * roughHarmonic T (N / a)) ^ 2 / (a * roughHarmonic T (N / a))) /
        (δ * H) ^ 2 := by
    rw [sum_div]
    refine sum_congr rfl fun a ha => ?_
    rw [fibreSum_twin_sub_finiteFlip P hT μ ha, mul_pow,
      show primeSetFlip P a ^ 2 = 1 by rw [sq]; exact primeSetFlip_mul_self P a, one_mul]
    have hsub : gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
        μ * roughHarmonic T (N / a) = (δ * H * gaugeHarmonicSum (roughGauge T (primeSetFlip P))
          (N / a) - S * roughHarmonic T (N / a)) / (δ * H) := by
      simp only [μ]; field_simp
    rw [hsub, div_pow, div_div, div_div, mul_comm ((δ * H) ^ 2)]
  have hM : M ≤ ε₂ * S ^ 2 / H := by
    rw [e, div_le_iff₀ (by positivity)]
    refine hdef.trans (le_of_eq ?_)
    field_simp
  have hM0 : 0 ≤ M := sum_nonneg fun a ha => by
    have := hR a ha
    have := (mem_smoothSet.mp ha).1
    positivity
  refine (norm_starProjection_sq_le _ hM0 fun v hv => ?_).trans hM
  rw [mul_comm M]
  exact inner_sq_le_of_mem_smoothFibreSpace _ hv

/-- **The pointwise estimate at one horizon.** With the finite flip `F` below `T`, its density `δ`,
the excited-resolvent bound, the fixed-scale defect, the multiscale bound and the energy facts at
horizon `N`, `|⟨w, v_P⟩| ≤ c_N (√W + θ) √(Q_N(w) − s|w|²)` for `w ⊥ e_{i₀}`. -/
theorem abs_inner_primeSetHorizonVector_le (P : Set ℕ) {T N : ℕ} (hT : 1 ≤ T)
    {i₀ : PrimeHorizonIndex N} {s t W θ CD K₁ K₂ LT c'' κ : ℝ} (hst : s < t)
    (hg : IsGroundBelow N t i₀) {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hw : ⟪w, primeEigen N i₀⟫ = 0) (hW0 : 0 ≤ W) (hθ : 0 ≤ θ) (hc'' : 0 ≤ c'') (hCD : 0 ≤ CD)
    (hL1 : 1 ≤ Real.log N)
    (hρ : excitedResolvent N s i₀ (finiteFlipHorizonVector (primeSetCutoff P (T - 1)) N) ≤
      finiteFlipHarmonicDensity (primeSetCutoff P (T - 1)) ^ 2 * W +
        (finiteFlipHarmonicDensity (primeSetCutoff P (T - 1)) * θ / 4) ^ 2)
    (hdef : ∑ a ∈ smoothSet T N, (finiteFlipHarmonicDensity (primeSetCutoff P (T - 1)) *
        gaugeHarmonicSum (fun _ => (1 : ℝ)) N *
        gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
        gaugeHarmonicSum (primeSetFlip P) N * roughHarmonic T (N / a)) ^ 2 /
          (a * roughHarmonic T (N / a)) ≤
      ((θ / 4) ^ 2 * (t - s)) * finiteFlipHarmonicDensity (primeSetCutoff P (T - 1)) ^ 2 *
        gaugeHarmonicSum (fun _ => (1 : ℝ)) N * gaugeHarmonicSum (primeSetFlip P) N ^ 2)
    (hms : |⟪w, gaugeVector N (primeSetFlip P) -
      (smoothFibreSpace T N).starProjection (gaugeVector N (primeSetFlip P))⟫| ≤
        (K₁ * Real.log N ^ (1 / 2 - 2 * κ) * LT + K₂) * Real.sqrt (poleDefect N (horizonExtend w)))
    (hD : poleDefect N (horizonExtend w) ≤ CD * (primeEnergy N w - s * ‖w‖ ^ 2))
    (hcoef : 0 ≤ K₁ * Real.log N ^ (1 / 2 - 2 * κ) * LT + K₂)
    (hTch : K₁ * LT * Real.sqrt CD ≤ θ / 4 * c'')
    (hK₂ : K₂ * Real.sqrt CD ≤ θ / 4 * c'' * Real.log N ^ (1 / 2 - 2 * κ))
    (hcN : c'' * Real.log N ^ (-(2 * κ)) ≤ harmonicCorrelation (primeSetFlip P) N) :
    |⟪w, primeSetHorizonVector P N⟫| ≤ harmonicCorrelation (primeSetFlip P) N *
      (Real.sqrt W + θ) * Real.sqrt (primeEnergy N w - s * ‖w‖ ^ 2) := by
  set F := primeSetCutoff P (T - 1)
  set δ := finiteFlipHarmonicDensity F
  have hδ0 : 0 < δ := finiteFlipHarmonicDensity_pos (primeSetCutoff_prime' P (T - 1))
  have hFT := primeSetCutoff_lt P hT
  set H := gaugeHarmonicSum (fun _ => (1 : ℝ)) N with hHdef
  set S := gaugeHarmonicSum (primeSetFlip P) N with hSdef
  set cN := harmonicCorrelation (primeSetFlip P) N
  have hcNdef : cN = S / H := rfl
  have hHL : Real.log N ≤ H := log_le_harmonic N
  have hH0 : 0 < H := by linarith
  have hcN0 : 0 ≤ cN := le_trans (mul_nonneg hc'' (Real.rpow_nonneg (by linarith) _)) hcN
  have hts : 0 < t - s := by linarith
  set G := primeEnergy N w - s * ‖w‖ ^ 2
  have hcoer := primeEnergy_sub_ge_of_perp (s := s) hg hw
  have hG0 : 0 ≤ G := le_trans (mul_nonneg hts.le (sq_nonneg _)) hcoer
  have hw2 : ‖w‖ ^ 2 ≤ G / (t - s) := by rw [le_div_iff₀ hts]; linarith
  -- the decomposition `ω⃗ = μ ω⃗_F + P_T(ω⃗ − μ ω⃗_F) + (ω⃗ − P_T ω⃗)`
  set ωv := gaugeVector N (primeSetFlip P)
  set ωvF := gaugeVector N (finiteFlip F)
  set PT := (smoothFibreSpace T N).starProjection
  set μ := cN / δ
  have hμ : μ = S / (H * δ) := by simp only [μ, hcNdef]; field_simp
  have hz : gaugeVector N (fun n => primeSetFlip P n - S / (H * δ) * finiteFlip F n) =
      ωv - μ • ωvF := by
    ext i; simp only [ωv, ωvF, gaugeVector, PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_toLp,
      smul_eq_mul, hμ]; ring
  have hinner := inner_decomp w (primeSetHorizonVector P N) (finiteFlipHorizonVector F N) ωv ωvF PT
    (1 / Real.sqrt H) μ (primeSetHorizonVector_eq P N) (finiteFlipHorizonVector_eq F N)
    (Submodule.starProjection_eq_self_iff.mpr (gaugeVector_finiteFlip_mem hFT N))
  -- term 1: the finite flip
  have hT1sq : ⟪w, finiteFlipHorizonVector F N⟫ ^ 2 ≤ (δ ^ 2 * W + (δ * θ / 4) ^ 2) * G :=
    (inner_sq_le_excited hg hst hw _).trans (mul_le_mul_of_nonneg_right hρ hG0)
  have hX1 := abs_mul_le_term1 hδ0 hcN0 hW0 hθ rfl hT1sq
  -- term 2: the fixed-scale defect
  have hPz2 : ‖PT (ωv - μ • ωvF)‖ ^ 2 ≤ (θ / 4) ^ 2 * (t - s) * cN ^ 2 * H := by
    have h := norm_starProjection_twin_sub_sq_le P hT hδ0 hH0 hdef
    rw [← hHdef, ← hSdef, hz] at h
    refine h.trans (le_of_eq ?_)
    rw [hcNdef]; field_simp
  have hX2 := abs_div_le_term2 (x := ⟪w, PT (ωv - μ • ωvF)⟫) hH0 hcN0 hts (norm_nonneg w)
    (norm_nonneg _) hθ (abs_real_inner_le_norm _ _) hw2 hPz2
  -- term 3: the rough fluctuations
  have hX3 : |1 / Real.sqrt H * ⟪w, ωv - PT ωv⟫| ≤ cN * (θ / 2) * Real.sqrt G := by
    exact abs_div_le_term3 hL1 hHL hθ hc'' hCD
      (hms.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hD) hcoef)) hTch hK₂ hcN
  -- combine
  rw [hinner]
  calc _ ≤ |μ * ⟪w, finiteFlipHorizonVector F N⟫| +
        |1 / Real.sqrt H * ⟪w, PT (ωv - μ • ωvF)⟫| + |1 / Real.sqrt H * ⟪w, ωv - PT ωv⟫| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ cN * (Real.sqrt W + θ / 4) * Real.sqrt G + cN * (θ / 4) * Real.sqrt G +
        cN * (θ / 2) * Real.sqrt G := add_le_add (add_le_add hX1 hX2) hX3
    _ = cN * (Real.sqrt W + θ) * Real.sqrt G := by ring

/-- **The spectral weight of a zero-density twin at precision `c_N²`.** Let `P` have relative log
density `κ ∈ (0, 1/4)`, `0 < s < t < 2 log 2`, and let every partial sum of the conductor series
`Σ_{m ≥ 2} w_P(m)/(E_m − γ − s)` be at most `W`. Then for every `ε > 0`, eventually, for every ground
index `i₀` below `γ + t` and every `w ⊥ e_{i₀}`,
`⟨w, v_P⟩² ≤ c_N² (W + ε)(Q_N(w) − s|w|²)`. -/
theorem eventually_inner_sq_le_conductorSeries (P : Set ℕ) {κ C : ℝ} (hκ0 : 0 < κ)
    (hκ : κ < 1 / 4) (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C)
    {s t W : ℝ} (hs : 0 < s) (hst : s < t) (ht2 : t < 2 * Real.log 2)
    (hW : ∀ K, ∑ k ∈ range K, primeSetSpectralWeight P (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s) ≤ W) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i₀ : PrimeHorizonIndex N, IsGroundBelow N t i₀ →
      ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪w, primeEigen N i₀⟫ = 0 →
        ⟪w, primeSetHorizonVector P N⟫ ^ 2 ≤
          harmonicCorrelation (primeSetFlip P) N ^ 2 * (W + ε) * (primeEnergy N w - s * ‖w‖ ^ 2) := by
  have hs2 : s < 2 * Real.log 2 := hst.trans ht2
  have hts : 0 < t - s := by linarith
  have hW0 : 0 ≤ W := by simpa using hW 0
  -- the tolerance `θ` with `(√W + θ)² ≤ W + ε`
  set θ := min 1 (ε / (2 * Real.sqrt W + 1))
  have hθ0 : 0 < θ := lt_min one_pos (by positivity)
  have hθε : θ * (2 * Real.sqrt W + θ) ≤ ε := by
    have h1 : θ ≤ ε / (2 * Real.sqrt W + 1) := min_le_right _ _
    have h2 : θ * (2 * Real.sqrt W + 1) ≤ ε := by rwa [le_div_iff₀ (by positivity)] at h1
    have h3 : θ ≤ 1 := min_le_left _ _
    nlinarith [Real.sqrt_nonneg W]
  have hWθ : (Real.sqrt W + θ) ^ 2 ≤ W + ε := by
    have e : (Real.sqrt W + θ) ^ 2 = W + θ * (2 * Real.sqrt W + θ) := by
      rw [add_sq, Real.sq_sqrt hW0]; ring
    linarith only [e, hθε]
  set CD := 2 + (2 * s + 1) / (t - s)
  have hCD : 0 ≤ CD := by positivity
  obtain ⟨K₁, K₂, hK₁, hK₂, hms⟩ := exists_abs_inner_twin_sub_starProjection_le P hκ0 hκ hP
  obtain ⟨c', hc', N₂, hN₂⟩ :=
    exists_pos_mul_rpow_le_gaugeHarmonicSum_primeSetFlip P (by linarith : κ < 1 / 2) hP
  have hc'' : 0 < c' / 2 := by positivity
  -- choose the scale `T`
  have hTlim : Tendsto (fun T : ℕ => Real.log T ^ (2 * κ - 1 / 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1 / 2 - 2 * κ by linarith)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    refine h.congr fun T => ?_
    simp only [Function.comp_apply]
    congr 1; ring
  have hsmall : 0 < θ / 4 * (c' / 2) / (K₁ * Real.sqrt CD + 1) := by positivity
  obtain ⟨T, hT3, hTsmall⟩ := ((eventually_ge_atTop 3).and
    (hTlim.eventually (ge_mem_nhds hsmall))).exists
  have hLT0 : 0 ≤ Real.log T ^ (2 * κ - 1 / 2) := Real.rpow_nonneg (Real.log_natCast_nonneg T) _
  have hTch : K₁ * Real.log T ^ (2 * κ - 1 / 2) * Real.sqrt CD ≤ θ / 4 * (c' / 2) := by
    rw [le_div_iff₀ (by positivity)] at hTsmall
    have h1 : K₁ * Real.sqrt CD * Real.log T ^ (2 * κ - 1 / 2) ≤
        (K₁ * Real.sqrt CD + 1) * Real.log T ^ (2 * κ - 1 / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hLT0
    nlinarith
  -- the flipped primes below `T`
  set F := primeSetCutoff P (T - 1)
  have hF := primeSetCutoff_prime' P (T - 1)
  set δ := finiteFlipHarmonicDensity F
  have hδeq : flipDensityBelow (primeSetFlip P) T = δ := flipDensityBelow_eq P (by omega)
  have hWF : finiteFlipSecular F s + 1 / s ≤ W := finiteFlipSecular_add_le P hs hs2 hW (T - 1)
  -- eventual facts at the horizon
  have h5 := eventually_excitedResolvent_finiteFlip_le F hF hs hst ht2
    (ε := (δ * θ / 4) ^ 2) (by have := finiteFlipHarmonicDensity_pos hF; positivity)
  obtain ⟨N₃, h3⟩ := eventually_fixedScaleDefect_le P hκ0 (by linarith) hP hT3
    (ε := (θ / 4) ^ 2 * (t - s)) (by positivity)
  obtain ⟨N₄, h4⟩ := eventually_poleDefect_le_primeEnergy
  have hLa : Tendsto (fun N : ℕ => Real.log N ^ (1 / 2 - 2 * κ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hK₂ev := hLa.eventually_ge_atTop (K₂ * Real.sqrt CD / (θ / 4 * (c' / 2)))
  filter_upwards [h5, eventually_ge_atTop (max (max N₃ N₄) (max N₂ T)), hK₂ev]
    with N h5N hN hK₂N i₀ hg w hw
  have hN3 : N₃ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN4 : N₄ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNN₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hTN : T ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hL1 : 1 ≤ Real.log N := one_le_log_of_three_le (hT3.trans hTN)
  -- `c_N ≥ (c'/2)(log N)^{−2κ}`
  have hcN : c' / 2 * Real.log N ^ (-(2 * κ)) ≤ harmonicCorrelation (primeSetFlip P) N := by
    have hH0 : 0 < gaugeHarmonicSum (fun _ => (1 : ℝ)) N := lt_of_lt_of_le (by linarith)
      (log_le_harmonic N)
    have hHu : gaugeHarmonicSum (fun _ => (1 : ℝ)) N ≤ 2 * Real.log N := by
      have := (abs_le.mp (abs_harmonic_sub_log_le N)).2; linarith
    have hLpow : Real.log N ^ (1 - 2 * κ) = Real.log N * Real.log N ^ (-(2 * κ)) := by
      rw [show 1 - 2 * κ = 1 + -(2 * κ) by ring, Real.rpow_add (by linarith), Real.rpow_one]
    have hp0 : 0 ≤ Real.log N ^ (-(2 * κ)) := Real.rpow_nonneg (by linarith) _
    rw [harmonicCorrelation, le_div_iff₀ hH0]
    calc c' / 2 * Real.log N ^ (-(2 * κ)) * gaugeHarmonicSum (fun _ => (1 : ℝ)) N ≤
          c' / 2 * Real.log N ^ (-(2 * κ)) * (2 * Real.log N) :=
          mul_le_mul_of_nonneg_left hHu (by positivity)
      _ = c' * Real.log N ^ (1 - 2 * κ) := by rw [hLpow]; ring
      _ ≤ gaugeHarmonicSum (primeSetFlip P) N := hN₂ N hNN₂
  have hρ : excitedResolvent N s i₀ (finiteFlipHorizonVector F N) ≤ δ ^ 2 * W + (δ * θ / 4) ^ 2 := by
    refine (h5N i₀ hg).trans ?_
    have := mul_le_mul_of_nonneg_left hWF (sq_nonneg δ)
    linarith
  have hdef := h3 N hN3
  rw [hδeq] at hdef
  -- the defect against the energy
  have hD : poleDefect N (horizonExtend w) ≤ CD * (primeEnergy N w - s * ‖w‖ ^ 2) := by
    have h := h4 N hN4 w
    have hcoer := primeEnergy_sub_ge_of_perp (s := s) hg hw
    have hw2 : (2 * s + 1) * ‖w‖ ^ 2 ≤ (2 * s + 1) / (t - s) * (primeEnergy N w - s * ‖w‖ ^ 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hts]; nlinarith
    simp only [CD]
    nlinarith
  have hK₂' : K₂ * Real.sqrt CD ≤ θ / 4 * (c' / 2) * Real.log N ^ (1 / 2 - 2 * κ) := by
    rw [div_le_iff₀ (by positivity)] at hK₂N; linarith
  have hpt := abs_inner_primeSetHorizonVector_le P (show 1 ≤ T by omega) hst hg hw hW0 hθ0.le
    hc''.le hCD hL1 hρ hdef (hms T N hT3 hTN w) hD
    (by have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.log N) (1 / 2 - 2 * κ); positivity)
    hTch hK₂' hcN
  have hG0 : 0 ≤ primeEnergy N w - s * ‖w‖ ^ 2 :=
    le_trans (mul_nonneg hts.le (sq_nonneg _)) (primeEnergy_sub_ge_of_perp (s := s) hg hw)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hpt 2
  rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt hG0] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWθ (sq_nonneg _)) hG0)

end MainEstimate


section Margin

open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (ramanujanAdjunctionEnergy_one)

theorem norm_primeEigen (N : ℕ) (i : PrimeHorizonIndex N) : ‖primeEigen N i‖ = 1 :=
  (fullPrimeMatrix_isHermitian N).eigenvectorBasis.orthonormal.1 i

theorem inner_primeEigen (N : ℕ) (i j : PrimeHorizonIndex N) :
    ⟪primeEigen N j, primeEigen N i⟫ = if j = i then 1 else 0 :=
  orthonormal_iff_ite.mp (fullPrimeMatrix_isHermitian N).eigenvectorBasis.orthonormal j i

/-- **Splitting off the ground**: with `a = ⟨u, e_{i₀}⟩` and `w = u − a e_{i₀}`,
`Q_N(u) − s|u|² = (E_{i₀} − γ − s) a² + (Q_N(w) − s|w|²)`. -/
theorem primeEnergy_sub_split (N : ℕ) (s : ℝ) (i₀ : PrimeHorizonIndex N)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeEnergy N u - s * ‖u‖ ^ 2 =
      (fullPrimeEnergyEigenvalue N i₀ - γ - s) * ⟪u, primeEigen N i₀⟫ ^ 2 +
        (primeEnergy N (u - ⟪u, primeEigen N i₀⟫ • primeEigen N i₀) -
          s * ‖u - ⟪u, primeEigen N i₀⟫ • primeEigen N i₀‖ ^ 2) := by
  rw [primeEnergy_sub_eq_sum, primeEnergy_sub_eq_sum, ← add_sum_erase _ _ (mem_univ i₀),
    ← add_sum_erase _ _ (mem_univ i₀)]
  have hcoord : ∀ i, ⟪u - ⟪u, primeEigen N i₀⟫ • primeEigen N i₀, primeEigen N i⟫ =
      ⟪u, primeEigen N i⟫ - ⟪u, primeEigen N i₀⟫ * (if i₀ = i then 1 else 0) := fun i => by
    rw [inner_sub_left, real_inner_smul_left, inner_primeEigen]
  rw [hcoord i₀, if_pos rfl]
  simp only [mul_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_add, add_right_inj]
  refine sum_congr rfl fun i hi => ?_
  rw [hcoord i, if_neg (Ne.symm (ne_of_mem_erase hi)), mul_zero, sub_zero]

/-- **The ground coordinate of `v`.** If the excited estimate holds off the ground with constant
`c²(W + ε)`, the ground energy is within `ε₀` of `0`, `‖b‖ = 1`, `⟨b, v⟩ = c` and `Q_N(b) ≤ ε₀`, then
`|⟨e_{i₀}, v⟩| ≥ c (1 − √(2ε₀(W + ε)))`. -/
theorem ground_coord_ge {N : ℕ} {i₀ : PrimeHorizonIndex N} {s t W ε ε₀ c : ℝ} (hs0 : 0 ≤ s)
    (hc : 0 ≤ c) (hWε : 0 ≤ W + ε) (hε₀ : 0 ≤ ε₀) {v b : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hlam : |fullPrimeEnergyEigenvalue N i₀ - γ| ≤ ε₀)
    (hmain : ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪w, primeEigen N i₀⟫ = 0 →
      ⟪w, v⟫ ^ 2 ≤ c ^ 2 * (W + ε) * (primeEnergy N w - s * ‖w‖ ^ 2))
    (hb : ‖b‖ = 1) (hbv : ⟪b, v⟫ = c) (hpole : primeEnergy N b ≤ ε₀) :
    c * (1 - Real.sqrt (2 * ε₀ * (W + ε))) ≤ |⟪primeEigen N i₀, v⟫| := by
  set e := primeEigen N i₀
  set α := ⟪b, e⟫
  set w₀ := b - α • e
  have he : ‖e‖ = 1 := norm_primeEigen N i₀
  have hw₀ : ⟪w₀, e⟫ = 0 := by
    simp only [w₀, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]; ring
  have hα1 : |α| ≤ 1 := by
    have := abs_real_inner_le_norm b e; rwa [hb, he, mul_one] at this
  have hα : α ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg α]
  have hsplitb := primeEnergy_sub_split N s i₀ b
  rw [hb, one_pow, mul_one] at hsplitb
  have hl := (abs_le.mp hlam).1
  have h1 : (s - (fullPrimeEnergyEigenvalue N i₀ - γ)) * α ^ 2 ≤ (s + ε₀) * α ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg α)
  have h2 : (s + ε₀) * α ^ 2 ≤ s + ε₀ := mul_le_of_le_one_right (by linarith) hα
  have hGw₀ : primeEnergy N w₀ - s * ‖w₀‖ ^ 2 ≤ 2 * ε₀ := by
    have e1 : primeEnergy N w₀ - s * ‖w₀‖ ^ 2 = primeEnergy N b - s -
        (fullPrimeEnergyEigenvalue N i₀ - γ - s) * α ^ 2 := by
      change _ = primeEnergy N b - s - (fullPrimeEnergyEigenvalue N i₀ - γ - s) * ⟪b, e⟫ ^ 2
      linarith [hsplitb]
    rw [e1]
    linarith only [h1, h2, hpole]
  have hw₀v : |⟪w₀, v⟫| ≤ c * Real.sqrt (2 * ε₀ * (W + ε)) := by
    have h := Real.abs_le_sqrt ((hmain w₀ hw₀).trans
      (mul_le_mul_of_nonneg_left hGw₀ (mul_nonneg (sq_nonneg c) hWε)))
    rwa [show c ^ 2 * (W + ε) * (2 * ε₀) = c ^ 2 * (2 * ε₀ * (W + ε)) by ring,
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc] at h
  have hbsplit : c = α * ⟪e, v⟫ + ⟪w₀, v⟫ := by
    rw [← hbv]; simp only [w₀, inner_sub_left, real_inner_smul_left]; ring
  have hαe : |α * ⟪e, v⟫| ≤ |⟪e, v⟫| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hα1
  have htri := abs_add_le (α * ⟪e, v⟫) ⟪w₀, v⟫
  rw [← hbsplit, abs_of_nonneg hc] at htri
  linarith only [htri, hαe, hw₀v]

/-- The final real inequality: with `G ≥ 0`, `a²(1 − θ')² ≤ (W + ε) G`,
`(s + ε₀)(W + ε) ≤ (1 − θ')²`, `1 − θ' > 0` and `|λ| ≤ ε₀`, `(λ − s) a² + G ≥ 0`. -/
theorem split_nonneg {a G W ε ε₀ s θ' lam : ℝ} (hs : 0 ≤ s) (hε₀ : 0 ≤ ε₀) (hG : 0 ≤ G)
    (hθ : 0 < 1 - θ') (ha : a ^ 2 * (1 - θ') ^ 2 ≤ (W + ε) * G)
    (hcond : (s + ε₀) * (W + ε) ≤ (1 - θ') ^ 2) (hlam : |lam| ≤ ε₀) :
    0 ≤ (lam - s) * a ^ 2 + G := by
  have hθ2 : 0 < (1 - θ') ^ 2 := by positivity
  have h5 : (s + ε₀) * (a ^ 2 * (1 - θ') ^ 2) ≤ (s + ε₀) * ((W + ε) * G) :=
    mul_le_mul_of_nonneg_left ha (by linarith)
  have h6 : (s + ε₀) * ((W + ε) * G) ≤ (1 - θ') ^ 2 * G := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcond hG
  have hsa : (s + ε₀) * a ^ 2 ≤ G := by
    have h7 : ((s + ε₀) * a ^ 2) * (1 - θ') ^ 2 ≤ G * (1 - θ') ^ 2 := by
      calc ((s + ε₀) * a ^ 2) * (1 - θ') ^ 2 = (s + ε₀) * (a ^ 2 * (1 - θ') ^ 2) := by ring
        _ ≤ (1 - θ') ^ 2 * G := h5.trans h6
        _ = G * (1 - θ') ^ 2 := by ring
    exact le_of_mul_le_mul_right h7 hθ2
  have hl := (abs_le.mp hlam).1
  have h8 : -(s + ε₀) * a ^ 2 ≤ (lam - s) * a ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg a)
  linarith only [hsa, h8]

/-- **The maximal margin at one horizon.** Under the hypotheses of `ground_coord_ge` with `c > 0`,
`θ' = √(2ε₀(W + ε)) < 1` and `(s + ε₀)(W + ε) ≤ (1 − θ')²`, `Q_N(u) ≥ s|u|²` for all `u ⊥ v`. -/
theorem le_primeEnergy_of_perp {N : ℕ} {i₀ : PrimeHorizonIndex N} {s t W ε ε₀ c : ℝ}
    (hs0 : 0 ≤ s) (hst : s < t) (hg : IsGroundBelow N t i₀)
    {v b : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hc : 0 < c) (hWε : 0 ≤ W + ε) (hε₀ : 0 ≤ ε₀)
    (hlam : |fullPrimeEnergyEigenvalue N i₀ - γ| ≤ ε₀)
    (hmain : ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪w, primeEigen N i₀⟫ = 0 →
      ⟪w, v⟫ ^ 2 ≤ c ^ 2 * (W + ε) * (primeEnergy N w - s * ‖w‖ ^ 2))
    (hb : ‖b‖ = 1) (hbv : ⟪b, v⟫ = c) (hpole : primeEnergy N b ≤ ε₀)
    (hθ : Real.sqrt (2 * ε₀ * (W + ε)) < 1)
    (hcond : (s + ε₀) * (W + ε) ≤ (1 - Real.sqrt (2 * ε₀ * (W + ε))) ^ 2)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) (hu : ⟪u, v⟫ = 0) :
    s * ‖u‖ ^ 2 ≤ primeEnergy N u := by
  set e := primeEigen N i₀
  set θ' := Real.sqrt (2 * ε₀ * (W + ε))
  have hev := ground_coord_ge (t := t) hs0 hc.le hWε hε₀ hlam hmain hb hbv hpole
  have hθpos : 0 < 1 - θ' := by linarith
  set a := ⟪u, e⟫
  set w := u - a • e
  have he : ‖e‖ = 1 := norm_primeEigen N i₀
  have hw : ⟪w, e⟫ = 0 := by
    simp only [w, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]; ring
  have hsplitu := primeEnergy_sub_split N s i₀ u
  set G := primeEnergy N w - s * ‖w‖ ^ 2
  have hG0 : 0 ≤ G := le_trans (mul_nonneg (by linarith) (sq_nonneg _))
    (primeEnergy_sub_ge_of_perp (s := s) hg hw)
  have huv : a * ⟪e, v⟫ = -⟪w, v⟫ := by
    have : ⟪u, v⟫ = a * ⟪e, v⟫ + ⟪w, v⟫ := by
      simp only [w, inner_sub_left, real_inner_smul_left]; ring
    linarith
  have ha : a ^ 2 * (1 - θ') ^ 2 ≤ (W + ε) * G := by
    have h1 : (c * (1 - θ')) ^ 2 ≤ ⟪e, v⟫ ^ 2 := by
      rw [← sq_abs ⟪e, v⟫]; exact pow_le_pow_left₀ (by positivity) hev 2
    have h2 : a ^ 2 * ⟪e, v⟫ ^ 2 ≤ c ^ 2 * (W + ε) * G := by
      rw [← mul_pow, huv, neg_sq]; exact hmain w hw
    have h4 : c ^ 2 * (a ^ 2 * (1 - θ') ^ 2) ≤ c ^ 2 * ((W + ε) * G) := by
      calc c ^ 2 * (a ^ 2 * (1 - θ') ^ 2) = a ^ 2 * (c * (1 - θ')) ^ 2 := by ring
        _ ≤ a ^ 2 * ⟪e, v⟫ ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
        _ ≤ c ^ 2 * (W + ε) * G := h2
        _ = c ^ 2 * ((W + ε) * G) := by ring
    exact le_of_mul_le_mul_left h4 (by positivity)
  have hfin := split_nonneg hs0 hε₀ hG0 hθpos ha hcond hlam
  linarith only [hsplitu, hfin]

end Margin


end GaloisForLFunctions.RenormalizedIntersectionTheory
