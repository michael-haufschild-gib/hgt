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
    (hG : 0 ≤ G) (hμ : μ = c / δ) (hy : y ^ 2 ≤ (δ ^ 2 * W + (δ * θ / 4) ^ 2) * G) :
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
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hLT : 0 ≤ LT) (hCD : 0 ≤ CD) (hG : 0 ≤ G)
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
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hsH0), Real.sqrt_mul hCD]
  have hc'' : 0 ≤ c'' * L ^ (-(2 * κ)) ∨ c'' * L ^ (-(2 * κ)) < 0 := le_or_gt _ _
  calc 1 / Real.sqrt H * |X| ≤ 1 / Real.sqrt H *
        ((K₁ * L ^ (1 / 2 - 2 * κ) * LT + K₂) * (Real.sqrt CD * Real.sqrt G)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 1 / Real.sqrt H * ((K₁ * L ^ (1 / 2 - 2 * κ) * LT + K₂) * Real.sqrt CD) * Real.sqrt G := by
        ring
    _ ≤ 1 / Real.sqrt H * (θ / 2 * c'' * L ^ (1 / 2 - 2 * κ)) * Real.sqrt G :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (by positivity))
          (Real.sqrt_nonneg _)
    _ ≤ 1 / Real.sqrt L * (θ / 2 * c'' * L ^ (1 / 2 - 2 * κ)) * Real.sqrt G := by
        rcases le_or_gt 0 (θ / 2 * c'' * L ^ (1 / 2 - 2 * κ)) with h0 | h0
        · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ h0) (Real.sqrt_nonneg _)
          exact one_div_le_one_div_of_le hsL hsH
        · have h1 : θ / 2 * c'' * L ^ (1 / 2 - 2 * κ) ≤ 0 := h0.le
          have h2 : 1 / Real.sqrt L * (θ / 2 * c'' * L ^ (1 / 2 - 2 * κ)) ≥
              1 / Real.sqrt H * (θ / 2 * c'' * L ^ (1 / 2 - 2 * κ)) := by
            have := one_div_le_one_div_of_le hsL hsH
            nlinarith [one_div_pos.mpr hsH0]
          exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
    _ = θ / 2 * (c'' * L ^ (-(2 * κ))) * Real.sqrt G := by
        rw [hLa]; field_simp
    _ ≤ θ / 2 * c * Real.sqrt G := by
        rcases le_or_gt 0 θ with hθ | hθ
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity))
            (Real.sqrt_nonneg _)
        · nlinarith [Real.sqrt_nonneg G, hT, mul_nonneg hK₁ hLT, Real.sqrt_nonneg CD]
    _ = c * (θ / 2) * Real.sqrt G := by ring

end MainEstimate


end GaloisForLFunctions.RenormalizedIntersectionTheory
