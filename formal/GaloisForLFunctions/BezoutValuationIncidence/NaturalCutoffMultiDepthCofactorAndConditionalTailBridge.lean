import GaloisForLFunctions.BezoutValuationIncidence.AllDepthHilbertDilationCubeAndHyperCubeGramFactorization
import GaloisForLFunctions.BezoutValuationIncidence.PrimePacketConditionalTailAndCoherentPrefix
import GaloisForLFunctions.RHTower.PMRamanujanCompleteAperture
import GaloisForLFunctions.RHTower.PMRamanujanGrowingCofactorHead
import GaloisForLFunctions.RHTower.PMRamanujanComplementaryCancellation

/-!
# Natural-Cutoff Multi-Depth Cofactor and Conditional-Tail Bridge

This module bridges the all-depth Euler–Dirichlet operator and Gram hypercube factorizations in
`CrossDepthEulerOperatorFactorizationAndPrimePairGramIdentity` and
`AllDepthHilbertDilationCubeAndHyperCubeGramFactorization` with the existing natural-cutoff and
completed-aperture infrastructure in `RHTower`:

1. **Exact Bridge to `RHTower.PMRamanujanCompleteAperture` (§1)**:
   For any finite set of primes `S : Finset ℕ` (`hS : ∀ p ∈ S, p.Prime`), the local Euler cube
   factor `pmEulerCubeFactor ε (∏ p ∈ S, p)` times the base weight `pmRealRamanujanWeight ε 1`
   is identically `RHTower.pmRamanujanApertureScale ε S`
   (`pmEulerCubeFactor_mul_weight_one_eq_apertureScale`), and the divisor-indexed hypercube sum of
   `pmRamanujanPrimitive` over `(∏ p ∈ S, p).divisors` equals
   `(RHTower.pmCompleteRamanujanPrimitive ε S N).re` (`pmCompleteRamanujanPrimitive_re_eq_sum_divisors`),
   directly connecting the all-depth hypercube factorization to the `PMRamanujanCompleteAperture`
   small-damping divergence theorem (`pmCompleteRamanujan_eventually_exceeds_logSquare_budget`)
   that establishes the necessity of the natural denominator order `q ≤ Q`.

2. **Multi-Depth Energy-Centered Prime Cofactor Packet Head Identity (§2)**:
   Extending `RHTower.PMRamanujanGrowingCofactorHead` (`pmRamanujanPrimeCofactorPacket_head`) from
   uncentered primitives to `pmRamanujanEnergyCenteredPrimitive`, we prove that for any prime `p`
   and any cofactor `2 ≤ r < p`, `vonMangoldt (p * r) = 0`. Consequently,
   across the entire multi-depth cofactor packet `1 ≤ r ≤ R` (`1 ≤ R < p`), the von Mangoldt
   centering sum collapses to the single depth-1 term `r = 1`
   (`pmRamanujanEnergyCenteredPrimeCofactorPacket_eq_re_add_log`):
   $$\sum_{r=1}^R Y_\varepsilon(pr)\,F_{pr}^{\mathrm{ec}}(N)
     = \operatorname{Re}\bigl(\operatorname{pmRamanujanPrimeCofactorPacket}(\varepsilon, p, R, N)\bigr)
       + Y_\varepsilon(p)\,\log p,$$
   and before the first prime multiple (`N < p`), the multi-depth energy-centered cofactor packet
   collapses to the depth-1 energy-centered term plus the scaled lower-cutoff cumulative prefix
   (`pmRamanujanEnergyCenteredPrimeCofactorPacket_head`):
   $$\sum_{r=1}^R Y_\varepsilon(pr)\,F_{pr}^{\mathrm{ec}}(N)
     = Y_\varepsilon(p)\,F_p^{\mathrm{ec}}(N)
       + \frac{\operatorname{Re}\bigl(\operatorname{pmPowerDampedRamanujanCumulativePrefix}(\varepsilon, R - 1, N)\bigr)}{p^{1+\varepsilon} - 1}.$$

3. **All-Depth Natural-Cutoff Conditional-Tail Decomposition of `pmPowerDampedRamanujanEnergyVariance` (§3)**:
   Lifting the pronic conditional-tail decomposition of `PrimePacketConditionalTailAndCoherentPrefix`
   from depth-1 prime packets to the full all-depth natural-cutoff energy-centered cumulative prefix
   `naturalCutoffEnergyCenteredPrefix ε Q N = (pmPowerDampedRamanujanCumulativePrefix ε Q N).re - pmPowerDampedRamanujanEnergyMean ε Q`,
   we prove for every horizon `H : ℕ`:
   - The exact orthogonal decomposition (`pmPowerDampedRamanujanEnergyVariance_eq_head_add_tail`):
     $$\operatorname{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q)
       = \operatorname{naturalCutoffHeadEnergy}(\varepsilon, Q, H)
         + (H + 1)\,\bigl(\operatorname{naturalCutoffHeadMean}(\varepsilon, Q, H)\bigr)^2
         + \operatorname{naturalCutoffTailVariance}(\varepsilon, Q, H).$$
   - Explicit uncentered-prefix expansion of `naturalCutoffTailResidual`
     (`naturalCutoffTailResidual_eq_uncentered`).
   - Quantitative reduction of `naturalCutoffHeadEnergy ε Q H` to the uncentered prefix energy
     `pmPowerDampedRamanujanPrefixEnergy ε Q H` and `(pmPowerDampedRamanujanEnergyMean ε Q) ^ 2`
     (`naturalCutoffHeadEnergy_le_prefixEnergy_add_mean_sq`).
-/

open Complex MeasureTheory Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

/-! ## §1. Exact Bridge to `RHTower.PMRamanujanCompleteAperture` -/

/-- At `q = 1`, `pmRealRamanujanWeight ε 1` equals `(pmPowerDampedDivisorDensity ε).re`. -/
theorem pmRealRamanujanWeight_one {ε : ℝ} (hε : 0 < ε) :
    pmRealRamanujanWeight ε 1 = (pmPowerDampedDivisorDensity ε).re := by
  unfold pmRealRamanujanWeight
  rw [pmPowerDampedRamanujanWeight_one hε]

/-- At a prime `p`, `pmRealRamanujanWeight ε p` equals
`-(pmPowerDampedDivisorDensity ε).re / ((p : ℝ) ^ (1 + ε) - 1)`. -/
theorem pmRealRamanujanWeight_prime {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    pmRealRamanujanWeight ε p =
      -(pmPowerDampedDivisorDensity ε).re / ((p : ℝ) ^ (1 + ε) - 1) := by
  have hp1 : ¬ p ∣ 1 := hp.not_dvd_one
  have h := pmRealRamanujanWeight_prime_mul hε hp hp1
  simpa only [mul_one, pmRealRamanujanWeight_one hε] using h

/-- For any prime `p` and `ε > 0`, the local factor `1 + 1 / (p^{1+ε} - 1)` in
`RHTower.pmRamanujanApertureScale` equals `p^{1+ε} / (p^{1+ε} - 1)` in `pmEulerCubeFactor`. -/
theorem one_add_one_div_prime_rpow_sub_one {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    1 + 1 / ((p : ℝ) ^ (1 + ε) - 1) =
      (p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) := by
  have hb : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 :=
    ne_of_gt (zero_lt_one.trans (pmPowerDampedRamanujan_prime_denominator_one_lt hε hp))
  field_simp
  ring

/-- **Exact Scale Bridge to `RHTower.pmRamanujanApertureScale`**:
For any `ε > 0` and any finite set of primes `S : Finset ℕ` (`hS : ∀ p ∈ S, p.Prime`), the product
of `pmEulerCubeFactor ε (∏ p ∈ S, p)` and `pmRealRamanujanWeight ε 1` equals
`RHTower.pmRamanujanApertureScale ε S`. -/
theorem pmEulerCubeFactor_mul_weight_one_eq_apertureScale {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    pmEulerCubeFactor ε (∏ p ∈ S, p) * pmRealRamanujanWeight ε 1 =
      pmRamanujanApertureScale ε S := by
  rw [pmEulerCubeFactor, Nat.primeFactors_prod hS, pmRealRamanujanWeight_one hε,
    pmRamanujanApertureScale, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  exact (one_add_one_div_prime_rpow_sub_one hε (hS p hp)).symm

/-- Bijection between `S.powerset` and `(∏ p ∈ S, p).divisors` for a finite set of primes `S`. -/
theorem sum_divisors_prod_primes_eq_powerset {α : Type*} [AddCommMonoid α]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (f : ℕ → α) :
    (∑ m ∈ (∏ p ∈ S, p).divisors, f m) =
      ∑ T ∈ S.powerset, f (∏ p ∈ T, p) := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => simp
  | @insert p S hpS ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hp_ndvd : ¬ p ∣ ∏ q ∈ S, q := by
      intro hd
      have hmem : p ∈ (∏ q ∈ S, q).primeFactors := Nat.mem_primeFactors.mpr
        ⟨hp, hd, (Finset.prod_pos (fun q hq => (hS' q hq).pos)).ne'⟩
      rw [Nat.primeFactors_prod hS'] at hmem
      exact hpS hmem
    rw [Finset.prod_insert hpS, (hp.coprime_iff_not_dvd.mpr hp_ndvd).divisors_mul]
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
    trans ∑ x ∈ p.divisors ×ˢ (∏ q ∈ S, q).divisors, f (x.1 * x.2)
    · exact Finset.sum_attach (p.divisors ×ˢ (∏ q ∈ S, q).divisors) (fun x : ℕ × ℕ => f (x.1 * x.2))
    rw [Finset.sum_product, hp.divisors, Finset.sum_pair hp.ne_one.symm]
    simp only [one_mul, ih hS' f, ih hS' (fun x => f (p * x)), Finset.sum_powerset_insert hpS]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun T hT => ?_)
    have hpT : p ∉ T := fun ht => hpS (Finset.mem_powerset.mp hT ht)
    rw [Finset.prod_insert hpT]

/-- **Exact Bridge Between Divisor-Cube Sums and `RHTower.pmCompleteRamanujanPrimitive`**:
For any `ε > 0` and any finite set of primes `S : Finset ℕ` (`hS : ∀ p ∈ S, p.Prime`), the real
part of `RHTower.pmCompleteRamanujanPrimitive ε S N` equals the divisor-cube sum
`∑ m ∈ (∏ p ∈ S, p).divisors, pmRealRamanujanWeight ε m * (pmRamanujanPrimitive m N).re`. -/
theorem pmCompleteRamanujanPrimitive_re_eq_sum_divisors {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    (pmCompleteRamanujanPrimitive ε S N).re =
      ∑ m ∈ (∏ p ∈ S, p).divisors,
        pmRealRamanujanWeight ε m * (pmRamanujanPrimitive m N).re := by
  rw [pmCompleteRamanujanPrimitive, sum_divisors_prod_primes_eq_powerset S hS, Complex.re_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [pmPowerDampedRamanujanWeight_eq_ofReal_pmRealRamanujanWeight hε (∏ p ∈ T, p)]
  simp [Complex.mul_re]

/-! ## §2. Multi-Depth Energy-Centered Prime Cofactor Packet Head Identity -/

/-- For any prime `p` and any cofactor `2 ≤ r < p`, `vonMangoldt (p * r) = 0`. -/
theorem vonMangoldt_prime_mul_of_two_le_of_lt {p r : ℕ} (hp : p.Prime)
    (hr2 : 2 ≤ r) (hrp : r < p) :
    vonMangoldt (p * r) = 0 := by
  have hpr : ¬ p ∣ r := Nat.not_dvd_of_pos_of_lt (by omega) hrp
  exact vonMangoldt_mul_eq_zero_of_coprime (hp.coprime_iff_not_dvd.mpr hpr) hp.one_lt
    (by omega : 1 < r)

/-- Across all cofactors `1 ≤ r ≤ R` with `1 ≤ R < p`, the weighted von Mangoldt sum
`∑ r ∈ Icc 1 R, f r * vonMangoldt (p * r)` collapses to the single depth-1 term `f 1 * Real.log p`. -/
theorem sum_Icc_vonMangoldt_prime_mul_eq_log {p R : ℕ} (hp : p.Prime)
    (hR : 1 ≤ R) (hRp : R < p) (f : ℕ → ℝ) :
    (∑ r ∈ Icc 1 R, f r * vonMangoldt (p * r)) = f 1 * Real.log p := by
  have h1 : (1 : ℕ) ∈ Icc 1 R := mem_Icc.mpr ⟨le_rfl, hR⟩
  rw [← Finset.add_sum_erase _ _ h1]
  have hrest : ∑ r ∈ (Icc 1 R).erase 1, f r * vonMangoldt (p * r) = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    have hr_ne : r ≠ 1 := (mem_erase.mp hr).1
    have hr_mem : r ∈ Icc 1 R := (mem_erase.mp hr).2
    have hr2 : 2 ≤ r := by have := (mem_Icc.mp hr_mem).1; omega
    have hrp : r < p := (mem_Icc.mp hr_mem).2.trans_lt hRp
    rw [vonMangoldt_prime_mul_of_two_le_of_lt hp hr2 hrp, mul_zero]
  rw [hrest, add_zero, mul_one, vonMangoldt_apply_prime hp]

/-- **Energy-Centered Prime Cofactor Packet**:
All actual cofactors `1 ≤ r ≤ R` of a prime `p`, evaluated on the energy-centered primitive
`pmRamanujanEnergyCenteredPrimitive (p * r) N = (pmRamanujanPrimitive (p * r) N).re + vonMangoldt (p * r)`. -/
def pmRamanujanEnergyCenteredPrimeCofactorPacket (ε : ℝ) (p R N : ℕ) : ℝ :=
  ∑ r ∈ Icc 1 R,
    pmRealRamanujanWeight ε (p * r) * pmRamanujanEnergyCenteredPrimitive (p * r) N

/-- **Collapse of Von Mangoldt Centering Across Multi-Depth Cofactor Packets**:
For any `ε > 0`, prime `p`, and `1 ≤ R < p`, the energy-centered prime cofactor packet differs from
the real part of `RHTower.pmRamanujanPrimeCofactorPacket ε p R N` solely by the single depth-1
prime log shift `pmRealRamanujanWeight ε p * Real.log p`. -/
theorem pmRamanujanEnergyCenteredPrimeCofactorPacket_eq_re_add_log {ε : ℝ} (hε : 0 < ε)
    {p R : ℕ} (hp : p.Prime) (hR : 1 ≤ R) (hRp : R < p) (N : ℕ) :
    pmRamanujanEnergyCenteredPrimeCofactorPacket ε p R N =
      (pmRamanujanPrimeCofactorPacket ε p R N).re +
        pmRealRamanujanWeight ε p * Real.log p := by
  rw [pmRamanujanEnergyCenteredPrimeCofactorPacket, pmRamanujanPrimeCofactorPacket, Complex.re_sum]
  have hsplit :
      (∑ r ∈ Icc 1 R,
        pmRealRamanujanWeight ε (p * r) * pmRamanujanEnergyCenteredPrimitive (p * r) N) =
      (∑ r ∈ Icc 1 R,
        pmRealRamanujanWeight ε (p * r) * (pmRamanujanPrimitive (p * r) N).re) +
      (∑ r ∈ Icc 1 R,
        pmRealRamanujanWeight ε (p * r) * vonMangoldt (p * r)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold pmRamanujanEnergyCenteredPrimitive
    ring
  rw [hsplit, sum_Icc_vonMangoldt_prime_mul_eq_log hp hR hRp (fun r => pmRealRamanujanWeight ε (p * r)),
    mul_one]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pmPowerDampedRamanujanWeight_eq_ofReal_pmRealRamanujanWeight hε (p * r)]
  simp [Complex.mul_re]

/-- **Multi-Depth Energy-Centered Prime Cofactor Head Formula Before the First Prime Multiple**:
For `ε > 0`, prime `p`, `1 ≤ R < p`, and `N < p`, summing `Y_ε(pr) F_{pr}^{ec}(N)` across all
cofactors `1 ≤ r ≤ R` (spanning all multiplicative depths of `r ≤ R`) collapses to the depth-1
energy-centered term `pmRealRamanujanWeight ε p * pmRamanujanEnergyCenteredPrimitive p N` plus the
scaled lower-cutoff cumulative prefix
`(pmPowerDampedRamanujanCumulativePrefix ε (R - 1) N).re / ((p : ℝ) ^ (1 + ε) - 1)`. -/
theorem pmRamanujanEnergyCenteredPrimeCofactorPacket_head {ε : ℝ} (hε : 0 < ε)
    {p R N : ℕ} (hp : p.Prime) (hR : 1 ≤ R) (hRp : R < p) (hNp : N < p) :
    pmRamanujanEnergyCenteredPrimeCofactorPacket ε p R N =
      pmRealRamanujanWeight ε p * pmRamanujanEnergyCenteredPrimitive p N +
        (pmPowerDampedRamanujanCumulativePrefix ε (R - 1) N).re /
          ((p : ℝ) ^ (1 + ε) - 1) := by
  rw [pmRamanujanEnergyCenteredPrimeCofactorPacket_eq_re_add_log hε hp hR hRp N,
    pmRamanujanPrimeCofactorPacket_head hε hp hR hRp hNp, Complex.div_ofReal_re]
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    mul_zero, sub_zero]
  rw [pmRamanujanEnergyCenteredPrimitive, pmRamanujanPrimitive_prime hp,
    Nat.mod_eq_of_lt hNp, vonMangoldt_apply_prime hp, pmRealRamanujanWeight_prime hε hp]
  simp only [Complex.neg_re, Complex.natCast_re]
  ring

/-- Explicit linear-plus-log head formula for `pmRamanujanEnergyCenteredPrimeCofactorPacket`
before the first prime multiple (`N < p`). -/
theorem pmRamanujanEnergyCenteredPrimeCofactorPacket_head_explicit {ε : ℝ} (hε : 0 < ε)
    {p R N : ℕ} (hp : p.Prime) (hR : 1 ≤ R) (hRp : R < p) (hNp : N < p) :
    pmRamanujanEnergyCenteredPrimeCofactorPacket ε p R N =
      (-(pmPowerDampedDivisorDensity ε).re * Real.log p +
        (pmPowerDampedDivisorDensity ε).re * (N : ℝ) +
        (pmPowerDampedRamanujanCumulativePrefix ε (R - 1) N).re) /
          ((p : ℝ) ^ (1 + ε) - 1) := by
  rw [pmRamanujanEnergyCenteredPrimeCofactorPacket_head hε hp hR hRp hNp,
    pmRamanujanEnergyCenteredPrimitive, pmRamanujanPrimitive_prime hp,
    Nat.mod_eq_of_lt hNp, vonMangoldt_apply_prime hp, pmRealRamanujanWeight_prime hε hp]
  simp only [Complex.neg_re, Complex.natCast_re]
  ring

/-! ## §3. All-Depth Natural-Cutoff Conditional-Tail Decomposition of `pmPowerDampedRamanujanEnergyVariance` -/

/-- The all-depth natural-cutoff energy-centered cumulative prefix at cutoff `Q` and observation `N`:
`S_{ε, Q}^{ec}(N) = (pmPowerDampedRamanujanCumulativePrefix ε Q N).re - pmPowerDampedRamanujanEnergyMean ε Q`. -/
def naturalCutoffEnergyCenteredPrefix (ε : ℝ) (Q N : ℕ) : ℝ :=
  (pmPowerDampedRamanujanCumulativePrefix ε Q N).re -
    pmPowerDampedRamanujanEnergyMean ε Q

/-- Finite-prefix pronic mean of `naturalCutoffEnergyCenteredPrefix ε Q` up to horizon `H`. -/
def naturalCutoffHeadMean (ε : ℝ) (Q H : ℕ) : ℝ :=
  ∑ n ∈ range (H + 1),
    naturalCutoffEnergyCenteredPrefix ε Q n / ((n : ℝ) * ((n : ℝ) + 1))

/-- Finite-prefix pronic energy of `naturalCutoffEnergyCenteredPrefix ε Q` up to horizon `H`. -/
def naturalCutoffHeadEnergy (ε : ℝ) (Q H : ℕ) : ℝ :=
  ∑ n ∈ range (H + 1),
    (naturalCutoffEnergyCenteredPrefix ε Q n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- Conditional-mean-centered tail residual of `naturalCutoffEnergyCenteredPrefix ε Q` beyond
horizon `H`, indexed by `n : ℕ` corresponding to observation index `H + 1 + n`. -/
def naturalCutoffTailResidual (ε : ℝ) (Q H n : ℕ) : ℝ :=
  naturalCutoffEnergyCenteredPrefix ε Q (H + 1 + n) +
    ((H : ℝ) + 1) * naturalCutoffHeadMean ε Q H

/-- Conditional-mean-centered pronic tail variance of `naturalCutoffEnergyCenteredPrefix ε Q`
beyond horizon `H`. -/
def naturalCutoffTailVariance (ε : ℝ) (Q H : ℕ) : ℝ :=
  ∑' n : ℕ,
    (naturalCutoffTailResidual ε Q H n) ^ 2 /
      (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))

/-- `naturalCutoffEnergyCenteredPrefix ε Q N` has zero pronic mean over `N : ℕ`. -/
theorem hasSum_naturalCutoffEnergyCenteredPrefix {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    HasSum (fun N : ℕ =>
      naturalCutoffEnergyCenteredPrefix ε Q N / ((N : ℝ) * ((N : ℝ) + 1))) 0 := by
  have h := (hasSum_pmPowerDampedRamanujanCumulativeMean hε Q).sub
    (hasSum_pm_reciprocal_weight.mul_left (pmPowerDampedRamanujanEnergyMean ε Q))
  simp only [mul_one, sub_self] at h
  refine h.congr_fun fun N => ?_
  unfold naturalCutoffEnergyCenteredPrefix
  ring

/-- The pronic tail sum of `naturalCutoffEnergyCenteredPrefix ε Q` from `H + 1` to `∞` equals
`-naturalCutoffHeadMean ε Q H`. -/
theorem hasSum_naturalCutoffEnergyCenteredPrefix_tail {ε : ℝ} (hε : 0 < ε) (Q H : ℕ) :
    HasSum (fun n : ℕ =>
      naturalCutoffEnergyCenteredPrefix ε Q (H + 1 + n) /
        (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1)))
      (-naturalCutoffHeadMean ε Q H) := by
  have hs := hasSum_naturalCutoffEnergyCenteredPrefix hε Q
  have ht := hs.summable.comp_injective
    (fun i j h => Nat.add_left_cancel h : Function.Injective (fun n : ℕ => H + 1 + n))
  have he := hs.summable.sum_add_tsum_nat_add (H + 1)
  rw [hs.tsum_eq] at he
  have he' : naturalCutoffHeadMean ε Q H +
      (∑' n : ℕ, naturalCutoffEnergyCenteredPrefix ε Q (H + 1 + n) /
        (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) = 0 := by
    simpa only [naturalCutoffHeadMean, Nat.add_comm, Nat.cast_add, Nat.cast_one, add_comm] using he
  have ht' : Summable (fun n : ℕ => naturalCutoffEnergyCenteredPrefix ε Q (H + 1 + n) /
      (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using ht
  convert ht'.hasSum using 1
  linarith

/-- The pronic tail sum of `(naturalCutoffEnergyCenteredPrefix ε Q (H + 1 + n)) ^ 2` equals
`pmPowerDampedRamanujanEnergyVariance ε Q - naturalCutoffHeadEnergy ε Q H`. -/
theorem hasSum_naturalCutoffEnergyVariance_tail {ε : ℝ} (hε : 0 < ε) (Q H : ℕ) :
    HasSum (fun n : ℕ =>
      (naturalCutoffEnergyCenteredPrefix ε Q (H + 1 + n)) ^ 2 /
        (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1)))
      (pmPowerDampedRamanujanEnergyVariance ε Q - naturalCutoffHeadEnergy ε Q H) := by
  have hs : HasSum (fun N : ℕ =>
      (naturalCutoffEnergyCenteredPrefix ε Q N) ^ 2 / ((N : ℝ) * ((N : ℝ) + 1)))
      (pmPowerDampedRamanujanEnergyVariance ε Q) := by
    have h0 := hasSum_pmPowerDampedRamanujanEnergyVariance hε Q
    rw [← h0.tsum_eq] at h0
    exact h0
  have ht := hs.summable.comp_injective
    (fun i j h => Nat.add_left_cancel h : Function.Injective (fun n : ℕ => H + 1 + n))
  have he := hs.summable.sum_add_tsum_nat_add (H + 1)
  rw [hs.tsum_eq] at he
  have he' : naturalCutoffHeadEnergy ε Q H +
      (∑' n : ℕ, (naturalCutoffEnergyCenteredPrefix ε Q (H + 1 + n)) ^ 2 /
        (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) =
      pmPowerDampedRamanujanEnergyVariance ε Q := by
    simpa only [naturalCutoffHeadEnergy, Nat.add_comm, Nat.cast_add, Nat.cast_one, add_comm] using he
  have ht' : Summable (fun n : ℕ => (naturalCutoffEnergyCenteredPrefix ε Q (H + 1 + n)) ^ 2 /
      (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using ht
  convert ht'.hasSum using 1
  linarith

/-- The conditional-mean-centered tail residual `naturalCutoffTailResidual ε Q H` has zero pronic
mean for every cutoff `Q` and horizon `H`. -/
theorem hasSum_naturalCutoffTailResidual {ε : ℝ} (hε : 0 < ε) (Q H : ℕ) :
    HasSum (fun n : ℕ =>
      naturalCutoffTailResidual ε Q H n /
        (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) 0 := by
  have hs := (hasSum_naturalCutoffEnergyCenteredPrefix_tail hε Q H).add
    ((GaloisForLFunctions.hasSum_one_div_shift_mul_succ (by positivity : (0 : ℝ) < (H : ℝ) + 1)).mul_left
      (((H : ℝ) + 1) * naturalCutoffHeadMean ε Q H))
  have hH : (H : ℝ) + 1 ≠ 0 := by positivity
  have he : -naturalCutoffHeadMean ε Q H +
      (((H : ℝ) + 1) * naturalCutoffHeadMean ε Q H) * (1 / ((H : ℝ) + 1)) = 0 := by
    field_simp
    ring
  rw [he] at hs
  exact hs.congr_fun fun n => by unfold naturalCutoffTailResidual; ring

/-- `HasSum` evaluation of `naturalCutoffTailVariance ε Q H`. -/
theorem hasSum_naturalCutoffTailVariance {ε : ℝ} (hε : 0 < ε) (Q H : ℕ) :
    HasSum (fun n : ℕ =>
      (naturalCutoffTailResidual ε Q H n) ^ 2 /
        (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1)))
      (pmPowerDampedRamanujanEnergyVariance ε Q - naturalCutoffHeadEnergy ε Q H -
        ((H : ℝ) + 1) * (naturalCutoffHeadMean ε Q H) ^ 2) := by
  have hmass := GaloisForLFunctions.hasSum_one_div_shift_mul_succ
    (by positivity : (0 : ℝ) < (H : ℝ) + 1)
  have hs := ((hasSum_naturalCutoffEnergyVariance_tail hε Q H).add
    ((hasSum_naturalCutoffEnergyCenteredPrefix_tail hε Q H).mul_left
      (2 * (((H : ℝ) + 1) * naturalCutoffHeadMean ε Q H)))).add
    (hmass.mul_left ((((H : ℝ) + 1) * naturalCutoffHeadMean ε Q H) ^ 2))
  have hH : (H : ℝ) + 1 ≠ 0 := by positivity
  have he : pmPowerDampedRamanujanEnergyVariance ε Q - naturalCutoffHeadEnergy ε Q H +
      (2 * (((H : ℝ) + 1) * naturalCutoffHeadMean ε Q H)) * (-naturalCutoffHeadMean ε Q H) +
      (((H : ℝ) + 1) * naturalCutoffHeadMean ε Q H) ^ 2 * (1 / ((H : ℝ) + 1)) =
      pmPowerDampedRamanujanEnergyVariance ε Q - naturalCutoffHeadEnergy ε Q H -
        ((H : ℝ) + 1) * (naturalCutoffHeadMean ε Q H) ^ 2 := by
    field_simp
    ring
  rw [he] at hs
  exact hs.congr_fun fun n => by unfold naturalCutoffTailResidual; ring

/-- **All-Depth Natural-Cutoff Conditional-Tail Orthogonal Decomposition of `pmPowerDampedRamanujanEnergyVariance`**:
For every `ε > 0`, every natural denominator cutoff `Q`, and every splitting horizon `H : ℕ`,
`pmPowerDampedRamanujanEnergyVariance ε Q` decomposes orthogonally into:
1. the finite prefix energy `naturalCutoffHeadEnergy ε Q H`,
2. the forced conditional tail-mean energy `((H : ℝ) + 1) * (naturalCutoffHeadMean ε Q H) ^ 2`, and
3. the conditional-mean-centered tail variance `naturalCutoffTailVariance ε Q H`. -/
theorem pmPowerDampedRamanujanEnergyVariance_eq_head_add_tail {ε : ℝ} (hε : 0 < ε) (Q H : ℕ) :
    pmPowerDampedRamanujanEnergyVariance ε Q =
      naturalCutoffHeadEnergy ε Q H +
        ((H : ℝ) + 1) * (naturalCutoffHeadMean ε Q H) ^ 2 +
        naturalCutoffTailVariance ε Q H := by
  have h := (hasSum_naturalCutoffTailVariance hε Q H).tsum_eq
  change naturalCutoffTailVariance ε Q H = _ at h
  linarith

/-- Nonnegativity of the centered tail variance `naturalCutoffTailVariance ε Q H`. -/
theorem naturalCutoffTailVariance_nonneg (ε : ℝ) (Q H : ℕ) :
    0 ≤ naturalCutoffTailVariance ε Q H :=
  tsum_nonneg fun _ => div_nonneg (sq_nonneg _) (by positivity)

/-- Telescoping partial sum of the pronic weight `∑ n ∈ range (H + 1), 1 / (n * (n + 1))`. -/
theorem sum_range_pronic_inv (H : ℕ) :
    (∑ n ∈ range (H + 1), 1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      (H : ℝ) / ((H : ℝ) + 1) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (H : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (H : ℝ) + 1 + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **Explicit Uncentered-Prefix Formula for `naturalCutoffTailResidual`**:
Combining the `-pmPowerDampedRamanujanEnergyMean ε Q` shift at `H + 1 + n` with the finite-prefix
pronic weight sum `(H + 1) * ∑_{m=0}^H 1/(m(m+1)) = H` yields the exact identity in terms of the
uncentered prefix `(pmPowerDampedRamanujanCumulativePrefix ε Q ·).re` and `-(H + 1) E_{ε, Q}`. -/
theorem naturalCutoffTailResidual_eq_uncentered (ε : ℝ) (Q H n : ℕ) :
    naturalCutoffTailResidual ε Q H n =
      (pmPowerDampedRamanujanCumulativePrefix ε Q (H + 1 + n)).re +
        ((H : ℝ) + 1) *
          (∑ m ∈ range (H + 1),
            (pmPowerDampedRamanujanCumulativePrefix ε Q m).re / ((m : ℝ) * ((m : ℝ) + 1))) -
        ((H : ℝ) + 1) * pmPowerDampedRamanujanEnergyMean ε Q := by
  unfold naturalCutoffTailResidual naturalCutoffHeadMean naturalCutoffEnergyCenteredPrefix
  have hsplit :
      (∑ m ∈ range (H + 1),
        ((pmPowerDampedRamanujanCumulativePrefix ε Q m).re - pmPowerDampedRamanujanEnergyMean ε Q) /
          ((m : ℝ) * ((m : ℝ) + 1))) =
      (∑ m ∈ range (H + 1),
        (pmPowerDampedRamanujanCumulativePrefix ε Q m).re / ((m : ℝ) * ((m : ℝ) + 1))) -
      pmPowerDampedRamanujanEnergyMean ε Q *
        (∑ m ∈ range (H + 1), 1 / ((m : ℝ) * ((m : ℝ) + 1))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [hsplit, sum_range_pronic_inv H]
  have hH : (H : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **Quantitative Bound on `naturalCutoffHeadEnergy` via `pmPowerDampedRamanujanPrefixEnergy`**:
For any `ε > 0` and any `Q, H : ℕ`, the energy-centered finite prefix energy up to `H` is bounded
by twice the uncentered prefix energy `pmPowerDampedRamanujanPrefixEnergy ε Q H` plus twice the
squared von Mangoldt mean `(pmPowerDampedRamanujanEnergyMean ε Q) ^ 2`. -/
theorem naturalCutoffHeadEnergy_le_prefixEnergy_add_mean_sq {ε : ℝ} (hε : 0 < ε) (Q H : ℕ) :
    naturalCutoffHeadEnergy ε Q H ≤
      2 * pmPowerDampedRamanujanPrefixEnergy ε Q H +
        2 * (pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 := by
  have hrange :
      naturalCutoffHeadEnergy ε Q H =
        ∑ n ∈ Finset.Icc 1 H,
          (naturalCutoffEnergyCenteredPrefix ε Q n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    unfold naturalCutoffHeadEnergy
    rw [Finset.range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (by omega : 0 < H + 1),
      Finset.sum_insert (by simp)]
    simp [Finset.Ico_add_one_right_eq_Icc]
  rw [hrange]
  have hterm :
      ∀ n ∈ Finset.Icc 1 H,
        (naturalCutoffEnergyCenteredPrefix ε Q n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
          2 * (‖pmPowerDampedRamanujanCumulativePrefix ε Q n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
            2 * (pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    intro n _
    have hn : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) := by positivity
    have hnorm :
        ((pmPowerDampedRamanujanCumulativePrefix ε Q n).re) ^ 2 =
          ‖pmPowerDampedRamanujanCumulativePrefix ε Q n‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        pmPowerDampedRamanujanCumulativePrefix_im hε]
      ring
    have hsq :
        (naturalCutoffEnergyCenteredPrefix ε Q n) ^ 2 ≤
          2 * ‖pmPowerDampedRamanujanCumulativePrefix ε Q n‖ ^ 2 +
            2 * (pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 := by
      unfold naturalCutoffEnergyCenteredPrefix
      rw [← hnorm]
      nlinarith [sq_nonneg ((pmPowerDampedRamanujanCumulativePrefix ε Q n).re +
        pmPowerDampedRamanujanEnergyMean ε Q)]
    calc
      (naturalCutoffEnergyCenteredPrefix ε Q n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ (2 * ‖pmPowerDampedRamanujanCumulativePrefix ε Q n‖ ^ 2 +
            2 * (pmPowerDampedRamanujanEnergyMean ε Q) ^ 2) / ((n : ℝ) * ((n : ℝ) + 1)) :=
        div_le_div_of_nonneg_right hsq hn
      _ = _ := by ring
  calc
    (∑ n ∈ Finset.Icc 1 H,
        (naturalCutoffEnergyCenteredPrefix ε Q n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
      ≤ ∑ n ∈ Finset.Icc 1 H,
          (2 * (‖pmPowerDampedRamanujanCumulativePrefix ε Q n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
            2 * (pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1)))) :=
      Finset.sum_le_sum hterm
    _ = 2 * pmPowerDampedRamanujanPrefixEnergy ε Q H +
          2 * (pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 *
            (∑ n ∈ Finset.Icc 1 H, 1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl
    _ ≤ 2 * pmPowerDampedRamanujanPrefixEnergy ε Q H +
          2 * (pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 * 1 := by
      gcongr
      have hsub : (∑ n ∈ Finset.Icc 1 H, 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
          ∑ n ∈ range (H + 1), 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro n hn
        exact mem_range.mpr (by have := (mem_Icc.mp hn).2; omega)
      rw [sum_range_pronic_inv H] at hsub
      exact hsub.trans (div_le_one_of_le₀ (by linarith) (by positivity))
    _ = _ := by ring

end GaloisForLFunctions.BezoutValuationIncidence

end
