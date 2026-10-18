import GaloisForLFunctions.BezoutValuationIncidence.RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence

/-!
# Cross-Depth Euler Operator Factorization and Prime-Pair Gram Identity (Tool 1)

This module constructs **Tool 1** of the Post–Module 74 Wall 1 programme: the exact multi-depth
operator factorization that pairs multiplicative depth `ω(r) = k` directly against depth
`ω(pr) = k + 1` and iterates coherently across all `2^{ω(P)}` squarefree divisors `m ∣ P`
(`0 ≤ ω(m) ≤ ω(P)`):

1. **Single-Prime Cross-Depth (`ω(r) = k ↔ ω(pr) = k + 1`) Euler Operator Factorization (§1)**:
   For `ε > 0`, prime `p`, and `¬ p ∣ r`, the Route PM Ramanujan weight
   `pmRealRamanujanWeight ε q := (pmPowerDampedRamanujanWeight ε q).re` satisfies
   $$Y_\varepsilon(pr) = -\frac{Y_\varepsilon(r)}{p^{1+\varepsilon} - 1}, \qquad
     Y_\varepsilon(r) - Y_\varepsilon(pr) = \frac{p^{1+\varepsilon}}{p^{1+\varepsilon} - 1}\,Y_\varepsilon(r).$$
   Combining this with the prime-insertion laws for `pmRamanujanPrimitive`, `pmRamanujanStepSource`,
   and `pmRamanujanStepVector` absorbs the `-f_r` shift into the local Euler factor
   `p^{1+ε} / (p^{1+ε} - 1) = (1 - p^{-1-ε})⁻¹` and converts the growing dilation weight into a
   pure decaying Dirichlet power:
   - **Cumulative primitive (`cross_depth_pmRamanujanPrimitive_prime_pair_eq`)**:
     $$Y_\varepsilon(r)\,S_r(N) + Y_\varepsilon(pr)\,S_{pr}(N)
       = \frac{p^{1+\varepsilon}}{p^{1+\varepsilon} - 1}\,Y_\varepsilon(r)\,
         \Bigl(S_r(N) - p^{-\varepsilon}\,S_r(\lfloor N / p \rfloor)\Bigr);$$
   - **Physical step source (`cross_depth_pmRamanujanStepSource_prime_pair_eq`)**:
     $$Y_\varepsilon(r)\,f_r(x) + Y_\varepsilon(pr)\,f_{pr}(x)
       = \frac{p^{1+\varepsilon}}{p^{1+\varepsilon} - 1}\,Y_\varepsilon(r)\,
         \Bigl(f_r(x) - p^{-1-\varepsilon}\,f_r(x / p)\Bigr);$$
   - **Hilbert `SoninL2` step vector (`cross_depth_pmRamanujanStepVector_prime_pair_eq`)**:
     $$Y_\varepsilon(r) \bullet f_r + Y_\varepsilon(pr) \bullet f_{pr}
       = \left(\frac{p^{1+\varepsilon}}{p^{1+\varepsilon} - 1}\,Y_\varepsilon(r)\right) \bullet
         \Bigl(f_r - p^{-\frac{1}{2}-\varepsilon}\,D_{p^{-1}} f_r\Bigr).$$

2. **All-Depth Coherent Hypercube Factorization & Exact `ζ(1+ε) ζ(1+ε)⁻¹ = 1` Cancellation (§2)**:
   Iterating the single-prime cross-depth operator across all divisors `m ∣ P` of an arbitrary
   squarefree integer `P` coprime to `r` (spanning all multiplicative depths
   `ω(mr) = ω(r) + ω(m)` for `0 ≤ ω(m) ≤ ω(P)` simultaneously) transforms the sum of `2^{ω(P)}`
   step sources into the local Euler product `pmEulerCubeFactor ε P = ∏_{p ∣ P} p^{1+ε}/(p^{1+ε}-1)`
   times the pure Dirichlet dilation polynomial `∑_{d ∣ P} μ(d) d^{-1-ε} f_r(x / d)`
   (`all_depth_coherent_pmRamanujanStepSource_re_eq`, `all_depth_coherent_pmRamanujanPrimitive_eq`).
   Moreover, the Euler product prefactor and the alternating Dirichlet sum across all depths satisfy
   the **exact finite-level cancellation identity**
   (`pmEulerCubeFactor_mul_dirichlet_moebius_sum_eq_one`):
   $$\left(\prod_{p \in P.\text{primeFactors}} \frac{p^{1+\varepsilon}}{p^{1+\varepsilon} - 1}\right)
     \left(\sum_{d \in P.\text{divisors}} \mu(d)\,d^{-1-\varepsilon}\right) = 1,$$
   which cancels the un-dilated `f_r(x)` singularity identically across all depths to leave the pure
   scale-difference operator (`all_depth_singularity_cancelled_stepSource_re_eq`).

3. **Cross-Depth Paired Gram Identities, Prime-Star Decomposition & Prime Summability (§3)**:
   - On `{r, pr}`, the quadratic form of `pmRamanujanPrimitiveGram` (`G`) and
     `pmRamanujanEnergyCenteredGram` (`G^{ec}`) factors into
     `(p^{1+ε} / (p^{1+ε} - 1))² Y_ε(r)² [(1 + p^{-1-2ε}) G(r, r) - 2 p^{-1-ε} (G(pr, r) + G(r, r))]`
     (`cross_depth_primitiveGram_two_mode_eq`, `cross_depth_energyCenteredGram_two_mode_eq`).
   - On a multi-branch prime star `{r} ∪ {pr : p ∈ S}`, `cross_depth_prime_star_primitiveGram_eq`
     expresses the full star quadratic form in terms of three unconditionally prime-summable defect
     series (`summable_prime_inv_rpow_sub_one`, `summable_prime_div_sq_rpow_sub_one`,
     `summable_cross_depth_primitiveGram_prime_shift`,
     `summable_cross_depth_energyCenteredGram_prime_shift`) plus the off-diagonal two-prime
     dilation-profile kernel.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

/-! ## §1. Single-Prime Cross-Depth (`ω(r) = k ↔ ω(pr) = k + 1`) Euler Operator Factorization -/

/-- The real Route PM Ramanujan weight `Y_ε(q) := (pmPowerDampedRamanujanWeight ε q).re`. -/
def pmRealRamanujanWeight (ε : ℝ) (q : ℕ) : ℝ :=
  (pmPowerDampedRamanujanWeight ε q).re

/-- Because `pmPowerDampedRamanujanWeight ε q` is purely real for `ε > 0`, it equals the complex
coercion of `pmRealRamanujanWeight ε q`. -/
theorem pmPowerDampedRamanujanWeight_eq_ofReal_pmRealRamanujanWeight
    {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    pmPowerDampedRamanujanWeight ε q = (pmRealRamanujanWeight ε q : ℂ) := by
  rw [pmRealRamanujanWeight, pmPowerDampedRamanujanWeight_eq_ofReal hε, Complex.ofReal_re]

/-- **Single-Prime Multiplicative Recursion for `pmRealRamanujanWeight`**:
For `ε > 0`, prime `p`, and `¬ p ∣ r`, advancing from depth `ω(r) = k` to `ω(pr) = k + 1` divides
the Ramanujan weight by `-(p^{1+ε} - 1)`. -/
theorem pmRealRamanujanWeight_prime_mul {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) :
    pmRealRamanujanWeight ε (p * r) =
      -pmRealRamanujanWeight ε r / ((p : ℝ) ^ (1 + ε) - 1) := by
  have h := congrArg Complex.re (pmPowerDampedRamanujanWeight_prime_mul hε hp hpr)
  simpa only [pmRealRamanujanWeight, Complex.div_ofReal_re, Complex.neg_re] using h

/-- **Cross-Depth Weight Difference Equals Local Euler Factor**:
Pairing the depth-`k` weight `Y_ε(r)` against the depth-`(k+1)` weight `-Y_ε(pr)` (inherited from
the `-f_r` shift in `f_{pr} = √p D_{1/p} f_r - f_r`) produces the exact local Euler factor
`p^{1+ε} / (p^{1+ε} - 1) = (1 - p^{-1-ε})⁻¹`. -/
theorem pmRealRamanujanWeight_sub_prime_mul {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) :
    pmRealRamanujanWeight ε r - pmRealRamanujanWeight ε (p * r) =
      (p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) * pmRealRamanujanWeight ε r := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hden : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_rpow hp1 (by linarith)))
  rw [pmRealRamanujanWeight_prime_mul hε hp hpr]
  field_simp [hden]
  ring

/-- Helper: for any `p > 0` and `ε : ℝ`, `p^{1+ε} * p^{-ε} = p`. -/
private theorem rpow_one_add_mul_rpow_neg {p : ℝ} (hp : 0 < p) (ε : ℝ) :
    p ^ (1 + ε) * p ^ (-ε) = p := by
  rw [← Real.rpow_add hp, show 1 + ε + -ε = (1 : ℝ) by ring, Real.rpow_one]

/-- Helper: for any `p > 0` and `ε : ℝ`, `p^{1+ε} * p^{-1-ε} = 1`. -/
private theorem rpow_one_add_mul_rpow_neg_one_sub {p : ℝ} (hp : 0 < p) (ε : ℝ) :
    p ^ (1 + ε) * p ^ (-1 - ε) = 1 := by
  rw [← Real.rpow_add hp, show 1 + ε + (-1 - ε) = (0 : ℝ) by ring, Real.rpow_zero]

/-- Helper: for any `p > 0` and `ε : ℝ`, `p^{1+ε} * p^{-1/2-ε} = √p`. -/
private theorem rpow_one_add_mul_rpow_neg_half_sub {p : ℝ} (hp : 0 < p) (ε : ℝ) :
    p ^ (1 + ε) * p ^ (-(1 / 2 : ℝ) - ε) = Real.sqrt p := by
  rw [← Real.rpow_add hp, show 1 + ε + (-(1 / 2 : ℝ) - ε) = (1 / 2 : ℝ) by ring,
    ← Real.sqrt_eq_rpow]

/-- **Cross-Depth Dilation Weight Conversion**:
The `√p`-amplified depth-`(k+1)` weight `Y_ε(pr) √p` equals the local Euler factor
`(p^{1+ε} / (p^{1+ε} - 1)) Y_ε(r)` times the decaying Dirichlet weight `-p^{-1/2-ε}`. -/
theorem pmRealRamanujanWeight_prime_mul_mul_sqrt {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) :
    pmRealRamanujanWeight ε (p * r) * Real.sqrt (p : ℝ) =
      -((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) * pmRealRamanujanWeight ε r *
        (p : ℝ) ^ (-(1 / 2 : ℝ) - ε)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [pmRealRamanujanWeight_prime_mul hε hp hpr,
    ← rpow_one_add_mul_rpow_neg_half_sub hp0 ε]
  ring

/-- **Cross-Depth Cumulative Primitive Factorization (`ω(r) = k ↔ ω(pr) = k + 1`)**:
Pairing the depth-`k` primitive `Y_ε(r) S_r(N)` with its depth-`(k+1)` prime multiple
`Y_ε(pr) S_{pr}(N)` factors out the local Euler factor `p^{1+ε} / (p^{1+ε} - 1)` and converts the
growing `+p` multiplier in `S_{pr}(N) = p S_r(⌊N/p⌋) - S_r(N)` into the decaying power `-p^{-ε}`. -/
theorem cross_depth_pmRamanujanPrimitive_prime_pair_eq {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) (N : ℕ) :
    pmRealRamanujanWeight ε r * (pmRamanujanPrimitive r N).re +
        pmRealRamanujanWeight ε (p * r) * (pmRamanujanPrimitive (p * r) N).re =
      (p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) * pmRealRamanujanWeight ε r *
        ((pmRamanujanPrimitive r N).re -
          (p : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / p)).re) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hden : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_rpow hp1 (by linarith)))
  have hprim : (pmRamanujanPrimitive (p * r) N).re =
      (p : ℝ) * (pmRamanujanPrimitive r (N / p)).re - (pmRamanujanPrimitive r N).re := by
    have h := congrArg Complex.re (pmRamanujanPrimitive_prime_mul hp hpr N)
    simpa only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero] using h
  rw [hprim, pmRealRamanujanWeight_prime_mul hε hp hpr]
  have hp_pow : (p : ℝ) ^ (1 + ε) * (p : ℝ) ^ (-ε) = (p : ℝ) :=
    rpow_one_add_mul_rpow_neg hp0 ε
  field_simp [hden]
  linear_combination
    pmRealRamanujanWeight ε r * (pmRamanujanPrimitive r (N / p)).re * hp_pow

/-- **Cross-Depth Physical Step-Source Factorization (`ω(r) = k ↔ ω(pr) = k + 1`)**:
Pairing the depth-`k` step source `Y_ε(r) pmRamanujanStepSource r x` with its depth-`(k+1)` prime
multiple `Y_ε(pr) pmRamanujanStepSource (p * r) x` factors out the local Euler factor
`p^{1+ε} / (p^{1+ε} - 1)` and weights the dilated source `pmRamanujanStepSource r (x / p)` by the
unconditionally prime-summable Dirichlet coefficient `-p^{-1-ε}`. -/
theorem cross_depth_pmRamanujanStepSource_prime_pair_re_eq {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) (x : ℝ) :
    pmRealRamanujanWeight ε r * (pmRamanujanStepSource r x).re +
        pmRealRamanujanWeight ε (p * r) * (pmRamanujanStepSource (p * r) x).re =
      (p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) * pmRealRamanujanWeight ε r *
        ((pmRamanujanStepSource r x).re -
          (p : ℝ) ^ (-1 - ε) * (pmRamanujanStepSource r (x / p)).re) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hden : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_rpow hp1 (by linarith)))
  have hstep : (pmRamanujanStepSource (p * r) x).re =
      (pmRamanujanStepSource r (x / p)).re - (pmRamanujanStepSource r x).re := by
    have h := congrArg Complex.re (pmRamanujanStepSource_prime_mul hp hpr x)
    simpa only [Complex.sub_re] using h
  rw [hstep, pmRealRamanujanWeight_prime_mul hε hp hpr]
  have hp_pow : (p : ℝ) ^ (1 + ε) * (p : ℝ) ^ (-1 - ε) = 1 :=
    rpow_one_add_mul_rpow_neg_one_sub hp0 ε
  field_simp [hden]
  linear_combination
    pmRealRamanujanWeight ε r * (pmRamanujanStepSource r (x / p)).re * hp_pow

/-- **Cross-Depth Hilbert `SoninL2` Step-Vector Euler Factorization**:
In the full-line Hilbert space `SoninL2`, pairing the depth-`k` vector
`pmPowerDampedRamanujanWeight ε r • pmRamanujanStepVector r hr` with its depth-`(k+1)` prime
multiple `pmPowerDampedRamanujanWeight ε (p * r) • pmRamanujanStepVector (p * r) hpr'` yields the
exact local Euler difference operator `(p^{1+ε} / (p^{1+ε} - 1)) (I - p^{-1/2-ε} D_{p⁻¹})` acting
on `pmRamanujanStepVector r hr`. -/
theorem cross_depth_pmRamanujanStepVector_prime_pair_eq {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) :
    pmPowerDampedRamanujanWeight ε r • pmRamanujanStepVector r hr +
        pmPowerDampedRamanujanWeight ε (p * r) •
          pmRamanujanStepVector (p * r)
            (lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)) =
      (((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) *
          pmRealRamanujanWeight ε r : ℝ) : ℂ) •
        (pmRamanujanStepVector r hr -
          (((p : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ) •
            dilation (p : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hp.pos))
              (pmRamanujanStepVector r hr)) := by
  let f := pmRamanujanStepVector r hr
  let u := dilation (p : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hp.pos)) f
  rw [pmRamanujanStepVector_prime_mul hp hr hpr,
    pmPowerDampedRamanujanWeight_eq_ofReal_pmRealRamanujanWeight hε r,
    pmPowerDampedRamanujanWeight_eq_ofReal_pmRealRamanujanWeight hε (p * r)]
  change (pmRealRamanujanWeight ε r : ℂ) • f +
      (pmRealRamanujanWeight ε (p * r) : ℂ) • ((Real.sqrt (p : ℝ) : ℂ) • u - f) =
    (((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) *
        pmRealRamanujanWeight ε r : ℝ) : ℂ) •
      (f - (((p : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ) • u)
  rw [smul_sub, smul_smul, smul_sub, smul_smul]
  have h1 :
      (((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) *
          pmRealRamanujanWeight ε r : ℝ) : ℂ) • f =
        (pmRealRamanujanWeight ε r : ℂ) • f -
          (pmRealRamanujanWeight ε (p * r) : ℂ) • f := by
    rw [← sub_smul]
    congr 1
    exact_mod_cast (pmRealRamanujanWeight_sub_prime_mul hε hp hpr).symm
  have h2 :
      (pmRealRamanujanWeight ε (p * r) : ℂ) * (Real.sqrt (p : ℝ) : ℂ) =
        -((((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) *
            pmRealRamanujanWeight ε r : ℝ) : ℂ) *
          (((p : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)) := by
    exact_mod_cast pmRealRamanujanWeight_prime_mul_mul_sqrt hε hp hpr
  rw [h1, h2, neg_smul]
  abel

/-! ## §2. All-Depth Coherent Hypercube Factorization & Exact `ζ(1+ε) ζ(1+ε)⁻¹ = 1` Cancellation -/

/-- The multi-depth local Euler product factor
`∏_{p ∈ P.primeFactors} (p^{1+ε} / (p^{1+ε} - 1)) = ∏_{p ∣ P} (1 - p^{-1-ε})⁻¹`. -/
def pmEulerCubeFactor (ε : ℝ) (P : ℕ) : ℝ :=
  ∏ p ∈ P.primeFactors, (p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1)

@[simp]
theorem pmEulerCubeFactor_one (ε : ℝ) : pmEulerCubeFactor ε 1 = 1 := by
  simp [pmEulerCubeFactor]

theorem pmEulerCubeFactor_pos {ε : ℝ} (hε : 0 < ε) (P : ℕ) :
    0 < pmEulerCubeFactor ε P := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hr : 1 < (p : ℝ) ^ (1 + ε) := Real.one_lt_rpow hp1 (by linarith)
  exact div_pos (by linarith) (sub_pos.mpr hr)

theorem pmEulerCubeFactor_prime_mul (ε : ℝ) {p Q : ℕ}
    (hp : p.Prime) (hQ : Q ≠ 0) (hpQ : ¬ p ∣ Q) :
    pmEulerCubeFactor ε (p * Q) =
      (p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) * pmEulerCubeFactor ε Q := by
  have hnot : p ∉ Q.primeFactors := fun h => hpQ (Nat.dvd_of_mem_primeFactors h)
  simp only [pmEulerCubeFactor, Nat.primeFactors_mul hp.ne_zero hQ,
    hp.primeFactors, Finset.singleton_union, Finset.prod_insert hnot]

/-- Helper: divisor sum splitting under multiplication by a prime `p ∤ Q`. -/
private theorem sum_divisors_prime_mul {α : Type*} [AddCommMonoid α] (F : ℕ → α)
    {p Q : ℕ} (hp : p.Prime) (hpQ : ¬ p ∣ Q) :
    (∑ d ∈ (p * Q).divisors, F d) = ∑ d ∈ Q.divisors, (F d + F (p * d)) := by
  classical
  rw [(hp.coprime_iff_not_dvd.mpr hpQ).divisors_mul]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
  trans ∑ x ∈ p.divisors ×ˢ Q.divisors, F (x.1 * x.2)
  · exact Finset.sum_attach (p.divisors ×ˢ Q.divisors) (fun x : ℕ × ℕ => F (x.1 * x.2))
  rw [Finset.sum_product, hp.divisors, Finset.sum_pair hp.ne_one.symm]
  simp only [one_mul, Finset.sum_add_distrib]

/-- **Multiplicative Factoring of the Finite Dirichlet Möbius Polynomial**:
For any prime `p ∤ Q` and any real exponent `s : ℝ`, summing `μ(d) d^s` over `d ∣ pQ` factors out
`1 - p^s`. -/
theorem dirichlet_moebius_sum_divisors_prime_mul (s : ℝ) {p Q : ℕ}
    (hp : p.Prime) (hpQ : ¬ p ∣ Q) :
    (∑ d ∈ (p * Q).divisors, moebiusReal d * (d : ℝ) ^ s) =
      (1 - (p : ℝ) ^ s) * ∑ d ∈ Q.divisors, moebiusReal d * (d : ℝ) ^ s := by
  rw [sum_divisors_prime_mul _ hp hpQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdQ : d ∣ Q := Nat.dvd_of_mem_divisors hd
  have hpd : ¬ p ∣ d := fun h => hpQ (h.trans hdQ)
  have hmu : moebiusReal (p * d) = -moebiusReal d := by
    simpa [moebiusReal, hpd] using Sieve.moebius_prime_mul (e := d) hp
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hd0 : (0 : ℝ) ≤ d := by positivity
  rw [hmu, Nat.cast_mul, Real.mul_rpow hp0 hd0]
  ring

/-- **Exact Finite-Level `ζ(1+ε) ζ(1+ε)⁻¹ = 1` Cancellation Across All Multiplicative Depths**:
For every `ε > 0` and every squarefree integer `P`, the local Euler product
`pmEulerCubeFactor ε P = ∏_{p ∣ P} p^{1+ε} / (p^{1+ε} - 1)` and the coherent alternating Dirichlet
sum `∑_{d ∣ P} μ(d) d^{-1-ε}` across all depths `k = ω(d) ∈ {0, ..., ω(P)}` multiply to `1`
identically. -/
theorem pmEulerCubeFactor_mul_dirichlet_moebius_sum_eq_one
    {ε : ℝ} (hε : 0 < ε) {P : ℕ} (hP : Squarefree P) :
    pmEulerCubeFactor ε P *
        (∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-1 - ε)) = 1 := by
  induction P using induction_on_primes with
  | zero => exact (_root_.not_squarefree_zero hP).elim
  | one => simp [pmEulerCubeFactor_one, moebiusReal]
  | prime_mul p Q hp ih =>
    have hQ : Squarefree Q := hP.of_mul_right
    have hQ0 : Q ≠ 0 := by intro h; subst h; exact _root_.not_squarefree_zero hQ
    have hpQ : ¬ p ∣ Q := fun h =>
      (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hP)) h
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hden : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.one_lt_rpow hp1 (by linarith)))
    have hlocal :
        (p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) * (1 - (p : ℝ) ^ (-1 - ε)) = 1 := by
      have hp_pow := rpow_one_add_mul_rpow_neg_one_sub hp0 ε
      field_simp [hden]
      linear_combination -hp_pow
    rw [pmEulerCubeFactor_prime_mul ε hp hQ0 hpQ,
      dirichlet_moebius_sum_divisors_prime_mul (-1 - ε) hp hpQ]
    calc
      (p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) * pmEulerCubeFactor ε Q *
          ((1 - (p : ℝ) ^ (-1 - ε)) * ∑ d ∈ Q.divisors, moebiusReal d * (d : ℝ) ^ (-1 - ε)) =
        ((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) * (1 - (p : ℝ) ^ (-1 - ε))) *
          (pmEulerCubeFactor ε Q * ∑ d ∈ Q.divisors, moebiusReal d * (d : ℝ) ^ (-1 - ε)) := by
        ring
      _ = 1 * 1 := by rw [hlocal, ih hQ]
      _ = 1 := mul_one 1

/-- **All-Depth Coherent Factorization for Cumulative Primitives (`0 ≤ ω(m) ≤ ω(P)`)**:
For any `ε > 0`, any squarefree `P`, any base modulus `r` coprime to `P`, and any `N : ℕ`, summing
`Y_ε(mr) S_{mr}(N)` coherently across all `2^{ω(P)}` divisors `m ∣ P` factors out
`pmEulerCubeFactor ε P * Y_ε(r)` and converts the signed divisor sum into the pure Dirichlet
dilation polynomial `∑_{d ∣ P} μ(d) d^{-ε} S_r(⌊N / d⌋)`. -/
theorem all_depth_coherent_pmRamanujanPrimitive_eq {ε : ℝ} (hε : 0 < ε)
    {P r : ℕ} (hP : Squarefree P) (hPr : Nat.Coprime P r) (N : ℕ) :
    (∑ m ∈ P.divisors,
        pmRealRamanujanWeight ε (m * r) * (pmRamanujanPrimitive (m * r) N).re) =
      pmEulerCubeFactor ε P * pmRealRamanujanWeight ε r *
        ∑ d ∈ P.divisors,
          moebiusReal d * (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / d)).re := by
  induction P using induction_on_primes generalizing N with
  | zero => exact (_root_.not_squarefree_zero hP).elim
  | one => simp [pmEulerCubeFactor_one, moebiusReal]
  | prime_mul p Q hp ih =>
    have hQ : Squarefree Q := hP.of_mul_right
    have hQ0 : Q ≠ 0 := by intro h; subst h; exact _root_.not_squarefree_zero hQ
    have hpQ : ¬ p ∣ Q := fun h =>
      (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hP)) h
    have hQr : Nat.Coprime Q r := (Nat.coprime_mul_iff_left.mp hPr).2
    have hpr : ¬ p ∣ r := hp.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_left.mp hPr).1
    rw [sum_divisors_prime_mul _ hp hpQ]
    have hpair :
        ∀ m ∈ Q.divisors,
          pmRealRamanujanWeight ε (m * r) * (pmRamanujanPrimitive (m * r) N).re +
              pmRealRamanujanWeight ε (p * m * r) * (pmRamanujanPrimitive (p * m * r) N).re =
            (p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) *
              (pmRealRamanujanWeight ε (m * r) * (pmRamanujanPrimitive (m * r) N).re -
                (p : ℝ) ^ (-ε) *
                  (pmRealRamanujanWeight ε (m * r) *
                    (pmRamanujanPrimitive (m * r) (N / p)).re)) := by
      intro m hm
      have hmQ : m ∣ Q := Nat.dvd_of_mem_divisors hm
      have hpm : ¬ p ∣ m := fun h => hpQ (h.trans hmQ)
      have hpmr : ¬ p ∣ m * r := by
        rw [hp.dvd_mul]
        exact not_or.mpr ⟨hpm, hpr⟩
      have h := cross_depth_pmRamanujanPrimitive_prime_pair_eq hε hp hpmr N
      rw [mul_assoc p m r]
      linarith
    rw [Finset.sum_congr rfl hpair, ← Finset.mul_sum, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ih hQ hQr N, ih hQ hQr (N / p),
      pmEulerCubeFactor_prime_mul ε hp hQ0 hpQ, sum_divisors_prime_mul _ hp hpQ]
    have hrhs :
        (∑ d ∈ Q.divisors,
            moebiusReal d * (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / d)).re) -
          (p : ℝ) ^ (-ε) *
            (∑ d ∈ Q.divisors,
              moebiusReal d * (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / p / d)).re) =
        ∑ d ∈ Q.divisors,
          (moebiusReal d * (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / d)).re +
            moebiusReal (p * d) * ((p * d : ℕ) : ℝ) ^ (-ε) *
              (pmRamanujanPrimitive r (N / (p * d))).re) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdQ : d ∣ Q := Nat.dvd_of_mem_divisors hd
      have hpd : ¬ p ∣ d := fun h => hpQ (h.trans hdQ)
      have hmu : moebiusReal (p * d) = -moebiusReal d := by
        simpa [moebiusReal, hpd] using Sieve.moebius_prime_mul (e := d) hp
      have hp0 : (0 : ℝ) ≤ p := by positivity
      have hd0 : (0 : ℝ) ≤ d := by positivity
      rw [hmu, Nat.cast_mul, Real.mul_rpow hp0 hd0, Nat.div_div_eq_div_mul]
      ring
    rw [← hrhs]
    ring

/-- **All-Depth Coherent Factorization for Physical Step Sources (`0 ≤ ω(m) ≤ ω(P)`)**:
For any `ε > 0`, any squarefree `P`, any base modulus `r` coprime to `P`, and any `x : ℝ`, summing
`Y_ε(mr) (pmRamanujanStepSource (mr) x).re` coherently across all `2^{ω(P)}` divisors `m ∣ P`
factors out `pmEulerCubeFactor ε P * Y_ε(r)` and produces the pure Dirichlet dilation polynomial
`∑_{d ∣ P} μ(d) d^{-1-ε} (pmRamanujanStepSource r (x / d)).re`. -/
theorem all_depth_coherent_pmRamanujanStepSource_re_eq {ε : ℝ} (hε : 0 < ε)
    {P r : ℕ} (hP : Squarefree P) (hPr : Nat.Coprime P r) (x : ℝ) :
    (∑ m ∈ P.divisors,
        pmRealRamanujanWeight ε (m * r) * (pmRamanujanStepSource (m * r) x).re) =
      pmEulerCubeFactor ε P * pmRealRamanujanWeight ε r *
        ∑ d ∈ P.divisors,
          moebiusReal d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanStepSource r (x / d)).re := by
  induction P using induction_on_primes generalizing x with
  | zero => exact (_root_.not_squarefree_zero hP).elim
  | one => simp [pmEulerCubeFactor_one, moebiusReal]
  | prime_mul p Q hp ih =>
    have hQ : Squarefree Q := hP.of_mul_right
    have hQ0 : Q ≠ 0 := by intro h; subst h; exact _root_.not_squarefree_zero hQ
    have hpQ : ¬ p ∣ Q := fun h =>
      (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hP)) h
    have hQr : Nat.Coprime Q r := (Nat.coprime_mul_iff_left.mp hPr).2
    have hpr : ¬ p ∣ r := hp.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_left.mp hPr).1
    rw [sum_divisors_prime_mul _ hp hpQ]
    have hpair :
        ∀ m ∈ Q.divisors,
          pmRealRamanujanWeight ε (m * r) * (pmRamanujanStepSource (m * r) x).re +
              pmRealRamanujanWeight ε (p * m * r) * (pmRamanujanStepSource (p * m * r) x).re =
            (p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1) *
              (pmRealRamanujanWeight ε (m * r) * (pmRamanujanStepSource (m * r) x).re -
                (p : ℝ) ^ (-1 - ε) *
                  (pmRealRamanujanWeight ε (m * r) *
                    (pmRamanujanStepSource (m * r) (x / p)).re)) := by
      intro m hm
      have hmQ : m ∣ Q := Nat.dvd_of_mem_divisors hm
      have hpm : ¬ p ∣ m := fun h => hpQ (h.trans hmQ)
      have hpmr : ¬ p ∣ m * r := by
        rw [hp.dvd_mul]
        exact not_or.mpr ⟨hpm, hpr⟩
      have h := cross_depth_pmRamanujanStepSource_prime_pair_re_eq hε hp hpmr x
      rw [mul_assoc p m r]
      linarith
    rw [Finset.sum_congr rfl hpair, ← Finset.mul_sum, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ih hQ hQr x, ih hQ hQr (x / p),
      pmEulerCubeFactor_prime_mul ε hp hQ0 hpQ, sum_divisors_prime_mul _ hp hpQ]
    have hrhs :
        (∑ d ∈ Q.divisors,
            moebiusReal d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanStepSource r (x / d)).re) -
          (p : ℝ) ^ (-1 - ε) *
            (∑ d ∈ Q.divisors,
              moebiusReal d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanStepSource r (x / p / d)).re) =
        ∑ d ∈ Q.divisors,
          (moebiusReal d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanStepSource r (x / d)).re +
            moebiusReal (p * d) * ((p * d : ℕ) : ℝ) ^ (-1 - ε) *
              (pmRamanujanStepSource r (x / (p * d : ℕ))).re) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdQ : d ∣ Q := Nat.dvd_of_mem_divisors hd
      have hpd : ¬ p ∣ d := fun h => hpQ (h.trans hdQ)
      have hmu : moebiusReal (p * d) = -moebiusReal d := by
        simpa [moebiusReal, hpd] using Sieve.moebius_prime_mul (e := d) hp
      have hp0 : (0 : ℝ) ≤ p := by positivity
      have hd0 : (0 : ℝ) ≤ d := by positivity
      rw [hmu, Nat.cast_mul, Real.mul_rpow hp0 hd0, div_div]
      ring
    rw [← hrhs]
    ring

/-- **Singularity-Cancelled All-Depth Scale-Difference Identity**:
Combining `all_depth_coherent_pmRamanujanStepSource_re_eq` with the exact finite-level cancellation
`pmEulerCubeFactor_mul_dirichlet_moebius_sum_eq_one` shows that the un-dilated `f_r(x)` mode
cancels the `pmEulerCubeFactor ε P` singularity across all multiplicative depths `k = ω(d)`
simultaneously, leaving `Y_ε(r) f_r(x)` plus the pure scale-difference sum over `d ∣ P`. -/
theorem all_depth_singularity_cancelled_stepSource_re_eq {ε : ℝ} (hε : 0 < ε)
    {P r : ℕ} (hP : Squarefree P) (hPr : Nat.Coprime P r) (x : ℝ) :
    (∑ m ∈ P.divisors,
        pmRealRamanujanWeight ε (m * r) * (pmRamanujanStepSource (m * r) x).re) =
      pmRealRamanujanWeight ε r * (pmRamanujanStepSource r x).re +
        pmEulerCubeFactor ε P * pmRealRamanujanWeight ε r *
          ∑ d ∈ P.divisors,
            moebiusReal d * (d : ℝ) ^ (-1 - ε) *
              ((pmRamanujanStepSource r (x / d)).re - (pmRamanujanStepSource r x).re) := by
  rw [all_depth_coherent_pmRamanujanStepSource_re_eq hε hP hPr x]
  have hsplit :
      (∑ d ∈ P.divisors,
          moebiusReal d * (d : ℝ) ^ (-1 - ε) *
            ((pmRamanujanStepSource r (x / d)).re - (pmRamanujanStepSource r x).re)) =
        (∑ d ∈ P.divisors,
            moebiusReal d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanStepSource r (x / d)).re) -
          (∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-1 - ε)) *
            (pmRamanujanStepSource r x).re := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsplit]
  have hcancel := pmEulerCubeFactor_mul_dirichlet_moebius_sum_eq_one hε hP
  linear_combination
    pmRealRamanujanWeight ε r * (pmRamanujanStepSource r x).re * hcancel

/-! ## §3. Cross-Depth Paired Gram Identities, Prime-Star Decomposition & Prime Summability -/

/-- **Cross-Depth Paired Two-Mode Gram Identity (Raw Pronic Gram)**:
For `ε > 0`, prime `p`, `r > 1`, and `¬ p ∣ r`, the quadratic form of `pmRamanujanPrimitiveGram` on
the depth-`k` / depth-`(k+1)` pair `{r, pr}` with weights `Y_ε(r)` and `Y_ε(pr)` factors out the
squared local Euler factor `(p^{1+ε} / (p^{1+ε} - 1))² Y_ε(r)²`, converts the `(p - 1)` diagonal
growth into `1 + p^{-1-2ε}`, and replaces the raw off-diagonal `G(pr, r)` by the decaying shifted
covariance `-2 p^{-1-ε} (G(pr, r) + G(r, r))`. -/
theorem cross_depth_primitiveGram_two_mode_eq {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) :
    pmRealRamanujanWeight ε r ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * pmRealRamanujanWeight ε r * pmRealRamanujanWeight ε (p * r) *
          pmRamanujanPrimitiveGram (p * r) r +
        pmRealRamanujanWeight ε (p * r) ^ 2 * pmRamanujanPrimitiveGram (p * r) (p * r) =
      ((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1)) ^ 2 * pmRealRamanujanWeight ε r ^ 2 *
        ((1 + (p : ℝ) ^ (-1 - 2 * ε)) * pmRamanujanPrimitiveGram r r -
          2 * (p : ℝ) ^ (-1 - ε) *
            (pmRamanujanPrimitiveGram (p * r) r + pmRamanujanPrimitiveGram r r)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (p : ℝ) ^ (1 + ε) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp0 _)
  have hden : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_rpow hp1 (by linarith)))
  rw [pmRamanujanPrimitiveGram_shifted_two_mode_eq hp hr hpr,
    pmRealRamanujanWeight_sub_prime_mul hε hp hpr,
    pmRealRamanujanWeight_prime_mul hε hp hpr]
  have hp_pow1 : (p : ℝ) ^ (-1 - ε) = 1 / (p : ℝ) ^ (1 + ε) :=
    eq_one_div_of_mul_eq_one_right (rpow_one_add_mul_rpow_neg_one_sub hp0 ε)
  have hp_pow2 : (p : ℝ) ^ (-1 - 2 * ε) = (p : ℝ) / ((p : ℝ) ^ (1 + ε)) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hpos), sq, ← mul_assoc, ← Real.rpow_add hp0,
      ← Real.rpow_add hp0, show -1 - 2 * ε + (1 + ε) + (1 + ε) = (1 : ℝ) by ring,
      Real.rpow_one]
  rw [hp_pow1, hp_pow2]
  field_simp [hden, hpos]
  ring

/-- **Cross-Depth Paired Two-Mode Gram Identity in Dilation-Profile Form**:
Rewriting `G(pr, r) + G(r, r) = √p Φ_r(p)` shows that the paired cross-depth quadratic form on
`{r, pr}` is governed by `-2 p^{-1/2-ε} Φ_r(p)`. -/
theorem cross_depth_primitiveGram_two_mode_eq_dilationProfile {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) :
    pmRealRamanujanWeight ε r ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * pmRealRamanujanWeight ε r * pmRealRamanujanWeight ε (p * r) *
          pmRamanujanPrimitiveGram (p * r) r +
        pmRealRamanujanWeight ε (p * r) ^ 2 * pmRamanujanPrimitiveGram (p * r) (p * r) =
      ((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1)) ^ 2 * pmRealRamanujanWeight ε r ^ 2 *
        ((1 + (p : ℝ) ^ (-1 - 2 * ε)) * pmRamanujanPrimitiveGram r r -
          2 * (p : ℝ) ^ (-(1 / 2 : ℝ) - ε) * pmRamanujanDilationProfile r hr (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [cross_depth_primitiveGram_two_mode_eq hε hp hr hpr,
    pmRamanujanPrimitiveGram_prime_mul_add_diag_eq_dilationProfile hp hr hpr]
  have hp_sqrt : (p : ℝ) ^ (-1 - ε) * Real.sqrt (p : ℝ) = (p : ℝ) ^ (-(1 / 2 : ℝ) - ε) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp0]
    congr 1; ring
  linear_combination
    -2 * ((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1)) ^ 2 *
      pmRealRamanujanWeight ε r ^ 2 * pmRamanujanDilationProfile r hr (p : ℝ) * hp_sqrt

/-- **Cross-Depth Paired Two-Mode Identity (Energy-Centered Gram)**:
For `G^{ec} = pmRamanujanEnergyCenteredGram`, pairing depth `k` (`r`) with depth `k+1` (`pr`) yields
the exact same local Euler factorization plus the prime-power von Mangoldt innovation
`((p - 1) / (p^{1+ε} - 1)²) Y_ε(r)² Λ(r)²`. -/
theorem cross_depth_energyCenteredGram_two_mode_eq {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) :
    pmRealRamanujanWeight ε r ^ 2 * pmRamanujanEnergyCenteredGram r r +
        2 * pmRealRamanujanWeight ε r * pmRealRamanujanWeight ε (p * r) *
          pmRamanujanEnergyCenteredGram (p * r) r +
        pmRealRamanujanWeight ε (p * r) ^ 2 * pmRamanujanEnergyCenteredGram (p * r) (p * r) =
      ((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1)) ^ 2 * pmRealRamanujanWeight ε r ^ 2 *
        ((1 + (p : ℝ) ^ (-1 - 2 * ε)) * pmRamanujanEnergyCenteredGram r r -
          2 * (p : ℝ) ^ (-1 - ε) *
            (pmRamanujanEnergyCenteredGram (p * r) r + pmRamanujanEnergyCenteredGram r r)) +
        ((p : ℝ) - 1) / ((p : ℝ) ^ (1 + ε) - 1) ^ 2 *
          pmRealRamanujanWeight ε r ^ 2 * (vonMangoldt r) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (p : ℝ) ^ (1 + ε) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp0 _)
  have hden : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_rpow hp1 (by linarith)))
  rw [pmRamanujanEnergyCenteredGram_shifted_two_mode_eq hp hr hpr,
    pmRealRamanujanWeight_sub_prime_mul hε hp hpr,
    pmRealRamanujanWeight_prime_mul hε hp hpr]
  have hp_pow1 : (p : ℝ) ^ (-1 - ε) = 1 / (p : ℝ) ^ (1 + ε) :=
    eq_one_div_of_mul_eq_one_right (rpow_one_add_mul_rpow_neg_one_sub hp0 ε)
  have hp_pow2 : (p : ℝ) ^ (-1 - 2 * ε) = (p : ℝ) / ((p : ℝ) ^ (1 + ε)) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hpos), sq, ← mul_assoc, ← Real.rpow_add hp0,
      ← Real.rpow_add hp0, show -1 - 2 * ε + (1 + ε) + (1 + ε) = (1 : ℝ) by ring,
      Real.rpow_one]
  rw [hp_pow1, hp_pow2]
  field_simp [hden, hpos]
  ring

/-- For any composite non-prime-power modulus `r > 1` (`¬ IsPrimePow r`), the von Mangoldt
innovation vanishes identically, so `pmRamanujanEnergyCenteredGram` satisfies the pure Euler
two-mode factorization. -/
theorem cross_depth_energyCenteredGram_two_mode_eq_of_not_isPrimePow {ε : ℝ} (hε : 0 < ε)
    {p r : ℕ} (hp : p.Prime) (hr : 1 < r) (hrp : ¬ IsPrimePow r) (hpr : ¬ p ∣ r) :
    pmRealRamanujanWeight ε r ^ 2 * pmRamanujanEnergyCenteredGram r r +
        2 * pmRealRamanujanWeight ε r * pmRealRamanujanWeight ε (p * r) *
          pmRamanujanEnergyCenteredGram (p * r) r +
        pmRealRamanujanWeight ε (p * r) ^ 2 * pmRamanujanEnergyCenteredGram (p * r) (p * r) =
      ((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1)) ^ 2 * pmRealRamanujanWeight ε r ^ 2 *
        ((1 + (p : ℝ) ^ (-1 - 2 * ε)) * pmRamanujanEnergyCenteredGram r r -
          2 * (p : ℝ) ^ (-1 - ε) *
            (pmRamanujanEnergyCenteredGram (p * r) r + pmRamanujanEnergyCenteredGram r r)) := by
  have hΛ : vonMangoldt r = 0 := vonMangoldt_eq_zero_iff.mpr hrp
  simpa [hΛ] using cross_depth_energyCenteredGram_two_mode_eq hε hp hr hpr

/-- **Multi-Branch Prime-Star Cross-Depth Decomposition**:
For any `ε > 0`, any base modulus `r > 1`, and any finite set `S` of primes not dividing `r`, the
quadratic form of `pmRamanujanPrimitiveGram` on the star `{r} ∪ {pr : p ∈ S}` with the actual Route
PM weights `Y_ε(r)` and `Y_ε(pr)` decomposes into:
1. the shifted base energy `(1 + ∑_{p ∈ S} 1/(p^{1+ε} - 1))² Y_ε(r)² G(r, r)`,
2. the shifted single-prime cross-term
   `-2 (1 + ∑_{p ∈ S} 1/(p^{1+ε} - 1)) Y_ε(r)² ∑_{p ∈ S} (G(pr, r) + G(r, r)) / (p^{1+ε} - 1)`,
3. the pure two-prime dilation-profile quadratic form
   `Y_ε(r)² ∑_{p ∈ S} ∑_{q ∈ S} (√p / (p^{1+ε} - 1)) (√q / (q^{1+ε} - 1)) Φ_r(p / q)`. -/
theorem cross_depth_prime_star_primitiveGram_eq {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : 1 < r) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ r) :
    pmRealRamanujanWeight ε r ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * pmRealRamanujanWeight ε r *
          (∑ p ∈ S, pmRealRamanujanWeight ε (p * r) * pmRamanujanPrimitiveGram (p * r) r) +
        (∑ p ∈ S, ∑ q ∈ S,
          pmRealRamanujanWeight ε (p * r) * pmRealRamanujanWeight ε (q * r) *
            pmRamanujanPrimitiveGram (p * r) (q * r)) =
      pmRealRamanujanWeight ε r ^ 2 *
        ((1 + ∑ p ∈ S, 1 / ((p : ℝ) ^ (1 + ε) - 1)) ^ 2 * pmRamanujanPrimitiveGram r r -
          2 * (1 + ∑ p ∈ S, 1 / ((p : ℝ) ^ (1 + ε) - 1)) *
            (∑ p ∈ S,
              (pmRamanujanPrimitiveGram (p * r) r + pmRamanujanPrimitiveGram r r) /
                ((p : ℝ) ^ (1 + ε) - 1)) +
          ∑ p ∈ S, ∑ q ∈ S,
            (Real.sqrt (p : ℝ) / ((p : ℝ) ^ (1 + ε) - 1)) *
              (Real.sqrt (q : ℝ) / ((q : ℝ) ^ (1 + ε) - 1)) *
              pmRamanujanDilationProfile r hr ((p : ℝ) / q)) := by
  rw [prime_star_dilationProfile_decomposition hr S hS
    (pmRealRamanujanWeight ε r) (fun p => pmRealRamanujanWeight ε (p * r))]
  have hsum_w :
      pmRealRamanujanWeight ε r - ∑ p ∈ S, pmRealRamanujanWeight ε (p * r) =
        pmRealRamanujanWeight ε r * (1 + ∑ p ∈ S, 1 / ((p : ℝ) ^ (1 + ε) - 1)) := by
    have hw :
        (∑ p ∈ S, pmRealRamanujanWeight ε (p * r)) =
          -(pmRealRamanujanWeight ε r * ∑ p ∈ S, 1 / ((p : ℝ) ^ (1 + ε) - 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [pmRealRamanujanWeight_prime_mul hε (hS p hp).1 (hS p hp).2]
      ring
    rw [hw]
    ring
  have hcross :
      (∑ p ∈ S,
          pmRealRamanujanWeight ε (p * r) *
            (pmRamanujanPrimitiveGram (p * r) r + pmRamanujanPrimitiveGram r r)) =
        -(pmRealRamanujanWeight ε r *
          ∑ p ∈ S,
            (pmRamanujanPrimitiveGram (p * r) r + pmRamanujanPrimitiveGram r r) /
              ((p : ℝ) ^ (1 + ε) - 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [pmRealRamanujanWeight_prime_mul hε (hS p hp).1 (hS p hp).2]
    ring
  have hdil :
      (∑ p ∈ S, ∑ q ∈ S,
          (pmRealRamanujanWeight ε (p * r) * Real.sqrt (p : ℝ)) *
            (pmRealRamanujanWeight ε (q * r) * Real.sqrt (q : ℝ)) *
            pmRamanujanDilationProfile r hr ((p : ℝ) / q)) =
        pmRealRamanujanWeight ε r ^ 2 *
          ∑ p ∈ S, ∑ q ∈ S,
            (Real.sqrt (p : ℝ) / ((p : ℝ) ^ (1 + ε) - 1)) *
              (Real.sqrt (q : ℝ) / ((q : ℝ) ^ (1 + ε) - 1)) *
              pmRamanujanDilationProfile r hr ((p : ℝ) / q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [pmRealRamanujanWeight_prime_mul hε (hS p hp).1 (hS p hp).2,
      pmRealRamanujanWeight_prime_mul hε (hS q hq).1 (hS q hq).2]
    ring
  rw [hsum_w, hcross, hdil]
  ring

/-- **Pointwise Prime Denominator Bound**:
For every prime `p` and `ε > 0`, `0 < 1 / (p^{1+ε} - 1) ≤ 2 / p^{1+ε}`. -/
theorem inv_prime_rpow_sub_one_le {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    0 < 1 / ((p : ℝ) ^ (1 + ε) - 1) ∧
      1 / ((p : ℝ) ^ (1 + ε) - 1) ≤ 2 / (p : ℝ) ^ (1 + ε) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpow : (p : ℝ) ≤ (p : ℝ) ^ (1 + ε) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : (1 : ℝ) ≤ p) (by linarith : (1 : ℝ) ≤ 1 + ε)
  have hden : 0 < (p : ℝ) ^ (1 + ε) - 1 := by linarith
  have hpos : 0 < (p : ℝ) ^ (1 + ε) := by linarith
  refine ⟨div_pos one_pos hden, ?_⟩
  rw [div_le_div_iff₀ hden hpos]
  linarith

/-- **Pointwise Prime Diagonal Bound**:
For every prime `p` and `ε > 0`, `0 ≤ p / (p^{1+ε} - 1)² ≤ 4 / p^{1+2ε}`. -/
theorem prime_div_sq_prime_rpow_sub_one_le {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    0 ≤ (p : ℝ) / ((p : ℝ) ^ (1 + ε) - 1) ^ 2 ∧
      (p : ℝ) / ((p : ℝ) ^ (1 + ε) - 1) ^ 2 ≤ 4 / (p : ℝ) ^ (1 + 2 * ε) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb := inv_prime_rpow_sub_one_le hε hp
  have hsq : (1 / ((p : ℝ) ^ (1 + ε) - 1)) ^ 2 ≤ (2 / (p : ℝ) ^ (1 + ε)) ^ 2 :=
    pow_le_pow_left₀ hb.1.le hb.2 2
  have hmul :
      (p : ℝ) * (1 / ((p : ℝ) ^ (1 + ε) - 1)) ^ 2 ≤
        (p : ℝ) * (2 / (p : ℝ) ^ (1 + ε)) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hp_pos.le
  have hp_pow : ((p : ℝ) ^ (1 + ε)) ^ 2 = (p : ℝ) ^ (1 + 2 * ε) * (p : ℝ) := by
    rw [sq, ← Real.rpow_add hp_pos, ← Real.rpow_add_one hp_pos.ne']
    congr 1; ring
  have hrhs : (p : ℝ) * (2 / (p : ℝ) ^ (1 + ε)) ^ 2 = 4 / (p : ℝ) ^ (1 + 2 * ε) := by
    calc
      (p : ℝ) * (2 / (p : ℝ) ^ (1 + ε)) ^ 2 =
          4 * (p : ℝ) / ((p : ℝ) ^ (1 + ε)) ^ 2 := by ring
      _ = 4 * (p : ℝ) / ((p : ℝ) ^ (1 + 2 * ε) * (p : ℝ)) := by rw [hp_pow]
      _ = 4 / (p : ℝ) ^ (1 + 2 * ε) := by
        rw [mul_div_mul_right (4 : ℝ) ((p : ℝ) ^ (1 + 2 * ε)) hp_pos.ne']
  refine ⟨by positivity, ?_⟩
  calc
    (p : ℝ) / ((p : ℝ) ^ (1 + ε) - 1) ^ 2 =
        (p : ℝ) * (1 / ((p : ℝ) ^ (1 + ε) - 1)) ^ 2 := by
      rw [one_div_pow, mul_one_div]
    _ ≤ (p : ℝ) * (2 / (p : ℝ) ^ (1 + ε)) ^ 2 := hmul
    _ = 4 / (p : ℝ) ^ (1 + 2 * ε) := hrhs

/-- **Unconditional Prime Summability of `1 / (p^{1+ε} - 1)`**:
For every `ε > 0`, the series `∑_{p prime} 1 / (p^{1+ε} - 1)` is unconditionally summable. -/
theorem summable_prime_inv_rpow_sub_one {ε : ℝ} (hε : 0 < ε) :
    Summable (fun p : {p : ℕ // p.Prime} => 1 / (((p : ℕ) : ℝ) ^ (1 + ε) - 1)) := by
  have hmaj : Summable (fun n : ℕ => 2 / (n : ℝ) ^ (1 + ε)) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 1 + ε)).mul_left 2
  let f : ℕ → ℝ := fun n => if n.Prime then 1 / ((n : ℝ) ^ (1 + ε) - 1) else 0
  have hnat : Summable f := by
    refine Summable.of_norm_bounded hmaj fun n => ?_
    dsimp only [f]
    split_ifs with hn
    · have hb := inv_prime_rpow_sub_one_le hε hn
      rw [Real.norm_eq_abs, abs_of_pos hb.1]
      exact hb.2
    · simp only [norm_zero]
      positivity
  have hcomp : Summable (fun p : {p : ℕ // p.Prime} => f (p : ℕ)) :=
    hnat.comp_injective (@Subtype.val_injective ℕ Nat.Prime)
  refine hcomp.congr fun p => ?_
  dsimp [f]
  rw [if_pos p.property]

/-- **Unconditional Prime Summability of `p / (p^{1+ε} - 1)²`**:
For every `ε > 0`, the diagonal prime-star weight series `∑_{p prime} p / (p^{1+ε} - 1)²` is
unconditionally summable. -/
theorem summable_prime_div_sq_rpow_sub_one {ε : ℝ} (hε : 0 < ε) :
    Summable (fun p : {p : ℕ // p.Prime} =>
      ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) ^ (1 + ε) - 1) ^ 2) := by
  have hmaj : Summable (fun n : ℕ => 4 / (n : ℝ) ^ (1 + 2 * ε)) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 1 + 2 * ε)).mul_left 4
  let f : ℕ → ℝ := fun n =>
    if n.Prime then (n : ℝ) / ((n : ℝ) ^ (1 + ε) - 1) ^ 2 else 0
  have hnat : Summable f := by
    refine Summable.of_norm_bounded hmaj fun n => ?_
    dsimp only [f]
    split_ifs with hn
    · have hb := prime_div_sq_prime_rpow_sub_one_le hε hn
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2
    · simp only [norm_zero]
      positivity
  have hcomp : Summable (fun p : {p : ℕ // p.Prime} => f (p : ℕ)) :=
    hnat.comp_injective (@Subtype.val_injective ℕ Nat.Prime)
  refine hcomp.congr fun p => ?_
  dsimp [f]
  rw [if_pos p.property]

/-- Helper: if `F : {p : ℕ // p.Prime} → ℝ` converges along `atTop`, then for every `ε > 0`,
`p ↦ |F p| / (p^{1+ε} - 1)` is summable over `{p : ℕ // p.Prime}`. -/
private theorem summable_abs_div_prime_rpow_sub_one_of_tendsto {ε : ℝ} (hε : 0 < ε)
    (F : {p : ℕ // p.Prime} → ℝ) {L : ℝ} (hF : Tendsto F atTop (𝓝 L)) :
    Summable (fun p : {p : ℕ // p.Prime} => |F p| / (((p : ℕ) : ℝ) ^ (1 + ε) - 1)) := by
  have hnorm : Tendsto (fun p => |F p|) atTop (𝓝 |L|) := hF.abs
  have hev : ∀ᶠ p : {p : ℕ // p.Prime} in atTop, |F p| < |L| + 1 :=
    (tendsto_order.mp hnorm).2 (|L| + 1) (lt_add_one _)
  obtain ⟨P, _, hPrime⟩ := Nat.exists_infinite_primes 2
  letI : Nonempty {p : ℕ // p.Prime} := ⟨⟨P, hPrime⟩⟩
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.mp hev
  have hmaj : Summable (fun n : ℕ => (|L| + 1) * (2 / (n : ℝ) ^ (1 + ε))) := by
    have h1 : Summable (fun n : ℕ => 2 / (n : ℝ) ^ (1 + ε)) := by
      simpa only [mul_one_div] using
        (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 1 + ε)).mul_left 2
    exact h1.mul_left (|L| + 1)
  let G : ℕ → ℝ := fun n =>
    if hn : n.Prime then |F ⟨n, hn⟩| * (1 / ((n : ℝ) ^ (1 + ε) - 1)) else 0
  have hG : Summable G := by
    refine Summable.of_norm_bounded_eventually_nat hmaj ?_
    filter_upwards [eventually_ge_atTop (p₀ : ℕ)] with n hn_ge
    dsimp only [G]
    split_ifs with hn
    · have hb := inv_prime_rpow_sub_one_le hε hn
      have hFp : |F ⟨n, hn⟩| ≤ |L| + 1 := (hp₀ ⟨n, hn⟩ hn_ge).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hb.1.le)]
      exact mul_le_mul hFp hb.2 hb.1.le (by positivity)
    · simp only [norm_zero]
      positivity
  have hcomp : Summable (fun p : {p : ℕ // p.Prime} => G (p : ℕ)) :=
    hG.comp_injective (@Subtype.val_injective ℕ Nat.Prime)
  refine hcomp.congr fun p => ?_
  dsimp [G]
  rw [dif_pos p.property, mul_one_div]

/-- **Unconditional Prime Summability of the Cross-Depth Raw Pronic Gram Shift**:
For every `ε > 0` and `r > 1`, the cross-depth single-prime shift series
`∑_{p prime} |G(pr, r) + G(r, r)| / (p^{1+ε} - 1)` is unconditionally summable. -/
theorem summable_cross_depth_primitiveGram_prime_shift {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : 1 < r) :
    Summable (fun p : {p : ℕ // p.Prime} =>
      |pmRamanujanPrimitiveGram ((p : ℕ) * r) r + pmRamanujanPrimitiveGram r r| /
        (((p : ℕ) : ℝ) ^ (1 + ε) - 1)) := by
  have hlim := (tendsto_pmRamanujanPrimitiveGram_prime_mul hr hr).add_const
    (pmRamanujanPrimitiveGram r r)
  exact summable_abs_div_prime_rpow_sub_one_of_tendsto hε _ hlim

/-- **Unconditional Prime Summability of the Cross-Depth Energy-Centered Gram Shift**:
For every `ε > 0` and `r > 1`, the cross-depth energy-centered single-prime shift series
`∑_{p prime} |G^{ec}(pr, r) + G^{ec}(r, r)| / (p^{1+ε} - 1)` is unconditionally summable. -/
theorem summable_cross_depth_energyCenteredGram_prime_shift {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : 1 < r) :
    Summable (fun p : {p : ℕ // p.Prime} =>
      |pmRamanujanEnergyCenteredGram ((p : ℕ) * r) r + pmRamanujanEnergyCenteredGram r r| /
        (((p : ℕ) : ℝ) ^ (1 + ε) - 1)) := by
  have hlim := (tendsto_pmRamanujanEnergyCenteredGram_prime_mul hr hr).add_const
    (pmRamanujanEnergyCenteredGram r r)
  exact summable_abs_div_prime_rpow_sub_one_of_tendsto hε _ hlim

/-- **Cross-Depth Band-Residue Cancellation Summary (`pmRamanujanBandResidue`)**:
For every `ε > 0` and `d ≠ 0`, the Möbius-convolved cross-depth band residue
`pmRamanujanBandResidue ε d = moebius * pmRamanujanBandSquarefree ε d` satisfies simultaneously:
1. at every prime `p ∤ d`, depth-0 and depth-1 cancel `1` against `p^{1+ε}/(p^{1+ε}-1)` to leave
   `1 / (p^{1+ε} - 1)`,
2. at every prime power `p^k` with `k ≥ 3`, `pmRamanujanBandResidue ε d (p^k) = 0`, and
3. the absolute reciprocal residue series `∑_n |pmRamanujanBandResidue ε d n| / n` is
   unconditionally summable. -/
theorem cross_depth_bandResidue_cancellation_summary {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : d ≠ 0) :
    (∀ p : ℕ, p.Prime → ¬ p ∣ d →
      pmRamanujanBandResidue ε d p = 1 / ((p : ℝ) ^ (1 + ε) - 1)) ∧
    (∀ p k : ℕ, p.Prime → 3 ≤ k → pmRamanujanBandResidue ε d (p ^ k) = 0) ∧
    Summable (fun n : ℕ => |pmRamanujanBandResidue ε d n| / (n : ℝ)) := by
  refine ⟨fun p hp hpd => ?_, fun p k hp hk =>
    pmRamanujanBandResidue_prime_pow_eq_zero ε d hp hk,
    summable_pmRamanujanBandResidue_reciprocal hε hd⟩
  rw [pmRamanujanBandResidue_prime ε d hp]
  unfold pmPowerDampedRamanujanPrimeCorrection
  rw [if_neg hpd]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hden : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_rpow hp1 (by linarith)))
  field_simp [hden]
  ring

end GaloisForLFunctions.BezoutValuationIncidence
