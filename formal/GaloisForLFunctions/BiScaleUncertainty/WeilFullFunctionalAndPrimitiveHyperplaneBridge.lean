import GaloisForLFunctions.BiScaleUncertainty.ChebyshevWeilExplicitFormulaAndUnconditionalSynthesis
import GaloisForLFunctions.RHTower.PrimitiveHyperplaneBlindPositivity

/-!
# Pillar XXIII: Unconditional Full Weil Functional Decomposition & the Primitive-Hyperplane Bridge

This module develops **Pillar XXIII** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), establishing the **100% unconditional** bridge between
the physical-space Bi-Scale Lévy–sinh / Chebyshev–Gram apparatus (Pillars III–XXII) and the full
untruncated Weil explicit-formula functional
`RHTower.WeilOneSided.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))` and
primitive-hyperplane archimedean form `RHTower.EvenSector.poleWeightArchRe` on
`RealEvenPolarTestFn` and `RealSmoothEvenPolarTestFn`.

Every main theorem in this module is **100% unconditional**, taking only concrete test functions
`g : RealEvenPolarTestFn` (or `g : RealSmoothEvenPolarTestFn`) and real/natural parameters
`a b c : ℝ`, `N : ℕ`, with **zero** conditional hypotheses.

## Main Unconditional Results

1. **Exact `logValue`, `poleWeightArchRe`, and `weilPoleWeightFunctional` Identities on
   `RealEvenPolarTestFn` (`RealEvenPolarTestFn.logValue_eq_two_mul_autocorr_div_sqrt`,
   `RealEvenPolarTestFn.poleWeightArchRe_eq_gamma_add_biScaleLevyEnergy`,
   `RealEvenPolarTestFn.re_weilPoleWeightFunctional_eq_re_weilFullFunctional`):**
   - For every `g : RealEvenPolarTestFn` and `n : ℕ`,
     $$\operatorname{logValue}(g.1.1.1, n)
       = \frac{2\,\operatorname{autocorr}(g.\mathrm{source}, \log n)}{\sqrt{n}}
       = \frac{2\,(\operatorname{weilTest}\,g\,g\,(\log n)).\mathrm{re}}{\sqrt{n}}.$$
   - For every `g : RealEvenPolarTestFn` and every pole weight `β : ℝ`,
     $$\operatorname{poleWeightArchRe}(\beta, g.1.1)
       = \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
       = \Omega(0)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}
         + \operatorname{biScaleLevyEnergy}(g.\mathrm{source}).$$

2. **Canonical Support Scale & Exact Vanishing of the Polar and Prime Tails
   (`RealEvenPolarTestFn.supportRadius`, `RealEvenPolarTestFn.supportScale`,
   `RealEvenPolarTestFn.polar_tail_eq_zero_of_supportScale_le`,
   `RealEvenPolarTestFn.linearCombination_vonMangoldt_logVector_eq_of_supportScale_le`):**
   - Every `g : RealEvenPolarTestFn` carries an intrinsic support scale
     `g.supportScale : ℕ` such that for every `N ≥ g.supportScale`, `autocorr g.source` vanishes on
     `[cutoff N, ∞)`, the polar tail integral on `(cutoff N, ∞)` is identically zero, and the full
     finitely-supported prime-power pairing `linearCombination ℝ Λ (logVector g.1.1)` equals
     `2 * SignedPrimePolar.pairing N (autocorr g.source)`.

3. **Unconditional Full Weil Functional Identity & Chebyshev–Packet Bounds for `Λ`
   (`RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_weilArchRe_sub_two_pairing`,
   `RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing`,
   `RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound`,
   `RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound`,
   `RealSmoothEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound`):**
   - For EVERY `g : RealEvenPolarTestFn` (with **zero hypotheses**!), the full untruncated Weil
     functional of the von Mangoldt function satisfies the exact identity
     $$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,g\,g)).\mathrm{re}
       = \Omega(0)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}
         + \operatorname{biScaleLevyEnergy}(g.\mathrm{source})
         - 2\,\operatorname{SignedPrimePolar.pairing}\,(g.\mathrm{supportScale})\,(\operatorname{autocorr}\,g.\mathrm{source}),$$
     and is unconditionally approximated and bounded below by
     `weilArchRe (weilTest g g) - 2 * chebyshevWork g.toCompactlySupported a b g.supportScale`
     up to the Bi-Scale Lévy + Signed Gram Packet remainder.
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided RHTower.WeilPoleWeight
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Unconditional `logValue`, `poleWeightArchRe`, and `weilPoleWeightFunctional` Identities -/

/-- For every `g : RealEvenPolarTestFn` and `x : ℝ`, the real part of `weilTest g g` is even:
`(weilTest g g (-x)).re = (weilTest g g x).re`. -/
theorem RealEvenPolarTestFn.weilTest_neg_re_eq (g : RealEvenPolarTestFn) (x : ℝ) :
    (EF.weilTest g.1.1.1 g.1.1.1 (-x)).re = (EF.weilTest g.1.1.1 g.1.1.1 x).re := by
  rw [← g.autocorr_eq (-x), ← g.autocorr_eq x, autocorr_neg]

/-- **Unconditional `logValue` Formula on `RealEvenPolarTestFn` (`autocorr` form):**
For every `g : RealEvenPolarTestFn` and every `n : ℕ`,
$$\operatorname{logValue}(g.1.1.1, n)
  = \frac{2\,\operatorname{autocorr}(g.\mathrm{source}, \log n)}{\sqrt{n}}.$$ -/
theorem RealEvenPolarTestFn.logValue_eq_two_mul_autocorr_div_sqrt
    (g : RealEvenPolarTestFn) (n : ℕ) :
    WeilOneSided.logValue g.1.1.1 n =
      2 * autocorr g.source (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) := by
  unfold WeilOneSided.logValue
  rw [Complex.add_re, RealEvenPolarTestFn.weilTest_neg_re_eq g (Real.log (n : ℝ)),
    ← g.autocorr_eq (Real.log (n : ℝ))]
  ring

/-- **Unconditional `logValue` Formula on `RealEvenPolarTestFn` (`weilTest` form):**
For every `g : RealEvenPolarTestFn` and every `n : ℕ`,
$$\operatorname{logValue}(g.1.1.1, n)
  = \frac{2\,(\operatorname{weilTest}\,g.1.1.1\,g.1.1.1\,(\log n)).\mathrm{re}}{\sqrt{n}}.$$ -/
theorem RealEvenPolarTestFn.logValue_eq_two_mul_weilTest_re_div_sqrt
    (g : RealEvenPolarTestFn) (n : ℕ) :
    WeilOneSided.logValue g.1.1.1 n =
      2 * (EF.weilTest g.1.1.1 g.1.1.1 (Real.log (n : ℝ))).re / Real.sqrt (n : ℝ) := by
  rw [RealEvenPolarTestFn.logValue_eq_two_mul_autocorr_div_sqrt g n, g.autocorr_eq]

/-- **Unconditional `logValue`–`primeWeight` Bridge for the Von Mangoldt Function:**
For every `g : RealEvenPolarTestFn` and every `n : ℕ`,
$$\operatorname{logValue}(g.1.1.1, n) \cdot \Lambda(n)
  = 2 \cdot \bigl(\operatorname{SignedPrimePolar.primeWeight}(n) \cdot
    (\operatorname{weilTest}\,g.1.1.1\,g.1.1.1\,(\log n)).\mathrm{re}\bigr).$$ -/
theorem RealEvenPolarTestFn.logValue_mul_vonMangoldt_eq_two_mul_primeWeight
    (g : RealEvenPolarTestFn) (n : ℕ) :
    WeilOneSided.logValue g.1.1.1 n * (ArithmeticFunction.vonMangoldt n : ℝ) =
      2 * (SignedPrimePolar.primeWeight n *
        (EF.weilTest g.1.1.1 g.1.1.1 (Real.log (n : ℝ))).re) := by
  rw [RealEvenPolarTestFn.logValue_eq_two_mul_weilTest_re_div_sqrt g n]
  unfold SignedPrimePolar.primeWeight
  ring

/-- **Unconditional Pole-Weight Invariance of `poleWeightArchRe` on `RealEvenPolarTestFn`:**
Because `(weilPoleTerm (weilTest g g)).re = 0` on `WeilEvenPolarTestFn`, `poleWeightArchRe β g.1.1`
equals `weilArchRe (weilTest g g)` for every `β : ℝ`. -/
theorem RealEvenPolarTestFn.poleWeightArchRe_eq_weilArchRe
    (g : RealEvenPolarTestFn) (β : ℝ) :
    poleWeightArchRe β g.1.1 =
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) := by
  unfold poleWeightArchRe
  have hp : (weilPoleTerm (EF.weilTest g.1.1.1 g.1.1.1)).re = 0 :=
    re_weilPoleTerm_eq_zero_of_evenPolar g.1
  change WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
    (β - 1) * (weilPoleTerm (EF.weilTest g.1.1.1 g.1.1.1)).re = _
  rw [hp, mul_zero, add_zero]

/-- **Unconditional `poleWeightArchRe`–Lévy Identity on `RealEvenPolarTestFn`:**
For every `g : RealEvenPolarTestFn` and every `β : ℝ`,
$$\operatorname{poleWeightArchRe}(\beta, g.1.1)
  = \Omega(0)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(g.\mathrm{source}).$$ -/
theorem RealEvenPolarTestFn.poleWeightArchRe_eq_gamma_add_biScaleLevyEnergy
    (g : RealEvenPolarTestFn) (β : ℝ) :
    poleWeightArchRe β g.1.1 =
      EF.gammaBracket 0 * (EF.weilTest g.1.1.1 g.1.1.1 0).re +
        biScaleLevyEnergy g.source := by
  rw [RealEvenPolarTestFn.poleWeightArchRe_eq_weilArchRe g β,
    RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy g]

/-- **Unconditional Pole-Weight Invariance of `weilPoleWeightFunctional` on `RealEvenPolarTestFn`:**
For every `g : RealEvenPolarTestFn`, every pole weight `β : ℝ`, and every weight sequence
`lam : ℕ → ℝ`,
$$(\operatorname{weilPoleWeightFunctional}\,\beta\,\mathrm{lam}\,(\operatorname{weilTest}\,g\,g)).\mathrm{re}
  = (\operatorname{weilFullFunctional}\,\mathrm{lam}\,(\operatorname{weilTest}\,g\,g)).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.re_weilPoleWeightFunctional_eq_re_weilFullFunctional
    (g : RealEvenPolarTestFn) (β : ℝ) (lam : ℕ → ℝ) :
    (weilPoleWeightFunctional β lam (EF.weilTest g.1.1.1 g.1.1.1)).re =
      (weilFullFunctional lam (EF.weilTest g.1.1.1 g.1.1.1)).re := by
  rw [re_weilPoleWeightFunctional_eq_add, re_weilPoleTerm_eq_zero_of_evenPolar g.1,
    mul_zero, add_zero]

/-! ## §2. Canonical Support Radius & Support Scale on `RealEvenPolarTestFn` -/

/-- **Canonical Support Radius of `autocorr g.source`:**
For every `g : RealEvenPolarTestFn`, `autocorr g.source` has compact support, so there is a
canonical nonnegative radius outside which `autocorr g.source` vanishes identically. -/
def RealEvenPolarTestFn.supportRadius (g : RealEvenPolarTestFn) : ℝ :=
  Classical.choose
    (exists_abs_gt_eq_zero_of_hasCompactSupport
      (hasCompactSupport_autocorr g.hasCompactSupport_source))

/-- `0 ≤ RealEvenPolarTestFn.supportRadius g` for every `g : RealEvenPolarTestFn`. -/
theorem RealEvenPolarTestFn.supportRadius_nonneg (g : RealEvenPolarTestFn) :
    0 ≤ RealEvenPolarTestFn.supportRadius g :=
  (Classical.choose_spec
    (exists_abs_gt_eq_zero_of_hasCompactSupport
      (hasCompactSupport_autocorr g.hasCompactSupport_source))).1

/-- `autocorr g.source x = 0` whenever `RealEvenPolarTestFn.supportRadius g < |x|`. -/
theorem RealEvenPolarTestFn.autocorr_eq_zero_of_supportRadius_lt
    (g : RealEvenPolarTestFn) {x : ℝ} (hx : RealEvenPolarTestFn.supportRadius g < |x|) :
    autocorr g.source x = 0 :=
  (Classical.choose_spec
    (exists_abs_gt_eq_zero_of_hasCompactSupport
      (hasCompactSupport_autocorr g.hasCompactSupport_source))).2 x hx

/-- **Canonical Integer Support Scale of `g : RealEvenPolarTestFn`:**
`supportScale g := ⌈exp (supportRadius g)⌉₊`, ensuring `supportRadius g < log(N + 2) = cutoff N`
for every `N ≥ supportScale g`. -/
def RealEvenPolarTestFn.supportScale (g : RealEvenPolarTestFn) : ℕ :=
  ⌈Real.exp (RealEvenPolarTestFn.supportRadius g)⌉₊

/-- For every `g : RealEvenPolarTestFn` and every `N ≥ supportScale g`,
`supportRadius g < SignedPrimePolar.cutoff N`. -/
theorem RealEvenPolarTestFn.supportRadius_lt_cutoff_of_supportScale_le
    (g : RealEvenPolarTestFn) {N : ℕ} (hN : RealEvenPolarTestFn.supportScale g ≤ N) :
    RealEvenPolarTestFn.supportRadius g < SignedPrimePolar.cutoff N := by
  unfold SignedPrimePolar.cutoff
  have hexp_le : Real.exp (RealEvenPolarTestFn.supportRadius g) ≤ (N : ℝ) := by
    have h1 : Real.exp (RealEvenPolarTestFn.supportRadius g) ≤
        ((RealEvenPolarTestFn.supportScale g : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ((RealEvenPolarTestFn.supportScale g : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact le_trans h1 h2
  have hexp_lt : Real.exp (RealEvenPolarTestFn.supportRadius g) < ((N + 2 : ℕ) : ℝ) := by
    have hlt : (N : ℝ) < ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : N < N + 2)
    exact lt_of_le_of_lt hexp_le hlt
  have hlog := Real.log_lt_log (Real.exp_pos _) hexp_lt
  rwa [Real.log_exp] at hlog

/-- For every `g : RealEvenPolarTestFn`, `N ≥ supportScale g`, and `x ≥ cutoff N`,
`autocorr g.source x = 0`. -/
theorem RealEvenPolarTestFn.autocorr_eq_zero_of_cutoff_le
    (g : RealEvenPolarTestFn) {N : ℕ} (hN : RealEvenPolarTestFn.supportScale g ≤ N)
    {x : ℝ} (hx : SignedPrimePolar.cutoff N ≤ x) :
    autocorr g.source x = 0 := by
  refine RealEvenPolarTestFn.autocorr_eq_zero_of_supportRadius_lt g ?_
  have h1 := RealEvenPolarTestFn.supportRadius_lt_cutoff_of_supportScale_le g hN
  exact lt_of_lt_of_le (lt_of_lt_of_le h1 hx) (le_abs_self x)

/-- **Unconditional Vanishing of the Polar Tail Integral above `supportScale g`:**
For every `g : RealEvenPolarTestFn` and every `N ≥ supportScale g`,
$$\int_{Ioi\,(\operatorname{cutoff} N)} \operatorname{polarDensity}(x)\,\operatorname{autocorr}(g.\mathrm{source}, x)\,dx = 0.$$ -/
theorem RealEvenPolarTestFn.polar_tail_eq_zero_of_supportScale_le
    (g : RealEvenPolarTestFn) {N : ℕ} (hN : RealEvenPolarTestFn.supportScale g ≤ N) :
    (∫ x in Ioi (SignedPrimePolar.cutoff N),
        SignedPrimePolar.polarDensity x * autocorr g.source x) = 0 := by
  have hzero :
      EqOn (fun x => SignedPrimePolar.polarDensity x * autocorr g.source x) (fun _ => 0)
        (Ioi (SignedPrimePolar.cutoff N)) := by
    intro x hx
    dsimp only
    rw [RealEvenPolarTestFn.autocorr_eq_zero_of_cutoff_le g hN (le_of_lt hx), mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hzero]
  simp

/-- **Exact Agreement of the Prime Sum and `SignedPrimePolar.pairing` above `supportScale g`:**
For every `g : RealEvenPolarTestFn` and every `N ≥ supportScale g`,
$$\sum_{n \in \operatorname{Icc} 1 (N+2)} \operatorname{primeWeight}(n)\,(\operatorname{weilTest}\,g\,g\,(\log n)).\mathrm{re}
  = \operatorname{SignedPrimePolar.pairing} N (\operatorname{autocorr} g.\mathrm{source}).$$ -/
theorem RealEvenPolarTestFn.prime_sum_eq_pairing_of_supportScale_le
    (g : RealEvenPolarTestFn) {N : ℕ} (hN : RealEvenPolarTestFn.supportScale g ≤ N) :
    (∑ n ∈ Finset.Icc 1 (N + 2),
        SignedPrimePolar.primeWeight n * (EF.weilTest g.1.1.1 g.1.1.1 (Real.log (n : ℝ))).re) =
      SignedPrimePolar.pairing N (autocorr g.source) := by
  have h1 := RealEvenPolarTestFn.prime_sum_add_polar_tail_eq_pairing g N
  rw [RealEvenPolarTestFn.polar_tail_eq_zero_of_supportScale_le g hN, add_zero] at h1
  exact h1

/-! ## §3. Exact Unconditional Decomposition of `weilFullFunctional Λ` -/

/-- For every `g : RealEvenPolarTestFn`, `N ≥ supportScale g`, and `n > N + 2`,
`logValue g.1.1.1 n = 0`. -/
theorem RealEvenPolarTestFn.logValue_eq_zero_of_supportScale_le
    (g : RealEvenPolarTestFn) {N n : ℕ} (hN : RealEvenPolarTestFn.supportScale g ≤ N)
    (hn : N + 2 < n) :
    WeilOneSided.logValue g.1.1.1 n = 0 := by
  rw [RealEvenPolarTestFn.logValue_eq_two_mul_autocorr_div_sqrt g n]
  have hcut : SignedPrimePolar.cutoff N ≤ Real.log (n : ℝ) := by
    unfold SignedPrimePolar.cutoff
    refine Real.log_le_log (by positivity) ?_
    exact_mod_cast (by omega : N + 2 ≤ n)
  rw [RealEvenPolarTestFn.autocorr_eq_zero_of_cutoff_le g hN hcut, mul_zero, zero_div]

/-- **Exact Identity for the Finitely-Supported Von Mangoldt Pairing on `logVector g.1.1`:**
For every `g : RealEvenPolarTestFn` and every `N ≥ supportScale g`,
$$\operatorname{linearCombination}\,\mathbb{R}\,(\mathrm{fun}\,j : \operatorname{LogIndex} \Rightarrow \Lambda(j))\,(\operatorname{logVector}\,g.1.1)
  = 2\,\operatorname{SignedPrimePolar.pairing} N (\operatorname{autocorr} g.\mathrm{source}).$$ -/
theorem RealEvenPolarTestFn.linearCombination_vonMangoldt_logVector_eq_of_supportScale_le
    (g : RealEvenPolarTestFn) {N : ℕ} (hN : RealEvenPolarTestFn.supportScale g ≤ N) :
    linearCombination ℝ
        (fun j : WeilOneSided.LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (WeilOneSided.logVector g.1.1) =
      2 * SignedPrimePolar.pairing N (autocorr g.source) := by
  classical
  have hlc :
      linearCombination ℝ
          (fun j : WeilOneSided.LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
          (WeilOneSided.logVector g.1.1) =
        ∑ j ∈ (Finset.Icc 1 (N + 2)).subtype (fun n => 2 ≤ n),
          WeilOneSided.logValue g.1.1.1 j * (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ) := by
    rw [linearCombination_apply]
    refine (Finsupp.sum_of_support_subset (WeilOneSided.logVector g.1.1) (fun j hj => ?_)
      (fun j a => a • (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
      fun _ _ => zero_smul _ _).trans
      (Finset.sum_congr rfl fun j _ => by rw [WeilOneSided.logVector_apply, smul_eq_mul])
    rw [Finsupp.mem_support_iff, WeilOneSided.logVector_apply] at hj
    rw [Finset.mem_subtype, Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    by_contra hgt
    exact hj (RealEvenPolarTestFn.logValue_eq_zero_of_supportScale_le g hN (by omega))
  rw [hlc,
    Finset.sum_subtype_eq_sum_filter
      (fun n => WeilOneSided.logValue g.1.1.1 n * (ArithmeticFunction.vonMangoldt n : ℝ)),
    Finset.sum_filter]
  have hfilter_eq :
      (∑ n ∈ Finset.Icc 1 (N + 2),
          if 2 ≤ n then
            WeilOneSided.logValue g.1.1.1 n * (ArithmeticFunction.vonMangoldt n : ℝ)
          else 0) =
        2 * ∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n *
            (EF.weilTest g.1.1.1 g.1.1.1 (Real.log (n : ℝ))).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    split_ifs with hn2
    · exact RealEvenPolarTestFn.logValue_mul_vonMangoldt_eq_two_mul_primeWeight g n
    · have hn_eq1 : n = 1 := by omega
      subst hn_eq1
      unfold SignedPrimePolar.primeWeight
      simp
  rw [hfilter_eq, RealEvenPolarTestFn.prime_sum_eq_pairing_of_supportScale_le g hN]

/-- **Exact Decomposition of `weilFullFunctional Λ` for any `N ≥ supportScale g`:**
For every `g : RealEvenPolarTestFn` and every `N ≥ supportScale g`,
$$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,g\,g)).\mathrm{re}
  = \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
    - 2\,\operatorname{SignedPrimePolar.pairing} N (\operatorname{autocorr} g.\mathrm{source}).$$ -/
theorem RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_of_supportScale_le
    (g : RealEvenPolarTestFn) {N : ℕ} (hN : RealEvenPolarTestFn.supportScale g ≤ N) :
    (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1 g.1.1.1)).re =
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) -
        2 * SignedPrimePolar.pairing N (autocorr g.source) := by
  rw [WeilOneSided.re_weilFullFunctional_eq
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g.1.1,
    RealEvenPolarTestFn.linearCombination_vonMangoldt_logVector_eq_of_supportScale_le g hN]

/-- **Unconditional Full Weil Functional Identity on `RealEvenPolarTestFn` (`weilArchRe` form):**
For EVERY `g : RealEvenPolarTestFn` (with **zero hypotheses**!),
$$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,g\,g)).\mathrm{re}
  = \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
    - 2\,\operatorname{SignedPrimePolar.pairing}\,(g.\mathrm{supportScale})\,(\operatorname{autocorr}\,g.\mathrm{source}).$$ -/
theorem RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_weilArchRe_sub_two_pairing
    (g : RealEvenPolarTestFn) :
    (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1 g.1.1.1)).re =
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) -
        2 * SignedPrimePolar.pairing (RealEvenPolarTestFn.supportScale g) (autocorr g.source) :=
  RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_of_supportScale_le g le_rfl

/-- **Unconditional Full Weil Functional Identity on `RealEvenPolarTestFn` (`biScaleLevyEnergy` form):**
For EVERY `g : RealEvenPolarTestFn` (with **zero hypotheses**!),
$$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,g\,g)).\mathrm{re}
  = \Omega(0)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(g.\mathrm{source})
    - 2\,\operatorname{SignedPrimePolar.pairing}\,(g.\mathrm{supportScale})\,(\operatorname{autocorr}\,g.\mathrm{source}).$$ -/
theorem RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing
    (g : RealEvenPolarTestFn) :
    (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1 g.1.1.1)).re =
      EF.gammaBracket 0 * (EF.weilTest g.1.1.1 g.1.1.1 0).re +
        biScaleLevyEnergy g.source -
        2 * SignedPrimePolar.pairing (RealEvenPolarTestFn.supportScale g) (autocorr g.source) := by
  rw [RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_weilArchRe_sub_two_pairing g,
    RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy g]

/-! ## §4. Unconditional Chebyshev–Packet & All-Scale Bounds for `weilFullFunctional Λ` -/

/-- **Unconditional Full Weil Functional Chebyshev–Packet Approximation Theorem
(`RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound`):**
For EVERY `g : RealEvenPolarTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses** on `g`, `a`,
`b`, or `c`!), the full untruncated Weil explicit-formula functional of `Λ` satisfies:
$$\Bigl|(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,g\,g)).\mathrm{re}
  - \bigl(\operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
    - 2\,\operatorname{chebyshevWork}(g.\mathrm{toCompactlySupported}, a, b, g.\mathrm{supportScale})\bigr)\Bigr|$$
$$\le\; 2 e^c\,\bigl(\operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  + |\Omega(0)|\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}\bigr)
  + \frac{\operatorname{packetEnergy}(g.\mathrm{toCompactlySupported}, g.\mathrm{supportScale})}{e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy.$$ -/
theorem RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound
    (g : RealEvenPolarTestFn) (a b c : ℝ) :
    |(weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest g.1.1.1 g.1.1.1)).re -
        (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) -
          2 * SignedPrimePolar.chebyshevWork
            (RealEvenPolarTestFn.toCompactlySupported g) a b
            (RealEvenPolarTestFn.supportScale g))| ≤
      2 * Real.exp c *
          (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
            |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re) +
        SignedPrimePolar.packetEnergy
            (RealEvenPolarTestFn.toCompactlySupported g)
            (RealEvenPolarTestFn.supportScale g) /
            (Real.exp c * Real.exp b ^ 2) *
          ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
  set N := RealEvenPolarTestFn.supportScale g
  rw [RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_weilArchRe_sub_two_pairing g]
  have hdiff :
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) -
          2 * SignedPrimePolar.pairing N (autocorr g.source) -
          (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) -
            2 * SignedPrimePolar.chebyshevWork
              (RealEvenPolarTestFn.toCompactlySupported g) a b N) =
        -(2 * (SignedPrimePolar.pairing N (autocorr g.source) -
          SignedPrimePolar.chebyshevWork
            (RealEvenPolarTestFn.toCompactlySupported g) a b N)) := by
    ring
  rw [hdiff, abs_neg, abs_mul, abs_of_pos two_pos]
  have hpack := RealEvenPolarTestFn.unconditional_chebyshev_packet_weil_bound g a b c N
  rw [RealEvenPolarTestFn.prime_sum_add_polar_tail_eq_pairing g N] at hpack
  have h2 := mul_le_mul_of_nonneg_left hpack zero_le_two
  have hrhs_eq :
      2 * (Real.exp c *
            (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
              |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re) +
          SignedPrimePolar.packetEnergy (RealEvenPolarTestFn.toCompactlySupported g) N /
              (2 * Real.exp c * Real.exp b ^ 2) *
            ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) =
        2 * Real.exp c *
            (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
              |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re) +
          SignedPrimePolar.packetEnergy (RealEvenPolarTestFn.toCompactlySupported g) N /
              (Real.exp c * Real.exp b ^ 2) *
            ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
    have hec : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
    have heb : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
    field_simp [hec, heb]
  linarith only [h2, hrhs_eq]

/-- **Unconditional Full Weil Functional Lower Bound via Chebyshev Work & Signed Gram Packet
(`RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound`):**
For EVERY `g : RealEvenPolarTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!),
$$(1 - 2 e^c)\,\operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  - 2 e^c\,|\Omega(0)|\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}
  - 2\,\operatorname{chebyshevWork}(g.\mathrm{toCompactlySupported}, a, b, g.\mathrm{supportScale})
  - \frac{\operatorname{packetEnergy}(g.\mathrm{toCompactlySupported}, g.\mathrm{supportScale})}{e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy$$
$$\le\; (\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,g\,g)).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound
    (g : RealEvenPolarTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) -
        2 * Real.exp c * |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork
          (RealEvenPolarTestFn.toCompactlySupported g) a b
          (RealEvenPolarTestFn.supportScale g) -
        SignedPrimePolar.packetEnergy
            (RealEvenPolarTestFn.toCompactlySupported g)
            (RealEvenPolarTestFn.supportScale g) /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1 g.1.1.1)).re := by
  have habs :=
    RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound g a b c
  have hlow := neg_le_of_abs_le habs
  linarith only [hlow]

/-- **Unconditional Full Weil Functional Chebyshev–Packet Bound on `RealSmoothEvenPolarTestFn`:** -/
theorem RealSmoothEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound
    (g : RealSmoothEvenPolarTestFn) (a b c : ℝ) :
    |(weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest g.1.1.1.1 g.1.1.1.1)).re -
        (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1.1 g.1.1.1.1) -
          2 * SignedPrimePolar.chebyshevWork
            (RealEvenPolarTestFn.toCompactlySupported g.toRealEvenPolar) a b
            (RealEvenPolarTestFn.supportScale g.toRealEvenPolar))| ≤
      2 * Real.exp c *
          (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1.1 g.1.1.1.1) +
            |EF.gammaBracket 0| * (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re) +
        SignedPrimePolar.packetEnergy
            (RealEvenPolarTestFn.toCompactlySupported g.toRealEvenPolar)
            (RealEvenPolarTestFn.supportScale g.toRealEvenPolar) /
            (Real.exp c * Real.exp b ^ 2) *
          ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y :=
  RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound
    g.toRealEvenPolar a b c

/-- **Unconditional Full Weil Functional Lower Bound on `RealSmoothEvenPolarTestFn`:** -/
theorem RealSmoothEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound
    (g : RealSmoothEvenPolarTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * WeilOneSided.weilArchRe (EF.weilTest g.1.1.1.1 g.1.1.1.1) -
        2 * Real.exp c * |EF.gammaBracket 0| * (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork
          (RealEvenPolarTestFn.toCompactlySupported g.toRealEvenPolar) a b
          (RealEvenPolarTestFn.supportScale g.toRealEvenPolar) -
        SignedPrimePolar.packetEnergy
            (RealEvenPolarTestFn.toCompactlySupported g.toRealEvenPolar)
            (RealEvenPolarTestFn.supportScale g.toRealEvenPolar) /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1.1 g.1.1.1.1)).re :=
  RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound
    g.toRealEvenPolar a b c

/-- **Unconditional All-Scale Coercive Lower Bound for the Full Weil Functional `weilFullFunctional Λ`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `N : ℕ` (with **zero hypotheses**!),
$$\bigl(\Omega(0) + \mathcal{C}_{\Lambda, \mathrm{all}}(N)\bigr)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}$$
$$\le\; (\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,g\,g)).\mathrm{re}
  + 2\,\operatorname{SignedPrimePolar.pairing}\,(g.\mathrm{supportScale})\,(\operatorname{autocorr}\,g.\mathrm{source})$$
$$+\; \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,w_\Lambda(k+2)\,
  (\operatorname{weilTest}\,g\,g\,(\log(k+2))).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_all_scale_lower_bound
    (g : RealEvenPolarTestFn) (N : ℕ) :
    (EF.gammaBracket 0 + allScaleVonMangoldtCoerciveConstant N) *
        (EF.weilTest g.1.1.1 g.1.1.1 0).re ≤
      (weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest g.1.1.1 g.1.1.1)).re +
        2 * SignedPrimePolar.pairing (RealEvenPolarTestFn.supportScale g) (autocorr g.source) +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            (EF.weilTest g.1.1.1 g.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re := by
  have h1 := RealEvenPolarTestFn.unconditional_vonMangoldt_all_scale_signed_weil_lower_bound g N
  have h2 := RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_weilArchRe_sub_two_pairing g
  linarith only [h1, h2]

end

end GaloisForLFunctions.BiScaleUncertainty
