import GaloisForLFunctions.BiScaleUncertainty.IntegratedMultiNodeDyadicCosetWeilCoercivity

/-!
# Pillar XXVII: Universal All-Parity Full Weil Functional Decomposition & Chebyshev–Packet Synthesis

This module develops **Pillar XXVII** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), proving the **Universal Pole-to-Chebyshev Absorption
Theorem** across the **entire real Weil test space `RealWeilTestFn`** (including `RealOddTestFn`,
`RealEvenPolarTestFn`, and `RealHyperplaneGenerator`) with **zero** parity or polar-vanishing
hypotheses.

## The Structural Discovery: Universal Pole Absorption at $\beta = 1$

In Weil's explicit formula for $\zeta(s)$, why does the true pole weight $\beta = 1$ of $\zeta(s)$
play a distinguished role across all parities?

For **any** real test $f : \operatorname{RealWeilTestFn}$ (even, odd, or arbitrary, without
assuming $\hat{f}(\pm i/2) = 0$):
1. By `weilArchRe_eq_exactForm`, the archimedean functional splits as
   $$\operatorname{weilArchRe}(k_f)
     = \Omega(0)\,h_f(0) + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
       + 4 \int_0^\infty h_f(x)\,\cosh(x/2)\,dx,$$
   where $4 \int_0^\infty h_f(x)\,\cosh(x/2)\,dx = (\operatorname{weilPoleTerm}(k_f)).\mathrm{re}
   = 2 \int_0^\infty \operatorname{polarDensity}(x)\,h_f(x)\,dx$.
2. For any $N \ge f.\mathrm{supportScale}$, $\operatorname{autocorr}(f.\mathrm{source}, x) = 0$ on
   $[\operatorname{cutoff} N, \infty)$, so the continuum polar integral in
   $-2\,\operatorname{SignedPrimePolar.pairing}(N, h_f)$ is
   $$2 \int_0^{\operatorname{cutoff} N} \operatorname{polarDensity}(x)\,h_f(x)\,dx
     = 4 \int_0^\infty h_f(x)\,\cosh(x/2)\,dx
     = (\operatorname{weilPoleTerm}(k_f)).\mathrm{re}.$$
3. Therefore, when the prime sum $-\sum_{n \ge 2} \frac{\Lambda(n)}{\sqrt{n}}\,2 h_f(\log n)$ is
   combined with the pole term $+(\operatorname{weilPoleTerm}(k_f)).\mathrm{re}$ of $\zeta(s)$ at
   pole weight $\beta = 1$, the pole term is **identically absorbed** as the continuum polar measure
   of $\operatorname{SignedPrimePolar.pairing}$:
   $$\operatorname{linearCombination}\,\mathbb{R}\,\Lambda\,(\operatorname{logVector}\,f.1)
     - (\operatorname{weilPoleTerm}(k_f)).\mathrm{re}
     = 2\,\operatorname{SignedPrimePolar.pairing}(N, \operatorname{autocorr} f.\mathrm{source}).$$
4. Consequently, for **every** $f : \operatorname{RealWeilTestFn}$ (and in particular for every odd
   test $f : \operatorname{RealOddTestFn}$ and every primitive-hyperplane generator
   $x : \operatorname{RealHyperplaneGenerator}$), the **full untruncated Weil functional**
   `weilFullFunctional Λ` (at the true pole weight $\beta = 1$!) satisfies the exact pole-free
   identity:
   $$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}
     = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
       + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
       - 2\,\operatorname{SignedPrimePolar.pairing}\,(f.\mathrm{supportScale})\,(\operatorname{autocorr}\,f.\mathrm{source})$$
   $$= \operatorname{poleWeightArchRe}(0, f.1)
     - 2\,\operatorname{SignedPrimePolar.pairing}\,(f.\mathrm{supportScale})\,(\operatorname{autocorr}\,f.\mathrm{source}).$$
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided RHTower.WeilPoleWeight
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Universal Half-Line Polar Integral & Support Scale on `RealWeilTestFn` -/

/-- **Universal Half-Line Cosh Moment Identity for Real $C^2_c(\mathbb{R})$ Sources:**
For EVERY `f ∈ C²_c(ℝ)` (with zero parity or polar assumptions),
$$4 \int_{Ioi\,0} \operatorname{autocorr}(f, x)\,\cosh(x/2)\,dx
  = (\operatorname{weilPoleTerm}(\operatorname{weilTest}\,F\,F)).\mathrm{re}.$$ -/
theorem four_mul_integral_Ioi_autocorr_mul_cosh_eq_re_weilPoleTerm
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    4 * (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) =
      (weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hcs : HasCompactSupport (autocorr f) := hasCompactSupport_autocorr hfc
  have hJ : IntegrableOn
      (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x) (Ioi 0) :=
    integrableOn_biScaleLevyIntegrand hf hfc
  have hP : IntegrableOn (fun x => 4 * autocorr f x * Real.cosh (x / 2)) (Ioi 0) := by
    refine Integrable.integrableOn ?_
    refine ((continuous_const.mul hc).mul (by fun_prop)).integrable_of_hasCompactSupport ?_
    exact (hcs.mul_left (f := fun _ => (4 : ℝ))).mul_right
  have hexact := weilArchRe_eq_exactForm hf hfc
  have hlev := weilArchRe_ofReal_eq_pole_add_gamma_add_biScaleLevyEnergy hf hfc
  have hsplit : (∫ x in Ioi 0, ((autocorr f 0 - autocorr f x) *
      (Real.exp (x / 2) / Real.sinh x) + 4 * autocorr f x * Real.cosh (x / 2))) =
      biScaleLevyEnergy f + 4 * ∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2) := by
    unfold archLevySinhWeight at hJ
    unfold biScaleLevyEnergy archLevySinhWeight
    rw [integral_add hJ hP]
    congr 1
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hsplit] at hexact
  linarith only [hexact, hlev]

/-- **Universal Half-Line `polarDensity` Integral Identity for Real $C^2_c(\mathbb{R})$ Sources:**
For EVERY `f ∈ C²_c(ℝ)`,
$$2 \int_{Ioi\,0} \operatorname{SignedPrimePolar.polarDensity}(x)\,\operatorname{autocorr}(f, x)\,dx
  = (\operatorname{weilPoleTerm}(\operatorname{weilTest}\,F\,F)).\mathrm{re}.$$ -/
theorem two_mul_integral_Ioi_polarDensity_autocorr_eq_re_weilPoleTerm
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    2 * (∫ x in Ioi 0, SignedPrimePolar.polarDensity x * autocorr f x) =
      (weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  have heq : (fun x => SignedPrimePolar.polarDensity x * autocorr f x) =
      fun x => 2 * (autocorr f x * Real.cosh (x / 2)) := by
    funext x
    unfold SignedPrimePolar.polarDensity
    ring
  rw [heq, integral_const_mul, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num]
  exact four_mul_integral_Ioi_autocorr_mul_cosh_eq_re_weilPoleTerm hf hfc

namespace RealWeilTestFn

/-- **Canonical Support Radius of `autocorr f.source` for `f : RealWeilTestFn`:** -/
def supportRadius (f : RealWeilTestFn) : ℝ :=
  Classical.choose
    (exists_abs_gt_eq_zero_of_hasCompactSupport
      (hasCompactSupport_autocorr f.hasCompactSupport_source))

theorem supportRadius_nonneg (f : RealWeilTestFn) :
    0 ≤ f.supportRadius :=
  (Classical.choose_spec
    (exists_abs_gt_eq_zero_of_hasCompactSupport
      (hasCompactSupport_autocorr f.hasCompactSupport_source))).1

theorem autocorr_eq_zero_of_supportRadius_lt
    (f : RealWeilTestFn) {x : ℝ} (hx : f.supportRadius < |x|) :
    autocorr f.source x = 0 :=
  (Classical.choose_spec
    (exists_abs_gt_eq_zero_of_hasCompactSupport
      (hasCompactSupport_autocorr f.hasCompactSupport_source))).2 x hx

/-- **Canonical Integer Support Scale of `f : RealWeilTestFn`:**
`supportScale f := ⌈exp (supportRadius f)⌉₊`. -/
def supportScale (f : RealWeilTestFn) : ℕ :=
  ⌈Real.exp f.supportRadius⌉₊

theorem supportRadius_lt_cutoff_of_supportScale_le
    (f : RealWeilTestFn) {N : ℕ} (hN : f.supportScale ≤ N) :
    f.supportRadius < SignedPrimePolar.cutoff N := by
  unfold SignedPrimePolar.cutoff
  have hexp_le : Real.exp f.supportRadius ≤ (N : ℝ) := by
    have h1 : Real.exp f.supportRadius ≤ ((f.supportScale : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((f.supportScale : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact le_trans h1 h2
  have hexp_lt : Real.exp f.supportRadius < ((N + 2 : ℕ) : ℝ) := by
    have hlt : (N : ℝ) < ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : N < N + 2)
    exact lt_of_le_of_lt hexp_le hlt
  have hlog := Real.log_lt_log (Real.exp_pos _) hexp_lt
  rwa [Real.log_exp] at hlog

theorem autocorr_eq_zero_of_cutoff_le
    (f : RealWeilTestFn) {N : ℕ} (hN : f.supportScale ≤ N)
    {x : ℝ} (hx : SignedPrimePolar.cutoff N ≤ x) :
    autocorr f.source x = 0 := by
  refine f.autocorr_eq_zero_of_supportRadius_lt ?_
  have h1 := f.supportRadius_lt_cutoff_of_supportScale_le hN
  exact lt_of_lt_of_le (lt_of_lt_of_le h1 hx) (le_abs_self x)

theorem polar_tail_eq_zero_of_supportScale_le
    (f : RealWeilTestFn) {N : ℕ} (hN : f.supportScale ≤ N) :
    (∫ x in Ioi (SignedPrimePolar.cutoff N),
        SignedPrimePolar.polarDensity x * autocorr f.source x) = 0 := by
  have hzero :
      EqOn (fun x => SignedPrimePolar.polarDensity x * autocorr f.source x) (fun _ => 0)
        (Ioi (SignedPrimePolar.cutoff N)) := by
    intro x hx
    dsimp only
    rw [f.autocorr_eq_zero_of_cutoff_le hN (le_of_lt hx), mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hzero]
  simp

/-! ## §2. Universal Pole-to-Chebyshev Absorption on `RealWeilTestFn` -/

/-- **Universal Truncated Prime-Sum plus Polar-Tail Identity on `RealWeilTestFn`:**
For EVERY `f : RealWeilTestFn` and EVERY `N : ℕ` (with zero parity or polar hypotheses!),
$$2\left(\sum_{n \in \operatorname{Icc} 1 (N+2)} \operatorname{primeWeight}(n)\,(\operatorname{weilTest}\,f\,f\,(\log n)).\mathrm{re}
  + \int_{Ioi\,(\operatorname{cutoff} N)} \operatorname{polarDensity}(x)\,\operatorname{autocorr}(f.\mathrm{source}, x)\,dx\right)$$
$$= 2\,\operatorname{SignedPrimePolar.pairing} N (\operatorname{autocorr} f.\mathrm{source})
  + (\operatorname{weilPoleTerm}(\operatorname{weilTest}\,f\,f)).\mathrm{re}.$$ -/
theorem two_mul_prime_sum_add_polar_tail_eq_two_pairing_add_pole
    (f : RealWeilTestFn) (N : ℕ) :
    2 * ((∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n * (EF.weilTest f.1.1 f.1.1 (Real.log (n : ℝ))).re) +
        ∫ x in Ioi (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr f.source x) =
      2 * SignedPrimePolar.pairing N (autocorr f.source) +
        (weilPoleTerm (EF.weilTest f.1.1 f.1.1)).re := by
  have hf := f.contDiff_source
  have hfc := f.hasCompactSupport_source
  have hc : Continuous (autocorr f.source) := continuous_autocorr hf hfc
  have hcs : HasCompactSupport (autocorr f.source) := hasCompactSupport_autocorr hfc
  have hint_all : Integrable (fun x => SignedPrimePolar.polarDensity x * autocorr f.source x) := by
    unfold SignedPrimePolar.polarDensity
    exact ((continuous_const.mul (by fun_prop)).mul hc).integrable_of_hasCompactSupport
      (hcs.mul_left)
  have hL_nn : 0 ≤ SignedPrimePolar.cutoff N := SignedPrimePolar.cutoff_nonneg N
  have hdisj : Disjoint (Ioc 0 (SignedPrimePolar.cutoff N)) (Ioi (SignedPrimePolar.cutoff N)) :=
    Ioc_disjoint_Ioi le_rfl
  have hunion : Ioc 0 (SignedPrimePolar.cutoff N) ∪ Ioi (SignedPrimePolar.cutoff N) = Ioi 0 :=
    Ioc_union_Ioi_eq_Ioi hL_nn
  have hsplit :
      (∫ x in Icc 0 (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr f.source x) +
        (∫ x in Ioi (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr f.source x) =
        ∫ x in Ioi 0, SignedPrimePolar.polarDensity x * autocorr f.source x := by
    rw [integral_Icc_eq_integral_Ioc, ← setIntegral_union hdisj measurableSet_Ioi
      hint_all.integrableOn hint_all.integrableOn, hunion]
  have hpole := two_mul_integral_Ioi_polarDensity_autocorr_eq_re_weilPoleTerm hf hfc
  rw [f.source_eq] at hpole
  have hsum_eq :
      (∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n * (EF.weilTest f.1.1 f.1.1 (Real.log (n : ℝ))).re) =
        ∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n * autocorr f.source (Real.log (n : ℝ)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [f.autocorr_eq]
  rw [hsum_eq]
  unfold SignedPrimePolar.pairing
  linarith only [hsplit, hpole]

/-- For every `f : RealWeilTestFn` and `n : ℕ`,
`logValue f.1.1 n * Λ(n) = 2 * (primeWeight n * (weilTest f f (log n)).re)`. -/
theorem logValue_mul_vonMangoldt_eq_two_mul_primeWeight
    (f : RealWeilTestFn) (n : ℕ) :
    WeilOneSided.logValue f.1.1 n * (ArithmeticFunction.vonMangoldt n : ℝ) =
      2 * (SignedPrimePolar.primeWeight n *
        (EF.weilTest f.1.1 f.1.1 (Real.log (n : ℝ))).re) := by
  rw [f.logValue_eq_two_mul_weilTest_re_div_sqrt n]
  unfold SignedPrimePolar.primeWeight
  ring

theorem logValue_eq_zero_of_supportScale_le
    (f : RealWeilTestFn) {N n : ℕ} (hN : f.supportScale ≤ N) (hn : N + 2 < n) :
    WeilOneSided.logValue f.1.1 n = 0 := by
  rw [f.logValue_eq_two_mul_weilTest_re_div_sqrt n, ← f.autocorr_eq]
  have hcut : SignedPrimePolar.cutoff N ≤ Real.log (n : ℝ) := by
    unfold SignedPrimePolar.cutoff
    refine Real.log_le_log (by positivity) ?_
    exact_mod_cast (by omega : N + 2 ≤ n)
  rw [f.autocorr_eq_zero_of_cutoff_le hN hcut, mul_zero, zero_div]

/-- **Universal Pole-to-Chebyshev Identity for `linearCombination ℝ Λ (logVector f.1)`:**
For EVERY `f : RealWeilTestFn` and EVERY `N ≥ f.supportScale` (with **zero** parity or polar
hypotheses!),
$$\operatorname{linearCombination}\,\mathbb{R}\,(\mathrm{fun}\,j : \operatorname{LogIndex} \Rightarrow \Lambda(j))\,(\operatorname{logVector}\,f.1)$$
$$= 2\,\operatorname{SignedPrimePolar.pairing} N (\operatorname{autocorr} f.\mathrm{source})
  + (\operatorname{weilPoleTerm}(\operatorname{weilTest}\,f\,f)).\mathrm{re}.$$ -/
theorem linearCombination_vonMangoldt_logVector_eq_two_pairing_add_pole
    (f : RealWeilTestFn) {N : ℕ} (hN : f.supportScale ≤ N) :
    linearCombination ℝ
        (fun j : WeilOneSided.LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (WeilOneSided.logVector f.1) =
      2 * SignedPrimePolar.pairing N (autocorr f.source) +
        (weilPoleTerm (EF.weilTest f.1.1 f.1.1)).re := by
  classical
  have hlc :
      linearCombination ℝ
          (fun j : WeilOneSided.LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
          (WeilOneSided.logVector f.1) =
        ∑ j ∈ (Finset.Icc 1 (N + 2)).subtype (fun n => 2 ≤ n),
          WeilOneSided.logValue f.1.1 j * (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ) := by
    rw [linearCombination_apply]
    refine (Finsupp.sum_of_support_subset (WeilOneSided.logVector f.1) (fun j hj => ?_)
      (fun j a => a • (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
      fun _ _ => zero_smul _ _).trans
      (Finset.sum_congr rfl fun j _ => by rw [WeilOneSided.logVector_apply, smul_eq_mul])
    rw [Finsupp.mem_support_iff, WeilOneSided.logVector_apply] at hj
    rw [Finset.mem_subtype, Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    by_contra hgt
    exact hj (f.logValue_eq_zero_of_supportScale_le hN (by omega))
  rw [hlc,
    Finset.sum_subtype_eq_sum_filter
      (fun n => WeilOneSided.logValue f.1.1 n * (ArithmeticFunction.vonMangoldt n : ℝ)),
    Finset.sum_filter]
  have hfilter_eq :
      (∑ n ∈ Finset.Icc 1 (N + 2),
          if 2 ≤ n then
            WeilOneSided.logValue f.1.1 n * (ArithmeticFunction.vonMangoldt n : ℝ)
          else 0) =
        2 * ∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n *
            (EF.weilTest f.1.1 f.1.1 (Real.log (n : ℝ))).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    split_ifs with hn2
    · exact f.logValue_mul_vonMangoldt_eq_two_mul_primeWeight n
    · have hn_eq1 : n = 1 := by omega
      subst hn_eq1
      unfold SignedPrimePolar.primeWeight
      simp
  rw [hfilter_eq]
  have hbridge := f.two_mul_prime_sum_add_polar_tail_eq_two_pairing_add_pole N
  rw [f.polar_tail_eq_zero_of_supportScale_le hN, add_zero] at hbridge
  exact hbridge

/-- **Universal Full Weil Functional Decomposition on `RealWeilTestFn` (for any `N ≥ f.supportScale`):**
For EVERY `f : RealWeilTestFn` and EVERY `N ≥ f.supportScale` (with **zero** parity or polar
hypotheses!), the pole term in `weilArchRe` cancels identically against the continuum polar term in
`linearCombination ℝ Λ (logVector f.1)`:
$$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
    - 2\,\operatorname{SignedPrimePolar.pairing} N (\operatorname{autocorr} f.\mathrm{source})$$
$$= \operatorname{poleWeightArchRe}(0, f.1)
  - 2\,\operatorname{SignedPrimePolar.pairing} N (\operatorname{autocorr} f.\mathrm{source}).$$ -/
theorem re_weilFullFunctional_vonMangoldt_eq_of_supportScale_le
    (f : RealWeilTestFn) {N : ℕ} (hN : f.supportScale ≤ N) :
    (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re =
      EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re +
        biScaleLevyEnergy f.source -
        2 * SignedPrimePolar.pairing N (autocorr f.source) := by
  rw [WeilOneSided.re_weilFullFunctional_eq
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f.1,
    f.linearCombination_vonMangoldt_logVector_eq_two_pairing_add_pole hN]
  have harch := weilArchRe_ofReal_eq_pole_add_gamma_add_biScaleLevyEnergy
    f.contDiff_source f.hasCompactSupport_source
  rw [f.source_eq, f.autocorr_eq 0] at harch
  linarith only [harch]

/-- **Universal Full Weil Functional Identity on `RealWeilTestFn` (`biScaleLevyEnergy` form):**
For EVERY `f : RealWeilTestFn` (even, odd, or arbitrary, with **zero hypotheses**!):
$$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
    - 2\,\operatorname{SignedPrimePolar.pairing}\,(f.\mathrm{supportScale})\,(\operatorname{autocorr}\,f.\mathrm{source}).$$ -/
theorem re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing
    (f : RealWeilTestFn) :
    (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re =
      EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re +
        biScaleLevyEnergy f.source -
        2 * SignedPrimePolar.pairing f.supportScale (autocorr f.source) :=
  f.re_weilFullFunctional_vonMangoldt_eq_of_supportScale_le le_rfl

/-- **Universal Full Weil Functional Identity on `RealWeilTestFn` (`poleWeightArchRe 0` form):**
For EVERY `f : RealWeilTestFn` (with **zero hypotheses**!):
$$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}
  = \operatorname{poleWeightArchRe}(0, f.1)
    - 2\,\operatorname{SignedPrimePolar.pairing}\,(f.\mathrm{supportScale})\,(\operatorname{autocorr}\,f.\mathrm{source}).$$ -/
theorem re_weilFullFunctional_vonMangoldt_eq_poleWeightArchRe_zero_sub_two_pairing
    (f : RealWeilTestFn) :
    (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re =
      poleWeightArchRe 0 f.1 -
        2 * SignedPrimePolar.pairing f.supportScale (autocorr f.source) := by
  rw [f.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing,
    f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy]

/-! ## §3. Unconditional Full Weil Functional Chebyshev–Packet Bounds on `RealWeilTestFn` & `RealOddTestFn` -/

/-- **Unconditional Full Weil Functional Chebyshev–Packet Bound on `RealWeilTestFn`
(`RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound`):**
For EVERY `f : RealWeilTestFn` and EVERY `a b c : ℝ` (with **zero** parity or polar-vanishing
hypotheses!), the full untruncated Weil explicit-formula functional of `Λ` satisfies:
$$\Bigl|(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}
  - \bigl(\operatorname{poleWeightArchRe}(0, f.1)
    - 2\,\operatorname{chebyshevWork}(f.\mathrm{toCompactlySupported}, a, b, f.\mathrm{supportScale})\bigr)\Bigr|$$
$$\le\; 2 e^c\,\operatorname{biScaleLevyEnergy}(f.\mathrm{source})
  + \frac{\operatorname{packetEnergy}(f.\mathrm{toCompactlySupported}, f.\mathrm{supportScale})}{e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy.$$ -/
theorem unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound
    (f : RealWeilTestFn) (a b c : ℝ) :
    |(weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re -
        (poleWeightArchRe 0 f.1 -
          2 * SignedPrimePolar.chebyshevWork
            f.toCompactlySupported a b f.supportScale)| ≤
      2 * Real.exp c * biScaleLevyEnergy f.source +
        SignedPrimePolar.packetEnergy f.toCompactlySupported f.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
  set N := f.supportScale
  rw [f.re_weilFullFunctional_vonMangoldt_eq_poleWeightArchRe_zero_sub_two_pairing]
  have hdiff :
      poleWeightArchRe 0 f.1 - 2 * SignedPrimePolar.pairing N (autocorr f.source) -
          (poleWeightArchRe 0 f.1 -
            2 * SignedPrimePolar.chebyshevWork f.toCompactlySupported a b N) =
        -(2 * (SignedPrimePolar.pairing N (autocorr f.source) -
          SignedPrimePolar.chebyshevWork f.toCompactlySupported a b N)) := by
    ring
  rw [hdiff, abs_neg, abs_mul, abs_of_pos two_pos]
  have hpack := SignedPrimePolar.abs_pairing_sub_chebyshevWork_le_packet_levy
    f.toCompactlySupported a b c N
  have hann := annular_levy_integral_le_biScaleLevyEnergy
    f.contDiff_source f.hasCompactSupport_source a b
  have hmul := mul_le_mul_of_nonneg_left hann (Real.exp_pos c).le
  have hcomb :
      |SignedPrimePolar.pairing N (autocorr f.source) -
          SignedPrimePolar.chebyshevWork f.toCompactlySupported a b N| ≤
        Real.exp c * biScaleLevyEnergy f.source +
          SignedPrimePolar.packetEnergy f.toCompactlySupported N /
              (2 * Real.exp c * Real.exp b ^ 2) *
            ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
    change |SignedPrimePolar.pairing N (autocorr (f.toCompactlySupported : ℝ → ℝ)) - _| ≤ _
      at hpack
    linarith only [hpack, hmul]
  have h2 := mul_le_mul_of_nonneg_left hcomb zero_le_two
  have hrhs_eq :
      2 * (Real.exp c * biScaleLevyEnergy f.source +
          SignedPrimePolar.packetEnergy f.toCompactlySupported N /
              (2 * Real.exp c * Real.exp b ^ 2) *
            ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) =
        2 * Real.exp c * biScaleLevyEnergy f.source +
          SignedPrimePolar.packetEnergy f.toCompactlySupported N /
              (Real.exp c * Real.exp b ^ 2) *
            ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
    have hec : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
    have heb : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
    field_simp [hec, heb]
  linarith only [h2, hrhs_eq]

/-- **Unconditional Full Weil Functional Lower Bound on `RealWeilTestFn`:**
For EVERY `f : RealWeilTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!),
$$(1 - 2 e^c)\,\operatorname{biScaleLevyEnergy}(f.\mathrm{source})
  + \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
  - 2\,\operatorname{chebyshevWork}(f.\mathrm{toCompactlySupported}, a, b, f.\mathrm{supportScale})
  - \frac{\operatorname{packetEnergy}(f.\mathrm{toCompactlySupported}, f.\mathrm{supportScale})}{e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy$$
$$\le\; (\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}.$$ -/
theorem unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound
    (f : RealWeilTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork f.toCompactlySupported a b f.supportScale -
        SignedPrimePolar.packetEnergy f.toCompactlySupported f.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  have habs := f.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound a b c
  have hlow := neg_le_of_abs_le habs
  have hpole := f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  linarith only [hlow, hpole]

end RealWeilTestFn

namespace RealOddTestFn

/-- **Unconditional Full Weil Functional Identity on `RealOddTestFn`:**
For EVERY `f : RealOddTestFn` (with **zero hypotheses**!):
$$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
    - 2\,\operatorname{SignedPrimePolar.pairing}\,(f.\mathrm{toRealWeilTestFn}.\mathrm{supportScale})\,(\operatorname{autocorr}\,f.\mathrm{source}).$$ -/
theorem re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing
    (f : RealOddTestFn) :
    (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1.1 f.1.1.1)).re =
      EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re +
        biScaleLevyEnergy f.source -
        2 * SignedPrimePolar.pairing f.toRealWeilTestFn.supportScale (autocorr f.source) :=
  f.toRealWeilTestFn.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing

/-- **Unconditional Full Weil Functional Lower Bound on `RealOddTestFn`:**
For EVERY `f : RealOddTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!): -/
theorem unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound
    (f : RealOddTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork
          f.toCompactlySupported a b f.toRealWeilTestFn.supportScale -
        SignedPrimePolar.packetEnergy
            f.toCompactlySupported f.toRealWeilTestFn.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1.1 f.1.1.1)).re :=
  f.toRealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound a b c

end RealOddTestFn

end

end GaloisForLFunctions.BiScaleUncertainty
