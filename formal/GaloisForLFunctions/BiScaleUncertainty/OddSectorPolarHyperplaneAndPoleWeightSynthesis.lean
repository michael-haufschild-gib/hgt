import GaloisForLFunctions.BiScaleUncertainty.AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis
import GaloisForLFunctions.BiScaleUncertainty.EvenSourceSymmetricPolarEnforcement
import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalFinitePartAndBroadClassification
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicShiftCommutatorAndParityIntertwining
import GaloisForLFunctions.RHTower.OddSectorPoleWeightAtMostOne
import GaloisForLFunctions.RHTower.OddSectorAnyPoleWeightJointRigidity

/-!
# Odd-Sector Polar Hyperplane, Hyperbolic Multiplier Pole Mass, and Pole-Weight Synthesis

This module resolves the odd-sector pole-weight problem (§7.3) in Bi-Scale Uncertainty Theory by:

1. **Hyperbolic Multiplier Intertwining of the Pole Term (`integral_autocorr_sinhMultiplier_half_eq_sq`,
   `RealOddTestFn.re_weilPoleTerm_eq_neg_two_mul_integral_autocorr_sinhMultiplier`):**
   For any continuous compactly supported real source $f$, the hyperbolic moments at $\pm 1/2$ are
   the means of the multiplier states $C_{1/2} f(u) = \cosh(u/2) f(u)$ and
   $S_{1/2} f(u) = \sinh(u/2) f(u)$, so their squares equal the total autocorrelation masses
   $\int_{\mathbb{R}} h_{C_{1/2} f}(x)\,dx$ and $\int_{\mathbb{R}} h_{S_{1/2} f}(x)\,dx$. When $f$
   is odd, $C_{1/2} f$ is odd with zero total autocorrelation mass while $S_{1/2} f$ is lifted into
   the even sector, and the odd pole term is minus twice the total autocorrelation mass of the
   lifted even state:
   $$(\operatorname{weilPoleTerm}(\operatorname{weilTest}\,f\,f)).\mathrm{re}
     = 2 \int_0^\infty \operatorname{polarDensity}(x)\,h_f(x)\,dx
     = -2 \int_{\mathbb{R}} h_{S_{1/2} f}(x)\,dx
     = -2 \left(\int_{\mathbb{R}} f(u)\,\sinh(u/2)\,du\right)^2 \le 0.$$

2. **The Real Odd Polar Hyperplane (`RealOddPolarTestFn`) and Elimination of the Sinh-Moment Cost
   at Pole Weight One:**
   On the hyperplane `RealOddPolarTestFn` of odd real tests satisfying
   $\int_{\mathbb{R}} f(u)\,\sinh(u/2)\,du = 0$ (equivalently, where the lifted even state
   $S_{1/2} f$ has zero mean and zero total autocorrelation mass), the pole term and the half-line
   polar integral vanish identically. Consequently, for **every** pole weight $\beta \in \mathbb{R}$
   — and in particular at the true pole weight $\beta = 1$ — the archimedean functional satisfies
   $$\operatorname{weilArchRe}(\operatorname{weilTest}\,f\,f)
     = \operatorname{poleWeightArchRe}(\beta, f.1.1.1)
     = \Omega(0)\,h_f(0) + \operatorname{biScaleLevyEnergy}(f)$$
   with **zero $\sinh$-moment cost**, so the unconditional dyadic Nyquist and all-scale von Mangoldt
   signed coercivity bounds hold directly for `weilArchRe` at $\beta = 1$.

3. **Symmetric Three-Copy Odd-Polar Enforcement (`evenPolarCopy_odd_of_odd`,
   `exists_odd_polar_source_local_energy_close`, `odd_polar_log_grid_lower_bound_iff`):**
   The symmetric three-copy operator `evenPolarCopy f T` preserves odd parity, annihilates the
   $\sinh(u/2)$ moment, preserves all normalized correlations on $[-A, A]$ for $T > D + A$, and
   perturbs `normalizedArchEnergy` by $O(e^{-T})$. Thus the odd $\sinh$-neutral (`RealOddPolarTestFn`)
   and general odd (`RealOddTestFn`) finite-grid classes have identical normalized archimedean
   energy infima.

4. **Complete Characterization of the Odd Weil Sign and Pole-Weight Window $(-\infty, 1]$ on
   `RealOddPolarTestFn` and `RealOddTestFn` (`riemannHypothesis_iff_realOddPolar_weilFullFunctional_nonneg`,
   `riemannHypothesis_iff_realWeilPositiveOddAt_vonMangoldt`,
   `not_realWeilPositiveOddAt_vonMangoldt_of_one_lt`):**
   Restricting from `RealOddTestFn` to `RealOddPolarTestFn` loses no zero-side information:
   nonnegativity of `weilFullFunctional Λ` on `RealOddPolarTestFn` (where the $\sinh$-moment cost is
   zero) is equivalent to nonnegativity on all of `RealOddTestFn`, and to nonnegativity of
   `weilPoleWeightFunctional β Λ` on `RealOddTestFn` at any $\beta \le 1$, each being equivalent to
   `RiemannHypothesis`; for $\beta > 1$, positivity on `RealOddTestFn` fails unconditionally.
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open _root_.RHTower.WeilMarkovPole _root_.RHTower.EvenSector _root_.RHTower.WeilOneSided
open _root_.RHTower.WeilPoleWeight
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Hyperbolic Multiplier Intertwining of the Pole Term & Odd Sinh-Moment Mass -/

/-- The integral of `coshMultiplier (1 / 2) f` is the $\cosh(u/2)$ moment of `f`. -/
theorem integral_coshMultiplier_half_eq (f : ℝ → ℝ) :
    (∫ u, coshMultiplier (1 / 2) f u) = ∫ u, f u * Real.cosh (u / 2) := by
  unfold coshMultiplier
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [show (1 / 2 : ℝ) * u = u / 2 by ring, mul_comm]

/-- The integral of `sinhMultiplier (1 / 2) f` is the $\sinh(u/2)$ moment of `f`. -/
theorem integral_sinhMultiplier_half_eq (f : ℝ → ℝ) :
    (∫ u, sinhMultiplier (1 / 2) f u) = ∫ u, f u * Real.sinh (u / 2) := by
  unfold sinhMultiplier
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [show (1 / 2 : ℝ) * u = u / 2 by ring, mul_comm]

/-- **Total Autocorrelation Mass of `coshMultiplier (1 / 2) f`:**
For any continuous compactly supported `f : ℝ → ℝ`,
$$\int_{\mathbb{R}} \operatorname{autocorr}(\operatorname{coshMultiplier}(1/2, f), x)\,dx
  = \left(\int_{\mathbb{R}} f(u)\,\cosh(u/2)\,du\right)^2.$$ -/
theorem integral_autocorr_coshMultiplier_half_eq_sq {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∫ x, autocorr (coshMultiplier (1 / 2) f) x) =
      (∫ u, f u * Real.cosh (u / 2)) ^ 2 := by
  let g : C_c(ℝ, ℝ) :=
    ⟨⟨coshMultiplier (1 / 2) f, continuous_coshMultiplier (1 / 2) hf⟩,
      hasCompactSupport_coshMultiplier (1 / 2) hfc⟩
  have hmass := integral_autocorr_eq_sq_integral g
  change (∫ x, autocorr (coshMultiplier (1 / 2) f) x) =
    (∫ u, coshMultiplier (1 / 2) f u) ^ 2 at hmass
  rw [hmass, integral_coshMultiplier_half_eq]

/-- **Total Autocorrelation Mass of `sinhMultiplier (1 / 2) f`:**
For any continuous compactly supported `f : ℝ → ℝ`,
$$\int_{\mathbb{R}} \operatorname{autocorr}(\operatorname{sinhMultiplier}(1/2, f), x)\,dx
  = \left(\int_{\mathbb{R}} f(u)\,\sinh(u/2)\,du\right)^2.$$ -/
theorem integral_autocorr_sinhMultiplier_half_eq_sq {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∫ x, autocorr (sinhMultiplier (1 / 2) f) x) =
      (∫ u, f u * Real.sinh (u / 2)) ^ 2 := by
  let g : C_c(ℝ, ℝ) :=
    ⟨⟨sinhMultiplier (1 / 2) f, continuous_sinhMultiplier (1 / 2) hf⟩,
      hasCompactSupport_sinhMultiplier (1 / 2) hfc⟩
  have hmass := integral_autocorr_eq_sq_integral g
  change (∫ x, autocorr (sinhMultiplier (1 / 2) f) x) =
    (∫ u, sinhMultiplier (1 / 2) f u) ^ 2 at hmass
  rw [hmass, integral_sinhMultiplier_half_eq]

/-- **Hyperbolic Multiplier Autocorrelation Mass Formula for `weilPoleTerm`:**
For every continuous compactly supported `f : ℝ → ℝ`, the real pole term equals twice the
difference between the total autocorrelation masses of `coshMultiplier (1 / 2) f` and
`sinhMultiplier (1 / 2) f`. -/
theorem re_weilPoleTerm_ofReal_eq_two_mul_integral_autocorr_cosh_sub_sinh {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    (weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      2 * ((∫ x, autocorr (coshMultiplier (1 / 2) f) x) -
        (∫ x, autocorr (sinhMultiplier (1 / 2) f) x)) := by
  rw [re_weilPoleTerm_ofReal_eq_cosh_sq_sub_sinh_sq hf hfc,
    ← integral_autocorr_coshMultiplier_half_eq_sq hf hfc,
    ← integral_autocorr_sinhMultiplier_half_eq_sq hf hfc]

/-- Any odd function `f : ℝ → ℝ` has zero integral over `ℝ`. -/
theorem integral_eq_zero_of_odd {f : ℝ → ℝ} (hodd : ∀ u : ℝ, f (-u) = -f u) :
    (∫ u : ℝ, f u) = 0 := by
  have hneg := integral_neg_eq_self (μ := volume) f
  have hfun : (fun u : ℝ => f (-u)) = fun u : ℝ => -f u := funext hodd
  rw [hfun, integral_neg] at hneg
  linarith only [hneg]

/-- The autocorrelation of any odd continuous compactly supported source has zero total integral. -/
theorem integral_autocorr_eq_zero_of_odd {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hodd : ∀ u : ℝ, f (-u) = -f u) :
    (∫ x : ℝ, autocorr f x) = 0 := by
  let g : C_c(ℝ, ℝ) := ⟨⟨f, hf⟩, hfc⟩
  have hmass := integral_autocorr_eq_sq_integral g
  change (∫ x, autocorr f x) = (∫ u, f u) ^ 2 at hmass
  rw [hmass, integral_eq_zero_of_odd hodd, sq, zero_mul]

/-- For any odd continuous compactly supported source `f`, `coshMultiplier α f` is odd and its
autocorrelation has zero total integral. -/
theorem integral_autocorr_coshMultiplier_eq_zero_of_odd {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hodd : ∀ u : ℝ, f (-u) = -f u) (α : ℝ) :
    (∫ x : ℝ, autocorr (coshMultiplier α f) x) = 0 :=
  integral_autocorr_eq_zero_of_odd (continuous_coshMultiplier α hf)
    (hasCompactSupport_coshMultiplier α hfc) (coshMultiplier_odd_of_odd α hodd)

namespace RealOddTestFn

/-- **Hyperbolic Multiplier Formula for the Odd Pole Term:**
For every `f : RealOddTestFn`, the real pole term equals minus twice the total autocorrelation
mass of the lifted even state `sinhMultiplier (1 / 2) f.source`:
$$(\operatorname{weilPoleTerm}(\operatorname{weilTest}\,f\,f)).\mathrm{re}
  = -2 \int_{\mathbb{R}} \operatorname{autocorr}(\operatorname{sinhMultiplier}(1/2, f.\mathrm{source}), x)\,dx.$$ -/
theorem re_weilPoleTerm_eq_neg_two_mul_integral_autocorr_sinhMultiplier (f : RealOddTestFn) :
    (weilPoleTerm (EF.weilTest f.1.1.1 f.1.1.1)).re =
      -2 * ∫ x, autocorr (sinhMultiplier (1 / 2) f.source) x := by
  rw [f.re_weilPoleTerm_eq_neg_two_mul_sinh_sq,
    ← integral_autocorr_sinhMultiplier_half_eq_sq
      f.contDiff_source.continuous f.hasCompactSupport_source]

/-- **Half-Line Polar Integral Sign Law on `RealOddTestFn`:**
For every `f : RealOddTestFn`, the half-line polar integral is nonpositive and equals minus twice
the squared $\sinh(u/2)$ moment:
$$2 \int_0^\infty \operatorname{polarDensity}(x)\,\operatorname{autocorr}(f.\mathrm{source}, x)\,dx
  = -2\left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\sinh(u/2)\,du\right)^2 \le 0.$$ -/
theorem two_mul_integral_Ioi_polarDensity_autocorr_eq_neg_two_mul_sinh_sq (f : RealOddTestFn) :
    2 * (∫ x in Ioi 0, SignedPrimePolar.polarDensity x * autocorr f.source x) =
      -2 * (∫ u, f.source u * Real.sinh (u / 2)) ^ 2 := by
  have hp := two_mul_integral_Ioi_polarDensity_autocorr_eq_re_weilPoleTerm
    f.contDiff_source f.hasCompactSupport_source
  rw [f.source_eq, f.re_weilPoleTerm_eq_neg_two_mul_sinh_sq] at hp
  exact hp

/-- **Hyperbolic Multiplier Form of the Sinh-Capacity Weil Identity on `RealOddTestFn` ($\beta = 1$):**
For every `f : RealOddTestFn`,
$$\operatorname{weilArchRe}(\operatorname{weilTest}\,f\,f)
  + 2 \int_{\mathbb{R}} \operatorname{autocorr}(\operatorname{sinhMultiplier}(1/2, f.\mathrm{source}), x)\,dx
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source}).$$ -/
theorem weilArchRe_add_two_mul_integral_autocorr_sinhMultiplier_eq (f : RealOddTestFn) :
    WeilOneSided.weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) +
        2 * (∫ x, autocorr (sinhMultiplier (1 / 2) f.source) x) =
      EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re +
        biScaleLevyEnergy f.source := by
  rw [integral_autocorr_sinhMultiplier_half_eq_sq
    f.contDiff_source.continuous f.hasCompactSupport_source]
  exact f.weilArchRe_add_two_mul_sinh_sq_eq_gamma_add_biScaleLevyEnergy

/-- **Antitonicity of `poleWeightArchRe` on `RealOddTestFn`:**
Because the odd pole term is nonpositive, `poleWeightArchRe β f.1.1` is antitone in $\beta$. -/
theorem poleWeightArchRe_anti (f : RealOddTestFn) {β β' : ℝ} (hβ : β ≤ β') :
    poleWeightArchRe β' f.1.1 ≤ poleWeightArchRe β f.1.1 := by
  rw [f.poleWeightArchRe_eq β', f.poleWeightArchRe_eq β]
  have hnn : 0 ≤ 2 * (β' - β) * (∫ u, f.source u * Real.sinh (u / 2)) ^ 2 := by
    positivity
  linarith only [hnn]

/-- For every nonpositive pole weight $\beta \le 0$ and every `f : RealOddTestFn`,
`poleWeightArchRe β f.1.1` dominates the pole-free archimedean energy with a nonnegative
$\sinh$-moment bonus. -/
theorem gamma_add_biScaleLevyEnergy_le_poleWeightArchRe_of_nonpos
    (f : RealOddTestFn) {β : ℝ} (hβ : β ≤ 0) :
    EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re +
        biScaleLevyEnergy f.source ≤
      poleWeightArchRe β f.1.1 := by
  rw [← f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy]
  exact f.poleWeightArchRe_anti hβ

end RealOddTestFn

/-! ## §2. The Real Odd Polar Hyperplane `RealOddPolarTestFn` & Zero Sinh-Moment Cost at $\beta = 1$ -/

/-- **The Real Odd Polar Hyperplane (`RealOddPolarTestFn`):**
All real odd Weil test functions `f : RealOddTestFn` whose hyperbolic sine moment vanishes
(`∫ u, f.source u * Real.sinh (u / 2) = 0`), equivalently whose lifted even multiplier state
`sinhMultiplier (1 / 2) f.source` has zero mean and zero total autocorrelation mass. -/
def RealOddPolarTestFn : Type :=
  {f : RealOddTestFn // (∫ u : ℝ, f.source u * Real.sinh (u / 2)) = 0}

namespace RealOddPolarTestFn

/-- The underlying real source of `f : RealOddPolarTestFn`. -/
def source (f : RealOddPolarTestFn) : ℝ → ℝ := f.1.source

theorem integral_source_mul_sinh_eq_zero (f : RealOddPolarTestFn) :
    (∫ u : ℝ, f.source u * Real.sinh (u / 2)) = 0 := f.2

theorem integral_source_mul_cosh_eq_zero (f : RealOddPolarTestFn) :
    (∫ u : ℝ, f.source u * Real.cosh (u / 2)) = 0 :=
  f.1.integral_source_mul_cosh_eq_zero

/-- On `RealOddPolarTestFn`, the lifted even multiplier state `sinhMultiplier (1 / 2) f.source`
has zero mean. -/
theorem integral_sinhMultiplier_half_eq_zero (f : RealOddPolarTestFn) :
    (∫ u : ℝ, sinhMultiplier (1 / 2) f.source u) = 0 := by
  rw [integral_sinhMultiplier_half_eq]
  exact f.2

/-- On `RealOddPolarTestFn`, the lifted even multiplier state `sinhMultiplier (1 / 2) f.source`
has zero total autocorrelation mass. -/
theorem integral_autocorr_sinhMultiplier_half_eq_zero (f : RealOddPolarTestFn) :
    (∫ x : ℝ, autocorr (sinhMultiplier (1 / 2) f.source) x) = 0 := by
  rw [integral_autocorr_sinhMultiplier_half_eq_sq
    f.1.contDiff_source.continuous f.1.hasCompactSupport_source,
    f.integral_source_mul_sinh_eq_zero, sq, zero_mul]

/-- **Vanishing Pole Term on `RealOddPolarTestFn`:**
For every `f : RealOddPolarTestFn`, `(weilPoleTerm (weilTest f f)).re = 0`. -/
theorem re_weilPoleTerm_eq_zero (f : RealOddPolarTestFn) :
    (weilPoleTerm (EF.weilTest f.1.1.1.1 f.1.1.1.1)).re = 0 := by
  rw [f.1.re_weilPoleTerm_eq_neg_two_mul_sinh_sq, f.2]
  ring

/-- **Exact Half-Line Polar Balance on `RealOddPolarTestFn`:**
For every `f : RealOddPolarTestFn`,
$$\int_0^\infty \operatorname{polarDensity}(x)\,\operatorname{autocorr}(f.\mathrm{source}, x)\,dx = 0.$$ -/
theorem integral_Ioi_polarDensity_autocorr_eq_zero (f : RealOddPolarTestFn) :
    (∫ x in Ioi 0, SignedPrimePolar.polarDensity x * autocorr f.source x) = 0 := by
  have h := f.1.two_mul_integral_Ioi_polarDensity_autocorr_eq_neg_two_mul_sinh_sq
  rw [f.2] at h
  change 2 * (∫ x in Ioi 0, SignedPrimePolar.polarDensity x * autocorr f.source x) =
    -2 * (0 : ℝ) ^ 2 at h
  linarith only [h]

/-- **Exact Pole-Weight Invariance on `RealOddPolarTestFn`:**
For every `f : RealOddPolarTestFn` and **every** pole weight $\beta \in \mathbb{R}$, the
$\sinh$-moment cost vanishes identically:
$$\operatorname{poleWeightArchRe}(\beta, f.1.1.1)
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source}).$$ -/
theorem poleWeightArchRe_eq_gamma_add_biScaleLevyEnergy
    (f : RealOddPolarTestFn) (β : ℝ) :
    poleWeightArchRe β f.1.1.1 =
      EF.gammaBracket 0 * (EF.weilTest f.1.1.1.1 f.1.1.1.1 0).re +
        biScaleLevyEnergy f.source := by
  have h := f.1.poleWeightArchRe_eq β
  rw [f.2] at h
  change poleWeightArchRe β f.1.1.1 =
    EF.gammaBracket 0 * (EF.weilTest f.1.1.1.1 f.1.1.1.1 0).re +
      biScaleLevyEnergy f.source - 2 * β * (0 : ℝ) ^ 2 at h
  linarith only [h]

/-- **Exact Pole-Weight-One Identity on `RealOddPolarTestFn` (Zero Sinh-Moment Cost):**
For every `f : RealOddPolarTestFn`, at the true pole weight $\beta = 1$,
$$\operatorname{weilArchRe}(\operatorname{weilTest}\,f\,f)
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source}).$$ -/
theorem weilArchRe_eq_gamma_add_biScaleLevyEnergy (f : RealOddPolarTestFn) :
    WeilOneSided.weilArchRe (EF.weilTest f.1.1.1.1 f.1.1.1.1) =
      EF.gammaBracket 0 * (EF.weilTest f.1.1.1.1 f.1.1.1.1 0).re +
        biScaleLevyEnergy f.source := by
  have h := f.1.weilArchRe_add_two_mul_sinh_sq_eq_gamma_add_biScaleLevyEnergy
  rw [f.2] at h
  change WeilOneSided.weilArchRe (EF.weilTest f.1.1.1.1 f.1.1.1.1) + 2 * (0 : ℝ) ^ 2 =
    EF.gammaBracket 0 * (EF.weilTest f.1.1.1.1 f.1.1.1.1 0).re +
      biScaleLevyEnergy f.source at h
  linarith only [h]

/-- **Unconditional Dyadic-Window Signed Lower Bound for `weilArchRe` ($\beta = 1$) on
`RealOddPolarTestFn` with Zero Sinh-Moment Cost:** -/
theorem unconditional_dyadic_signed_weilArchRe_lower_bound
    (f : RealOddPolarTestFn) (M : ℕ) :
    (EF.gammaBracket 0 + dyadicNyquistCoerciveConstant (M + 2)) *
        (EF.weilTest f.1.1.1.1 f.1.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest f.1.1.1.1 f.1.1.1.1) +
        ∑ k ∈ Finset.range (M + 2),
          (Real.log ((M + 2 + k + 1 : ℕ) : ℝ) - Real.log ((M + 2 + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((M + 2 + k + 1 : ℕ) : ℝ)) *
            (EF.weilTest f.1.1.1.1 f.1.1.1.1 (Real.log ((M + 2 + k : ℕ) : ℝ))).re := by
  have h0 := f.1.unconditional_dyadic_signed_poleWeightArchRe_zero_lower_bound M
  have hp0 := f.1.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  have hp1 := f.weilArchRe_eq_gamma_add_biScaleLevyEnergy
  change biScaleLevyEnergy f.1.source = _ at *
  unfold source at hp1
  linarith only [h0, hp0, hp1]

/-- **Unconditional All-Scale Von Mangoldt Signed Lower Bound for `weilArchRe` ($\beta = 1$) on
`RealOddPolarTestFn` with Zero Sinh-Moment Cost:**
For every `f : RealOddPolarTestFn` and every `N : ℕ`, `weilArchRe` at pole weight one satisfies the
exact all-scale von Mangoldt lower bound with **no** residual $\sinh$-moment penalty. -/
theorem unconditional_vonMangoldt_all_scale_signed_weilArchRe_lower_bound
    (f : RealOddPolarTestFn) (N : ℕ) :
    (EF.gammaBracket 0 + allScaleVonMangoldtCoerciveConstant N) *
        (EF.weilTest f.1.1.1.1 f.1.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest f.1.1.1.1 f.1.1.1.1) +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 3 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            (EF.weilTest f.1.1.1.1 f.1.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re := by
  have h := f.1.unconditional_vonMangoldt_all_scale_signed_weilArchRe_sinh_lower_bound N
  rw [f.2] at h
  linarith only [h]

/-- On `RealOddPolarTestFn`, for every `N ≥ f.1.toRealWeilTestFn.supportScale`, the continuum
polar integral in `SignedPrimePolar.pairing` vanishes identically, so `SignedPrimePolar.pairing`
equals the finite prime-power sum. -/
theorem pairing_eq_prime_sum (f : RealOddPolarTestFn) {N : ℕ}
    (hN : f.1.toRealWeilTestFn.supportScale ≤ N) :
    SignedPrimePolar.pairing N (autocorr f.source) =
      ∑ n ∈ Finset.Icc 1 (N + 2),
        SignedPrimePolar.primeWeight n *
          (EF.weilTest f.1.1.1.1 f.1.1.1.1 (Real.log (n : ℝ))).re := by
  have hbridge := f.1.toRealWeilTestFn.two_mul_prime_sum_add_polar_tail_eq_two_pairing_add_pole N
  have htail := f.1.toRealWeilTestFn.polar_tail_eq_zero_of_supportScale_le hN
  have hpole := f.re_weilPoleTerm_eq_zero
  change 2 * ((∑ n ∈ Finset.Icc 1 (N + 2),
        SignedPrimePolar.primeWeight n * (EF.weilTest f.1.1.1.1 f.1.1.1.1 (Real.log (n : ℝ))).re) +
      ∫ x in Ioi (SignedPrimePolar.cutoff N),
        SignedPrimePolar.polarDensity x * autocorr f.source x) =
    2 * SignedPrimePolar.pairing N (autocorr f.source) +
      (weilPoleTerm (EF.weilTest f.1.1.1.1 f.1.1.1.1)).re at hbridge
  change (∫ x in Ioi (SignedPrimePolar.cutoff N),
      SignedPrimePolar.polarDensity x * autocorr f.source x) = 0 at htail
  linarith only [hbridge, htail, hpole]

end RealOddPolarTestFn

/-! ## §3. Symmetric Three-Copy Odd-Polar Enforcement & Odd Finite-Grid Infimum Equivalence -/

/-- `evenPolarCopy f T` preserves odd source parity (`∀ u, f (-u) = -f u`). -/
theorem evenPolarCopy_odd_of_odd {f : ℝ → ℝ}
    (hodd : ∀ u : ℝ, f (-u) = -f u) (T u : ℝ) :
    evenPolarCopy f T (-u) = -evenPolarCopy f T u :=
  symmetricCopy_odd_of_odd hodd _ T u

/-- `evenPolarCopy f T` has vanishing $\sinh(u/2)$ moment for every continuous compactly supported
`f : ℝ → ℝ` and every `T ∈ ℝ`. -/
theorem integral_evenPolarCopy_sinh_half {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (T : ℝ) :
    (∫ u, evenPolarCopy f T u * Real.sinh (u / 2)) = 0 := by
  have hc := continuous_symmetricCopy hf (1 / (2 * Real.cosh (T / 2))) T
  have hcs := hasCompactSupport_symmetricCopy hfc (1 / (2 * Real.cosh (T / 2))) T
  have hip : Integrable (fun u => evenPolarCopy f T u * Real.exp (u / 2)) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hin : Integrable (fun u => evenPolarCopy f T u * Real.exp (-u / 2)) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hrew : (fun u => evenPolarCopy f T u * Real.sinh (u / 2)) =
      fun u => (1 / 2 : ℝ) * (evenPolarCopy f T u * Real.exp (u / 2) -
        evenPolarCopy f T u * Real.exp (-u / 2)) := by
    funext u
    rw [Real.sinh_eq, show -(u / 2) = -u / 2 by ring]
    ring
  rw [hrew, integral_const_mul, integral_sub hip hin,
    integral_evenPolarCopy_exp_pos_half hf hfc T,
    integral_evenPolarCopy_exp_neg_half hf hfc T]
  ring

/-- `evenPolarCopy f T` has vanishing $\cosh(u/2)$ moment for every continuous compactly supported
`f : ℝ → ℝ` and every `T ∈ ℝ`. -/
theorem integral_evenPolarCopy_cosh_half {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (T : ℝ) :
    (∫ u, evenPolarCopy f T u * Real.cosh (u / 2)) = 0 := by
  have hc := continuous_symmetricCopy hf (1 / (2 * Real.cosh (T / 2))) T
  have hcs := hasCompactSupport_symmetricCopy hfc (1 / (2 * Real.cosh (T / 2))) T
  have hip : Integrable (fun u => evenPolarCopy f T u * Real.exp (u / 2)) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hin : Integrable (fun u => evenPolarCopy f T u * Real.exp (-u / 2)) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hrew : (fun u => evenPolarCopy f T u * Real.cosh (u / 2)) =
      fun u => (1 / 2 : ℝ) * (evenPolarCopy f T u * Real.exp (u / 2) +
        evenPolarCopy f T u * Real.exp (-u / 2)) := by
    funext u
    rw [Real.cosh_eq, show -(u / 2) = -u / 2 by ring]
    ring
  rw [hrew, integral_const_mul, integral_add hip hin,
    integral_evenPolarCopy_exp_pos_half hf hfc T,
    integral_evenPolarCopy_exp_neg_half hf hfc T]
  ring

/-- Every nonzero **odd** compactly supported $C^r$ source ($r \ge 2$) admits an **odd**,
$\sinh$-neutral ($\int g(u)\sinh(u/2)\,du = 0$), dual-rate ($\pm 1/2$) neutral, polar-neutral
($\int_0^\infty h_g(x)\cosh(x/2)\,dx = 0$) $C^r$ compact source with identical normalized
autocorrelation on `[-A, A]` and normalized Bi-Scale Lévy energy within `ε`. -/
theorem exists_odd_polar_source_local_energy_close {f : ℝ → ℝ} {r : WithTop ℕ∞}
    (hr : 2 ≤ r) (hf : ContDiff ℝ r f) (hfc : HasCompactSupport f)
    (hodd : ∀ u : ℝ, f (-u) = -f u) (hR : 0 < autocorr f 0) (A : ℝ) (hA : 0 ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ r g ∧ HasCompactSupport g ∧
      (∀ u : ℝ, g (-u) = -g u) ∧ 0 < autocorr g 0 ∧
      (∫ u, g u * Real.sinh (u / 2)) = 0 ∧
      (∫ u, g u * Real.exp (u / 2)) = 0 ∧
      (∫ u, g u * Real.exp (-u / 2)) = 0 ∧
      (∫ x in Ioi 0, autocorr g x * Real.cosh (x / 2)) = 0 ∧
      (∀ x, |x| ≤ A → autocorr g x / autocorr g 0 = autocorr f x / autocorr f 0) ∧
      |normalizedArchEnergy g - normalizedArchEnergy f| < ε := by
  obtain ⟨D, hDpos, hsupp⟩ := exists_pos_autocorr_support_radius hfc
  have hf2 : ContDiff ℝ 2 f := hf.of_le hr
  have htend :
      Tendsto (fun T : ℝ => 3 * polarEnergyErrorConstant f D * Real.exp (-T)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (3 * polarEnergyErrorConstant f D)
  have hevent := (tendsto_order.mp htend).2 ε hε
  obtain ⟨T, hlarge, hsmall⟩ := ((eventually_gt_atTop (D + max A 1)).and hevent).exists
  have hTA : D + A < T := lt_of_le_of_lt (by linarith [le_max_left A 1]) hlarge
  have hT1 : D + 1 ≤ T := le_of_lt (lt_of_le_of_lt (by linarith [le_max_right A 1]) hlarge)
  refine ⟨evenPolarCopy f T,
    contDiff_symmetricCopy hf _ _,
    hasCompactSupport_symmetricCopy hfc _ _,
    evenPolarCopy_odd_of_odd hodd T,
    ?_,
    integral_evenPolarCopy_sinh_half hf.continuous hfc T,
    integral_evenPolarCopy_exp_pos_half hf.continuous hfc T,
    integral_evenPolarCopy_exp_neg_half hf.continuous hfc T,
    integral_evenPolarCopy_autocorr_cosh hf2 hfc T,
    ?_,
    (normalizedArchEnergy_evenPolarCopy_error hf2 hfc hR hDpos.le hsupp hT1).trans_lt hsmall⟩
  · change 0 < autocorr (symmetricCopy f (1 / (2 * Real.cosh (T / 2))) T) 0
    rw [autocorr_symmetricCopy_local hf.continuous hfc hDpos.le hA hsupp hTA
      (by simpa using hA : |(0 : ℝ)| ≤ A)]
    positivity
  · intro x hx
    exact normalized_autocorr_symmetricCopy_local hf.continuous hfc hDpos.le hA hsupp hTA hx _

/-- **Odd-Source Polar Infimum Equivalence (`↔`):**
A lower bound `C` on `normalizedArchEnergy` holds for all **odd** $\sinh$-neutral
(`∫ u, f u * Real.sinh (u / 2) = 0`) logarithmic-grid sources if and only if it holds for all
**odd** logarithmic-grid sources without the $\sinh$-neutrality condition. -/
theorem odd_polar_log_grid_lower_bound_iff (r : WithTop ℕ∞) (hr : 2 ≤ r) (N : ℕ) (C : ℝ) :
    (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → (∀ u : ℝ, f (-u) = -f u) →
      0 < autocorr f 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) →
      (∫ u, f u * Real.sinh (u / 2)) = 0 → C ≤ normalizedArchEnergy f) ↔
    (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → (∀ u : ℝ, f (-u) = -f u) →
      0 < autocorr f 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) → C ≤ normalizedArchEnergy f) := by
  constructor
  · intro hpolar f hf hfc hodd hR hgrid
    by_contra hbad
    have hgap : 0 < (C - normalizedArchEnergy f) / 2 := by linarith
    let A := max (Real.log (N : ℝ)) 0
    obtain ⟨g, hg, hgc, hgodd, hRg, hsinh, _, _, _, hlocal, herr⟩ :=
      exists_odd_polar_source_local_energy_close hr hf hfc hodd hR A (le_max_right _ _) hgap
    have hgridg : ∀ n ∈ Finset.Icc 2 N, autocorr g (Real.log (n : ℝ)) = 0 := by
      intro n hn
      have hnrange := Finset.mem_Icc.mp hn
      have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      have hbound : |Real.log (n : ℝ)| ≤ A := by
        rw [abs_of_nonneg hln]
        exact (Real.log_le_log hnp (by exact_mod_cast hnrange.2)).trans (le_max_left _ _)
      have hval := hlocal (Real.log (n : ℝ)) hbound
      rw [hgrid n hn, zero_div] at hval
      exact (div_eq_zero_iff.mp hval).resolve_right hRg.ne'
    have hgC := hpolar g hg hgc hgodd hRg hgridg hsinh
    have := (le_abs_self (normalizedArchEnergy g - normalizedArchEnergy f)).trans_lt herr
    linarith
  · intro hall f hf hfc hodd hR hgrid _
    exact hall f hf hfc hodd hR hgrid

/-! ## §4. Complete Characterization of the Odd Weil Sign & Pole-Weight Window $(-\infty, 1]$ -/

/-- Canonical constructor for `RealOddTestFn` from a real odd $C^2_c$ source `f : ℝ → ℝ`. -/
def RealOddTestFn.ofRealSource (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ u : ℝ, f (-u) = -f u) : RealOddTestFn :=
  ⟨⟨⟨fun u => (f u : ℂ), Complex.ofRealCLM.contDiff.comp hf, hfc.comp_left Complex.ofReal_zero⟩,
    fun u => by simp only [hodd u, Complex.ofReal_neg]⟩,
    fun _ => Complex.ofReal_im _⟩

@[simp]
theorem RealOddTestFn.source_ofRealSource (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hodd : ∀ u : ℝ, f (-u) = -f u) :
    (RealOddTestFn.ofRealSource f hf hfc hodd).source = f := rfl

/-- If an odd continuous compactly supported real source `f` has `paperFT (f : ℝ → ℂ) (I / 2) = 0`,
then its $\sinh(u/2)$ moment vanishes. -/
theorem integral_sinh_half_eq_zero_of_odd_of_paperFT_I_div_two_eq_zero
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hodd : ∀ u : ℝ, f (-u) = -f u)
    (hp : EF.paperFT (fun u => (f u : ℂ)) (I / 2) = 0) :
    (∫ u : ℝ, f u * Real.sinh (u / 2)) = 0 := by
  have hexp : (∫ u : ℝ, f u * Real.exp (-u / 2)) = 0 := by
    have h1 := _root_.RHTower.paperFT_ofRealFun_I_div_two f
    rw [hp] at h1
    exact_mod_cast h1.symm
  have hcosh : (∫ u : ℝ, f u * Real.cosh (u / 2)) = 0 := by
    have hneg := integral_neg_eq_self (μ := volume) (fun u : ℝ => f u * Real.cosh (u / 2))
    have hfun : (fun u : ℝ => f (-u) * Real.cosh (-u / 2)) =
        fun u : ℝ => -(f u * Real.cosh (u / 2)) := by
      funext u
      rw [hodd u, show (-u : ℝ) / 2 = -(u / 2) by ring, Real.cosh_neg]
      ring
    rw [hfun, integral_neg] at hneg
    linarith only [hneg]
  have hic : Integrable (fun u => f u * Real.cosh (u / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hie : Integrable (fun u => f u * Real.exp (-u / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hrew : (fun u : ℝ => f u * Real.sinh (u / 2)) =
      fun u : ℝ => f u * Real.cosh (u / 2) - f u * Real.exp (-u / 2) := by
    funext u
    rw [Real.sinh_eq, Real.cosh_eq, show -(u / 2) = -u / 2 by ring]
    ring
  rw [hrew, integral_sub hic hie, hcosh, hexp, sub_zero]

/-- Real-valued odd Weil positivity at pole weight `β` on `RealOddTestFn`. -/
def RealWeilPositiveOddAt (β : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ f : RealOddTestFn,
    0 ≤ (weilPoleWeightFunctional β lam (EF.weilTest f.1.1.1 f.1.1.1)).re

/-- Real-valued odd polar Weil positivity on `RealOddPolarTestFn` (where the pole term and
$\sinh$-moment cost are identically zero, so all pole weights $\beta \in \mathbb{R}$ coincide). -/
def RealOddPolarWeilPositive (lam : ℕ → ℝ) : Prop :=
  ∀ f : RealOddPolarTestFn,
    0 ≤ (weilFullFunctional lam (EF.weilTest f.1.1.1.1 f.1.1.1.1)).re

/-- Antitonicity of `RealWeilPositiveOddAt` in the pole weight `β`. -/
theorem realWeilPositiveOddAt_anti {β β' : ℝ} (hβ : β ≤ β') {lam : ℕ → ℝ}
    (h : RealWeilPositiveOddAt β' lam) : RealWeilPositiveOddAt β lam := by
  intro f
  have h1 := h f
  rw [_root_.RHTower.re_weilPoleWeightFunctional_eq_add,
    f.re_weilPoleTerm_eq_neg_two_mul_sinh_sq] at h1 ⊢
  have h2 : 0 ≤ 2 * (β' - β) * (∫ u, f.source u * Real.sinh (u / 2)) ^ 2 := by positivity
  linarith only [h1, h2]

/-- Every `RealWeilPositiveOddAt β lam` system (for any $\beta \in \mathbb{R}$) is
`RealOddPolarWeilPositive lam`. -/
theorem realOddPolarWeilPositive_of_realWeilPositiveOddAt {β : ℝ} {lam : ℕ → ℝ}
    (h : RealWeilPositiveOddAt β lam) : RealOddPolarWeilPositive lam := by
  intro f
  have h1 := h f.1
  rw [_root_.RHTower.re_weilPoleWeightFunctional_eq_add, f.re_weilPoleTerm_eq_zero] at h1
  linarith only [h1]

/-- **Without RH, `RealOddPolarWeilPositive Λ` fails (and hence `RealWeilPositiveOddAt β Λ` fails
for every $\beta \in \mathbb{R}$):**
There is an explicit odd polar test `f : RealOddPolarTestFn` (with zero $\sinh$-moment cost) of
strictly negative Weil energy. -/
theorem not_realOddPolarWeilPositive_vonMangoldt_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ¬ RealOddPolarWeilPositive (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  intro hpos
  obtain ⟨f, hf, hfc, hodd, hp, hneg⟩ :=
    _root_.RHTower.exists_odd_poleFree_negative_of_not_riemannHypothesis hRH
  have hsinh := integral_sinh_half_eq_zero_of_odd_of_paperFT_I_div_two_eq_zero
    hf.continuous hfc hodd hp
  let F : RealOddPolarTestFn := ⟨RealOddTestFn.ofRealSource f hf hfc hodd, hsinh⟩
  have hF := hpos F
  have hval := _root_.RHTower.re_weilPoleWeightFunctional_vonMangoldt_of_poleFree 1 hf hfc hp
  rw [_root_.RHTower.re_weilPoleWeightFunctional_eq_add] at hval
  change (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest F.1.1.1.1 F.1.1.1.1)).re +
    (1 - 1) * (weilPoleTerm (EF.weilTest F.1.1.1.1 F.1.1.1.1)).re =
    ( _root_.RHTower.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re at hval
  linarith only [hF, hval, hneg]

/-- **Exact Odd-Polar RH Equivalence (Zero Sinh-Moment Cost):**
The Riemann Hypothesis is equivalent to nonnegativity of `weilFullFunctional Λ` on the odd polar
hyperplane `RealOddPolarTestFn` (where the $\sinh$-moment cost vanishes identically), and
equivalently on all of `RealOddTestFn`. -/
theorem riemannHypothesis_iff_realOddPolarWeilPositive_vonMangoldt :
    RiemannHypothesis ↔
      RealOddPolarWeilPositive (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  constructor
  · intro hRH f
    have hW := (_root_.RHTower.riemannHypothesis_iff_weilPositiveOdd_vonMangoldt.mp hRH)
      f.1.1.1.1 f.1.1.1.2.1 f.1.1.1.2.2 f.1.1.2
    exact hW
  · intro h
    by_contra hRH
    exact not_realOddPolarWeilPositive_vonMangoldt_of_not_riemannHypothesis hRH h

/-- **Exact Odd Pole-Weight RH Equivalence for Every $\beta \le 1$:**
For any pole weight $\beta \le 1$ (including $\beta = 1$ and $\beta = 0$), `RiemannHypothesis` is
equivalent to `RealWeilPositiveOddAt β Λ` on `RealOddTestFn`. -/
theorem riemannHypothesis_iff_realWeilPositiveOddAt_vonMangoldt {β : ℝ} (hβ : β ≤ 1) :
    RiemannHypothesis ↔
      RealWeilPositiveOddAt β (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  constructor
  · intro hRH f
    exact (_root_.RHTower.riemannHypothesis_iff_weilPositiveOddAt_vonMangoldt hβ).mp hRH
      f.1.1.1 f.1.1.2.1 f.1.1.2.2 f.1.2
  · intro h
    exact riemannHypothesis_iff_realOddPolarWeilPositive_vonMangoldt.mpr
      (realOddPolarWeilPositive_of_realWeilPositiveOddAt h)

/-- **Unconditional Failure of Odd Positivity Above Pole Weight One ($\beta > 1$):**
For every $\beta > 1$ and every real weight sequence `lam : ℕ → ℝ`, `WeilPositiveOddAt β lam` is
false unconditionally, and `PrimeBlindPositiveOddAt β` is false unconditionally. -/
theorem not_weilPositiveOddAt_and_not_primeBlindPositiveOddAt_of_one_lt {β : ℝ} (hβ : 1 < β)
    (lam : ℕ → ℝ) :
    ¬ _root_.RHTower.WeilPositiveOddAt β lam ∧
      ¬ _root_.RHTower.PrimeBlindPositiveOddAt β :=
  ⟨_root_.RHTower.OddSector.not_weilPositiveOddAt_of_one_lt hβ lam,
    _root_.RHTower.OddSector.not_primeBlindPositiveOddAt_of_one_lt hβ⟩

/-- **Joint Parity Rigidity Across All Odd Pole Weights:**
If a real weight sequence `lam : ℕ → ℝ` is Weil-positive on odd tests at *any* pole weight
$\beta \in \mathbb{R}$ and on even pole-free tests, then `RiemannHypothesis` holds and
$\mathrm{lam}(n) = \Lambda(n)$ for all $n \ge 2$. -/
theorem riemannHypothesis_and_eq_vonMangoldt_of_weilPositiveOddAt_of_evenPolar {β : ℝ}
    {lam : ℕ → ℝ} (ho : _root_.RHTower.WeilPositiveOddAt β lam)
    (he : _root_.RHTower.EvenSector.WeilPositiveEvenPolar lam) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  _root_.RHTower.EvenSector.riemannHypothesis_of_weilPositiveOddAt_anyWeight_of_weilPositiveEvenPolar
    ho he

end

end GaloisForLFunctions.BiScaleUncertainty
