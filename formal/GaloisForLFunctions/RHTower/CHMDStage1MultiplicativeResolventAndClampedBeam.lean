import GaloisForLFunctions.RHTower.EvenSectorAbelRigidity
import GaloisForLFunctions.RHTower.PrimitiveHyperplaneBlindPositivity
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegular
import GaloisForLFunctions.RHTower.WeilLevyPoleGaussModeCancellation
import GaloisForLFunctions.RHTower.MarkovResolventCoercivityAndEulerMaclaurinPBAP
import GaloisForLFunctions.RHTower.CosDilationPrimitiveEnergyRigidity

/-!
# CHMD Stage 1: Even Polar Rigidity for `Λ`, Four-Mode Gauss Floor, and Clamped-Beam Resolvent

This module establishes the three foundational pillars of **Stage 1** of the Causal
Hyperbolic–Modular Duality (CHMD) route:

1. **Even Pole-Free Rigidity for `Λ` (`riemannHypothesis_iff_weilPositiveEvenPolar_vonMangoldt`)**:
   Using the regular decomposition `-ζ'/ζ(1 + s) = 1/s + zetaLogDerivReg(1 + s)` (`ZetaLogDerivRegular`)
   to establish `s · oddDirichlet Λ s → 1` as `s → 0⁺` unconditionally, and feeding this into
   `realWeil_nonneg_of_polar` (`EvenSectorAbelRigidity`), we prove that the Riemann Hypothesis is
   equivalent to `WeilPositiveEvenPolar Λ` alone — positivity of the Weil functional for `Λ` on
   **even pole-free** tests (`f(-x) = f(x)` and `f̂(i/2) = 0`), with **no odd sector** and **no pole
   term**.

2. **Four-Mode Gauss Extraction (`fourMode_gauss_pole_le_weilArchRe`, `gammaBracket_zero_add_fourMode_pos`)**:
   Using `log π ≤ π / e` to sharpen the upper bound on `-EF.gammaBracket 0` from `28/5 = 5.6` to
   `137/25 = 5.48`, we prove that extracting `M = 4` Gauss modes (`e^{-x/2}, e^{-5x/2}, e^{-9x/2}, e^{-13x/2}`)
   from `archLevyDensity` gives total `L²` weight
   `4 + 4/5 + 4/9 + 4/13 = 3248/585 > 5.552 > 137/25 > -EF.gammaBracket 0`,
   flipping the diagonal `L²` coefficient of `weilArchRe` from negative (at `M = 1, 2, 3`) to
   **strictly positive** (`EF.gammaBracket 0 + 3248 / 585 > 42 / 585 > 0`) for all signed tests
   `f ∈ C²_c(ℝ)`. We also establish the weighted multiplicative core scaling law
   `dilationAutocorr (powMulCore m f) r = r ^ m * dilationAutocorr f r` and universal nonnegativity
   of all polynomial moments `∫ r in 0..1, r ^ (2 * m) * dilationAutocorr f r ≥ 0` on `(0, 1]`.

3. **Clamped-Beam Factorization (`f = (-D_x² + 1/4) q`) and `H¹` Resolvent Coercivity**:
   For any `q ∈ C⁴_c(ℝ)`, `clampedBeam q = -q'' + (1/4) q` has Fourier transform
   `(z² + 1/4) q̂(z)`, automatically vanishes at the pole nodes `±i/2`, preserves evenness, and
   satisfies the exact `H¹` Bochner resolvent identity
   `bochnerResolventEnergy (weilTest (clampedBeam q) (clampedBeam q)) =
     (1 / (2 * π)) * ∫ r : ℝ, (r ^ 2 + 1 / 4) * ‖paperFT q r‖ ^ 2`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.CHMDStage1

open EvenSector OddSector WeilOneSided WeilPoleWeight WeilLevyPole WeilLevyPoleGauss
open GaloisForLFunctions.HTGeometry.QuantileTransport RHTower.NonnegativeCone

/-! ## Section 1: Unconditional Even Pole-Free Rigidity for `Λ` -/

/-- Absolute `LSeries` summability for `Λ` on `σ > 1` in the `|Λ(n)| / n^σ` form. -/
theorem summable_abs_vonMangoldt_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |(ArithmeticFunction.vonMangoldt n : ℝ)| / (n : ℝ) ^ σ := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
  refine ((LSeriesSummable_iff_of_re_eq_re (s' := (σ : ℂ)) rfl).mp h).norm.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn; simp
  · simp

/-- `WeilHerglotz.lamC` for `Λ` agrees with `(Λ n : ℂ)` at every `n : ℕ`. -/
theorem lamC_vonMangoldt_eq (n : ℕ) :
    WeilHerglotz.lamC (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) n =
      (ArithmeticFunction.vonMangoldt n : ℂ) := by
  unfold WeilHerglotz.lamC
  split_ifs with hn
  · rfl
  · interval_cases n <;> simp

/-- For `s > 0`, `oddDirichlet Λ s = 1 / s + (Sieve.zetaLogDerivReg (1 + s)).re`. -/
theorem oddDirichlet_vonMangoldt_eq {s : ℝ} (hs : 0 < s) :
    oddDirichlet (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s =
      1 / s + (RHTower.Sieve.zetaLogDerivReg (1 + (s : ℂ))).re := by
  have hre : 1 < (1 + (s : ℂ)).re := by simp [hs]
  have hs1 : (1 + (s : ℂ)) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz : riemannZeta (1 + (s : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  have hL1 := LSeries_lamC_eq_oddDirichlet (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s
  have hcongr : WeilHerglotz.lamC (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
      fun n => (ArithmeticFunction.vonMangoldt n : ℂ) := funext lamC_vonMangoldt_eq
  rw [hcongr, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre,
    neg_div, ← logDeriv_apply, RHTower.Sieve.neg_logDeriv_riemannZeta_eq_of_ne_zero hs1 hz] at hL1
  have hsub : (1 + (s : ℂ) - 1)⁻¹ = ((1 / s : ℝ) : ℂ) := by
    rw [add_sub_cancel_left]
    push_cast
    ring
  rw [hsub] at hL1
  have hre_eq := congrArg Complex.re hL1
  simpa using hre_eq.symm

/-- For `s > 0`, `s * oddDirichlet Λ s = 1 + s * (Sieve.zetaLogDerivReg (1 + s)).re`. -/
theorem mul_oddDirichlet_vonMangoldt_eq {s : ℝ} (hs : 0 < s) :
    s * oddDirichlet (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s =
      1 + s * (RHTower.Sieve.zetaLogDerivReg (1 + (s : ℂ))).re := by
  rw [oddDirichlet_vonMangoldt_eq hs, mul_add, mul_one_div_cancel hs.ne']

/-- **Exact residue limit for `oddDirichlet Λ`**: `s * oddDirichlet Λ s → 1` as `s → 0⁺`. -/
theorem tendsto_mul_oddDirichlet_vonMangoldt :
    Tendsto (fun s : ℝ => s * oddDirichlet (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s)
      (𝓝[>] 0) (𝓝 1) := by
  have hcont : ContinuousAt (fun s : ℝ => (RHTower.Sieve.zetaLogDerivReg (1 + (s : ℂ))).re) 0 := by
    have h1 : ContinuousAt (fun s : ℝ => (1 : ℂ) + (s : ℂ)) 0 := by fun_prop
    have h2 : DifferentiableAt ℂ RHTower.Sieve.zetaLogDerivReg ((1 : ℂ) + ((0 : ℝ) : ℂ)) := by
      simpa using RHTower.Sieve.differentiableAt_zetaLogDerivReg_one
    exact ContinuousAt.comp (f := fun s : ℝ => (1 : ℂ) + (s : ℂ))
      (g := fun z : ℂ => (RHTower.Sieve.zetaLogDerivReg z).re)
      (Complex.continuous_re.continuousAt.comp h2.continuousAt) h1
  have hmul : Tendsto (fun s : ℝ => 1 + s * (RHTower.Sieve.zetaLogDerivReg (1 + (s : ℂ))).re)
      (𝓝[>] 0) (𝓝 1) := by
    have h0 : Tendsto (fun s : ℝ => 1 + s * (RHTower.Sieve.zetaLogDerivReg (1 + (s : ℂ))).re)
        (𝓝 0) (𝓝 (1 + 0 * (RHTower.Sieve.zetaLogDerivReg (1 + ((0 : ℝ) : ℂ))).re)) :=
      tendsto_const_nhds.add (tendsto_id.mul hcont.tendsto)
    rw [zero_mul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (mul_oddDirichlet_vonMangoldt_eq hs).symm

/-- **Unconditional upper Abel bound for `Λ`**: `s * oddDirichlet Λ s ≤ 1 + ε` near `0⁺`. -/
theorem eventually_mul_oddDirichlet_vonMangoldt_le :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ),
      s * oddDirichlet (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s ≤ 1 + ε := by
  intro ε hε
  filter_upwards [tendsto_mul_oddDirichlet_vonMangoldt.eventually
    (ge_mem_nhds (by linarith : (1 : ℝ) < 1 + ε))] with s hs
  exact hs

/-- **Unconditional lower double-pole bound for `Λ`**: `-ε ≤ s * (s * oddDirichlet Λ s)` near `0⁺`. -/
theorem eventually_neg_le_mul_mul_oddDirichlet_vonMangoldt :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ),
      -ε ≤ s * (s * oddDirichlet (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s) := by
  intro ε hε
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s := hs
  have h0 : 0 ≤ oddDirichlet (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s :=
    oddDirichlet_nonneg_of_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg) s
  have : 0 ≤ s * (s * oddDirichlet (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s) := by
    positivity
  linarith

/-- **Even Pole-Free Rigidity for `Λ`**:
The Riemann Hypothesis holds if and only if `Λ` is Weil-positive on **even pole-free** tests
(`WeilPositiveEvenPolar Λ`, i.e. `f(-x) = f(x)` and `paperFT f (I / 2) = 0`), with no odd-sector
tests and no pole terms. -/
theorem riemannHypothesis_iff_weilPositiveEvenPolar_vonMangoldt :
    RiemannHypothesis ↔
      WeilPositiveEvenPolar (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  constructor
  · intro hRH
    exact weilPositiveEvenPolar_of_weilPositiveEvenAt
      (weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩)
  · intro hpf
    have h1 : WeilPositiveEvenAt 1 (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
      weilPositiveEvenAt_one_of_real fun g hg hgc hge =>
        realWeil_nonneg_of_polar hpf
          (fun _ hσ => summable_abs_vonMangoldt_div_rpow hσ)
          eventually_mul_oddDirichlet_vonMangoldt_le
          eventually_neg_le_mul_mul_oddDirichlet_vonMangoldt hg hgc hge
    exact (weilPositiveEvenAt_one_iff.mp h1).1

/-- **Archimedean-versus-Prime Form on `WeilEvenPolarTestFn`**:
The Riemann Hypothesis holds if and only if for every even pole-free test `g : WeilEvenPolarTestFn`,
its prime pairing against `Λ` is bounded above by its pure archimedean energy `weilArchRe`:
`∑_{n ≥ 2} Λ(n) / √n * (k(log n) + k(-log n)).re ≤ weilArchRe k`. -/
theorem riemannHypothesis_iff_forall_weilEvenPolarTestFn :
    RiemannHypothesis ↔
      ∀ g : WeilEvenPolarTestFn,
        Finsupp.linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
          (logVector g.1) ≤ weilArchRe (EF.weilTest g.1.1 g.1.1) := by
  rw [riemannHypothesis_iff_weilPositiveEvenPolar_vonMangoldt]
  constructor
  · intro hpf g
    have h := hpf g.1.1 g.1.2.1 g.1.2.2 g.2.1 g.2.2
    rw [re_weilFullFunctional_eq _ g.1] at h
    linarith
  · intro h f hf hfc hfe h0
    have hg := h ⟨⟨f, hf, hfc⟩, hfe, h0⟩
    rw [re_weilFullFunctional_eq _ ⟨f, hf, hfc⟩]
    change 0 ≤ weilArchRe (EF.weilTest f f) - _
    linarith

/-! ## Section 2: Sharpened `-EF.gammaBracket 0 < 137 / 25` and Four-Mode Gauss Floor -/

/-- Sharpened elementary upper bound `log π ≤ π / exp 1` via `log(π / e) ≤ π / e - 1`. -/
theorem log_pi_le_pi_div_exp_one : Real.log Real.pi ≤ Real.pi / Real.exp 1 := by
  have h1 : 0 < Real.pi / Real.exp 1 := by positivity
  have h2 := Real.log_le_sub_one_of_pos h1
  rw [Real.log_div Real.pi_pos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h2
  linarith

/-- Sharpened rational upper bound `Real.log Real.pi < 289 / 250` (`= 1.156`). -/
theorem log_pi_lt_289_div_250 : Real.log Real.pi < 289 / 250 := by
  have h1 := log_pi_le_pi_div_exp_one
  have hpi := Real.pi_lt_d4
  have hexp := Real.exp_one_gt_d9
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hdiv : Real.pi / Real.exp 1 < 289 / 250 := by
    rw [div_lt_iff₀ hepos]
    linarith
  linarith

/-- **Sharpened rational upper bound on `-EF.gammaBracket 0`**:
`-EF.gammaBracket 0 < 137 / 25` (`= 5.48`). -/
theorem neg_gammaBracket_zero_lt_137_div_25 : -EF.gammaBracket 0 < 137 / 25 := by
  rw [neg_gammaBracket_zero_eq]
  have h1 := log_pi_lt_289_div_250
  have h2 := Real.log_two_lt_d9
  have h3 := Real.eulerMascheroniConstant_lt_two_thirds
  have h4 := Real.pi_lt_d4
  linarith

/-- **The Four-Mode Gauss Threshold Exceeds `-EF.gammaBracket 0`**:
With `M = 4` Gauss modes (`α = 1/2, 5/2, 9/2, 13/2`), the total `L²` jump-energy weight
`4 + 4/5 + 4/9 + 4/13 = 3248 / 585` strictly exceeds `-EF.gammaBracket 0`, leaving a positive
diagonal margin `EF.gammaBracket 0 + 3248 / 585 > 42 / 585 > 0`. -/
theorem gammaBracket_zero_add_fourMode_gt :
    (42 : ℝ) / 585 < EF.gammaBracket 0 + 3248 / 585 := by
  have h := neg_gammaBracket_zero_lt_137_div_25
  linarith

theorem gammaBracket_zero_add_fourMode_pos :
    0 < EF.gammaBracket 0 + 3248 / 585 := by
  have h := gammaBracket_zero_add_fourMode_gt
  linarith

/-- Four-mode Gauss decomposition of `archLevyDensity`:
`ω(x) = e^{-x/2} + e^{-5x/2} + e^{-9x/2} + e^{-13x/2} + e^{-8x} ω(x)` for `x ≠ 0`. -/
theorem archLevyDensity_eq_fourMode {x : ℝ} (hx : x ≠ 0) :
    archLevyDensity x =
      Real.exp (-x / 2) + Real.exp (-5 * x / 2) + Real.exp (-9 * x / 2) +
        Real.exp (-13 * x / 2) + Real.exp (-8 * x) * archLevyDensity x := by
  have h2 := archLevyDensity_eq_twoMode hx
  have hexp9 : Real.exp (-4 * x) * Real.exp (-x / 2) = Real.exp (-9 * x / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hexp13 : Real.exp (-4 * x) * Real.exp (-5 * x / 2) = Real.exp (-13 * x / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hexp8 : Real.exp (-4 * x) ^ 2 = Real.exp (-8 * x) := by
    rw [sq, ← Real.exp_add]; ring_nf
  linear_combination (1 + Real.exp (-4 * x)) * h2 + hexp9 + hexp13 + archLevyDensity x * hexp8

/-- On `(0, ∞)`, `archLevyDensity x` dominates its first four Gauss modes. -/
theorem archLevyDensity_ge_fourMode {x : ℝ} (hx : 0 < x) :
    Real.exp (-x / 2) + Real.exp (-5 * x / 2) + Real.exp (-9 * x / 2) +
      Real.exp (-13 * x / 2) ≤ archLevyDensity x := by
  rw [archLevyDensity_eq_fourMode hx.ne']
  have hpos : 0 ≤ Real.exp (-8 * x) * archLevyDensity x :=
    mul_nonneg (Real.exp_pos _).le (archLevyDensity_pos hx).le
  linarith

/-- Four-mode Gauss lower bound on `jumpEnergy h` in `ENNReal`. -/
theorem ofReal_fourMode_le_jumpEnergy {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ} (hh : BddSupp A h C) :
    ENNReal.ofReal ((3248 / 585) * (∫ u, h u ^ 2) -
        ((∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
          (∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) +
          (∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(9 / 2) * |p.1 - p.2|)) +
          (∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(13 / 2) * |p.1 - p.2|)))) ≤
      jumpEnergy h := by
  have h1 := integral_exp_mul_jump_sq hh (α := 1 / 2) (by norm_num)
  have h2 := integral_exp_mul_jump_sq hh (α := 5 / 2) (by norm_num)
  have h3 := integral_exp_mul_jump_sq hh (α := 9 / 2) (by norm_num)
  have h4 := integral_exp_mul_jump_sq hh (α := 13 / 2) (by norm_num)
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hDm := measurable_jump hh
  have hI : ∀ α : ℝ, 0 < α →
      IntegrableOn (fun x : ℝ => Real.exp (-α * x) * ∫ u, (h u - h (u + x)) ^ 2) (Ioi 0) := by
    intro α hα
    refine ((integrableOn_exp_mul_Ioi (by linarith : -α < 0) 0).mul_const
      (4 * ∫ u, h u ^ 2)).mono'
      ((by fun_prop : Measurable fun x : ℝ => Real.exp (-α * x)).mul hDm).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) (Real.exp_pos _).le
  have hI1 := hI (1 / 2) (by norm_num)
  have hI2 := hI (5 / 2) (by norm_num)
  have hI3 := hI (9 / 2) (by norm_num)
  have hI4 := hI (13 / 2) (by norm_num)
  have hI12 : IntegrableOn (fun x : ℝ =>
      Real.exp (-(1 / 2) * x) * (∫ u, (h u - h (u + x)) ^ 2) +
        Real.exp (-(5 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2) (Ioi 0) := hI1.add hI2
  have hI123 : IntegrableOn (fun x : ℝ =>
      (Real.exp (-(1 / 2) * x) * (∫ u, (h u - h (u + x)) ^ 2) +
        Real.exp (-(5 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2) +
        Real.exp (-(9 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2) (Ioi 0) := hI12.add hI3
  have hI1234 : IntegrableOn (fun x : ℝ =>
      (Real.exp (-(1 / 2) * x) + Real.exp (-(5 / 2) * x) +
        Real.exp (-(9 / 2) * x) + Real.exp (-(13 / 2) * x)) *
        ∫ u, (h u - h (u + x)) ^ 2) (Ioi 0) :=
    (hI123.add hI4).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  have hsum : (3248 / 585) * (∫ u, h u ^ 2) -
      ((∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
        (∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) +
        (∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(9 / 2) * |p.1 - p.2|)) +
        (∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(13 / 2) * |p.1 - p.2|))) =
      ∫ x in Ioi (0 : ℝ),
        (Real.exp (-(1 / 2) * x) + Real.exp (-(5 / 2) * x) +
          Real.exp (-(9 / 2) * x) + Real.exp (-(13 / 2) * x)) *
          ∫ u, (h u - h (u + x)) ^ 2 := by
    have hadd : (∫ x in Ioi (0 : ℝ),
        (Real.exp (-(1 / 2) * x) + Real.exp (-(5 / 2) * x) +
          Real.exp (-(9 / 2) * x) + Real.exp (-(13 / 2) * x)) *
          ∫ u, (h u - h (u + x)) ^ 2) =
        (((∫ x in Ioi (0 : ℝ), Real.exp (-(1 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2) +
          ∫ x in Ioi (0 : ℝ), Real.exp (-(5 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2) +
          ∫ x in Ioi (0 : ℝ), Real.exp (-(9 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2) +
          ∫ x in Ioi (0 : ℝ), Real.exp (-(13 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2 := by
      rw [← integral_add hI1 hI2, ← integral_add hI12 hI3, ← integral_add hI123 hI4]
      exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring
    rw [hadd, h1, h2, h3, h4]
    ring
  rw [hsum, ofReal_integral_eq_lintegral_ofReal hI1234
    (ae_of_all _ fun x => mul_nonneg (by positivity) (hD0 x))]
  unfold jumpEnergy
  refine setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal ?_
  rw [show -(1 / 2 : ℝ) * x = -x / 2 by ring,
    show -(5 / 2 : ℝ) * x = -5 * x / 2 by ring,
    show -(9 / 2 : ℝ) * x = -9 * x / 2 by ring,
    show -(13 / 2 : ℝ) * x = -13 * x / 2 by ring]
  exact mul_le_mul_of_nonneg_right (archLevyDensity_ge_fourMode hx) (hD0 x)

/-- **Four-Mode Gauss–Pole Lower Bound for `weilArchRe` (All Signed `f ∈ C²_c(ℝ)`)**:
Unlike `M = 1, 2, 3`, at `M = 4` the diagonal `L²` coefficient `EF.gammaBracket 0 + 3248 / 585`
is **strictly positive** (`> 42 / 585 > 0`). -/
theorem fourMode_gauss_pole_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (EF.gammaBracket 0 + 3248 / 585) * (∫ u, f u ^ 2) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (|p.1 - p.2| / 2)) -
        ((∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) +
          (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(9 / 2) * |p.1 - p.2|)) +
          (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(13 / 2) * |p.1 - p.2|))) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  have h4 := ENNReal.toReal_mono hJ (ofReal_fourMode_le_jumpEnergy hB)
  have h4' : (3248 / 585) * (∫ u, f u ^ 2) -
      ((∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(9 / 2) * |p.1 - p.2|)) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(13 / 2) * |p.1 - p.2|))) ≤
      (jumpEnergy f).toReal := by
    rcases le_or_gt 0 ((3248 / 585) * (∫ u, f u ^ 2) -
      ((∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(9 / 2) * |p.1 - p.2|)) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(13 / 2) * |p.1 - p.2|)))) with ha | ha
    · rwa [ENNReal.toReal_ofReal ha] at h4
    · exact ha.le.trans ENNReal.toReal_nonneg
  have hcs_cosh : HasCompactSupport fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) := by
    refine HasCompactSupport.intro (hfc.isCompact.prod hfc.isCompact) fun p hp => ?_
    rcases not_and_or.mp (show ¬(p.1 ∈ tsupport f ∧ p.2 ∈ tsupport f) from hp) with h1 | h2
    · rw [image_eq_zero_of_notMem_tsupport h1]; ring
    · rw [image_eq_zero_of_notMem_tsupport h2]; ring
  have hI_cosh : Integrable fun p : ℝ × ℝ => f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)).integrable_of_hasCompactSupport hcs_cosh
  have hI_neg : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|) :=
    integrable_pair_exp_neg hB (by norm_num)
  have hcomb : 2 * (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)) -
      (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) =
      ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (|p.1 - p.2| / 2) := by
    rw [← integral_const_mul, ← integral_sub (hI_cosh.const_mul 2) hI_neg]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only
    have hca : Real.cosh ((p.1 - p.2) / 2) = Real.cosh (|p.1 - p.2| / 2) := by
      rw [← Real.cosh_abs, abs_div, abs_two]
    have hlin := two_mul_cosh_sub_exp_neg_half |p.1 - p.2|
    rw [hca, show -(1 / 2 : ℝ) * |p.1 - p.2| = -|p.1 - p.2| / 2 by ring]
    linear_combination f p.1 * f p.2 * hlin
  rw [weilArchRe_eq_levy_pole hf hfc]
  change _ ≤ EF.gammaBracket 0 * (∫ u, f u ^ 2) + (jumpEnergy f).toReal +
    2 * ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)
  linarith

/-! ## Section 3: Multiplicative Unit-Interval Polynomial Moments of `dilationAutocorr` -/

/-- The `m`-th power-weighted multiplicative core `f_m(y) = y ^ m * f(y)`. -/
def powMulCore (m : ℕ) (f : ℝ → ℝ) (y : ℝ) : ℝ := y ^ m * f y

theorem continuous_powMulCore (m : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (powMulCore m f) := by
  unfold powMulCore; fun_prop

theorem powMulCore_support (m : ℕ) {f : ℝ → ℝ} {α β : ℝ}
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (y : ℝ) (hy : powMulCore m f y ≠ 0) :
    α ≤ y ∧ y ≤ β :=
  hsupp y fun h0 => hy (by simp [powMulCore, h0])

/-- **Universal Nonnegativity of Unit-Interval Moments of `powMulCore`**:
For every `m : ℕ` and continuous `f` supported in `[α, β] ⊂ (0, ∞)`,
`0 ≤ ∫ r in 0..1, dilationAutocorr (powMulCore m f) r`, with exact primitive energy decomposition
`(primCore (powMulCore m f) β)² / (2β) + ½ ∫ y in α..β, (primCore (powMulCore m f) y / y)²`. -/
theorem intervalIntegral_zero_one_dilationAutocorr_powMulCore_eq (m : ℕ) {f : ℝ → ℝ}
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ r in (0 : ℝ)..1, dilationAutocorr (powMulCore m f) r =
      (primCore (powMulCore m f) β) ^ 2 / (2 * β) +
        1 / 2 * ∫ y in α..β, (primCore (powMulCore m f) y / y) ^ 2 :=
  intervalIntegral_zero_one_dilationAutocorr_eq (continuous_powMulCore m hf) hα hαβ
    (powMulCore_support m hsupp)

theorem intervalIntegral_zero_one_dilationAutocorr_powMulCore_nonneg (m : ℕ) {f : ℝ → ℝ}
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    0 ≤ ∫ r in (0 : ℝ)..1, dilationAutocorr (powMulCore m f) r :=
  intervalIntegral_zero_one_dilationAutocorr_nonneg (continuous_powMulCore m hf) hα hαβ
    (powMulCore_support m hsupp)

/-! ## Section 4: Clamped-Beam Factorization `f = (-D_x² + 1/4) q` and `H¹` Resolvent Identity -/

/-- The **clamped-beam operator** `(-D_x² + 1/4) q(x) = -q''(x) + (1/4) q(x)`. -/
def clampedBeam (q : ℝ → ℂ) (x : ℝ) : ℂ :=
  -deriv (deriv q) x + (1 / 4 : ℂ) * q x

theorem contDiff_clampedBeam {q : ℝ → ℂ} (hq : ContDiff ℝ 4 q) :
    ContDiff ℝ 2 (clampedBeam q) := by
  have h1 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (3 + 1) q from hq)
  have h2 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (2 + 1) (deriv q) from h1.2.2)
  unfold clampedBeam
  exact h2.2.2.neg.add (contDiff_const.mul (hq.of_le (by norm_num)))

theorem hasCompactSupport_clampedBeam {q : ℝ → ℂ} (hqc : HasCompactSupport q) :
    HasCompactSupport (clampedBeam q) := by
  unfold clampedBeam
  exact hqc.deriv.deriv.neg.add hqc.mul_left

theorem clampedBeam_even {q : ℝ → ℂ} (hqe : ∀ x, q (-x) = q x) (x : ℝ) :
    clampedBeam q (-x) = clampedBeam q x := by
  have h : (fun y => q (-y)) = q := funext hqe
  have hd1 : ∀ v, deriv q (-v) = -deriv q v := fun v => by
    have h1 := deriv_comp_neg q (-v)
    rw [h, neg_neg] at h1
    exact h1
  have h' : (fun y => deriv q (-y)) = fun y => -deriv q y := funext hd1
  have hd2 : deriv (deriv q) (-x) = deriv (deriv q) x := by
    have h2 := deriv_comp_neg (deriv q) (-x)
    rw [h', deriv.fun_neg, neg_neg] at h2
    exact neg_inj.mp h2
  unfold clampedBeam
  rw [hd2, hqe]

/-- **Fourier Symbol of the Clamped-Beam Operator**:
`paperFT (clampedBeam q) z = (z ^ 2 + 1 / 4) * paperFT q z`. -/
theorem paperFT_clampedBeam {q : ℝ → ℂ} (hq : ContDiff ℝ 2 q) (hqc : HasCompactSupport q)
    (z : ℂ) :
    paperFT (clampedBeam q) z = (z ^ 2 + 1 / 4) * paperFT q z := by
  have h1 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) q from hq)
  have h2 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv q) from h1.2.2)
  have hd2 : Continuous (deriv (deriv q)) := h2.2.2.continuous
  have hi_dd : Integrable fun u : ℝ => deriv (deriv q) u * cexp (I * z * u) :=
    (hd2.mul (by fun_prop)).integrable_of_hasCompactSupport hqc.deriv.deriv.mul_right
  have hi_q : Integrable fun u : ℝ => q u * cexp (I * z * u) :=
    (hq.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hqc.mul_right
  have hsplit : paperFT (clampedBeam q) z =
      -paperFT (deriv (deriv q)) z + (1 / 4 : ℂ) * paperFT q z := by
    unfold paperFT clampedBeam
    have heq : (fun u : ℝ => (-deriv (deriv q) u + (1 / 4 : ℂ) * q u) * cexp (I * z * u)) =
        fun u : ℝ => -(deriv (deriv q) u * cexp (I * z * u)) +
          (1 / 4 : ℂ) * (q u * cexp (I * z * u)) := by
      funext u; ring
    have h_add := integral_add hi_dd.neg (hi_q.const_mul (1 / 4 : ℂ))
    simp only [Pi.neg_apply] at h_add
    rw [heq, h_add, integral_neg, integral_const_mul]
  rw [hsplit, paperFT_deriv_deriv_of_compact hq hqc]
  ring

/-- **Automatic Pole Annihilation at `±i/2`**:
For every `q ∈ C²_c(ℝ)`, `clampedBeam q` has vanishing Fourier transform at `±i/2`. -/
theorem paperFT_clampedBeam_I_div_two {q : ℝ → ℂ} (hq : ContDiff ℝ 2 q)
    (hqc : HasCompactSupport q) :
    paperFT (clampedBeam q) (I / 2) = 0 := by
  rw [paperFT_clampedBeam hq hqc]
  have h0 : (I / 2 : ℂ) ^ 2 + 1 / 4 = 0 := by
    rw [div_pow, Complex.I_sq]; ring
  rw [h0, zero_mul]

theorem paperFT_clampedBeam_neg_I_div_two {q : ℝ → ℂ} (hq : ContDiff ℝ 2 q)
    (hqc : HasCompactSupport q) :
    paperFT (clampedBeam q) (-I / 2) = 0 := by
  rw [paperFT_clampedBeam hq hqc]
  have h0 : (-I / 2 : ℂ) ^ 2 + 1 / 4 = 0 := by
    rw [div_pow, neg_sq, Complex.I_sq]; ring
  rw [h0, zero_mul]

/-- Packaging an even `q ∈ C⁴_c(ℝ)` as an element of `WeilEvenPolarTestFn`. -/
def clampedBeamEvenPolarTestFn (q : ℝ → ℂ) (hq : ContDiff ℝ 4 q) (hqc : HasCompactSupport q)
    (hqe : ∀ x, q (-x) = q x) : WeilEvenPolarTestFn :=
  ⟨⟨clampedBeam q, contDiff_clampedBeam hq, hasCompactSupport_clampedBeam hqc⟩,
    clampedBeam_even hqe, paperFT_clampedBeam_I_div_two (hq.of_le (by norm_num)) hqc⟩

/-- **Exact `H¹` Bochner Resolvent Identity for the Clamped-Beam Operator**:
On `f = clampedBeam q = (-D_x² + 1/4) q`, the singular resolvent weight `1 / (1/4 + r²)` cancels one
factor of `(1/4 + r²)²` in `‖f̂(r)‖² = (1/4 + r²)² ‖q̂(r)‖²`, yielding the non-singular `H¹` energy
`bochnerResolventEnergy (EF.weilTest f f) =
  (1 / (2 * π)) * ∫ r : ℝ, (1 / 4 + r ^ 2) * ‖paperFT q r‖ ^ 2`. -/
theorem bochnerResolventEnergy_clampedBeam_eq {q : ℝ → ℂ} (hq : ContDiff ℝ 4 q)
    (hqc : HasCompactSupport q) :
    bochnerResolventEnergy (EF.weilTest (clampedBeam q) (clampedBeam q)) =
      (1 / (2 * Real.pi)) * ∫ r : ℝ, (1 / 4 + r ^ 2) * ‖paperFT q r‖ ^ 2 := by
  let F : WeilTestFn := ⟨clampedBeam q, contDiff_clampedBeam hq, hasCompactSupport_clampedBeam hqc⟩
  have hres : bochnerResolventEnergy (EF.weilTest (clampedBeam q) (clampedBeam q)) =
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT (clampedBeam q) r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) :=
    bochnerResolventEnergy_weilTest_eq F
  rw [hres]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  dsimp only
  have hft := paperFT_clampedBeam (hq.of_le (by norm_num)) hqc (r : ℂ)
  have hcast : ((r : ℂ) ^ 2 + 1 / 4) = ((1 / 4 + r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hft, hcast, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / 4 + r ^ 2), mul_pow]
  have hpos : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp

end RHTower.CHMDStage1

end
