import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge
import GaloisForLFunctions.SquareRootThreshold.LagGridsSeeAttainedTops
import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe
import GaloisForLFunctions.RHTower.CHMDExactParityBoundStateDimensionAndShiftedThetaOrthogonality
import GaloisForLFunctions.RHTower.JointAncestryTypicalAsymptoticAbscissa

/-!
# Cross-Corpus Wall-Sidestepping Synthesis for the Riemann Hypothesis

This module connects five previously separate umbrellas of the corpus (`RHTower`,
`SquareRootThreshold`, `BiScaleUncertainty`, `CHMDPolar`, and `ArithmeticPositivityTheory`)
into a unified two-pillar architecture that sidesteps the 15 single-route walls:

1. **CHMD Bound-State Finiteness Bridge and the Asymptotic Abscissa Law Dichotomy:**
   Proves `offLineZeros_finite_iff_finiteOffLine`, identifying `CHMDPolar.offLineZeros.Finite`
   (and hence `FiniteDimensional ℝ oddBoundStateSpace`, `FiniteDimensional ℝ evenBoundStateSpace`,
   and `FiniteDimensional ℝ boundStateSpace`) with `BacklundConverse.FiniteOffLine`,
   `EventualSlicePositivity`, and `EventualFilteredCentralGapBudget`. Consequently,
   finite-dimensionality of `oddBoundStateSpace` unconditionally implies `ZerosApproachLine` and
   `¬ JasOffLineChain`, and under `AsymptoticAbscissaLaw` the arithmetic resolvent satisfies the
   bound-state dichotomy `FiniteDimensional ℝ oddBoundStateSpace ↔ RiemannHypothesis`
   (`oddBoundStateSpace = ⊥ ∨ ¬ FiniteDimensional ℝ oddBoundStateSpace`).

2. **Subexponential and Constant-Bounded Discrete Lag Grids as `AsymptoticAbscissaLaw` Producers:**
   Generalizes `exists_re_gt_of_grid_lag_ge` (`SquareRootThreshold.LagGridsSeeAttainedTops`) to
   subexponential lower bounds `-(C * Real.exp (σ * (k * ℓ)))` for `0 ≤ σ < ρ₀.re - 1/2` on a
   single discrete lag grid `v = kℓ`, and proves that subexponential (or constant `-C`) lower
   bounds on a single geometric progression of prime windows `X = e^{kℓ}` unconditionally rule out
   attained tops (`¬ ∃ β₀ > 1/2, AttainedTop β₀`) and produce `AsymptoticAbscissaLaw`.

3. **Slack-Preserving Cubic-Spline Prime-Sum and One-Parameter Prime-Window Equivalences:**
   Connects `BiScaleUncertainty.CubicSplineUniversalProbe` and
   `SquareRootThreshold.OneParameterLagFamilyMeasuresTheAbscissa` to `RHTower`'s
   `XiZeroHalfPlaneBound` and `AsymptoticAbscissaLaw`, showing both that
   `∀ β > 0, XiZeroHalfPlaneBound β ↔ RiemannHypothesis` (retaining strictly positive exponential
   slack `e^{βτ}` at each individual `β > 0`) and that under `AsymptoticAbscissaLaw` every
   large-height abscissa receiver (`EventualHadamardPositivityRight (1/2 + β)`,
   `EventualFilteredCentralGapRate (β + β²/8)`) collapses to the global `splinePrimeSum` and
   `lagPrimeWindowRHS` bounds at rate `β`.

4. **Cross-Corpus Master Equivalence:**
   Combines all five umbrellas into an unconditional multi-route equivalence for
   `RiemannHypothesis`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators CompactlySupported ComplexConjugate
open _root_.Zeta23 _root_.RHTower
open _root_.RHTower.BacklundConverse _root_.RHTower.LindelofSparse
open _root_.RHTower.CHMDPolar _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.WeilOneSided _root_.RHTower.WeilWorkPBAP _root_.RHTower.WeilSpectral
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory

/-! ## Section 1: Bridging `zetaZeroConfig`, `XiZeroCopy`, `XiZeroHalfPlaneBound`, and `CHMDPolar` -/

/-- `zetaZeroConfig.carrier` is definitionally `{ρ : ℂ | IsNontrivialZero ρ}`. -/
theorem mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip {ρ : ℂ} :
    ρ ∈ zetaZeroConfig.carrier ↔ _root_.RHTower.xi ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · intro hρ
    refine ⟨_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr ⟨hρ.1, ?_⟩, hρ.2⟩
    intro n hn
    have h := congrArg Complex.re hn
    have h0 := hρ.2.1
    rw [h] at h0
    simp at h0
    linarith [(Nat.cast_nonneg (α := ℝ) n)]
  · rintro ⟨hxi, h0, h1⟩
    exact ⟨(_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1, h0, h1⟩

/-- Every zero of `ξ` lies in the open critical strip `0 < Re ρ < 1` and hence in `zetaZeroConfig.carrier`. -/
theorem mem_zetaZeroConfig_carrier_of_xi_eq_zero {ρ : ℂ} (hxi : _root_.RHTower.xi ρ = 0) :
    ρ ∈ zetaZeroConfig.carrier := by
  rw [mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip]
  have h1 : ρ.re < 1 := by
    by_contra h
    exact _root_.RHTower.xi_ne_zero_of_one_le_re (not_lt.mp h) hxi
  have h0 : 0 < ρ.re := by
    have hxi' : _root_.RHTower.xi (1 - ρ) = 0 := by
      rw [_root_.RHTower.xi_one_sub]; exact hxi
    have h1' : (1 - ρ).re < 1 := by
      by_contra h
      exact _root_.RHTower.xi_ne_zero_of_one_le_re (not_lt.mp h) hxi'
    simp only [sub_re, one_re] at h1'
    linarith
  exact ⟨hxi, h0, h1⟩

/-- Every `q : XiZeroCopy` has underlying zero `(q.1 : ℂ) ∈ zetaZeroConfig.carrier`. -/
theorem xiZeroCopy_mem_zetaZeroConfig_carrier (q : XiZeroCopy) :
    (q.1 : ℂ) ∈ zetaZeroConfig.carrier :=
  mem_zetaZeroConfig_carrier_of_xi_eq_zero (xi_xiZeroCopy_eq_zero q)

/-- `XiZeroHalfPlaneBound β` is equivalent to `∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + β`
and to `∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + β`. -/
theorem xiZeroHalfPlaneBound_iff_zetaZeroConfig_re_le (β : ℝ) :
    _root_.RHTower.XiZeroHalfPlaneBound β ↔
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + β :=
  ⟨fun h ρ hρ => h ρ (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).1,
   fun h ρ hxi => h ρ (mem_zetaZeroConfig_carrier_of_xi_eq_zero hxi)⟩

theorem xiZeroHalfPlaneBound_iff_xiZeroCopy_re_le (β : ℝ) :
    _root_.RHTower.XiZeroHalfPlaneBound β ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + β := by
  constructor
  · intro h q
    exact h (q.1 : ℂ) (xi_xiZeroCopy_eq_zero q)
  · intro h ρ hxi
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    rw [← hq]
    exact h q

/-- `RiemannHypothesis` is equivalent to `∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2`. -/
theorem riemannHypothesis_iff_zetaZeroConfig_onLine :
    RiemannHypothesis ↔ ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    xiZeroHalfPlaneBound_iff_zetaZeroConfig_re_le]
  constructor
  · intro h0 ρ hρ
    have h1 := h0 ρ hρ
    have h2 := h0 (reflect ρ) (zetaZeroConfig.reflect_mem ρ hρ)
    rw [Zeta23.reflect_re] at h2
    linarith
  · intro hon ρ hρ
    rw [hon ρ hρ, add_zero]

/-- **Positive-Slack Half-Plane Intersection Equivalence:**
`RiemannHypothesis` holds if and only if `XiZeroHalfPlaneBound β` holds for every `β > 0`. -/
theorem riemannHypothesis_iff_forall_pos_xiZeroHalfPlaneBound :
    RiemannHypothesis ↔ ∀ β : ℝ, 0 < β → _root_.RHTower.XiZeroHalfPlaneBound β := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  constructor
  · intro h0 β hβ ρ hxi
    have := h0 ρ hxi
    linarith
  · intro hall ρ hxi
    rw [add_zero]
    by_contra hgt
    push Not at hgt
    have := hall ((ρ.re - 1 / 2) / 2) (by linarith) ρ hxi
    linarith

/-- **Unconditional Bridge between `CHMDPolar.offLineZeros.Finite` and `BacklundConverse.FiniteOffLine`.**
The off-line nontrivial zero set of `CHMDPolar` is finite if and only if the off-line `XiZeroCopy`
set of `BacklundConverse` is finite. -/
theorem offLineZeros_finite_iff_finiteOffLine :
    offLineZeros.Finite ↔ FiniteOffLine := by
  constructor
  · intro hfin
    obtain ⟨M, hM⟩ := (hfin.image fun ρ : ℂ => |ρ.im|).bddAbove
    refine (xiZeroBall (⌈|M| + 1⌉₊)).finite_toSet.subset fun q hq => ?_
    simp only [Finset.mem_coe, mem_xiZeroBall]
    have hq_im : (xiSpectralPoint q).im ≠ 0 := hq
    have hre_ne : (q.1 : ℂ).re ≠ 1 / 2 := by
      intro hre
      apply hq_im
      rw [spectral_im_eq, hre, sub_self]
    have hmem : (q.1 : ℂ) ∈ offLineZeros :=
      ⟨xiZeroCopy_mem_zetaZeroConfig_carrier q, hre_ne⟩
    have him_le : |(q.1 : ℂ).im| ≤ M := hM ⟨(q.1 : ℂ), hmem, rfl⟩
    have h1 := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    have h2 := abs_spectral_im_lt_half q
    have h3 : |M| + 1 ≤ (⌈|M| + 1⌉₊ : ℝ) := Nat.le_ceil _
    have h4 : |(xiSpectralPoint q).re| ≤ |M| := by
      rw [spectral_re_eq]
      exact him_le.trans (le_abs_self M)
    linarith
  · intro hF
    refine (hF.image fun q : XiZeroCopy => (q.1 : ℂ)).subset fun ρ hρ => ?_
    have hxi : _root_.RHTower.xi ρ = 0 :=
      (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ.1).1
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    refine ⟨q, ?_, hq⟩
    show (xiSpectralPoint q).im ≠ 0
    rw [spectral_im_eq, hq]
    exact sub_ne_zero.mpr hρ.2.symm

/-- **Finite-Dimensionality of `oddBoundStateSpace` is Equivalent to `FiniteOffLine`,
`EventualSlicePositivity`, and `EventualFilteredCentralGapBudget`.** -/
theorem finiteDimensional_oddBoundStateSpace_iff_finiteOffLine :
    FiniteDimensional ℝ oddBoundStateSpace ↔ FiniteOffLine :=
  offLineZeros_finite_iff_finiteDimensional_oddBoundStateSpace.symm.trans
    offLineZeros_finite_iff_finiteOffLine

theorem finiteDimensional_oddBoundStateSpace_iff_eventualSlicePositivity :
    FiniteDimensional ℝ oddBoundStateSpace ↔ EventualSlicePositivity :=
  finiteDimensional_oddBoundStateSpace_iff_finiteOffLine.trans
    eventualSlicePositivity_iff_finiteOffLine.symm

theorem finiteDimensional_oddBoundStateSpace_iff_eventualFilteredCentralGapBudget :
    FiniteDimensional ℝ oddBoundStateSpace ↔ EventualFilteredCentralGapBudget :=
  finiteDimensional_oddBoundStateSpace_iff_finiteOffLine.trans
    eventualFilteredCentralGapBudget_iff_finiteOffLine.symm

/-- **Finite-Dimensional CHMD Bound-State Spaces Give `ZerosApproachLine` and Exclude Off-Line Chains.** -/
theorem zerosApproachLine_of_finiteDimensional_oddBoundStateSpace
    (hfin : FiniteDimensional ℝ oddBoundStateSpace) : ZerosApproachLine :=
  zerosApproachLine_of_finiteOffLine
    (finiteDimensional_oddBoundStateSpace_iff_finiteOffLine.mp hfin)

theorem zerosApproachLine_of_finiteDimensional_evenBoundStateSpace
    (hfin : FiniteDimensional ℝ evenBoundStateSpace) : ZerosApproachLine :=
  zerosApproachLine_of_finiteOffLine
    (offLineZeros_finite_iff_finiteOffLine.mp
      (offLineZeros_finite_iff_finiteDimensional_evenBoundStateSpace.mpr hfin))

theorem zerosApproachLine_of_finiteDimensional_boundStateSpace
    (hfin : FiniteDimensional ℝ boundStateSpace) : ZerosApproachLine :=
  zerosApproachLine_of_finiteOffLine
    (offLineZeros_finite_iff_finiteOffLine.mp
      (offLineZeros_finite_iff_finiteDimensional_boundStateSpace.mpr hfin))

theorem not_jasOffLineChain_of_finiteDimensional_oddBoundStateSpace
    (hfin : FiniteDimensional ℝ oddBoundStateSpace) : ¬ _root_.RHTower.JasOffLineChain := by
  intro hc
  have hAAL : AsymptoticAbscissaLaw :=
    asymptoticAbscissaLaw_of_offLine_chain hc.2
  have hRH : RiemannHypothesis :=
    riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨zerosApproachLine_of_finiteDimensional_oddBoundStateSpace hfin, hAAL⟩
  obtain ⟨q, hq⟩ := hc.1
  exact hq (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)

/-- **CHMD Bound-State Dimension Dichotomy under `AsymptoticAbscissaLaw`:**
Under `AsymptoticAbscissaLaw`, the arithmetic resolvent cannot have a non-trivial finite-dimensional
odd bound-state space: `oddBoundStateSpace` is finite-dimensional if and only if `RiemannHypothesis`
holds (i.e. `oddBoundStateSpace = ⊥`). -/
theorem finiteDimensional_oddBoundStateSpace_iff_riemannHypothesis_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) :
    FiniteDimensional ℝ oddBoundStateSpace ↔ RiemannHypothesis := by
  constructor
  · intro hfin
    exact riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨zerosApproachLine_of_finiteDimensional_oddBoundStateSpace hfin, hAAL⟩
  · intro hRH
    rw [riemannHypothesis_iff_oddBoundStateSpace_eq_bot.mp hRH]
    infer_instance

theorem oddBoundStateSpace_eq_bot_or_not_finiteDimensional_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) :
    oddBoundStateSpace = ⊥ ∨ ¬ FiniteDimensional ℝ oddBoundStateSpace := by
  by_cases hfin : FiniteDimensional ℝ oddBoundStateSpace
  · left
    exact riemannHypothesis_iff_oddBoundStateSpace_eq_bot.mp
      ((finiteDimensional_oddBoundStateSpace_iff_riemannHypothesis_of_asymptoticAbscissaLaw hAAL).mp hfin)
  · exact Or.inr hfin

theorem riemannHypothesis_iff_finiteDimensional_oddBoundStateSpace_and_asymptoticAbscissaLaw :
    RiemannHypothesis ↔ FiniteDimensional ℝ oddBoundStateSpace ∧ AsymptoticAbscissaLaw := by
  constructor
  · intro hRH
    refine ⟨?_, asymptoticAbscissaLaw_of_riemannHypothesis hRH⟩
    rw [riemannHypothesis_iff_oddBoundStateSpace_eq_bot.mp hRH]
    infer_instance
  · rintro ⟨hfin, hAAL⟩
    exact (finiteDimensional_oddBoundStateSpace_iff_riemannHypothesis_of_asymptoticAbscissaLaw hAAL).mp hfin

/-! ## Section 2: Subexponential & Constant-Bounded Discrete Lag Grids Produce `AsymptoticAbscissaLaw` -/

/-- **Subexponential Discrete Lag Grids See Attained Tops.**
Generalizing `exists_re_gt_of_grid_lag_ge` from a constant lower bound `-C` to an exponential
lower bound `-(C * Real.exp (σ * (k * ℓ)))` with `0 ≤ σ < ρ₀.re - 1 / 2`: on any non-resonant
lag grid `v = kℓ` (`k ≥ N`), an exponential lower bound of rate strictly smaller than `ρ₀.re - 1/2`
still decays under `e^{-(ρ₀.re - 1/2)kℓ}` normalization and forces a strictly deeper zero. -/
theorem exists_re_gt_of_grid_lag_ge_neg_exp (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps Z)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre₀ : 1 / 2 < ρ₀.re)
    {σ C : ℝ} {N : ℕ} (hσ0 : 0 ≤ σ) (hσD : σ < ρ₀.re - 1 / 2)
    (hm : ∀ k : ℕ, N ≤ k → -(C * Real.exp (σ * (k * ℓ))) ≤
      (Z.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
        (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re) :
    ∃ ρ ∈ Z.carrier, ρ₀.re < ρ.re := by
  classical
  by_contra hno
  push Not at hno
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs := modScaledBump_support hw 0
  set D := ρ₀.re - 1 / 2 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hDσ : 0 < D - σ := by rw [hD]; linarith
  set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
  haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
  have hDs : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
    have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hreD : ∀ z : ι, (z : ℂ).re ≤ D := fun z => by
    rcases mem_of_evenCoeff_ne_zero z.2 with h | h
    · have := hno _ h; simp at this; linarith
    · have := hno _ h; simp at this; linarith
  set W : ι → ℂ := fun z => cexp (((z : ℂ) - D) * ℓ) with hWdef
  have hWre : ∀ z : ι, ‖W z‖ = Real.exp (((z : ℂ).re - D) * ℓ) := fun z => by
    rw [hWdef, Complex.norm_exp]; simp
  have hWn : ∀ z : ι, ‖W z‖ ≤ 1 := fun z => by
    rw [hWre, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hreD z]) hℓ.le
  have hgrid : ∀ k : ℕ, ∑' z : ι, evenCoeff Z b z * W z ^ k =
      ((Real.exp (-D * (k * ℓ)) * (2 * (lagStructure Z b (k * ℓ)).re) : ℝ) : ℂ) := fun k => by
    have hsub :
        Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * ((k * ℓ : ℝ) : ℂ))) ⊆ ι :=
      fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * ((k * ℓ : ℝ) : ℂ)) = 0 by
        rw [h0, zero_mul])
    rw [Complex.ofReal_mul, (two_re_lagStructure_eq Z hZ hb hbs (k * ℓ)).2,
      ← tsum_subtype_eq_of_support_subset hsub, ← tsum_mul_left]
    refine tsum_congr fun z => ?_
    have e : W z ^ k = cexp (((-D * (k * ℓ) : ℝ) : ℂ)) * cexp ((z : ℂ) * ((k * ℓ : ℝ) : ℂ)) := by
      rw [hWdef, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e, Complex.ofReal_exp]
    ring
  have hreal : ∀ k : ℕ, (∑' z : ι, evenCoeff Z b z * W z ^ k).im = 0 := fun k => by
    rw [hgrid, Complex.ofReal_im]
  have hlim : ∀ ε > 0, ∀ᶠ k : ℕ in atTop, (∑' z : ι, evenCoeff Z b z * W z ^ k).re ≤ ε := by
    intro ε hε
    set A := max (2 * (lagStructure Z b 0).re) 0 + max C 0 with hA
    have hexp : Tendsto (fun k : ℕ => Real.exp (-(D - σ) * (k * ℓ)) * A) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => -(D - σ) * (k * ℓ)) atTop atBot := by
        have : Tendsto (fun k : ℕ => (D - σ) * ℓ * (k : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos hDσ hℓ)
        refine (tendsto_neg_atTop_atBot.comp this).congr fun k => ?_
        simp only [Function.comp]
        ring
      simpa using (Real.tendsto_exp_atBot.comp h1).mul_const A
    filter_upwards [eventually_ge_atTop N, (tendsto_order.1 hexp).2 ε hε] with k hk hk'
    rw [hgrid, Complex.ofReal_re]
    have h := hm k hk
    rw [re_W_lag_eq Z hZ hb hbs] at h
    have hkℓ0 : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le
    have hexp1 : 1 ≤ Real.exp (σ * (k * ℓ)) := Real.one_le_exp (mul_nonneg hσ0 hkℓ0)
    have hA1 : 2 * (lagStructure Z b 0).re ≤ max (2 * (lagStructure Z b 0).re) 0 * Real.exp (σ * (k * ℓ)) :=
      (le_max_left _ _).trans (le_mul_of_one_le_right (le_max_right _ _) hexp1)
    have hC1 : C * Real.exp (σ * (k * ℓ)) ≤ max C 0 * Real.exp (σ * (k * ℓ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    have h2 : 2 * (lagStructure Z b (k * ℓ)).re ≤ A * Real.exp (σ * (k * ℓ)) := by
      rw [hA, add_mul]
      linarith
    have h3 : Real.exp (-D * (k * ℓ)) * (A * Real.exp (σ * (k * ℓ))) =
        Real.exp (-(D - σ) * (k * ℓ)) * A := by
      rw [mul_left_comm, ← Real.exp_add, mul_comm A]
      congr 2
      ring
    exact ((mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le).trans_eq h3).trans hk'.le
  set z₀ : ℂ := ρ₀ - 1 / 2 with hz₀def
  have hz₀ : evenCoeff Z b z₀ ≠ 0 :=
    evenCoeff_modScaledBump_zero_sub_half_ne_zero Z hw hρ₀ (hgood ρ₀ hρ₀ (ne_of_gt hre₀))
  have hz₀re : z₀.re = D := by rw [hz₀def, hD]; simp
  have hWz₀ : ‖W ⟨z₀, hz₀⟩‖ = 1 := by
    rw [hWre]; simp only [hz₀re, sub_self, zero_mul, Real.exp_zero]
  have hsumι : Summable fun z : ι => ‖evenCoeff Z b z‖ := hDs.subtype ι
  have key := norm_tsum_ite_le_of_limsup_nonpos hsumι hWn hreal hlim hWz₀
  have hL : (∑' z : ι, if W z = W ⟨z₀, hz₀⟩ then evenCoeff Z b z else 0) =
      evenCoeff Z b z₀ := by
    rw [tsum_eq_single ⟨z₀, hz₀⟩ fun z hz => if_neg fun h => hz (Subtype.ext
      (eq_of_cexp_eq_of_not_resonant hℓ hres (im_mem_zeroHeights_of_evenCoeff_ne_zero z.2)
        (im_mem_zeroHeights_of_evenCoeff_ne_zero hz₀) h)), if_pos rfl]
  have hR : 0 ≤ (∑' z : ι, if W z = 1 then evenCoeff Z b z else 0).re := by
    rw [Complex.re_tsum (f := fun z : ι => if W z = 1 then evenCoeff Z b z else 0)
      (Summable.of_norm_bounded hsumι fun z => by split_ifs <;> simp)]
    refine tsum_nonneg fun z => ?_
    split_ifs with h
    · have h0 : (z : ℂ) = (D : ℂ) := eq_of_cexp_eq_of_not_resonant hℓ hres
        (im_mem_zeroHeights_of_evenCoeff_ne_zero z.2) (by simp [zeroHeights])
        (h.trans (by simp))
      have him : (z : ℂ).im = 0 := by rw [h0, Complex.ofReal_im]
      have hmem : (1 / 2 + (z : ℂ)) ∈ Z.carrier :=
        (mem_of_evenCoeff_ne_zero z.2).elim id fun h' => by
          rwa [show conj (z : ℂ) = z from Complex.ext (by simp) (by simp [him])] at h'
      exact (re_evenCoeff_modScaledBump_zero_pos Z hw hmem him).le
    · simp
  rw [hL] at key
  have := norm_pos_iff.mpr hz₀
  linarith

/-- **Subexponential Discrete Lag Grid Excludes Attained Tops and Produces `AsymptoticAbscissaLaw`.**
For any good width `w > 0` and non-resonant step `ℓ > 0` of `zetaZeroConfig`, if for every `σ > 0`
the two-bump Weil form on the discrete lag grid `v = kℓ` satisfies `-(C * e^{σkℓ}) ≤ Re W(f_{kℓ}, f_{kℓ})`
for all large `k`, then no off-line zero attains a maximal real part above `1/2`, and
`AsymptoticAbscissaLaw` holds unconditionally. -/
theorem not_attainedTop_of_grid_lag_subexponential {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps zetaZeroConfig)
    (hm : ∀ σ : ℝ, 0 < σ → ∃ (C : ℝ) (N : ℕ), ∀ k : ℕ, N ≤ k →
      -(C * Real.exp (σ * (k * ℓ))) ≤
        (zetaZeroConfig.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
          (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re) :
    ¬ ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀ := by
  rintro ⟨β₀, hβ₀, ⟨q₀, hq₀⟩, hmax⟩
  have hρ₀ : (q₀.1 : ℂ) ∈ zetaZeroConfig.carrier := xiZeroCopy_mem_zetaZeroConfig_carrier q₀
  have hre₀ : 1 / 2 < (q₀.1 : ℂ).re := by linarith
  obtain ⟨C, N, hCN⟩ := hm (((q₀.1 : ℂ).re - 1 / 2) / 2) (by linarith)
  obtain ⟨ρ, hρ, hgt⟩ := exists_re_gt_of_grid_lag_ge_neg_exp zetaZeroConfig
    temperedConfig_zetaZeroConfig hw hgood hℓ hres hρ₀ hre₀ (by linarith) (by linarith) hCN
  have hxi : _root_.RHTower.xi ρ = 0 :=
    (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).1
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have hle := hmax q
  rw [hq, ← hq₀] at hle
  linarith

theorem asymptoticAbscissaLaw_of_grid_lag_subexponential {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps zetaZeroConfig)
    (hm : ∀ σ : ℝ, 0 < σ → ∃ (C : ℝ) (N : ℕ), ∀ k : ℕ, N ≤ k →
      -(C * Real.exp (σ * (k * ℓ))) ≤
        (zetaZeroConfig.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
          (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re) :
    AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_not_attainedTop
    (not_attainedTop_of_grid_lag_subexponential hw hgood hℓ hres hm)

/-- **Prime-Side Discrete Lag Grid Producer for `AsymptoticAbscissaLaw`:**
For all but countably many widths `w ∈ (0, ½ log 2)` and all but countably many grid steps `ℓ > 0`,
subexponential lower bounds `-(C * e^{σkℓ}) ≤ Re P_{kℓ}` (`∀ σ > 0`) on a single geometric
progression of prime windows `X = e^{kℓ}` unconditionally produce `AsymptoticAbscissaLaw`
(and a fortiori so does any constant lower bound `-C ≤ Re P_{kℓ}`). -/
theorem zeta_asymptoticAbscissaLaw_of_grid_primeWindow_subexponential :
    ∃ E : Set ℝ, E.Countable ∧ ∃ E' : Set ℝ, E'.Countable ∧ ∀ w : ℝ, 0 < w →
      2 * w < Real.log 2 → w ∉ E → ∀ ℓ : ℝ, 0 < ℓ → ℓ ∉ E' →
        ((∀ σ : ℝ, 0 < σ → ∃ (C : ℝ) (N : ℕ), ∀ k : ℕ, N ≤ k →
          -(C * Real.exp (σ * (k * ℓ))) ≤
            (lagPrimeWindowRHS (k * ℓ) w
              (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
                (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re) →
          AsymptoticAbscissaLaw) ∧
        ((∃ (C : ℝ) (N : ℕ), ∀ k : ℕ, N ≤ k →
          -C ≤ (lagPrimeWindowRHS (k * ℓ) w
            (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
              (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re) →
          AsymptoticAbscissaLaw) ∧
        (RiemannHypothesis ↔ ZerosApproachLine ∧
          ∃ (C : ℝ) (N : ℕ), ∀ k : ℕ, N ≤ k →
            -C ≤ (lagPrimeWindowRHS (k * ℓ) w
              (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
                (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re) := by
  refine ⟨_, countable_bad_widths zetaZeroConfig, _, countable_resonantSteps zetaZeroConfig,
    fun w hw hw2 hwE ℓ hℓ hres => ?_⟩
  have hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  have heq : ∀ k : ℕ,
      (zetaZeroConfig.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
        (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re =
      (lagPrimeWindowRHS (k * ℓ) w
        (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
          (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re := fun k => by
    have hv : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le
    rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) (k * ℓ) (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) (k * ℓ) ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) (k * ℓ) (-1)),
      literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv]
  have hsub : (∀ σ : ℝ, 0 < σ → ∃ (C : ℝ) (N : ℕ), ∀ k : ℕ, N ≤ k →
      -(C * Real.exp (σ * (k * ℓ))) ≤
        (lagPrimeWindowRHS (k * ℓ) w
          (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
            (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re) → AsymptoticAbscissaLaw := by
    intro hm
    refine asymptoticAbscissaLaw_of_grid_lag_subexponential hw hgood hℓ hres fun σ hσ => ?_
    obtain ⟨C, N, hCN⟩ := hm σ hσ
    exact ⟨C, N, fun k hk => by rw [heq k]; exact hCN k hk⟩
  have hbdd : (∃ (C : ℝ) (N : ℕ), ∀ k : ℕ, N ≤ k →
      -C ≤ (lagPrimeWindowRHS (k * ℓ) w
        (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
          (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re) → AsymptoticAbscissaLaw := by
    rintro ⟨C, N, hCN⟩
    refine hsub fun σ hσ => ⟨max C 0, N, fun k hk => ?_⟩
    have hkℓ0 : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le
    have hexp1 : 1 ≤ Real.exp (σ * (k * ℓ)) := Real.one_le_exp (mul_nonneg hσ.le hkℓ0)
    have hC : C ≤ max C 0 * Real.exp (σ * (k * ℓ)) :=
      (le_max_left C 0).trans (le_mul_of_one_le_right (le_max_right C 0) hexp1)
    linarith [hCN k hk]
  refine ⟨hsub, hbdd, ?_⟩
  constructor
  · intro hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, 0, 0, fun k _ => ?_⟩
    rw [neg_zero, ← heq k]
    exact weil_nonneg_of_onLine zetaZeroConfig
      (riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH) _
  · rintro ⟨hZAL, hgrid⟩
    exact riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨hZAL, hbdd hgrid⟩

/-- **Positive-Slack Continuous Prime-Window Equivalence and Large-Height Abscissa Collapse:**
For all but countably many widths `w ∈ (0, ½ log 2)`:
1. `RiemannHypothesis` holds iff for every `σ > 0` (with strictly positive exponential slack
   `e^{σv}`), the prime-window functional satisfies `-(C * e^{σv}) ≤ Re P_v` for all large `v`;
2. Under `AsymptoticAbscissaLaw`, for every `σ ≥ 0`, large-height Hadamard positivity
   `EventualHadamardPositivityRight (1/2 + σ)` is equivalent to `-(C * e^{σv}) ≤ Re P_v`
   for all large `v`. -/
theorem zeta_riemannHypothesis_iff_forall_pos_lag_primeWindow_ge_neg_exp :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E →
      (RiemannHypothesis ↔ ∀ σ : ℝ, 0 < σ → ∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v →
        -(C * Real.exp (σ * v)) ≤ (lagPrimeWindowRHS v w (EF.weilTest
          (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re) ∧
      (AsymptoticAbscissaLaw → ∀ σ : ℝ, 0 ≤ σ →
        (EventualHadamardPositivityRight (1 / 2 + σ) ↔
          ∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v →
            -(C * Real.exp (σ * v)) ≤ (lagPrimeWindowRHS v w (EF.weilTest
              (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re)) := by
  obtain ⟨E, hE, hlag⟩ := zeta_re_le_iff_lag_primeWindow_ge_neg_exp
  refine ⟨E, hE, fun w hw hw2 hwE => ⟨?_, fun hAAL σ hσ => ?_⟩⟩
  · rw [riemannHypothesis_iff_forall_pos_xiZeroHalfPlaneBound]
    refine forall_congr' fun σ => imp_congr_right fun hσ => ?_
    rw [xiZeroHalfPlaneBound_iff_zetaZeroConfig_re_le]
    exact hlag w hw hw2 hwE σ hσ.le
  · rw [eventualHadamardPositivityRight_iff hσ,
      ← hlag w hw hw2 hwE σ hσ,
      ← xiZeroHalfPlaneBound_iff_zetaZeroConfig_re_le,
      xiZeroHalfPlaneBound_iff_xiZeroCopy_re_le]
    refine ⟨hAAL σ hσ, fun hall => Set.finite_empty.subset fun q hq => ?_⟩
    simp only [mem_setOf_eq] at hq
    exact absurd (hall q) (not_le.mpr hq)

/-! ## Section 3: Cubic-Spline Universal Probe Characterizations of `AsymptoticAbscissaLaw` & Positive-Slack RH -/

/-- **Positive-Slack Cubic-Spline Prime-Sum Equivalence for `RiemannHypothesis`:**
`RiemannHypothesis` holds if and only if for every `β > 0` (with strictly positive exponential
slack `e^{βτ}`), `splinePrimeSum τ ≤ splinePolarMass τ + K * exp((1 + β) * τ)` for all large `τ`. -/
theorem riemannHypothesis_iff_forall_pos_spline_prime_sum_le :
    RiemannHypothesis ↔ ∀ β : ℝ, 0 < β →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
        splinePrimeSum τ ≤ splinePolarMass τ + K * Real.exp ((1 + β) * τ) := by
  rw [riemannHypothesis_iff_forall_pos_xiZeroHalfPlaneBound]
  refine forall_congr' fun β => imp_congr_right fun hβ => ?_
  exact xiZeroHalfPlaneBound_iff_spline_prime_sum_le hβ.le

/-- **Positive-Slack Stationary-Packet Equivalence for `RiemannHypothesis`:**
`RiemannHypothesis` holds if and only if for every `β > 0`, the cubic-spline stationary packet
satisfies `stationaryPacket splineProbe τ ≤ K * exp(β * τ)` for all large `τ`. -/
theorem riemannHypothesis_iff_forall_pos_splineProbe_packet_upper :
    RiemannHypothesis ↔ ∀ β : ℝ, 0 < β →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket splineProbe τ ≤ K * Real.exp (β * τ) := by
  rw [riemannHypothesis_iff_forall_pos_xiZeroHalfPlaneBound]
  refine forall_congr' fun β => imp_congr_right fun hβ => ?_
  exact xiZeroHalfPlaneBound_iff_splineProbe_packet_upper hβ.le

/-- **Under `AsymptoticAbscissaLaw`, Every Large-Height Hadamard Abscissa Collapses to the
Global Cubic-Spline Prime-Sum Bound at Rate `β`.**
For every `β ≥ 0`, under `AsymptoticAbscissaLaw`, large-height Hadamard positivity
`EventualHadamardPositivityRight (1/2 + β)` is equivalent to the global prime-sum bound
`splinePrimeSum τ ≤ splinePolarMass τ + K * exp((1 + β) * τ)`. -/
theorem eventualHadamardPositivityRight_iff_spline_prime_sum_le_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) {β : ℝ} (hβ : 0 ≤ β) :
    EventualHadamardPositivityRight (1 / 2 + β) ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
        splinePrimeSum τ ≤ splinePolarMass τ + K * Real.exp ((1 + β) * τ) := by
  rw [eventualHadamardPositivityRight_iff hβ,
    ← xiZeroHalfPlaneBound_iff_spline_prime_sum_le hβ,
    xiZeroHalfPlaneBound_iff_xiZeroCopy_re_le]
  refine ⟨hAAL β hβ, fun hall => Set.finite_empty.subset fun q hq => ?_⟩
  simp only [mem_setOf_eq] at hq
  exact absurd (hall q) (not_le.mpr hq)

/-- **Under `AsymptoticAbscissaLaw`, Every Large-Height Gaussian Central-Gap Rate Collapses to the
Global Cubic-Spline Prime-Sum Bound at Rate `β`.** -/
theorem eventualFilteredCentralGapRate_iff_spline_prime_sum_le_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) {β : ℝ} (hβ : 0 ≤ β) :
    EventualFilteredCentralGapRate (β + β ^ 2 / 8) ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
        splinePrimeSum τ ≤ splinePolarMass τ + K * Real.exp ((1 + β) * τ) := by
  rw [eventualFilteredCentralGapRate_iff_finite_re_gt hβ]
  change {q : XiZeroCopy | 1 / 2 + β < (q.1 : ℂ).re}.Finite ↔ _
  rw [← eventualHadamardPositivityRight_iff hβ,
    eventualHadamardPositivityRight_iff_spline_prime_sum_le_of_asymptoticAbscissaLaw hAAL hβ]

/-! ## Section 4: Cross-Corpus Wall-Sidestepping Master Synthesis -/

/-- **Grid-Lag Negativity Directly Triggers Single-Scale Factorial-Tent Detection Across All Five
Channels (`compactFullWeilEnergy`, `fullZeroForm`, `weilFullFunctional Λ`, `zetaZeroConfig.W`,
and `configurationReflectionDefect - configurationSquareMass`).** -/
theorem grid_lag_neg_detected_by_gridTentPattern {w ℓ : ℝ} (hw : 0 < w) (k : ℕ)
    (hneg : (zetaZeroConfig.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
      (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re < 0) :
    ∃ (G : ℝ → ℝ) (R μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧ 0 ≤ R ∧ 0 < μ ∧
      ∀ᶠ n : ℕ in atTop,
        let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D := by
  set f : ℝ → ℂ := twoBump (modScaledBump w 0) (k * ℓ) (-1)
  have hf : ContDiff ℝ 2 f := contDiff_bumpTest (contDiff_modScaledBump_two w 0) (k * ℓ) ![1, -1]
  have hfc : HasCompactSupport f := hasCompactSupport_twoBump
    (hasCompactSupport_of_support_subset_abs (modScaledBump_support hw 0)) (k * ℓ) (-1)
  obtain ⟨R, hR, hfR⟩ := exists_radius_bound hfc
  have hfR' : ∀ x, R < |x| → f x = 0 := fun x hx => by
    by_contra hne
    exact not_le.mpr hx (hfR x hne)
  obtain ⟨φ, hφ, hφc, hφR, -, hφneg⟩ :=
    exists_real_contDiff_fullZeroForm_neg_of_zeta_W_neg hf hfc hfR' hneg
  have hspec := gridTentPattern_actual_zeta_detector_spec hφ hφc hR hφR hφneg
  refine ⟨fun x => Real.exp (-(3 * x / 2)) * φ x, R, -fullZeroForm φ / 4,
    by fun_prop, hφc.mul_left, hR, hspec.1, ?_⟩
  filter_upwards [hspec.2] with n hn
  refine ⟨hn.1, hn.2.1, fun q hq => ?_⟩
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := hn.2.2 q hq
  exact ⟨h1, h2, h4, h5, h6⟩

/-- **Cross-Corpus Wall-Sidestepping Master Equivalence for the Riemann Hypothesis:**
Unconditional synthesis uniting `RHTower`, `SquareRootThreshold`, `BiScaleUncertainty`,
`CHMDPolar`, and `ArithmeticPositivityTheory`. -/
theorem cross_corpus_wall_sidestepping_master_equivalence :
    (RiemannHypothesis ↔ ZerosApproachLine ∧ AsymptoticAbscissaLaw) ∧
    (RiemannHypothesis ↔ EventualHadamardPositivity ∧ AsymptoticAbscissaLaw) ∧
    (RiemannHypothesis ↔ EventualFilteredCentralGapSubexponential ∧ AsymptoticAbscissaLaw) ∧
    (RiemannHypothesis ↔ FiniteDimensional ℝ oddBoundStateSpace ∧ AsymptoticAbscissaLaw) ∧
    (RiemannHypothesis ↔ FiniteDimensional ℝ oddBoundStateSpace ∧ ZetaZeroDiscWeaklyRecurrent) ∧
    (RiemannHypothesis ↔ ∀ β : ℝ, 0 < β →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
        splinePrimeSum τ ≤ splinePolarMass τ + K * Real.exp ((1 + β) * τ)) ∧
    (RiemannHypothesis ↔ ∀ β : ℝ, 0 < β →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket splineProbe τ ≤ K * Real.exp (β * τ)) ∧
    (RiemannHypothesis ↔ oddBoundStateSpace = ⊥) ∧
    (RiemannHypothesis ↔ ∀ (G : ℝ → ℝ) (R : ℝ), 0 ≤ R →
      ∀ᶠ n : ℕ in atTop,
        0 ≤ compactFullWeilEnergy
          (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊)) := by
  refine ⟨riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw,
    ?_, ?_,
    riemannHypothesis_iff_finiteDimensional_oddBoundStateSpace_and_asymptoticAbscissaLaw,
    ?_,
    riemannHypothesis_iff_forall_pos_spline_prime_sum_le,
    riemannHypothesis_iff_forall_pos_splineProbe_packet_upper,
    riemannHypothesis_iff_oddBoundStateSpace_eq_bot,
    riemannHypothesis_iff_eventually_gridTentPattern_nonneg⟩
  · rw [eventualHadamardPositivity_iff_zerosApproachLine]
    exact riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw
  · rw [eventualFilteredCentralGapSubexponential_iff_zerosApproachLine]
    exact riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw
  · constructor
    · intro hRH
      exact ⟨(riemannHypothesis_iff_finiteDimensional_oddBoundStateSpace_and_asymptoticAbscissaLaw.mp hRH).1,
        (riemannHypothesis_iff_zerosApproachLine_and_zeroDiscWeaklyRecurrent.mp hRH).2⟩
    · rintro ⟨hfin, hW⟩
      exact riemannHypothesis_iff_finiteDimensional_oddBoundStateSpace_and_asymptoticAbscissaLaw.mpr
        ⟨hfin, asymptoticAbscissaLaw_of_zeroDiscWeaklyRecurrent hW⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
end
