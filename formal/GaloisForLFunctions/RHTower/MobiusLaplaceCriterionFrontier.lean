import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.RHTower.ThetaHalfPlaneBound
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The 2026 discrete Möbius--Laplace criterion frontier

Liflandsky (`arXiv:2607.09797`) studies

`Phi(exp(-x)) = sum mu(n) * exp(-n*x)`.

The paper proves unconditionally that an `O(x^(-1/2))` bound at zero implies RH.  Its mechanism is
that the Mellin transform, initially `Gamma(s) / zeta(s)` on `Re s > 1`, then extends analytically
to `Re s > 1/2`; the zero-free Gamma numerator forbids a zeta zero there.  The converse in the
paper uses additional simple-zero and zero-sum hypotheses and is not imported as an unconditional
fact.

This file constructs the exact series, proves its absolute convergence and continuity for every
`x > 0`, establishes its exponential tail, identifies its Mellin transform with
`Gamma(s) / zeta(s)` on `Re s > 1`, and formalizes the paper's analytic-continuation argument.
Consequently the source half-power decay implies RH as an unconditional Lean theorem.  The theorem
does not assert that the open decay premise holds.
-/

open Complex Filter Set ArithmeticFunction MeasureTheory Asymptotics
open scoped Moebius Topology LSeries.notation

namespace RHTower

noncomputable section

/-- A term of Liflandsky's discrete Laplace transform.  The `n = 0` term vanishes because
the arithmetic Möbius function is zero there, so this equals the paper's sum from `n = 1`. -/
def mobiusDiscreteLaplaceTerm (x : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
    Complex.exp (-((n : ℝ) * x : ℝ))

/-- Liflandsky's discrete Möbius--Laplace transform `sum mu(n) exp(-n*x)`. -/
def mobiusDiscreteLaplaceTransform (x : ℝ) : ℂ :=
  ∑' n : ℕ, mobiusDiscreteLaplaceTerm x n

/-- The source series is absolutely summable at every positive Laplace scale. -/
theorem summable_mobiusDiscreteLaplaceTerm {x : ℝ} (hx : 0 < x) :
    Summable (mobiusDiscreteLaplaceTerm x) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_pow_mul_exp_neg 0 hx)
  rw [mobiusDiscreteLaplaceTerm, norm_mul, Complex.norm_exp]
  have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hexp : 0 ≤ Real.exp (-((n : ℝ) * x)) := (Real.exp_pos _).le
  simpa using mul_le_mul_of_nonneg_right hmu hexp

/-- The defining series converges to the named transform at every positive scale. -/
theorem mobiusDiscreteLaplaceTerm_hasSum {x : ℝ} (hx : 0 < x) :
    HasSum (mobiusDiscreteLaplaceTerm x) (mobiusDiscreteLaplaceTransform x) :=
  (summable_mobiusDiscreteLaplaceTerm hx).hasSum

/-- The Möbius--Laplace transform is continuous on the positive real axis. -/
theorem continuousOn_mobiusDiscreteLaplaceTransform :
    ContinuousOn mobiusDiscreteLaplaceTransform (Ioi 0) := by
  intro x hx
  let a : ℝ := x / 2
  have hxpos : 0 < x := hx
  have ha : 0 < a := by dsimp [a]; linarith
  have hax : a < x := by dsimp [a]; linarith
  have hmajor : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * a))) := by
    simpa using summable_pow_mul_exp_neg 0 ha
  have hcontinuous : ContinuousOn
      (fun y : ℝ => ∑' n : ℕ, mobiusDiscreteLaplaceTerm y n) (Ici a) := by
    refine continuousOn_tsum (fun n => ?_) hmajor (fun n y hy => ?_)
    · unfold mobiusDiscreteLaplaceTerm
      fun_prop
    · rw [mobiusDiscreteLaplaceTerm, norm_mul, Complex.norm_exp]
      have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      have hexp : Real.exp (-((n : ℝ) * y)) ≤ Real.exp (-((n : ℝ) * a)) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hmul : (n : ℝ) * a ≤ (n : ℝ) * y :=
          mul_le_mul_of_nonneg_left hy hn
        linarith
      calc
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ * Real.exp (-((n : ℝ) * y))
            ≤ 1 * Real.exp (-((n : ℝ) * y)) :=
          mul_le_mul_of_nonneg_right hmu (Real.exp_pos _).le
        _ ≤ Real.exp (-((n : ℝ) * a)) := by simpa using hexp
  have hxIci : x ∈ Ici a := hax.le
  have hxnhds : Ici a ∈ 𝓝 x := Ici_mem_nhds hax
  exact (hcontinuous x hxIci).continuousAt hxnhds |>.continuousWithinAt

/-- The positive-axis transform is locally integrable, as required by Mellin theory. -/
theorem mobiusDiscreteLaplaceTransform_locallyIntegrableOn :
    LocallyIntegrableOn mobiusDiscreteLaplaceTransform (Ioi 0) :=
  continuousOn_mobiusDiscreteLaplaceTransform.locallyIntegrableOn measurableSet_Ioi

/-- Past scale one, the transform is bounded by a fixed geometric constant times `exp(-x)`. -/
theorem norm_mobiusDiscreteLaplaceTransform_le_exp_neg
    {x : ℝ} (hx : 1 ≤ x) :
    ‖mobiusDiscreteLaplaceTransform x‖ ≤
      Real.exp (-x) * ∑' n : ℕ, Real.exp (-(n : ℝ)) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsum := summable_mobiusDiscreteLaplaceTerm hxpos
  have hshift : mobiusDiscreteLaplaceTransform x =
      ∑' n : ℕ, mobiusDiscreteLaplaceTerm x (n + 1) := by
    have hsplit := hsum.sum_add_tsum_nat_add 1
    rw [mobiusDiscreteLaplaceTransform]
    simpa [mobiusDiscreteLaplaceTerm] using hsplit.symm
  have hshiftSum : Summable (fun n : ℕ => mobiusDiscreteLaplaceTerm x (n + 1)) :=
    hsum.comp_injective Nat.succ_injective
  have hgeom : Summable (fun n : ℕ => Real.exp (-x) * Real.exp (-(n : ℝ))) :=
    Real.summable_exp_neg_nat.mul_left _
  rw [hshift]
  calc
    ‖∑' n : ℕ, mobiusDiscreteLaplaceTerm x (n + 1)‖
        ≤ ∑' n : ℕ, ‖mobiusDiscreteLaplaceTerm x (n + 1)‖ :=
      norm_tsum_le_tsum_norm hshiftSum.norm
    _ ≤ ∑' n : ℕ, Real.exp (-x) * Real.exp (-(n : ℝ)) := by
      refine hshiftSum.norm.tsum_le_tsum (fun n => ?_) hgeom
      rw [mobiusDiscreteLaplaceTerm, norm_mul, Complex.norm_exp]
      have hmu : ‖((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
      have hexp : Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) ≤
          Real.exp (-x) * Real.exp (-(n : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        push_cast
        nlinarith
      exact (mul_le_mul_of_nonneg_right hmu (Real.exp_pos _).le).trans
        (by simpa using hexp)
    _ = Real.exp (-x) * ∑' n : ℕ, Real.exp (-(n : ℝ)) := by
      rw [tsum_mul_left]

/-- The source transform has the exponential tail used by the Mellin theorem. -/
theorem mobiusDiscreteLaplaceTransform_isBigO_exp_neg :
    mobiusDiscreteLaplaceTransform =O[atTop] (fun x : ℝ => Real.exp (-1 * x)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨∑' n : ℕ, Real.exp (-(n : ℝ)), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := norm_mobiusDiscreteLaplaceTransform_le_exp_neg hx
  rw [neg_one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa [mul_comm] using h

/-- The exact open decay statement in Liflandsky's one-way criterion. -/
def MobiusDiscreteLaplaceHalfDecay : Prop :=
  ∃ C delta : ℝ, 0 ≤ C ∧ 0 < delta ∧
    ∀ x : ℝ, 0 < x → x < delta →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ C * x ^ (-(1 / 2 : ℝ))

/-- The source `O(x^(-1/2))` statement in filter form. -/
theorem MobiusDiscreteLaplaceHalfDecay.isBigO
    (hdecay : MobiusDiscreteLaplaceHalfDecay) :
    mobiusDiscreteLaplaceTransform =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) := by
  rcases hdecay with ⟨C, delta, hC, hdelta, hbound⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < delta :=
    (eventually_lt_nhds hdelta).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with x hx hxd
  have hxpos : 0 < x := hx
  calc
    ‖mobiusDiscreteLaplaceTransform x‖
        ≤ C * x ^ (-(1 / 2 : ℝ)) := hbound x hxpos hxd
    _ = C * ‖x ^ (-(1 / 2 : ℝ))‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxpos _)]

/-- The weighted Möbius coefficients required for Mellin--Dirichlet interchange are summable on
`Re s > 1`. -/
theorem mobiusMellin_weight_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ =>
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ / (n : ℝ) ^ s.re) := by
  have h := (LSeriesSummable_moebius_iff.mpr hs).norm
  refine h.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn]

/-- **Mellin--Dirichlet identity.**  On the half-plane of absolute convergence, the Mellin
transform of the concrete Möbius--Laplace series is `Gamma(s)` times the Möbius L-series. -/
theorem mellin_mobiusDiscreteLaplaceTransform_eq_gamma_mul_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    mellin mobiusDiscreteLaplaceTransform s =
      Complex.Gamma s * (L ↗μ s) := by
  let a : ℕ → ℂ := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)
  let p : ℕ → ℝ := fun n => (n : ℝ)
  have hp : ∀ n, a n = 0 ∨ 0 < p n := by
    intro n
    by_cases hn : n = 0
    · left
      subst n
      simp [a]
    · right
      dsimp [p]
      exact_mod_cast Nat.pos_of_ne_zero hn
  have hs0 : 0 < s.re := by linarith
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun n => a n * Real.exp (-p n * t))
        (mobiusDiscreteLaplaceTransform t) := by
    intro t ht
    convert mobiusDiscreteLaplaceTerm_hasSum ht using 1 with n
    funext n
    dsimp [a, p, mobiusDiscreteLaplaceTerm]
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  have hweight : Summable (fun n => ‖a n‖ / p n ^ s.re) := by
    simpa [a, p] using mobiusMellin_weight_summable hs
  have hmellin : HasSum (fun n => Complex.Gamma s * a n / (p n : ℂ) ^ s)
      (mellin mobiusDiscreteLaplaceTransform s) :=
    hasSum_mellin hp hs0 hF hweight
  rw [← hmellin.tsum_eq, LSeries, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [LSeries.term_def₀ (by simp) s n]
  dsimp [a, p]
  rw [div_eq_mul_inv, Complex.cpow_neg]
  ring

/-- The Mellin transform of the concrete source equals `Gamma(s)/zeta(s)` on `Re s > 1`. -/
theorem mellin_mobiusDiscreteLaplaceTransform_eq_gamma_div_zeta
    {s : ℂ} (hs : 1 < s.re) :
    mellin mobiusDiscreteLaplaceTransform s =
      Complex.Gamma s * (riemannZeta s)⁻¹ := by
  rw [mellin_mobiusDiscreteLaplaceTransform_eq_gamma_mul_LSeries hs,
    LSeries_moebius_eq_inv_riemannZeta hs]

/-- Gamma is analytic at every point of positive real part. -/
private theorem analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gamma s := by
  have hinv : AnalyticAt ℂ (fun z => (Complex.Gamma z)⁻¹) s :=
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ)
      s (mem_univ s)
  have h := hinv.inv (inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos hs))
  change AnalyticAt ℂ (fun z => ((Complex.Gamma z)⁻¹)⁻¹) s at h
  simpa using h

/-- The regularized zeta residue unit is analytic everywhere. -/
private theorem analyticAt_zetaResidueUnit (s : ℂ) :
    AnalyticAt ℂ zetaResidueUnit s := by
  by_cases hs : s = 1
  · simpa [hs] using zetaResidueUnit_analyticAt
  · have hdiff : DifferentiableOn ℂ (fun z => (z - 1) * riemannZeta z) ({1}ᶜ) := by
      intro z hz
      exact (differentiableAt_id.sub_const 1).mul
        (differentiableAt_riemannZeta (by simpa using hz)) |>.differentiableWithinAt
    have han : AnalyticAt ℂ (fun z => (z - 1) * riemannZeta z) s :=
      (hdiff.analyticOnNhd isOpen_compl_singleton) s (by simpa using hs)
    exact han.congr (zetaResidueUnit_eventuallyEq hs).symm

/-- The source decay gives analyticity of its Mellin transform on `Re s > 1/2`. -/
theorem analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform
    (hdecay : MobiusDiscreteLaplaceHalfDecay) :
    AnalyticOnNhd ℂ (mellin mobiusDiscreteLaplaceTransform) rightHalf := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_rightHalf
  exact (mellin_differentiableAt_of_isBigO_rpow_exp
    (a := 1) (b := 1 / 2) (by norm_num)
    mobiusDiscreteLaplaceTransform_locallyIntegrableOn
    mobiusDiscreteLaplaceTransform_isBigO_exp_neg hdecay.isBigO
    (mem_rightHalf.mp hs)).differentiableWithinAt

/-- The analytic continuation endpoint produced in the paper from the half-power decay bound.
The denominator-free identity uses the analytic residue unit `(s-1) zeta(s)`, so it remains a
genuine analytic identity at the Euler pole `s = 1`. -/
def MobiusLaplaceMellinContinuationWall : Prop :=
  ∃ G : ℂ → ℂ,
    AnalyticOnNhd ℂ G rightHalf ∧
      ∀ s ∈ rightHalf,
        G s * zetaResidueUnit s = Complex.Gamma s * (s - 1)

/-- The Mellin bridge isolated as a proposition.  It is discharged below for the concrete source. -/
def MobiusLaplaceDecayToContinuationBridge : Prop :=
  MobiusDiscreteLaplaceHalfDecay → MobiusLaplaceMellinContinuationWall

/-- **Unconditional source-to-continuation bridge.**  The half-power bound makes the concrete
Mellin transform analytic on `Re s > 1/2`; the identity theorem propagates its classical
`Gamma/zeta` identity from `Re s > 1` across the connected half-plane. -/
theorem mobiusLaplaceDecayToContinuationBridge :
    MobiusLaplaceDecayToContinuationBridge := by
  intro hdecay
  let G : ℂ → ℂ := mellin mobiusDiscreteLaplaceTransform
  have hG : AnalyticOnNhd ℂ G rightHalf :=
    analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform hdecay
  have hleft : AnalyticOnNhd ℂ
      (fun s => G s * zetaResidueUnit s) rightHalf := by
    intro s hs
    exact (hG s hs).mul (analyticAt_zetaResidueUnit s)
  have hright : AnalyticOnNhd ℂ
      (fun s => Complex.Gamma s * (s - 1)) rightHalf := by
    intro s hs
    have hspos : 0 < s.re := lt_trans (by norm_num) (mem_rightHalf.mp hs)
    exact (analyticAt_Gamma_of_re_pos hspos).mul
      (analyticAt_id.sub analyticAt_const)
  have hevent :
      (fun s => G s * zetaResidueUnit s) =ᶠ[𝓝 (2 : ℂ)]
        (fun s => Complex.Gamma s * (s - 1)) := by
    have hgt : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with s hs
    have hs1 : s ≠ 1 := by
      intro hsone
      subst s
      norm_num at hs
    have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    rw [show G s = Complex.Gamma s * (riemannZeta s)⁻¹ by
      simpa [G] using mellin_mobiusDiscreteLaplaceTransform_eq_gamma_div_zeta hs]
    simp only [zetaResidueUnit, Function.update_of_ne hs1]
    field_simp
  refine ⟨G, hG, ?_⟩
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    convex_rightHalf.isPreconnected two_mem_rightHalf hevent

/-- **Terminal Möbius--Laplace zero-free connector.**  An analytic continuation satisfying the
Mellin identity on `Re s > 1/2` proves RH, because Gamma has no zero in that half-plane. -/
theorem mobiusLaplaceMellinContinuationWall_implies_riemannHypothesis
    (hwall : MobiusLaplaceMellinContinuationWall) : RiemannHypothesis := by
  rcases hwall with ⟨G, _hG, hidentity⟩
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hxis
  have hhalf : 1 / 2 < s.re := mem_rightHalf.mp hs
  have hs1 : s ≠ 1 := by
    intro hsone
    subst s
    rw [xi_one] at hxis
    norm_num at hxis
  have hspos : 0 < s.re := lt_trans (by norm_num) hhalf
  have hzeta : riemannZeta s = 0 := (xi_eq_zero_iff hspos hs1).mp hxis
  have hgamma : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hspos
  have hresidue : zetaResidueUnit s = 0 := by
    simp [zetaResidueUnit, hs1, hzeta]
  have hident := hidentity s hs
  rw [hresidue, mul_zero] at hident
  exact (mul_ne_zero hgamma (sub_ne_zero.mpr hs1)) hident.symm

/-- Once the paper's Mellin bridge is present, the named half-power decay wall has its exact
unconditional one-way consequence.  This theorem does not assert either open premise. -/
theorem mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis_of_bridge
    (hbridge : MobiusLaplaceDecayToContinuationBridge)
    (hdecay : MobiusDiscreteLaplaceHalfDecay) : RiemannHypothesis :=
  mobiusLaplaceMellinContinuationWall_implies_riemannHypothesis (hbridge hdecay)

/-- **Liflandsky's unconditional one-way criterion (2026).**  If the concrete discrete
Möbius--Laplace transform is `O(x^(-1/2))` at zero, then RH follows. -/
theorem mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis
    (hdecay : MobiusDiscreteLaplaceHalfDecay) : RiemannHypothesis :=
  mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis_of_bridge
    mobiusLaplaceDecayToContinuationBridge hdecay

end

end RHTower
