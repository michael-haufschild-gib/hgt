import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.Mollifier
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.RHTower.ThetaHalfPlaneBound
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

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

/-- At positive real scale, the Möbius--Laplace transform is real. -/
theorem mobiusDiscreteLaplaceTransform_im_eq_zero {x : ℝ} (hx : 0 < x) :
    (mobiusDiscreteLaplaceTransform x).im = 0 := by
  have hsum := summable_mobiusDiscreteLaplaceTerm hx
  have hmap := hsum.hasSum.map Complex.imCLM Complex.imCLM.continuous
  have hterm (n : ℕ) : (mobiusDiscreteLaplaceTerm x n).im = 0 := by
    have hexpim :
        (Complex.exp (-((n : ℝ) * x : ℝ))).im = 0 :=
      by simpa using Complex.exp_ofReal_im (-((n : ℝ) * x))
    rw [mobiusDiscreteLaplaceTerm, Complex.mul_im]
    change ((ArithmeticFunction.moebius n : ℤ) : ℂ).re *
        (Complex.exp (-((n : ℝ) * x : ℝ))).im +
      ((ArithmeticFunction.moebius n : ℤ) : ℂ).im *
        (Complex.exp (-((n : ℝ) * x : ℝ))).re = 0
    rw [hexpim]
    simp
  change HasSum (fun n => (mobiusDiscreteLaplaceTerm x n).im)
    (mobiusDiscreteLaplaceTransform x).im at hmap
  have hfun : (fun n => (mobiusDiscreteLaplaceTerm x n).im) =
      (fun _ : ℕ => (0 : ℝ)) := funext hterm
  rw [hfun] at hmap
  exact hmap.unique hasSum_zero

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

/-- The elementary geometric majorant is at most `1 / x`.  This is the sharp unconditional
power wall obtainable without cancellation from the Möbius coefficients. -/
theorem norm_mobiusDiscreteLaplaceTransform_le_inv {x : ℝ} (hx : 0 < x) :
    ‖mobiusDiscreteLaplaceTransform x‖ ≤ 1 / x := by
  let q := Real.exp (-x)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos hx)
  have hsum := summable_mobiusDiscreteLaplaceTerm hx
  have hshift : mobiusDiscreteLaplaceTransform x =
      ∑' n : ℕ, mobiusDiscreteLaplaceTerm x (n + 1) := by
    have hsplit := hsum.sum_add_tsum_nat_add 1
    rw [mobiusDiscreteLaplaceTransform]
    simpa [mobiusDiscreteLaplaceTerm] using hsplit.symm
  have hshiftSum : Summable (fun n : ℕ => mobiusDiscreteLaplaceTerm x (n + 1)) :=
    hsum.comp_injective Nat.succ_injective
  have hgeom : Summable (fun n : ℕ => q ^ (n + 1)) := by
    have hbase := summable_geometric_of_lt_one hq0 hq1
    rw [show (fun n : ℕ => q ^ (n + 1)) = fun n : ℕ => q * q ^ n by
      funext n
      rw [pow_succ']]
    exact hbase.mul_left q
  have hterm (n : ℕ) :
      ‖mobiusDiscreteLaplaceTerm x (n + 1)‖ ≤ q ^ (n + 1) := by
    rw [mobiusDiscreteLaplaceTerm, norm_mul, Complex.norm_exp]
    have hmu : ‖((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
    have hexp : Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) = q ^ (n + 1) := by
      rw [show -(((n + 1 : ℕ) : ℝ) * x) = ((n + 1 : ℕ) : ℝ) * (-x) by ring,
        Real.exp_nat_mul]
    change ‖((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)‖ *
      Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) ≤ q ^ (n + 1)
    rw [hexp]
    simpa using mul_le_mul_of_nonneg_right hmu (pow_nonneg hq0 _)
  have hnorm : ‖mobiusDiscreteLaplaceTransform x‖ ≤ q * (1 - q)⁻¹ := by
    rw [hshift]
    calc
      ‖∑' n : ℕ, mobiusDiscreteLaplaceTerm x (n + 1)‖
          ≤ ∑' n : ℕ, ‖mobiusDiscreteLaplaceTerm x (n + 1)‖ :=
        norm_tsum_le_tsum_norm hshiftSum.norm
      _ ≤ ∑' n : ℕ, q ^ (n + 1) :=
        hshiftSum.norm.tsum_le_tsum hterm hgeom
      _ = ∑' n : ℕ, q * q ^ n := by
        apply tsum_congr
        intro n
        rw [pow_succ']
      _ = q * ∑' n : ℕ, q ^ n := tsum_mul_left
      _ = q * (1 - q)⁻¹ := by rw [tsum_geometric_of_lt_one hq0 hq1]
  have hexpinv : Real.exp x * q = 1 := by
    dsimp [q]
    rw [← Real.exp_add]
    simp
  have hmul := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) hq0
  rw [hexpinv] at hmul
  have hquot : q * (1 - q)⁻¹ ≤ 1 / x := by
    have hqx : q * x ≤ 1 - q := by nlinarith
    have hdiv : q / (1 - q) ≤ 1 / x :=
      (div_le_div_iff₀ (sub_pos.mpr hq1) hx).2 (by simpa using hqx)
    simpa [div_eq_mul_inv] using hdiv
  exact hnorm.trans hquot

/-- Near zero, the concrete Möbius--Laplace source is `O(x⁻¹)` unconditionally. -/
theorem mobiusDiscreteLaplaceTransform_isBigO_inv :
    mobiusDiscreteLaplaceTransform =O[𝓝[>] 0] (fun x : ℝ => x ^ (-1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hbound := norm_mobiusDiscreteLaplaceTransform_le_inv hx
  rw [one_mul, Real.rpow_neg (le_of_lt hx), Real.rpow_one,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
  simpa [one_div] using hbound

/-- The source Mellin integral converges throughout its classical half-plane `Re s > 1`. -/
theorem mellinConvergent_mobiusDiscreteLaplaceTransform {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent mobiusDiscreteLaplaceTransform s :=
  mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := 1) (by norm_num)
    mobiusDiscreteLaplaceTransform_locallyIntegrableOn
    mobiusDiscreteLaplaceTransform_isBigO_exp_neg
    mobiusDiscreteLaplaceTransform_isBigO_inv hs

/-! ## Exact Lambert dilation and critical renewal laws -/

/-- Absolutely summable double-series term behind the Möbius--Laplace Lambert identity.  The first
positive integer is the dilation index and the second is the Möbius index. -/
def mobiusLaplaceLambertPair (x : ℝ) (c : ℕ+ × ℕ+) : ℂ :=
  ((ArithmeticFunction.moebius c.2 : ℤ) : ℂ) *
    Complex.exp (-((c.1 : ℝ) * (c.2 : ℝ) * x : ℝ))

/-- Positive Laplace scale gives absolute summability of the full dilation/Möbius double series. -/
theorem summable_mobiusLaplaceLambertPair {x : ℝ} (hx : 0 < x) :
    Summable (mobiusLaplaceLambertPair x) := by
  have hgeoNat : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * x))) := by
    simpa using summable_pow_mul_exp_neg 0 hx
  have hgeo : Summable (fun n : ℕ+ => Real.exp (-((n : ℝ) * x))) :=
    hgeoNat.comp_injective PNat.coe_injective
  have hmajor : Summable (fun c : ℕ+ × ℕ+ =>
      Real.exp x * (Real.exp (-((c.1 : ℝ) * x)) *
        Real.exp (-((c.2 : ℝ) * x)))) :=
    (hgeo.mul_of_nonneg hgeo (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)).mul_left (Real.exp x)
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun c => norm_nonneg _) (fun c => ?_) hmajor
  rw [mobiusLaplaceLambertPair, norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  have hmu : ‖((ArithmeticFunction.moebius c.2 : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := c.2)
  have hn : (1 : ℝ) ≤ (c.1 : ℝ) := by exact_mod_cast c.1.property
  have hk : (1 : ℝ) ≤ (c.2 : ℝ) := by exact_mod_cast c.2.property
  have hprod : (c.1 : ℝ) + (c.2 : ℝ) - 1 ≤ (c.1 : ℝ) * (c.2 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hk)]
  have hexp : Real.exp (-((c.1 : ℝ) * (c.2 : ℝ) * x)) ≤
      Real.exp x * (Real.exp (-((c.1 : ℝ) * x)) *
        Real.exp (-((c.2 : ℝ) * x))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    ‖((ArithmeticFunction.moebius c.2 : ℤ) : ℂ)‖ *
          Real.exp (-((c.1 : ℝ) * (c.2 : ℝ) * x))
        ≤ 1 * Real.exp (-((c.1 : ℝ) * (c.2 : ℝ) * x)) :=
      mul_le_mul_of_nonneg_right hmu (Real.exp_pos _).le
    _ = Real.exp (-((c.1 : ℝ) * (c.2 : ℝ) * x)) := one_mul _
    _ ≤ _ := hexp

private theorem sum_moebius_second_divisorsAntidiagonal (b : ℕ+) :
    (∑ z : (b : ℕ).divisorsAntidiagonal,
      ArithmeticFunction.moebius z.1.2) = if b = 1 then 1 else 0 := by
  rw [show (∑ z : (b : ℕ).divisorsAntidiagonal,
      ArithmeticFunction.moebius z.1.2) =
      ∑ z ∈ (b : ℕ).divisorsAntidiagonal, ArithmeticFunction.moebius z.2 from by
        simpa only [Finset.univ_eq_attach] using
          ((b : ℕ).divisorsAntidiagonal.sum_attach
            (fun z ↦ ArithmeticFunction.moebius z.2))]
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun _ j ↦ ArithmeticFunction.moebius j)]
  simpa using sum_moebius_divisors (b : ℕ)

private theorem mobiusLaplaceLambertPair_antidiagonal (x : ℝ) (b : ℕ+) :
    (∑ z : (b : ℕ).divisorsAntidiagonal,
      mobiusLaplaceLambertPair x (divisorsAntidiagonalFactors b z)) =
      if b = 1 then Complex.exp (-x) else 0 := by
  classical
  have hterm (z : (b : ℕ).divisorsAntidiagonal) :
      mobiusLaplaceLambertPair x (divisorsAntidiagonalFactors b z) =
        (ArithmeticFunction.moebius z.1.2 : ℂ) * Complex.exp (-((b : ℝ) * x)) := by
    let d := divisorsAntidiagonalFactors b z
    have hval : d.1.1 * d.2.1 = (b : ℕ) := divisorsAntidiagonalFactors_eq z
    have hvalR : (d.1 : ℝ) * (d.2 : ℝ) = (b : ℝ) := by
      simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ)) hval
    change ((ArithmeticFunction.moebius d.2 : ℤ) : ℂ) *
      Complex.exp (-((d.1 : ℝ) * (d.2 : ℝ) * x : ℝ)) = _
    have hd2 : d.2.1 = z.1.2 := rfl
    have hmu : ArithmeticFunction.moebius (d.2 : ℕ) =
        ArithmeticFunction.moebius z.1.2 := congrArg ArithmeticFunction.moebius hd2
    rw [hvalR, hmu]
    congr 2
    push_cast
    rfl
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  have hmuC :
      (∑ z : (b : ℕ).divisorsAntidiagonal,
        (ArithmeticFunction.moebius z.1.2 : ℂ)) = if b = 1 then 1 else 0 := by
    rw [← Int.cast_sum, sum_moebius_second_divisorsAntidiagonal b]
    split_ifs <;> simp
  rw [hmuC]
  split_ifs with hb
  · subst b
    norm_num
  · simp

/-- Regrouping the absolutely summable double series by its product index leaves only `kn=1`. -/
theorem tsum_mobiusLaplaceLambertPair_eq_exp_neg (x : ℝ) (hx : 0 < x) :
    (∑' c : ℕ+ × ℕ+, mobiusLaplaceLambertPair x c) = Complex.exp (-x) := by
  have hsum := summable_mobiusLaplaceLambertPair hx
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  rw [Summable.tsum_sigma]
  · calc
      _ = ∑' b : ℕ+, if b = 1 then Complex.exp (-x) else 0 := by
        apply tsum_congr
        intro b
        rw [tsum_fintype]
        exact mobiusLaplaceLambertPair_antidiagonal x b
      _ = Complex.exp (-x) := by simp
  · exact (sigmaAntidiagonalEquivProd.summable_iff).2 hsum

private theorem tsum_mobiusLaplaceLambertPair_row
    (x : ℝ) (hx : 0 < x) (k : ℕ+) :
    (∑' n : ℕ+, mobiusLaplaceLambertPair x (k, n)) =
      mobiusDiscreteLaplaceTransform ((k : ℝ) * x) := by
  have hkx : 0 < (k : ℝ) * x := mul_pos (by exact_mod_cast k.property) hx
  have hsum := summable_mobiusDiscreteLaplaceTerm hkx
  have hsplit := hsum.sum_add_tsum_nat_add 1
  calc
    (∑' n : ℕ+, mobiusLaplaceLambertPair x (k, n)) =
        ∑' n : ℕ+, mobiusDiscreteLaplaceTerm ((k : ℝ) * x) (n : ℕ) := by
      apply tsum_congr
      intro n
      rw [mobiusLaplaceLambertPair, mobiusDiscreteLaplaceTerm]
      apply congrArg (fun z : ℂ =>
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * z)
      apply congrArg Complex.exp
      push_cast
      ring
    _ = ∑' n : ℕ, mobiusDiscreteLaplaceTerm ((k : ℝ) * x) (n + 1) := by
      exact tsum_pnat_eq_tsum_succ
    _ = mobiusDiscreteLaplaceTransform ((k : ℝ) * x) := by
      rw [mobiusDiscreteLaplaceTransform]
      simpa [mobiusDiscreteLaplaceTerm] using hsplit

/-- **Exact Möbius--Laplace Lambert law.**  The absolutely convergent sum of all positive integer
dilates of the concrete transform is the first exponential atom. -/
theorem tsum_pnat_mobiusDiscreteLaplaceTransform_dilate
    (x : ℝ) (hx : 0 < x) :
    (∑' k : ℕ+, mobiusDiscreteLaplaceTransform ((k : ℝ) * x)) =
      Complex.exp (-x) := by
  have hsum := summable_mobiusLaplaceLambertPair hx
  calc
    (∑' k : ℕ+, mobiusDiscreteLaplaceTransform ((k : ℝ) * x)) =
        ∑' k : ℕ+, ∑' n : ℕ+, mobiusLaplaceLambertPair x (k, n) := by
      apply tsum_congr
      intro k
      exact (tsum_mobiusLaplaceLambertPair_row x hx k).symm
    _ = ∑' c : ℕ+ × ℕ+, mobiusLaplaceLambertPair x c := hsum.tsum_prod.symm
    _ = Complex.exp (-x) := tsum_mobiusLaplaceLambertPair_eq_exp_neg x hx

/-- The dilation family in the exact Lambert law is absolutely summable. -/
theorem summable_pnat_mobiusDiscreteLaplaceTransform_dilate
    (x : ℝ) (hx : 0 < x) :
    Summable (fun k : ℕ+ => mobiusDiscreteLaplaceTransform ((k : ℝ) * x)) := by
  have hsum := summable_mobiusLaplaceLambertPair hx
  exact hsum.prod.congr fun k => tsum_mobiusLaplaceLambertPair_row x hx k

/-- Every positive dilation lattice contains a transform value with strictly positive real part.
This is forced by the positive first atom in the exact Lambert law. -/
theorem exists_mobiusDiscreteLaplaceTransform_dilate_re_pos
    (x : ℝ) (hx : 0 < x) :
    ∃ k : ℕ+, 0 < (mobiusDiscreteLaplaceTransform ((k : ℝ) * x)).re := by
  let f : ℕ+ → ℂ := fun k => mobiusDiscreteLaplaceTransform ((k : ℝ) * x)
  by_contra h
  push Not at h
  have hsum : Summable f :=
    summable_pnat_mobiusDiscreteLaplaceTransform_dilate x hx
  have hre : (∑' k : ℕ+, f k).re = ∑' k : ℕ+, (f k).re := by
    simpa [Function.comp_def] using
      (hsum.hasSum.map Complex.reCLM Complex.reCLM.continuous).tsum_eq.symm
  have hnonpos : ∑' k : ℕ+, (f k).re ≤ 0 := tsum_nonpos h
  have hpos : 0 < (∑' k : ℕ+, f k).re := by
    rw [tsum_pnat_mobiusDiscreteLaplaceTransform_dilate x hx]
    simpa [Complex.exp_re] using Real.exp_pos (-x)
  rw [hre] at hpos
  exact (not_lt_of_ge hnonpos) hpos

/-- Critical log-coordinate normalization: boundedness as `y → +∞` is the requested
`O(x^(-1/2))` behavior at `x=0`. -/
def mobiusLaplaceCriticalProfile (y : ℝ) : ℂ :=
  (Real.exp (-y / 2) : ℂ) *
    mobiusDiscreteLaplaceTransform (Real.exp (-y))

/-- Positive renewal weight, written exponentially to make the log-translation law exact. -/
def mobiusLaplaceCriticalRenewalWeight (k : ℕ+) : ℝ :=
  Real.exp (-Real.log (k : ℝ) / 2)

/-- The critical renewal weight is exactly `k^(-1/2)`. -/
theorem mobiusLaplaceCriticalRenewalWeight_eq_rpow (k : ℕ+) :
    mobiusLaplaceCriticalRenewalWeight k = (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [mobiusLaplaceCriticalRenewalWeight, Real.rpow_def_of_pos (by positivity)]
  congr 1
  ring

private theorem mobiusLaplaceCriticalRenewal_term_eq (y : ℝ) (k : ℕ+) :
    (mobiusLaplaceCriticalRenewalWeight k : ℂ) *
        mobiusLaplaceCriticalProfile (y - Real.log (k : ℝ)) =
      (Real.exp (-y / 2) : ℂ) *
        mobiusDiscreteLaplaceTransform ((k : ℝ) * Real.exp (-y)) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast k.property
  have hscale : Real.exp (-(y - Real.log (k : ℝ))) =
      (k : ℝ) * Real.exp (-y) := by
    rw [show -(y - Real.log (k : ℝ)) = -y + Real.log (k : ℝ) by ring,
      Real.exp_add, Real.exp_log hkpos]
    ring
  rw [mobiusLaplaceCriticalProfile, hscale]
  rw [← mul_assoc]
  apply congrArg (fun z : ℂ => z *
    mobiusDiscreteLaplaceTransform ((k : ℝ) * Real.exp (-y)))
  norm_cast
  rw [mobiusLaplaceCriticalRenewalWeight, ← Real.exp_add]
  congr 1
  ring

/-- Absolute convergence of the critical renewal series. -/
theorem summable_mobiusLaplaceCriticalRenewal (y : ℝ) :
    Summable (fun k : ℕ+ => (mobiusLaplaceCriticalRenewalWeight k : ℂ) *
      mobiusLaplaceCriticalProfile (y - Real.log (k : ℝ))) := by
  have hbase :=
    summable_pnat_mobiusDiscreteLaplaceTransform_dilate
      (Real.exp (-y)) (Real.exp_pos _)
  have hscaled := hbase.mul_left (Real.exp (-y / 2) : ℂ)
  exact hscaled.congr fun k => (mobiusLaplaceCriticalRenewal_term_eq y k).symm

/-- **Exact critical renewal equation.**  In half-power log coordinates, positive integer
dilations become translations by `log k` with weight `k^(-1/2)`. -/
theorem tsum_mobiusLaplaceCriticalRenewal (y : ℝ) :
    (∑' k : ℕ+, (mobiusLaplaceCriticalRenewalWeight k : ℂ) *
      mobiusLaplaceCriticalProfile (y - Real.log (k : ℝ))) =
        (Real.exp (-y / 2) : ℂ) * Complex.exp (-Real.exp (-y)) := by
  calc
    _ = ∑' k : ℕ+, (Real.exp (-y / 2) : ℂ) *
          mobiusDiscreteLaplaceTransform ((k : ℝ) * Real.exp (-y)) := by
      apply tsum_congr
      exact mobiusLaplaceCriticalRenewal_term_eq y
    _ = (Real.exp (-y / 2) : ℂ) *
          ∑' k : ℕ+, mobiusDiscreteLaplaceTransform ((k : ℝ) * Real.exp (-y)) := by
      rw [tsum_mul_left]
    _ = (Real.exp (-y / 2) : ℂ) * Complex.exp (-Real.exp (-y)) := by
      rw [tsum_pnat_mobiusDiscreteLaplaceTransform_dilate
        (Real.exp (-y)) (Real.exp_pos _)]

/-! ## Prime-divisibility anti-TP2 law -/

/-- Real mass of the exact Möbius--Laplace renewal law at a positive dilation scale. -/
def mobiusLaplaceRenewalMass (scale x : ℝ) : ℝ :=
  Real.exp (-(scale * x))

/-- The closed renewal mass is the actual absolutely convergent sum of all positive-integer
dilates at the given scale. -/
theorem ofReal_mobiusLaplaceRenewalMass_eq_tsum
    {scale x : ℝ} (hscale : 0 < scale) (hx : 0 < x) :
    ((mobiusLaplaceRenewalMass scale x : ℝ) : ℂ) =
      ∑' k : ℕ+, mobiusDiscreteLaplaceTransform ((k : ℝ) * (scale * x)) := by
  rw [tsum_pnat_mobiusDiscreteLaplaceTransform_dilate
    (scale * x) (mul_pos hscale hx)]
  simp [mobiusLaplaceRenewalMass, Complex.ofReal_exp]

/-- At fixed positive `x`, renewal mass is strictly decreasing in its dilation scale. -/
theorem mobiusLaplaceRenewalMass_strictAnti_scale
    {u v x : ℝ} (huv : u < v) (hx : 0 < x) :
    mobiusLaplaceRenewalMass v x < mobiusLaplaceRenewalMass u x := by
  exact Real.exp_lt_exp.mpr (neg_lt_neg (mul_lt_mul_of_pos_right huv hx))

/-- Renewal mass of dilation indices divisible by neither `p` nor `q`, written by exact finite
inclusion--exclusion.  For its prime-divisibility interpretation, `p` and `q` are distinct. -/
def mobiusLaplacePrimeDivisibilityCell00 (a x : ℝ) (p q : ℕ) : ℝ :=
  mobiusLaplaceRenewalMass a x - mobiusLaplaceRenewalMass (a * p) x -
    mobiusLaplaceRenewalMass (a * q) x + mobiusLaplaceRenewalMass (a * p * q) x

/-- Renewal mass of indices divisible by `q` and not by `p`. -/
def mobiusLaplacePrimeDivisibilityCell01 (a x : ℝ) (p q : ℕ) : ℝ :=
  mobiusLaplaceRenewalMass (a * q) x - mobiusLaplaceRenewalMass (a * p * q) x

/-- Renewal mass of indices divisible by `p` and not by `q`. -/
def mobiusLaplacePrimeDivisibilityCell10 (a x : ℝ) (p q : ℕ) : ℝ :=
  mobiusLaplaceRenewalMass (a * p) x - mobiusLaplaceRenewalMass (a * p * q) x

/-- Renewal mass of indices divisible by both `p` and `q`. -/
def mobiusLaplacePrimeDivisibilityCell11 (a x : ℝ) (p q : ℕ) : ℝ :=
  mobiusLaplaceRenewalMass (a * p * q) x

/-- Determinant of the two-prime divisibility table of renewal masses. -/
def mobiusLaplacePrimeDivisibilityDet (a x : ℝ) (p q : ℕ) : ℝ :=
  mobiusLaplacePrimeDivisibilityCell00 a x p q *
      mobiusLaplacePrimeDivisibilityCell11 a x p q -
    mobiusLaplacePrimeDivisibilityCell01 a x p q *
      mobiusLaplacePrimeDivisibilityCell10 a x p q

/-- Finite inclusion--exclusion collapses the divisibility determinant to one cross product. -/
theorem mobiusLaplacePrimeDivisibilityDet_eq_massCross (a x : ℝ) (p q : ℕ) :
    mobiusLaplacePrimeDivisibilityDet a x p q =
      mobiusLaplaceRenewalMass a x * mobiusLaplaceRenewalMass (a * p * q) x -
        mobiusLaplaceRenewalMass (a * p) x * mobiusLaplaceRenewalMass (a * q) x := by
  simp only [mobiusLaplacePrimeDivisibilityDet,
    mobiusLaplacePrimeDivisibilityCell00, mobiusLaplacePrimeDivisibilityCell01,
    mobiusLaplacePrimeDivisibilityCell10, mobiusLaplacePrimeDivisibilityCell11]
  ring

/-- Exact exponential normal form of the prime-divisibility determinant. -/
theorem mobiusLaplacePrimeDivisibilityDet_eq_exp_sub_exp (a x : ℝ) (p q : ℕ) :
    mobiusLaplacePrimeDivisibilityDet a x p q =
      Real.exp (-(a * (1 + (p : ℝ) * (q : ℝ)) * x)) -
        Real.exp (-(a * ((p : ℝ) + (q : ℝ)) * x)) := by
  rw [mobiusLaplacePrimeDivisibilityDet_eq_massCross]
  simp only [mobiusLaplaceRenewalMass]
  rw [← Real.exp_add, ← Real.exp_add]
  ring_nf

/-- Row-zero marginal: indices not divisible by `p`. -/
theorem mobiusLaplacePrimeDivisibility_row0 (a x : ℝ) (p q : ℕ) :
    mobiusLaplacePrimeDivisibilityCell00 a x p q +
        mobiusLaplacePrimeDivisibilityCell01 a x p q =
      mobiusLaplaceRenewalMass a x - mobiusLaplaceRenewalMass (a * p) x := by
  simp only [mobiusLaplacePrimeDivisibilityCell00,
    mobiusLaplacePrimeDivisibilityCell01]
  ring

/-- Row-one marginal: indices divisible by `p`. -/
theorem mobiusLaplacePrimeDivisibility_row1 (a x : ℝ) (p q : ℕ) :
    mobiusLaplacePrimeDivisibilityCell10 a x p q +
        mobiusLaplacePrimeDivisibilityCell11 a x p q =
      mobiusLaplaceRenewalMass (a * p) x := by
  simp [mobiusLaplacePrimeDivisibilityCell10,
    mobiusLaplacePrimeDivisibilityCell11]

/-- Column-zero marginal: indices not divisible by `q`. -/
theorem mobiusLaplacePrimeDivisibility_col0 (a x : ℝ) (p q : ℕ) :
    mobiusLaplacePrimeDivisibilityCell00 a x p q +
        mobiusLaplacePrimeDivisibilityCell10 a x p q =
      mobiusLaplaceRenewalMass a x - mobiusLaplaceRenewalMass (a * q) x := by
  simp only [mobiusLaplacePrimeDivisibilityCell00,
    mobiusLaplacePrimeDivisibilityCell10]
  ring

/-- Column-one marginal: indices divisible by `q`. -/
theorem mobiusLaplacePrimeDivisibility_col1 (a x : ℝ) (p q : ℕ) :
    mobiusLaplacePrimeDivisibilityCell01 a x p q +
        mobiusLaplacePrimeDivisibilityCell11 a x p q =
      mobiusLaplaceRenewalMass (a * q) x := by
  simp [mobiusLaplacePrimeDivisibilityCell01,
    mobiusLaplacePrimeDivisibilityCell11]

/-- Every one-prime row and column marginal of the two-prime table is strictly positive. -/
theorem mobiusLaplacePrimeDivisibility_marginals_pos
    {a x : ℝ} {p q : ℕ} (ha : 0 < a) (hp : p.Prime) (hq : q.Prime)
    (hx : 0 < x) :
    0 < mobiusLaplacePrimeDivisibilityCell00 a x p q +
          mobiusLaplacePrimeDivisibilityCell01 a x p q ∧
    0 < mobiusLaplacePrimeDivisibilityCell10 a x p q +
          mobiusLaplacePrimeDivisibilityCell11 a x p q ∧
    0 < mobiusLaplacePrimeDivisibilityCell00 a x p q +
          mobiusLaplacePrimeDivisibilityCell10 a x p q ∧
    0 < mobiusLaplacePrimeDivisibilityCell01 a x p q +
          mobiusLaplacePrimeDivisibilityCell11 a x p q := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hap : a < a * (p : ℝ) := by
    simpa using mul_lt_mul_of_pos_left hp1 ha
  have haq : a < a * (q : ℝ) := by
    simpa using mul_lt_mul_of_pos_left hq1 ha
  constructor
  · rw [mobiusLaplacePrimeDivisibility_row0]
    exact sub_pos.mpr (mobiusLaplaceRenewalMass_strictAnti_scale hap hx)
  constructor
  · rw [mobiusLaplacePrimeDivisibility_row1]
    exact Real.exp_pos _
  constructor
  · rw [mobiusLaplacePrimeDivisibility_col0]
    exact sub_pos.mpr (mobiusLaplaceRenewalMass_strictAnti_scale haq hx)
  · rw [mobiusLaplacePrimeDivisibility_col1]
    exact Real.exp_pos _

/-- **Strict prime-pair anti-TP2 law.**  At every positive scale, the determinant of the
Möbius--Laplace renewal table for two prime divisibility channels is strictly negative.  For
distinct primes the four entries are the exact signed cylinder masses; the theorem itself is the
stronger algebraic sign law and does not need distinctness. -/
theorem mobiusLaplacePrimeDivisibilityDet_neg
    {a x : ℝ} {p q : ℕ} (ha : 0 < a) (hp : p.Prime) (hq : q.Prime)
    (hx : 0 < x) :
    mobiusLaplacePrimeDivisibilityDet a x p q < 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hpqpos : 0 < ((p : ℝ) - 1) * ((q : ℝ) - 1) :=
    mul_pos (sub_pos.mpr hp1) (sub_pos.mpr hq1)
  have hmul : 0 < a * (((p : ℝ) - 1) * ((q : ℝ) - 1)) * x :=
    mul_pos (mul_pos ha hpqpos) hx
  have horder : a * ((p : ℝ) + (q : ℝ)) * x <
      a * (1 + (p : ℝ) * (q : ℝ)) * x := by
    apply sub_pos.mp
    calc
      a * (1 + (p : ℝ) * (q : ℝ)) * x -
          a * ((p : ℝ) + (q : ℝ)) * x =
        a * (((p : ℝ) - 1) * ((q : ℝ) - 1)) * x := by ring
      _ > 0 := hmul
  have hexp := Real.exp_lt_exp.mpr (neg_lt_neg horder)
  rw [mobiusLaplacePrimeDivisibilityDet_eq_exp_sub_exp]
  linarith

/-! ## Forced negative values on every fine dilation lattice -/

/-- Multiplication by a positive integer identifies all positive integers with the multiples of
that integer.  This packages the exact reindexing needed to resolve divisibility-restricted
Lambert sums. -/
def pnatMulEquivDvd (m : ℕ+) : ℕ+ ≃ {n : ℕ+ // m ∣ n} where
  toFun k := ⟨m * k, dvd_mul_right m k⟩
  invFun n := PNat.divExact n.1 m
  left_inv k := by
    apply mul_left_cancel (a := m)
    exact PNat.mul_div_exact (dvd_mul_right m k)
  right_inv n := by
    apply Subtype.ext
    exact PNat.mul_div_exact n.2

/-- The sum of the Möbius--Laplace transform over dilation indices divisible by `m` is exactly
the renewal atom at scale `m`. -/
theorem tsum_pnat_mobiusDiscreteLaplaceTransform_dvd
    (m : ℕ+) (x : ℝ) (hx : 0 < x) :
    (∑' k : ℕ+, {k : ℕ+ | m ∣ k}.indicator
      (fun k => mobiusDiscreteLaplaceTransform ((k : ℝ) * x)) k) =
      Complex.exp (-((m : ℝ) * x)) := by
  rw [← tsum_subtype]
  calc
    (∑' k : {k : ℕ+ // m ∣ k},
        mobiusDiscreteLaplaceTransform ((k.1 : ℝ) * x)) =
      ∑' j : ℕ+, mobiusDiscreteLaplaceTransform (((m * j : ℕ+) : ℝ) * x) := by
        exact (Equiv.tsum_eq (pnatMulEquivDvd m)
          (fun k : {k : ℕ+ // m ∣ k} =>
            mobiusDiscreteLaplaceTransform ((k.1 : ℝ) * x))).symm
    _ = ∑' j : ℕ+, mobiusDiscreteLaplaceTransform
        ((j : ℝ) * ((m : ℝ) * x)) := by
      apply tsum_congr
      intro j
      congr 1
      push_cast
      ring
    _ = Complex.exp (-((m : ℝ) * x)) := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_neg] using
        tsum_pnat_mobiusDiscreteLaplaceTransform_dilate
          ((m : ℝ) * x) (mul_pos (by exact_mod_cast m.property) hx)

private theorem pnat_six_dvd_iff_two_dvd_and_three_dvd (k : ℕ+) :
    (6 : ℕ+) ∣ k ↔ (2 : ℕ+) ∣ k ∧ (3 : ℕ+) ∣ k := by
  constructor
  · intro h
    rcases h with ⟨c, rfl⟩
    constructor
    · exact ⟨3 * c, by ring⟩
    · exact ⟨2 * c, by ring⟩
  · rintro ⟨h2, h3⟩
    rcases h2 with ⟨a, ha⟩
    rcases h3 with ⟨b, hb⟩
    have h2nat : (2 : ℕ) ∣ (k : ℕ) :=
      ⟨(a : ℕ), congrArg Subtype.val ha⟩
    have h3nat : (3 : ℕ) ∣ (k : ℕ) :=
      ⟨(b : ℕ), congrArg Subtype.val hb⟩
    have h6nat : (6 : ℕ) ∣ (k : ℕ) :=
      (show Nat.Coprime 2 3 by norm_num).mul_dvd_of_dvd_of_dvd h2nat h3nat
    rcases h6nat with ⟨c, hc⟩
    have hcpos : 0 < c := by
      by_contra hcnot
      have hc0 : c = 0 := Nat.eq_zero_of_not_pos hcnot
      subst c
      have hk0 : (k : ℕ) = 0 := hc.trans (by norm_num)
      exact (Nat.ne_of_gt k.property) hk0
    exact ⟨⟨c, hcpos⟩, by apply PNat.eq; exact hc⟩

/-- Absolutely convergent dilation sum over indices divisible by neither `2` nor `3`. -/
def mobiusLaplaceTwoThreeFreeDilationSum (x : ℝ) : ℂ :=
  ∑' k : ℕ+, {k : ℕ+ | ¬ (2 : ℕ+) ∣ k ∧ ¬ (3 : ℕ+) ∣ k}.indicator
    (fun k => mobiusDiscreteLaplaceTransform ((k : ℝ) * x)) k

/-- Exact `2`--`3` inclusion--exclusion law for the dilation family. -/
theorem mobiusLaplaceTwoThreeFreeDilationSum_eq (x : ℝ) (hx : 0 < x) :
    mobiusLaplaceTwoThreeFreeDilationSum x =
      Complex.exp (-x) - Complex.exp (-(2 * x)) -
        Complex.exp (-(3 * x)) + Complex.exp (-(6 * x)) := by
  let f : ℕ+ → ℂ := fun k => mobiusDiscreteLaplaceTransform ((k : ℝ) * x)
  let S2 : Set ℕ+ := {k : ℕ+ | (2 : ℕ+) ∣ k}
  let S3 : Set ℕ+ := {k : ℕ+ | (3 : ℕ+) ∣ k}
  let S6 : Set ℕ+ := {k : ℕ+ | (6 : ℕ+) ∣ k}
  let S00 : Set ℕ+ := {k : ℕ+ | ¬ (2 : ℕ+) ∣ k ∧ ¬ (3 : ℕ+) ∣ k}
  have hf : Summable f := summable_pnat_mobiusDiscreteLaplaceTransform_dilate x hx
  have h2 : Summable (S2.indicator f) := hf.indicator S2
  have h3 : Summable (S3.indicator f) := hf.indicator S3
  have h6 : Summable (S6.indicator f) := hf.indicator S6
  have hpoint (k : ℕ+) :
      S00.indicator f k = f k - S2.indicator f k - S3.indicator f k + S6.indicator f k := by
    have hiff := pnat_six_dvd_iff_two_dvd_and_three_dvd k
    by_cases hk2 : (2 : ℕ+) ∣ k <;> by_cases hk3 : (3 : ℕ+) ∣ k <;>
      simp [S00, S2, S3, S6, Set.indicator, hk2, hk3, hiff]
  rw [mobiusLaplaceTwoThreeFreeDilationSum]
  change (∑' k : ℕ+, S00.indicator f k) = _
  calc
    (∑' k : ℕ+, S00.indicator f k) =
        ∑' k : ℕ+,
          ((f k - S2.indicator f k) - S3.indicator f k + S6.indicator f k) := by
      apply tsum_congr
      exact hpoint
    _ = (∑' k : ℕ+, ((f k - S2.indicator f k) - S3.indicator f k)) +
          (∑' k : ℕ+, S6.indicator f k) :=
      ((hf.sub h2).sub h3).tsum_add h6
    _ = ((∑' k : ℕ+, f k) - ∑' k : ℕ+, S2.indicator f k) -
          (∑' k : ℕ+, S3.indicator f k) + ∑' k : ℕ+, S6.indicator f k := by
      rw [(hf.sub h2).tsum_sub h3, hf.tsum_sub h2]
    _ = _ := by
      rw [tsum_pnat_mobiusDiscreteLaplaceTransform_dilate x hx]
      change _ - (∑' k : ℕ+, {k : ℕ+ | (2 : ℕ+) ∣ k}.indicator f k) -
        (∑' k : ℕ+, {k : ℕ+ | (3 : ℕ+) ∣ k}.indicator f k) +
        (∑' k : ℕ+, {k : ℕ+ | (6 : ℕ+) ∣ k}.indicator f k) = _
      rw [tsum_pnat_mobiusDiscreteLaplaceTransform_dvd (2 : ℕ+) x hx,
        tsum_pnat_mobiusDiscreteLaplaceTransform_dvd (3 : ℕ+) x hx,
        tsum_pnat_mobiusDiscreteLaplaceTransform_dvd (6 : ℕ+) x hx]
      norm_num

/-- The exact signed mass of indices divisible by neither `2` nor `3` is negative throughout the
explicit fine-scale window `0 < x ≤ log(4/3)`. -/
theorem mobiusLaplacePrimeDivisibilityCell00_two_three_neg
    {x : ℝ} (hx : 0 < x) (hxlog : x ≤ Real.log (4 / 3 : ℝ)) :
    mobiusLaplacePrimeDivisibilityCell00 1 x 2 3 < 0 := by
  let t := Real.exp (-x)
  have ht0 : 0 < t := Real.exp_pos _
  have htlt : t < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos hx)
  have hexplog : Real.exp (-Real.log (4 / 3 : ℝ)) = 3 / 4 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
  have ht34 : (3 / 4 : ℝ) ≤ t := by
    rw [← hexplog]
    exact Real.exp_le_exp.mpr (neg_le_neg hxlog)
  have ht2 : (9 / 16 : ℝ) ≤ t ^ 2 := by
    nlinarith [sq_nonneg (t - 3 / 4)]
  have ht3raw := mul_le_mul ht2 ht34 (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (sq_nonneg t)
  have ht3 : (27 / 64 : ℝ) ≤ t ^ 3 := by
    nlinarith [ht3raw]
  have ht4raw := mul_le_mul ht2 ht2 (by norm_num : (0 : ℝ) ≤ 9 / 16)
    (sq_nonneg t)
  have ht4 : (81 / 256 : ℝ) ≤ t ^ 4 := by
    nlinarith [ht4raw]
  have hq : 0 < t ^ 4 + t ^ 3 + t ^ 2 - 1 := by
    nlinarith
  have hnormal :
      mobiusLaplacePrimeDivisibilityCell00 1 x 2 3 =
        t - t ^ 2 - t ^ 3 + t ^ 6 := by
    simp only [mobiusLaplacePrimeDivisibilityCell00,
      mobiusLaplaceRenewalMass]
    have hpow (n : ℕ) : Real.exp (-(1 * (n : ℝ) * x)) = t ^ n := by
      rw [show -(1 * (n : ℝ) * x) = (n : ℝ) * (-x) by ring,
        Real.exp_nat_mul]
    have h1 : Real.exp (-(1 * x)) = t := by simpa using hpow 1
    have h2 : Real.exp (-(1 * ((2 : ℕ) : ℝ) * x)) = t ^ 2 := hpow 2
    have h3 : Real.exp (-(1 * ((3 : ℕ) : ℝ) * x)) = t ^ 3 := hpow 3
    have h6 : Real.exp (-(1 * ((2 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) * x)) = t ^ 6 := by
      rw [show -(1 * ((2 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) * x) =
          -(1 * ((6 : ℕ) : ℝ) * x) by norm_num]
      exact hpow 6
    rw [h1, h2, h3, h6]
  rw [hnormal]
  rw [show t - t ^ 2 - t ^ 3 + t ^ 6 =
      t * (t - 1) * (t ^ 4 + t ^ 3 + t ^ 2 - 1) by ring]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg ht0 (sub_neg.mpr htlt)) hq

/-- The `2`--`3`-free dilation sum has strictly negative real part on the same explicit window. -/
theorem mobiusLaplaceTwoThreeFreeDilationSum_re_neg
    {x : ℝ} (hx : 0 < x) (hxlog : x ≤ Real.log (4 / 3 : ℝ)) :
    (mobiusLaplaceTwoThreeFreeDilationSum x).re < 0 := by
  rw [mobiusLaplaceTwoThreeFreeDilationSum_eq x hx]
  have h := mobiusLaplacePrimeDivisibilityCell00_two_three_neg hx hxlog
  simp only [mobiusLaplacePrimeDivisibilityCell00,
    mobiusLaplaceRenewalMass] at h
  norm_num at h
  simpa [Complex.exp_re, Complex.mul_re, Complex.mul_im] using h

/-- **Forced negative Möbius--Laplace value.**  On every dilation lattice with
`0 < x ≤ log(4/3)`, some index divisible by neither `2` nor `3` has a transform value with
strictly negative real part. -/
theorem exists_twoThreeFree_mobiusDiscreteLaplaceTransform_re_neg
    {x : ℝ} (hx : 0 < x) (hxlog : x ≤ Real.log (4 / 3 : ℝ)) :
    ∃ k : ℕ+, (¬ (2 : ℕ+) ∣ k ∧ ¬ (3 : ℕ+) ∣ k) ∧
      (mobiusDiscreteLaplaceTransform ((k : ℝ) * x)).re < 0 := by
  let S00 : Set ℕ+ := {k : ℕ+ | ¬ (2 : ℕ+) ∣ k ∧ ¬ (3 : ℕ+) ∣ k}
  let f : ℕ+ → ℂ := fun k => mobiusDiscreteLaplaceTransform ((k : ℝ) * x)
  by_contra h
  push Not at h
  have hsum : Summable (S00.indicator f) :=
    (summable_pnat_mobiusDiscreteLaplaceTransform_dilate x hx).indicator S00
  have hre : (mobiusLaplaceTwoThreeFreeDilationSum x).re =
      ∑' k : ℕ+, (S00.indicator f k).re := by
    rw [mobiusLaplaceTwoThreeFreeDilationSum]
    simpa [Function.comp_def] using
      (hsum.hasSum.map Complex.reCLM Complex.reCLM.continuous).tsum_eq.symm
  have hterm (k : ℕ+) : 0 ≤ (S00.indicator f k).re := by
    by_cases hk : k ∈ S00
    · simp only [Set.indicator_of_mem hk]
      exact h k hk
    · simp [Set.indicator, hk]
  have hnonneg : 0 ≤ ∑' k : ℕ+, (S00.indicator f k).re :=
    tsum_nonneg hterm
  have hneg := mobiusLaplaceTwoThreeFreeDilationSum_re_neg hx hxlog
  rw [hre] at hneg
  exact (not_lt_of_ge hnonneg) hneg

/-- Quantitative first-atom lower bound: the real part is at least the first exponential atom
minus the exact geometric majorant for all later atoms. -/
theorem mobiusDiscreteLaplaceTransform_re_ge_firstAtom_sub_geometricTail
    {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) - Real.exp (-x) ^ 2 * (1 - Real.exp (-x))⁻¹ ≤
      (mobiusDiscreteLaplaceTransform x).re := by
  let q := Real.exp (-x)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos hx)
  have hsum := summable_mobiusDiscreteLaplaceTerm hx
  have hinj : Function.Injective (fun n : ℕ => n + 2) := by
    intro a b h
    exact Nat.add_right_cancel h
  have htailSum : Summable (fun n : ℕ => mobiusDiscreteLaplaceTerm x (n + 2)) :=
    hsum.comp_injective hinj
  have hdecomp : mobiusDiscreteLaplaceTransform x =
      (q : ℂ) + ∑' n : ℕ, mobiusDiscreteLaplaceTerm x (n + 2) := by
    have hsplit := hsum.sum_add_tsum_nat_add 2
    have hfinite :
        (∑ i ∈ Finset.range 2, mobiusDiscreteLaplaceTerm x i) = (q : ℂ) := by
      simp [Finset.sum_range_succ, mobiusDiscreteLaplaceTerm, q,
        Complex.ofReal_exp]
    rw [mobiusDiscreteLaplaceTransform]
    rw [← hfinite]
    exact hsplit.symm
  have hgeom : Summable (fun n : ℕ => q ^ (n + 2)) := by
    have hbase := summable_geometric_of_lt_one hq0 hq1
    rw [show (fun n : ℕ => q ^ (n + 2)) = fun n : ℕ => q ^ 2 * q ^ n by
      funext n
      rw [Nat.add_comm, pow_add]]
    exact hbase.mul_left (q ^ 2)
  have hterm (n : ℕ) :
      ‖mobiusDiscreteLaplaceTerm x (n + 2)‖ ≤ q ^ (n + 2) := by
    rw [mobiusDiscreteLaplaceTerm, norm_mul, Complex.norm_exp]
    have hmu :
        ‖((ArithmeticFunction.moebius (n + 2) : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 2)
    have hexp : Real.exp (-(((n + 2 : ℕ) : ℝ) * x)) = q ^ (n + 2) := by
      rw [show -(((n + 2 : ℕ) : ℝ) * x) = ((n + 2 : ℕ) : ℝ) * (-x) by ring,
        Real.exp_nat_mul]
    change ‖((ArithmeticFunction.moebius (n + 2) : ℤ) : ℂ)‖ *
      Real.exp (-(((n + 2 : ℕ) : ℝ) * x)) ≤ q ^ (n + 2)
    rw [hexp]
    simpa using mul_le_mul_of_nonneg_right hmu (pow_nonneg hq0 _)
  have htailNorm :
      ‖∑' n : ℕ, mobiusDiscreteLaplaceTerm x (n + 2)‖ ≤
        q ^ 2 * (1 - q)⁻¹ := by
    calc
      ‖∑' n : ℕ, mobiusDiscreteLaplaceTerm x (n + 2)‖
          ≤ ∑' n : ℕ, ‖mobiusDiscreteLaplaceTerm x (n + 2)‖ :=
        norm_tsum_le_tsum_norm htailSum.norm
      _ ≤ ∑' n : ℕ, q ^ (n + 2) :=
        htailSum.norm.tsum_le_tsum hterm hgeom
      _ = ∑' n : ℕ, q ^ 2 * q ^ n := by
        apply tsum_congr
        intro n
        rw [Nat.add_comm n 2, pow_add]
      _ = q ^ 2 * ∑' n : ℕ, q ^ n := tsum_mul_left
      _ = q ^ 2 * (1 - q)⁻¹ := by
        rw [tsum_geometric_of_lt_one hq0 hq1]
  change q - q ^ 2 * (1 - q)⁻¹ ≤ (mobiusDiscreteLaplaceTransform x).re
  rw [hdecomp]
  change q - q ^ 2 * (1 - q)⁻¹ ≤
    q + (∑' n : ℕ, mobiusDiscreteLaplaceTerm x (n + 2)).re
  have hreNorm :
      |(∑' n : ℕ, mobiusDiscreteLaplaceTerm x (n + 2)).re| ≤
        q ^ 2 * (1 - q)⁻¹ :=
    (Complex.abs_re_le_norm _).trans htailNorm
  have htailLower := (abs_le.mp hreNorm).1
  linarith

/-- Past `log 2`, the first Möbius--Laplace atom dominates the full tail, forcing nonnegative real
part.  This uses only `|mu(n)| ≤ 1` and the exact geometric tail. -/
theorem mobiusDiscreteLaplaceTransform_re_nonneg_of_log_two_le
    {x : ℝ} (hx : Real.log 2 ≤ x) :
    0 ≤ (mobiusDiscreteLaplaceTransform x).re := by
  let q := Real.exp (-x)
  have hxpos : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num)) hx
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqhalf : q ≤ 1 / 2 := by
    have htwo : (0 : ℝ) < 2 := by norm_num
    have hexplog : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log htwo]
      norm_num
    rw [← hexplog]
    exact Real.exp_le_exp.mpr (neg_le_neg hx)
  have hq1 : q < 1 := lt_of_le_of_lt hqhalf (by norm_num)
  have htailLe : q ^ 2 * (1 - q)⁻¹ ≤ q := by
    have hden : 0 < 1 - q := sub_pos.mpr hq1
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hbound :=
    mobiusDiscreteLaplaceTransform_re_ge_firstAtom_sub_geometricTail hxpos
  change q - q ^ 2 * (1 - q)⁻¹ ≤
    (mobiusDiscreteLaplaceTransform x).re at hbound
  linarith

/-- Strictly past `log 2`, first-atom dominance is strict. -/
theorem mobiusDiscreteLaplaceTransform_re_pos_of_log_two_lt
    {x : ℝ} (hx : Real.log 2 < x) :
    0 < (mobiusDiscreteLaplaceTransform x).re := by
  let q := Real.exp (-x)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxpos : 0 < x := lt_trans hlog2 hx
  have hq0 : 0 < q := Real.exp_pos _
  have hqhalf : q < 1 / 2 := by
    have htwo : (0 : ℝ) < 2 := by norm_num
    have hexplog : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log htwo]
      norm_num
    rw [← hexplog]
    exact Real.exp_lt_exp.mpr (neg_lt_neg hx)
  have hq1 : q < 1 := lt_trans hqhalf (by norm_num)
  have htailLt : q ^ 2 * (1 - q)⁻¹ < q := by
    have hden : 0 < 1 - q := sub_pos.mpr hq1
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hbound :=
    mobiusDiscreteLaplaceTransform_re_ge_firstAtom_sub_geometricTail hxpos
  change q - q ^ 2 * (1 - q)⁻¹ ≤
    (mobiusDiscreteLaplaceTransform x).re at hbound
  linarith

/-- The forced negative value on every fine dilation lattice occurs before scale `log 2`.  Thus
its dilation index has the explicit bound `k < log(2)/x`. -/
theorem exists_twoThreeFree_mobiusDiscreteLaplaceTransform_re_neg_bounded
    {x : ℝ} (hx : 0 < x) (hxlog : x ≤ Real.log (4 / 3 : ℝ)) :
    ∃ k : ℕ+, (¬ (2 : ℕ+) ∣ k ∧ ¬ (3 : ℕ+) ∣ k) ∧
      (k : ℝ) * x < Real.log 2 ∧ (k : ℝ) < Real.log 2 / x ∧
      (mobiusDiscreteLaplaceTransform ((k : ℝ) * x)).re < 0 := by
  rcases exists_twoThreeFree_mobiusDiscreteLaplaceTransform_re_neg hx hxlog with
    ⟨k, hkfree, hkneg⟩
  have hscale : (k : ℝ) * x < Real.log 2 := by
    by_contra hnot
    have hnonneg := mobiusDiscreteLaplaceTransform_re_nonneg_of_log_two_le
      (le_of_not_gt hnot)
    linarith
  exact ⟨k, hkfree, hscale, (lt_div_iff₀ hx).2 hscale, hkneg⟩

/-- The explicit negativity window below is nonempty. -/
theorem log_two_div_five_lt_log_four_thirds :
    Real.log 2 / 5 < Real.log (4 / 3 : ℝ) := by
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hpowpos : (0 : ℝ) < (4 / 3 : ℝ) ^ 5 := by positivity
  have hlt : (2 : ℝ) < (4 / 3 : ℝ) ^ 5 := by norm_num
  have hlog := Real.strictMonoOn_log hpos hpowpos hlt
  rw [Real.log_pow] at hlog
  nlinarith

/-- **Explicit interval of strict negativity.**  Every scale between `log 2 / 5` and
`log(4/3)` has a strictly negative Möbius--Laplace transform.  The upper endpoint forces a
negative value on a dilation index coprime to `6`; the lower endpoint and first-atom dominance
exclude every such index except `1`. -/
theorem mobiusDiscreteLaplaceTransform_re_neg_on_explicit_interval
    {x : ℝ} (hxlow : Real.log 2 / 5 ≤ x)
    (hxhigh : x ≤ Real.log (4 / 3 : ℝ)) :
    (mobiusDiscreteLaplaceTransform x).re < 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxpos : 0 < x := by nlinarith
  rcases exists_twoThreeFree_mobiusDiscreteLaplaceTransform_re_neg hxpos hxhigh with
    ⟨k, hkfree, hkneg⟩
  have hkone : k = 1 := by
    by_contra hkone
    have hk1nat : (k : ℕ) ≠ 1 := by
      intro hk
      apply hkone
      apply PNat.eq
      exact hk
    have hk2nat : (k : ℕ) ≠ 2 := by
      intro hk
      apply hkfree.1
      have hkeq : k = (2 : ℕ+) := by
        apply PNat.eq
        exact hk
      rw [hkeq]
    have hk3nat : (k : ℕ) ≠ 3 := by
      intro hk
      apply hkfree.2
      have hkeq : k = (3 : ℕ+) := by
        apply PNat.eq
        exact hk
      rw [hkeq]
    have hk4nat : (k : ℕ) ≠ 4 := by
      intro hk
      apply hkfree.1
      have hkeq : k = (4 : ℕ+) := by
        apply PNat.eq
        exact hk
      rw [hkeq]
      exact ⟨2, rfl⟩
    have hkfiveNat : 5 ≤ (k : ℕ) := by
      have hkposNat : 0 < (k : ℕ) := k.property
      omega
    have hkfive : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkfiveNat
    have hlogScale : Real.log 2 ≤ (k : ℝ) * x := by
      calc
        Real.log 2 ≤ 5 * x := by nlinarith
        _ ≤ (k : ℝ) * x := mul_le_mul_of_nonneg_right hkfive hxpos.le
    have hnonneg :=
      mobiusDiscreteLaplaceTransform_re_nonneg_of_log_two_le hlogScale
    linarith
  subst k
  simpa using hkneg

/-- In particular, the transform is strictly negative at the exact algebraic-logarithmic scale
`log 2 / 5`; this also certifies that the interval theorem is nonvacuous. -/
theorem mobiusDiscreteLaplaceTransform_re_neg_at_log_two_div_five :
    (mobiusDiscreteLaplaceTransform (Real.log 2 / 5)).re < 0 :=
  mobiusDiscreteLaplaceTransform_re_neg_on_explicit_interval le_rfl
    log_two_div_five_lt_log_four_thirds.le

/-- **A genuine positive-axis zero in a fixed exact bracket.**  Strict negativity at `log(4/3)`,
strict first-atom positivity at `3 log(4/3) > log 2`, and continuity force an actual transform
zero strictly between those scales. -/
theorem exists_mobiusDiscreteLaplaceTransform_pos_real_zero :
    ∃ c ∈ Ioo (Real.log (4 / 3 : ℝ)) (3 * Real.log (4 / 3 : ℝ)),
      mobiusDiscreteLaplaceTransform c = 0 := by
  let a : ℝ := Real.log (4 / 3 : ℝ)
  have ha : 0 < a := Real.log_pos (by norm_num)
  have hneg : (mobiusDiscreteLaplaceTransform a).re < 0 := by
    exact mobiusDiscreteLaplaceTransform_re_neg_on_explicit_interval
      log_two_div_five_lt_log_four_thirds.le le_rfl
  have hlogScale : Real.log 2 < 3 * a := by
    have hpos2 : (0 : ℝ) < 2 := by norm_num
    have hposPow : (0 : ℝ) < (4 / 3 : ℝ) ^ 3 := by positivity
    have hlt : (2 : ℝ) < (4 / 3 : ℝ) ^ 3 := by norm_num
    have hlog := Real.strictMonoOn_log hpos2 hposPow hlt
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have hpos : 0 < (mobiusDiscreteLaplaceTransform (3 * a)).re :=
    mobiusDiscreteLaplaceTransform_re_pos_of_log_two_lt hlogScale
  have hab : a < 3 * a := by nlinarith
  have hsub : Icc a (3 * a) ⊆ Ioi 0 := by
    intro y hy
    exact lt_of_lt_of_le ha hy.1
  have hcont : ContinuousOn
      (fun y : ℝ => (mobiusDiscreteLaplaceTransform y).re)
      (Icc a (3 * a)) :=
    Complex.continuous_re.comp_continuousOn
      (continuousOn_mobiusDiscreteLaplaceTransform.mono hsub)
  have hzeroMem : (0 : ℝ) ∈ Icc
      (mobiusDiscreteLaplaceTransform a).re
      (mobiusDiscreteLaplaceTransform (3 * a)).re :=
    ⟨hneg.le, hpos.le⟩
  obtain ⟨c, hc, hczeroRe⟩ := intermediate_value_Icc hab.le hcont hzeroMem
  have hac : a < c := by
    apply lt_of_le_of_ne hc.1
    intro hacEq
    rw [← hacEq] at hczeroRe
    linarith
  have hcb : c < 3 * a := by
    apply lt_of_le_of_ne hc.2
    intro hcbEq
    rw [hcbEq] at hczeroRe
    linarith
  have hcpos : 0 < c := lt_trans ha hac
  have hczeroIm := mobiusDiscreteLaplaceTransform_im_eq_zero hcpos
  refine ⟨c, ⟨hac, hcb⟩, ?_⟩
  apply Complex.ext
  · simpa using hczeroRe
  · simpa using hczeroIm

/-- In ordinary generating-function coordinate `q = exp(-c)`, the zero lies in the fixed rational
interval `(27/64, 3/4)`. -/
theorem exists_mobiusDiscreteLaplaceTransform_zero_with_exp_in_rational_interval :
    ∃ c : ℝ, (27 / 64 : ℝ) < Real.exp (-c) ∧
      Real.exp (-c) < 3 / 4 ∧ mobiusDiscreteLaplaceTransform c = 0 := by
  obtain ⟨c, hc, hzero⟩ := exists_mobiusDiscreteLaplaceTransform_pos_real_zero
  have hcLower := hc.1
  have hcUpper := hc.2
  let a : ℝ := Real.log (4 / 3 : ℝ)
  have hexpNegA : Real.exp (-a) = (3 / 4 : ℝ) := by
    dsimp [a]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
  have hexpNegThreeA : Real.exp (-(3 * a)) = (27 / 64 : ℝ) := by
    calc
      Real.exp (-(3 * a)) = Real.exp (-a) ^ 3 := by
        rw [show -(3 * a) = ((3 : ℕ) : ℝ) * (-a) by ring]
        exact Real.exp_nat_mul (-a) 3
      _ = 27 / 64 := by rw [hexpNegA]; norm_num
  have hLowerExp : (27 / 64 : ℝ) < Real.exp (-c) := by
    rw [← hexpNegThreeA]
    exact Real.exp_lt_exp.mpr (neg_lt_neg hcUpper)
  have hUpperExp : Real.exp (-c) < (3 / 4 : ℝ) := by
    rw [← hexpNegA]
    exact Real.exp_lt_exp.mpr (neg_lt_neg hcLower)
  exact ⟨c, hLowerExp, hUpperExp, hzero⟩

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

/-- Analyticity of the concrete Mellin transform propagates its denominator-free classical
identity to every point of `Re s > 1/2`.  This public form is also the boundary-rigidity interface:
it retains the canonical Mellin witness rather than hiding it behind an existential wall. -/
theorem mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_analyticOnNhd
    (hG : AnalyticOnNhd ℂ (mellin mobiusDiscreteLaplaceTransform) rightHalf) :
    ∀ s ∈ rightHalf,
      mellin mobiusDiscreteLaplaceTransform s * zetaResidueUnit s =
        Complex.Gamma s * (s - 1) := by
  let G : ℂ → ℂ := mellin mobiusDiscreteLaplaceTransform
  have hleft : AnalyticOnNhd ℂ
      (fun s => G s * zetaResidueUnit s) rightHalf := by
    intro s hs
    exact (hG s hs).mul (RHTower.analyticAt_zetaResidueUnit s)
  have hright : AnalyticOnNhd ℂ
      (fun s => Complex.Gamma s * (s - 1)) rightHalf := by
    intro s hs
    have hspos : 0 < s.re := lt_trans (by norm_num) (mem_rightHalf.mp hs)
    exact (HTGeometry.analyticAt_Gamma_of_re_pos hspos).mul
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
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    convex_rightHalf.isPreconnected two_mem_rightHalf hevent

/-- Any proof that the concrete Möbius--Laplace Mellin transform is analytic on `Re s > 1/2`
discharges the continuation wall.  This separates the source estimate from the fixed identity-
theorem argument. -/
theorem mobiusLaplaceMellinContinuationWall_of_analyticOnNhd_mellin
    (hG : AnalyticOnNhd ℂ (mellin mobiusDiscreteLaplaceTransform) rightHalf) :
    MobiusLaplaceMellinContinuationWall :=
  ⟨mellin mobiusDiscreteLaplaceTransform, hG,
    mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_analyticOnNhd hG⟩

/-- The Mellin bridge isolated as a proposition.  It is discharged below for the concrete source. -/
def MobiusLaplaceDecayToContinuationBridge : Prop :=
  MobiusDiscreteLaplaceHalfDecay → MobiusLaplaceMellinContinuationWall

/-- **Unconditional source-to-continuation bridge.**  The half-power bound makes the concrete
Mellin transform analytic on `Re s > 1/2`; the identity theorem propagates its classical
`Gamma/zeta` identity from `Re s > 1` across the connected half-plane. -/
theorem mobiusLaplaceDecayToContinuationBridge :
    MobiusLaplaceDecayToContinuationBridge := by
  intro hdecay
  exact mobiusLaplaceMellinContinuationWall_of_analyticOnNhd_mellin
    (analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform hdecay)

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

/-- RH makes the regularized zeta residue unit nonzero throughout `Re s > 1/2`. -/
theorem zetaResidueUnit_ne_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) {s : ℂ} (hs : s ∈ rightHalf) :
    zetaResidueUnit s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    simp [zetaResidueUnit]
  · have hspos : 0 < s.re := lt_trans (by norm_num) (mem_rightHalf.mp hs)
    have hxi : xi s ≠ 0 := rh_iff_xi_ne_zero_right.mp hRH s hs
    have hzeta : riemannZeta s ≠ 0 := (xi_eq_zero_iff hspos hs1).not.mp hxi
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    simp [zetaResidueUnit, hs1, hsub, hzeta]

/-- Under RH the Mellin wall is witnessed by the canonical analytic quotient
`Gamma(s) * (s - 1) / zetaResidueUnit(s)`. -/
theorem mobiusLaplaceMellinContinuationWall_of_riemannHypothesis
    (hRH : RiemannHypothesis) : MobiusLaplaceMellinContinuationWall := by
  let G : ℂ → ℂ := fun s => Complex.Gamma s * (s - 1) / zetaResidueUnit s
  refine ⟨G, ?_, ?_⟩
  · intro s hs
    have hspos : 0 < s.re := lt_trans (by norm_num) (mem_rightHalf.mp hs)
    exact ((HTGeometry.analyticAt_Gamma_of_re_pos hspos).mul
      (analyticAt_id.sub analyticAt_const)).div
        (RHTower.analyticAt_zetaResidueUnit s)
        (zetaResidueUnit_ne_zero_of_riemannHypothesis hRH hs)
  · intro s hs
    dsimp [G]
    exact div_mul_cancel₀ _ (zetaResidueUnit_ne_zero_of_riemannHypothesis hRH hs)

/-- **Exact classification of the continuation wall.**  The wall is equivalent to RH.  Thus an
independent proof must construct its analytic witness without assuming right-half zero-freeness. -/
theorem mobiusLaplaceMellinContinuationWall_iff_riemannHypothesis :
    MobiusLaplaceMellinContinuationWall ↔ RiemannHypothesis :=
  ⟨mobiusLaplaceMellinContinuationWall_implies_riemannHypothesis,
    mobiusLaplaceMellinContinuationWall_of_riemannHypothesis⟩

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
