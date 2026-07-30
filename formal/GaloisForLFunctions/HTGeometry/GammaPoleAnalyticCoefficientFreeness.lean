import GaloisForLFunctions.HTGeometry.GammaPoleFormalGermFreeness
import GaloisForLFunctions.HTGeometry.GammaFactorialAllOrderPoleJet
import GaloisForLFunctions.HTGeometry.LogDerivBellTransfer
import GaloisForLFunctions.Hurwitz.PolygammaHurwitzValue

/-!
# Algebraic independence of the actual analytic Gamma pole germs

For the canonical factorial scale

`s_n = (-1)^(n+1) / n!`,

define the analytic unit at the pole `-n` by

`U_n(x) = Gamma(1 + s_n x) / product_{k=1}^n (1 - s_n x / k)`.

The exact Gamma recurrence gives `Gamma(-n + s_n x) = -U_n(x) / x` near the puncture, so the
Taylor coefficients of `U_n` are the genuine regular Laurent coefficients of the factorially
rescaled Gamma pole, not formal surrogates.

This module identifies every logarithmic jet of `U_n` with the factorial--harmonic--zeta sequence
from `GammaFactorialHarmonicSequenceFreeness`.  The Bell transform then identifies every Taylor
coefficient of `U_n` with the formally free coefficient family from
`GammaPoleFormalGermFreeness`.  Consequently:

* all logarithmic-jet sequences of the actual units are countably algebraically independent over
  `ℂ` as germs in the pole index;
* all regular Laurent-coefficient sequences are countably algebraically independent over `ℂ`;
* the resulting power series over the pole-index germ ring has no nonzero finite-order algebraic
  differential relation over `ℂ[X]`.

No numerical approximation of Euler's constant or zeta values occurs.  They enter only through
the exact values of the polygamma jets at one.
-/

open Complex Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

def gammaPoleRegularUnit (n : ℕ) (x : ℂ) : ℂ :=
  Complex.Gamma (reciprocalGammaFactorialScale n * x + 1) /
    reciprocalGammaNormalizedProduct n x

def gammaPoleRegularLogDeriv (n : ℕ) (x : ℂ) : ℂ :=
  reciprocalGammaFactorialScale n *
      Complex.digamma (reciprocalGammaFactorialScale n * x + 1) +
    reciprocalGammaFactorialScale n *
      shiftedHarmonicPowerSum 1 n (reciprocalGammaFactorialScale n * x)

theorem reciprocalGammaFactorialScale_ne_zero (n : ℕ) :
    reciprocalGammaFactorialScale n ≠ 0 := by
  exact div_ne_zero (pow_ne_zero _ (by norm_num))
    (by exact_mod_cast Nat.factorial_ne_zero n)

theorem reciprocalGammaNormalizedProduct_zero (n : ℕ) :
    reciprocalGammaNormalizedProduct n 0 = 1 := by
  simp [reciprocalGammaNormalizedProduct]

theorem gammaPoleRegularUnit_zero (n : ℕ) : gammaPoleRegularUnit n 0 = 1 := by
  simp [gammaPoleRegularUnit, reciprocalGammaNormalizedProduct_zero]

theorem logDeriv_gammaPoleRegularUnit {n : ℕ} {x : ℂ}
    (hpole : ∀ m : ℕ,
      reciprocalGammaFactorialScale n * x + 1 ≠ -(m : ℂ))
    (hprod : reciprocalGammaNormalizedProduct n x ≠ 0) :
    logDeriv (gammaPoleRegularUnit n) x = gammaPoleRegularLogDeriv n x := by
  have hnumne :
      Complex.Gamma (reciprocalGammaFactorialScale n * x + 1) ≠ 0 :=
    Complex.Gamma_ne_zero hpole
  have hnumdiff : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (reciprocalGammaFactorialScale n * z + 1)) x :=
    (analyticAt_Gamma _ hpole).differentiableAt.comp x
      ((differentiableAt_id.const_mul _).add_const _)
  have hdendiff : DifferentiableAt ℂ (reciprocalGammaNormalizedProduct n) x := by
    unfold reciprocalGammaNormalizedProduct
    fun_prop
  change logDeriv
      (fun z : ℂ => Complex.Gamma (reciprocalGammaFactorialScale n * z + 1) /
        reciprocalGammaNormalizedProduct n z) x = _
  rw [logDeriv_div x hnumne hprod hnumdiff hdendiff]
  rw [HTGeometry.logDeriv_Gamma_affine x hpole]
  rw [show logDeriv (reciprocalGammaNormalizedProduct n) x =
      ∑ j ∈ Finset.range n,
        logDeriv (fun z : ℂ =>
          1 - reciprocalGammaFactorialScale n * z / ((j + 1 : ℕ) : ℂ)) x by
    change logDeriv
        (fun z : ℂ => ∏ j ∈ Finset.range n,
          (1 - reciprocalGammaFactorialScale n * z / ((j + 1 : ℕ) : ℂ))) x = _
    apply logDeriv_prod
    · intro j hj
      exact Finset.prod_ne_zero_iff.mp hprod j hj
    · intro j hj
      fun_prop]
  rw [gammaPoleRegularLogDeriv, shiftedHarmonicPowerSum]
  simp only [pow_one]
  have hterm : ∀ j ∈ Finset.range n,
      logDeriv (fun z : ℂ =>
          1 - reciprocalGammaFactorialScale n * z / ((j + 1 : ℕ) : ℂ)) x =
        -reciprocalGammaFactorialScale n /
          (((j + 1 : ℕ) : ℂ) - reciprocalGammaFactorialScale n * x) := by
    intro j hj
    have hj0 : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero j
    have hfac :
        1 - reciprocalGammaFactorialScale n * x / ((j + 1 : ℕ) : ℂ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hprod j hj
    rw [logDeriv_apply]
    have hd : deriv (fun z : ℂ =>
        1 - reciprocalGammaFactorialScale n * z / ((j + 1 : ℕ) : ℂ)) x =
        -reciprocalGammaFactorialScale n / ((j + 1 : ℕ) : ℂ) := by
      have h := (hasDerivAt_const x (1 : ℂ)).sub
        (((hasDerivAt_const x (reciprocalGammaFactorialScale n)).mul
          (hasDerivAt_id x)).div_const (((j + 1 : ℕ) : ℂ)))
      convert! h.deriv using 1
      all_goals ring_nf
    rw [hd]
    field_simp [hj0, hfac]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.mul_sum]
  simp_rw [neg_div, div_eq_mul_inv]
  rw [Finset.sum_neg_distrib]
  ring

theorem iteratedDeriv_natSucc_sub_inv_zero (m k : ℕ) :
    iteratedDeriv m (fun z : ℂ => (((k + 1 : ℕ) : ℂ) - z)⁻¹) 0 =
      (m.factorial : ℂ) * ((((k + 1 : ℕ) : ℂ) ^ (m + 1))⁻¹) := by
  have hk0 : (((k + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have hfun : (fun z : ℂ => (((k + 1 : ℕ) : ℂ) - z)⁻¹) =
      fun z : ℂ => (-1 : ℂ) * (z + (-((k + 1 : ℕ) : ℂ)))⁻¹ := by
    funext z
    rw [show (((k + 1 : ℕ) : ℂ) - z) =
      -(z + (-((k + 1 : ℕ) : ℂ))) by ring, inv_neg]
    simp
  rw [hfun, congrFun (iteratedDeriv_const_mul_field (-1 : ℂ)
    (fun z : ℂ => (z + (-((k + 1 : ℕ) : ℂ)))⁻¹) m) 0]
  rw [iteratedDeriv_inv_add_const (-((k + 1 : ℕ) : ℂ)) m 0 (by
    simpa only [zero_add] using neg_ne_zero.mpr hk0)]
  simp only [zero_add]
  rw [show (-(((k + 1 : ℕ) : ℂ))) ^ (m + 1) =
    (-1 : ℂ) ^ (m + 1) * (((k + 1 : ℕ) : ℂ)) ^ (m + 1) by rw [neg_pow]]
  field_simp [hk0]
  rw [pow_succ]
  ring

theorem iteratedDeriv_shiftedHarmonicPowerSum_one_scale_zero
    (m n : ℕ) (s : ℂ) :
    iteratedDeriv m
        (fun x : ℂ => shiftedHarmonicPowerSum 1 n (s * x)) 0 =
      s ^ m * (m.factorial : ℂ) * shiftedHarmonicPowerSum (m + 1) n 0 := by
  unfold shiftedHarmonicPowerSum
  have hfun :
      (fun x : ℂ => ∑ j ∈ Finset.range n,
        (((((j + 1 : ℕ) : ℂ) - s * x) ^ 1)⁻¹)) =
      ∑ j ∈ Finset.range n,
        (fun x : ℂ => (((((j + 1 : ℕ) : ℂ) - s * x) ^ 1)⁻¹)) := by
    funext x
    simp
  rw [hfun]
  simp only [pow_one]
  rw [iteratedDeriv_sum (fun j hj => by
    have hj0 : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero j
    have hbase : ContDiffAt ℂ m
        (fun x : ℂ => (((j + 1 : ℕ) : ℂ) - s * x)) 0 := by fun_prop
    exact hbase.inv (by simpa using hj0))]
  simp only [sub_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_comp_mul_left_uncond
    (fun z : ℂ => (((j + 1 : ℕ) : ℂ) - z)⁻¹) s m 0]
  rw [mul_zero, iteratedDeriv_natSucc_sub_inv_zero]
  ring

theorem iteratedDeriv_gammaPoleRegularLogDeriv_zero (m n : ℕ) :
    iteratedDeriv m (gammaPoleRegularLogDeriv n) 0 =
      reciprocalGammaFactorialScale n ^ (m + 1) *
        (iteratedDeriv m Complex.digamma 1 +
          (m.factorial : ℂ) * shiftedHarmonicPowerSum (m + 1) n 0) := by
  let s := reciprocalGammaFactorialScale n
  have hoff : ∀ p : ℕ, (1 : ℂ) ≠ -(p : ℂ) := by
    intro p hp
    have hre := congrArg Complex.re hp
    norm_num only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have hpsi : ContDiffAt ℂ m
      (fun x : ℂ => s * Complex.digamma (s * x + 1)) 0 := by
    have haff : AnalyticAt ℂ (fun x : ℂ => s * x + 1) 0 := by fun_prop
    have hcomp : AnalyticAt ℂ (fun x : ℂ => Complex.digamma (s * x + 1)) 0 :=
      by
        simpa [Function.comp_def] using
          (AnalyticAt.comp (g := Complex.digamma) (f := fun x : ℂ => s * x + 1)
            (analyticAt_digamma_of_offPoles (by simpa using hoff)) haff)
    have hc : AnalyticAt ℂ (fun _x : ℂ => s) 0 := analyticAt_const
    exact (hc.mul hcomp).contDiffAt
  have htail : ContDiffAt ℂ m
      (fun x : ℂ => s * shiftedHarmonicPowerSum 1 n (s * x)) 0 := by
    have hc : ContDiffAt ℂ m (fun _x : ℂ => s) 0 := contDiffAt_const
    apply hc.mul
    unfold shiftedHarmonicPowerSum
    apply ContDiffAt.sum
    intro j hj
    have hj0 : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero j
    have hbase : ContDiffAt ℂ m
        (fun x : ℂ => ((((j + 1 : ℕ) : ℂ) - s * x) ^ 1)) 0 := by fun_prop
    exact hbase.inv (by simpa using hj0)
  change iteratedDeriv m
      ((fun x : ℂ => s * Complex.digamma (s * x + 1)) +
        (fun x : ℂ => s * shiftedHarmonicPowerSum 1 n (s * x))) 0 = _
  rw [iteratedDeriv_add hpsi htail]
  rw [congrFun (iteratedDeriv_const_mul_field s
    (fun x : ℂ => Complex.digamma (s * x + 1)) m) 0]
  rw [iteratedDeriv_comp_mul_left_uncond
    (fun z : ℂ => Complex.digamma (z + 1)) s m 0]
  simp only [mul_zero]
  rw [congrFun (_root_.iteratedDeriv_comp_add_const m Complex.digamma 1) 0]
  rw [congrFun (iteratedDeriv_const_mul_field s
    (fun x : ℂ => shiftedHarmonicPowerSum 1 n (s * x)) m) 0]
  rw [iteratedDeriv_shiftedHarmonicPowerSum_one_scale_zero]
  dsimp [s]
  ring

theorem signedFactorialSequence_succ_eq (n : ℕ) :
    signedFactorialSequence (n + 1) =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) := by
  induction n with
  | zero => simp [signedFactorialSequence]
  | succ n ih =>
      rw [signedFactorialSequence, Finset.prod_range_succ]
      change signedFactorialSequence (n + 1) *
          (if n + 1 = 0 then 1 else -((n + 1 : ℕ) : ℂ)) = _
      rw [ih]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.factorial_succ, pow_succ]
      push_cast
      ring

theorem reciprocalSignedFactorialSequence_succ_eq_neg_scale (n : ℕ) :
    reciprocalSignedFactorialSequence (n + 1) =
      -reciprocalGammaFactorialScale n := by
  rw [reciprocalSignedFactorialSequence, signedFactorialSequence_succ_eq,
    reciprocalGammaFactorialScale]
  have hn0 : ((n.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hsignsq : (((-1 : ℂ) ^ n) ^ 2) = 1 := by
    rw [← pow_mul, show n * 2 = 2 * n by omega, pow_mul]
    norm_num
  field_simp [hn0]
  rw [pow_succ]
  rw [show -((-1 : ℂ) ^ n * ((-1 : ℂ) ^ n * -1)) =
      ((-1 : ℂ) ^ n) ^ 2 by ring, hsignsq]

theorem harmonicJetSequence_succ_eq_shiftedHarmonicPowerSum
    (j n : ℕ) :
    harmonicJetSequence j (n + 1) =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) *
        shiftedHarmonicPowerSum (j + 1) n 0 := by
  induction n with
  | zero => simp [harmonicJetSequence, shiftedHarmonicPowerSum]
  | succ n ih =>
      rw [harmonicJetSequence_succ, ih]
      unfold shiftedHarmonicPowerSum
      rw [Finset.sum_range_succ]
      simp only [sub_zero]
      ring

theorem iteratedDeriv_gammaPoleRegularLogDeriv_zero_eq_sequence
    (j n : ℕ) :
    iteratedDeriv j (gammaPoleRegularLogDeriv n) 0 =
      reciprocalSignedFactorialSequence (n + 1) ^ (j + 1) *
        (-harmonicJetSequence j (n + 1) +
          ((j + 1).factorial : ℂ) * gammaPoleLogConstant j) := by
  rw [iteratedDeriv_gammaPoleRegularLogDeriv_zero,
    reciprocalSignedFactorialSequence_succ_eq_neg_scale,
    harmonicJetSequence_succ_eq_shiftedHarmonicPowerSum]
  cases j with
  | zero =>
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, zero_add,
        pow_one, one_mul]
      rw [Complex.digamma_one]
      simp [gammaPoleLogConstant]
      ring
  | succ m =>
      rw [polygamma_one_eq_riemannZeta]
      simp only [gammaPoleLogConstant, Nat.succ_ne_zero, ↓reduceIte]
      have hm2 : (((m + 2 : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero (m + 1)
      have hfacdiv :
          (((m + 2).factorial : ℂ) *
              (riemannZeta ((m + 2 : ℕ) : ℂ) / ((m + 2 : ℕ) : ℂ))) =
            ((m + 1).factorial : ℂ) * riemannZeta ((m + 2 : ℕ) : ℂ) := by
        rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ]
        push_cast
        have hm2' : (2 + (m : ℂ)) ≠ 0 := by
          simpa only [Nat.cast_add, Nat.cast_ofNat, add_comm] using hm2
        rw [div_eq_mul_inv]
        have hcancel : (2 + (m : ℂ)) * (2 + (m : ℂ))⁻¹ = 1 :=
          mul_inv_cancel₀ hm2'
        have harg : (m : ℂ) + 1 + 1 = 2 + (m : ℂ) := by ring
        rw [harg]
        calc
          (2 + (m : ℂ)) * ((m + 1).factorial : ℂ) *
                (riemannZeta (2 + (m : ℂ)) * (2 + (m : ℂ))⁻¹) =
              ((m + 1).factorial : ℂ) * riemannZeta (2 + (m : ℂ)) *
                ((2 + (m : ℂ)) * (2 + (m : ℂ))⁻¹) := by ring
          _ = _ := by rw [hcancel, mul_one]
      have hsign2 : (-1 : ℂ) ^ (m + 2) = (-1 : ℂ) ^ m := by
        rw [show m + 2 = m + 2 by rfl, pow_add]
        norm_num
      have hsign1 : (-1 : ℂ) ^ (m + 1) = -((-1 : ℂ) ^ m) := by
        rw [pow_succ]
        ring
      have hnegscale :
          (-reciprocalGammaFactorialScale n) ^ (m + 2) =
            (-1 : ℂ) ^ m * reciprocalGammaFactorialScale n ^ (m + 2) := by
        rw [neg_pow, hsign2]
      have hsignsq : (((-1 : ℂ) ^ m) ^ 2) = 1 := by
        rw [← pow_mul, show m * 2 = 2 * m by omega, pow_mul]
        norm_num
      have hsignmul : (-1 : ℂ) ^ (m * 2) = 1 := by
        rw [pow_mul, hsignsq]
      have hidxNat : m + 1 + 1 = m + 2 := by omega
      have hidxCast : ((m + 1 : ℕ) : ℂ) + 1 = ((m + 2 : ℕ) : ℂ) := by
        push_cast
        ring
      rw [hidxNat, hidxCast]
      rw [hfacdiv, hsign2, hsign1, hnegscale]
      ring_nf
      rw [hsignmul]
      ring

local instance gammaPoleAnalyticNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

theorem complexNatGerm_eq_constGerm (c : ℂ) :
    complexNatGerm c = (fun _n : ℕ => c : NatGerm) := by
  change ratNatEval (RatFunc.C c) = _
  rw [show RatFunc.C c =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) by simp,
    ratNatEval_algebraMap]
  change (↑(fun n : ℕ => (Polynomial.C c).eval (n : ℂ)) : NatGerm) =
    ↑(fun _n : ℕ => c)
  rw [Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun n => by simp

/-- The germ, across the pole index, of the actual analytic regular unit's logarithmic jets. -/
def actualGammaPoleLogDerivativeGerm (j : ℕ) : NatGerm :=
  fun N : ℕ =>
    iteratedDeriv j (gammaPoleRegularLogDeriv (N - 1)) 0

theorem actualGammaPoleLogDerivativeGerm_eq (j : ℕ) :
    actualGammaPoleLogDerivativeGerm j = gammaPoleLogDerivativeGerm j := by
  rw [gammaPoleLogDerivativeGerm]
  change (↑(fun N : ℕ =>
      iteratedDeriv j (gammaPoleRegularLogDeriv (N - 1)) 0) : NatGerm) =
    reciprocalSignedFactorialGerm ^ (j + 1) *
      (complexNatGerm (-1) * harmonicJetGerm j +
        complexNatGerm (((j + 1).factorial : ℂ) * gammaPoleLogConstant j))
  rw [complexNatGerm_eq_constGerm, complexNatGerm_eq_constGerm]
  unfold reciprocalSignedFactorialGerm harmonicJetGerm
  rw [← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul,
    ← Filter.Germ.coe_add, ← Filter.Germ.coe_mul]
  rw [Filter.Germ.coe_eq]
  exact Filter.eventually_atTop.2 ⟨1, fun N hN => by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
    simpa [add_comm] using
      (iteratedDeriv_gammaPoleRegularLogDeriv_zero_eq_sequence j n)⟩

theorem gammaPoleRegularUnit_analyticAt_zero (n : ℕ) :
    AnalyticAt ℂ (gammaPoleRegularUnit n) 0 := by
  have hoff : ∀ p : ℕ, (1 : ℂ) ≠ -(p : ℂ) := by
    intro p hp
    have hre := congrArg Complex.re hp
    norm_num only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have haff : AnalyticAt ℂ
      (fun x : ℂ => reciprocalGammaFactorialScale n * x + 1) 0 := by fun_prop
  have hnum : AnalyticAt ℂ
      (fun x : ℂ => Complex.Gamma (reciprocalGammaFactorialScale n * x + 1)) 0 := by
    have hout : AnalyticAt ℂ Complex.Gamma
        (reciprocalGammaFactorialScale n * 0 + 1) := by
      simpa using analyticAt_Gamma 1 hoff
    simpa [Function.comp_def] using
      (AnalyticAt.comp (g := Complex.Gamma)
        (f := fun x : ℂ => reciprocalGammaFactorialScale n * x + 1)
        hout haff)
  have hden : AnalyticAt ℂ (reciprocalGammaNormalizedProduct n) 0 := by
    unfold reciprocalGammaNormalizedProduct
    fun_prop
  exact hnum.div hden (by rw [reciprocalGammaNormalizedProduct_zero]; exact one_ne_zero)

/-- The pointwise Bell identity needs only analyticity and nonvanishing at the base point. -/
theorem iteratedDeriv_eq_bellCore_analyticAt
    {f : ℂ → ℂ} {z : ℂ} (hfan : AnalyticAt ℂ f z) (hfne : f z ≠ 0)
    (k : ℕ) :
    iteratedDeriv k f z =
      f z * MvPolynomial.eval
        (fun j : Fin k =>
          iteratedDeriv (j : ℕ) (fun w => deriv f w / f w) z)
        (bellCore k) := by
  have hmem : {w : ℂ | AnalyticAt ℂ f w ∧ f w ≠ 0} ∈ 𝓝 z :=
    hfan.eventually_analyticAt.and (hfan.continuousAt.eventually_ne hfne)
  rw [mem_nhds_iff] at hmem
  obtain ⟨Ω, hΩsub, hΩopen, hzΩ⟩ := hmem
  exact iteratedDeriv_eq_bellCore_generic hΩopen
    (fun w hw => (hΩsub hw).1) (fun w hw => (hΩsub hw).2) k hzΩ

theorem eventually_logDeriv_gammaPoleRegularUnit (n : ℕ) :
    (fun x : ℂ => logDeriv (gammaPoleRegularUnit n) x) =ᶠ[𝓝 0]
      gammaPoleRegularLogDeriv n := by
  have hoff : ∀ p : ℕ, (1 : ℂ) ≠ -(p : ℂ) := by
    intro p hp
    have hre := congrArg Complex.re hp
    norm_num only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have haff : ContinuousAt
      (fun x : ℂ => reciprocalGammaFactorialScale n * x + 1) 0 := by fun_prop
  have hpole : ∀ᶠ x : ℂ in 𝓝 0,
      ∀ p : ℕ, reciprocalGammaFactorialScale n * x + 1 ≠ -(p : ℂ) :=
    haff (offPoles_isOpen.mem_nhds (by simpa using hoff))
  have hprodcont : ContinuousAt (reciprocalGammaNormalizedProduct n) 0 := by
    unfold reciprocalGammaNormalizedProduct
    fun_prop
  have hprod : ∀ᶠ x : ℂ in 𝓝 0,
      reciprocalGammaNormalizedProduct n x ≠ 0 :=
    hprodcont.eventually_ne (by
      rw [reciprocalGammaNormalizedProduct_zero]
      exact one_ne_zero)
  filter_upwards [hpole, hprod] with x hx hp
  exact logDeriv_gammaPoleRegularUnit hx hp

theorem iteratedDeriv_gammaPoleRegularUnit_zero_eq_bell (k n : ℕ) :
    iteratedDeriv k (gammaPoleRegularUnit n) 0 =
      MvPolynomial.eval
        (fun j : Fin k =>
          iteratedDeriv (j : ℕ) (gammaPoleRegularLogDeriv n) 0)
        (bellCore k) := by
  have hbell := iteratedDeriv_eq_bellCore_analyticAt
    (gammaPoleRegularUnit_analyticAt_zero n)
    (by rw [gammaPoleRegularUnit_zero]; exact one_ne_zero) k
  have hlogfun :
      (fun w => deriv (gammaPoleRegularUnit n) w / gammaPoleRegularUnit n w) =
        fun w => logDeriv (gammaPoleRegularUnit n) w := by
    funext w
    rw [logDeriv_apply]
  rw [hlogfun, gammaPoleRegularUnit_zero, one_mul] at hbell
  have heq := eventually_logDeriv_gammaPoleRegularUnit n
  have hv :
      (fun j : Fin k =>
        iteratedDeriv (j : ℕ) (fun w => logDeriv (gammaPoleRegularUnit n) w) 0) =
      fun j : Fin k =>
        iteratedDeriv (j : ℕ) (gammaPoleRegularLogDeriv n) 0 := by
    funext j
    exact heq.iteratedDeriv_eq (j : ℕ)
  rwa [hv] at hbell

theorem iteratedDeriv_gammaPoleRegularUnit_zero_eq_sequenceBell (k n : ℕ) :
    iteratedDeriv k (gammaPoleRegularUnit n) 0 =
      MvPolynomial.eval
        (fun j : Fin k =>
          reciprocalSignedFactorialSequence (n + 1) ^ ((j : ℕ) + 1) *
            (-harmonicJetSequence (j : ℕ) (n + 1) +
              (((j : ℕ) + 1).factorial : ℂ) *
                gammaPoleLogConstant (j : ℕ)))
        (bellCore k) := by
  rw [iteratedDeriv_gammaPoleRegularUnit_zero_eq_bell]
  apply congrArg (fun v : Fin k → ℂ => MvPolynomial.eval v (bellCore k))
  funext j
  exact iteratedDeriv_gammaPoleRegularLogDeriv_zero_eq_sequence (j : ℕ) n

/-- The analytic unit is the exact regular numerator of the factorially rescaled Gamma pole. -/
theorem reciprocalGammaTangent_eq_one_div_Gamma_add_one (z : ℂ) :
    reciprocalGammaTangent z = (Complex.Gamma (z + 1))⁻¹ := by
  by_cases hz : z = 0
  · subst z
    simp [reciprocalGammaTangent_zero, Complex.Gamma_one]
  · apply mul_left_cancel₀ hz
    rw [← reciprocalGammaEntire_eq_mul_tangent]
    change (Complex.Gamma z)⁻¹ = z * (Complex.Gamma (z + 1))⁻¹
    exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z

theorem gammaPoleRegularUnit_source_identity
    (n : ℕ) {x : ℂ} (hx : x ≠ 0)
    (hpole : ∀ m : ℕ,
      reciprocalGammaFactorialScale n * x + 1 ≠ -(m : ℂ))
    (hprod : reciprocalGammaNormalizedProduct n x ≠ 0) :
    Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * x) =
      -gammaPoleRegularUnit n x / x := by
  have h := reciprocalGammaFactorialBlowUp_exact n x
  rw [reciprocalGammaTangent_eq_one_div_Gamma_add_one] at h
  change (Complex.Gamma
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x))⁻¹ =
    -x * reciprocalGammaNormalizedProduct n x *
      (Complex.Gamma (reciprocalGammaFactorialScale n * x + 1))⁻¹ at h
  have hnumne :
      Complex.Gamma (reciprocalGammaFactorialScale n * x + 1) ≠ 0 :=
    Complex.Gamma_ne_zero hpole
  have hrhsne :
      -x * reciprocalGammaNormalizedProduct n x *
          (Complex.Gamma (reciprocalGammaFactorialScale n * x + 1))⁻¹ ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hx) hprod) (inv_ne_zero hnumne)
  have hgamne : Complex.Gamma
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x) ≠ 0 := by
    have hleftne :
        (Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * x))⁻¹ ≠ 0 :=
      h.symm ▸ hrhsne
    intro hzero
    apply hleftne
    rw [hzero, inv_zero]
  change Complex.Gamma
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x) =
    -(Complex.Gamma (reciprocalGammaFactorialScale n * x + 1) /
      reciprocalGammaNormalizedProduct n x) / x
  field_simp [hgamne, hnumne, hprod, hx] at h ⊢
  rw [h]
  ring

theorem algebraicIndependent_actualGammaPoleLogDerivativeGerm :
    AlgebraicIndependent ℂ actualGammaPoleLogDerivativeGerm := by
  have hfamily : actualGammaPoleLogDerivativeGerm = gammaPoleLogDerivativeGerm := by
    funext j
    exact actualGammaPoleLogDerivativeGerm_eq j
  rw [hfamily]
  exact algebraicIndependent_gammaPoleLogDerivativeGerm

def constantSequenceRingHom : ℂ →+* (ℕ → ℂ) where
  toFun c := fun _n => c
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def mvPolynomialSequenceEval {ι : Type*} (x : ι → ℕ → ℂ) :
    MvPolynomial ι ℂ →+* (ℕ → ℂ) :=
  MvPolynomial.eval₂Hom constantSequenceRingHom x

def sequenceEvalAtRingHom (N : ℕ) : (ℕ → ℂ) →+* ℂ where
  toFun f := f N
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem mvPolynomialSequenceEval_apply {ι : Type*} (x : ι → ℕ → ℂ)
    (P : MvPolynomial ι ℂ) (N : ℕ) :
    mvPolynomialSequenceEval x P N =
      MvPolynomial.eval (fun i => x i N) P := by
  have hhom :
      (sequenceEvalAtRingHom N).comp (mvPolynomialSequenceEval x) =
        MvPolynomial.eval (fun i => x i N) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [mvPolynomialSequenceEval, constantSequenceRingHom, sequenceEvalAtRingHom]
    · intro i
      simp [mvPolynomialSequenceEval, sequenceEvalAtRingHom]
  exact RingHom.congr_fun hhom P

theorem aeval_sequenceGerm_eq {ι : Type*} (x : ι → ℕ → ℂ)
    (P : MvPolynomial ι ℂ) :
    MvPolynomial.aeval (fun i => (x i : NatGerm)) P =
      ((mvPolynomialSequenceEval x P : ℕ → ℂ) : NatGerm) := by
  have hhom :
      (MvPolynomial.aeval (fun i => (x i : NatGerm))).toRingHom =
        (Filter.Germ.coeRingHom Filter.atTop).comp (mvPolynomialSequenceEval x) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [mvPolynomialSequenceEval, constantSequenceRingHom]
      exact complexNatGerm_eq_constGerm c
    · intro i
      simp [mvPolynomialSequenceEval]
  exact RingHom.congr_fun hhom P

/-- The germ of the actual regular Laurent coefficient at order `j` across the Gamma poles. -/
def actualGammaPoleRegularCoefficientGerm (j : ℕ) : NatGerm :=
  fun N : ℕ =>
    -(((j + 1).factorial : ℂ)⁻¹) *
      iteratedDeriv (j + 1) (gammaPoleRegularUnit (N - 1)) 0

theorem actualGammaPoleRegularCoefficientGerm_eq_bell (j : ℕ) :
    actualGammaPoleRegularCoefficientGerm j =
      complexNatGerm (-(((j + 1).factorial : ℂ)⁻¹)) *
        MvPolynomial.aeval
          (fun i : Fin (j + 1) =>
            actualGammaPoleLogDerivativeGerm (i : ℕ))
          (bellCore (j + 1)) := by
  let x : Fin (j + 1) → ℕ → ℂ := fun i N =>
    iteratedDeriv (i : ℕ) (gammaPoleRegularLogDeriv (N - 1)) 0
  have hx (i : Fin (j + 1)) :
      actualGammaPoleLogDerivativeGerm (i : ℕ) = (x i : NatGerm) := rfl
  rw [complexNatGerm_eq_constGerm]
  simp_rw [hx]
  rw [aeval_sequenceGerm_eq x (bellCore (j + 1))]
  change (↑(fun N : ℕ =>
      -(((j + 1).factorial : ℂ)⁻¹) *
        iteratedDeriv (j + 1) (gammaPoleRegularUnit (N - 1)) 0) : NatGerm) =
    (↑(fun _N : ℕ => -(((j + 1).factorial : ℂ)⁻¹)) : NatGerm) *
      ↑(mvPolynomialSequenceEval x (bellCore (j + 1)))
  rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  exact Filter.eventually_atTop.2 ⟨1, fun N hN => by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
    change -(((j + 1).factorial : ℂ)⁻¹) *
        iteratedDeriv (j + 1) (gammaPoleRegularUnit ((1 + n) - 1)) 0 =
      -(((j + 1).factorial : ℂ)⁻¹) *
        mvPolynomialSequenceEval x (bellCore (j + 1)) (1 + n)
    rw [mvPolynomialSequenceEval_apply]
    simp only [x, Nat.add_sub_cancel_left]
    rw [iteratedDeriv_gammaPoleRegularUnit_zero_eq_bell]⟩

theorem actualGammaPoleRegularCoefficientGerm_eq (j : ℕ) :
    actualGammaPoleRegularCoefficientGerm j = gammaPoleRegularCoefficientGerm j := by
  rw [actualGammaPoleRegularCoefficientGerm_eq_bell]
  have hfamily :
      (fun i : Fin (j + 1) => actualGammaPoleLogDerivativeGerm (i : ℕ)) =
        fun i : Fin (j + 1) => gammaPoleLogDerivativeGerm (i : ℕ) := by
    funext i
    exact actualGammaPoleLogDerivativeGerm_eq (i : ℕ)
  rw [hfamily]
  rfl

theorem algebraicIndependent_actualGammaPoleRegularCoefficientGerm :
    AlgebraicIndependent ℂ actualGammaPoleRegularCoefficientGerm := by
  have hfamily :
      actualGammaPoleRegularCoefficientGerm = gammaPoleRegularCoefficientGerm := by
    funext j
    exact actualGammaPoleRegularCoefficientGerm_eq j
  rw [hfamily]
  exact algebraicIndependent_gammaPoleRegularCoefficientGerm

/-- The actual regular Laurent-series family of the factorially rescaled Gamma poles. -/
def actualGammaPoleRegularFormalGerm : PowerSeries NatGerm :=
  PowerSeries.mk actualGammaPoleRegularCoefficientGerm

/-- No nonzero finite-order algebraic differential equation over `ℂ[X]` annihilates the actual
regular Laurent-coefficient germ carried by the complete Gamma pole family. -/
theorem actualGammaPoleRegularFormalGerm_formallyHypertranscendental
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    MvPolynomial.aeval (formalJetsOver n actualGammaPoleRegularFormalGerm) P ≠ 0 := by
  exact aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent
    actualGammaPoleRegularCoefficientGerm
    algebraicIndependent_actualGammaPoleRegularCoefficientGerm hP

end

end GaloisForLFunctions
