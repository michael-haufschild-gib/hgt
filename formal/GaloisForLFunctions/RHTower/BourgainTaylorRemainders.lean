/-
# Exact Taylor phases in Bourgain's mean-value reduction

Equations (2.18)--(2.19) of Bourgain's proof replace the `3/2` and `1/2`
powers by quadratic Taylor polynomials plus normalized cubic and quartic
phases.  The paper writes only the asymptotic description
`φ₃(t) ∼ t³`, `φ₄(t) ∼ t⁴`.

This file defines normalized phases exactly, proves both Taylor identities,
computes their third and fourth derivatives, and proves the separated
determinant condition (2.11) directly.  For `0 < q ≤ 1/2`, where `q=M/N₀`,
that determinant is strictly positive on `[0,1]²`; no asymptotic premise is
used.
-/
import GaloisForLFunctions.RHTower.BourgainPolynomialCurveNondegenerate
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

namespace RHTower

noncomputable section

/-- Fractional power after dimensionless translation by scale ratio `q`. -/
def bourgainAffineRpow (q r t : ℝ) : ℝ := (1 + q * t) ^ r

/-- Quadratic Taylor polynomial for `(1+qt)^(3/2)`. -/
def bourgainThreeHalvesTaylorPolynomial (q t : ℝ) : ℝ :=
  1 + (3 / 2 : ℝ) * q * t + (3 / 8 : ℝ) * q ^ (2 : ℕ) * t ^ (2 : ℕ)

/-- Quadratic Taylor polynomial for `(1+qt)^(1/2)`. -/
def bourgainHalfTaylorPolynomial (q t : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * q * t - (1 / 8 : ℝ) * q ^ (2 : ℕ) * t ^ (2 : ℕ)

/-- Cubic phase normalized to converge in jets to `t³` as `q→0`. -/
def bourgainNormalizedCubicRemainder (q t : ℝ) : ℝ :=
  (-16 / q ^ (3 : ℕ)) *
    (bourgainAffineRpow q (3 / 2 : ℝ) t -
      bourgainThreeHalvesTaylorPolynomial q t)

/-- Quartic phase normalized to converge in jets to `t⁴` as `q→0`. -/
def bourgainNormalizedQuarticRemainder (q t : ℝ) : ℝ :=
  (4 / q) * bourgainNormalizedCubicRemainder q t -
    (64 / q ^ (4 : ℕ)) *
      (bourgainAffineRpow q (1 / 2 : ℝ) t -
        bourgainHalfTaylorPolynomial q t)

/-- Exact normalized form of Bourgain (2.18). -/
theorem bourgainAffineRpow_three_halves_taylor
    {q t : ℝ} (hq : q ≠ 0) :
    bourgainAffineRpow q (3 / 2 : ℝ) t =
      bourgainThreeHalvesTaylorPolynomial q t -
        q ^ (3 : ℕ) / 16 *
          bourgainNormalizedCubicRemainder q t := by
  unfold bourgainNormalizedCubicRemainder
  field_simp
  ring

/-- Exact normalized form of Bourgain (2.19). -/
theorem bourgainAffineRpow_half_taylor
    {q t : ℝ} (hq : q ≠ 0) :
    bourgainAffineRpow q (1 / 2 : ℝ) t =
      bourgainHalfTaylorPolynomial q t +
        q ^ (3 : ℕ) / 16 *
          bourgainNormalizedCubicRemainder q t -
        q ^ (4 : ℕ) / 64 *
          bourgainNormalizedQuarticRemainder q t := by
  unfold bourgainNormalizedQuarticRemainder
  field_simp
  ring

private theorem iteratedDeriv_quadratic_three
    (a b c t : ℝ) :
    iteratedDeriv 3 (fun x : ℝ => a + b * x + c * x ^ (2 : ℕ)) t = 0 := by
  change iteratedDeriv 3
    ((fun _x : ℝ => a) + (fun x : ℝ => b * x) +
      (fun x : ℝ => c * x ^ (2 : ℕ))) t = 0
  have ha : ContDiffAt ℝ 3 (fun _x : ℝ => a) t := contDiffAt_const
  have hb : ContDiffAt ℝ 3 (fun x : ℝ => b * x) t :=
    contDiffAt_const.mul contDiffAt_id
  have hc : ContDiffAt ℝ 3 (fun x : ℝ => c * x ^ (2 : ℕ)) t :=
    contDiffAt_const.mul (contDiffAt_id.pow 2)
  have houter := iteratedDeriv_add (n := 3) (f := (fun _x : ℝ => a) +
    fun x : ℝ => b * x) (g := fun x : ℝ => c * x ^ (2 : ℕ)) (ha.add hb) hc
  rw [houter]
  have hinner := iteratedDeriv_add (n := 3) (f := fun _x : ℝ => a)
    (g := fun x : ℝ => b * x) ha hb
  rw [hinner]
  simp [iteratedDeriv_eq_iterate]

private theorem iteratedDeriv_quadratic_four
    (a b c t : ℝ) :
    iteratedDeriv 4 (fun x : ℝ => a + b * x + c * x ^ (2 : ℕ)) t = 0 := by
  change iteratedDeriv 4
    ((fun _x : ℝ => a) + (fun x : ℝ => b * x) +
      (fun x : ℝ => c * x ^ (2 : ℕ))) t = 0
  have ha : ContDiffAt ℝ 4 (fun _x : ℝ => a) t := contDiffAt_const
  have hb : ContDiffAt ℝ 4 (fun x : ℝ => b * x) t :=
    contDiffAt_const.mul contDiffAt_id
  have hc : ContDiffAt ℝ 4 (fun x : ℝ => c * x ^ (2 : ℕ)) t :=
    contDiffAt_const.mul (contDiffAt_id.pow 2)
  have houter := iteratedDeriv_add (n := 4) (f := (fun _x : ℝ => a) +
    fun x : ℝ => b * x) (g := fun x : ℝ => c * x ^ (2 : ℕ)) (ha.add hb) hc
  rw [houter]
  have hinner := iteratedDeriv_add (n := 4) (f := fun _x : ℝ => a)
    (g := fun x : ℝ => b * x) ha hb
  rw [hinner]
  simp [iteratedDeriv_eq_iterate]

theorem iteratedDeriv_bourgainThreeHalvesTaylorPolynomial_three
    (q t : ℝ) :
    iteratedDeriv 3 (bourgainThreeHalvesTaylorPolynomial q) t = 0 := by
  change iteratedDeriv 3
    (fun x : ℝ =>
      1 + (3 / 2 : ℝ) * q * x +
        (3 / 8 : ℝ) * q ^ (2 : ℕ) * x ^ (2 : ℕ)) t = 0
  exact iteratedDeriv_quadratic_three
    1 ((3 / 2 : ℝ) * q) ((3 / 8 : ℝ) * q ^ (2 : ℕ)) t

theorem iteratedDeriv_bourgainThreeHalvesTaylorPolynomial_four
    (q t : ℝ) :
    iteratedDeriv 4 (bourgainThreeHalvesTaylorPolynomial q) t = 0 := by
  change iteratedDeriv 4
    (fun x : ℝ =>
      1 + (3 / 2 : ℝ) * q * x +
        (3 / 8 : ℝ) * q ^ (2 : ℕ) * x ^ (2 : ℕ)) t = 0
  exact iteratedDeriv_quadratic_four
    1 ((3 / 2 : ℝ) * q) ((3 / 8 : ℝ) * q ^ (2 : ℕ)) t

theorem iteratedDeriv_bourgainHalfTaylorPolynomial_three
    (q t : ℝ) :
    iteratedDeriv 3 (bourgainHalfTaylorPolynomial q) t = 0 := by
  change iteratedDeriv 3
    (fun x : ℝ =>
      1 + (1 / 2 : ℝ) * q * x -
        (1 / 8 : ℝ) * q ^ (2 : ℕ) * x ^ (2 : ℕ)) t = 0
  simpa [sub_eq_add_neg] using
    (iteratedDeriv_quadratic_three
      1 ((1 / 2 : ℝ) * q) (-(1 / 8 : ℝ) * q ^ (2 : ℕ)) t)

theorem iteratedDeriv_bourgainHalfTaylorPolynomial_four
    (q t : ℝ) :
    iteratedDeriv 4 (bourgainHalfTaylorPolynomial q) t = 0 := by
  change iteratedDeriv 4
    (fun x : ℝ =>
      1 + (1 / 2 : ℝ) * q * x -
        (1 / 8 : ℝ) * q ^ (2 : ℕ) * x ^ (2 : ℕ)) t = 0
  simpa [sub_eq_add_neg] using
    (iteratedDeriv_quadratic_four
      1 ((1 / 2 : ℝ) * q) (-(1 / 8 : ℝ) * q ^ (2 : ℕ)) t)

/-- Third derivative of a translated and scaled real power. -/
theorem iteratedDeriv_bourgainAffineRpow_three
    {q r t : ℝ} (hbase : 0 < 1 + q * t) :
    iteratedDeriv 3 (bourgainAffineRpow q r) t =
      q ^ (3 : ℕ) * (descPochhammer ℝ 3).eval r *
        (1 + q * t) ^ (r - 3) := by
  let g : ℝ → ℝ := fun u => u ^ r
  let f : ℝ → ℝ := fun x => 1 + q * x
  have hg : ContDiffAt ℝ 3 g (f t) :=
    Real.contDiffAt_rpow_const_of_ne hbase.ne'
  have hf : ContDiffAt ℝ 3 f t := by
    dsimp [f]
    fun_prop
  have hcomp := iteratedDeriv_comp_three hg hf
  change iteratedDeriv 3 (g ∘ f) t = _ at hcomp
  change iteratedDeriv 3 (g ∘ f) t = _
  rw [hcomp]
  dsimp [g, f]
  simp only [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  norm_num [Function.iterate_succ_apply']
  ring

theorem contDiffAt_bourgainAffineRpow
    {q r t : ℝ} {n : ℕ} (hbase : 0 < 1 + q * t) :
    ContDiffAt ℝ n (bourgainAffineRpow q r) t := by
  have hout : ContDiffAt ℝ n (fun u : ℝ => u ^ r) (1 + q * t) :=
    Real.contDiffAt_rpow_const_of_ne hbase.ne'
  have hinn : ContDiffAt ℝ n (fun x : ℝ => 1 + q * x) t := by fun_prop
  simpa [bourgainAffineRpow, Function.comp_def] using
    hout.comp t hinn

theorem contDiffAt_bourgainNormalizedCubicRemainder
    {q t : ℝ} {n : ℕ} (hbase : 0 < 1 + q * t) :
    ContDiffAt ℝ n (bourgainNormalizedCubicRemainder q) t := by
  unfold bourgainNormalizedCubicRemainder
  apply contDiffAt_const.mul
  apply (contDiffAt_bourgainAffineRpow hbase).sub
  unfold bourgainThreeHalvesTaylorPolynomial
  fun_prop

/-- Fourth derivative of a translated and scaled real power. -/
theorem iteratedDeriv_bourgainAffineRpow_four
    {q r t : ℝ} (hbase : 0 < 1 + q * t) :
    iteratedDeriv 4 (bourgainAffineRpow q r) t =
      q ^ (4 : ℕ) * (descPochhammer ℝ 4).eval r *
        (1 + q * t) ^ (r - 4) := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ]
  have hcont :
      ContinuousAt (fun y : ℝ => 1 + q * y) t := by fun_prop
  have hpos : ∀ᶠ y : ℝ in nhds t, 0 < 1 + q * y :=
    hcont.eventually (eventually_gt_nhds hbase)
  have heq :
      iteratedDeriv 3 (bourgainAffineRpow q r) =ᶠ[nhds t]
        (fun y =>
          q ^ (3 : ℕ) * (descPochhammer ℝ 3).eval r *
            (1 + q * y) ^ (r - 3)) := by
    filter_upwards [hpos] with y hy
    exact iteratedDeriv_bourgainAffineRpow_three hy
  rw [heq.deriv_eq]
  have haffine :
      HasDerivAt (fun y : ℝ => 1 + q * y) q t := by
    convert (hasDerivAt_const t (1 : ℝ)).add
      ((hasDerivAt_id t).const_mul q) using 1
    all_goals ring_nf
  have hpow :
      HasDerivAt (fun y : ℝ => (1 + q * y) ^ (r - 3))
        (q * (r - 3) * (1 + q * t) ^ (r - 4)) t := by
    convert haffine.rpow_const (p := r - 3) (Or.inl hbase.ne') using 1
    all_goals ring_nf
  rw [(hpow.const_mul
    (q ^ (3 : ℕ) * (descPochhammer ℝ 3).eval r)).deriv]
  norm_num [descPochhammer]
  ring

/-- Cubic normalized phase has exact third jet. -/
theorem iteratedDeriv_bourgainNormalizedCubicRemainder_three
    {q t : ℝ} (hq : q ≠ 0) (hbase : 0 < 1 + q * t) :
    iteratedDeriv 3 (bourgainNormalizedCubicRemainder q) t =
      6 * (1 + q * t) ^ (-(3 / 2 : ℝ)) := by
  unfold bourgainNormalizedCubicRemainder
  rw [iteratedDeriv_const_mul_field]
  change (-16 / q ^ (3 : ℕ)) *
    iteratedDeriv 3
      (bourgainAffineRpow q (3 / 2 : ℝ) -
        bourgainThreeHalvesTaylorPolynomial q) t =
      6 * (1 + q * t) ^ (-(3 / 2 : ℝ))
  rw [iteratedDeriv_sub
    (contDiffAt_bourgainAffineRpow hbase)
    (by
      unfold bourgainThreeHalvesTaylorPolynomial
      fun_prop)]
  rw [iteratedDeriv_bourgainAffineRpow_three hbase,
    iteratedDeriv_bourgainThreeHalvesTaylorPolynomial_three]
  norm_num [descPochhammer]
  field_simp
  ring

/-- Cubic normalized phase has exact fourth jet. -/
theorem iteratedDeriv_bourgainNormalizedCubicRemainder_four
    {q t : ℝ} (hq : q ≠ 0) (hbase : 0 < 1 + q * t) :
    iteratedDeriv 4 (bourgainNormalizedCubicRemainder q) t =
      -9 * q * (1 + q * t) ^ (-(5 / 2 : ℝ)) := by
  unfold bourgainNormalizedCubicRemainder
  rw [iteratedDeriv_const_mul_field]
  change (-16 / q ^ (3 : ℕ)) *
    iteratedDeriv 4
      (bourgainAffineRpow q (3 / 2 : ℝ) -
        bourgainThreeHalvesTaylorPolynomial q) t =
      -9 * q * (1 + q * t) ^ (-(5 / 2 : ℝ))
  rw [iteratedDeriv_sub
    (contDiffAt_bourgainAffineRpow hbase)
    (by
      unfold bourgainThreeHalvesTaylorPolynomial
      fun_prop)]
  rw [iteratedDeriv_bourgainAffineRpow_four hbase,
    iteratedDeriv_bourgainThreeHalvesTaylorPolynomial_four]
  norm_num [descPochhammer]
  field_simp

/-- Quartic normalized phase has exact third jet. -/
theorem iteratedDeriv_bourgainNormalizedQuarticRemainder_three
    {q t : ℝ} (hq : q ≠ 0) (hbase : 0 < 1 + q * t) :
    iteratedDeriv 3 (bourgainNormalizedQuarticRemainder q) t =
      24 * t * (1 + q * t) ^ (-(5 / 2 : ℝ)) := by
  unfold bourgainNormalizedQuarticRemainder
  change iteratedDeriv 3
    ((fun x : ℝ => (4 / q) * bourgainNormalizedCubicRemainder q x) -
      (fun x : ℝ =>
        (64 / q ^ (4 : ℕ)) *
          (bourgainAffineRpow q (1 / 2 : ℝ) x -
            bourgainHalfTaylorPolynomial q x))) t =
      24 * t * (1 + q * t) ^ (-(5 / 2 : ℝ))
  rw [iteratedDeriv_sub
    (contDiffAt_const.mul
      (contDiffAt_bourgainNormalizedCubicRemainder hbase))
    (contDiffAt_const.mul
      ((contDiffAt_bourgainAffineRpow hbase).sub
        (by
          unfold bourgainHalfTaylorPolynomial
          fun_prop)))]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  change (4 / q) *
      iteratedDeriv 3 (bourgainNormalizedCubicRemainder q) t -
    (64 / q ^ (4 : ℕ)) *
      iteratedDeriv 3
        (bourgainAffineRpow q (1 / 2 : ℝ) -
          bourgainHalfTaylorPolynomial q) t =
    24 * t * (1 + q * t) ^ (-(5 / 2 : ℝ))
  rw [iteratedDeriv_bourgainNormalizedCubicRemainder_three hq hbase]
  rw [iteratedDeriv_sub
    (contDiffAt_bourgainAffineRpow hbase)
    (by
      unfold bourgainHalfTaylorPolynomial
      fun_prop)]
  rw [iteratedDeriv_bourgainAffineRpow_three hbase,
    iteratedDeriv_bourgainHalfTaylorPolynomial_three]
  norm_num [descPochhammer]
  have hpow :
      (1 + q * t) ^ (-(3 / 2 : ℝ)) =
        (1 + q * t) ^ (-(5 / 2 : ℝ)) * (1 + q * t) := by
    rw [show (-(3 / 2 : ℝ)) = -(5 / 2 : ℝ) + 1 by norm_num,
      Real.rpow_add hbase, Real.rpow_one]
  rw [hpow]
  field_simp
  ring

/-- Quartic normalized phase has exact fourth jet. -/
theorem iteratedDeriv_bourgainNormalizedQuarticRemainder_four
    {q t : ℝ} (hq : q ≠ 0) (hbase : 0 < 1 + q * t) :
    iteratedDeriv 4 (bourgainNormalizedQuarticRemainder q) t =
      24 * (1 + q * t) ^ (-(7 / 2 : ℝ)) *
        (1 - (3 / 2 : ℝ) * q * t) := by
  unfold bourgainNormalizedQuarticRemainder
  change iteratedDeriv 4
    ((fun x : ℝ => (4 / q) * bourgainNormalizedCubicRemainder q x) -
      (fun x : ℝ =>
        (64 / q ^ (4 : ℕ)) *
          (bourgainAffineRpow q (1 / 2 : ℝ) x -
            bourgainHalfTaylorPolynomial q x))) t =
      24 * (1 + q * t) ^ (-(7 / 2 : ℝ)) *
        (1 - (3 / 2 : ℝ) * q * t)
  rw [iteratedDeriv_sub
    (contDiffAt_const.mul
      (contDiffAt_bourgainNormalizedCubicRemainder hbase))
    (contDiffAt_const.mul
      ((contDiffAt_bourgainAffineRpow hbase).sub
        (by
          unfold bourgainHalfTaylorPolynomial
          fun_prop)))]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  change (4 / q) *
      iteratedDeriv 4 (bourgainNormalizedCubicRemainder q) t -
    (64 / q ^ (4 : ℕ)) *
      iteratedDeriv 4
        (bourgainAffineRpow q (1 / 2 : ℝ) -
          bourgainHalfTaylorPolynomial q) t =
    24 * (1 + q * t) ^ (-(7 / 2 : ℝ)) *
      (1 - (3 / 2 : ℝ) * q * t)
  rw [iteratedDeriv_bourgainNormalizedCubicRemainder_four hq hbase]
  rw [iteratedDeriv_sub
    (contDiffAt_bourgainAffineRpow hbase)
    (by
      unfold bourgainHalfTaylorPolynomial
      fun_prop)]
  rw [iteratedDeriv_bourgainAffineRpow_four hbase,
    iteratedDeriv_bourgainHalfTaylorPolynomial_four]
  norm_num [descPochhammer]
  have hpow :
      (1 + q * t) ^ (-(5 / 2 : ℝ)) =
        (1 + q * t) ^ (-(7 / 2 : ℝ)) * (1 + q * t) := by
    rw [show (-(5 / 2 : ℝ)) = -(7 / 2 : ℝ) + 1 by norm_num,
      Real.rpow_add hbase, Real.rpow_one]
  rw [hpow]
  field_simp
  ring

/-- Exact separated-jet determinant of Bourgain's normalized phase pair. -/
theorem bourgainSeparatedJetDet_normalized_remainders
    {q s t : ℝ} (hq : q ≠ 0)
    (hsbase : 0 < 1 + q * s) (htbase : 0 < 1 + q * t) :
    bourgainSeparatedJetDet
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) s t =
      144 *
        (1 + q * s) ^ (-(5 / 2 : ℝ)) *
        (1 + q * t) ^ (-(7 / 2 : ℝ)) *
        (1 + (5 / 2 : ℝ) * q * s - (3 / 2 : ℝ) * q * t) := by
  rw [bourgainSeparatedJetDet,
    iteratedDeriv_bourgainNormalizedCubicRemainder_three hq hsbase,
    iteratedDeriv_bourgainNormalizedCubicRemainder_four hq htbase,
    iteratedDeriv_bourgainNormalizedQuarticRemainder_three hq hsbase,
    iteratedDeriv_bourgainNormalizedQuarticRemainder_four hq htbase]
  have hspow :
      (1 + q * s) ^ (-(3 / 2 : ℝ)) =
        (1 + q * s) ^ (-(5 / 2 : ℝ)) * (1 + q * s) := by
    rw [show (-(3 / 2 : ℝ)) = -(5 / 2 : ℝ) + 1 by norm_num,
      Real.rpow_add hsbase, Real.rpow_one]
  have htpow :
      (1 + q * t) ^ (-(5 / 2 : ℝ)) =
        (1 + q * t) ^ (-(7 / 2 : ℝ)) * (1 + q * t) := by
    rw [show (-(5 / 2 : ℝ)) = -(7 / 2 : ℝ) + 1 by norm_num,
      Real.rpow_add htbase, Real.rpow_one]
  rw [hspow, htpow]
  ring

/-- Bourgain's actual normalized Taylor phases satisfy the separated
nondegeneracy condition (2.11) throughout the parameter range used in the
local reduction. -/
theorem bourgainSeparatedJetDet_normalized_remainders_pos
    {q s t : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 <
      bourgainSeparatedJetDet
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) s t := by
  have hqs : 0 ≤ q * s := mul_nonneg hq0.le hs.1
  have hqt : 0 ≤ q * t := mul_nonneg hq0.le ht.1
  have hsbase : 0 < 1 + q * s := by linarith
  have htbase : 0 < 1 + q * t := by linarith
  rw [bourgainSeparatedJetDet_normalized_remainders hq0.ne' hsbase htbase]
  have hbracket :
      0 < 1 + (5 / 2 : ℝ) * q * s - (3 / 2 : ℝ) * q * t := by
    have hqtnonneg : 0 ≤ q * t := mul_nonneg hq0.le ht.1
    have hqtle : q * t ≤ 1 / 2 := by
      calc
        q * t ≤ q * 1 := mul_le_mul_of_nonneg_left ht.2 hq0.le
        _ ≤ 1 / 2 := by simpa using hq1
    have hqsnonnneg : 0 ≤ (5 / 2 : ℝ) * q * s := by
      exact mul_nonneg (mul_nonneg (by norm_num) hq0.le) hs.1
    nlinarith
  have hspow : 0 < (1 + q * s) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos hsbase _
  have htpow : 0 < (1 + q * t) ^ (-(7 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos htbase _
  positivity

private theorem one_eighth_le_rpow_neg_five_halves
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    (1 / 8 : ℝ) ≤ x ^ (-(5 / 2 : ℝ)) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
  have hxpow : x ^ (3 : ℕ) ≤ (2 : ℝ) ^ (3 : ℕ) :=
    pow_le_pow_left₀ hx0 hx2 3
  have hposx : 0 < x ^ (3 : ℕ) :=
    pow_pos (lt_of_lt_of_le (by norm_num) hx1) _
  have hpos2 : 0 < (2 : ℝ) ^ (3 : ℕ) := by positivity
  have hinv :
      ((2 : ℝ) ^ (3 : ℕ))⁻¹ ≤ (x ^ (3 : ℕ))⁻¹ :=
    (inv_le_inv₀ hpos2 hposx).2 hxpow
  have hneg :
      x ^ (-(3 : ℝ)) = (x ^ (3 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hx0]
    exact congrArg Inv.inv (Real.rpow_natCast x 3)
  have hexp :
      x ^ (-(3 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  norm_num at hinv
  rw [hneg] at hexp
  exact le_trans hinv hexp

private theorem one_sixteenth_le_rpow_neg_seven_halves
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    (1 / 16 : ℝ) ≤ x ^ (-(7 / 2 : ℝ)) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
  have hxpow : x ^ (4 : ℕ) ≤ (2 : ℝ) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hx0 hx2 4
  have hposx : 0 < x ^ (4 : ℕ) :=
    pow_pos (lt_of_lt_of_le (by norm_num) hx1) _
  have hpos2 : 0 < (2 : ℝ) ^ (4 : ℕ) := by positivity
  have hinv :
      ((2 : ℝ) ^ (4 : ℕ))⁻¹ ≤ (x ^ (4 : ℕ))⁻¹ :=
    (inv_le_inv₀ hpos2 hposx).2 hxpow
  have hneg :
      x ^ (-(4 : ℝ)) = (x ^ (4 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hx0]
    exact congrArg Inv.inv (Real.rpow_natCast x 4)
  have hexp :
      x ^ (-(4 : ℝ)) ≤ x ^ (-(7 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  norm_num at hinv
  rw [hneg] at hexp
  exact le_trans hinv hexp

/-- Explicit uniform form of Bourgain (2.11): the separated determinant is
bounded below by `9/32`, uniformly in `q,s,t` throughout the local
parameter box. -/
theorem bourgainSeparatedJetDet_normalized_remainders_ge
    {q s t : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (9 / 32 : ℝ) ≤
      bourgainSeparatedJetDet
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) s t := by
  have hqs : 0 ≤ q * s := mul_nonneg hq0.le hs.1
  have hqt : 0 ≤ q * t := mul_nonneg hq0.le ht.1
  have hsbase : 0 < 1 + q * s := by linarith
  have htbase : 0 < 1 + q * t := by linarith
  rw [bourgainSeparatedJetDet_normalized_remainders hq0.ne' hsbase htbase]
  have hsle : 1 + q * s ≤ 2 := by
    have hqsl : q * s ≤ 1 / 2 := by
      calc
        q * s ≤ q * 1 := mul_le_mul_of_nonneg_left hs.2 hq0.le
        _ ≤ 1 / 2 := by simpa using hq1
    linarith
  have htle : 1 + q * t ≤ 2 := by
    have hqtl : q * t ≤ 1 / 2 := by
      calc
        q * t ≤ q * 1 := mul_le_mul_of_nonneg_left ht.2 hq0.le
        _ ≤ 1 / 2 := by simpa using hq1
    linarith
  have hspow :
      (1 / 8 : ℝ) ≤ (1 + q * s) ^ (-(5 / 2 : ℝ)) :=
    one_eighth_le_rpow_neg_five_halves (by linarith) hsle
  have htpow :
      (1 / 16 : ℝ) ≤ (1 + q * t) ^ (-(7 / 2 : ℝ)) :=
    one_sixteenth_le_rpow_neg_seven_halves (by linarith) htle
  have hbracket :
      (1 / 4 : ℝ) ≤
        1 + (5 / 2 : ℝ) * q * s - (3 / 2 : ℝ) * q * t := by
    have hqtle : q * t ≤ 1 / 2 := by
      calc
        q * t ≤ q * 1 := mul_le_mul_of_nonneg_left ht.2 hq0.le
        _ ≤ 1 / 2 := by simpa using hq1
    have hqsnonnneg : 0 ≤ (5 / 2 : ℝ) * q * s :=
      mul_nonneg (mul_nonneg (by norm_num) hq0.le) hs.1
    nlinarith
  have hspow0 : 0 ≤ (1 + q * s) ^ (-(5 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos hsbase _).le
  have htpow0 : 0 ≤ (1 + q * t) ^ (-(7 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos htbase _).le
  nlinarith [mul_nonneg
    (sub_nonneg.mpr hspow)
    (sub_nonneg.mpr htpow),
    mul_nonneg
      (sub_nonneg.mpr
        (mul_le_mul hspow htpow (by norm_num) hspow0))
      (sub_nonneg.mpr hbracket)]

end

end RHTower
