/-
# Hurwitz shift ladder — the branch-coefficient deformation family

The Hurwitz zeta series `ζ(s,a) = ∑_{m≥0} (m+a)^{-s}` has one branch point per term, at
`a = -m`.  Deforming the coefficients of finitely many terms produces the family

`dzeta c k a = ζ(s+k, a) + ∑_{n≤M} (c_n - 1)·(n+a)^{-(s+k)}`,

which at `c = (1,…,1)` is the genuine ladder rung `ζ(s+k,·)` and in general carries an
independent scalar on each of the first `M+1` singular terms.  Monodromy around `a = -n`
multiplies exactly the coordinate `c_n` by `q = e^{-2πi s}` and fixes the rest; the affine
`c`-orbit of the ladder is the geometric object behind the algebraic-independence proof.

This file provides the analytic substrate: the genuine `hzeta` and the whole deformed family
are differentiable (hence analytic) on the upper half-plane — every base `m + a` has positive
imaginary part there, so each term is a slit-plane power, and the tail obeys a Weierstrass
M-test on any ball whose closure avoids the real axis.
-/
import GaloisForLFunctions.Hurwitz.HurwitzZeta
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Complex Filter HurwitzZetaShift Polynomial Topology

namespace HurwitzLadder

/-- The upper half-plane, the common domain of the deformed ladder. -/
def UHP : Set ℂ := {a : ℂ | 0 < a.im}

theorem isOpen_UHP : IsOpen UHP := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_UHP : IsPreconnected UHP := (convex_halfSpace_im_gt 0).isPreconnected

/-- On the upper half-plane every series base `m + a` lies in the slit plane
(its imaginary part is `Im a ≠ 0`). -/
theorem natCast_add_mem_slitPlane {a : ℂ} (ha : 0 < a.im) (m : ℕ) :
    ((m : ℂ) + a) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  right
  have him : ((m : ℂ) + a).im = a.im := by simp
  rw [him]
  exact ne_of_gt ha

/-- A single power term `a ↦ (m+a)^w` is differentiable at any point of the upper
half-plane. -/
theorem term_differentiableAt {a : ℂ} (ha : 0 < a.im) (m : ℕ) (w : ℂ) :
    DifferentiableAt ℂ (fun y : ℂ => ((m : ℂ) + y) ^ w) a := by
  have hb : ((m : ℂ) + a) ∈ Complex.slitPlane := natCast_add_mem_slitPlane ha m
  have haff : DifferentiableAt ℂ (fun y : ℂ => (m : ℂ) + y) a := by fun_prop
  exact ((hasStrictDerivAt_cpow_const hb).hasDerivAt.differentiableAt).comp a haff

/-- **`hzeta` is differentiable on the upper half-plane.**  At `a₀` split the series after
`M₀ > 2(‖a₀‖ + ρ)` terms (`ρ = Im a₀ / 2`): the head is a finite sum of slit-plane powers, and
on the ball `B(a₀,ρ)` the tail terms obey `‖(m+M₀+a)^{-s}‖ ≤ C·((m+M₀)/2)^{-Re s}`, a summable
bound, so the tail is a locally uniform limit of differentiable functions. -/
theorem hzeta_differentiableOn {s' : ℂ} (hs : 1 < s'.re) :
    DifferentiableOn ℂ (hzeta s') UHP := by
  intro a₀ ha₀
  have ha₀im : 0 < a₀.im := ha₀
  set ρ : ℝ := a₀.im / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  set R : ℝ := ‖a₀‖ + ρ with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (2 * R)
  have hM₀pos : (0 : ℝ) < M₀ := lt_trans (by positivity) hM₀
  -- ball membership facts
  have hball_im : ∀ a ∈ Metric.ball a₀ ρ, ρ < a.im := by
    intro a ha
    have h1 : ‖a - a₀‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at ha
    have h2 : |(a - a₀).im| ≤ ‖a - a₀‖ := Complex.abs_im_le_norm _
    have h3 : (a - a₀).im = a.im - a₀.im := by simp
    rw [h3] at h2
    have h4 := abs_lt.mp (lt_of_le_of_lt h2 h1)
    rw [hρ]
    linarith [h4.1]
  have hball_pos : ∀ a ∈ Metric.ball a₀ ρ, 0 < a.im :=
    fun a ha => lt_trans hρpos (hball_im a ha)
  have hball_norm : ∀ a ∈ Metric.ball a₀ ρ, ‖a‖ < R := by
    intro a ha
    have h1 : ‖a - a₀‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at ha
    have h2 : ‖a‖ = ‖a₀ + (a - a₀)‖ := by congr 1; ring
    calc ‖a‖ = ‖a₀ + (a - a₀)‖ := h2
      _ ≤ ‖a₀‖ + ‖a - a₀‖ := norm_add_le _ _
      _ < R := by rw [hR]; linarith
  -- the split of the series
  have hsplit : ∀ a : ℂ, hzeta s' a
      = (∑ m ∈ Finset.range M₀, ((m : ℂ) + a) ^ (-s'))
        + ∑' m : ℕ, ((↑(m + M₀) : ℂ) + a) ^ (-s') := by
    intro a
    rw [hzeta]
    exact ((summable_hurwitzSeries hs a).sum_add_tsum_nat_add M₀).symm
  have hopen : IsOpen (Metric.ball a₀ ρ) := Metric.isOpen_ball
  -- head: finite sum of slit-plane powers
  have hfin : DifferentiableOn ℂ
      (fun a => ∑ m ∈ Finset.range M₀, ((m : ℂ) + a) ^ (-s')) (Metric.ball a₀ ρ) := by
    apply DifferentiableOn.fun_sum
    intro m _ a ha
    exact (term_differentiableAt (hball_pos a ha) m (-s')).differentiableWithinAt
  -- tail: M-test
  set C : ℝ := Real.exp (Real.pi * |s'.im|) with hC
  have hCpos : 0 < C := Real.exp_pos _
  set u : ℕ → ℝ := fun m => C * ((((m : ℝ) + M₀)) / 2) ^ (-s'.re) with hu
  have hsre : -s'.re ≤ 0 := by linarith
  have hsum_u : Summable u := by
    have hpser : Summable (fun n : ℕ => (n : ℝ) ^ (-s'.re)) := by
      have h := (Real.summable_nat_rpow_inv (p := s'.re)).mpr hs
      exact h.congr (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])
    have hshift : Summable (fun m : ℕ => ((m : ℝ) + M₀) ^ (-s'.re)) := by
      have h := (summable_nat_add_iff M₀).mpr hpser
      exact h.congr (fun m => by push_cast; ring_nf)
    have heq : u = fun m : ℕ => (C * (2 : ℝ) ^ s'.re) * ((m : ℝ) + M₀) ^ (-s'.re) := by
      funext m
      show C * ((((m : ℝ) + M₀)) / 2) ^ (-s'.re) = _
      have hb : (0 : ℝ) ≤ ((m : ℝ) + M₀) := by positivity
      rw [Real.div_rpow hb (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv]
      ring
    rw [heq]
    exact hshift.mul_left _
  have hdiff : ∀ m : ℕ, DifferentiableOn ℂ
      (fun a => ((↑(m + M₀) : ℂ) + a) ^ (-s')) (Metric.ball a₀ ρ) := by
    intro m a ha
    exact (term_differentiableAt (hball_pos a ha) (m + M₀) (-s')).differentiableWithinAt
  have hbound : ∀ m : ℕ, ∀ a ∈ Metric.ball a₀ ρ, ‖((↑(m + M₀) : ℂ) + a) ^ (-s')‖ ≤ u m := by
    intro m a ha
    have hbasepos : (0 : ℝ) < ((m : ℝ) + M₀) / 2 := by positivity
    set z : ℂ := (↑(m + M₀) : ℂ) + a with hzdef
    have hmM : ((m : ℝ) + M₀) / 2 ≤ ‖z‖ := by
      have hge : ‖(↑(m + M₀) : ℂ)‖ - ‖a‖ ≤ ‖z‖ := by
        have h := norm_add_le z (-a)
        simp only [hzdef, add_neg_cancel_right, norm_neg] at h
        linarith
      rw [Complex.norm_natCast] at hge
      push_cast at hge
      have hna : ‖a‖ < R := hball_norm a ha
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    calc ‖z ^ (-s')‖
        ≤ ‖z‖ ^ (-s').re / Real.exp (z.arg * (-s').im) := Complex.norm_cpow_le z (-s')
      _ = ‖z‖ ^ (-s'.re) * Real.exp (z.arg * s'.im) := by
          rw [Complex.neg_re, Complex.neg_im, div_eq_mul_inv]
          congr 1
          rw [show z.arg * -s'.im = -(z.arg * s'.im) from by ring, Real.exp_neg, inv_inv]
      _ ≤ (((m : ℝ) + M₀) / 2) ^ (-s'.re) * Real.exp (Real.pi * |s'.im|) := by
          refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hbasepos hmM hsre)
            (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (Real.rpow_nonneg hbasepos.le _)
          calc z.arg * s'.im ≤ |z.arg * s'.im| := le_abs_self _
            _ = |z.arg| * |s'.im| := abs_mul _ _
            _ ≤ Real.pi * |s'.im| := by
                exact mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi z) (abs_nonneg _)
      _ = u m := by rw [hu, hC]; ring
  have htail : DifferentiableOn ℂ
      (fun a => ∑' m : ℕ, ((↑(m + M₀) : ℂ) + a) ^ (-s')) (Metric.ball a₀ ρ) :=
    Complex.differentiableOn_tsum_of_summable_norm hsum_u hdiff hopen hbound
  have hd : DifferentiableOn ℂ (hzeta s') (Metric.ball a₀ ρ) := by
    refine DifferentiableOn.congr (hfin.add htail) ?_
    intro a _
    exact hsplit a
  exact (hd.differentiableAt (hopen.mem_nhds (Metric.mem_ball_self hρpos))).differentiableWithinAt

/-- **Hurwitz shift-derivative ladder.**  On the upper half-plane and for `Re s > 1`,
the derivative in the shift variable is the next exponent value:

`d/da ζ(s,a) = -s ζ(s+1,a)`. -/
theorem hzeta_hasDerivAt {s : ℂ} (hs : 1 < s.re) {a₀ : ℂ} (ha₀ : a₀ ∈ UHP) :
    HasDerivAt (hzeta s) (-s * hzeta (s + 1) a₀) a₀ := by
  have ha₀im : 0 < a₀.im := ha₀
  set ρ : ℝ := a₀.im / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  set R : ℝ := ‖a₀‖ + ρ with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (2 * R)
  have hM₀pos : (0 : ℝ) < M₀ := lt_trans (by positivity) hM₀
  have hball_im : ∀ a ∈ Metric.ball a₀ ρ, ρ < a.im := by
    intro a ha
    have h1 : ‖a - a₀‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at ha
    have h2 : |(a - a₀).im| ≤ ‖a - a₀‖ := Complex.abs_im_le_norm _
    have h3 : (a - a₀).im = a.im - a₀.im := by simp
    rw [h3] at h2
    have h4 := abs_lt.mp (lt_of_le_of_lt h2 h1)
    rw [hρ]
    linarith [h4.1]
  have hball_pos : ∀ a ∈ Metric.ball a₀ ρ, 0 < a.im :=
    fun a ha => lt_trans hρpos (hball_im a ha)
  have hball_norm : ∀ a ∈ Metric.ball a₀ ρ, ‖a‖ < R := by
    intro a ha
    have h1 : ‖a - a₀‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at ha
    have h2 : ‖a‖ = ‖a₀ + (a - a₀)‖ := by
      congr 1
      ring
    calc
      ‖a‖ = ‖a₀ + (a - a₀)‖ := h2
      _ ≤ ‖a₀‖ + ‖a - a₀‖ := norm_add_le _ _
      _ < R := by rw [hR]; linarith
  have hsplit : hzeta s = fun a : ℂ =>
      (∑ m ∈ Finset.range M₀, ((m : ℂ) + a) ^ (-s))
        + ∑' m : ℕ, ((↑(m + M₀) : ℂ) + a) ^ (-s) := by
    funext a
    rw [hzeta]
    exact ((summable_hurwitzSeries hs a).sum_add_tsum_nat_add M₀).symm
  have hhead : HasDerivAt
      (fun a : ℂ => ∑ m ∈ Finset.range M₀, ((m : ℂ) + a) ^ (-s))
      (∑ m ∈ Finset.range M₀, -s * ((m : ℂ) + a₀) ^ (-(s + 1))) a₀ := by
    apply HasDerivAt.fun_sum
    intro m _
    have hb : ((m : ℂ) + a₀) ∈ Complex.slitPlane := natCast_add_mem_slitPlane ha₀im m
    have h := (Complex.hasStrictDerivAt_cpow_const (c := -s) hb).hasDerivAt.comp a₀
      ((hasDerivAt_const a₀ (m : ℂ)).add (hasDerivAt_id a₀))
    simpa only [Function.comp_apply, Pi.add_apply, id_eq] using!
      h.congr_deriv (by ring_nf)
  set C : ℝ := ‖s‖ * Real.exp (Real.pi * |s.im|) with hC
  set u : ℕ → ℝ := fun m => C * ((((m : ℝ) + M₀)) / 2) ^ (-(s.re + 1)) with hu
  have hsum_u : Summable u := by
    have hpser : Summable (fun n : ℕ => (n : ℝ) ^ (-(s.re + 1))) := by
      have hp : 1 < s.re + 1 := by linarith
      have h := (Real.summable_nat_rpow_inv (p := s.re + 1)).mpr hp
      exact h.congr (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])
    have hshift : Summable (fun m : ℕ => ((m : ℝ) + M₀) ^ (-(s.re + 1))) := by
      have h := (summable_nat_add_iff M₀).mpr hpser
      exact h.congr (fun m => by push_cast; ring_nf)
    have heq : u = fun m : ℕ =>
        (C * (2 : ℝ) ^ (s.re + 1)) * ((m : ℝ) + M₀) ^ (-(s.re + 1)) := by
      funext m
      show C * ((((m : ℝ) + M₀)) / 2) ^ (-(s.re + 1)) = _
      have hb : (0 : ℝ) ≤ ((m : ℝ) + M₀) := by positivity
      rw [Real.div_rpow hb (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv]
      ring
    rw [heq]
    exact hshift.mul_left _
  have hterm : ∀ m : ℕ, ∀ a ∈ Metric.ball a₀ ρ,
      HasDerivAt (fun y : ℂ => ((↑(m + M₀) : ℂ) + y) ^ (-s))
        (-s * ((↑(m + M₀) : ℂ) + a) ^ (-(s + 1))) a := by
    intro m a ha
    have hb : ((↑(m + M₀) : ℂ) + a) ∈ Complex.slitPlane :=
      natCast_add_mem_slitPlane (hball_pos a ha) (m + M₀)
    have h := (Complex.hasStrictDerivAt_cpow_const (c := -s) hb).hasDerivAt.comp a
      ((hasDerivAt_const a (↑(m + M₀) : ℂ)).add (hasDerivAt_id a))
    simpa only [Function.comp_apply, Pi.add_apply, id_eq] using!
      h.congr_deriv (by ring_nf)
  have hbound : ∀ m : ℕ, ∀ a ∈ Metric.ball a₀ ρ,
      ‖-s * ((↑(m + M₀) : ℂ) + a) ^ (-(s + 1))‖ ≤ u m := by
    intro m a ha
    have hbasepos : (0 : ℝ) < ((m : ℝ) + M₀) / 2 := by positivity
    set z : ℂ := (↑(m + M₀) : ℂ) + a with hzdef
    have hmM : ((m : ℝ) + M₀) / 2 ≤ ‖z‖ := by
      have hge : ‖(↑(m + M₀) : ℂ)‖ - ‖a‖ ≤ ‖z‖ := by
        have h := norm_add_le z (-a)
        simp only [hzdef, add_neg_cancel_right, norm_neg] at h
        linarith
      rw [Complex.norm_natCast] at hge
      push_cast at hge
      have hna : ‖a‖ < R := hball_norm a ha
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    have hsre : -(s.re + 1) ≤ 0 := by linarith
    have hcpow : ‖z ^ (-(s + 1))‖ ≤
        (((m : ℝ) + M₀) / 2) ^ (-(s.re + 1)) * Real.exp (Real.pi * |s.im|) := by
      calc
        ‖z ^ (-(s + 1))‖
            ≤ ‖z‖ ^ (-(s + 1)).re / Real.exp (z.arg * (-(s + 1)).im) :=
              Complex.norm_cpow_le z (-(s + 1))
        _ = ‖z‖ ^ (-(s.re + 1)) * Real.exp (z.arg * s.im) := by
          rw [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.neg_im,
            Complex.add_im, Complex.one_im, add_zero, div_eq_mul_inv]
          congr 1
          rw [show z.arg * -s.im = -(z.arg * s.im) from by ring,
            Real.exp_neg, inv_inv]
        _ ≤ (((m : ℝ) + M₀) / 2) ^ (-(s.re + 1)) *
            Real.exp (Real.pi * |s.im|) := by
          refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hbasepos hmM hsre)
            (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _)
            (Real.rpow_nonneg hbasepos.le _)
          calc
            z.arg * s.im ≤ |z.arg * s.im| := le_abs_self _
            _ = |z.arg| * |s.im| := abs_mul _ _
            _ ≤ Real.pi * |s.im| :=
              mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi z) (abs_nonneg _)
    calc
      ‖-s * z ^ (-(s + 1))‖ = ‖s‖ * ‖z ^ (-(s + 1))‖ := by simp
      _ ≤ ‖s‖ * ((((m : ℝ) + M₀) / 2) ^ (-(s.re + 1)) *
          Real.exp (Real.pi * |s.im|)) :=
        mul_le_mul_of_nonneg_left hcpow (norm_nonneg s)
      _ = u m := by rw [hu, hC]; ring
  have hsum0 : Summable (fun m : ℕ => ((↑(m + M₀) : ℂ) + a₀) ^ (-s)) := by
    exact (summable_nat_add_iff M₀).mpr (summable_hurwitzSeries hs a₀)
  have htail : HasDerivAt
      (fun a : ℂ => ∑' m : ℕ, ((↑(m + M₀) : ℂ) + a) ^ (-s))
      (∑' m : ℕ, -s * ((↑(m + M₀) : ℂ) + a₀) ^ (-(s + 1))) a₀ := by
    exact hasDerivAt_tsum_of_isPreconnected hsum_u Metric.isOpen_ball
      (convex_ball a₀ ρ).isPreconnected hterm hbound (Metric.mem_ball_self hρpos) hsum0
      (Metric.mem_ball_self hρpos)
  rw [hsplit]
  have hsum := hhead.add htail
  have hcoef :
      (∑ m ∈ Finset.range M₀, -s * ((m : ℂ) + a₀) ^ (-(s + 1))) +
          ∑' m : ℕ, -s * ((↑(m + M₀) : ℂ) + a₀) ^ (-(s + 1)) =
        -s * hzeta (s + 1) a₀ := by
    have hs1 : 1 < (s + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
    have hseries := (summable_hurwitzSeries hs1 a₀).sum_add_tsum_nat_add M₀
    rw [hzeta]
    rw [tsum_mul_left, ← Finset.mul_sum]
    rw [← hseries]
    ring
  simpa only [Pi.add_apply] using! hsum.congr_deriv hcoef

/-- Derivative form of `hzeta_hasDerivAt`. -/
theorem hzeta_deriv {s : ℂ} (hs : 1 < s.re) {a : ℂ} (ha : a ∈ UHP) :
    deriv (hzeta s) a = -s * hzeta (s + 1) a :=
  (hzeta_hasDerivAt hs ha).deriv

/-- **All-order Hurwitz differential ladder.**  Repeated shift differentiation raises the
exponent and multiplies by the signed ascending factorial:

`d^r/da^r ζ(s,a) = (-1)^r (s)_r ζ(s+r,a)`. -/
theorem hzeta_iteratedDeriv (r : ℕ) {s : ℂ} (hs : 1 < s.re) {a : ℂ} (ha : a ∈ UHP) :
    iteratedDeriv r (hzeta s) a =
      (-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s * hzeta (s + r) a := by
  induction r generalizing a with
  | zero => simp
  | succ r ih =>
      rw [show r + 1 = Nat.succ r by rfl, iteratedDeriv_succ]
      have hevent : iteratedDeriv r (hzeta s) =ᶠ[𝓝 a]
          (fun z => (-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s * hzeta (s + r) z) := by
        filter_upwards [isOpen_UHP.mem_nhds ha] with z hz
        exact ih hz
      rw [hevent.deriv_eq]
      have hs' : 1 < (s + (r : ℂ)).re := by
        rw [Complex.add_re, Complex.natCast_re]
        have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        linarith
      have hd := (hzeta_hasDerivAt (s := s + (r : ℂ)) hs' ha).const_mul
        ((-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s)
      rw [hd.deriv]
      rw [ascPochhammer_succ_eval]
      push_cast
      rw [pow_succ]
      ring_nf

/-- The ascending-factorial coefficient in the Hurwitz differential ladder is nonzero throughout
the convergence half-plane. -/
theorem ascPochhammer_eval_ne_zero_of_one_lt_re (r : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (ascPochhammer ℂ r).eval s ≠ 0 := by
  rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
  push Not
  intro j _ heq
  have hre := congrArg Complex.re heq
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

/-- Every shifted Hurwitz rung is a normalized derivative of the base rung. -/
theorem hzeta_shift_eq_iteratedDeriv_div (r : ℕ) {s : ℂ} (hs : 1 < s.re)
    {a : ℂ} (ha : a ∈ UHP) :
    hzeta (s + r) a =
      iteratedDeriv r (hzeta s) a /
        ((-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s) := by
  have h := hzeta_iteratedDeriv r hs ha
  have hC : ((-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ascPochhammer_eval_ne_zero_of_one_lt_re r hs)
  rw [h]
  field_simp [ascPochhammer_eval_ne_zero_of_one_lt_re r hs]

/-- The shifted exponent keeps `Re > 1`. -/
theorem shifted_re {s : ℂ} (hs : 1 < s.re) (k : ℕ) : 1 < (s + (k : ℂ)).re := by
  rw [Complex.add_re, Complex.natCast_re]
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

/-- **The deformed Hurwitz ladder**: the genuine rung `ζ(s+k,·)` plus a scalar deformation
`(c_n - 1)` on each of the first `M+1` singular terms `(n+a)^{-(s+k)}`. -/
noncomputable def dzeta (s : ℂ) (M : ℕ) (c : Fin (M + 1) → ℂ) (k : ℕ) (a : ℂ) : ℂ :=
  hzeta (s + (k : ℂ)) a
    + ∑ n : Fin (M + 1), (c n - 1) * ((((n : ℕ) : ℂ) + a) ^ (-(s + (k : ℂ))))

/-- At the undeformed point `c = (1,…,1)` the family is the genuine ladder. -/
theorem dzeta_one (s : ℂ) (M k : ℕ) (a : ℂ) :
    dzeta s M (fun _ => 1) k a = hzeta (s + (k : ℂ)) a := by
  simp [dzeta]

/-- The deformed ladder is differentiable on the upper half-plane. -/
theorem dzeta_differentiableOn {s : ℂ} (hs : 1 < s.re) (M : ℕ) (c : Fin (M + 1) → ℂ) (k : ℕ) :
    DifferentiableOn ℂ (dzeta s M c k) UHP := by
  apply DifferentiableOn.add
  · exact hzeta_differentiableOn (shifted_re hs k)
  · apply DifferentiableOn.fun_sum
    intro n _
    apply DifferentiableOn.const_mul
    intro a ha
    exact (term_differentiableAt ha (n : ℕ) (-(s + (k : ℂ)))).differentiableWithinAt

end HurwitzLadder
