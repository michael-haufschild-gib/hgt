import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelCriticalWall
import GaloisForLFunctions.RHTower.RadialGramOffDiagonalDecay
import GaloisForLFunctions.RHTower.Sieve.LogLogTelescope
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLineContinuity
import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonMellin

/-!
# Natural integer log-mesh continuation

The natural Wold residual uses the exact mesh increments
`log (N+2) - log (N+1)`. This module splits their Dirichlet series into
`ζ(s+1)-1` plus an absolutely convergent remainder. The remainder extends
holomorphically to `re s > -1`; hence the whole mesh current does too, away
from the unique translated zeta pole `s = 0`.

This continuation is the arithmetic half of the T2 square-energy no-go: it
allows the natural Wold Abel identity, initially valid for `re s > 0`, to be
continued to the upper critical wall without assuming RH.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def integerLogMeshIncrement (N : ℕ) : ℝ :=
  Real.log ((N : ℝ) + 2) - Real.log ((N : ℝ) + 1)

def integerLogMeshRemainderCoeff (N : ℕ) : ℝ :=
  integerLogMeshIncrement N - 1 / ((N : ℝ) + 2)

theorem integerLogMeshRemainderCoeff_nonneg (N : ℕ) :
    0 ≤ integerLogMeshRemainderCoeff N := by
  have h := one_div_succ_le_log_sub N
  rw [integerLogMeshRemainderCoeff, integerLogMeshIncrement]
  convert sub_nonneg.mpr h using 1 <;> ring

theorem integerLogMeshRemainderCoeff_le (N : ℕ) :
    integerLogMeshRemainderCoeff N ≤ 2 / ((N : ℝ) + 2) ^ 2 := by
  have hpos : 0 < (N : ℝ) + 1 := by positivity
  have hab : (N : ℝ) + 1 ≤ (N : ℝ) + 2 := by linarith
  have hlog := Sieve.log_sub_log_le hpos hab
  have hupper : integerLogMeshIncrement N ≤ 1 / ((N : ℝ) + 1) := by
    rw [integerLogMeshIncrement]
    convert hlog using 1
    field_simp
    ring
  have hN : (0 : ℝ) ≤ N := by positivity
  rw [integerLogMeshRemainderCoeff]
  have hdiff : 1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2) =
      1 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
    field_simp
    ring
  have hden : ((N : ℝ) + 2) ^ 2 ≤
      2 * (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by nlinarith
  have hdenpos : 0 < (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by positivity
  have hsqpos : 0 < ((N : ℝ) + 2) ^ 2 := by positivity
  calc
    integerLogMeshIncrement N - 1 / ((N : ℝ) + 2) ≤
        1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2) := by linarith
    _ = 1 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) := hdiff
    _ ≤ 2 / ((N : ℝ) + 2) ^ 2 := by
      rw [div_le_div_iff₀ hdenpos hsqpos]
      nlinarith

theorem abs_integerLogMeshRemainderCoeff_le (N : ℕ) :
    |integerLogMeshRemainderCoeff N| ≤ 2 / ((N : ℝ) + 2) ^ 2 := by
  rw [abs_of_nonneg (integerLogMeshRemainderCoeff_nonneg N)]
  exact integerLogMeshRemainderCoeff_le N

def integerLogMeshRemainderAtom (s : ℂ) (N : ℕ) : ℂ :=
  (integerLogMeshRemainderCoeff N : ℂ) *
    ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s))

def integerLogMeshRemainderCurrent (s : ℂ) : ℂ :=
  ∑' N : ℕ, integerLogMeshRemainderAtom s N

def integerLogMeshPrincipalAtom (s : ℂ) (N : ℕ) : ℂ :=
  ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-(s + 1)))

def integerLogMeshPrincipalCurrent (s : ℂ) : ℂ :=
  ∑' N : ℕ, integerLogMeshPrincipalAtom s N

def integerLogMeshAtom (s : ℂ) (N : ℕ) : ℂ :=
  (integerLogMeshIncrement N : ℂ) * ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s))

def integerLogMeshCurrent (s : ℂ) : ℂ :=
  ∑' N : ℕ, integerLogMeshAtom s N

theorem integerLogMeshPrincipalAtom_eq (s : ℂ) (N : ℕ) :
    integerLogMeshPrincipalAtom s N =
      ((1 / ((N : ℝ) + 2) : ℝ) : ℂ) *
        ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) := by
  have hbaseR : (N : ℝ) + 2 ≠ 0 := by positivity
  have hbaseC : ((((N : ℝ) + 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hbaseR
  rw [integerLogMeshPrincipalAtom,
    show -(s + 1) = (-1 : ℂ) + (-s) by ring,
    Complex.cpow_add (-1) (-s) hbaseC, Complex.cpow_neg, Complex.cpow_one]
  rw [one_div, Complex.ofReal_inv]

theorem integerLogMeshAtom_eq_remainder_add_principal (s : ℂ) (N : ℕ) :
    integerLogMeshAtom s N =
      integerLogMeshRemainderAtom s N + integerLogMeshPrincipalAtom s N := by
  rw [integerLogMeshAtom, integerLogMeshRemainderAtom,
    integerLogMeshPrincipalAtom_eq, integerLogMeshRemainderCoeff]
  push_cast
  ring

theorem summable_integerLogMeshPrincipalAtom {s : ℂ} (hs : 0 < s.re) :
    Summable (integerLogMeshPrincipalAtom s) := by
  let a : ℝ := 1 + s.re
  have ha : 1 < a := by dsimp only [a]; linarith
  have hp0 := GaloisForLFunctions.RHTower.summable_one_div_nat_add_one_rpow ha
  have hp : Summable (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 2) ^ a) := by
    have hshift := (summable_nat_add_iff 1).mpr hp0
    exact hshift.congr fun N => by push_cast; ring
  refine Summable.of_norm_bounded hp fun N => ?_
  have hbase : 0 < (N : ℝ) + 2 := by positivity
  rw [integerLogMeshPrincipalAtom, Complex.norm_cpow_eq_rpow_re_of_pos hbase]
  simp only [neg_re, add_re, one_re]
  rw [show -(s.re + 1) = -(1 + s.re) by ring, Real.rpow_neg hbase.le]
  dsimp only [a]
  rw [one_div]

theorem norm_integerLogMeshRemainderAtom_le (s : ℂ) (N : ℕ) :
    ‖integerLogMeshRemainderAtom s N‖ ≤
      2 / ((N : ℝ) + 2) ^ (2 + s.re) := by
  have hbase : 0 < (N : ℝ) + 2 := by positivity
  rw [integerLogMeshRemainderAtom, norm_mul, norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hbase]
  have hc := abs_integerLogMeshRemainderCoeff_le N
  have hpow : 0 ≤ ((N : ℝ) + 2) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  calc
    |integerLogMeshRemainderCoeff N| * ((N : ℝ) + 2) ^ (-s.re) ≤
        (2 / ((N : ℝ) + 2) ^ 2) * ((N : ℝ) + 2) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right hc hpow
    _ = 2 / ((N : ℝ) + 2) ^ (2 + s.re) := by
      rw [Real.rpow_neg hbase.le]
      have htwo : ((N : ℝ) + 2) ^ 2 = ((N : ℝ) + 2) ^ (2 : ℝ) := by
        norm_num [Real.rpow_natCast]
      have hadd : ((N : ℝ) + 2) ^ (2 + s.re) =
          ((N : ℝ) + 2) ^ 2 * ((N : ℝ) + 2) ^ s.re := by
        rw [htwo, Real.rpow_add hbase]
      rw [hadd]
      field_simp [(Real.rpow_pos_of_pos hbase s.re).ne']

theorem summable_integerLogMeshRemainderAtom {s : ℂ} (hs : -1 < s.re) :
    Summable (integerLogMeshRemainderAtom s) := by
  let a : ℝ := 2 + s.re
  have ha : 1 < a := by dsimp only [a]; linarith
  have hp0 : Summable (fun N : ℕ =>
      (1 : ℝ) / ((N : ℝ) + 1) ^ a) :=
    GaloisForLFunctions.RHTower.summable_one_div_nat_add_one_rpow ha
  have hp : Summable (fun N : ℕ =>
      (2 : ℝ) / ((N : ℝ) + 2) ^ a) := by
    have hshift := (summable_nat_add_iff 1).mpr hp0
    exact (hshift.mul_left 2).congr fun N => by
      dsimp only [a]
      push_cast
      ring
  exact Summable.of_norm_bounded hp fun N => by
    simpa only [a] using norm_integerLogMeshRemainderAtom_le s N

theorem summable_integerLogMeshAtom {s : ℂ} (hs : 0 < s.re) :
    Summable (integerLogMeshAtom s) := by
  have hr := summable_integerLogMeshRemainderAtom (s := s) (by linarith)
  have hp := summable_integerLogMeshPrincipalAtom (s := s) hs
  exact (hr.add hp).congr fun N =>
    (integerLogMeshAtom_eq_remainder_add_principal s N).symm

theorem integerLogMeshPrincipalCurrent_eq_riemannZeta_sub_one
    {s : ℂ} (hs : 0 < s.re) :
    integerLogMeshPrincipalCurrent s = riemannZeta (s + 1) - 1 := by
  let f : ℕ → ℂ := fun N => (((N : ℂ) + 1) ^ (-(s + 1)))
  have hp := summable_integerLogMeshPrincipalAtom (s := s) hs
  have htail : Summable (fun N : ℕ => f (N + 1)) := by
    exact hp.congr fun N => by
      rw [integerLogMeshPrincipalAtom]
      dsimp only [f]
      congr 2
      push_cast
      ring
  have hsplit := htail.sum_add_tsum_nat_add' (k := 1)
  have hz := tsum_one_add_cpow_eq_zeta (s := s + 1) (by
    simp only [add_re, one_re]
    linarith)
  have hhead : ∑ N ∈ Finset.range 1, f N = 1 := by
    simp [f]
  have htailCurrent : (∑' N : ℕ, f (N + 1)) =
      integerLogMeshPrincipalCurrent s := by
    rw [integerLogMeshPrincipalCurrent]
    apply tsum_congr
    intro N
    rw [integerLogMeshPrincipalAtom]
    dsimp only [f]
    congr 2
    push_cast
    ring
  rw [hhead, htailCurrent, hz] at hsplit
  linear_combination hsplit

def integerLogMeshContinuation (s : ℂ) : ℂ :=
  riemannZeta (s + 1) - 1 + integerLogMeshRemainderCurrent s

theorem integerLogMeshContinuation_eq_current {s : ℂ} (hs : 0 < s.re) :
    integerLogMeshContinuation s = integerLogMeshCurrent s := by
  have hr := summable_integerLogMeshRemainderAtom (s := s) (by linarith)
  have hp := summable_integerLogMeshPrincipalAtom (s := s) hs
  rw [integerLogMeshContinuation,
    ← integerLogMeshPrincipalCurrent_eq_riemannZeta_sub_one hs,
    integerLogMeshPrincipalCurrent, integerLogMeshRemainderCurrent,
    integerLogMeshCurrent, ← hp.tsum_add hr]
  apply tsum_congr
  intro N
  rw [integerLogMeshAtom_eq_remainder_add_principal]
  ac_rfl

theorem differentiableAt_integerLogMeshRemainderCurrent
    {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ integerLogMeshRemainderCurrent s := by
  let sigma : ℝ := (s.re - 1) / 2
  let radius : ℝ := (s.re + 1) / 2
  have hradius : 0 < radius := by dsimp only [radius]; linarith
  have hsigma : -1 < sigma := by dsimp only [sigma]; linarith
  let bound : ℕ → ℝ := fun N => 2 / ((N : ℝ) + 2) ^ (2 + sigma)
  have hboundSum : Summable bound := by
    have ha : 1 < 2 + sigma := by linarith
    have hp0 := GaloisForLFunctions.RHTower.summable_one_div_nat_add_one_rpow ha
    have hp := (summable_nat_add_iff 1).mpr hp0
    exact (hp.mul_left 2).congr fun N => by
      dsimp only [bound]
      push_cast
      ring
  have hdiff : ∀ N : ℕ,
      DifferentiableOn ℂ (integerLogMeshRemainderAtom · N) (Metric.ball s radius) := by
    intro N
    intro z hz
    have hbase : ((((N : ℝ) + 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (N : ℝ) + 2 ≠ 0 by positivity)
    unfold integerLogMeshRemainderAtom
    exact (((differentiableAt_id.neg).const_cpow (Or.inl hbase)).const_mul
      (integerLogMeshRemainderCoeff N : ℂ)).differentiableWithinAt
  have hbound : ∀ N : ℕ, ∀ z ∈ Metric.ball s radius,
      ‖integerLogMeshRemainderAtom z N‖ ≤ bound N := by
    intro N z hz
    have hdist : ‖z - s‖ < radius := by
      rw [Metric.mem_ball, dist_eq] at hz
      exact hz
    have hreNorm : |(z - s).re| ≤ ‖z - s‖ := abs_re_le_norm (z - s)
    have hre : sigma < z.re := by
      dsimp only [sigma, radius] at hdist ⊢
      simp only [sub_re] at hreNorm
      have hleft : -‖z - s‖ ≤ z.re - s.re := by
        have := (abs_le.mp hreNorm).1
        simpa only [sub_re] using this
      linarith
    have hbase : 1 ≤ (N : ℝ) + 2 := by
      have hN : (0 : ℝ) ≤ N := by positivity
      linarith
    have hpow : ((N : ℝ) + 2) ^ (2 + sigma) ≤
        ((N : ℝ) + 2) ^ (2 + z.re) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    have hdenpos : 0 < ((N : ℝ) + 2) ^ (2 + sigma) := by positivity
    calc
      ‖integerLogMeshRemainderAtom z N‖ ≤
          2 / ((N : ℝ) + 2) ^ (2 + z.re) :=
        norm_integerLogMeshRemainderAtom_le z N
      _ ≤ 2 / ((N : ℝ) + 2) ^ (2 + sigma) := by
        exact div_le_div_of_nonneg_left (by norm_num) hdenpos hpow
      _ = bound N := rfl
  change DifferentiableAt ℂ
    (fun z : ℂ => ∑' N : ℕ, integerLogMeshRemainderAtom z N) s
  exact GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated
    hradius hdiff hbound hboundSum

theorem differentiableAt_integerLogMeshContinuation
    {s : ℂ} (hs : -1 < s.re) (hs0 : s ≠ 0) :
    DifferentiableAt ℂ integerLogMeshContinuation s := by
  have hzarg : s + 1 ≠ 1 := by
    intro h
    apply hs0
    linear_combination h
  have hz := (Sieve.analyticAt_riemannZeta_of_ne_one hzarg).differentiableAt
  have hzcomp : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (z + 1)) s :=
    hz.comp s (by fun_prop)
  exact (hzcomp.sub_const 1).add
    (differentiableAt_integerLogMeshRemainderCurrent hs)

end

end RHTower

