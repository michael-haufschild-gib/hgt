import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergyThreeQuarter
import GaloisForLFunctions.HTGeometry.CpowHarmonicTailAsymptotic
import GaloisForLFunctions.RHTower.ConstrainedProlateRayleighFloor
import GaloisForLFunctions.RHTower.ZetaRealBound

/-!
# Natural Wold square energy reaches the translated critical wall

Let `R N` be the literal centered Wold discrepancy at every natural cutoff.  Its weighted square
energy at radius `t` is exactly the square norm of `N^(t-1/2) R N`.  When `t > 1/2`,
Cauchy--Schwarz against the ordinary `p`-series `sum N^(-2t)` gives the sharp consequence

`sum N, |R (N+1)| (N+1)^(-1/2) < infinity`.

Testing this `l¹` sequence against the adjacent complex-power difference defines the natural Abel
current.  The unit-window complex-power estimate bounds its atom throughout `Re s >= -1/2` by
`||s|| |R (N+1)| (N+1)^(-1/2)`.  Hence the current converges absolutely on the closed translated
critical half-plane and is radially continuous at every nonreal wall point.

This discharges the Hilbert-to-critical-wall premise of the T2 natural-Abel no-go chain.  It avoids
prime-gap moments entirely: the dual threshold is the exact ordinary `p`-series aperture
`t > 1/2`.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

local notation "R" => xiHeatCassiniWoldNatResidualLogDiscrepancy

/-- Above the exact half-density threshold, natural Wold square energy forces the critical-wall
weighted `l¹` residual sum. -/
theorem summable_abs_woldNatResidual_mul_succ_rpow_neg_half_of_squareEnergy
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t) :
    Summable (fun N : ℕ =>
      |R (N + 1)| * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  let a : ℕ → ℝ := fun N =>
    ((N : ℝ) + 1) ^ (t - 1 / 2) * |R (N + 1)|
  let b : ℕ → ℝ := fun N => ((N : ℝ) + 1) ^ (-t)
  have ha2 : Summable (fun N : ℕ => a N ^ 2) := by
    have hshift : Summable (fun N : ℕ =>
        ((N + 1 : ℕ) : ℝ) ^ (2 * t - 1) * |R (N + 1)| ^ 2) :=
      (summable_nat_add_iff 1).mpr hEnergy
    refine hshift.congr fun N => ?_
    have hpos : 0 < (N : ℝ) + 1 := by positivity
    dsimp only [a]
    rw [mul_pow]
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    congr 1
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hpos.le]
    congr 1
    norm_num
    ring
  have hb2 : Summable (fun N : ℕ => b N ^ 2) := by
    have hp : Summable (fun N : ℕ =>
        (1 : ℝ) / ((N : ℝ) + 1) ^ (2 * t)) :=
      GaloisForLFunctions.RHTower.summable_one_div_nat_add_one_rpow (by linarith)
    refine hp.congr fun N => ?_
    have hpos : 0 < (N : ℝ) + 1 := by positivity
    dsimp only [b]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hpos.le]
    norm_num
    rw [show -(t * 2) = -(2 * t) by ring, Real.rpow_neg hpos.le]
  have hab : Summable (fun N : ℕ => a N * b N) :=
    summable_mul_of_sq_summable ha2 hb2
  refine hab.congr fun N => ?_
  have hpos : 0 < (N : ℝ) + 1 := by positivity
  dsimp only [a, b]
  calc
    ((N : ℝ) + 1) ^ (t - 1 / 2) * |R (N + 1)| *
        ((N : ℝ) + 1) ^ (-t) =
        |R (N + 1)| * (((N : ℝ) + 1) ^ (t - 1 / 2) *
          ((N : ℝ) + 1) ^ (-t)) := by ring
    _ = |R (N + 1)| * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hpos]
      congr 2
      ring

/-- Natural first-difference Abel atom of the literal Wold residual. -/
def woldNatResidualAbelAtom (s : ℂ) (N : ℕ) : ℂ :=
  (R (N + 1) : ℂ) *
    (((((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) -
      ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))

/-- Natural first-difference Abel current of the literal Wold residual. -/
def woldNatResidualAbelCurrent (s : ℂ) : ℂ :=
  ∑' N : ℕ, woldNatResidualAbelAtom s N

private theorem norm_woldNatResidualAbelAtom_le
    {s : ℂ} (hsne : s ≠ 0) (hsre : -(1 / 2 : ℝ) ≤ s.re) (N : ℕ) :
    ‖woldNatResidualAbelAtom s N‖ ≤
      ‖s‖ * (|R (N + 1)| * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  have hm : 0 < (N : ℝ) + 1 := by positivity
  have ht : (N : ℝ) + 2 ∈ Set.Icc ((N : ℝ) + 1) (((N : ℝ) + 1) + 1) := by
    constructor <;> linarith
  have hwne : -s ≠ 0 := neg_ne_zero.mpr hsne
  have hwre : (-s).re ≤ 1 := by
    simp only [neg_re]
    linarith
  have hinc := GaloisForLFunctions.HTGeometry.norm_ofReal_cpow_sub_le
    hwne hwre hm ht
  have hexp : (-s).re - 1 ≤ -(1 / 2 : ℝ) := by
    simp only [neg_re]
    linarith
  have hbase : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have hN : (0 : ℝ) ≤ N := by positivity
    linarith
  have hpow : ((N : ℝ) + 1) ^ ((-s).re - 1) ≤
      ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  rw [norm_sub_rev] at hinc
  have hinc' :
      ‖(((((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) -
          ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))‖ ≤
        ‖s‖ * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖(((((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) -
          ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))‖ ≤
          ‖-s‖ * ((N : ℝ) + 1) ^ ((-s).re - 1) := hinc
      _ ≤ ‖-s‖ * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = ‖s‖ * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by rw [norm_neg]
  rw [woldNatResidualAbelAtom, norm_mul, norm_real, Real.norm_eq_abs]
  calc
    |R (N + 1)| *
        ‖(((((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) -
          ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))‖ ≤
        |R (N + 1)| *
          (‖s‖ * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hinc' (abs_nonneg _)
    _ = ‖s‖ *
        (|R (N + 1)| * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by ring

/-- Square energy above one half makes the natural Abel current absolutely convergent on the
closed translated critical half-plane, away from the harmless point `s = 0`. -/
theorem summable_woldNatResidualAbelAtom_of_squareEnergy
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t)
    {s : ℂ} (hsne : s ≠ 0) (hsre : -(1 / 2 : ℝ) ≤ s.re) :
    Summable (woldNatResidualAbelAtom s) := by
  have hmajor :=
    (summable_abs_woldNatResidual_mul_succ_rpow_neg_half_of_squareEnergy ht hEnergy).mul_left ‖s‖
  exact Summable.of_norm_bounded hmajor (norm_woldNatResidualAbelAtom_le hsne hsre)

/-- Square energy above one half makes the natural Abel current radially continuous at every
nonreal point of the translated critical wall. -/
theorem tendsto_woldNatResidualAbelCurrent_critical_radial_of_squareEnergy
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t)
    {s0 : ℂ} (hs0re : s0.re = -(1 / 2 : ℝ)) (hs0im : s0.im ≠ 0) :
    Tendsto (fun x : ℝ => woldNatResidualAbelCurrent (s0 + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (woldNatResidualAbelCurrent s0)) := by
  let q : ℕ → ℝ := fun N =>
    |R (N + 1)| * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ))
  let bound : ℕ → ℝ := fun N => (‖s0‖ + 1) * q N
  have hq : Summable q :=
    summable_abs_woldNatResidual_mul_succ_rpow_neg_half_of_squareEnergy ht hEnergy
  have hbound : Summable bound := hq.mul_left (‖s0‖ + 1)
  have hpath : Tendsto (fun x : ℝ => s0 + (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 s0) := by
    have hcont : ContinuousAt (fun x : ℝ => s0 + (x : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpoint : ∀ N : ℕ,
      Tendsto (fun x : ℝ => woldNatResidualAbelAtom (s0 + (x : ℂ)) N)
        (𝓝[>] (0 : ℝ)) (𝓝 (woldNatResidualAbelAtom s0 N)) := by
    intro N
    have hbase1 : ((((N : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (N : ℝ) + 1 ≠ 0 by positivity)
    have hbase2 : ((((N : ℝ) + 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (N : ℝ) + 2 ≠ 0 by positivity)
    have hexp : Tendsto (fun x : ℝ => -(s0 + (x : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (-s0)) := hpath.neg
    have hpow1 := hexp.const_cpow (a := ((((N : ℝ) + 1 : ℝ) : ℂ))) (Or.inl hbase1)
    have hpow2 := hexp.const_cpow (a := ((((N : ℝ) + 2 : ℝ) : ℂ))) (Or.inl hbase2)
    exact (hpow1.sub hpow2).const_mul (R (N + 1) : ℂ)
  have hdom : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), ∀ N : ℕ,
      ‖woldNatResidualAbelAtom (s0 + (x : ℂ)) N‖ ≤ bound N := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx hx1 N
    have hx0 : 0 < x := hx
    have hsne : s0 + (x : ℂ) ≠ 0 := by
      intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at him
      exact hs0im him
    have hsre : -(1 / 2 : ℝ) ≤ (s0 + (x : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re, hs0re]
      linarith
    have hnorm : ‖s0 + (x : ℂ)‖ ≤ ‖s0‖ + 1 := by
      calc
        ‖s0 + (x : ℂ)‖ ≤ ‖s0‖ + ‖(x : ℂ)‖ := norm_add_le _ _
        _ = ‖s0‖ + x := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
        _ ≤ ‖s0‖ + 1 := by linarith
    have hqnonneg : 0 ≤ q N := by
      dsimp only [q]
      positivity
    calc
      ‖woldNatResidualAbelAtom (s0 + (x : ℂ)) N‖ ≤
          ‖s0 + (x : ℂ)‖ * q N := by
        simpa only [q] using norm_woldNatResidualAbelAtom_le hsne hsre N
      _ ≤ (‖s0‖ + 1) * q N :=
        mul_le_mul_of_nonneg_right hnorm hqnonneg
      _ = bound N := rfl
  simpa only [woldNatResidualAbelCurrent] using
    tendsto_tsum_of_dominated_convergence hbound hpoint hdom

end

end RHTower
