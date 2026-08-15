import GaloisForLFunctions.RHTower.BarnesCanonicalProductExpansion
import GaloisForLFunctions.HTGeometry.AsymptoticExpansionAlgebra
import GaloisForLFunctions.HTGeometry.BarnesTailNonlinearObstruction

/-!
# The Barnes remainder carries the formal tail as its asymptotic expansion

Subtracting from `D^m (x W_s'/W_s)` the leading power and the terms of the expansion at the
nonpositive integers leaves a function of `x` whose expansion at `x = +∞` is the descending series
`∑_{k ≥ 1} (-k)^m b_k x^{-k}`, `b_k = (-1)^k ζ(-sk)`.

In the variable `t = 1/x`, and after the sign `(-1)^m` that turns `x d/dx` into `t d/dt`, this says
exactly that the `m`-th Euler jet of the Barnes remainder has the `m`-th Euler jet of the formal
Barnes tail as its Poincaré expansion at `0⁺`.

The truncation bookkeeping is the only content: the contour ladder gives an error of order
`x^{-(J + 1/2)}` after `J` descending terms, and a half-integer of room is what makes the error of
one extra term absorb the next term of the expansion.
-/

open Complex Filter Set MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

variable {s : ℝ}

/-- The Barnes remainder at Euler weight `m`: the `m`-th Euler derivative of `x W_s'/W_s` with the
leading power and the terms at the nonpositive integers removed. -/
def barnesEulerRemainder (s : ℝ) (m : ℕ) (x : ℝ) : ℂ :=
  (eulerDeriv^[m] (powerCanonicalEulerSum s)) x
    + barnesLeadingGenusResidue s x m
    + ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
        barnesIntResidue s x m ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))

/-- The Barnes remainder read in `t = 1/x`, with the sign that turns `x d/dx` into `t d/dt`. -/
def barnesEulerJet (s : ℝ) (m : ℕ) (t : ℝ) : ℂ :=
  ((-1 : ℂ)) ^ m * barnesEulerRemainder s m (1 / t)

/-- At a positive integer the crossed residue is the corresponding term of the formal tail. -/
theorem neg_barnesIntResidue_succ (s x : ℝ) (m i : ℕ) :
    -barnesIntResidue s x m ((i : ℤ) + 1)
      = (-((i + 1 : ℕ) : ℂ)) ^ m * PowerSeries.coeff (i + 1) (barnesTailSeries s)
        * ((x : ℝ) : ℂ) ^ (-((i + 1 : ℕ) : ℂ)) := by
  have hcc : ((((i : ℤ) + 1 : ℤ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by push_cast; ring
  have hsign : ((-1 : ℂ)) ^ ((i : ℤ) + 1) = ((-1 : ℂ)) ^ (i + 1 : ℕ) := by
    rw [show ((i : ℤ) + 1 : ℤ) = ((i + 1 : ℕ) : ℤ) from by push_cast; ring, zpow_natCast]
  have hz : ((-(s * ((i + 1 : ℕ) : ℝ)) : ℝ) : ℂ) = -(s : ℂ) * (((i + 1 : ℕ)) : ℂ) := by
    push_cast; ring
  rw [barnesIntResidue, barnesTailSeries, PowerSeries.coeff_mk,
    if_neg (Nat.succ_ne_zero i), hsign, hcc, hz]
  ring

theorem coeff_zero_barnesTailSeries (s : ℝ) :
    PowerSeries.coeff 0 (barnesTailSeries s) = 0 := by
  rw [barnesTailSeries, PowerSeries.coeff_mk, if_pos rfl]

/-! ### The expansion in the original variable -/

/-- **The Barnes remainder has the descending tail as its expansion**, with an error of order
`x^{-(J+1/2)}` after `J` terms. -/
theorem barnesEulerRemainder_expansion (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) (m J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖barnesEulerRemainder s m x
          - ∑ j ∈ Finset.range (J + 1),
              (-(j : ℂ)) ^ m * PowerSeries.coeff j (barnesTailSeries s)
                * ((x : ℝ) : ℂ) ^ (-(j : ℂ))‖
        ≤ C * x ^ (-((J : ℝ) + 1 / 2)) := by
  classical
  obtain ⟨C, hC0, hC⟩ :=
    barnes_expansion_powerCanonicalProduct_euler hs hne m ((HTGeometry.powerGenus s + 1) + J)
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hsplit : ∑ k ∈ Finset.range ((HTGeometry.powerGenus s + 1) + J),
        barnesIntResidue s x m ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))
      = (∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
            barnesIntResidue s x m ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)))
        + ∑ i ∈ Finset.range J, barnesIntResidue s x m ((i : ℤ) + 1) := by
    rw [Finset.sum_range_add]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    congr 1
    push_cast
    ring
  have habs : genusAbscissa s (HTGeometry.powerGenus s) (((HTGeometry.powerGenus s + 1) + J) + 1)
      = (J : ℝ) + 1 / 2 := by
    rw [show ((HTGeometry.powerGenus s + 1) + J) + 1 = (J + HTGeometry.powerGenus s) + 2 from by omega,
      genusAbscissa_add_two]
    push_cast
    ring
  have hkey := hC x hx
  rw [hsplit, habs] at hkey
  have hid : ∑ j ∈ Finset.range (J + 1),
        (-(j : ℂ)) ^ m * PowerSeries.coeff j (barnesTailSeries s)
          * ((x : ℝ) : ℂ) ^ (-(j : ℂ))
      = -∑ i ∈ Finset.range J, barnesIntResidue s x m ((i : ℤ) + 1) := by
    rw [Finset.sum_range_succ', coeff_zero_barnesTailSeries, ← Finset.sum_neg_distrib]
    simp only [mul_zero, zero_mul, add_zero]
    exact Finset.sum_congr rfl fun i _ => (neg_barnesIntResidue_succ s x m i).symm
  rw [hid, sub_neg_eq_add]
  refine le_trans (le_of_eq (congrArg norm ?_)) hkey
  rw [barnesEulerRemainder]
  ring

/-! ### The expansion in the reciprocal variable -/

theorem eventually_lt_one_originRight : ∀ᶠ t : ℝ in originRight, t ≤ 1 := by
  filter_upwards [eventually_norm_le_one] with t ht
  rw [Complex.norm_real, Real.norm_eq_abs] at ht
  exact le_trans (le_abs_self t) ht

/-- **The `m`-th Euler jet of the Barnes remainder has the `m`-th Euler jet of the formal Barnes
tail as its Poincaré expansion at `0⁺`.** -/
theorem isAsymptoticExpansion_barnesEulerJet (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) (m : ℕ) :
    IsAsymptoticExpansion (barnesEulerJet s m)
      (formalEulerOp^[m] (barnesTailSeries s)) := by
  classical
  intro N
  obtain ⟨C, hC0, hC⟩ := barnesEulerRemainder_expansion hs hne m N
  set φ : PowerSeries ℂ := formalEulerOp^[m] (barnesTailSeries s) with hφ
  refine Asymptotics.IsBigO.of_bound (C + ‖PowerSeries.coeff N φ‖) ?_
  filter_upwards [self_mem_nhdsWithin, eventually_lt_one_originRight] with t ht htle
  have htpos : (0 : ℝ) < t := ht
  have hxpos : (0 : ℝ) < 1 / t := by positivity
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htpos)
  have hpow : ∀ j : ℕ, (((1 / t : ℝ)) : ℂ) ^ (-(j : ℂ)) = ((t : ℝ) : ℂ) ^ j := by
    intro j
    have hcast : (-(j : ℂ)) = (((-(j : ℤ)) : ℤ) : ℂ) := by push_cast; ring
    rw [Complex.ofReal_div, Complex.ofReal_one, one_div, hcast, Complex.cpow_intCast,
      zpow_neg, zpow_natCast, inv_pow, inv_inv]
  have hcoeff : ∀ j : ℕ,
      ((-1 : ℂ)) ^ m * ((-(j : ℂ)) ^ m * PowerSeries.coeff j (barnesTailSeries s)
          * (((1 / t : ℝ)) : ℂ) ^ (-(j : ℂ)))
        = PowerSeries.coeff j φ * ((t : ℝ) : ℂ) ^ j := by
    intro j
    rw [hpow j, hφ, coeff_formalEulerOp_iterate]
    rw [show (-(j : ℂ)) ^ m = ((-1 : ℂ)) ^ m * (j : ℂ) ^ m from by rw [← mul_pow]; ring]
    have hsq : ((-1 : ℂ)) ^ m * ((-1 : ℂ)) ^ m = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    calc ((-1 : ℂ)) ^ m * (((-1 : ℂ)) ^ m * (j : ℂ) ^ m * PowerSeries.coeff j (barnesTailSeries s)
            * ((t : ℝ) : ℂ) ^ j)
        = (((-1 : ℂ)) ^ m * ((-1 : ℂ)) ^ m) *
            ((j : ℂ) ^ m * PowerSeries.coeff j (barnesTailSeries s) * ((t : ℝ) : ℂ) ^ j) := by
          ring
      _ = (j : ℂ) ^ m * PowerSeries.coeff j (barnesTailSeries s) * ((t : ℝ) : ℂ) ^ j := by
          rw [hsq, one_mul]
  have hmain : ‖barnesEulerJet s m t
      - ∑ j ∈ Finset.range (N + 1), PowerSeries.coeff j φ * ((t : ℝ) : ℂ) ^ j‖
      ≤ C * t ^ ((N : ℝ) + 1 / 2) := by
    have hrw : barnesEulerJet s m t
        - ∑ j ∈ Finset.range (N + 1), PowerSeries.coeff j φ * ((t : ℝ) : ℂ) ^ j
        = ((-1 : ℂ)) ^ m *
          (barnesEulerRemainder s m (1 / t)
            - ∑ j ∈ Finset.range (N + 1),
                (-(j : ℂ)) ^ m * PowerSeries.coeff j (barnesTailSeries s)
                  * (((1 / t : ℝ)) : ℂ) ^ (-(j : ℂ))) := by
      rw [barnesEulerJet, mul_sub, Finset.mul_sum]
      refine congrArg _ (Finset.sum_congr rfl fun j _ => (hcoeff j).symm)
    have hnorm : ‖((-1 : ℂ)) ^ m‖ = 1 := by
      rw [norm_pow, norm_neg, norm_one, one_pow]
    have hrpow : (1 / t) ^ (-((N : ℝ) + 1 / 2)) = t ^ ((N : ℝ) + 1 / 2) := by
      rw [one_div, Real.inv_rpow htpos.le, Real.rpow_neg (by positivity), inv_inv]
    rw [hrw, norm_mul, hnorm, one_mul]
    have h := hC (1 / t) hxpos
    rwa [hrpow] at h
  have hnormpow : ‖((t : ℝ) : ℂ) ^ N‖ = t ^ N := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have hhalf : t ^ ((N : ℝ) + 1 / 2) ≤ t ^ N := by
    have h := Real.rpow_le_rpow_of_exponent_ge htpos htle
      (show (N : ℝ) ≤ (N : ℝ) + 1 / 2 from by linarith)
    rwa [Real.rpow_natCast] at h
  have hsplit : barnesEulerJet s m t
      - ∑ j ∈ Finset.range N, PowerSeries.coeff j φ * ((t : ℝ) : ℂ) ^ j
      = (barnesEulerJet s m t
          - ∑ j ∈ Finset.range (N + 1), PowerSeries.coeff j φ * ((t : ℝ) : ℂ) ^ j)
        + PowerSeries.coeff N φ * ((t : ℝ) : ℂ) ^ N := by
    rw [Finset.sum_range_succ]
    ring
  rw [hsplit, hnormpow]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖barnesEulerJet s m t
      - ∑ j ∈ Finset.range (N + 1), PowerSeries.coeff j φ * ((t : ℝ) : ℂ) ^ j‖ ≤ C * t ^ N :=
    le_trans hmain (mul_le_mul_of_nonneg_left hhalf hC0)
  have h2 : ‖PowerSeries.coeff N φ * ((t : ℝ) : ℂ) ^ N‖ = ‖PowerSeries.coeff N φ‖ * t ^ N := by
    rw [norm_mul, hnormpow]
  rw [h2]
  have : C * t ^ N + ‖PowerSeries.coeff N φ‖ * t ^ N
      = (C + ‖PowerSeries.coeff N φ‖) * t ^ N := by ring
  linarith [h1]

end

end RHTower
