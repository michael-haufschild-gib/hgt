import GaloisForLFunctions.RHTower.ShiftPairLocalIntersectionAlgebra
import GaloisForLFunctions.RHTower.PairIdealCensusAlgebra
import GaloisForLFunctions.HTGeometry.EntirePoincareLelong
import GaloisForLFunctions.RHTower.XiHorizontalCollisionChargeEndpoint
import GaloisForLFunctions.RHTower.XiHorizontalCollisionGaussHodgePrimeCurrent
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.WindingXiCircle
import GaloisForLFunctions.HTGeometry.DivisorPairing
import Mathlib.Topology.Algebra.Order.Field

/-!
# Euler shift-pair incidence current

The inverse center/shift coordinate map sends an ordered zero pair `(rho,sigma)` to
`((rho+sigma)/2,(sigma-rho)/2)`.  This file pushes the canonical Poincare--Lelong divisor current
through that map, takes a positive-real-shift thin slice, and proves that the cutoff-independent
limit is exactly the Xi horizontal-collision charge.

The same module records the diagonal conservation law and the exact distinction between local
intersection product multiplicity `m*n` and quotient-cancellation multiplicity `min m n`.
-/

open Complex Set Filter Topology

namespace RHTower
namespace EulerShiftPairIncidenceCurrent

noncomputable section

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.ShiftPairLocalIntersectionAlgebra
open GaloisForLFunctions.RHTower.PairIdealCensusAlgebra

/-- A normalized continuous cutoff supported in `[-1,1]`. -/
structure Cutoff where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  nonneg : ∀ x, 0 ≤ toFun x
  le_one : ∀ x, toFun x ≤ 1
  zero_value : toFun 0 = 1
  eq_zero_of_one_lt_abs : ∀ x, 1 < |x| → toFun x = 0

instance : CoeFun Cutoff (fun _ => ℝ → ℝ) := ⟨Cutoff.toFun⟩

/-- Inverse center/shift coordinate map `(rho,sigma) ↦ (c,u)`. -/
def point (rho sigma : ℂ) : ℂ × ℂ :=
  ((rho + sigma) / 2, (sigma - rho) / 2)

@[simp] theorem point_center_im (rho sigma : ℂ) :
    (point rho sigma).1.im = (rho.im + sigma.im) / 2 := by
  simp [point]

@[simp] theorem point_shift_re (rho sigma : ℂ) :
    (point rho sigma).2.re = (sigma.re - rho.re) / 2 := by
  simp [point]

@[simp] theorem point_shift_im (rho sigma : ℂ) :
    (point rho sigma).2.im = (sigma.im - rho.im) / 2 := by
  simp [point]

/-- Weight of one ordered zero pair in a thin positive-real-shift slice. -/
def weight (k : Cutoff) (lo hi eps : ℝ) (rho sigma : ℂ) : ℝ :=
  if lo ≤ (point rho sigma).1.im ∧ (point rho sigma).1.im < hi ∧
      0 < (point rho sigma).2.re then
    k ((point rho sigma).2.im / eps)
  else 0

/-- Finite weighted mass of a thin positive-real-shift slice. -/
def mass (S : Finset ℂ) (m : ℂ → ℕ) (k : Cutoff)
    (lo hi eps : ℝ) : ℝ :=
  2 * ∑ rho ∈ S, ∑ sigma ∈ S,
    (m rho : ℝ) * (m sigma : ℝ) * weight k lo hi eps rho sigma

/-- Pointwise zero-width limit of `weight`. -/
def limitWeight (lo hi : ℝ) (rho sigma : ℂ) : ℝ :=
  if lo ≤ (point rho sigma).1.im ∧ (point rho sigma).1.im < hi ∧
      0 < (point rho sigma).2.re ∧ (point rho sigma).2.im = 0 then 1 else 0

/-- Finite zero-width mass. -/
def limitMass (S : Finset ℂ) (m : ℂ → ℕ) (lo hi : ℝ) : ℝ :=
  2 * ∑ rho ∈ S, ∑ sigma ∈ S,
    (m rho : ℝ) * (m sigma : ℝ) * limitWeight lo hi rho sigma

theorem tendsto_cutoff_div {k : Cutoff} {d : ℝ} :
    Tendsto (fun eps : ℝ => k (d / eps)) (nhdsWithin 0 (Ioi 0))
      (nhds (if d = 0 then 1 else 0)) := by
  by_cases hd : d = 0
  · subst d
    simp [k.zero_value]
  · have hevent : ∀ᶠ eps in nhdsWithin 0 (Ioi (0 : ℝ)), k (d / eps) = 0 := by
      have hdpos : 0 < |d| := abs_pos.mpr hd
      filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < |d| / 2)] with eps heps
      apply k.eq_zero_of_one_lt_abs
      rw [abs_div, abs_of_pos heps.1, one_lt_div heps.1]
      exact lt_trans heps.2 (by linarith)
    simpa [hd] using tendsto_nhds_of_eventually_eq hevent

theorem tendsto_weight (k : Cutoff) (lo hi : ℝ) (rho sigma : ℂ) :
    Tendsto (fun eps : ℝ => weight k lo hi eps rho sigma)
      (nhdsWithin 0 (Ioi 0)) (nhds (limitWeight lo hi rho sigma)) := by
  by_cases hc : lo ≤ (point rho sigma).1.im ∧
      (point rho sigma).1.im < hi ∧ 0 < (point rho sigma).2.re
  · have hmain := tendsto_cutoff_div
      (k := k) (d := (point rho sigma).2.im)
    by_cases him : (point rho sigma).2.im = 0
    · have hlim : lo ≤ (point rho sigma).1.im ∧
          (point rho sigma).1.im < hi ∧ 0 < (point rho sigma).2.re ∧
            (point rho sigma).2.im = 0 := ⟨hc.1, hc.2.1, hc.2.2, him⟩
      simp only [weight, if_pos hc, limitWeight, if_pos hlim]
      simpa only [him, if_pos] using hmain
    · have hlim : ¬ (lo ≤ (point rho sigma).1.im ∧
          (point rho sigma).1.im < hi ∧ 0 < (point rho sigma).2.re ∧
            (point rho sigma).2.im = 0) := fun h => him h.2.2.2
      simp only [weight, if_pos hc, limitWeight, if_neg hlim]
      simpa only [him, if_neg, if_false] using hmain
  · have hlc : ¬ (lo ≤ (point rho sigma).1.im ∧
        (point rho sigma).1.im < hi ∧ 0 < (point rho sigma).2.re ∧
          (point rho sigma).2.im = 0) := by
      intro h
      exact hc ⟨h.1, h.2.1, h.2.2.1⟩
    simp only [weight, if_neg hc, limitWeight, if_neg hlc]
    exact tendsto_const_nhds

theorem tendsto_mass (S : Finset ℂ) (m : ℂ → ℕ) (k : Cutoff)
    (lo hi : ℝ) :
    Tendsto (fun eps : ℝ => mass S m k lo hi eps)
      (nhdsWithin 0 (Ioi 0)) (nhds (limitMass S m lo hi)) := by
  have houter : Tendsto
      (fun eps : ℝ => ∑ rho ∈ S, ∑ sigma ∈ S,
        (m rho : ℝ) * (m sigma : ℝ) * weight k lo hi eps rho sigma)
      (nhdsWithin 0 (Ioi 0))
      (nhds (∑ rho ∈ S, ∑ sigma ∈ S,
        (m rho : ℝ) * (m sigma : ℝ) * limitWeight lo hi rho sigma)) := by
    apply tendsto_finsetSum S
    intro rho _
    apply tendsto_finsetSum S
    intro sigma _
    simpa [mul_assoc] using tendsto_const_nhds.mul (tendsto_const_nhds.mul
      (tendsto_weight k lo hi rho sigma))
  simpa [mass, limitMass] using tendsto_const_nhds.mul houter

/-- Ordered same-height pairs selected by positive real shift. -/
def orientedPairs (S : Finset ℂ) (lo hi : ℝ) : Finset (ℂ × ℂ) :=
  (S ×ˢ S).filter fun p =>
    lo ≤ p.1.im ∧ p.1.im < hi ∧ p.1.im = p.2.im ∧ p.1.re < p.2.re

/-- Both orientations of distinct same-height pairs. -/
def collisionPairs (S : Finset ℂ) (lo hi : ℝ) : Finset (ℂ × ℂ) :=
  (S ×ˢ S).filter fun p =>
    lo ≤ p.1.im ∧ p.1.im < hi ∧ p.1.im = p.2.im ∧ p.1 ≠ p.2

theorem limitWeight_eq_indicator (lo hi : ℝ) (rho sigma : ℂ) :
    limitWeight lo hi rho sigma =
      if lo ≤ rho.im ∧ rho.im < hi ∧ rho.im = sigma.im ∧ rho.re < sigma.re
      then 1 else 0 := by
  have heq :
      (lo ≤ (point rho sigma).1.im ∧ (point rho sigma).1.im < hi ∧
        0 < (point rho sigma).2.re ∧ (point rho sigma).2.im = 0) ↔
      (lo ≤ rho.im ∧ rho.im < hi ∧ rho.im = sigma.im ∧ rho.re < sigma.re) := by
    constructor
    · rintro ⟨hlo, hhi, hre, him⟩
      have hsame : rho.im = sigma.im := by
        rw [point_shift_im, div_eq_zero_iff] at him
        rcases him with h | h
        · linarith
        · norm_num at h
      have hcenter : (rho.im + sigma.im) / 2 = rho.im := by
        rw [← hsame]
        ring
      rw [point_center_im, hcenter] at hlo hhi
      rw [point_shift_re] at hre
      exact ⟨hlo, hhi, hsame, by linarith⟩
    · rintro ⟨hlo, hhi, hsame, hre⟩
      have hcenter : (rho.im + sigma.im) / 2 = rho.im := by
        rw [← hsame]
        ring
      rw [point_center_im, hcenter, point_shift_re, point_shift_im]
      exact ⟨hlo, hhi, by linarith, by rw [← hsame]; simp⟩
  simp only [limitWeight]
  rw [if_congr heq rfl rfl]

theorem limitMass_eq_orientedPairs (S : Finset ℂ) (m : ℂ → ℕ) (lo hi : ℝ) :
    limitMass S m lo hi =
      2 * ∑ p ∈ orientedPairs S lo hi, (m p.1 : ℝ) * (m p.2 : ℝ) := by
  rw [limitMass, orientedPairs, Finset.sum_filter, Finset.sum_product]
  apply congrArg (fun x : ℝ => 2 * x)
  apply Finset.sum_congr rfl
  intro rho _
  apply Finset.sum_congr rfl
  intro sigma _
  rw [limitWeight_eq_indicator]
  by_cases h : lo ≤ rho.im ∧ rho.im < hi ∧ rho.im = sigma.im ∧ rho.re < sigma.re
  · simp [h]
  · simp [h]

theorem sum_collisionPairs_eq_two_mul_orientedPairs
    (S : Finset ℂ) (m : ℂ → ℕ) (lo hi : ℝ) :
    (∑ p ∈ collisionPairs S lo hi, (m p.1 : ℝ) * (m p.2 : ℝ)) =
      2 * ∑ p ∈ orientedPairs S lo hi, (m p.1 : ℝ) * (m p.2 : ℝ) := by
  let P := collisionPairs S lo hi
  let Q := orientedPairs S lo hi
  let F : ℂ × ℂ → ℝ := fun p => (m p.1 : ℝ) * (m p.2 : ℝ)
  have hpos : P.filter (fun p => p.1.re < p.2.re) = Q := by
    ext p
    simp only [P, Q, collisionPairs, orientedPairs, Finset.mem_filter,
      Finset.mem_product]
    constructor
    · rintro ⟨⟨hS, hlo, hhi, him, _hne⟩, hlt⟩
      exact ⟨hS, hlo, hhi, him, hlt⟩
    · rintro ⟨hS, hlo, hhi, him, hlt⟩
      refine ⟨⟨hS, hlo, hhi, him, ?_⟩, hlt⟩
      intro heq
      exact (ne_of_lt hlt) (congrArg Complex.re heq)
  have hneg :
      ∑ p ∈ P.filter (fun p => ¬ p.1.re < p.2.re), F p = ∑ p ∈ Q, F p := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp
      rcases hp with ⟨hpP, hnlt⟩
      simp only [P, collisionPairs, Finset.mem_filter, Finset.mem_product] at hpP
      rcases hpP with ⟨⟨hpS, hqS⟩, hlo, hhi, him, hne⟩
      have hreNe : p.2.re ≠ p.1.re := by
        intro hre
        apply hne
        apply Complex.ext
        · exact hre.symm
        · exact him
      have hlt : p.2.re < p.1.re :=
        lt_of_le_of_ne (not_lt.mp hnlt) hreNe
      simp only [Q, orientedPairs, Finset.mem_filter, Finset.mem_product,
        Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨hqS, hpS⟩, him ▸ hlo, him ▸ hhi, him.symm, hlt⟩
    · intro p hp
      simp only [Q, orientedPairs, Finset.mem_filter, Finset.mem_product] at hp
      rcases hp with ⟨⟨hpS, hqS⟩, hlo, hhi, him, hlt⟩
      simp only [Finset.mem_filter, P, collisionPairs, Finset.mem_product,
        Prod.fst_swap, Prod.snd_swap]
      refine ⟨⟨⟨hqS, hpS⟩, him ▸ hlo, him ▸ hhi, him.symm, ?_⟩, ?_⟩
      · intro heq
        have hre := congrArg Complex.re heq
        exact (ne_of_lt hlt) hre.symm
      · exact not_lt.mpr (le_of_lt hlt)
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      simp [F, mul_comm]
  have hsplit := Finset.sum_filter_add_sum_filter_not P
    (fun p => p.1.re < p.2.re) F
  calc
    (∑ p ∈ collisionPairs S lo hi, (m p.1 : ℝ) * (m p.2 : ℝ)) =
        ∑ p ∈ P, F p := rfl
    _ = (∑ p ∈ P.filter (fun p => p.1.re < p.2.re), F p) +
        ∑ p ∈ P.filter (fun p => ¬ p.1.re < p.2.re), F p := hsplit.symm
    _ = (∑ p ∈ Q, F p) + ∑ p ∈ Q, F p := by rw [hpos, hneg]
    _ = 2 * ∑ p ∈ orientedPairs S lo hi, (m p.1 : ℝ) * (m p.2 : ℝ) := by
      simp only [Q, F]
      ring

theorem limitMass_eq_collisionPairs
    (S : Finset ℂ) (m : ℂ → ℕ) (lo hi : ℝ) :
    limitMass S m lo hi =
      ∑ p ∈ collisionPairs S lo hi, (m p.1 : ℝ) * (m p.2 : ℝ) := by
  rw [limitMass_eq_orientedPairs, sum_collisionPairs_eq_two_mul_orientedPairs]

/-- Product of the two canonical Poincare--Lelong divisors, pushed through the inverse
shift-pair coordinate map. -/
def shiftPairIntersectionCurrent (f : ℂ → ℂ) (psi : ℂ × ℂ → ℝ) : ℝ :=
  ∑ᶠ p : ℂ × ℂ, (zeroMult f p.1 : ℝ) * (zeroMult f p.2 : ℝ) *
    psi (point p.1 p.2)

/-- Exact zero-cycle expansion of the shift-pair intersection current. -/
theorem shiftPairIntersectionCurrent_zeroCycle_expansion (f : ℂ → ℂ)
    (psi : ℂ × ℂ → ℝ) :
    shiftPairIntersectionCurrent f psi =
      ∑ᶠ p : ℂ × ℂ, (zeroMult f p.1 : ℝ) * (zeroMult f p.2 : ℝ) *
        psi ((p.1 + p.2) / 2, (p.2 - p.1) / 2) := by
  rfl

/-- Test function selecting a bounded center-height window and positive real shifts. -/
def pairCutoffTest (k : Cutoff) (lo hi eps : ℝ) (q : ℂ × ℂ) : ℝ :=
  if lo ≤ q.1.im ∧ q.1.im < hi ∧ 0 < q.2.re then k (q.2.im / eps) else 0

theorem weight_eq_pairCutoffTest (k : Cutoff) (lo hi eps : ℝ) (rho sigma : ℂ) :
    weight k lo hi eps rho sigma = pairCutoffTest k lo hi eps (point rho sigma) := rfl

/-- Source-current thin-slice mass for Xi. -/
def xiSourceThinSliceMass (T : ℝ) (k : Cutoff) (eps : ℝ) : ℝ :=
  2 * shiftPairIntersectionCurrent xi (pairCutoffTest k 0 T eps)

/-- Finite Xi zero set containing every atom that can contribute when `0 < eps ≤ 1`. -/
def xiThinSliceRelevantZeros (T : ℝ) : Finset ℂ :=
  (xi_zeros_closedBall_finite 0 (|T| + 3)).toFinset

theorem mem_xiThinSliceRelevantZeros_of_weight_ne_zero
    {T eps : ℝ} (k : Cutoff) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {rho sigma : ℂ} (hrho : zeroMult xi rho ≠ 0) (hsigma : zeroMult xi sigma ≠ 0)
    (hw : weight k 0 T eps rho sigma ≠ 0) :
    rho ∈ xiThinSliceRelevantZeros T ∧ sigma ∈ xiThinSliceRelevantZeros T := by
  have hzrho : xi rho = 0 := eq_zero_of_zeroMult_ne_zero hrho
  have hzsigma : xi sigma = 0 := eq_zero_of_zeroMult_ne_zero hsigma
  have hrhoRe := xi_zero_re_mem_open_unit hzrho
  have hsigmaRe := xi_zero_re_mem_open_unit hzsigma
  have hc : 0 ≤ (point rho sigma).1.im ∧ (point rho sigma).1.im < T ∧
      0 < (point rho sigma).2.re := by
    by_contra hnc
    apply hw
    simp only [weight, if_neg hnc]
  have hkw : k ((point rho sigma).2.im / eps) ≠ 0 := by
    simpa only [weight, if_pos hc] using hw
  have hratio : |(point rho sigma).2.im / eps| ≤ 1 := by
    apply le_of_not_gt
    intro hgt
    exact hkw (k.eq_zero_of_one_lt_abs _ hgt)
  have huabs : |(point rho sigma).2.im| ≤ eps := by
    rw [abs_div, abs_of_pos heps, div_le_one heps] at hratio
    exact hratio
  have hTpos : 0 < T := lt_of_le_of_lt hc.1 hc.2.1
  have hcabs : |(point rho sigma).1.im| < T := by
    rw [abs_of_nonneg hc.1]
    exact hc.2.1
  have hrhoIm : rho.im = (point rho sigma).1.im - (point rho sigma).2.im := by
    simp [point]
    ring
  have hsigmaIm : sigma.im = (point rho sigma).1.im + (point rho sigma).2.im := by
    simp [point]
    ring
  have hrhoImAbs : |rho.im| < T + 1 := by
    rw [hrhoIm]
    calc
      |(point rho sigma).1.im - (point rho sigma).2.im| ≤
          |(point rho sigma).1.im| + |(point rho sigma).2.im| := abs_sub _ _
      _ < T + 1 := by linarith
  have hsigmaImAbs : |sigma.im| < T + 1 := by
    rw [hsigmaIm]
    calc
      |(point rho sigma).1.im + (point rho sigma).2.im| ≤
          |(point rho sigma).1.im| + |(point rho sigma).2.im| := abs_add_le _ _
      _ < T + 1 := by linarith
  have hrhoReAbs : |rho.re| < 1 := by rw [abs_of_pos hrhoRe.1]; exact hrhoRe.2
  have hsigmaReAbs : |sigma.re| < 1 := by rw [abs_of_pos hsigmaRe.1]; exact hsigmaRe.2
  have hrhoNorm : ‖rho‖ < |T| + 3 := by
    calc
      ‖rho‖ ≤ |rho.re| + |rho.im| := norm_le_abs_re_add_abs_im rho
      _ < |T| + 3 := by rw [abs_of_pos hTpos]; linarith
  have hsigmaNorm : ‖sigma‖ < |T| + 3 := by
    calc
      ‖sigma‖ ≤ |sigma.re| + |sigma.im| := norm_le_abs_re_add_abs_im sigma
      _ < |T| + 3 := by rw [abs_of_pos hTpos]; linarith
  constructor
  · rw [xiThinSliceRelevantZeros, Set.Finite.mem_toFinset]
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hrhoNorm.le, hzrho⟩
  · rw [xiThinSliceRelevantZeros, Set.Finite.mem_toFinset]
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hsigmaNorm.le, hzsigma⟩

/-- Every sufficiently thin global source-current slice is exactly a finite zero-pair mass. -/
theorem xiSourceThinSliceMass_eq_mass_relevant
    {T eps : ℝ} (k : Cutoff) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    xiSourceThinSliceMass T k eps =
      mass (xiThinSliceRelevantZeros T) (fun rho => (analyticOrderAt xi rho).toNat)
        k 0 T eps := by
  have hcurrent : shiftPairIntersectionCurrent xi (pairCutoffTest k 0 T eps) =
      ∑ p ∈ xiThinSliceRelevantZeros T ×ˢ xiThinSliceRelevantZeros T,
        (zeroMult xi p.1 : ℝ) * (zeroMult xi p.2 : ℝ) *
          pairCutoffTest k 0 T eps (point p.1 p.2) := by
    refine finsum_eq_finsetSum_of_support_subset _ ?_
    intro p hp
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hp
    have hp1 : zeroMult xi p.1 ≠ 0 := by exact_mod_cast hp.1.1
    have hp2 : zeroMult xi p.2 ≠ 0 := by exact_mod_cast hp.1.2
    exact Finset.mem_product.mpr
      (mem_xiThinSliceRelevantZeros_of_weight_ne_zero k heps heps1
        hp1 hp2 (by simpa [weight_eq_pairCutoffTest] using hp.2))
  rw [xiSourceThinSliceMass, hcurrent, mass, Finset.sum_product]
  simp only [zeroMult, weight_eq_pairCutoffTest]

theorem mem_xiThinSliceRelevantZeros_of_mem_stripZeros
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ (stripZeros_finite T).toFinset) :
    rho ∈ xiThinSliceRelevantZeros T := by
  have hdata := (stripZeros_finite T).mem_toFinset.mp hrho
  have hreAbs : |rho.re| < 1 := by
    rw [abs_of_pos hdata.1.1]
    exact hdata.1.2.1
  have hTpos : 0 < T := lt_of_le_of_lt hdata.1.2.2.1 hdata.1.2.2.2
  have himAbs : |rho.im| < T := by
    rw [abs_of_nonneg hdata.1.2.2.1]
    exact hdata.1.2.2.2
  have hnorm : ‖rho‖ < |T| + 3 := by
    calc
      ‖rho‖ ≤ |rho.re| + |rho.im| := norm_le_abs_re_add_abs_im rho
      _ < |T| + 3 := by rw [abs_of_pos hTpos]; linarith
  rw [xiThinSliceRelevantZeros, Set.Finite.mem_toFinset]
  exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hnorm.le, hdata.2⟩

theorem collisionPairs_xiRelevant_eq (T : ℝ) :
    collisionPairs (xiThinSliceRelevantZeros T) 0 T = xiHorizontalCollisionPairs T := by
  ext p
  simp only [collisionPairs, xiHorizontalCollisionPairs, Finset.mem_filter,
    Finset.mem_product]
  constructor
  · rintro ⟨⟨hp, hq⟩, hp0, hpT, him, hne⟩
    have hpData := (xi_zeros_closedBall_finite 0 (|T| + 3)).mem_toFinset.mp hp
    have hqData := (xi_zeros_closedBall_finite 0 (|T| + 3)).mem_toFinset.mp hq
    have hpRe := xi_zero_re_mem_open_unit hpData.2
    have hqRe := xi_zero_re_mem_open_unit hqData.2
    have hpStrip : p.1 ∈ (stripZeros_finite T).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨⟨hpRe.1, hpRe.2, hp0, hpT⟩, hpData.2⟩
    have hqStrip : p.2 ∈ (stripZeros_finite T).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨⟨hqRe.1, hqRe.2, him ▸ hp0, him ▸ hpT⟩, hqData.2⟩
    exact ⟨⟨hpStrip, hqStrip⟩, him, hne⟩
  · rintro ⟨⟨hp, hq⟩, him, hne⟩
    have hpData := (stripZeros_finite T).mem_toFinset.mp hp
    exact ⟨⟨mem_xiThinSliceRelevantZeros_of_mem_stripZeros hp,
      mem_xiThinSliceRelevantZeros_of_mem_stripZeros hq⟩,
      hpData.1.2.2.1, hpData.1.2.2.2, him, hne⟩

theorem limitMass_xiRelevant_eq_collisionCharge (T : ℝ) :
    limitMass (xiThinSliceRelevantZeros T)
      (fun rho => (analyticOrderAt xi rho).toNat) 0 T =
        (xiHorizontalCollisionCharge T : ℝ) := by
  rw [limitMass_eq_collisionPairs, collisionPairs_xiRelevant_eq]
  exact_mod_cast (xiHorizontalCollisionCharge_eq_sum_pairs T).symm

/-- The positive-real-shift thin slice of the global Xi source current converges to the exact
horizontal collision charge. -/
theorem tendsto_xiSourceThinSliceMass (T : ℝ) (k : Cutoff) :
    Tendsto (xiSourceThinSliceMass T k) (nhdsWithin 0 (Ioi 0))
      (nhds (xiHorizontalCollisionCharge T : ℝ)) := by
  have hfinite := tendsto_mass (xiThinSliceRelevantZeros T)
    (fun rho => (analyticOrderAt xi rho).toNat) k 0 T
  rw [limitMass_xiRelevant_eq_collisionCharge] at hfinite
  have heq : xiSourceThinSliceMass T k =ᶠ[nhdsWithin 0 (Ioi (0 : ℝ))]
      fun eps => mass (xiThinSliceRelevantZeros T)
        (fun rho => (analyticOrderAt xi rho).toNat) k 0 T eps := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with eps heps
    exact xiSourceThinSliceMass_eq_mass_relevant k heps.1 heps.2.le
  exact hfinite.congr' heq.symm

theorem weight_nonneg (k : Cutoff) (lo hi eps : ℝ) (rho sigma : ℂ) :
    0 ≤ weight k lo hi eps rho sigma := by
  unfold weight
  split
  · exact k.nonneg _
  · exact le_rfl

/-- Every sufficiently thin Xi source-current slice is nonnegative. -/
theorem xiSourceThinSliceMass_nonneg
    {T eps : ℝ} (k : Cutoff) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    0 ≤ xiSourceThinSliceMass T k eps := by
  rw [xiSourceThinSliceMass_eq_mass_relevant k heps heps1]
  unfold mass
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun rho _ => ?_)
  exact Finset.sum_nonneg fun sigma _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (weight_nonneg k 0 T eps rho sigma)

/-- Any two normalized cutoffs converge to the same horizontal-collision mass. -/
theorem xiSourceThinSliceMass_cutoff_independent (T : ℝ) (k₁ k₂ : Cutoff) :
    Tendsto (xiSourceThinSliceMass T k₁) (nhdsWithin 0 (Ioi 0))
        (nhds (xiHorizontalCollisionCharge T : ℝ)) ∧
      Tendsto (xiSourceThinSliceMass T k₂) (nhdsWithin 0 (Ioi 0))
        (nhds (xiHorizontalCollisionCharge T : ℝ)) :=
  ⟨tendsto_xiSourceThinSliceMass T k₁, tendsto_xiSourceThinSliceMass T k₂⟩

/-- Xi itself satisfies the canonical Poincare--Lelong identity, with no factorization premise. -/
theorem xi_isPoincareLelongOfSmooth : IsPoincareLelongOfSmooth xi := by
  apply entire_isPoincareLelongOfSmooth (f := xi)
    (fun z => (xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ)
      z (Set.mem_univ z))
    (z₀ := (2 : ℂ))
  exact xi_ne_zero_of_one_le_re (by norm_num)

/-- Reduced diagonal intersection mass after deleting one identity copy at each zero. -/
def xiDiagonalReducedIntersectionCharge (T : ℝ) : ℕ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset,
    (analyticOrderAt xi rho).toNat * ((analyticOrderAt xi rho).toNat - 1)

/-- Total reduced real-shift incidence: off-diagonal plus reduced diagonal. -/
def xiReducedRealShiftIncidenceCharge (T : ℝ) : ℕ :=
  xiHorizontalCollisionCharge T + xiDiagonalReducedIntersectionCharge T

theorem xiStripWindowLocalSquareSum_eq_total_add_diagonalReduced (T : ℝ) :
    xiStripWindowLocalSquareSum T =
      xiStripWindowTotalOrder T + xiDiagonalReducedIntersectionCharge T := by
  rw [xiStripWindowLocalSquareSum, xiStripWindowTotalOrder,
    xiDiagonalReducedIntersectionCharge, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _
  let n := (analyticOrderAt xi rho).toNat
  change n ^ (2 : ℕ) = n + n * (n - 1)
  cases n with
  | zero => simp
  | succ n => simp [pow_two, Nat.succ_mul, Nat.mul_succ]; ring

/-- Exact conservation law `O_I + M_I = C_I - N_I`. -/
theorem xiReducedRealShiftIncidenceCharge_eq_horizontalSquare_sub_total (T : ℝ) :
    xiReducedRealShiftIncidenceCharge T =
      xiStripWindowHorizontalSquareSum T - xiStripWindowTotalOrder T := by
  have hh := xiStripWindowHorizontalSquareSum_eq_localSquare_add_collisionCharge T
  have hl := xiStripWindowLocalSquareSum_eq_total_add_diagonalReduced T
  unfold xiReducedRealShiftIncidenceCharge
  omega

/-- Colength retained after reducing the common factor of `X^m` and `X^n`. -/
def quotientCancellationMultiplicity (m n : ℕ) : ℕ :=
  Module.finrank ℂ
    (Polynomial ℂ ⧸ Ideal.span {(Polynomial.X : Polynomial ℂ) ^ m,
      (Polynomial.X : Polynomial ℂ) ^ n})

theorem quotientCancellationMultiplicity_eq_min (m n : ℕ) :
    quotientCancellationMultiplicity m n = min m n := by
  simpa [quotientCancellationMultiplicity] using
    (finrank_quotient_span_pair_X_pow m n)

/-- Reduced quotient cancellation retains `min(m,n)`, not intersection product `m*n`. -/
theorem reducedQuotient_deletes_productMultiplicity :
    (∀ m n : ℕ, quotientCancellationMultiplicity m n = min m n) ∧
      (∀ m n : ℕ, localIntersectionMultiplicity m n = m * n) ∧
      quotientCancellationMultiplicity 2 2 ≠ localIntersectionMultiplicity 2 2 := by
  refine ⟨quotientCancellationMultiplicity_eq_min,
    localIntersectionMultiplicity_eq_mul, ?_⟩
  norm_num [quotientCancellationMultiplicity_eq_min,
    localIntersectionMultiplicity_eq_mul]

/-- Closed capstone for Euler shift-pair incidence: source Poincare--Lelong current, exact
cutoff-independent thin-slice charge, off-diagonal census, line-support rigidity, diagonal
conservation, local product multiplicity, and quotient-cancellation mismatch. -/
theorem eulerShiftPairIncidenceResultant_unconditional :
    IsPoincareLelongOfSmooth xi ∧
      (∀ T : ℝ, ∀ k : Cutoff,
        Tendsto (xiSourceThinSliceMass T k) (nhdsWithin 0 (Ioi 0))
          (nhds (xiHorizontalCollisionCharge T : ℝ))) ∧
      (∀ T : ℝ, xiHorizontalCollisionCharge T =
        xiStripWindowHorizontalSquareSum T - xiStripWindowLocalSquareSum T) ∧
      (∀ T : ℝ, xiHorizontalCollisionCharge T = 0 ↔
        ∀ rho ∈ xiStripWindowDivisorSupportFinset T, (rho : ℂ).re = 1 / 2) ∧
      (∀ T : ℝ, xiReducedRealShiftIncidenceCharge T =
        xiStripWindowHorizontalSquareSum T - xiStripWindowTotalOrder T) ∧
      (∀ m n : ℕ, localIntersectionMultiplicity m n = m * n) ∧
      (∀ m n : ℕ, quotientCancellationMultiplicity m n = min m n) ∧
      quotientCancellationMultiplicity 2 2 ≠ localIntersectionMultiplicity 2 2 := by
  refine ⟨xi_isPoincareLelongOfSmooth, tendsto_xiSourceThinSliceMass,
    xiHorizontalCollisionCharge_eq_horizontalSquare_sub_localSquare,
    xiHorizontalCollisionCharge_eq_zero_iff_stripSupport_onLine,
    xiReducedRealShiftIncidenceCharge_eq_horizontalSquare_sub_total,
    localIntersectionMultiplicity_eq_mul, quotientCancellationMultiplicity_eq_min, ?_⟩
  exact reducedQuotient_deletes_productMultiplicity.2.2

end
end EulerShiftPairIncidenceCurrent
end RHTower
