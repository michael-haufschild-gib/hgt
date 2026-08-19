import GaloisForLFunctions.HTGeometry.HolderShiftElimination
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialVandermonde

/-!
# The unit shift drops the degree at infinity by exactly one

For a rational function `f` over `ℂ`, the difference `f(X+1) - f(X)` has degree at infinity exactly
`deg f - 1` whenever `deg f ≠ 0`, and at most `-2` when `deg f = 0` and `f` is not constant.  The
proof is the polynomial statement that the finite difference `p(X+1) - p(X)` has degree
`deg p - 1` with leading coefficient `deg p` times that of `p`, applied to the numerator and the
denominator of a reduced presentation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-! ### The finite difference of a polynomial -/

/-- The unit finite difference `p(X+1) - p(X)`. -/
def shiftDelta (p : ℂ[X]) : ℂ[X] := p.comp (X + C 1) - p

theorem degree_shiftDelta_lt {p : ℂ[X]} (hp : p ≠ 0) : (shiftDelta p).degree < p.degree := by
  have hne : p.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hp
  have hdeg : (p.comp (X + C 1)).degree = p.degree := by
    rw [degree_eq_natDegree hne, degree_eq_natDegree hp, natDegree_comp_X_add_one]
  have h := degree_sub_lt hdeg hne (leadingCoeff_comp_X_add_one' p)
  rwa [hdeg] at h

theorem shiftDelta_eq_zero_of_natDegree_zero {p : ℂ[X]} (h : p.natDegree = 0) :
    shiftDelta p = 0 := by
  obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp h
  simp [shiftDelta]

theorem coeff_shiftDelta_pred {p : ℂ[X]} (hd : 1 ≤ p.natDegree) :
    (shiftDelta p).coeff (p.natDegree - 1) = (p.natDegree : ℂ) * p.leadingCoeff := by
  have hnd : (hasseDeriv (p.natDegree - 1) p).natDegree = p.natDegree - (p.natDegree - 1) :=
    natDegree_hasseDeriv p _
  have hlt : (hasseDeriv (p.natDegree - 1) p).natDegree < 2 := by omega
  have h1 : (p.comp (X + C 1)).coeff (p.natDegree - 1)
      = eval 1 (hasseDeriv (p.natDegree - 1) p) := by
    rw [← taylor_apply, taylor_coeff]
  have h2 : eval (1 : ℂ) (hasseDeriv (p.natDegree - 1) p)
      = ∑ i ∈ Finset.range 2, (hasseDeriv (p.natDegree - 1) p).coeff i * (1 : ℂ) ^ i :=
    eval_eq_sum_range' hlt 1
  have hc0 : (hasseDeriv (p.natDegree - 1) p).coeff 0 = p.coeff (p.natDegree - 1) := by
    rw [hasseDeriv_coeff]
    simp
  have hc1 : (hasseDeriv (p.natDegree - 1) p).coeff 1 = (p.natDegree : ℂ) * p.leadingCoeff := by
    rw [hasseDeriv_coeff]
    have he : 1 + (p.natDegree - 1) = p.natDegree := by omega
    rw [he]
    have hch : p.natDegree.choose (p.natDegree - 1) = p.natDegree := by
      rw [Nat.choose_symm hd, Nat.choose_one_right]
    rw [hch, Polynomial.coeff_natDegree]
  have hsum : eval (1 : ℂ) (hasseDeriv (p.natDegree - 1) p)
      = p.coeff (p.natDegree - 1) + (p.natDegree : ℂ) * p.leadingCoeff := by
    rw [h2]
    simp [Finset.sum_range_succ, hc0, hc1]
  rw [shiftDelta, Polynomial.coeff_sub, h1, hsum]
  ring

theorem shiftDelta_ne_zero {p : ℂ[X]} (hd : 1 ≤ p.natDegree) : shiftDelta p ≠ 0 := by
  intro h
  have hc := coeff_shiftDelta_pred hd
  rw [h, Polynomial.coeff_zero] at hc
  have hlead : p.leadingCoeff ≠ 0 := by
    refine Polynomial.leadingCoeff_ne_zero.mpr ?_
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hd
    exact absurd hd (by omega)
  have hn : (p.natDegree : ℂ) ≠ 0 := by
    simpa using (by omega : p.natDegree ≠ 0)
  exact (mul_ne_zero hn hlead) hc.symm

theorem natDegree_shiftDelta {p : ℂ[X]} (hd : 1 ≤ p.natDegree) :
    (shiftDelta p).natDegree = p.natDegree - 1 := by
  have hp : p ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hd
    exact absurd hd (by omega)
  have hne := shiftDelta_ne_zero hd
  have hlt : (shiftDelta p).natDegree < p.natDegree :=
    Polynomial.natDegree_lt_natDegree hne (degree_shiftDelta_lt hp)
  have hge : p.natDegree - 1 ≤ (shiftDelta p).natDegree := by
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [coeff_shiftDelta_pred hd]
    have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hn : (p.natDegree : ℂ) ≠ 0 := by
      simpa using (by omega : p.natDegree ≠ 0)
    exact mul_ne_zero hn hlead
  omega

theorem leadingCoeff_shiftDelta {p : ℂ[X]} (hd : 1 ≤ p.natDegree) :
    (shiftDelta p).leadingCoeff = (p.natDegree : ℂ) * p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_shiftDelta hd, coeff_shiftDelta_pred hd]

/-! ### The degree at infinity of the shift difference -/

theorem algebraMap_poly_ne_zero {p : ℂ[X]} (hp : p ≠ 0) :
    algebraMap ℂ[X] (RatFunc ℂ) p ≠ 0 :=
  fun h => hp (RatFunc.algebraMap_injective ℂ (by rw [h, map_zero]))

theorem intDegree_algebraMap_div {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q).intDegree
      = (p.natDegree : ℤ) - (q.natDegree : ℤ) := by
  rw [RatFunc.intDegree_div (algebraMap_poly_ne_zero hp) (algebraMap_poly_ne_zero hq),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]

/-- The numerator of the shift difference in the reduced presentation. -/
def shiftDiffNum (f : RatFunc ℂ) : ℂ[X] :=
  shiftDelta f.num * f.denom - f.num * shiftDelta f.denom

theorem ratShift_mul_denom_comp (f : RatFunc ℂ) :
    ratShift f * algebraMap ℂ[X] (RatFunc ℂ) (f.denom.comp (X + C 1))
      = algebraMap ℂ[X] (RatFunc ℂ) (f.num.comp (X + C 1)) := by
  have ha1 : algebraMap ℂ[X] (RatFunc ℂ) f.denom ≠ 0 :=
    algebraMap_poly_ne_zero f.denom_ne_zero
  have h2 := div_mul_cancel₀ (algebraMap ℂ[X] (RatFunc ℂ) f.num) ha1
  rw [RatFunc.num_div_denom] at h2
  have h3 := congrArg ratShift h2
  rw [map_mul, ratShift_algebraMap, ratShift_algebraMap] at h3
  exact h3

theorem mul_denom_eq_num (f : RatFunc ℂ) :
    f * algebraMap ℂ[X] (RatFunc ℂ) f.denom = algebraMap ℂ[X] (RatFunc ℂ) f.num := by
  have ha1 : algebraMap ℂ[X] (RatFunc ℂ) f.denom ≠ 0 :=
    algebraMap_poly_ne_zero f.denom_ne_zero
  have h2 := div_mul_cancel₀ (algebraMap ℂ[X] (RatFunc ℂ) f.num) ha1
  rwa [RatFunc.num_div_denom] at h2

theorem ratShift_sub_self_eq (f : RatFunc ℂ) :
    ratShift f - f = algebraMap ℂ[X] (RatFunc ℂ) (shiftDiffNum f)
      / algebraMap ℂ[X] (RatFunc ℂ) (f.denom.comp (X + C 1) * f.denom) := by
  have hden : f.denom ≠ 0 := f.denom_ne_zero
  have hdenS : f.denom.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hden
  have ha1 : algebraMap ℂ[X] (RatFunc ℂ) f.denom ≠ 0 := algebraMap_poly_ne_zero hden
  have ha2 : algebraMap ℂ[X] (RatFunc ℂ) (f.denom.comp (X + C 1)) ≠ 0 :=
    algebraMap_poly_ne_zero hdenS
  have h1 := ratShift_mul_denom_comp f
  have h2 := mul_denom_eq_num f
  have hN : shiftDiffNum f
      = f.num.comp (X + C 1) * f.denom - f.num * f.denom.comp (X + C 1) := by
    rw [shiftDiffNum, shiftDelta, shiftDelta]; ring
  rw [eq_div_iff (by rw [map_mul]; exact mul_ne_zero ha2 ha1), hN, map_sub, map_mul, map_mul,
    map_mul, ← h1, ← h2]
  ring

theorem shiftDiffNum_spec {f : RatFunc ℂ} (hf : f ≠ 0)
    (hne : f.num.natDegree ≠ f.denom.natDegree) :
    shiftDiffNum f ≠ 0 ∧
      (shiftDiffNum f).natDegree = f.num.natDegree + f.denom.natDegree - 1 := by
  classical
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := f.denom_ne_zero
  rcases Nat.eq_zero_or_pos f.num.natDegree with hm0 | hm1
  · have hn1 : 1 ≤ f.denom.natDegree := by omega
    have hdp : shiftDelta f.num = 0 := shiftDelta_eq_zero_of_natDegree_zero hm0
    have hdq : shiftDelta f.denom ≠ 0 := shiftDelta_ne_zero hn1
    refine ⟨?_, ?_⟩
    · rw [shiftDiffNum, hdp, zero_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero hp hdq
    · rw [shiftDiffNum, hdp, zero_mul, zero_sub, Polynomial.natDegree_neg,
        Polynomial.natDegree_mul hp hdq, natDegree_shiftDelta hn1, hm0]
      omega
  · rcases Nat.eq_zero_or_pos f.denom.natDegree with hn0 | hn1
    · have hdq : shiftDelta f.denom = 0 := shiftDelta_eq_zero_of_natDegree_zero hn0
      have hdp : shiftDelta f.num ≠ 0 := shiftDelta_ne_zero hm1
      refine ⟨?_, ?_⟩
      · rw [shiftDiffNum, hdq, mul_zero, sub_zero]
        exact mul_ne_zero hdp hq
      · rw [shiftDiffNum, hdq, mul_zero, sub_zero, Polynomial.natDegree_mul hdp hq,
          natDegree_shiftDelta hm1, hn0]
        omega
    · have hdp : shiftDelta f.num ≠ 0 := shiftDelta_ne_zero hm1
      have hdq : shiftDelta f.denom ≠ 0 := shiftDelta_ne_zero hn1
      have hA : (shiftDelta f.num * f.denom).natDegree
          = f.num.natDegree + f.denom.natDegree - 1 := by
        rw [Polynomial.natDegree_mul hdp hq, natDegree_shiftDelta hm1]
        omega
      have hB : (f.num * shiftDelta f.denom).natDegree
          = f.num.natDegree + f.denom.natDegree - 1 := by
        rw [Polynomial.natDegree_mul hp hdq, natDegree_shiftDelta hn1]
        omega
      have hcA : (shiftDelta f.num * f.denom).coeff (f.num.natDegree + f.denom.natDegree - 1)
          = (f.num.natDegree : ℂ) * f.num.leadingCoeff * f.denom.leadingCoeff := by
        rw [← hA, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_mul,
          leadingCoeff_shiftDelta hm1]
      have hcB : (f.num * shiftDelta f.denom).coeff (f.num.natDegree + f.denom.natDegree - 1)
          = f.num.leadingCoeff * ((f.denom.natDegree : ℂ) * f.denom.leadingCoeff) := by
        rw [← hB, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_mul,
          leadingCoeff_shiftDelta hn1]
      have hlp : f.num.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
      have hlq : f.denom.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
      have hcast : (f.num.natDegree : ℂ) - (f.denom.natDegree : ℂ) ≠ 0 := by
        intro h
        exact hne (Nat.cast_injective (sub_eq_zero.mp h))
      have hcoeff : (shiftDiffNum f).coeff (f.num.natDegree + f.denom.natDegree - 1)
          = ((f.num.natDegree : ℂ) - (f.denom.natDegree : ℂ))
              * (f.num.leadingCoeff * f.denom.leadingCoeff) := by
        rw [shiftDiffNum, Polynomial.coeff_sub, hcA, hcB]
        ring
      have hne0 : (shiftDiffNum f).coeff (f.num.natDegree + f.denom.natDegree - 1) ≠ 0 := by
        rw [hcoeff]
        exact mul_ne_zero hcast (mul_ne_zero hlp hlq)
      refine ⟨fun h => hne0 (by rw [h, Polynomial.coeff_zero]), ?_⟩
      have hge : f.num.natDegree + f.denom.natDegree - 1 ≤ (shiftDiffNum f).natDegree :=
        Polynomial.le_natDegree_of_ne_zero hne0
      have hle : (shiftDiffNum f).natDegree ≤ f.num.natDegree + f.denom.natDegree - 1 := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        rw [hA, hB]
        exact le_of_eq (max_self _)
      omega

/-- **The shift difference drops the degree at infinity by exactly one**, for a rational function
of nonzero degree. -/
theorem intDegree_ratShift_sub {f : RatFunc ℂ} (hf : f ≠ 0) (hd : f.intDegree ≠ 0) :
    ratShift f - f ≠ 0 ∧ (ratShift f - f).intDegree = f.intDegree - 1 := by
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := f.denom_ne_zero
  have hqS : f.denom.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hq
  have hid : f.intDegree = (f.num.natDegree : ℤ) - (f.denom.natDegree : ℤ) := rfl
  have hne : f.num.natDegree ≠ f.denom.natDegree := by
    intro h
    exact hd (by rw [hid, h, sub_self])
  obtain ⟨hN, hNdeg⟩ := shiftDiffNum_spec hf hne
  have hD : (f.denom.comp (X + C 1) * f.denom).natDegree = 2 * f.denom.natDegree := by
    rw [Polynomial.natDegree_mul hqS hq, natDegree_comp_X_add_one]
    omega
  have hDne : f.denom.comp (X + C 1) * f.denom ≠ 0 := mul_ne_zero hqS hq
  constructor
  · rw [ratShift_sub_self_eq f]
    exact div_ne_zero (algebraMap_poly_ne_zero hN) (algebraMap_poly_ne_zero hDne)
  · rw [ratShift_sub_self_eq f, intDegree_algebraMap_div hN hDne, hNdeg, hD, RatFunc.intDegree]
    have h1 : 1 ≤ f.num.natDegree + f.denom.natDegree := by omega
    omega

/-- A shift-invariant rational function is constant, so a nonconstant rational function of degree
zero at infinity has shift difference of degree at most `-2`. -/
theorem intDegree_ratShift_sub_le_of_intDegree_zero {f : RatFunc ℂ}
    (h0 : f.intDegree = 0) (hnc : ratShift f ≠ f) :
    ratShift f - f ≠ 0 ∧ (ratShift f - f).intDegree ≤ -2 := by
  have hf : f ≠ 0 := by
    intro h
    exact hnc (by rw [h, map_zero])
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := f.denom_ne_zero
  have hid : f.intDegree = (f.num.natDegree : ℤ) - (f.denom.natDegree : ℤ) := rfl
  have hmn : f.num.natDegree = f.denom.natDegree := by
    have h1 := h0
    rw [hid, sub_eq_zero] at h1
    exact_mod_cast h1
  set c : ℂ := f.num.leadingCoeff / f.denom.leadingCoeff with hc
  have hlp : f.num.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hlq : f.denom.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hcne : c ≠ 0 := div_ne_zero hlp hlq
  set g : RatFunc ℂ := f - algebraMap ℂ (RatFunc ℂ) c with hg
  have hshiftg : ratShift g - g = ratShift f - f := by
    rw [hg, map_sub, ratShift_const]
    ring
  have hgne : g ≠ 0 := by
    intro h
    have hz : f - algebraMap ℂ (RatFunc ℂ) c = 0 := by rw [← hg]; exact h
    have hfc : f = algebraMap ℂ (RatFunc ℂ) c := sub_eq_zero.mp hz
    exact hnc (by rw [hfc, ratShift_const])
  have hnum : f.num - Polynomial.C c * f.denom ≠ 0 := by
    intro h
    have : f = algebraMap ℂ (RatFunc ℂ) c := by
      have hd : algebraMap ℂ[X] (RatFunc ℂ) f.num
          = algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c * f.denom) := by
        rw [← sub_eq_zero, ← map_sub, h, map_zero]
      have hfd : f = algebraMap ℂ[X] (RatFunc ℂ) f.num
          / algebraMap ℂ[X] (RatFunc ℂ) f.denom := (RatFunc.num_div_denom f).symm
      rw [hfd, hd, map_mul, algebraMap_polyC,
        mul_div_assoc, div_self (algebraMap_poly_ne_zero hq), mul_one]
    exact hnc (by rw [this, ratShift_const])
  have hdlt : (f.num - Polynomial.C c * f.denom).natDegree < f.denom.natDegree := by
    have hdeg : f.num.degree = (Polynomial.C c * f.denom).degree := by
      rw [Polynomial.degree_mul, Polynomial.degree_C hcne, zero_add,
        Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq, hmn]
    have hlead : f.num.leadingCoeff = (Polynomial.C c * f.denom).leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc]
      field_simp
    have := Polynomial.degree_sub_lt hdeg hp hlead
    have h2 : (f.num - Polynomial.C c * f.denom).natDegree < f.num.natDegree :=
      Polynomial.natDegree_lt_natDegree hnum this
    omega
  have hgdeg : g.intDegree < 0 := by
    have ha1 : algebraMap ℂ[X] (RatFunc ℂ) f.denom ≠ 0 := algebraMap_poly_ne_zero hq
    have hgeq : g = algebraMap ℂ[X] (RatFunc ℂ) (f.num - Polynomial.C c * f.denom)
        / algebraMap ℂ[X] (RatFunc ℂ) f.denom := by
      rw [eq_div_iff ha1, hg, sub_mul, mul_denom_eq_num f, map_sub, map_mul, algebraMap_polyC]
    rw [hgeq, intDegree_algebraMap_div hnum hq]
    omega
  obtain ⟨hgs, hgsdeg⟩ := intDegree_ratShift_sub hgne (by omega)
  refine ⟨by rw [← hshiftg]; exact hgs, ?_⟩
  rw [← hshiftg, hgsdeg]
  omega

end

end GaloisForLFunctions.HTGeometry
