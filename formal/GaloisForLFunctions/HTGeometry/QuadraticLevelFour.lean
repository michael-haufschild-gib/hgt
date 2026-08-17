import GaloisForLFunctions.HTGeometry.JetLevelFourDescent
import GaloisForLFunctions.HTGeometry.QuadraticLevelThree

/-!
# No normalizing shift at jet level four for the two quadratic maps

For both postcritically finite quadratics the third and fourth derivatives vanish and the second is
the constant `2`, so the two rational alternatives of the level-four descent read

`α(R)·(R')² = R'·α + c`  with `c` a nonzero constant, and
`α(R)·(R')³ = R'·α + 3·(R'')²/R'` ,

the first impossible because a nonzero constant inhomogeneous term cannot survive the ramification at
the critical point, the second because `3·(R'')²/R'` has a simple pole exactly where `R'` vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ## `z ↦ z² + 1` -/

theorem quadOne_fixed_isConst_of_order_three {g : JetField ℂ Unit}
    (hg : ∀ j : ℕ, 3 < j → JetField.pd ((), j) g = 0)
    (hgfix : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
      quadOne_substitutionDeriv_ne_zero g = g) :
    ∃ e : ℂ, g = algebraMap ℂ (JetField ℂ Unit) e := by
  refine fixed_isConst_of_order_le _ quadOne_substitutionDeriv_ne_zero
    (fun w hw hwfix => quadOne_fixed_of_order_one hw hwfix) 3 (fun M hM hM3 hsh => ?_) g hg hgfix
  interval_cases M
  · exact quadOne_not_hasNormalizingShift_two hsh
  · exact quadOne_not_hasNormalizingShift_three hsh

theorem quadOne_not_hasNormalizingShift_four :
    ¬ HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_substitutionDeriv_ne_zero (show (1 : ℕ) ≤ 4 by omega) := by
  intro h
  set R₀ : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne with hR₀def
  have hd1 : ratFuncDeriv R₀ = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)
    := ratFuncDeriv_algebraMap quadOne
  have hd2 : ratFuncDeriv (ratFuncDeriv R₀)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) := by
    rw [hd1, ratFuncDeriv_algebraMap, derivative_quadOne, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, mul_one, zero_add]
  have hd3 : ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R₀)) = 0 := by
    rw [hd2, ratFuncDeriv_algebraMap, Polynomial.derivative_C, map_zero]
  have hb : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero
      (derivative_ne_zero_of_natDegree_ne_zero quadOne_natDegree_ne_zero)
  have hAm2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ≠ 0 := by
    refine algebraMap_ne_zero_of_ne_zero ?_
    intro hh
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 0) hh
    simp at hc
  have hmultC : ∀ z : ℂ, Polynomial.rootMultiplicity z (Polynomial.C (2 : ℂ)) = 0 := by
    intro z
    refine Polynomial.rootMultiplicity_eq_zero ?_
    rw [Polynomial.IsRoot.def, Polynomial.eval_C]
    norm_num
  have hbunit : ∀ p : ℂ, p ≠ 0 →
      ratOrder (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)) p = 0 := by
    intro p hp
    rw [ratOrder_algebraMap, Polynomial.rootMultiplicity_eq_zero ?_, Nat.cast_zero]
    rw [Polynomial.IsRoot.def, derivative_quadOne_eval]
    exact mul_ne_zero (by norm_num) hp
  have hbcrit : ratOrder (algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.derivative quadOne)) 0 = 1 := by
    rw [ratOrder_algebraMap, rootMultiplicity_derivative_quadOne, Nat.cast_one]
  rcases level_four_alternatives _ quadOne_substitutionDeriv_ne_zero
      quadOne_pd_substitutionDeriv_ne_zero
      (fun g hg hgfix => quadOne_fixed_isConst_of_order_three hg hgfix) h with
    h3 | h2 | ⟨γ, α, hγ, hα⟩ | ⟨α, hα⟩
  · exact quadOne_not_hasNormalizingShift_three h3
  · exact quadOne_not_hasNormalizingShift_two h2
  · -- a scaled affine connection
    rw [hd2, hd1] at hα
    set c : RatFunc ℂ := RatFunc.C (-2 * γ) with hcdef
    have hcval : -(RatFunc.C γ * algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2)) = c := by
      rw [hcdef, RatFunc.algebraMap_C, ← map_mul, ← map_neg]
      congr 1
      ring
    have hIAT : IsAffineTransport quadOne quadOne_not_isConst 2
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)) c α := by
      show ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
          quadOne_not_isConst α
          * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)) ^ (2 : ℤ)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne) * α + c
      rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← hcval]
      linear_combination hα
    have hγ2 : (-2 * γ : ℂ) ≠ 0 := by
      intro hh
      exact hγ (by linear_combination -hh / 2)
    have hc0 : c ≠ 0 := by
      rw [hcdef]
      intro hh
      refine hγ2 ((RatFunc.C_injective (K := ℂ)) ?_)
      rw [hh, map_zero]
    have ha0 : α ≠ 0 := by
      intro hh
      have hz : ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
          quadOne_not_isConst α
          * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)) ^ (2 : ℤ)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne) * α + c := hIAT
      rw [hh, map_zero, zero_mul, mul_zero, zero_add] at hz
      exact hc0 hz.symm
    exact quadOne_no_affineTransport_of_const hγ2 ha0 (by omega) hIAT
  · -- the transport of exponent three
    rw [hd3, hd2, hd1] at hα
    set b : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)
      with hbdef
    set c : RatFunc ℂ := RatFunc.C (3 : ℂ)
        * algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ^ 2 / b with hcdef
    have hC3 : (RatFunc.C (3 : ℂ) : RatFunc ℂ) ≠ 0 := by
      intro hh
      have h3 : (3 : ℂ) = 0 := (RatFunc.C_injective (K := ℂ)) (by simp [hh])
      norm_num at h3
    have hc0 : c ≠ 0 := by
      rw [hcdef]
      exact div_ne_zero (mul_ne_zero hC3 (pow_ne_zero 2 hAm2)) hb
    have hcord : ∀ p : ℂ, ratOrder c p
        = -(Polynomial.rootMultiplicity p (Polynomial.derivative quadOne) : ℤ) := by
      intro p
      rw [hcdef, div_eq_mul_inv,
        ratOrder_mul (mul_ne_zero hC3 (pow_ne_zero 2 hAm2)) (inv_ne_zero hb),
        ratOrder_mul hC3 (pow_ne_zero 2 hAm2), ratOrder_C, ratOrder_pow hAm2,
        ratOrder_inv hb, ratOrder_algebraMap, ratOrder_algebraMap, hmultC p]
      norm_num
    have hIAT : IsAffineTransport quadOne quadOne_not_isConst 3 b c α := by
      show ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
          quadOne_not_isConst α
          * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)) ^ (3 : ℤ)
        = b * α + c
      rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hcdef]
      linear_combination hα
    have ha0 : α ≠ 0 := by
      intro hh
      have hz : ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
          quadOne_not_isConst α
          * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)) ^ (3 : ℤ)
        = b * α + c := hIAT
      rw [hh, map_zero, zero_mul, mul_zero, zero_add] at hz
      exact hc0 hz.symm
    refine quadOne_no_affineTransport_of_critical_order ha0 hb hc0 hIAT hbunit (fun p hp => ?_)
      ?_ ?_
    · rw [hcord p, Polynomial.rootMultiplicity_eq_zero ?_]
      · norm_num
      rw [Polynomial.IsRoot.def, derivative_quadOne_eval]
      exact mul_ne_zero (by norm_num) hp
    · rw [hcord, rootMultiplicity_derivative_quadOne, hbcrit, Nat.cast_one]
      norm_num
    · rw [hcord, rootMultiplicity_derivative_quadOne, Nat.cast_one]
      norm_num

/-! ## `z ↦ (z − 1)²` -/

theorem quadTwo_fixed_isConst_of_order_three {g : JetField ℂ Unit}
    (hg : ∀ j : ℕ, 3 < j → JetField.pd ((), j) g = 0)
    (hgfix : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
      quadTwo_substitutionDeriv_ne_zero g = g) :
    ∃ e : ℂ, g = algebraMap ℂ (JetField ℂ Unit) e := by
  refine fixed_isConst_of_order_le _ quadTwo_substitutionDeriv_ne_zero
    (fun w hw hwfix => quadTwo_fixed_of_order_one hw hwfix) 3 (fun M hM hM3 hsh => ?_) g hg hgfix
  interval_cases M
  · exact quadTwo_not_hasNormalizingShift_two hsh
  · exact quadTwo_not_hasNormalizingShift_three hsh

theorem quadTwo_not_hasNormalizingShift_four :
    ¬ HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
        quadTwo_substitutionDeriv_ne_zero (show (1 : ℕ) ≤ 4 by omega) := by
  intro h
  set R₀ : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo with hR₀def
  have hd1 : ratFuncDeriv R₀ = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)
    := ratFuncDeriv_algebraMap quadTwo
  have hd2 : ratFuncDeriv (ratFuncDeriv R₀)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) := by
    rw [hd1, ratFuncDeriv_algebraMap, derivative_quadTwo, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, zero_mul, mul_one, zero_add]
  have hd3 : ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R₀)) = 0 := by
    rw [hd2, ratFuncDeriv_algebraMap, Polynomial.derivative_C, map_zero]
  have hb : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero
      (derivative_ne_zero_of_natDegree_ne_zero quadTwo_natDegree_ne_zero)
  have hAm2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ≠ 0 := by
    refine algebraMap_ne_zero_of_ne_zero ?_
    intro hh
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 0) hh
    simp at hc
  have hmultC : ∀ z : ℂ, Polynomial.rootMultiplicity z (Polynomial.C (2 : ℂ)) = 0 := by
    intro z
    refine Polynomial.rootMultiplicity_eq_zero ?_
    rw [Polynomial.IsRoot.def, Polynomial.eval_C]
    norm_num
  have hbunit : ∀ p : ℂ, p ≠ 1 →
      ratOrder (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)) p = 0 := by
    intro p hp
    rw [ratOrder_algebraMap, Polynomial.rootMultiplicity_eq_zero ?_, Nat.cast_zero]
    rw [Polynomial.IsRoot.def, derivative_quadTwo_eval]
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hp)
  have hbcrit : ratOrder (algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.derivative quadTwo)) 1 = 1 := by
    rw [ratOrder_algebraMap, rootMultiplicity_derivative_quadTwo, Nat.cast_one]
  rcases level_four_alternatives _ quadTwo_substitutionDeriv_ne_zero
      quadTwo_pd_substitutionDeriv_ne_zero
      (fun g hg hgfix => quadTwo_fixed_isConst_of_order_three hg hgfix) h with
    h3 | h2 | ⟨γ, α, hγ, hα⟩ | ⟨α, hα⟩
  · exact quadTwo_not_hasNormalizingShift_three h3
  · exact quadTwo_not_hasNormalizingShift_two h2
  · -- a scaled affine connection
    rw [hd2, hd1] at hα
    set c : RatFunc ℂ := RatFunc.C (-2 * γ) with hcdef
    have hcval : -(RatFunc.C γ * algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2)) = c := by
      rw [hcdef, RatFunc.algebraMap_C, ← map_mul, ← map_neg]
      congr 1
      ring
    have hIAT : IsAffineTransport quadTwo quadTwo_not_isConst 2
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)) c α := by
      show ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
          quadTwo_not_isConst α
          * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)) ^ (2 : ℤ)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo) * α + c
      rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← hcval]
      linear_combination hα
    have hγ2 : (-2 * γ : ℂ) ≠ 0 := by
      intro hh
      exact hγ (by linear_combination -hh / 2)
    have hc0 : c ≠ 0 := by
      rw [hcdef]
      intro hh
      refine hγ2 ((RatFunc.C_injective (K := ℂ)) ?_)
      rw [hh, map_zero]
    have ha0 : α ≠ 0 := by
      intro hh
      have hz : ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
          quadTwo_not_isConst α
          * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)) ^ (2 : ℤ)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo) * α + c := hIAT
      rw [hh, map_zero, zero_mul, mul_zero, zero_add] at hz
      exact hc0 hz.symm
    exact quadTwo_no_affineTransport_of_const hγ2 ha0 (by omega) hIAT
  · -- the transport of exponent three
    rw [hd3, hd2, hd1] at hα
    set b : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)
      with hbdef
    set c : RatFunc ℂ := RatFunc.C (3 : ℂ)
        * algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ^ 2 / b with hcdef
    have hC3 : (RatFunc.C (3 : ℂ) : RatFunc ℂ) ≠ 0 := by
      intro hh
      have h3 : (3 : ℂ) = 0 := (RatFunc.C_injective (K := ℂ)) (by simp [hh])
      norm_num at h3
    have hc0 : c ≠ 0 := by
      rw [hcdef]
      exact div_ne_zero (mul_ne_zero hC3 (pow_ne_zero 2 hAm2)) hb
    have hcord : ∀ p : ℂ, ratOrder c p
        = -(Polynomial.rootMultiplicity p (Polynomial.derivative quadTwo) : ℤ) := by
      intro p
      rw [hcdef, div_eq_mul_inv,
        ratOrder_mul (mul_ne_zero hC3 (pow_ne_zero 2 hAm2)) (inv_ne_zero hb),
        ratOrder_mul hC3 (pow_ne_zero 2 hAm2), ratOrder_C, ratOrder_pow hAm2,
        ratOrder_inv hb, ratOrder_algebraMap, ratOrder_algebraMap, hmultC p]
      norm_num
    have hIAT : IsAffineTransport quadTwo quadTwo_not_isConst 3 b c α := by
      show ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
          quadTwo_not_isConst α
          * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)) ^ (3 : ℤ)
        = b * α + c
      rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hcdef]
      linear_combination hα
    have ha0 : α ≠ 0 := by
      intro hh
      have hz : ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
          quadTwo_not_isConst α
          * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)) ^ (3 : ℤ)
        = b * α + c := hIAT
      rw [hh, map_zero, zero_mul, mul_zero, zero_add] at hz
      exact hc0 hz.symm
    refine quadTwo_no_affineTransport_of_critical_order ha0 hb hc0 hIAT hbunit (fun p hp => ?_)
      ?_ ?_
    · rw [hcord p, Polynomial.rootMultiplicity_eq_zero ?_]
      · norm_num
      rw [Polynomial.IsRoot.def, derivative_quadTwo_eval]
      exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hp)
    · rw [hcord, rootMultiplicity_derivative_quadTwo, hbcrit, Nat.cast_one]
      norm_num
    · rw [hcord, rootMultiplicity_derivative_quadTwo, Nat.cast_one]
      norm_num

end

end GaloisForLFunctions.HTGeometry
