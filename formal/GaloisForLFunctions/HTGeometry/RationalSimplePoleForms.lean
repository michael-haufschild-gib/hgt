import GaloisForLFunctions.HTGeometry.RationalSphereDynamics
import GaloisForLFunctions.HTGeometry.RittTransportPolynomial

/-!
# Rational one-forms with simple poles

A rational function `f` is read as the one-form `f dx`; in the chart at infinity it becomes
`infForm f = f(1/x)·(−1/x²)`, whose order at `0` is `deg(denominator) − deg(numerator) − 2`.

* **Partial fractions.**  If `f dx` has at most simple poles on the whole projective line, then `f`
  is the sum of its polar parts, `f = Σ res_z f · (x − z)⁻¹`.
* **The residue theorem.**  For such a form the residues, including the residue at infinity, add up
  to zero.
* **Affine connections at infinity.**  In the chart at infinity an affine connection `a` reads
  `infForm a + ℓ` with `ℓ = (ι')'/ι'` of residue `−2`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-! ### Lower bounds on orders -/

omit [CharZero K] in
theorem le_ratOrder_add {f g : RatFunc K} {z : K} {n : ℤ} (hn : n ≤ 0) (hf : n ≤ ratOrder f z)
    (hg : n ≤ ratOrder g z) : n ≤ ratOrder (f + g) z := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rwa [zero_add]
  rcases eq_or_ne g 0 with rfl | hg0
  · rwa [add_zero]
  rcases eq_or_ne (f + g) 0 with h | h
  · rw [h, ratOrder_zero]; exact hn
  have := min_le_ratOrder_add hf0 hg0 h z
  omega

theorem le_ratOrder_neg {f : RatFunc K} {z : K} {n : ℤ} (hf : n ≤ ratOrder f z) :
    n ≤ ratOrder (-f) z := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rwa [neg_zero]
  · rwa [ratOrder_neg hf0]

theorem le_ratOrder_sub {f g : RatFunc K} {z : K} {n : ℤ} (hn : n ≤ 0) (hf : n ≤ ratOrder f z)
    (hg : n ≤ ratOrder g z) : n ≤ ratOrder (f - g) z := by
  rw [sub_eq_add_neg]
  exact le_ratOrder_add hn hf (le_ratOrder_neg hg)

omit [CharZero K] in
theorem le_ratOrder_C_mul {f : RatFunc K} {z : K} {n : ℤ} (hn : n ≤ 0) (c : K)
    (hf : n ≤ ratOrder f z) : n ≤ ratOrder (RatFunc.C c * f) z := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, zero_mul, ratOrder_zero]; exact hn
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero, ratOrder_zero]; exact hn
  rw [ratOrder_mul (by simpa using hc) hf0, ratOrder_C, zero_add]
  exact hf

omit [CharZero K] in
theorem le_ratOrder_sum {ι : Type*} (s : Finset ι) (F : ι → RatFunc K) {z : K} {n : ℤ}
    (hn : n ≤ 0) (h : ∀ i ∈ s, n ≤ ratOrder (F i) z) : n ≤ ratOrder (∑ i ∈ s, F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ratOrder_zero]; exact hn
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact le_ratOrder_add hn (h i (Finset.mem_insert_self i s))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ### Residues -/

omit [CharZero K] in
theorem ratResidue_C_mul {f : RatFunc K} {z : K} (c : K) (hf : -1 ≤ ratOrder f z) :
    ratResidue (RatFunc.C c * f) z = c * ratResidue f z := by
  rw [ratResidue_mul_regular (ratOrder_C_nonneg c z) hf, ratValue_C]

theorem ratResidue_neg {f : RatFunc K} {z : K} (hf : -1 ≤ ratOrder f z) :
    ratResidue (-f) z = -ratResidue f z := by
  rw [show -f = RatFunc.C (-1) * f by rw [map_neg, map_one, neg_one_mul], ratResidue_C_mul _ hf,
    neg_one_mul]

theorem ratResidue_sub {f g : RatFunc K} {z : K} (hf : -1 ≤ ratOrder f z) (hg : -1 ≤ ratOrder g z) :
    ratResidue (f - g) z = ratResidue f z - ratResidue g z := by
  rw [sub_eq_add_neg, ratResidue_add hf (le_ratOrder_neg hg), ratResidue_neg hg, sub_eq_add_neg]

omit [CharZero K] in
theorem ratResidue_sum {ι : Type*} (s : Finset ι) (F : ι → RatFunc K) {z : K}
    (h : ∀ i ∈ s, -1 ≤ ratOrder (F i) z) :
    ratResidue (∑ i ∈ s, F i) z = ∑ i ∈ s, ratResidue (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ratResidue_eq_zero_of_regular (by
      rw [ratOrder_zero])]
  | insert i s hi ih =>
      have hs : ∀ j ∈ s, -1 ≤ ratOrder (F j) z := fun j hj => h j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        ratResidue_add (h i (Finset.mem_insert_self i s)) (le_ratOrder_sum s F (by norm_num) hs),
        ih hs]

omit [CharZero K] in
theorem ratOrder_inv_linFac_of_ne {z w : K} (h : w ≠ z) : ratOrder (ratLinFac z)⁻¹ w = 0 := by
  classical
  rw [ratOrder_inv (ratLinFac_ne_zero z), ratLinFac_eq, ratOrder_algebraMap,
    rootMultiplicity_X_sub_C,
    if_neg h]
  simp

omit [CharZero K] in
theorem ratOrder_neg_iff_denom_isRoot {f : RatFunc K} {z : K} (h : ratOrder f z < 0) :
    f.denom.IsRoot z := by
  by_contra hn
  rw [ratOrder, rootMultiplicity_eq_zero hn] at h
  omega

/-! ### The chart at infinity -/

/-- The one-form `f dx` in the chart at infinity. -/
def infForm (f : RatFunc K) : RatFunc K :=
  ratFuncSubstitutionAlgHom invX nonconst_invX f * ratFuncDeriv invX

theorem infForm_add (f g : RatFunc K) : infForm (f + g) = infForm f + infForm g := by
  rw [infForm, infForm, infForm, map_add, add_mul]

theorem infForm_sub (f g : RatFunc K) : infForm (f - g) = infForm f - infForm g := by
  rw [infForm, infForm, infForm, map_sub, sub_mul]

theorem infForm_C_mul (c : K) (f : RatFunc K) :
    infForm (RatFunc.C c * f) = RatFunc.C c * infForm f := by
  rw [infForm, infForm, map_mul, ratFuncSubstitutionAlgHom_C, mul_assoc]

theorem infForm_sum {ι : Type*} (s : Finset ι) (F : ι → RatFunc K) :
    infForm (∑ i ∈ s, F i) = ∑ i ∈ s, infForm (F i) := by
  rw [infForm, map_sum, Finset.sum_mul]
  rfl

theorem ratOrder_deriv_invX : ratOrder (ratFuncDeriv (invX : RatFunc K)) 0 = -2 := by
  rw [ratFuncDeriv_invX, ratOrder_neg (inv_ne_zero (pow_ne_zero _ X_ne_zero')),
    ratOrder_inv (pow_ne_zero _ X_ne_zero'), ratOrder_X_pow_zero]
  rfl

/-- **The order of a form at infinity.** -/
theorem ratOrder_infForm {f : RatFunc K} (hf : f ≠ 0) :
    ratOrder (infForm f) 0 = (f.denom.natDegree : ℤ) - f.num.natDegree - 2 := by
  have hs : ratFuncSubstitutionAlgHom invX nonconst_invX f ≠ 0 := by
    intro h
    exact hf ((ratFuncSubstitutionAlgHom invX nonconst_invX).toRingHom.injective (by simpa using h))
  rw [infForm, ratOrder_mul hs ratFuncDeriv_invX_ne_zero, ratOrder_subst_invX hf,
    ratOrder_deriv_invX]
  ring

theorem ratOrder_infForm_polynomial {A : K[X]} (hA : A ≠ 0) :
    ratOrder (infForm (algebraMap K[X] (RatFunc K) A)) 0 = -(A.natDegree : ℤ) - 2 := by
  rw [ratOrder_infForm (algebraMap_ne_zero_of_ne_zero hA), RatFunc.num_algebraMap,
    RatFunc.denom_algebraMap, natDegree_one]
  ring

theorem one_sub_C_mul_X_regular (z : K) :
    ratOrder (1 - RatFunc.C z * RatFunc.X : RatFunc K) 0 = 0 ∧
      ratValue (1 - RatFunc.C z * RatFunc.X : RatFunc K) 0 = 1 := by
  have hreg : 0 ≤ ratOrder (1 - RatFunc.C z * RatFunc.X : RatFunc K) 0 :=
    ratOrder_sub_nonneg (by rw [ratOrder_one]) (ratOrder_mul_nonneg (ratOrder_C_nonneg z 0)
      (ratOrder_X_nonneg 0))
  have hval : ratValue (1 - RatFunc.C z * RatFunc.X : RatFunc K) 0 = 1 := by
    rw [ratValue_sub (by rw [ratOrder_one]) (ratOrder_mul_nonneg (ratOrder_C_nonneg z 0)
      (ratOrder_X_nonneg 0)), ratValue_one, ratValue_mul (ratOrder_C_nonneg z 0)
      (ratOrder_X_nonneg 0), ratValue_C, ratValue_X, mul_zero, sub_zero]
  refine ⟨?_, hval⟩
  have h0 : (1 - RatFunc.C z * RatFunc.X : RatFunc K) ≠ 0 := by
    intro h; rw [h, ratValue_zero] at hval; exact zero_ne_one hval
  by_contra hne
  have hpos : 0 < ratOrder (1 - RatFunc.C z * RatFunc.X : RatFunc K) 0 := lt_of_le_of_ne hreg
    (Ne.symm hne)
  rw [(ratValue_eq_zero_iff h0 hreg).mpr hpos] at hval
  exact zero_ne_one hval

/-- **The simple pole `(x − z)⁻¹` has residue `−1` at infinity.** -/
theorem infForm_inv_linFac (z : K) :
    -1 ≤ ratOrder (infForm (ratLinFac z)⁻¹) 0 ∧ ratResidue (infForm (ratLinFac z)⁻¹) 0 = -1 := by
  obtain ⟨hord, hval⟩ := one_sub_C_mul_X_regular z
  have h1 : (1 - RatFunc.C z * RatFunc.X : RatFunc K) ≠ 0 := by
    intro h; rw [h, ratValue_zero] at hval; exact zero_ne_one hval
  have hX := X_ne_zero' (K := K)
  have hid : infForm (ratLinFac z)⁻¹
      = RatFunc.C (-1) * ((1 - RatFunc.C z * RatFunc.X)⁻¹ * (ratLinFac 0)⁻¹) := by
    have hsub : ratFuncSubstitutionAlgHom invX nonconst_invX (ratLinFac z)
        = (1 - RatFunc.C z * RatFunc.X) * RatFunc.X⁻¹ := by
      rw [ratFuncSubstitution_linFac]
      show (RatFunc.X : RatFunc K)⁻¹ - RatFunc.C z = _
      field_simp
    rw [infForm, map_inv₀, hsub, ratFuncDeriv_invX, ratLinFac, map_zero, sub_zero, map_neg, map_one]
    field_simp
  have hinv : 0 ≤ ratOrder (1 - RatFunc.C z * RatFunc.X : RatFunc K)⁻¹ 0 := by
    rw [ratOrder_inv h1, hord]; rfl
  have hinvval : ratValue (1 - RatFunc.C z * RatFunc.X : RatFunc K)⁻¹ 0 = 1 := by
    rw [ratValue_inv h1 hord, hval, inv_one]
  have hpole : -1 ≤ ratOrder (ratLinFac (0 : K))⁻¹ 0 := by rw [ratOrder_inv_linFac]
  rw [hid]
  refine ⟨le_ratOrder_C_mul (by norm_num) _ (ratOrder_mul_ge hinv hpole), ?_⟩
  rw [ratResidue_C_mul _ (ratOrder_mul_ge hinv hpole), ratResidue_mul_regular hinv hpole, hinvval,
    ratResidue_inv_linFac]
  ring

/-! ### Partial fractions and the residue theorem -/

/-- **A form with at most simple poles is the sum of its polar parts.** -/
theorem eq_sum_polar [IsAlgClosed K] {f : RatFunc K} (S : Finset K)
    (hS : ∀ z, ratOrder f z < 0 → z ∈ S) (hfin : ∀ z, -1 ≤ ratOrder f z)
    (hinf : -1 ≤ ratOrder (infForm f) 0) :
    f = ∑ z ∈ S, RatFunc.C (ratResidue f z) * (ratLinFac z)⁻¹ := by
  classical
  set P := ∑ z ∈ S, RatFunc.C (ratResidue f z) * (ratLinFac z)⁻¹ with hP
  have hterm_inf :
      ∀ z ∈ S, -1 ≤ ratOrder (infForm (RatFunc.C (ratResidue f z) * (ratLinFac z)⁻¹)) 0 :=
    fun z _ => by
      rw [infForm_C_mul]
      exact le_ratOrder_C_mul (by norm_num) _ (infForm_inv_linFac z).1
  have hP_inf : -1 ≤ ratOrder (infForm P) 0 := by
    rw [hP, infForm_sum]
    exact le_ratOrder_sum S _ (by norm_num) hterm_inf
  have hh_inf : -1 ≤ ratOrder (infForm (f - P)) 0 := by
    rw [infForm_sub]
    exact le_ratOrder_sub (by norm_num) hinf hP_inf
  have hoff : ∀ w, ∀ T : Finset K, w ∉ T →
      0 ≤ ratOrder (∑ z ∈ T, RatFunc.C (ratResidue f z) * (ratLinFac z)⁻¹) w := by
    intro w T hw
    refine le_ratOrder_sum T _ le_rfl fun z hz => ?_
    have hne : w ≠ z := fun h => hw (h ▸ hz)
    exact le_ratOrder_C_mul le_rfl _ (by rw [ratOrder_inv_linFac_of_ne hne])
  have hh_fin : ∀ w, 0 ≤ ratOrder (f - P) w := by
    intro w
    by_cases hw : w ∈ S
    · have hsplit : f - P = (f - RatFunc.C (ratResidue f w) * (ratLinFac w)⁻¹)
          - ∑ z ∈ S.erase w, RatFunc.C (ratResidue f z) * (ratLinFac z)⁻¹ := by
        rw [hP, ← Finset.add_sum_erase S _ hw]
        ring
      rw [hsplit]
      exact ratOrder_sub_nonneg (regular_sub_polar (hfin w))
        (hoff w _ (Finset.notMem_erase w S))
    · have hf : 0 ≤ ratOrder f w := by
        by_contra h
        exact hw (hS w (lt_of_not_ge h))
      exact ratOrder_sub_nonneg hf (hoff w S hw)
  by_contra hne
  have hh0 : f - P ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨A, hA0, hA⟩ := exists_polynomial_of_ratOrder_nonneg hh0 hh_fin
  rw [hA, ratOrder_infForm_polynomial hA0] at hh_inf
  omega

/-- **The residue theorem for forms with at most simple poles.** -/
theorem sum_ratRes_add_infRes [IsAlgClosed K] {f : RatFunc K} (S : Finset K)
    (hS : ∀ z, ratOrder f z < 0 → z ∈ S) (hfin : ∀ z, -1 ≤ ratOrder f z)
    (hinf : -1 ≤ ratOrder (infForm f) 0) :
    ∑ z ∈ S, ratResidue f z + ratResidue (infForm f) 0 = 0 := by
  have hf := eq_sum_polar S hS hfin hinf
  have hterm : ∀ z ∈ S, -1 ≤ ratOrder (infForm (RatFunc.C (ratResidue f z) * (ratLinFac z)⁻¹)) 0 :=
    fun z _ => by
      rw [infForm_C_mul]
      exact le_ratOrder_C_mul (by norm_num) _ (infForm_inv_linFac z).1
  have hres : ratResidue (infForm f) 0 = -∑ z ∈ S, ratResidue f z := by
    conv_lhs => rw [hf]
    rw [infForm_sum, ratResidue_sum S _ hterm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [infForm_C_mul, ratResidue_C_mul _ (infForm_inv_linFac z).1, (infForm_inv_linFac z).2]
    ring
  rw [hres]
  ring

/-! ### Affine connections at infinity -/

theorem connAt_none (a : RatFunc K) :
    connAt a none = infForm a + logDerivRat (ratFuncDeriv (invX : RatFunc K)) := rfl

theorem logDerivRat_deriv_invX :
    -1 ≤ ratOrder (logDerivRat (ratFuncDeriv (invX : RatFunc K))) 0 ∧
      ratResidue (logDerivRat (ratFuncDeriv (invX : RatFunc K))) 0 = -2 := by
  obtain ⟨h1, h2⟩ := logDerivRat_residue (ratFuncDeriv_invX_ne_zero (K := K)) 0
  rw [ratOrder_deriv_invX] at h2
  exact ⟨h1, by rw [h2]; norm_num⟩

/-- An affine connection has at most a simple pole at infinity exactly when its form does. -/
theorem infForm_ord_of_connAt {a : RatFunc K} (ha : -1 ≤ ratOrder (connAt a none) 0) :
    -1 ≤ ratOrder (infForm a) 0 ∧ ratResidue (connAt a none) 0 = ratResidue (infForm a) 0 - 2 := by
  have hL := logDerivRat_deriv_invX (K := K)
  have hsplit : infForm a = connAt a none - logDerivRat (ratFuncDeriv (invX : RatFunc K)) := by
    rw [connAt_none]; ring
  have hinf : -1 ≤ ratOrder (infForm a) 0 := by
    rw [hsplit]; exact le_ratOrder_sub (by norm_num) ha hL.1
  refine ⟨hinf, ?_⟩
  rw [connAt_none, ratResidue_add hinf hL.1, hL.2]
  ring

/-- The difference of two affine connections at infinity is the form of their difference. -/
theorem connAt_none_sub (a b : RatFunc K) :
    connAt a none - connAt b none = infForm (a - b) := by
  rw [connAt_none, connAt_none, infForm_sub]
  ring

end

end GaloisForLFunctions.HTGeometry
