import GaloisForLFunctions.HTGeometry.RatFuncFieldShift

namespace GaloisForLFunctions.HTGeometry.FieldShift

noncomputable section

open Polynomial

variable {F : Type*} [Field F]

/-- Polynomial denominator form of the Bessel Riccati obstruction over any field. -/
theorem orderBesselRiccatiPolynomial_no_solution
    {c : F} (hc : c ≠ 0) {p q : Polynomial F} (hq : q ≠ 0)
    (hco : IsCoprime p q)
    (h : p * p.comp (X + C 1) -
        (C c * (X + C 1)) * p * q.comp (X + C 1) -
        q * q.comp (X + C 1) = 0) : False := by
  let S : Polynomial F := X + C 1
  have hSdeg : S.natDegree = 1 := by
    simpa [S] using Polynomial.natDegree_X_add_C (1 : F)
  have hqs : q.comp S ≠ 0 := comp_X_add_C_one_ne_zero hq
  have hcshift : IsCoprime (p.comp S) (q.comp S) := by
    obtain ⟨a, b, hab⟩ := hco
    refine ⟨a.comp S, b.comp S, ?_⟩
    have hc' := congrArg (fun t : Polynomial F => t.comp S) hab
    simpa only [Polynomial.add_comp, Polynomial.mul_comp, one_comp] using hc'
  have hdivprod : q.comp S ∣ p * p.comp S := by
    refine ⟨C c * S * p + q, ?_⟩
    dsimp [S] at h ⊢
    linear_combination h
  have hdivp : q.comp S ∣ p :=
    hcshift.symm.dvd_of_dvd_mul_right hdivprod
  obtain ⟨r, hr⟩ := hdivp
  have hfactored : q.comp S *
      (r * (q.comp S).comp S * r.comp S -
        (C c * S) * r * q.comp S - q) = 0 := by
    rw [hr] at h
    dsimp [S] at h ⊢
    simp only [Polynomial.mul_comp] at h
    linear_combination h
  have hres : r * (q.comp S).comp S * r.comp S -
      (C c * S) * r * q.comp S - q = 0 :=
    (mul_eq_zero.mp hfactored).resolve_left hqs
  have hrq : r ∣ q := by
    refine ⟨r.comp S * (q.comp S).comp S - C c * S * q.comp S, ?_⟩
    calc
      q = r * (q.comp S).comp S * r.comp S - (C c * S) * r * q.comp S := by
        exact (sub_eq_zero.mp hres).symm
      _ = r * (r.comp S * (q.comp S).comp S - C c * S * q.comp S) := by ring
  have hrp : r ∣ p := by
    rw [hr]
    exact dvd_mul_left _ _
  have hrunit : IsUnit r := hco.isUnit_of_dvd' hrp hrq
  obtain ⟨k, hk, hkr⟩ := Polynomial.isUnit_iff.mp hrunit
  have hk0 : k ≠ 0 := by simpa only [isUnit_iff_ne_zero] using hk
  have hs2q : (q.comp S).comp S ≠ 0 := comp_X_add_C_one_ne_zero hqs
  have hS0 : S ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hSdeg
    omega
  have hdegreeLeft : ((C c * S) * r * q.comp S).natDegree = q.natDegree + 1 := by
    rw [← hkr]
    calc
      (C c * S * C k * q.comp S).natDegree =
          (C (c * k) * (S * q.comp S)).natDegree := by
            rw [map_mul]
            ring_nf
      _ = (S * q.comp S).natDegree :=
        Polynomial.natDegree_C_mul (mul_ne_zero hc hk0)
      _ = S.natDegree + (q.comp S).natDegree :=
        Polynomial.natDegree_mul hS0 hqs
      _ = q.natDegree + 1 := by
        rw [Polynomial.natDegree_comp, hSdeg]
        omega
  have heq : (C c * S) * r * q.comp S =
      r * (q.comp S).comp S * r.comp S - q := by
    linear_combination -hres
  have hdegreeRight :
      (r * (q.comp S).comp S * r.comp S - q).natDegree ≤ q.natDegree := by
    apply le_trans (Polynomial.natDegree_sub_le _ _)
    apply max_le
    · rw [← hkr, Polynomial.C_comp]
      calc
        (C k * (q.comp S).comp S * C k).natDegree =
            (C (k * k) * (q.comp S).comp S).natDegree := by
              rw [map_mul]
              ring_nf
        _ = ((q.comp S).comp S).natDegree :=
          Polynomial.natDegree_C_mul (mul_ne_zero hk0 hk0)
        _ = q.natDegree := by
          rw [Polynomial.natDegree_comp, Polynomial.natDegree_comp, hSdeg]
          omega
        _ ≤ q.natDegree := le_rfl
    · exact le_rfl
  have hdegreeContradiction := hdegreeLeft
  rw [heq] at hdegreeContradiction
  omega

/-- The Bessel Riccati equation has no rational solution after any extension of its constant
field. -/
theorem orderBesselRiccati_no_ratFunc_solution {c : F} (hc : c ≠ 0) :
    ¬ ∃ u : RatFunc F,
      u * ratShift u -
        algebraMap (Polynomial F) (RatFunc F) (C c * (X + C 1)) * u - 1 = 0 := by
  rintro ⟨u, huRic⟩
  let p := u.num
  let q := u.denom
  have hq : q ≠ 0 := u.denom_ne_zero
  have hco : IsCoprime p q := u.isCoprime_num_denom
  have hqK : algebraMap (Polynomial F) (RatFunc F) q ≠ 0 := fun hzero =>
    hq (RatFunc.algebraMap_injective F (by rw [hzero, map_zero]))
  have hqs : q.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hq
  have hqsK : algebraMap (Polynomial F) (RatFunc F) (q.comp (X + C 1)) ≠ 0 :=
    fun hzero => hqs (RatFunc.algebraMap_injective F (by rw [hzero, map_zero]))
  have hratio : algebraMap (Polynomial F) (RatFunc F) p /
      algebraMap (Polynomial F) (RatFunc F) q = u := RatFunc.num_div_denom u
  have hshift : ratShift u =
      algebraMap (Polynomial F) (RatFunc F) (p.comp (X + C 1)) /
        algebraMap (Polynomial F) (RatFunc F) (q.comp (X + C 1)) := by
    rw [← hratio, map_div₀, ratShift_algebraMap, ratShift_algebraMap]
  have hcross : p * p.comp (X + C 1) -
      (C c * (X + C 1)) * p * q.comp (X + C 1) -
      q * q.comp (X + C 1) = 0 := by
    apply RatFunc.algebraMap_injective F
    simp only [map_sub, map_mul, map_zero]
    rw [hshift, ← hratio] at huRic
    field_simp [hqK, hqsK] at huRic
    simp only [map_mul] at huRic
    linear_combination huRic
  exact orderBesselRiccatiPolynomial_no_solution hc hq hco hcross

end

end GaloisForLFunctions.HTGeometry.FieldShift
