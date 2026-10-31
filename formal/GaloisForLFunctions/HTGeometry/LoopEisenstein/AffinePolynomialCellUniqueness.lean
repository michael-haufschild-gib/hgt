import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentIwahoriCriteria
import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2WeylLifts

import GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopBruhatDecomposition
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Uniqueness of affine polynomial cell coordinates

Conjugating a difference of root representatives shifts its polynomial
parameter beyond its degree bound. The Iwahori valuation condition then
forces every coefficient to vanish. Matrix right-coset factorizations lift
to the actual central loop group through the full Borel preimage.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable {L : Type*} [Field L]

private theorem upper_inverse (t : L) : (sl2Upper t)⁻¹ = sl2Upper (-t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]

private theorem lower_inverse (t : L) : (sl2Lower t)⁻¹ = sl2Lower (-t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Lower,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]

private theorem upper_diagonal_conjugate (v : Lˣ) (t : L) :
    (sl2Diagonal v)⁻¹ * sl2Upper t * sl2Diagonal v = sl2Upper (t / (v : L)^2) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper,sl2Diagonal,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,Units.val_inv_eq_inv_val] <;>
    field_simp [v.ne_zero]

private theorem lower_diagonal_conjugate (v : Lˣ) (t : L) :
    (sl2Diagonal v⁻¹)⁻¹ * sl2Lower t * sl2Diagonal v⁻¹ = sl2Lower (t / (v : L)^2) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Lower,sl2Diagonal,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,Units.val_inv_eq_inv_val] <;>
    field_simp [v.ne_zero]

private theorem upper_weyl_conjugate (v : Lˣ) (t : L) :
    (sl2WeylLower v⁻¹)⁻¹ * sl2Upper t * sl2WeylLower v⁻¹ =
      sl2Lower (-(t / (v : L)^2)) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper,sl2Lower,sl2WeylLower,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,Units.val_inv_eq_inv_val] <;>
    field_simp [v.ne_zero]

private theorem lower_weyl_conjugate (v : Lˣ) (t : L) :
    (sl2WeylLower v)⁻¹ * sl2Lower t * sl2WeylLower v =
      sl2Upper (-(t / (v : L)^2)) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper,sl2Lower,sl2WeylLower,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,Units.val_inv_eq_inv_val] <;>
    field_simp [v.ne_zero]

private theorem coset_difference_mem {G : Type*} [Group G] (I : Subgroup G)
    (g h j k : G) (hj : j ∈ I) (hk : k ∈ I) (he : g*j=h*k) : h⁻¹*g ∈ I := by
  have hd : h⁻¹*g = k*j⁻¹ := by
    calc
      h⁻¹*g = h⁻¹*(g*j)*j⁻¹ := by group
      _ = h⁻¹*(h*k)*j⁻¹ := by rw [he]
      _ = k*j⁻¹ := by group
  rw [hd]
  exact I.mul_mem hk (I.inv_mem hj)

private theorem upper_cell_difference (p q : L) (w : SL2 L) :
    (sl2Upper q * w)⁻¹ * (sl2Upper p * w) = w⁻¹ * sl2Upper (p-q) * w := by
  rw [mul_inv_rev,upper_inverse]
  calc
    (w⁻¹ * sl2Upper (-q)) * (sl2Upper p * w) =
        w⁻¹ * (sl2Upper (-q) * sl2Upper p) * w := by group
    _ = _ := by rw [← sl2Upper_add]; congr 2 <;> ring

private theorem lower_cell_difference (p q : L) (w : SL2 L) :
    (sl2Lower q * w)⁻¹ * (sl2Lower p * w) = w⁻¹ * sl2Lower (p-q) * w := by
  rw [mul_inv_rev,lower_inverse]
  calc
    (w⁻¹ * sl2Lower (-q)) * (sl2Lower p * w) =
        w⁻¹ * (sl2Lower (-q) * sl2Lower p) * w := by group
    _ = _ := by rw [← sl2Lower_add]; congr 2 <;> ring


variable {F : Type*} [Field F]

private theorem polynomial_eq_of_tail {n : ℕ} (p q : Polynomial F) (hp : p.degree < n) (hq : q.degree < n)
    (t : PowerSeries F) (he : (p : PowerSeries F) - (q : PowerSeries F) = PowerSeries.X ^ n * t) : p = q := by
  apply Polynomial.ext
  intro i
  by_cases hi : i < n
  · have hc := congrArg (PowerSeries.coeff i) he
    rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe,
      PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr hi)] at hc
    exact sub_eq_zero.mp hc
  · have hni : n ≤ i := Nat.le_of_not_gt hi
    have hpi : p.degree < i := hp.trans_le (by exact_mod_cast hni)
    have hqi : q.degree < i := hq.trans_le (by exact_mod_cast hni)
    rw [Polynomial.coeff_eq_zero_of_degree_lt hpi,
      Polynomial.coeff_eq_zero_of_degree_lt hqi]


/-- Integral shifted Laurent difference and the strict degree bounds force equality. -/
private theorem polynomial_eq_of_integral_shift (n : ℕ) (p q : Polynomial F) (hp : p.degree < n) (hq : q.degree < n)
    (hv : laurentValuation F
      ((((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F)) /
        ((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F)^n) ≤ 1) : p = q := by
  obtain ⟨t, ht⟩ := (LaurentSeries.val_le_one_iff_eq_coe F _).mp hv
  apply polynomial_eq_of_tail p q hp hq t
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [map_sub, map_mul, map_pow, HahnSeries.ofPowerSeries_X]
  change ((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F) =
    ((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F)^n * (t : LaurentSeries F)
  rw [ht]
  field_simp [(laurentXUnit F).ne_zero]

/-- A strictly integral shifted difference starts one degree later. -/
private theorem polynomial_eq_of_strict_shift (n : ℕ) (p q : Polynomial F) (hp : p.degree < n+1) (hq : q.degree < n+1)
    (hv : laurentValuation F
      ((((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F)) /
        ((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F)^n) < 1) : p = q := by
  obtain ⟨t, ht⟩ := (LaurentSeries.val_le_one_iff_eq_coe F _).mp hv.le
  have ht0 : PowerSeries.constantCoeff t = 0 := by
    apply (valuation_powerSeries_lt_one_iff F t).mp
    rw [ht]
    exact hv
  obtain ⟨s, hs⟩ := PowerSeries.X_dvd_iff.mpr ht0
  apply polynomial_eq_of_tail p q hp hq s
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  have he : ((t : PowerSeries F) : LaurentSeries F) =
      ((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F) * (s : LaurentSeries F) := by
    rw [hs, map_mul, HahnSeries.ofPowerSeries_X]
    rfl
  rw [ht] at he
  rw [map_sub, map_mul, map_pow, HahnSeries.ofPowerSeries_X]
  change ((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F) =
    ((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F)^(n+1) * (s : LaurentSeries F)
  have hd := (div_eq_iff (pow_ne_zero n (laurentXUnit F).ne_zero)).mp he
  rw [pow_succ]
  exact hd.trans (by ring)

/-- Strict integrality of an extra `X` is equivalent to losing that extra factor. -/
private theorem polynomial_eq_of_strict_X_shift (n : ℕ) (p q : Polynomial F) (hp : p.degree < n) (hq : q.degree < n)
    (hv : laurentValuation F
      (((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F) *
        (((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F)) /
          ((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F)^n) < 1) : p = q := by
  obtain ⟨t, ht⟩ := (LaurentSeries.val_le_one_iff_eq_coe F _).mp hv.le
  have ht0 : PowerSeries.constantCoeff t = 0 := by
    apply (valuation_powerSeries_lt_one_iff F t).mp
    rw [ht]
    exact hv
  obtain ⟨s, hs⟩ := PowerSeries.X_dvd_iff.mpr ht0
  have he : ((t : PowerSeries F) : LaurentSeries F) =
      ((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F) * (s : LaurentSeries F) := by
    rw [hs, map_mul, HahnSeries.ofPowerSeries_X]
    rfl
  rw [ht] at he
  have hd := (div_eq_iff (pow_ne_zero n (laurentXUnit F).ne_zero)).mp he
  have hx : ((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F) *
      (((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F)) =
      ((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F) *
        (((laurentXUnit F : (LaurentSeries F)ˣ) : LaurentSeries F)^n * (s : LaurentSeries F)) :=
    hd.trans (by ring)
  have hc := mul_left_cancel₀ (laurentXUnit F).ne_zero hx
  apply polynomial_eq_of_tail p q hp hq s
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [map_sub, map_mul, map_pow, HahnSeries.ofPowerSeries_X]
  exact hc

private theorem lower_polynomial_difference (p q : Polynomial F) :
    ((PowerSeries.X * (p : PowerSeries F) : PowerSeries F) : LaurentSeries F) -
        ((PowerSeries.X * (q : PowerSeries F) : PowerSeries F) : LaurentSeries F) =
      (laurentXUnit F : LaurentSeries F) *
        (((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F)) := by
  rw [map_mul, map_mul, HahnSeries.ofPowerSeries_X]
  exact (mul_sub _ _ _).symm

/-- An upper polynomial of degree below `2n` is unique in its translation right coset. -/
theorem upper_polynomial_translation_unique (n : ℕ) (p q : Polynomial F)
    (hp : p.degree < 2*n) (hq : q.degree < 2*n)
    (h : (sl2Upper ((q : PowerSeries F) : LaurentSeries F) *
          sl2Diagonal (laurentXUnit F ^ n))⁻¹ *
        (sl2Upper ((p : PowerSeries F) : LaurentSeries F) *
          sl2Diagonal (laurentXUnit F ^ n)) ∈ laurentIwahori F) : p = q := by
  rw [upper_cell_difference, upper_diagonal_conjugate] at h
  have hv := ((mem_laurentIwahori F _).mp h).1 0 1
  change laurentValuation F
    ((((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F)) /
      ((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F)^2) ≤ 1 at hv
  rw [Units.val_pow_eq_pow_val, ← pow_mul, Nat.mul_comm n 2] at hv
  exact polynomial_eq_of_integral_shift (2*n) p q hp hq hv

/-- A lower polynomial with zero constant term is unique in its translation right coset. -/
theorem lower_polynomial_translation_unique (n : ℕ) (p q : Polynomial F)
    (hp : p.degree < 2*n) (hq : q.degree < 2*n)
    (h : (sl2Lower ((PowerSeries.X * (q : PowerSeries F) : PowerSeries F) : LaurentSeries F) *
          sl2Diagonal ((laurentXUnit F ^ n)⁻¹))⁻¹ *
        (sl2Lower ((PowerSeries.X * (p : PowerSeries F) : PowerSeries F) : LaurentSeries F) *
          sl2Diagonal ((laurentXUnit F ^ n)⁻¹)) ∈ laurentIwahori F) : p = q := by
  rw [lower_cell_difference, lower_diagonal_conjugate] at h
  have hv := ((mem_laurentIwahori F _).mp h).2
  change laurentValuation F
    ((((PowerSeries.X * (p : PowerSeries F) : PowerSeries F) : LaurentSeries F) -
        ((PowerSeries.X * (q : PowerSeries F) : PowerSeries F) : LaurentSeries F)) /
      ((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F)^2) < 1 at hv
  rw [lower_polynomial_difference, Units.val_pow_eq_pow_val, ← pow_mul,
    Nat.mul_comm n 2] at hv
  exact polynomial_eq_of_strict_X_shift (2*n) p q hp hq hv

/-- Upper reflection heads have the exact uniqueness threshold `2n+1`. -/
theorem upper_polynomial_reflection_unique (n : ℕ) (p q : Polynomial F)
    (hp : p.degree < 2*n+1) (hq : q.degree < 2*n+1)
    (h : (sl2Upper ((q : PowerSeries F) : LaurentSeries F) *
          sl2WeylLower ((laurentXUnit F ^ n)⁻¹))⁻¹ *
        (sl2Upper ((p : PowerSeries F) : LaurentSeries F) *
          sl2WeylLower ((laurentXUnit F ^ n)⁻¹)) ∈ laurentIwahori F) : p = q := by
  rw [upper_cell_difference, upper_weyl_conjugate] at h
  have hv := ((mem_laurentIwahori F _).mp h).2
  change laurentValuation F
    (-((((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F)) /
      ((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F)^2)) < 1 at hv
  rw [Valuation.map_neg, Units.val_pow_eq_pow_val, ← pow_mul, Nat.mul_comm n 2] at hv
  exact polynomial_eq_of_strict_shift (2*n) p q hp hq hv

/-- Lower reflection heads have the exact uniqueness threshold `2n+1`. -/
theorem lower_polynomial_reflection_unique (n : ℕ) (p q : Polynomial F)
    (hp : p.degree < 2*n+1) (hq : q.degree < 2*n+1)
    (h : (sl2Lower ((PowerSeries.X * (q : PowerSeries F) : PowerSeries F) : LaurentSeries F) *
          sl2WeylLower (laurentXUnit F ^ (n+1)))⁻¹ *
        (sl2Lower ((PowerSeries.X * (p : PowerSeries F) : PowerSeries F) : LaurentSeries F) *
          sl2WeylLower (laurentXUnit F ^ (n+1))) ∈ laurentIwahori F) : p = q := by
  rw [lower_cell_difference, lower_weyl_conjugate] at h
  have hv := ((mem_laurentIwahori F _).mp h).1 0 1
  change laurentValuation F
    (-((((PowerSeries.X * (p : PowerSeries F) : PowerSeries F) : LaurentSeries F) -
        ((PowerSeries.X * (q : PowerSeries F) : PowerSeries F) : LaurentSeries F)) /
      ((laurentXUnit F ^ (n+1) : (LaurentSeries F)ˣ) : LaurentSeries F)^2)) ≤ 1 at hv
  rw [Valuation.map_neg, lower_polynomial_difference, Units.val_pow_eq_pow_val,
    ← pow_mul, Nat.mul_comm (n+1) 2] at hv
  have he : (laurentXUnit F : LaurentSeries F) *
        (((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F)) /
          (laurentXUnit F : LaurentSeries F)^(2*(n+1)) =
      (((p : PowerSeries F) : LaurentSeries F) - ((q : PowerSeries F) : LaurentSeries F)) /
        (laurentXUnit F : LaurentSeries F)^(2*n+1) := by
    have hn : 2*(n+1) = (2*n+1)+1 := by omega
    rw [hn, pow_succ]
    field_simp [(laurentXUnit F).ne_zero]
  rw [he] at hv
  exact polynomial_eq_of_integral_shift (2*n+1) p q hp hq hv

namespace LoopSL2

/-- A right Iwahori factorization lifts modulo the full positive Borel. -/
theorem exists_right_borel_of_projection_factor (g r : LoopSL2 F)
    (j : SL2 (LaurentSeries F)) (hj : j ∈ laurentIwahori F)
    (he : projection F g = projection F r * j) :
    ∃ b : positiveBorel F, g = r * b := by
  have hb : r⁻¹ * g ∈ positiveBorel F := by
    apply (mem_positiveBorel_iff_projection F _).mpr
    rw [map_mul, map_inv, he, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hj
  refine ⟨⟨r⁻¹ * g, hb⟩, ?_⟩
  change g = r * (r⁻¹ * g)
  group

end LoopSL2

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.upper_polynomial_translation_unique
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.lower_polynomial_translation_unique
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.upper_polynomial_reflection_unique
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.lower_polynomial_reflection_unique
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.exists_right_borel_of_projection_factor
