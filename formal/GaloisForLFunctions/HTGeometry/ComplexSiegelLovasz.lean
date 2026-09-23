import GaloisForLFunctions.HTGeometry.ComplexSiegelEntryBound
import GaloisForLFunctions.HTGeometry.ComplexSiegelGramDomination

/-!
# Complex Lovász bounds from local minimality

The real Siegel reduction layer already derives adjacent Jacobi-weight bounds from greedy
minimality.  This file supplies the Hermitian counterpart.  The diagonal of a Hermitian Jacobi
form is a weighted sum of squared norms, so the same sharp `4 / 3` argument applies after complex
size reduction.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The `j`-th Hermitian diagonal entry dominates its `j`-th Jacobi weight. -/
theorem ComplexJacobiData.d_le_form_diag (J : ComplexJacobiData n) (j : Fin n) :
    J.d j ≤ (J.form j j).re := by
  classical
  rw [J.form_diag j]
  refine Finset.single_le_sum
    (fun m _ => mul_nonneg (J.pos m).le (sq_nonneg ‖J.U m j‖))
    (Finset.mem_univ j) |>.trans' ?_
  rw [J.unit j, norm_one, one_pow, mul_one]

/-- The first Hermitian form diagonal is the first Jacobi weight. -/
theorem ComplexJacobiData.form_diag_zero (J : ComplexJacobiData n)
    {i : Fin n} (hi : (i : ℕ) = 0) :
    (J.form i i).re = J.d i := by
  classical
  rw [J.form_diag i]
  refine (Finset.sum_eq_single i (fun m _ hm => ?_)
    (fun hcon => absurd (Finset.mem_univ i) hcon)).trans ?_
  · rcases lt_trichotomy m i with hmi | hmi | hmi
    · exact absurd (Fin.lt_def.1 hmi) (by omega)
    · exact absurd hmi hm
    · rw [J.upper m i hmi, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · rw [J.unit i, norm_one, one_pow, mul_one]

/-- At a successor index, vanishing before `i` leaves exactly the `i`-th correction and the new
Jacobi weight. -/
theorem ComplexJacobiData.form_diag_succ (J : ComplexJacobiData n)
    {i j : Fin n} (hij : (j : ℕ) = (i : ℕ) + 1)
    (hpre : ∀ m : Fin n, m < i → J.U m j = 0) :
    (J.form j j).re = J.d i * ‖J.U i j‖ ^ (2 : ℕ) + J.d j := by
  classical
  rw [J.form_diag j]
  have hsplit : (∑ m, J.d m * ‖J.U m j‖ ^ (2 : ℕ)) =
      J.d i * ‖J.U i j‖ ^ (2 : ℕ) +
        ∑ m ∈ Finset.univ.filter (fun m : Fin n => m ≠ i),
          J.d m * ‖J.U m j‖ ^ (2 : ℕ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m : Fin n => m = i)]
    congr 1
    rw [Finset.filter_eq' Finset.univ i]
    simp
  rw [hsplit]
  congr 1
  refine (Finset.sum_eq_single j (fun m hm hmj => ?_) (fun hcon => ?_)).trans ?_
  · rw [Finset.mem_filter] at hm
    rcases lt_trichotomy m i with hmi | hmi | hmi
    · rw [hpre m hmi, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    · exact absurd hmi hm.2
    · have hjm : j < m := by
        refine Fin.lt_def.2 ?_
        have hmi' := Fin.lt_def.1 hmi
        have hmj' : (m : ℕ) ≠ (j : ℕ) := fun h => hmj (Fin.ext h)
        omega
      rw [J.upper m j hjm, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, fun h => by
      rw [h] at hij
      omega⟩) hcon
  · rw [J.unit j, norm_one, one_pow, mul_one]

/-- Complex Lovász bound from one projected minimality comparison. -/
theorem ComplexJacobiData.lovasz_of_le (J : ComplexJacobiData n)
    {k l : Fin n}
    (hred : ∀ i j : Fin n, i < j → ‖J.U i j‖ ≤ 1 / 2)
    (hkl : k < l)
    (hmin : J.d k ≤ J.d l + ‖J.U k l‖ ^ (2 : ℕ) * J.d k) :
    J.d k ≤ (4 / 3) * J.d l := by
  have hb : ‖J.U k l‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) ^ (2 : ℕ) := by
    nlinarith [hred k l hkl, norm_nonneg (J.U k l)]
  nlinarith [hmin, hb, J.pos k]

/-- Consecutive Hermitian Lovász bound from minimality against the next form diagonal. -/
theorem ComplexJacobiData.lovasz_succ (J : ComplexJacobiData n)
    {i j : Fin n} (hij : (j : ℕ) = (i : ℕ) + 1)
    (hred : ∀ a b : Fin n, a < b → ‖J.U a b‖ ≤ 1 / 2)
    (hpre : ∀ m : Fin n, m < i → J.U m j = 0)
    (hmin : J.d i ≤ (J.form j j).re) :
    J.d i ≤ (4 / 3) * J.d j := by
  refine J.lovasz_of_le hred (Fin.lt_def.2 (by omega)) ?_
  rw [J.form_diag_succ hij hpre] at hmin
  linarith

/-- Bottom Hermitian Lovász bound.  No earlier-coordinate hypothesis remains at index zero. -/
theorem ComplexJacobiData.lovasz_first (J : ComplexJacobiData n)
    {i j : Fin n} (hi : (i : ℕ) = 0) (hj : (j : ℕ) = 1)
    (hred : ∀ a b : Fin n, a < b → ‖J.U a b‖ ≤ 1 / 2)
    (hmin : (J.form i i).re ≤ (J.form j j).re) :
    J.d i ≤ (4 / 3) * J.d j := by
  refine J.lovasz_succ (by omega) hred (fun m hm => ?_) ?_
  · exact absurd (Fin.lt_def.1 hm) (by omega)
  · rw [← J.form_diag_zero hi]
    exact hmin

/-- The projected Hermitian norm at the next basis vector is exactly the current correction plus
the next Jacobi weight. -/
theorem ComplexJacobiData.projNorm_succ (J : ComplexJacobiData n)
    {i j : Fin n} (hij : (j : ℕ) = (i : ℕ) + 1) :
    J.projNorm i (Pi.single j (1 : ℂ)) =
      J.d i * ‖J.U i j‖ ^ (2 : ℕ) + J.d j := by
  classical
  have hij' : i < j := Fin.lt_def.2 (by omega)
  rw [ComplexJacobiData.projNorm]
  have hsplit :
      (∑ m ∈ Finset.univ.filter (fun m : Fin n => i ≤ m),
          J.d m * ‖J.U.mulVec (Pi.single j (1 : ℂ)) m‖ ^ (2 : ℕ)) =
        J.d i * ‖J.U.mulVec (Pi.single j (1 : ℂ)) i‖ ^ (2 : ℕ) +
          ∑ m ∈ Finset.univ.filter (fun m : Fin n => i ≤ m ∧ m ≠ i),
            J.d m * ‖J.U.mulVec (Pi.single j (1 : ℂ)) m‖ ^ (2 : ℕ) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun m : Fin n => i ≤ m)) (fun m : Fin n => m = i)]
    congr 1
    · rw [Finset.filter_filter]
      rw [Finset.filter_congr (q := fun m : Fin n => m = i) (fun m _ => by
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨by rw [h], h⟩)]
      rw [Finset.filter_eq' Finset.univ i]
      simp
    · rw [Finset.filter_filter]
  rw [hsplit, J.mulVec_single]
  congr 1
  refine (Finset.sum_eq_single j (fun m hm hmj => ?_) (fun hcon => ?_)).trans ?_
  · rw [Finset.mem_filter] at hm
    have him : i ≤ m := hm.2.1
    have hne : m ≠ i := hm.2.2
    have hjm : j < m := by
      refine Fin.lt_def.2 ?_
      have h1 : (i : ℕ) ≤ (m : ℕ) := him
      have h2 : (m : ℕ) ≠ (i : ℕ) := fun h => hne (Fin.ext h)
      have h3 : (m : ℕ) ≠ (j : ℕ) := fun h => hmj (Fin.ext h)
      omega
    rw [J.mulVec_single, J.upper m j hjm, norm_zero]
    ring
  · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j,
      le_of_lt hij', fun h => absurd (by rw [h] : (j : ℕ) = (i : ℕ)) (by omega)⟩) hcon
  · rw [J.mulVec_single, J.unit j, norm_one, one_pow, mul_one]

/-- Complex Lovász bound from greedy projected-norm minimality. -/
theorem ComplexJacobiData.lovasz_of_projNorm_min (J : ComplexJacobiData n)
    {i j : Fin n} (hij : (j : ℕ) = (i : ℕ) + 1)
    (hred : ∀ a b : Fin n, a < b → ‖J.U a b‖ ≤ 1 / 2)
    (hmin : J.d i ≤ J.projNorm i (Pi.single j (1 : ℂ))) :
    J.d i ≤ (4 / 3) * J.d j := by
  refine J.lovasz_of_le hred (Fin.lt_def.2 (by omega)) ?_
  rw [J.projNorm_succ hij] at hmin
  linarith

/-- Complex size reduction bounds every upper-unipotent entry by one. -/
theorem ComplexJacobiData.entries_le_one (J : ComplexJacobiData n)
    (hred : ∀ a b : Fin n, a < b → ‖J.U a b‖ ≤ 1 / 2)
    (i j : Fin n) : ‖J.U i j‖ ≤ 1 := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hred i j hij).trans (by norm_num)
  · subst j
    rw [J.unit, norm_one]
  · rw [J.upper i j hij, norm_zero]
    norm_num

/-- Greedy projected minima and complex size reduction imply the full Hermitian Siegel bounds. -/
theorem ComplexJacobiData.isSiegel_of_greedy (J : ComplexJacobiData n)
    (hred : ∀ a b : Fin n, a < b → ‖J.U a b‖ ≤ 1 / 2)
    (hgreedy : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 →
      J.d i ≤ J.projNorm i (Pi.single j (1 : ℂ))) :
    J.IsSiegel (4 / 3) 1 := by
  refine ⟨fun i j hij => ?_, fun i j => J.entries_le_one hred i j⟩
  exact J.lovasz_of_projNorm_min hij.symm hred (hgreedy i j hij.symm)

end GaloisForLFunctions.HTGeometry
