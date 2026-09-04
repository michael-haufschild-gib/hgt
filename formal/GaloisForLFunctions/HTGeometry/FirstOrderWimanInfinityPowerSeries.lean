import GaloisForLFunctions.HTGeometry.FirstOrderWimanInfinityCancellation
import GaloisForLFunctions.HTGeometry.NewtonPuiseuxPrescribedEdgeRoot

/-!
# Power-series compiler for a signed Wiman edge at infinity

A rational infinity slope can contain poles.  This module clears that signed slope by substituting
`U = s⁻q` and `T = s⁻M Y`, then multiplying every term by a common power `sᴴ`.  It proves the
resulting object is a genuine polynomial over `ℂ⟦s⟧`, computes its exact degree, verifies the
Newton divisibility condition, and identifies the transformed special fibre coefficientwise with
the original Wiman edge polynomial.  Ambient monicity is never assumed.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

noncomputable section

/-- Cleared power-series polynomial obtained from the complete top symbol at `U = ∞`. -/
noncomputable def firstOrderInfinityPowerSeriesPolynomial
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H : ℕ) :
    (PowerSeries ℂ)[X] :=
  ∑ i ∈ firstOrderTopNewtonFace S A d,
    ∑ n ∈ (A i).support,
      Polynomial.C (PowerSeries.C ((A i).coeff n) *
        (PowerSeries.X : PowerSeries ℂ) ^ (H - (q * n + M * i.2))) *
          Polynomial.X ^ i.2

/-- Exact outer coefficient of the cleared infinity polynomial. -/
theorem coeff_firstOrderInfinityPowerSeriesPolynomial
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H k : ℕ) :
    (firstOrderInfinityPowerSeriesPolynomial S A d q M H).coeff k =
      ∑ i ∈ firstOrderTopNewtonFace S A d,
        ∑ n ∈ (A i).support,
          if k = i.2 then
            PowerSeries.C ((A i).coeff n) *
              (PowerSeries.X : PowerSeries ℂ) ^ (H - (q * n + M * i.2))
          else 0 := by
  classical
  rw [firstOrderInfinityPowerSeriesPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : k = i.2
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]
    simp

/-- Derivative exponents in the top face bound the polynomial degree. -/
theorem natDegree_firstOrderInfinityPowerSeriesPolynomial_le
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H m : ℕ)
    (hm : ∀ i ∈ firstOrderTopNewtonFace S A d, i.2 ≤ m) :
    (firstOrderInfinityPowerSeriesPolynomial S A d q M H).natDegree ≤ m := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_firstOrderInfinityPowerSeriesPolynomial]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro n hn
  rw [if_neg]
  intro hki
  subst k
  exact (Nat.not_lt_of_ge (hm i hi)) hk

/-- At a maximal derivative exponent the outer coefficient is exactly its coefficient row. -/
theorem coeff_firstOrderInfinityPowerSeriesPolynomial_of_maxDerivative
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H : ℕ)
    (i₀ : ℕ × ℕ) (hi₀ : i₀ ∈ firstOrderTopNewtonFace S A d) :
    (firstOrderInfinityPowerSeriesPolynomial S A d q M H).coeff i₀.2 =
      ∑ n ∈ (A i₀).support,
        PowerSeries.C ((A i₀).coeff n) *
          (PowerSeries.X : PowerSeries ℂ) ^ (H - (q * n + M * i₀.2)) := by
  classical
  rw [coeff_firstOrderInfinityPowerSeriesPolynomial]
  rw [Finset.sum_eq_single_of_mem i₀ hi₀]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos rfl]
  · intro i hi hne
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg]
    intro hsnd
    apply hne
    apply Prod.ext
    · have hiDeg := (Finset.mem_filter.mp hi).2.1
      have hi₀Deg := (Finset.mem_filter.mp hi₀).2.1
      omega
    · exact hsnd.symm

private theorem coeff_powerSeries_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff k (∑ n ∈ s, g n) = ∑ n ∈ s, PowerSeries.coeff k (g n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      simp only [Finset.sum_insert hn, ih, map_add]

/-- A nonzero maximal derivative row gives the exact outer polynomial degree. -/
theorem natDegree_firstOrderInfinityPowerSeriesPolynomial_eq_maxDerivative
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H : ℕ)
    (i₀ : ℕ × ℕ) (hi₀ : i₀ ∈ firstOrderTopNewtonFace S A d)
    (hm : ∀ i ∈ firstOrderTopNewtonFace S A d, i.2 ≤ i₀.2)
    (hq : q ≠ 0) (hbound : q * (A i₀).natDegree + M * i₀.2 ≤ H) :
    (firstOrderInfinityPowerSeriesPolynomial S A d q M H).natDegree = i₀.2 := by
  have hiA : A i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2.2
  have hcoeff :
      (firstOrderInfinityPowerSeriesPolynomial S A d q M H).coeff i₀.2 ≠ 0 := by
    rw [coeff_firstOrderInfinityPowerSeriesPolynomial_of_maxDerivative S A d q M H i₀ hi₀]
    intro hzero
    have hz := congrArg
      (PowerSeries.coeff (H - (q * (A i₀).natDegree + M * i₀.2))) hzero
    rw [coeff_powerSeries_finset_sum] at hz
    rw [Finset.sum_eq_single_of_mem (A i₀).natDegree
      (Polynomial.natDegree_mem_support_of_nonzero hiA)] at hz
    · rw [PowerSeries.coeff_C_mul_X_pow, if_pos rfl, Polynomial.coeff_natDegree] at hz
      have hlead : (A i₀).leadingCoeff = 0 := by simpa using hz
      exact (Polynomial.leadingCoeff_ne_zero.mpr hiA) hlead
    · intro n hn hne
      rw [PowerSeries.coeff_C_mul_X_pow, if_neg]
      intro heq
      have hnle := Polynomial.le_natDegree_of_mem_supp n hn
      have hnBound : q * n + M * i₀.2 ≤ H := by
        calc
          q * n + M * i₀.2 ≤ q * (A i₀).natDegree + M * i₀.2 := by gcongr
          _ ≤ H := hbound
      have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      let x := q * n + M * i₀.2
      let y := q * (A i₀).natDegree + M * i₀.2
      have hxle : x ≤ H := hnBound
      have hyle : y ≤ H := hbound
      have hsub : H - y = H - x := heq
      have hxy : x = y := by omega
      have hmul : q * n = q * (A i₀).natDegree := by
        apply Nat.add_right_cancel (m := M * i₀.2)
        exact hxy
      exact hne (Nat.mul_left_cancel hqpos hmul)
  apply le_antisymm
  · exact natDegree_firstOrderInfinityPowerSeriesPolynomial_le S A d q M H i₀.2 hm
  · exact Polynomial.le_natDegree_of_ne_zero hcoeff

/-- Row-wise Newton bounds give the exact divisibility required by the slope transform. -/
theorem X_pow_dvd_coeff_firstOrderInfinityPowerSeriesPolynomial
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H m a : ℕ)
    (hdegree : (firstOrderInfinityPowerSeriesPolynomial S A d q M H).natDegree = m)
    (hbound : ∀ i ∈ firstOrderTopNewtonFace S A d, ∀ n ∈ (A i).support,
      a * (m - i.2) ≤ H - (q * n + M * i.2)) :
    ∀ k ≤ (firstOrderInfinityPowerSeriesPolynomial S A d q M H).natDegree,
      (PowerSeries.X : PowerSeries ℂ) ^
          (a * ((firstOrderInfinityPowerSeriesPolynomial S A d q M H).natDegree - k)) ∣
        (firstOrderInfinityPowerSeriesPolynomial S A d q M H).coeff k := by
  intro k hk
  rw [hdegree]
  rw [PowerSeries.X_pow_dvd_iff]
  intro r hr
  rw [coeff_firstOrderInfinityPowerSeriesPolynomial]
  rw [coeff_powerSeries_finset_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [coeff_powerSeries_finset_sum]
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hki : k = i.2
  · rw [if_pos hki]
    rw [PowerSeries.coeff_C_mul_X_pow, if_neg]
    intro hre
    have hle : a * (m - k) ≤ H - (q * n + M * k) := by
      simpa [hki] using hbound i hi n hn
    have hre' : r = H - (q * n + M * k) := by simpa [hki] using hre
    rw [← hre'] at hle
    exact (Nat.not_le_of_lt hr) hle
  · rw [if_neg hki]
    exact map_zero (PowerSeries.coeff r)

/-- Coefficient formula for the slope-transformed special fibre. -/
theorem coeff_specialFiber_newtonTransform_firstOrderInfinityPowerSeriesPolynomial
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H m a k : ℕ)
    (hdegree : (firstOrderInfinityPowerSeriesPolynomial S A d q M H).natDegree = m)
    (hk : k ≤ m) :
    (((newtonTransform (firstOrderInfinityPowerSeriesPolynomial S A d q M H)
        a 1 one_ne_zero).map (PowerSeries.constantCoeff (R := ℂ))).coeff k) =
      ∑ i ∈ firstOrderTopNewtonFace S A d,
        ∑ n ∈ (A i).support,
          if k = i.2 ∧ H - (q * n + M * i.2) = a * (m - k)
          then (A i).coeff n else 0 := by
  rw [coeff_map_constantCoeff_newtonTransform]
  · rw [hdegree]
    rw [PowerSeries.coeff_expand]
    simp only [one_dvd, if_true, Nat.div_one]
    rw [coeff_firstOrderInfinityPowerSeriesPolynomial]
    rw [coeff_powerSeries_finset_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coeff_powerSeries_finset_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hki : k = i.2
    · rw [if_pos hki]
      rw [PowerSeries.coeff_C_mul_X_pow]
      by_cases he : a * (m - k) = H - (q * n + M * i.2)
      · rw [if_pos he, if_pos ⟨hki, he.symm⟩]
      · rw [if_neg he, if_neg]
        intro h
        exact he h.2.symm
    · rw [if_neg hki]
      simp [hki]
  · rw [hdegree]
    exact hk

/-- Natural-number boundary polynomial after signed-slope clearing. -/
noncomputable def firstOrderInfinityNaturalEdgePolynomial
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H m a : ℕ) :
    Polynomial ℂ :=
  ∑ i ∈ (firstOrderTopNewtonFace S A d).filter (fun i =>
      q * (A i).natDegree + M * i.2 + a * (m - i.2) = H),
    Polynomial.C (A i).leadingCoeff * Polynomial.X ^ i.2

/-- Every nonempty top-face subfamily has a nonzero edge polynomial. -/
theorem firstOrderNewtonEdgePolynomial_ne_zero_of_mem
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (face : Finset (ℕ × ℕ)) (hface : face ⊆ firstOrderTopNewtonFace S A d)
    (i₀ : ℕ × ℕ) (hi₀ : i₀ ∈ face) :
    firstOrderNewtonEdgePolynomial face A ≠ 0 := by
  classical
  intro hzero
  have hcoeff := congrArg (fun P : Polynomial ℂ => P.coeff i₀.2) hzero
  rw [firstOrderNewtonEdgePolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single_of_mem i₀ hi₀] at hcoeff
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
      mul_one] at hcoeff
    have hiTop := hface hi₀
    have hiA : A i₀ ≠ 0 := (Finset.mem_filter.mp hiTop).2.2
    exact (Polynomial.leadingCoeff_ne_zero.mpr hiA) hcoeff
  · intro i hi hne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro hsnd
    apply hne
    apply Prod.ext
    · have hiTop := hface hi
      have hi₀Top := hface hi₀
      have hiDeg := (Finset.mem_filter.mp hiTop).2.1
      have hi₀Deg := (Finset.mem_filter.mp hi₀Top).2.1
      omega
    · exact hsnd.symm

/-- Natural boundary and rational Newton-weight descriptions give the same edge polynomial. -/
theorem firstOrderInfinityNaturalEdgePolynomial_eq_newtonEdge
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H m a : ℕ)
    (p : ℝ) (w : ℝ)
    (hface : ∀ i ∈ firstOrderTopNewtonFace S A d,
      (q * (A i).natDegree + M * i.2 + a * (m - i.2) = H ↔
        firstOrderNewtonWeight A p i = w)) :
    firstOrderInfinityNaturalEdgePolynomial S A d q M H m a =
      firstOrderNewtonEdgePolynomial (firstOrderMaxNewtonFace S A d p w) A := by
  rw [firstOrderInfinityNaturalEdgePolynomial, firstOrderNewtonEdgePolynomial]
  apply Finset.sum_congr
  · ext i
    rw [firstOrderMaxNewtonFace]
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, heq⟩
      exact ⟨hi, (hface i hi).mp heq⟩
    · rintro ⟨hi, heq⟩
      exact ⟨hi, (hface i hi).mpr heq⟩
  · intro i hi
    rfl

private theorem specialFiber_inner_sum_eq
    (A : Polynomial ℂ) (q M H m a k : ℕ) (hq : q ≠ 0)
    (hbound : q * A.natDegree + M * k + a * (m - k) ≤ H) :
    (∑ n ∈ A.support,
      if H - (q * n + M * k) = a * (m - k) then A.coeff n else 0) =
      if q * A.natDegree + M * k + a * (m - k) = H
      then A.leadingCoeff else 0 := by
  classical
  by_cases hA : A = 0
  · subst A
    simp
  by_cases hb : q * A.natDegree + M * k + a * (m - k) = H
  · rw [if_pos hb]
    rw [Finset.sum_eq_single_of_mem A.natDegree
      (Polynomial.natDegree_mem_support_of_nonzero hA)]
    · rw [if_pos]
      · exact Polynomial.coeff_natDegree
      · have hbase : q * A.natDegree + M * k ≤ H := by omega
        apply (Nat.sub_eq_iff_eq_add' hbase).2
        omega
    · intro n hn hne
      rw [if_neg]
      intro heq
      have hnle := Polynomial.le_natDegree_of_mem_supp n hn
      have hxle : q * n + M * k ≤ H := by
        calc
          q * n + M * k ≤ q * A.natDegree + M * k := by gcongr
          _ ≤ H := by omega
      have hHn : H = a * (m - k) + (q * n + M * k) :=
        Nat.eq_add_of_sub_eq hxle heq
      have hmul : q * n = q * A.natDegree := by omega
      exact hne (Nat.mul_left_cancel (Nat.pos_of_ne_zero hq) hmul)
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg]
    intro heq
    have hnle := Polynomial.le_natDegree_of_mem_supp n hn
    have hxbase : q * n + M * k ≤ q * A.natDegree + M * k := by gcongr
    have hxle : q * n + M * k ≤ H := le_trans hxbase (by omega)
    have hHn : H = a * (m - k) + (q * n + M * k) :=
      Nat.eq_add_of_sub_eq hxle heq
    apply hb
    apply le_antisymm
    · exact hbound
    · omega

/-- The complete transformed special fibre is exactly the natural edge polynomial. -/
theorem specialFiber_newtonTransform_firstOrderInfinityPowerSeriesPolynomial
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H m a : ℕ)
    (hdegree : (firstOrderInfinityPowerSeriesPolynomial S A d q M H).natDegree = m)
    (hq : q ≠ 0)
    (hm : ∀ i ∈ firstOrderTopNewtonFace S A d, i.2 ≤ m)
    (hbound : ∀ i ∈ firstOrderTopNewtonFace S A d,
      q * (A i).natDegree + M * i.2 + a * (m - i.2) ≤ H) :
    (newtonTransform (firstOrderInfinityPowerSeriesPolynomial S A d q M H)
        a 1 one_ne_zero).map (PowerSeries.constantCoeff (R := ℂ)) =
      firstOrderInfinityNaturalEdgePolynomial S A d q M H m a := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ m
  · rw [coeff_specialFiber_newtonTransform_firstOrderInfinityPowerSeriesPolynomial
      S A d q M H m a k hdegree hk]
    rw [firstOrderInfinityNaturalEdgePolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hki : k = i.2
    · rw [if_pos hki]
      subst k
      simp only [true_and]
      rw [specialFiber_inner_sum_eq (A i) q M H m a i.2 hq (hbound i hi)]
      by_cases hb : q * (A i).natDegree + M * i.2 + a * (m - i.2) = H
      · rw [if_pos hb, if_pos hb, mul_one]
      · simp [hb]
    · rw [if_neg hki]
      simp [hki]
  · have hk' : m < k := Nat.lt_of_not_ge hk
    have hleft :
        (((newtonTransform (firstOrderInfinityPowerSeriesPolynomial S A d q M H)
          a 1 one_ne_zero).map (PowerSeries.constantCoeff (R := ℂ))).coeff k) = 0 := by
      rw [Polynomial.coeff_map, coeff_newtonTransform, if_neg]
      · simp
      · rw [hdegree]
        exact Nat.not_le.mpr hk'
    rw [hleft]
    rw [firstOrderInfinityNaturalEdgePolynomial, Polynomial.finsetSum_coeff]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro hki
    have hiTop := (Finset.mem_filter.mp hi).1
    have hile : i.2 ≤ m := hm i hiTop
    omega

end

end GaloisForLFunctions.HTGeometry
