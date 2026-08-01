import GaloisForLFunctions.HTGeometry.StandardRationalExpansion
import GaloisForLFunctions.HTGeometry.LineAsymptoticScale

/-!
# The datum of a standard rational function

A nonzero standard rational function has an exact leading behaviour on a vertical line: with
numerator degree `d` and denominator length `d + p`,

`s^p · P(s)/∏_j(s+j) → leadingCoeff P`.

Both factors are elementary — a polynomial divided by its degree power tends to its leading
coefficient, and a shift product divided by its length power tends to `1` — so the datum of a
standard rational function is read off its numerator.

This is the extraction step of the residue law: once a jet polynomial is approximated by a standard
rational function, its datum is that function's datum.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- The reciprocal of a vertical point tends to zero. -/
theorem tendsto_inv_vertical (σ : ℝ) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm := (tendsto_norm_vertical σ).inv_tendsto_atTop
  refine hnorm.congr fun t => ?_
  rw [norm_inv]
  rfl

/-- A polynomial against its degree power tends to its leading coefficient. -/
theorem tendsto_polynomial_mul_inv_pow (σ : ℝ) (P : Polynomial ℂ) :
    Tendsto (fun t : ℝ => P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ P.natDegree)
      atTop (nhds P.leadingCoeff) := by
  have hinv := tendsto_inv_vertical σ
  have hterm : ∀ i ∈ Finset.range (P.natDegree + 1),
      Tendsto (fun t : ℝ => P.coeff i * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ (P.natDegree - i))
        atTop (nhds (if i = P.natDegree then P.coeff i else 0)) := by
    intro i hi
    by_cases hEq : i = P.natDegree
    · rw [if_pos hEq, hEq]
      simp only [Nat.sub_self, pow_zero, mul_one]
      exact tendsto_const_nhds
    · rw [if_neg hEq]
      have hlt : i < P.natDegree := by
        have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        omega
      obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
      rw [hk]
      have hpow : Tendsto (fun t : ℝ => (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ (k + 1))
          atTop (nhds 0) := by
        have := hinv.pow (k + 1)
        simpa using this
      have := hpow.const_mul (P.coeff i)
      simpa using this
  have hsum := tendsto_finsetSum (Finset.range (P.natDegree + 1)) hterm
  have hval : (∑ i ∈ Finset.range (P.natDegree + 1),
      if i = P.natDegree then P.coeff i else 0) = P.leadingCoeff := by
    rw [Finset.sum_ite_eq' (Finset.range (P.natDegree + 1)) P.natDegree P.coeff,
      if_pos (Finset.self_mem_range_succ P.natDegree)]
    rfl
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_vertical_ne_zero σ] with t hzero
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hle : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsub : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ i
      * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ P.natDegree
      = (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ (P.natDegree - i) := by
    have hpow : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ P.natDegree
        = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ i
          * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (P.natDegree - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [inv_pow, inv_pow, hpow, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero i hzero), one_mul]
  rw [← hsub]
  ring

/-- A shift product against its length power tends to one. -/
theorem tendsto_shiftProd_mul_inv_pow (σ : ℝ) (l : Multiset ℕ) :
    Tendsto (fun t : ℝ => shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)
        * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ Multiset.card l)
      atTop (nhds 1) := by
  induction l using Multiset.induction_on with
  | empty => simp [shiftProd]
  | cons j l ih =>
    have hone : Tendsto (fun t : ℝ => (((σ : ℂ) + (t : ℂ) * Complex.I) + (j : ℂ))
        * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) atTop (nhds 1) := by
      have hj : Tendsto (fun t : ℝ => (j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹)
          atTop (nhds 0) := by
        have := (tendsto_inv_vertical σ).const_mul (j : ℂ)
        simpa using this
      have hself : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)
          * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) atTop (nhds 1) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_vertical_ne_zero σ] with t ht
        rw [mul_inv_cancel₀ ht]
      have := hself.add hj
      rw [add_zero] at this
      refine this.congr fun t => ?_
      ring
    have hmul := hone.mul ih
    rw [one_mul] at hmul
    refine hmul.congr fun t => ?_
    have hexp : shiftProd (j ::ₘ l) ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ((σ : ℂ) + (t : ℂ) * Complex.I + (j : ℂ))
          * shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I) := by
      rw [shiftProd, Multiset.map_cons, Multiset.prod_cons, ← shiftProd]
    rw [hexp, Multiset.card_cons, pow_succ]
    ring

/-- **The datum of a nonzero standard rational function.** -/
theorem tendsto_stdRat_datum (hσ : 0 < σ) (P : Polynomial ℂ) (l : Multiset ℕ) (p : ℕ)
    (hcard : Multiset.card l = P.natDegree + p) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
        * (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)))
      atTop (nhds P.leadingCoeff) := by
  have hnum := tendsto_polynomial_mul_inv_pow σ P
  have hden := tendsto_shiftProd_mul_inv_pow σ l
  have hdenne : (1 : ℂ) ≠ 0 := one_ne_zero
  have hquot := hnum.div hden hdenne
  rw [div_one] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_vertical_ne_zero σ] with t ht
  have hden0 : shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    refine shiftProd_ne_zero ?_ l
    simpa using hσ
  show (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ P.natDegree)
      / (shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)
        * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ Multiset.card l)
    = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
      * (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I))
  rw [hcard, pow_add]
  field_simp
  rw [div_pow, one_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero p ht), mul_one]

end GaloisForLFunctions
