import GaloisForLFunctions.RHTower.PrimeSupportBoundaryJets
import GaloisForLFunctions.HTGeometry.PrimeWordSupportSelector

/-!
# Weighted prime-word ensemble tomography

The boundary-jet selector for one prime word extends linearly to every finite weighted word
ensemble.  Its derivative of order `r` extracts exactly the aggregate weight of words using
`r + 1` distinct labels, multiplied by an explicit nonzero signed factorial.

Consequently equality of all boundary jets is equivalent to equality of every positive
support-cardinality slice.  This is a finite source theorem, not an RH theorem: it supplies a
lossless support-stratified packet before a graph, code, or determinant construction is allowed
to specialize the source.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open Polynomial

/-- The linear marked deformation of a finite integer-weighted prime-word ensemble. -/
noncomputable def primeWordEnsembleDeformation {α : Type*} [DecidableEq α]
    (S : Finset (List α)) (a : List α → ℤ) : ℤ[X] :=
  ∑ w ∈ S, C (a w) *
    primeSupportMarkedDeformation (GaloisForLFunctions.primeWordSupport w).card

/-- Aggregate ensemble weight on the words with exactly `k` distinct labels. -/
def primeWordSupportWeightSlice {α : Type*} [DecidableEq α]
    (S : Finset (List α)) (a : List α → ℤ) (k : ℕ) : ℤ :=
  ∑ w ∈ S with (GaloisForLFunctions.primeWordSupport w).card = k, a w

/-- The `r`th boundary jet keeps precisely the `r + 1` support-cardinality stratum. -/
theorem primeWordEnsembleDeformation_boundaryJet {α : Type*} [DecidableEq α]
    (S : Finset (List α)) (a : List α → ℤ) (r : ℕ) :
    ((derivative^[r]) (primeWordEnsembleDeformation S a)).eval 1 =
      ∑ w ∈ S,
        if (GaloisForLFunctions.primeWordSupport w).card = r + 1 then
          a w * ((r + 1 : ℕ) : ℤ) * (-1 : ℤ) ^ r * (r.factorial : ℤ)
        else 0 := by
  rw [primeWordEnsembleDeformation, iterate_derivative_sum]
  rw [eval_finsetSum]
  simp_rw [iterate_derivative_C_mul, eval_C_mul]
  simp_rw [primeSupportMarkedDeformation_boundaryJet]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : (GaloisForLFunctions.primeWordSupport w).card = r + 1
  · rw [if_pos h, if_pos h, h]
    ring
  · rw [if_neg h, if_neg h]
    simp

/-- Factored tomography formula exposing the exact support-slice weight. -/
theorem primeWordEnsembleDeformation_boundaryJet_slice {α : Type*} [DecidableEq α]
    (S : Finset (List α)) (a : List α → ℤ) (r : ℕ) :
    ((derivative^[r]) (primeWordEnsembleDeformation S a)).eval 1 =
      ((r + 1 : ℕ) : ℤ) * (-1 : ℤ) ^ r * (r.factorial : ℤ) *
        primeWordSupportWeightSlice S a (r + 1) := by
  rw [primeWordEnsembleDeformation_boundaryJet]
  simp only [primeWordSupportWeightSlice, Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : (GaloisForLFunctions.primeWordSupport w).card = r + 1
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    simp

/-- Equality of one boundary jet forces equality of its corresponding weighted support slice. -/
theorem primeWordSupportWeightSlice_eq_of_boundaryJet_eq
    {α : Type*} [DecidableEq α]
    (S T : Finset (List α)) (a b : List α → ℤ) (r : ℕ)
    (hjet : ((derivative^[r]) (primeWordEnsembleDeformation S a)).eval 1 =
      ((derivative^[r]) (primeWordEnsembleDeformation T b)).eval 1) :
    primeWordSupportWeightSlice S a (r + 1) =
      primeWordSupportWeightSlice T b (r + 1) := by
  rw [primeWordEnsembleDeformation_boundaryJet_slice,
    primeWordEnsembleDeformation_boundaryJet_slice] at hjet
  have hr : (((r + 1 : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero r
  have hsign : ((-1 : ℤ) ^ r) ≠ 0 := pow_ne_zero r (by norm_num)
  have hfactorial : ((r.factorial : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero r
  exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hr hsign) hfactorial) hjet

/-- The complete boundary germ determines every positive support-cardinality aggregate. -/
theorem primeWordSupportWeightSlices_eq_of_all_boundaryJets_eq
    {α : Type*} [DecidableEq α]
    (S T : Finset (List α)) (a b : List α → ℤ)
    (hjet : ∀ r : ℕ,
      ((derivative^[r]) (primeWordEnsembleDeformation S a)).eval 1 =
        ((derivative^[r]) (primeWordEnsembleDeformation T b)).eval 1)
    {k : ℕ} (hk : 0 < k) :
    primeWordSupportWeightSlice S a k = primeWordSupportWeightSlice T b k := by
  have h := primeWordSupportWeightSlice_eq_of_boundaryJet_eq
    S T a b (k - 1) (hjet (k - 1))
  have hk' : 1 ≤ k := hk
  simpa only [Nat.sub_add_cancel hk'] using h

end GaloisForLFunctions.RHTower
