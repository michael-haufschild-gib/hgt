import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionFourierResolution
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic

/-!
# Detection by residue Newton coefficients

The binomial transform is triangular in total degree. A nonzero finite
coefficient array has a maximal monomial whose Newton coefficient is exactly
its original coefficient. Consequently, orders up to the degree detect every
array. Residues are independent labels; no analytic jet identification is
assumed.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {ρ ι : Type*} [DecidableEq ρ] [Fintype ι]

/-- Total order of a finite-coordinate multiindex. -/
def newtonOrder (a : ι → ℕ) : ℕ := ∑ i, a i

/-- Highest quotient degree occurring in a finite residue array. -/
def newtonDegree (c : (ρ × (ι → ℕ)) →₀ ℂ) : ℕ :=
  c.support.sup fun v => newtonOrder v.2

/-- The coefficient of `Yᵃ` in the residue component `Σₖ c(r,k) ∏ᵢ (1+Yᵢ)^kᵢ`. -/
def residueNewtonCoefficient (c : (ρ × (ι → ℕ)) →₀ ℂ) (r : ρ) (a : ι → ℕ) : ℂ :=
  ∑ v ∈ c.support with v.1 = r, c v * ∏ i, ((v.2 i).choose (a i) : ℂ)

private theorem multiindex_eq_of_le_of_order_le {a b : ι → ℕ}
    (hab : ∀ i, a i ≤ b i) (hsum : newtonOrder b ≤ newtonOrder a) : a = b := by
  have hsum' : (∑ i, a i) = ∑ i, b i :=
    le_antisymm (Finset.sum_le_sum fun i _ => hab i) hsum
  have he := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (univ : Finset ι)) => hab i)).mp hsum'
  exact funext fun i => he i (mem_univ i)

/-- A maximal nonzero quotient monomial is read unchanged by its own Newton coefficient. -/
theorem exists_top_residueNewtonCoefficient (c : (ρ × (ι → ℕ)) →₀ ℂ) (hc : c ≠ 0) :
    ∃ v ∈ c.support, newtonOrder v.2 = newtonDegree c ∧
      residueNewtonCoefficient c v.1 v.2 = c v := by
  classical
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image c.support
    (fun v => newtonOrder v.2) (Finsupp.support_nonempty_iff.mpr hc)
  refine ⟨v, hv, ?_, ?_⟩
  · apply le_antisymm
    · exact Finset.le_sup (f := fun w => newtonOrder w.2) hv
    · exact Finset.sup_le hmax
  · unfold residueNewtonCoefficient
    rw [Finset.sum_eq_single v]
    · simp only [Nat.choose_self, Nat.cast_one, Finset.prod_const_one, mul_one]
    · intro w hw hwv
      obtain ⟨hws, hwr⟩ := mem_filter.mp hw
      have hnot : ¬ ∀ i, v.2 i ≤ w.2 i := by
        intro hle
        have he := multiindex_eq_of_le_of_order_le hle (hmax w hws)
        exact hwv (Prod.ext hwr he.symm)
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      have hz : (∏ j, ((w.2 j).choose (v.2 j) : ℂ)) = 0 :=
        Finset.prod_eq_zero (mem_univ i) (by rw [Nat.choose_eq_zero_of_lt hi, Nat.cast_zero])
      rw [hz, mul_zero]
    · intro hvnot
      exact (hvnot (mem_filter.mpr ⟨hv, rfl⟩)).elim

/-- Finite Newton coordinates have no nonzero kernel; a detecting order never exceeds the degree. -/
theorem residueNewton_vanishing_iff (c : (ρ × (ι → ℕ)) →₀ ℂ) :
    (∀ r a, newtonOrder a ≤ newtonDegree c → residueNewtonCoefficient c r a = 0) ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨v, hv, hdeg, hval⟩ := exists_top_residueNewtonCoefficient c hc
    have hz := h v.1 v.2 hdeg.le
    rw [hval] at hz
    exact (Finsupp.mem_support_iff.mp hv) hz
  · intro hc r a _
    subst c
    simp only [residueNewtonCoefficient, Finsupp.support_zero, filter_empty, sum_empty]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
