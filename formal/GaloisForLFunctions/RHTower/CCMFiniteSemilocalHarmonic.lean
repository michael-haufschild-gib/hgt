import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite harmonic coefficients in the CCM semilocal moment expansion

Connes--Consani--Moscovici, equation (49), introduces

`p_ell(m) = sum_k 2^(3 k) binom(m,k) binom(ell,k) / binom(2 k,k)`.

This file records that literal finite coefficient over `ℚ`, proves the source formula is symmetric
in its two discrete indices, and isolates its finite support.  These are the algebraic inputs to
the rank-one Lambert coefficients and the Catalan-integrality theorem (Lemma 5.5).  No spectral
limit, positivity statement, or RH assumption is used here.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The `k`th summand in CCM equation (49). -/
def ccmFiniteSemilocalHarmonicTerm (ell m k : ℕ) : ℚ :=
  (2 : ℚ) ^ (3 * k) * (m.choose k : ℚ) * (ell.choose k : ℚ) /
    (Nat.centralBinom k : ℚ)

/-- CCM's finite harmonic polynomial value `p_ell(m)` from equation (49). -/
def ccmFiniteSemilocalHarmonic (ell m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (ell + 1), ccmFiniteSemilocalHarmonicTerm ell m k

private theorem ccmFiniteSemilocalHarmonicTerm_eq_zero_of_lt
    {ell m k : ℕ} (h : ell < k) :
    ccmFiniteSemilocalHarmonicTerm ell m k = 0 := by
  simp [ccmFiniteSemilocalHarmonicTerm, Nat.choose_eq_zero_of_lt h]

/-- Equation (49) can be summed over the symmetric common finite support. -/
theorem ccmFiniteSemilocalHarmonic_eq_sum_range_max (ell m : ℕ) :
    ccmFiniteSemilocalHarmonic ell m =
      ∑ k ∈ Finset.range (max ell m + 1),
        ccmFiniteSemilocalHarmonicTerm ell m k := by
  unfold ccmFiniteSemilocalHarmonic
  rw [Finset.sum_subset]
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hkn
    simp only [Finset.mem_range] at hk hkn
    exact ccmFiniteSemilocalHarmonicTerm_eq_zero_of_lt (by omega)

/-- CCM equation (49) is symmetric: `p_ell(m) = p_m(ell)`. -/
theorem ccmFiniteSemilocalHarmonic_symm (ell m : ℕ) :
    ccmFiniteSemilocalHarmonic ell m = ccmFiniteSemilocalHarmonic m ell := by
  rw [ccmFiniteSemilocalHarmonic_eq_sum_range_max,
    ccmFiniteSemilocalHarmonic_eq_sum_range_max, max_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [ccmFiniteSemilocalHarmonicTerm]
  ring

/-- The zeroth harmonic is the constant coefficient one. -/
@[simp] theorem ccmFiniteSemilocalHarmonic_zero_left (m : ℕ) :
    ccmFiniteSemilocalHarmonic 0 m = 1 := by
  unfold ccmFiniteSemilocalHarmonic ccmFiniteSemilocalHarmonicTerm
  norm_num

/-- The value at zero is one, by the symmetry of the source coefficient. -/
@[simp] theorem ccmFiniteSemilocalHarmonic_zero_right (ell : ℕ) :
    ccmFiniteSemilocalHarmonic ell 0 = 1 := by
  rw [ccmFiniteSemilocalHarmonic_symm]
  exact ccmFiniteSemilocalHarmonic_zero_left ell

/-- Values outside the common support do not contribute to the finite harmonic coefficient. -/
theorem ccmFiniteSemilocalHarmonicTerm_eq_zero_of_max_lt
    {ell m k : ℕ} (h : max ell m < k) :
    ccmFiniteSemilocalHarmonicTerm ell m k = 0 :=
  ccmFiniteSemilocalHarmonicTerm_eq_zero_of_lt (lt_of_le_of_lt (le_max_left _ _) h)

/-- Rational values represented by an actual integer. -/
def CCMRationalIntegral (q : ℚ) : Prop := ∃ z : ℤ, q = z

/-- Lemma 5.5(iii) is a formal consequence of Lemma 5.5(ii), once the
symmetry of equation (49) is retained.  Thus the remaining arithmetic core is
the termwise central-binomial divisibility used to establish (ii); no separate
integrality proof for the quadratic coefficient is needed. -/
theorem ccmFiniteSemilocalHarmonic_sigma_integral_of_scaled_integral
    (hscaled : ∀ ell m : ℕ,
      CCMRationalIntegral ((Nat.centralBinom ell : ℚ) * ccmFiniteSemilocalHarmonic ell m))
    (ell m : ℕ) :
    CCMRationalIntegral
      ((Nat.centralBinom ell : ℚ) * (Nat.centralBinom m : ℚ) *
        ccmFiniteSemilocalHarmonic ell m ^ (2 : ℕ)) := by
  obtain ⟨a, ha⟩ := hscaled ell m
  obtain ⟨b, hb⟩ := hscaled m ell
  refine ⟨a * b, ?_⟩
  calc
    (Nat.centralBinom ell : ℚ) * (Nat.centralBinom m : ℚ) *
        ccmFiniteSemilocalHarmonic ell m ^ (2 : ℕ) =
        ((Nat.centralBinom ell : ℚ) * ccmFiniteSemilocalHarmonic ell m) *
          ((Nat.centralBinom m : ℚ) * ccmFiniteSemilocalHarmonic m ell) := by
            rw [ccmFiniteSemilocalHarmonic_symm]
            ring
    _ = (a : ℚ) * (b : ℚ) := by rw [ha, hb]
    _ = ((a * b : ℤ) : ℚ) := by norm_num

end

end RHTower
