import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationProducts
import GaloisForLFunctions.HTGeometry.Arithmetic.IntegralResidue

/-!
# A single branch contact determines local twist parity

If the distances from one root to all other roots are units, positive
contact with that root makes every other linear factor a unit. The
product has exactly that contact order. On a quadratic twist its parity
is therefore the parity of the twist parameter, so odd contact forces
the contact prime to divide every integral twisting parameter.
-/

namespace GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic

open HTGeometry HTGeometry.Arithmetic

variable {p : ℕ} [Fact p.Prime]

/-- Positive contact with one point excludes contact with a point at
unit distance from it. -/
theorem branchContact_other_unit {x a b : ℚ} (hab : IsPadicUnit p (a - b))
    (hx : 0 < padicValRat p (x - a)) : IsPadicUnit p (x - b) := by
  have hxa : x - a ≠ 0 := by intro h; simp [h] at hx
  have habval := (padicValRat_eq_zero_iff hab.ne_zero).mpr hab
  have hne : padicValRat p (x - a) ≠ padicValRat p (a - b) := by
    rw [habval]
    omega
  have hsum := add_ne_zero_of_val_ne hne
  have heq : x - b = (x - a) + (a - b) := by ring
  rw [heq]
  apply (padicValRat_eq_zero_iff hsum).mp
  rw [padicValRat.add_eq_min hsum hxa hab.ne_zero hne, habval, min_eq_right hx.le]

/-- The split polynomial has exactly the order of its unique positive
branch contact. Only separation from the contacted root is required. -/
theorem branchContact_product_val {ι : Type*} (s : Finset ι) (a : ι → ℚ)
    {j : ι} (hj : j ∈ s) {x : ℚ} (hx : 0 < padicValRat p (x - a j))
    (hsep : ∀ i ∈ s, i ≠ j → IsPadicUnit p (a j - a i)) :
    (∏ i ∈ s, (x - a i)) ≠ 0 ∧
      padicValRat p (∏ i ∈ s, (x - a i)) = padicValRat p (x - a j) ∧
        ∀ i ∈ s, i ≠ j → IsPadicUnit p (x - a i) := by
  classical
  have hother : ∀ i ∈ s, i ≠ j → IsPadicUnit p (x - a i) :=
    fun i hi hij => branchContact_other_unit (hsep i hi hij) hx
  have hne : ∀ i ∈ s, x - a i ≠ 0 := by
    intro i hi
    by_cases hij : i = j
    · subst i
      intro h
      simp [h] at hx
    · exact (hother i hi hij).ne_zero
  refine ⟨Finset.prod_ne_zero_iff.mpr hne, ?_, hother⟩
  rw [val_finset_prod s _ hne, Finset.sum_eq_single j]
  · intro i hi hij
    exact (padicValRat_eq_zero_iff (hne i hi)).mpr (hother i hi hij)
  · intro hnot
    exact (hnot hj).elim

/-- The contacted branch is the only branch with positive contact. -/
theorem branchContact_unique {ι : Type*} (s : Finset ι) (a : ι → ℚ)
    {j : ι} (hj : j ∈ s) {x : ℚ} (hx : 0 < padicValRat p (x - a j))
    (hsep : ∀ i ∈ s, i ≠ j → IsPadicUnit p (a j - a i)) :
    ∀ i ∈ s, 0 < padicValRat p (x - a i) ↔ i = j := by
  intro i hi
  constructor
  · intro hpos
    by_contra hij
    have hu := (branchContact_product_val s a hj hx hsep).2.2 i hi hij
    have hz := (padicValRat_eq_zero_iff hu.ne_zero).mpr hu
    omega
  · rintro rfl
    exact hx

/-- The contact order and the twisting parameter have exactly the same
valuation parity on a quadratic cover. -/
theorem branchContact_twist_parity {ι : Type*} (s : Finset ι) (a : ι → ℚ)
    {j : ι} (hj : j ∈ s) {x y d : ℚ} (hd : d ≠ 0)
    (hx : 0 < padicValRat p (x - a j))
    (hsep : ∀ i ∈ s, i ≠ j → IsPadicUnit p (a j - a i))
    (hcurve : y ^ 2 = d * ∏ i ∈ s, (x - a i)) :
    Even (padicValRat p d) ↔ Even (padicValRat p (x - a j)) := by
  obtain ⟨hprod, hval, _⟩ := branchContact_product_val s a hj hx hsep
  have hv := congrArg (padicValRat p) hcurve
  rw [padicValRat.pow, padicValRat.mul hd hprod, hval] at hv
  rw [Int.even_iff, Int.even_iff]
  omega

/-- At a good branch-contact prime, odd contact forces divisibility of
every nonzero integral twisting parameter. -/
theorem odd_branchContact_dvd_integer_twist {ι : Type*} (s : Finset ι) (a : ι → ℚ)
    {j : ι} (hj : j ∈ s) {x y : ℚ} {d : ℤ} (hd : d ≠ 0)
    (hx : 0 < padicValRat p (x - a j))
    (hodd : ¬ Even (padicValRat p (x - a j)))
    (hsep : ∀ i ∈ s, i ≠ j → IsPadicUnit p (a j - a i))
    (hcurve : y ^ 2 = (d : ℚ) * ∏ i ∈ s, (x - a i)) : p ∣ d.natAbs := by
  have hparity := branchContact_twist_parity s a hj (Int.cast_ne_zero.mpr hd) hx hsep hcurve
  by_contra hnd
  have hv : padicValRat p (d : ℚ) = 0 := by
    rw [padicValRat.of_int]
    change (padicValNat p d.natAbs : ℤ) = 0
    rw [padicValNat.eq_zero_of_not_dvd hnd]
    rfl
  exact hodd (hparity.mp (hv ▸ Even.zero))

/-- Integer branch differences are units away from their prime divisors. -/
theorem integer_branch_separation {ι : Type*} (s : Finset ι) (a : ι → ℤ) (j : ι)
    (hsep : ∀ i ∈ s, i ≠ j → ¬ p ∣ (a j - a i).natAbs) :
    ∀ i ∈ s, i ≠ j → IsPadicUnit p ((a j : ℚ) - (a i : ℚ)) := by
  intro i hi hij
  have hcast : ((a j - a i : ℤ) : ZMod p) ≠ 0 := by
    rw [intCast_zmod_ne_zero_iff]
    exact fun h => hsep i hi hij (Int.natCast_dvd.mp h)
  simpa only [Int.cast_sub] using isPadicUnit_intCast hcast

#print axioms branchContact_product_val
#print axioms odd_branchContact_dvd_integer_twist

end GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic
