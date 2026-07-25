import GaloisForLFunctions.HTGeometry.ShiftDefectRationalPole
import Mathlib

/-!
# The extremal obstruction at an orbit-isolated pole

A rational function `R` has a shift defect `sigma R - R` whose poles always include the *extremes*
of every shift orbit of poles of `R`: if `beta` is the largest pole of `R` in its orbit then
`R (X + 1)` is regular at `beta` while `R` is not, and symmetrically `gamma - 1` is a pole when
`gamma` is the smallest.

Consequently a rational function with **exactly one** pole in some shift orbit is never a shift
defect: the largest pole of `R` in that orbit would have to be that point, and the smallest would
have to be one step above it.
-/

open Polynomial

namespace HTGeometry

/-- The integers `k` for which `alpha + k` is a root of a nonzero polynomial form a finite set. -/
theorem finite_orbit_roots {B : ℂ[X]} (hB : B ≠ 0) (α : ℂ) :
    {k : ℤ | B.eval (α + (k : ℂ)) = 0}.Finite := by
  have hinj : Function.Injective (fun k : ℤ => α + (k : ℂ)) := by
    intro a b hab
    simp only at hab
    exact_mod_cast add_left_cancel hab
  have hroots : {z : ℂ | B.IsRoot z}.Finite := Polynomial.finite_setOf_isRoot hB
  exact Set.Finite.preimage hinj.injOn hroots

/-- **No shift defect has an isolated pole in a shift orbit.**  If the identity below holds with
`E` vanishing at `alpha` and at no other point of `alpha + Z`, with `q` not vanishing at `alpha`
and `K` positive, then `A / B` cannot exist. -/
theorem no_shift_defect_orbit_isolated
    {A B E q : ℂ[X]} (hB : B.Monic) (hcop : IsCoprime A B) {α : ℂ} {K : ℕ} (hK : 0 < K)
    (hEα : E.eval α = 0)
    (hEorb : ∀ k : ℤ, k ≠ 0 → E.eval (α + (k : ℂ)) ≠ 0)
    (hqα : q.eval α ≠ 0)
    (hid : (A.comp (X + 1) * B - A * B.comp (X + 1)) * E ^ K = q * (B.comp (X + 1) * B)) :
    False := by
  classical
  have hBne : B ≠ 0 := hB.ne_zero
  set S : Set ℤ := {k : ℤ | B.eval (α + (k : ℂ)) = 0} with hS
  have hSfin : S.Finite := finite_orbit_roots hBne α
  have hshift : ∀ (p : ℂ[X]) (z : ℂ), (p.comp (X + 1)).eval z = p.eval (z + 1) := by
    intro p z
    simp [Polynomial.eval_comp]
  by_cases hSempty : S = ∅
  · -- no pole of `A / B` in the orbit at all: the defect is regular there
    have h0 : B.eval (α + ((0 : ℤ) : ℂ)) ≠ 0 := by
      intro h
      exact absurd (show (0 : ℤ) ∈ S from h) (by rw [hSempty]; exact fun h => h)
    have h1 : B.eval (α + ((1 : ℤ) : ℂ)) ≠ 0 := by
      intro h
      exact absurd (show (1 : ℤ) ∈ S from h) (by rw [hSempty]; exact fun h => h)
    have hB0 : B.eval α ≠ 0 := by simpa using h0
    have hB1 : B.eval (α + 1) ≠ 0 := by simpa using h1
    have heval := congrArg (fun p : ℂ[X] => p.eval α) hid
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      hshift, hEα] at heval
    rw [zero_pow (by omega), mul_zero] at heval
    exact (mul_ne_zero hqα (mul_ne_zero hB1 hB0)) heval.symm
  · obtain ⟨k0, hk0⟩ := Set.nonempty_iff_ne_empty.mpr hSempty
    set T : Finset ℤ := hSfin.toFinset with hT
    have hTne : T.Nonempty := ⟨k0, by simpa [hT] using hk0⟩
    set kmax : ℤ := T.max' hTne with hkmax
    set kmin : ℤ := T.min' hTne with hkmin
    have hmaxS : B.eval (α + (kmax : ℂ)) = 0 := by
      have := T.max'_mem hTne
      simpa [hT, hS] using this
    have hminS : B.eval (α + (kmin : ℂ)) = 0 := by
      have := T.min'_mem hTne
      simpa [hT, hS] using this
    have hmaxTop : B.eval (α + ((kmax + 1 : ℤ) : ℂ)) ≠ 0 := by
      intro h
      have hmem : (kmax + 1) ∈ T := by simpa [hT, hS] using h
      have := T.le_max' _ hmem
      omega
    have hminBot : B.eval (α + ((kmin - 1 : ℤ) : ℂ)) ≠ 0 := by
      intro h
      have hmem : (kmin - 1) ∈ T := by simpa [hT, hS] using h
      have := T.min'_le _ hmem
      omega
    -- the largest pole of `A / B` in the orbit is a pole of the defect
    have hmaxzero : E.eval (α + (kmax : ℂ)) = 0 := by
      have heval := congrArg (fun p : ℂ[X] => p.eval (α + (kmax : ℂ))) hid
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
        hshift, hmaxS, mul_zero, zero_sub] at heval
      have hA : A.eval (α + (kmax : ℂ)) ≠ 0 := eval_num_ne_zero_of_isCoprime hcop hmaxS
      have hB1 : B.eval (α + (kmax : ℂ) + 1) ≠ 0 := by
        intro h
        refine hmaxTop ?_
        push_cast
        rw [← add_assoc]
        exact h
      have hprod : A.eval (α + (kmax : ℂ)) * B.eval (α + (kmax : ℂ) + 1)
          * E.eval (α + (kmax : ℂ)) ^ K = 0 := by
        linear_combination -heval
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h (mul_ne_zero hA hB1)
      · exact (pow_eq_zero_iff' (n := K)).mp h |>.1
    have hkmax0 : kmax = 0 := by
      by_contra hne
      exact hEorb kmax hne hmaxzero
    -- one step below the smallest pole is also a pole of the defect
    have hminzero : E.eval (α + ((kmin - 1 : ℤ) : ℂ)) = 0 := by
      have hcast : (α + ((kmin - 1 : ℤ) : ℂ)) + 1 = α + (kmin : ℂ) := by
        push_cast; ring
      have heval := congrArg (fun p : ℂ[X] => p.eval (α + ((kmin - 1 : ℤ) : ℂ))) hid
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
        hshift, hcast, hminS, mul_zero, sub_zero] at heval
      have hA : A.eval (α + (kmin : ℂ)) ≠ 0 := eval_num_ne_zero_of_isCoprime hcop hminS
      have hprod : A.eval (α + (kmin : ℂ)) * B.eval (α + ((kmin - 1 : ℤ) : ℂ))
          * E.eval (α + ((kmin - 1 : ℤ) : ℂ)) ^ K = 0 := by
        linear_combination heval
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h (mul_ne_zero hA hminBot)
      · exact (pow_eq_zero_iff' (n := K)).mp h |>.1
    have hkmin1 : kmin = 1 := by
      by_contra hne
      exact hEorb (kmin - 1) (by omega) hminzero
    have hle : kmin ≤ kmax := T.min'_le _ (T.max'_mem hTne)
    omega

end HTGeometry
