import GaloisForLFunctions.RHTower.ConnesLocalFieldSymbol
import GaloisForLFunctions.RHTower.ConnesLocalShellAbstract

/-!
# §V (30) at a non-archimedean place: the window mass is a shell count

§V (29)-(30) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

After the substitution `u = xξ` of (30), the trace integral is weighted by the multiplicative mass
of the window `|u|/Λ ≤ |x| ≤ Λ`, which at the archimedean place is `2 log' Λ − log|u|`.  At a
non-archimedean place the module `|x|` takes the discrete values `q^{-n}`, so the window is a
finite range of shells and its mass is simply the *number* of shells it contains — the boundary
terms that `log'` exists to handle are exactly the endpoints of that integer range.

`ConnesLocalShellAbstract` supplies the shell decomposition (`count ⊗ ν` on
`Multiplicative ℤ × U`); this module computes the window mass in it.  Nothing is assumed about the
residue field, so the statement holds at every non-archimedean place of every local field.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {U : Type*} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν]

/-- The indicator of the shell window `A ≤ n ≤ B`. -/
def connesShellWindow (A B : ℤ) : ℤ → ℂ := fun m => if m ∈ Finset.Icc A B then 1 else 0

theorem connesShellWindow_eq_zero {A B : ℤ} {m : ℤ} (hm : m ∉ Finset.Icc A B) :
    connesShellWindow A B m = 0 := by
  rw [connesShellWindow, if_neg hm]

theorem connesShellWindow_summable (A B : ℤ) :
    Summable fun m : ℤ => ‖connesShellWindow A B m‖ := by
  refine summable_of_ne_finset_zero (s := Finset.Icc A B) fun m hm => ?_
  rw [connesShellWindow_eq_zero hm, norm_zero]

/-- **§V (30) at a non-archimedean place.**  The multiplicative mass of a shell window is the
number of shells it contains. -/
theorem connes_shell_window_mass (A B : ℤ) :
    (∫ z, connesShellRadial (connesShellWindow A B) z ∂(connesShellMeasure ν))
      = ((Finset.Icc A B).card : ℂ) := by
  rw [connes_shell_radial_integral ν (connesShellWindow_summable A B)]
  rw [tsum_eq_sum (s := Finset.Icc A B) fun m hm => connesShellWindow_eq_zero hm]
  have hsum : (∑ m ∈ Finset.Icc A B, connesShellWindow A B m)
      = ∑ _m ∈ Finset.Icc A B, (1 : ℂ) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [connesShellWindow, if_pos hm]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The symmetric window `−N ≤ n ≤ N` — the non-archimedean form of `2 log' Λ` — has mass
`2N + 1`. -/
theorem connes_shell_symmetricWindow_mass (N : ℕ) :
    (∫ z, connesShellRadial (connesShellWindow (-(N : ℤ)) (N : ℤ)) z
        ∂(connesShellMeasure ν))
      = ((2 * N + 1 : ℕ) : ℂ) := by
  rw [connes_shell_window_mass ν]
  congr 1
  rw [Int.card_Icc]
  simp only [sub_neg_eq_add]
  omega

end

end GaloisForLFunctions.RHTower
