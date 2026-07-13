import GaloisForLFunctions.HTGeometry.ExponentialSumDA

/-!
# Trigonometric linear carriers are differentially algebraic

`s ↦ cos(c·s)` and `s ↦ sin(c·s)` are differentially algebraic (they satisfy the order-2 equation
`y'' + c²·y = 0`).  These are the **trigonometric reflection carriers** that appear when a signed
Gamma product includes negative-slope (reflected) factors
(`signed-archimedean-gamma-orbit-charge-phase-law`, §1, §10 attack 6): reflection converts negative
slopes into positive-slope Gamma ratios plus trigonometric factors, and this shows those factors stay
inside the differentially-algebraic class.

The proof reuses `differentiallyAlgebraic_finset_expSum`: `cos(cs) = ½e^{ics} + ½e^{-ics}` and
`sin(cs) = (i/2)e^{-ics} − (i/2)e^{ics}` are two-term exponential sums.
-/

open GaloisForLFunctions

namespace GaloisForLFunctions

/-- **`cos(c·s)` is differentially algebraic** — the two-term exponential sum `½e^{ics} + ½e^{-ics}`. -/
theorem differentiallyAlgebraic_cos_linear (c : ℂ) :
    DifferentiallyAlgebraic (fun s => Complex.cos (c * s)) := by
  have hrw : (fun s => Complex.cos (c * s))
      = fun s => ∑ i ∈ ({0, 1} : Finset ℕ), (fun _ : ℕ => (1 / 2 : ℂ)) i
          * Complex.exp ((fun i : ℕ => if i = 0 then c * Complex.I else -(c * Complex.I)) i * s) := by
    funext s
    rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    simp only [if_true, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    rw [Complex.cos, show c * Complex.I * s = c * s * Complex.I by ring,
      show -(c * Complex.I) * s = -(c * s) * Complex.I by ring]
    ring
  rw [hrw]
  exact differentiallyAlgebraic_finset_expSum _ _ _

/-- **`sin(c·s)` is differentially algebraic** — the two-term exponential sum
`(i/2)e^{-ics} − (i/2)e^{ics}`. -/
theorem differentiallyAlgebraic_sin_linear (c : ℂ) :
    DifferentiallyAlgebraic (fun s => Complex.sin (c * s)) := by
  have hrw : (fun s => Complex.sin (c * s))
      = fun s => ∑ i ∈ ({0, 1} : Finset ℕ),
          (fun i : ℕ => if i = 0 then (Complex.I / 2) else -(Complex.I / 2)) i
          * Complex.exp ((fun i : ℕ => if i = 0 then -(c * Complex.I) else c * Complex.I) i * s) := by
    funext s
    rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    simp only [if_true, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    rw [Complex.sin, show -(c * Complex.I) * s = -(c * s) * Complex.I by ring,
      show c * Complex.I * s = c * s * Complex.I by ring]
    ring
  rw [hrw]
  exact differentiallyAlgebraic_finset_expSum _ _ _

end GaloisForLFunctions
