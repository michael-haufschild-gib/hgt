import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Inverse energies reverse a form comparison

For a positive semidefinite symmetric form `b` and a vector `w`, completing the square gives the
variational bound

`2 b(w,x) - b(x,x) ≤ b(w,w)`   for every `x`,

with equality at `x = w`.  So `b(w,w)` is the supremum of the affine functional it represents.
Two forms representing the *same* functional therefore compare in the direction opposite to the
forms themselves: if `c·b_S ≤ b_T` pointwise on the diagonal, then

`b_T(w_T,w_T) ≤ b_S(w_S,w_S)/c`.

No functional calculus, spectral theorem, or completeness is used — only the square completion.
This is the elementary replacement for "quadratic-form functional calculus" in a resolvent-energy
comparison, and it applies verbatim to both directions of a two-sided form bound.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The variational bound of a positive semidefinite form.**  Completing the square. -/
theorem psd_variational {b : V → V → ℝ}
    (hsymm : ∀ x y, b x y = b y x)
    (hadd : ∀ x y z, b (x + y) z = b x z + b y z)
    (hsmul : ∀ (t : ℝ) (x y : V), b (t • x) y = t * b x y)
    (hpsd : ∀ x, 0 ≤ b x x) (w x : V) :
    2 * b w x - b x x ≤ b w w := by
  have hadd₂ : ∀ p q r : V, b p (q + r) = b p q + b p r := by
    intro p q r
    rw [hsymm, hadd, hsymm q p, hsymm r p]
  have hsmul₂ : ∀ (t : ℝ) (p q : V), b p (t • q) = t * b p q := by
    intro t p q
    rw [hsymm, hsmul, hsymm q p]
  have hexp : b (x + (-1 : ℝ) • w) (x + (-1 : ℝ) • w)
      = b x x - 2 * b w x + b w w := by
    rw [hadd, hsmul, hadd₂, hadd₂, hsmul₂, hsmul₂, hsymm x w]
    ring
  have := hpsd (x + (-1 : ℝ) • w)
  rw [hexp] at this
  linarith

/-- **Inverse energies reverse a form comparison.**  If two symmetric forms represent the same
linear functional through `w_T` and `w_S`, and `c·b_S ≤ b_T` on the diagonal, then the represented
energies compare in the opposite direction with the reciprocal constant. -/
theorem energy_le_of_form_le {bT bS : V → V → ℝ} {wT wS : V} {c : ℝ} (hc : 0 < c)
    (hSsymm : ∀ x y, bS x y = bS y x)
    (hSadd : ∀ x y z, bS (x + y) z = bS x z + bS y z)
    (hSsmul : ∀ (t : ℝ) (x y : V), bS (t • x) y = t * bS x y)
    (hSpsd : ∀ x, 0 ≤ bS x x)
    (hrep : ∀ x, bT wT x = bS wS x)
    (hcomp : ∀ x, c * bS x x ≤ bT x x) :
    bT wT wT ≤ bS wS wS / c := by
  have hsmul₂ : ∀ (t : ℝ) (p q : V), bS p (t • q) = t * bS p q := by
    intro t p q
    rw [hSsymm, hSsmul, hSsymm q p]
  have hvar := psd_variational hSsymm hSadd hSsmul hSpsd wS (c • wT)
  rw [hsmul₂, hSsmul, hsmul₂] at hvar
  -- `bS wS wT` is the represented energy
  have hrepT : bT wT wT = bS wS wT := hrep wT
  have hdiag : c * bS wT wT ≤ bT wT wT := hcomp wT
  rw [← hrepT] at hvar
  have hstep : c * (bT wT wT) ≤ 2 * (c * bT wT wT) - c * (c * bS wT wT) := by
    nlinarith [hdiag, hc]
  rw [le_div_iff₀ hc]
  nlinarith [hvar, hstep, hc]

/-- The two-sided form of the same statement: a form dominated by `c·b_S` has the larger
represented energy. -/
theorem le_energy_of_form_le {bT bS : V → V → ℝ} {wT wS : V} {c : ℝ} (hc : 0 < c)
    (hTsymm : ∀ x y, bT x y = bT y x)
    (hTadd : ∀ x y z, bT (x + y) z = bT x z + bT y z)
    (hTsmul : ∀ (t : ℝ) (x y : V), bT (t • x) y = t * bT x y)
    (hTpsd : ∀ x, 0 ≤ bT x x)
    (hrep : ∀ x, bT wT x = bS wS x)
    (hcomp : ∀ x, bT x x ≤ c * bS x x) :
    bS wS wS / c ≤ bT wT wT := by
  have hc' : 0 < c⁻¹ := inv_pos.mpr hc
  have hrep' : ∀ x, bS wS x = bT wT x := fun x => (hrep x).symm
  have hcomp' : ∀ x, c⁻¹ * bT x x ≤ bS x x := by
    intro x
    rw [inv_mul_le_iff₀ hc]
    exact le_trans (hcomp x) (le_of_eq (by ring))
  have h := energy_le_of_form_le hc' hTsymm hTadd hTsmul hTpsd hrep' hcomp'
  rw [div_le_iff₀ hc]
  have hval : bT wT wT / c⁻¹ = bT wT wT * c := by
    field_simp
  rwa [hval] at h

end GaloisForLFunctions.HTGeometry
