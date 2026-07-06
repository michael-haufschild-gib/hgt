/-
The finite carrier gap `emCarrier M − gN N` reduces exactly to the approximate
functional-equation remainder of `ζ`.

The Euler–Maclaurin carrier `emCarrier M z = Σ_{n≤M} n^(−z) + M^(1−z)/(z−1)` and the
χ-symmetrized finite carrier `gN N z = Σ_{n≤N} n^(−z) + χ(z)·Σ_{n≤N} n^(−(1−z))` differ
by an amount that factors through `ζ`:

  `emCarrier M z − gN N z = (emCarrier M z − ζ z) + (ζ z − gN N z)`,

whose first summand is controlled unconditionally by the Euler–Maclaurin remainder
`‖z‖·M^(−re z)/re z`.  The remaining summand — the approximate functional-equation
remainder `ζ z − gN N z` — has the exact closed form

  `ζ z − gN N z = emPole N z − z·emTail N z − χ(z)·Σ_{n≤N} n^(−(1−z))`,

which follows from the Euler–Maclaurin representation of `ζ` at depth `N` alone (no
functional equation).  Of the three terms the pole `emPole N z` and the Euler–Maclaurin
tail `z·emTail N z` are elementarily small; the reflected Dirichlet block
`χ(z)·Σ_{n≤N} n^(−(1−z))` is the only oscillatory term, and its smallness is exactly the
content of the approximate functional equation.  This module records the reduction and the
resulting explicit majorant, isolating the reflected block as the sole irreducible input.
-/
import GaloisForLFunctions.RHTower.EMCarrier

open Complex

noncomputable section

namespace RHTower

/-- **Exact approximate-functional-equation remainder identity.**  On the region where the
Euler–Maclaurin representation of `ζ` holds (`0 < re z`, `z ≠ 1`), the gap between `ζ` and the
χ-symmetrized finite carrier is the pole term minus the Euler–Maclaurin tail minus the reflected
Dirichlet block:
`ζ z − gN N z = emPole N z − z·emTail N z − zetaChi z · dirichletPoly N (1 − z)`.
No functional equation is used — only the Euler–Maclaurin identity at depth `N`. -/
theorem zeta_sub_gN_eq {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hσ : 0 < z.re) (hz1 : z ≠ 1) :
    riemannZeta z - gN N z
      = emPole N z - z * emTail N z - zetaChi z * dirichletPoly N (1 - z) := by
  rw [zeta_eq_emCarrier_sub hN hσ hz1]
  unfold emCarrier gN chiSymmetrize
  ring

/-- **Explicit majorant for the AFE remainder.**  Bounding the three exact terms of
`zeta_sub_gN_eq` separately: the Euler–Maclaurin tail by `‖z‖·N^(−re z)/re z`
(`norm_emTail_le`), leaving the pole and reflected block explicit. -/
theorem norm_zeta_sub_gN_le {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hσ : 0 < z.re) (hz1 : z ≠ 1) :
    ‖riemannZeta z - gN N z‖
      ≤ ‖emPole N z‖ + ‖z‖ * (N : ℝ) ^ (-z.re) / z.re
        + ‖zetaChi z * dirichletPoly N (1 - z)‖ := by
  rw [zeta_sub_gN_eq hN hσ hz1]
  have htail : ‖z * emTail N z‖ ≤ ‖z‖ * (N : ℝ) ^ (-z.re) / z.re := by
    rw [norm_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (norm_emTail_le hN hσ hz1) (norm_nonneg z)
  calc ‖emPole N z - z * emTail N z - zetaChi z * dirichletPoly N (1 - z)‖
      ≤ ‖emPole N z - z * emTail N z‖ + ‖zetaChi z * dirichletPoly N (1 - z)‖ :=
        norm_sub_le _ _
    _ ≤ (‖emPole N z‖ + ‖z * emTail N z‖) + ‖zetaChi z * dirichletPoly N (1 - z)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ ‖emPole N z‖ + ‖z‖ * (N : ℝ) ^ (-z.re) / z.re
          + ‖zetaChi z * dirichletPoly N (1 - z)‖ := by
        gcongr

/-- **Tight reduction of the carrier gap to the AFE remainder.**  The gap between the depth-`M`
Euler–Maclaurin carrier and the depth-`N` χ-symmetrized carrier is bounded by the (elementary)
Euler–Maclaurin remainder plus the single genuine quantity `‖ζ z − gN N z‖`.  Unlike the
term-by-term triangle bound on `emCarrier M z − gN N z`, this keeps the reflected block inside the
AFE remainder, where the oscillatory cancellation lives. -/
theorem norm_emCarrier_sub_gN_le_afe {N M : ℕ} (hM : 1 ≤ M) {z : ℂ}
    (hσ : 0 < z.re) (hz1 : z ≠ 1) :
    ‖emCarrier M z - gN N z‖
      ≤ ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖riemannZeta z - gN N z‖ := by
  calc ‖emCarrier M z - gN N z‖
      ≤ ‖emCarrier M z - riemannZeta z‖ + ‖riemannZeta z - gN N z‖ := by
        have := norm_add_le (emCarrier M z - riemannZeta z) (riemannZeta z - gN N z)
        simpa using this.trans_eq (by ring_nf)
    _ ≤ ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖riemannZeta z - gN N z‖ := by
        gcongr
        rw [show emCarrier M z - riemannZeta z = -(riemannZeta z - emCarrier M z) by ring,
          norm_neg]
        exact zeta_sub_emCarrier_norm_le hM hσ hz1

/-- **The (R7) carrier-closeness face, supplied from an AFE-remainder budget.**  If on a set `S`
the Euler–Maclaurin remainder majorant is `≤ ε₁` and the approximate functional-equation remainder
`‖ζ − gN N‖` is `≤ a`, then the depth-`M` Euler–Maclaurin carrier is `(ε₁ + a)`-close to the
depth-`N` χ-symmetrized carrier on `S`.  This is the converse packaging of
`afeAccurateOn_of_emCarrier_close`: there closeness feeds accuracy, here accuracy feeds closeness,
so carrier-closeness and AFE accuracy are the same datum up to the elementary `ε₁`. -/
theorem emCarrier_gN_close_on_of_afe {S : Set ℂ} {N M : ℕ} (hM : 1 ≤ M) {ε₁ a : ℝ}
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z ≠ 1)
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hafe : ∀ z ∈ S, ‖riemannZeta z - gN N z‖ ≤ a) :
    ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ ε₁ + a := by
  intro z hz
  obtain ⟨h1, h2⟩ := hstrip z hz
  exact le_trans (norm_emCarrier_sub_gN_le_afe hM h1 h2)
    (add_le_add (hE z hz) (hafe z hz))

/-- **The (R7) face reduced to a single reflected-block budget.**  Bounding the AFE remainder by its
three exact terms (`norm_zeta_sub_gN_le`) and feeding the result through the tight reduction leaves
the carrier gap controlled by: the depth-`M` Euler–Maclaurin remainder `ε₁`, the depth-`N` pole
budget `δP`, the depth-`N` Euler–Maclaurin tail budget `δT`, and the reflected Dirichlet-block budget
`Rχ`.  The first three are elementarily small (`ε₁ → 0` as `M → ∞`; the pole and tail decay at the
matched depth), so the reflected block `zetaChi z · dirichletPoly N (1 − z)` is the **sole** input
carrying the oscillatory (approximate functional-equation) content.  This is strictly sharper than a
term-by-term split of `emCarrier M − gN N`, which retains a drift block and the depth-`M` pole, both
polynomially large. -/
theorem emCarrier_gN_close_on_of_reflected_budget {S : Set ℂ} {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) {ε₁ δP δT Rχ : ℝ}
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z ≠ 1)
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hP : ∀ z ∈ S, ‖emPole N z‖ ≤ δP)
    (hT : ∀ z ∈ S, ‖z‖ * (N : ℝ) ^ (-z.re) / z.re ≤ δT)
    (hχ : ∀ z ∈ S, ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ Rχ) :
    ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ ε₁ + (δP + δT + Rχ) := by
  intro z hz
  obtain ⟨h1, h2⟩ := hstrip z hz
  have hafe : ‖riemannZeta z - gN N z‖ ≤ δP + δT + Rχ :=
    le_trans (norm_zeta_sub_gN_le hN h1 h2)
      (add_le_add (add_le_add (hP z hz) (hT z hz)) (hχ z hz))
  exact le_trans (norm_emCarrier_sub_gN_le_afe hM h1 h2)
    (add_le_add (hE z hz) hafe)

end RHTower
