import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheSchurParametersOfSpecZ
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface

/-!
# The pole is a hyperbolic pair of angles

Write Weil's pairing as its polar part minus the local intersection (ACS `localPair`):
`W(f, g) = B(f)A(g) + A(f)B(g) − ℓ(f, g)`, `A(f) = ∫fe^{u/2}`, `B(f) = ∫fe^{−u/2}`. A lattice
translate scales the pole coordinates by `e^{∓dh/2}`, so on a lattice of step `h`

`κ(d) = 2A(φ)B(φ)cosh(dh/2) − ℓ(φ, φ(· + dh))` (`weilSeq_eq_polar_sub_local`),

and the polar part of the lattice Toeplitz form is a pole plane that factors through two evaluations
(`toeplitzForm_polar`, `toeplitzForm_polar_eq_hyperbolic`):

`Σ_{j,k} 2ab·cosh((j − k)h/2)x_jx_k = 2ab·(Σ_j x_je^{jh/2})(Σ_k x_ke^{−kh/2})`.

In the angle language of `TheAnglesOfADegenerateWindow` the pole is the pair of **hyperbolic angles**
`z = e^{±h/2}`, off the unit circle and inverse to each other, while the zeros on the line are the
unitary angles. Over `𝔽_q` with `h = log q` these are the trivial Frobenius eigenvalues `1, q`
normalized by `√q`: the polar part of every lattice window is one hyperbolic plane, and positivity is
the statement that the local part pays it on the remaining directions.

**The weight at the trivial angles** (`polarSeq_signature`): for `A(φ)B(φ) > 0` the polar plane is
positive on one site, negative on the first difference `e₀ − e₁` (`T = 4ab(1 − cosh(h/2))`), and
vanishes on the hyperplane `Σ_j x_je^{jh/2} = 0`: it carries exactly one negative square. The
lattice window is nonnegative iff the archimedean place and the primes pay that square; for all
lattices this is RH (`riemannHypothesis_iff_levinsonErr_pos`).
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri

variable {φ : ℝ → ℝ} {h : ℝ}

theorem latticeTranslate_eq_scaleShift (φ : ℝ → ℝ) (h : ℝ) (d : ℤ) :
    latticeTranslate φ h d = scaleShift (-((d : ℝ) * h)) φ := by
  funext u; simp [latticeTranslate, scaleShift]

/-- **The polar part of the Weil sequence is a hyperbolic cosine**:
`κ(d) = 2A(φ)B(φ)cosh(dh/2) − ℓ(φ, φ(· + dh))`. -/
theorem weilSeq_eq_polar_sub_local (φ : ℝ → ℝ) (h : ℝ) (d : ℤ) :
    weilSeq φ h d = 2 * poleA φ * poleB φ * Real.cosh ((d : ℝ) * h / 2) -
      localPair φ (latticeTranslate φ h d) := by
  have hloc : weilSeq φ h d = poleB φ * poleA (latticeTranslate φ h d) +
      poleA φ * poleB (latticeTranslate φ h d) - localPair φ (latticeTranslate φ h d) := by
    rw [localPair, weilSeq]; ring
  rw [hloc, latticeTranslate_eq_scaleShift, poleA_scaleShift, poleB_scaleShift, Real.cosh_eq]
  have e1 : -((d : ℝ) * h) / 2 = -((d : ℝ) * h / 2) := by ring
  have e2 : -(-((d : ℝ) * h)) / 2 = (d : ℝ) * h / 2 := by ring
  rw [e1, e2]
  ring

/-- **The polar Toeplitz form is a pole plane**:
`Σ_{j,k} 2ab·cosh((j − k)h/2)x_jx_k = 2ab((Σ_j x_jcosh(jh/2))² − (Σ_j x_jsinh(jh/2))²)`. -/
theorem toeplitzForm_polar (a b h : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    toeplitzForm (fun d : ℤ => 2 * a * b * Real.cosh ((d : ℝ) * h / 2)) n x =
      2 * a * b * ((∑ j : Fin n, x j * Real.cosh (((j : ℕ) : ℝ) * h / 2)) ^ 2 -
        (∑ j : Fin n, x j * Real.sinh (((j : ℕ) : ℝ) * h / 2)) ^ 2) := by
  calc toeplitzForm (fun d : ℤ => 2 * a * b * Real.cosh ((d : ℝ) * h / 2)) n x
      = ∑ j : Fin n, ∑ k : Fin n, 2 * a * b *
          (x j * Real.cosh (((j : ℕ) : ℝ) * h / 2) * (x k * Real.cosh (((k : ℕ) : ℝ) * h / 2)) -
            x j * Real.sinh (((j : ℕ) : ℝ) * h / 2) * (x k * Real.sinh (((k : ℕ) : ℝ) * h / 2))) := by
        simp only [toeplitzForm]
        refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
        have e : ((((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) : ℤ) : ℝ) * h / 2 =
            ((j : ℕ) : ℝ) * h / 2 - ((k : ℕ) : ℝ) * h / 2 := by push_cast; ring
        rw [e, Real.cosh_sub]
        ring
    _ = 2 * a * b * ((∑ j : Fin n, x j * Real.cosh (((j : ℕ) : ℝ) * h / 2)) *
          (∑ k : Fin n, x k * Real.cosh (((k : ℕ) : ℝ) * h / 2)) -
          (∑ j : Fin n, x j * Real.sinh (((j : ℕ) : ℝ) * h / 2)) *
          (∑ k : Fin n, x k * Real.sinh (((k : ℕ) : ℝ) * h / 2))) := by
        rw [sum_mul_sum, sum_mul_sum, ← sum_sub_distrib, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [← sum_sub_distrib, mul_sum]
    _ = _ := by ring

/-- **The pole is the pair of hyperbolic angles `e^{±h/2}`**: the polar Toeplitz form is
`2ab·(Σ_j x_je^{jh/2})(Σ_j x_je^{−jh/2})`, the product of the evaluations at `z = e^{h/2}` and
`z = e^{−h/2}`. -/
theorem toeplitzForm_polar_eq_hyperbolic (a b h : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    toeplitzForm (fun d : ℤ => 2 * a * b * Real.cosh ((d : ℝ) * h / 2)) n x =
      2 * a * b * (∑ j : Fin n, x j * Real.exp (((j : ℕ) : ℝ) * h / 2)) *
        (∑ j : Fin n, x j * Real.exp (-(((j : ℕ) : ℝ) * h / 2))) := by
  rw [toeplitzForm_polar]
  have hp : ∑ j : Fin n, x j * Real.exp (((j : ℕ) : ℝ) * h / 2) =
      ∑ j : Fin n, x j * Real.cosh (((j : ℕ) : ℝ) * h / 2) +
        ∑ j : Fin n, x j * Real.sinh (((j : ℕ) : ℝ) * h / 2) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by rw [← Real.cosh_add_sinh]; ring
  have hm : ∑ j : Fin n, x j * Real.exp (-(((j : ℕ) : ℝ) * h / 2)) =
      ∑ j : Fin n, x j * Real.cosh (((j : ℕ) : ℝ) * h / 2) -
        ∑ j : Fin n, x j * Real.sinh (((j : ℕ) : ℝ) * h / 2) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by rw [← Real.cosh_sub_sinh]; ring
  rw [hp, hm]
  ring

/-! ### The trivial angles carry one negative square -/

/-- The polar sequence `κ_pol(d) = 2ab·cosh(dh/2)`. -/
def polarSeq (a b h : ℝ) (d : ℤ) : ℝ := 2 * a * b * Real.cosh ((d : ℝ) * h / 2)

/-- **The pole plane is positive on a single site**: `T(e₀) = 2ab`. -/
theorem polarSeq_single (a b h : ℝ) : toeplitzForm (polarSeq a b h) 1 (fun _ => 1) = 2 * a * b := by
  simp [toeplitzForm, polarSeq]

/-- **The pole plane is negative on the first difference**: on `e₀ − e₁`,
`T = 4ab(1 − cosh(h/2)) < 0` for `ab > 0`, `h ≠ 0`. -/
theorem polarSeq_firstDiff (a b h : ℝ) :
    toeplitzForm (polarSeq a b h) 2 ![1, -1] = 4 * a * b * (1 - Real.cosh (h / 2)) := by
  simp only [toeplitzForm, polarSeq, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, sub_self, Int.cast_zero, zero_mul,
    zero_div, Real.cosh_zero]
  have e1 : ((((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : ℝ) * h / 2 = -(h / 2) := by push_cast; ring
  have e2 : ((((1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) : ℤ) : ℝ) * h / 2 = h / 2 := by push_cast; ring
  simp only [Nat.cast_zero, Nat.cast_one] at e1 e2
  rw [e1, e2, Real.cosh_neg]
  ring

/-- **The trivial angles carry exactly an indefinite plane.** For `ab > 0` and `h ≠ 0` the polar
Toeplitz form is positive on `e₀`, negative on `e₀ − e₁`, and vanishes on the hyperplane
`Σ_j x_je^{jh/2} = 0`: one positive and at most one negative square. -/
theorem polarSeq_signature {a b h : ℝ} (hab : 0 < a * b) (hh : h ≠ 0) :
    0 < toeplitzForm (polarSeq a b h) 1 (fun _ => 1) ∧
      toeplitzForm (polarSeq a b h) 2 ![1, -1] < 0 ∧
      ∀ n (x : Fin n → ℝ), ∑ j : Fin n, x j * Real.exp (((j : ℕ) : ℝ) * h / 2) = 0 →
        toeplitzForm (polarSeq a b h) n x = 0 := by
  refine ⟨by rw [polarSeq_single]; linarith, ?_, fun n x hx => ?_⟩
  · rw [polarSeq_firstDiff]
    have : 1 < Real.cosh (h / 2) := Real.one_lt_cosh.mpr (by intro h0; apply hh; linarith)
    nlinarith
  · have := toeplitzForm_polar_eq_hyperbolic a b h n x
    show toeplitzForm (fun d : ℤ => 2 * a * b * Real.cosh ((d : ℝ) * h / 2)) n x = 0
    rw [this, hx]
    ring

/-- **The trivial angles in the Weil sequence.** The Weil sequence of a lattice is the polar sequence
of `(A(φ), B(φ))` minus the local sequence: `κ = κ_pol − ℓ(φ, φ(· + dh))`. -/
theorem weilSeq_eq_polarSeq_sub (φ : ℝ → ℝ) (h : ℝ) (d : ℤ) :
    weilSeq φ h d = polarSeq (poleA φ) (poleB φ) h d - localPair φ (latticeTranslate φ h d) := by
  rw [weilSeq_eq_polar_sub_local, polarSeq]

end GaloisForLFunctions.GrowingWindowsOfSpecZ
