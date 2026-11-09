import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import GaloisForLFunctions.InfiniteRankWeilTheory.TheExceptionalCoordinate
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheReturnFormDuality

/-!
# Return bounds are statements about the prime labels

The main conjecture of the field (B97, `MainConjecture`): at every precision `δ ∈ (0, ½)` there are
`κ, c > 0` such that, for all large `y`, every `κ`-heavy subset of the primes `≤ y` (missing at most
the fraction `κ` of the weight `Σ p^{−½}`) has no `δ`-return before `exp(y^c)`.

It is a statement about the numbers `log p` alone. Every Euler product over the rational primes has
the same return bounds, whatever its coefficients. The shifted zeta function
`ζ(s − h) = Π_p (1 − p^h p^{−s})^{−1}` (`riemannZeta_shift_eulerProduct`) is such a product, and its
zeros `½ + h + iγ` at the critical ordinates of `ζ` violate ZAL (`not_zerosApproachLine_shift`).

So a route "return bounds ⇒ ZAL" cannot be uniform over any class of functions containing
`ζ(s − h)`: such a route refutes the main conjecture (`not_mainConjecture_of_uniform_route`). The
step from returns to zeros must use what `ζ(s − h)` lacks: Riemann's functional equation about
`Re s = ½`, or the size of the coefficients. The same holds for AAL with the finite-layer Euler
products over the rational primes of the corpus firewall.
-/

open Real Finset

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

/-! ## The main conjecture -/

/-- `H` is a `κ`-heavy subset of the primes `≤ y`. -/
def IsHeavy (y : ℕ) (κ : ℝ) (H : Finset ℕ) : Prop :=
  H ⊆ Nat.primesBelow (y + 1) ∧
    ∑ p ∈ Nat.primesBelow (y + 1) \ H, (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      κ * ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-(1 / 2 : ℝ))

/-- **Quantitative Kronecker for the primes** at precision `δ`, heaviness `κ` and exponent `c`. -/
def QuantitativeKronecker (δ κ c : ℝ) : Prop :=
  ∀ᶠ y : ℕ in Filter.atTop, ∀ H, IsHeavy y κ H → ∀ t : ℝ, 1 ≤ t →
    IsDeltaReturn H (fun p : ℕ => Real.log p) δ t → Real.exp ((y : ℝ) ^ c) ≤ t

/-- **The main conjecture (B97).** -/
def MainConjecture : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧ QuantitativeKronecker δ κ c

/-! ## The shifted zeta function -/

/-- `ζ(s − h)` is an Euler product over the rational primes, with coefficients `p^h`. -/
theorem riemannZeta_shift_eulerProduct (h : ℝ) {s : ℂ} (hs : 1 + h < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(s - h)))⁻¹ = riemannZeta (s - h) := by
  apply riemannZeta_eulerProduct_tprod
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

/-- **ZAL fails for `ζ(s − h)`**, `h > 0`: its zeros `½ + h + iγ` at the critical ordinates of `ζ` are
infinitely many. -/
theorem not_zerosApproachLine_shift {h : ℝ} (hh : 0 < h) :
    ¬ InfiniteRankWeilTheory.ZerosApproachLine
      (fun s : {s : ℂ // riemannZeta (s - h) = 0} => (s : ℂ)) := by
  intro hZ
  have hfin := hZ (h / 2) (by linarith)
  obtain ⟨T₀, hT₀, hz⟩ := RHTower.exists_riemannZeta_line_zero_dyadic
  obtain ⟨B, hB⟩ :=
    (hfin.image fun i : {s : ℂ // riemannZeta (s - h) = 0} => (i : ℂ).im).bddAbove
  obtain ⟨τ, hτ, hzero⟩ := hz (max T₀ (B + 1)) (le_max_left _ _)
  set s : ℂ := RHTower.linePt τ + h
  have hs : riemannZeta (s - h) = 0 := by simp only [s, add_sub_cancel_right]; exact hzero
  have hre : s.re = 1 / 2 + h := by simp [s, RHTower.linePt]
  have hmem : (⟨s, hs⟩ : {s : ℂ // riemannZeta (s - h) = 0}) ∈
      {i : {s : ℂ // riemannZeta (s - h) = 0} |
        1 / 2 + h / 2 < ((fun s : {s : ℂ // riemannZeta (s - h) = 0} => (s : ℂ)) i).re} := by
    show 1 / 2 + h / 2 < s.re; rw [hre]; linarith
  have him : s.im = τ := by simp [s, RHTower.linePt]
  have := hB ⟨⟨s, hs⟩, hmem, rfl⟩
  simp only [him] at this
  have := hτ.1
  have := le_max_right T₀ (B + 1)
  linarith

/-- **No uniform route from returns to ZAL.** A route deriving ZAL from the main conjecture for every
function in a class containing `ζ(s − h)`, `h > 0`, refutes the main conjecture. -/
theorem not_mainConjecture_of_uniform_route {h : ℝ} (hh : 0 < h) (P : (ℂ → ℂ) → Prop)
    (hP : P fun s => riemannZeta (s - h))
    (route : ∀ F : ℂ → ℂ, P F → MainConjecture →
      InfiniteRankWeilTheory.ZerosApproachLine (fun s : {s : ℂ // F s = 0} => (s : ℂ))) :
    ¬ MainConjecture := fun hB =>
  not_zerosApproachLine_shift hh (route _ hP hB)

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
