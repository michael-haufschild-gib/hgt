import Mathlib

/-!
# The critical six-tail keeps a nonzero Gamma residue

Write the completed Xi function as `Ξ(s) = A(s)ζ(s)` with the archimedean factor
`A(s) = ½ s(s-1)π^{-s/2}Γ(s/2)`, and let `B₆ = 1/ζ + P₆` be the meromorphic continuation of the
ordinary six-tail multiplier, `P₆(s) = -1 + 2^{-s} + 3^{-s} + 5^{-s}`.  Off the zeta zeros the
product `Ξ B₆` is `A + Ξ P₆`, and the right-hand side is the continuation across a nontrivial zero,
where it takes the nonzero value `A(ρ)`.  Hence no holomorphic counterterm can annihilate the
critical six-tail: a counterterm must have a pole along the Xi divisor with the exact opposite
principal germ.

* `deningerArchimedeanFactor_ne_zero` : **`A(ρ) ≠ 0` in the critical strip.**
* `deningerXiSixTail_eq` : **`(10)`: `Ξ B₆ = A + Ξ P₆` off the zeta zeros.**
* `deningerXiSixTailContinuation_at_zero` : **`(11)`: the continuation lands on `A(ρ)`.**
* `deningerXiSixTail_regular_counterterm` : **`(12)`: a holomorphic counterterm changes nothing.**
* `deningerXiSixTail_counterterm_germ` : **`(13)`: an annihilating counterterm must supply
  `-A(ρ)`.**
-/

namespace GaloisForLFunctions

open Complex

noncomputable section

/-- The archimedean factor `A(s) = ½ s(s-1)π^{-s/2}Γ(s/2)` of `(8)`. -/
def deningerArchimedeanFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-- The completed Xi function in the factored form `(8)`. -/
def deningerXi (s : ℂ) : ℂ := deningerArchimedeanFactor s * riemannZeta s

/-- The finite six-tail correction `P₆(s) = -1 + 2^{-s} + 3^{-s} + 5^{-s}` of `(9)`. -/
def deningerSixTailCorrection (s : ℂ) : ℂ :=
  -1 + (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s) + (5 : ℂ) ^ (-s)

/-- The six-tail multiplier `B₆ = 1/ζ + P₆` of `(9)`. -/
def deningerSixTailMultiplier (s : ℂ) : ℂ :=
  (riemannZeta s)⁻¹ + deningerSixTailCorrection s

/-- The continuation of `Ξ B₆`, namely `A + Ξ P₆`. -/
def deningerXiSixTailContinuation (s : ℂ) : ℂ :=
  deningerArchimedeanFactor s + deningerXi s * deningerSixTailCorrection s

/-- **`A(ρ) ≠ 0` in the critical strip.**  Every factor is nonzero there: `ρ ≠ 0` and `ρ ≠ 1`
because `0 < Re ρ < 1`, the complex power of `π` never vanishes, and `Γ` has no zeros. -/
theorem deningerArchimedeanFactor_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    deningerArchimedeanFactor s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination h
    rw [this] at h1
    simp at h1
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.2 (Or.inl ?_)
    exact_mod_cast Real.pi_ne_zero
  have hgamma : Complex.Gamma (s / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m => ?_
    intro hcontra
    have hre : (s / 2).re = -(m : ℝ) := by rw [hcontra]; simp
    have : s.re / 2 = -(m : ℝ) := by simpa using hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [deningerArchimedeanFactor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1) hpi) hgamma

/-- **`(10)`: `Ξ B₆ = A + Ξ P₆` wherever zeta does not vanish.** -/
theorem deningerXiSixTail_eq {s : ℂ} (hz : riemannZeta s ≠ 0) :
    deningerXi s * deningerSixTailMultiplier s = deningerXiSixTailContinuation s := by
  rw [deningerSixTailMultiplier, deningerXiSixTailContinuation, deningerXi, mul_add]
  congr 1
  field_simp

/-- **`(11)`: at a nontrivial Xi zero the continuation lands on the nonzero value `A(ρ)`.** -/
theorem deningerXiSixTailContinuation_at_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hxi : deningerXi s = 0) :
    deningerXiSixTailContinuation s = deningerArchimedeanFactor s
      ∧ deningerXiSixTailContinuation s ≠ 0 := by
  have hval : deningerXiSixTailContinuation s = deningerArchimedeanFactor s := by
    rw [deningerXiSixTailContinuation, hxi, zero_mul, add_zero]
  exact ⟨hval, by rw [hval]; exact deningerArchimedeanFactor_ne_zero h0 h1⟩

/-- **`(12)`: a counterterm holomorphic at the zero changes nothing.**  Adding any value `E` to the
multiplier adds `Ξ(ρ)E = 0`, so the landing value is still `A(ρ) ≠ 0`. -/
theorem deningerXiSixTail_regular_counterterm {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hxi : deningerXi s = 0) (E : ℂ) :
    deningerXiSixTailContinuation s + deningerXi s * E = deningerArchimedeanFactor s
      ∧ deningerXiSixTailContinuation s + deningerXi s * E ≠ 0 := by
  obtain ⟨hval, hne⟩ := deningerXiSixTailContinuation_at_zero h0 h1 hxi
  have hsum : deningerXiSixTailContinuation s + deningerXi s * E
      = deningerArchimedeanFactor s := by
    rw [hxi, zero_mul, add_zero, hval]
  exact ⟨hsum, by rw [hsum]; exact deningerArchimedeanFactor_ne_zero h0 h1⟩

/-- **`(13)`: an annihilating counterterm must supply exactly `-A(ρ)`.**  If the corrected product
vanishes at the zero, the counterterm contribution is forced to be the opposite of the archimedean
residue, which is nonzero. -/
theorem deningerXiSixTail_counterterm_germ {s c : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hxi : deningerXi s = 0)
    (hzero : deningerXiSixTailContinuation s + c = 0) :
    c = -deningerArchimedeanFactor s ∧ c ≠ 0 := by
  obtain ⟨hval, _⟩ := deningerXiSixTailContinuation_at_zero h0 h1 hxi
  have hc : c = -deningerArchimedeanFactor s := by
    rw [hval] at hzero
    linear_combination hzero
  refine ⟨hc, ?_⟩
  rw [hc, neg_ne_zero]
  exact deningerArchimedeanFactor_ne_zero h0 h1

end

end GaloisForLFunctions
