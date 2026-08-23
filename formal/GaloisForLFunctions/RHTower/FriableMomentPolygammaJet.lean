import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.Hurwitz.PolygammaHurwitzValue

/-!
# The digamma jet at a positive integer

Telescoping the digamma recurrence from `s = 1` expresses every polygamma value at a positive
integer through Euler's constant, a zeta value, and a rational harmonic sum:

```text
ψ(j+1)       = H_j - γ ,
ψ⁽ᵐ⁺¹⁾(j+1)  = (-1)^{m+2} (m+1)! (ζ(m+2) - H_j^{(m+2)}) .
```
-/

open Complex Filter Finset

namespace RHTower

noncomputable section

/-- The rational generalized harmonic sum `H_j^{(m+1)} = ∑_{k<j} 1/(k+1)^{m+1}`. -/
def harmonicQ (m j : ℕ) : ℚ := ∑ k ∈ Finset.range j, 1 / ((k : ℚ) + 1) ^ (m + 1)

theorem harmonicQ_cast (m j : ℕ) :
    ((harmonicQ m j : ℚ) : ℂ) = ∑ k ∈ Finset.range j, 1 / ((1 : ℂ) + (k : ℂ)) ^ (m + 1) := by
  rw [harmonicQ]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  ring

theorem digamma_eq_logDeriv_fun :
    Complex.digamma = fun z : ℂ => deriv Complex.Gamma z / Complex.Gamma z := rfl

theorem iteratedDeriv_digamma_natSucc (m j : ℕ) :
    iteratedDeriv m Complex.digamma ((j : ℂ) + 1)
      = iteratedDeriv m Complex.digamma 1
        + (-1) ^ m * (m.factorial : ℂ) * ((harmonicQ m j : ℚ) : ℂ) := by
  have h1off : ∀ p : ℕ, (1 : ℂ) ≠ -(p : ℂ) := by
    intro p hp
    have hre : (1 : ℝ) = -(p : ℝ) := by
      have := congrArg Complex.re hp
      simpa using this
    have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    linarith
  have h := GaloisForLFunctions.polygamma_telescope m 1 h1off j
  rw [digamma_eq_logDeriv_fun, harmonicQ_cast]
  rw [show ((j : ℂ) + 1) = (1 : ℂ) + (j : ℂ) by ring]
  exact h

/-- **The digamma value at a positive integer.**  `ψ(j+1) = H_j - γ`. -/
theorem digamma_natSucc (j : ℕ) :
    Complex.digamma ((j : ℂ) + 1)
      = ((harmonicQ 0 j : ℚ) : ℂ) - (Real.eulerMascheroniConstant : ℂ) := by
  have h := iteratedDeriv_digamma_natSucc 0 j
  simp only [iteratedDeriv_zero] at h
  rw [Complex.digamma_one] at h
  rw [h]
  ring

/-- **The positive-order polygamma values at a positive integer.**
`ψ⁽ᵐ⁺¹⁾(j+1) = (-1)^{m+2}(m+1)!(ζ(m+2) - H_j^{(m+2)})`. -/
theorem iteratedDeriv_digamma_natSucc_succ (m j : ℕ) :
    iteratedDeriv (m + 1) Complex.digamma ((j : ℂ) + 1)
      = (-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ)
        * (riemannZeta ((m + 2 : ℕ) : ℂ) - ((harmonicQ (m + 1) j : ℚ) : ℂ)) := by
  have h := iteratedDeriv_digamma_natSucc (m + 1) j
  rw [GaloisForLFunctions.polygamma_one_eq_riemannZeta m] at h
  rw [h]
  have hsign : (-1 : ℂ) ^ (m + 1) = -((-1 : ℂ) ^ (m + 2)) := by
    rw [pow_succ]
    ring
  rw [hsign]
  ring

end

end RHTower
