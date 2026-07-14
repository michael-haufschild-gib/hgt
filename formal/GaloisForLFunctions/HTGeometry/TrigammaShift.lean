import GaloisForLFunctions.HTGeometry.GammaDifferentialFE

/-!
# Finite integer-shift trigamma recurrence

The trigamma function `ψ' = (Γ'/Γ)'` obeys the single-step recurrence `ψ'(s+1) = ψ'(s) - 1/s²`
(`GaloisForLFunctions.trigamma_recurrence`).  Iterating gives the finite integer-shift form

`ψ'(w + n) = ψ'(w) - ∑_{i<n} 1/(w+i)²`,

the second-order companion of the digamma recurrence `digamma_add_nat`.  Together they say: the
trigamma *difference* across an integer shift is rational, so the second-order vertical boundary data of
a common-scale Gamma orbit is rational — the input the incommensurable-Gamma-orbit and neutral-Gamma-ratio
boundary-depth analyses build on.
-/

open Complex

namespace HTGeometry

/-- **Finite integer-shift trigamma recurrence.**  `ψ'(w + n) = ψ'(w) - ∑_{i<n} 1/(w+i)²` for `n : ℕ`,
off the poles, where `ψ' = deriv (Γ'/Γ)` is the trigamma function.  Iterates the single-step
`GaloisForLFunctions.trigamma_recurrence`. -/
theorem trigamma_add_nat (w : ℂ) (hw : ∀ k : ℕ, w ≠ -(k : ℂ)) (n : ℕ) :
    deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) (w + n)
      = deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) w
        - ∑ i ∈ Finset.range n, 1 / (w + i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hwn : ∀ k : ℕ, w + (n : ℂ) ≠ -(k : ℂ) := by
      intro k hk
      refine hw (k + n) ?_
      push_cast at hk ⊢
      linear_combination hk
    rw [show w + ((n : ℕ) + 1 : ℕ) = (w + (n : ℂ)) + 1 from by push_cast; ring,
      GaloisForLFunctions.trigamma_recurrence (w + n) hwn, ih, Finset.sum_range_succ]
    ring

/-- **Trigamma charge-collapse.**  Along a single shift-orbit `w + n_j` with vanishing total charge
`∑_j m_j = 0`, the trigamma content collapses to a rational function:
`∑_j m_j ψ'(w + n_j) = -∑_j m_j ∑_{i<n_j} 1/(w+i)²` — no transcendental `ψ'(w)` term survives.  The
second-order analogue of `digamma_charge_collapse`. -/
theorem trigamma_charge_collapse {d : ℕ} (w : ℂ) (hw : ∀ k : ℕ, w ≠ -(k : ℂ)) (nn : Fin d → ℕ)
    (m : Fin d → ℂ) (hcharge : ∑ j, m j = 0) :
    ∑ j, m j * deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) (w + nn j)
      = -∑ j, m j * ∑ i ∈ Finset.range (nn j), 1 / (w + i) ^ 2 := by
  simp_rw [trigamma_add_nat w hw, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hcharge,
    zero_mul, zero_sub]

end HTGeometry
