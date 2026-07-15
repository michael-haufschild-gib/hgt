import GaloisForLFunctions.HTGeometry.MagnitudeTailPairGap
import GaloisForLFunctions.HTGeometry.MagnitudeBalancedAtomExistence

/-!
# Minimal nonzero grouped weights

The valuation minimizer must be chosen only among grouped atoms with nonzero `aevalWeight`.
This module packages that finite selection and retains comparison with the balanced witness that
proves the nonzero support is inhabited.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

/-- A nonzero grouped witness guarantees a nonzero-weight valuation minimizer at the same
coefficient level.  The minimizer is no larger in valuation than every nonzero grouped atom,
including the supplied balanced witness. -/
theorem exists_min_nonzero_aevalWeight {n N : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (b : ℕ → ℝ) {νw : ℕ →₀ ℕ}
    (hνw : νw ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hww : aevalWeight n N Q νw ≠ 0) :
    ∃ ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n),
      aevalWeight n N Q ν₀ ≠ 0 ∧
      (∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 →
          ν₀.sum (fun i k => (k : ℝ) * b i) ≤
            ν.sum (fun i k => (k : ℝ) * b i)) ∧
      ν₀.sum (fun i k => (k : ℝ) * b i) ≤
        νw.sum (fun i k => (k : ℝ) * b i) := by
  classical
  let K := ((sigmaIdx n N Q).image (atomKeyOf n)).filter
    (fun ν => aevalWeight n N Q ν ≠ 0)
  have hνwK : νw ∈ K := Finset.mem_filter.mpr ⟨hνw, hww⟩
  obtain ⟨ν₀, hν₀K, hmin⟩ :=
    K.exists_min_image (fun ν => ν.sum (fun i k => (k : ℝ) * b i)) ⟨νw, hνwK⟩
  obtain ⟨hν₀, hw₀⟩ := Finset.mem_filter.mp hν₀K
  refine ⟨ν₀, hν₀, hw₀, ?_, hmin νw hνwK⟩
  intro ν hν hw
  exact hmin ν (Finset.mem_filter.mpr ⟨hν, hw⟩)

end

end GaloisForLFunctions
