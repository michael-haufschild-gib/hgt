# SEM dyadic Weyl degeneracy law

- **ID:** sem-dyadic-weyl-degeneracy-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** Lean-only dependency closure of `TruncatedJetWeylBoundary.lean` and `SEMTruncatedJetWeylCharge.lean`
- **Statement:** On an actual SEM hole packet of length `n+1`, the boundary-completed depth-`k` Weyl equation holds iff wrap holonomy is zero or completed SEM contour charge modulo `2^k` vanishes.

## Goal

Classify every boundary holonomy, including the singular branch suppressed by earlier nonzero-wrap
theorems.  This separates a source-detecting finite Weyl model from the automatic one-sided false
positive.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure, source-pure, exact proof found
- [x] Paper proof dependency-closed and `[PROVED HERE]`
- [ ] 2 → 3 formalized: direct Lean check, axiom audit, and final module build green
- [ ] 3 → 4 publication-ready: standalone treatment and priority audit

## Parent theorem closure

1. `truncatedJetClock_oneSidedShift_weyl`: zero wrap always satisfies the matrix Weyl equation.
2. `pow_dvd_card_of_dyadic_boundaryCompletedJetWeyl`: a nonzero wrap satisfying it forces
   `2^k ∣ n+1`.
3. `boundaryCompletedJetWeyl_of_phase_pow_card` plus
   `dyadicWeylPhase_isPrimitiveRoot`: divisibility suffices for every wrap.
4. `completedSEMContourCharge_zero_iff_dyadicPhase_pow_holeCount`: on actual SEM data, the same
   divisibility is exactly zero completed contour charge.

## Paper proof

`[PROVED HERE]` Let `h` be wrap holonomy.  If the Weyl equation holds, split on `h=0`.  The zero
case is the first alternative.  If `h≠0`, the dyadic boundary theorem forces `2^k ∣ n+1`.
Conversely, `h=0` gives the canonical one-sided Weyl law.  If `2^k ∣ n+1`, primitivity gives
`ζ_k^(n+1)=1`, and phase closure gives the full boundary-completed Weyl equation for arbitrary
`h`.  For SEM split data with hole count `n+1`, the completed-contour theorem identifies
`2^k ∣ n+1` with vanishing source charge.  Therefore

`Weyl_k(n,h) ↔ (h=0 ∨ completedSEMContourCharge_k=0)`.

No unproved analytic input occurs.

## Occupancy and novelty audit

- Exact Lean search found no arbitrary-holonomy disjunction and no full-matrix SEM equivalence.
- Existing `SEMTruncatedJetWeylCharge.lean` assumes nonzero holonomy and identifies charge with one
  defect entry, not the full equation including the singular branch.
- Finite-dimensional twisted commutation and dimension divisibility are standard; see
  Farenick--Ojo--Plosker, *Universality of Weyl Unitaries* (arXiv:2101.00129), and the finite
  Stone--von Neumann discussion in Hastings, *Approximate symmetries of Hamiltonians*
  (arXiv:1608.02600).
- Targeted literature searches found no conjunction with a completed symmetric
  Euler--Maclaurin contour charge or the exact zero-wrap/zero-charge dichotomy.  This is a
  noncollision finding, not a priority claim.

## Lean target

- Module: `GaloisForLFunctions.RHTower.SEMDyadicWeylDegeneracyLaw`
- Theorems:
  - `dyadicBoundaryCompletedJetWeyl_iff_zero_or_dvd`
  - `boundaryCompletedJetWeyl_iff_zero_or_completedSEMContourCharge_zero`

## Log

- 2026-07-21 — Derived bottom-up from actual Lean theorem statements; exact corpus search clean.
- 2026-07-21 — Paper proof closed; hostile literature search found standard parents but no exact
  source-specific law; Lean source written pending process-safe verification.
