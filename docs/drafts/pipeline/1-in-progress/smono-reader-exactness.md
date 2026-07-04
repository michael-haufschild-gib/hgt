# (S-mono): Section-Zero Energy Monotonicity and Exactness of the DISC Reader

- **ID:** smono-reader-exactness
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) — proved in outline with explicit margins; constant write-out pending
- **Source:** docs/drafts/rh-monodromy-weight-mismatch/ docs 23–31 (tasks #135/#138/#142)
- **Statement:** On (F)-fields (one-sided, nondecreasing x-gaps, |Δδ| = O(δ²) log-gap
  regularity), the scale-invariant equilibrium energy S_i = d + c²ℰ(c_i) is strictly
  increasing along outer critical points of the Jensen section; hence the margin crosses 1
  exactly once, T = 1, Z_c(J^d_{Pg}) = 2, and the DISC square-class reader is exact on
  one-sided-far recentered carriers.

## Goal
Reader exactness is the analytic half of the MWM bridge identity (#130): with the
machine-checked seam transport (SeamTransport.lean) and the unconditional domination on
the symmetrized exponential-AFE family (doc 32 §§6–8), it reduces ζ-window parity on
dominated windows to finite certified readings. Constraint-not-flow is the engine at
every joint: the crossing exists because the window is one-sided (doubly-infinite
lattice is rigid, doc 28 §5c); the equilibria are constraint solutions Σξ = d, not
trajectories.

## Gates
- [x] 0 → 1  in-progress: well-posed (docs 23–24), attack complete (docs 25–31)
- [ ] 1 → 2  fully-proven: consolidated write-out with all constants explicit
      (χ1/χ2 chased with margins ≈ 40 and ~ d/log d, doc 31 §5; remaining = line-by-line
      constant write-out + per-carrier (F2)/(F3) verification for the u-plane carriers)
- [ ] 2 → 3  formalized: partial — SpurHermite/SpurRescale/SpurOperator/SpurStability/
      SpurNoGo banked (20 theorems, axiom-clean); remaining: ledger identity, weight sum
      rules, doc 25 Thm A, counting lemma
- [ ] 3 → 4  publication-ready

## Approach
Chain (all banked): identity stack + (CPI) (doc 23) → electrostatic margin + corrected
counting Z_c ≤ 2 + T (doc 24) → tracking clearance, Hermite splitting, Lemma W (doc 25;
Lean) → reversal ξ = 1 − η, sum rule Σξ = d, localization reading (doc 26) → drift
hierarchy, pole-removed smooth path, midpoint-push θ < 1/2 (doc 27, 29) → operator
identity Ĵ = (D−τ)(D−τ̄)Â, winding formula, two-cluster shape-necessity no-go (doc 28;
Lean) → constant-δ lattice theorem (doc 29) → exact adiabatic ledger, O(1/δ) cushion,
(ADB-crude) (doc 30) → assembled theorem + (χ1)/(χ2) chases + citation audit
(delegate-citation-free critical chain) (doc 31).

## Log
- 2026-07-04 — created at stage 1 with the full proof outline complete; measured at
  zero violations in three independent forms; instance #136/#140 (u-plane, simple
  zeros) needs only the unconditional m ≤ 3 case.
