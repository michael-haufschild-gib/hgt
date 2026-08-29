# Theta-cusp C5 adapted physical-cone no-go

- **ID:** C5-ADAPTED-PHYSICAL-CONE
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/theta-cusp-c5-orbit-first-contact.md
- **Statement:** Source positivity, lower clock, and physical gap cap do not force positive corrected
  completed-C5 slope.

## Goal

Test whether pointwise constraints on actual positive theta orbit close C5 first-contact gate:

`positive U,B,Q`, `0 < gap < 20`, `5B < U+3B`

were proposed to imply positive corrected C5 slope.  That implication would give global positivity
of completed C5 orientation, then fixed-action Jacobian orientation, compact/tail rank-four
assembly, CLG/TTF or Weil positivity, and RH.

## Gates

- [x] 0 → 1  in-progress: exact corpus-derived cone and RH chain frozen
- [x] 1 → 2  fully-proven: exact seam sign plus continuity perturbation
- [x] 2 → 3  formalized: Lean module and closed route-killing theorem
- [ ] 3 → 4  publication-ready: not pursued for isolated no-go

## Approach

The corrected-slope seam restriction is the exact degree-twelve polynomial
`modularThetaC5FixedActionSeamPolynomialReal`.  At squared modular gap `X=9`, Lean proves this
polynomial is strictly negative.  Perturb seam state along

`U=3ε`, `B=ε`, `Q=3/16`, `0<ε≤1`.

Then every source coordinate is positive, `5B<U+3B`, reconstructed gap is `9-6ε²∈(0,20)`, and
continuity preserves negative corrected C5 slope for sufficiently small positive `ε`.

## No-go closure

- **Exact killing theorem/mechanism:**
  `not_forall_strictSourcePositiveCappedLowerClockCone_c5ExactCompletedSeamSlope_pos` gives a
  closed Lean negation of the proposed universal static-cone implication.
- **Strongest positive survivor:** The exact seam separator changes sign within physical cap.
  `exists_modularThetaC5FixedActionSeam_transition_wall` proves a zero at some
  `X∈(9,191/10)`, between exact negativity at `9` and corpus positivity on
  `[191/10,20)`.  Thus C5 geometry has an intrinsic transition wall, not one uniform physical
  chamber sign.
- **New insight:** Remaining viable C5 proof must either couple the independent refined projective
  clock/scale laws with the gap cap, or establish history-dependent actual-orbit incidence.  This
  card does not test that stronger joint capped-refined chamber.
- **Status:** Paper proof dependency-closed.  Lean module
  `GaloisForLFunctions.HTGeometry.ExactCompletedC5AdaptedPhysicalConeNoGo`; direct check and targeted
  module build required/passed in final audit.

## Literature audit

Planat--Solé (2026) treats second-level concavity; Salazar (2026) treats order-moment transport.
Neither contains this spatial log-cumulant seam separator or adapted physical-cone no-go.

## Log

- 2026-08-29 — Conjecture falsified; exact capped-cone counterexample and transition wall
  formalized in Lean.
