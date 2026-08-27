# PW-B reflection-orbit aggregate no-go (2026-08-27)

Formal module `GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekReflectionOrbitAggregateNoGo` is wired.

Exact result: critical-line reflection `J(s)=1-conj(s)` sends closed PW Borel recoil holonomy to its conjugate, hence `D_k(J(s))=-D_k(s)` for physical phase `D_k=Im H_k`. Every fixed two-copy linear aggregate equals `(a-b)D_k(s)` and vanishes in nonreal open strip iff `a=b` or `Re s=1/2`. Equal source weights are identically blind even off wall.

Positive survivor: quadratic orbit energy is exactly `2 D_k(s)^2`, nonnegative, and vanishes iff wall. Universal zero over Xi divisor support at any fixed grade is exactly RH.

No-go: linear reflection-complete global aggregation cannot be PW-B producer. Remaining core must force quadratic energy zero from source, or derive physical unequal-weight/oriented transport beyond self-similar finite-mass evaporation.

Verification: direct Lean passed; targeted build `11423/11423`; axioms only `propext`, `Classical.choice`, `Quot.sound`. Card `docs/drafts/pipeline/3-formalized/parikh-wilczek-reflection-orbit-aggregate-no-go.md`.

Frontier map is user-declared read-only; do not edit it.