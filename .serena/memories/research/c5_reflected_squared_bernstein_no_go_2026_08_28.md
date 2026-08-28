# C5 reflected squared-profile Bernstein no-go (2026-08-28)

Formalized `GaloisForLFunctions.RHTower.ThetaCuspReflectedSquaredBernsteinNoGo`.

Key theorem: for every center `u` and rate `a ≥ 0`,
`exp (a*t^2) * thetaCuspReflectedSourceProduct u t → 0` at `+∞`. Proof combines the literal completed-theta envelope with `exp(2t)/t² → ∞`.

Generic survivor: every nonzero finite positive measure on `NNReal` has a bounded interval with positive mass, so its Laplace transform admits an exponential minorant `c exp(-Nx)`.

Capstone: no finite positive measure represents
`x ↦ thetaCuspReflectedSourceProduct u (sqrt x)` on `x ≥ 0`. The zero measure is excluded at `x=0`; every nonzero measure contradicts super-exponential decay in squared scale.

Route consequence: fixed positive Bernstein/complete-monotonicity representation after `t ↦ t²` is dead. Any viable C5 measure mechanism must be signed, scale-dependent, or applied before squared displacement; next frontier is literal theta atom–ray cancellation/action–jet coupling.

Validation: direct Lean check clean; targeted module build passed; axiom audit for envelope, decay, minorant, capstone reports only `propext`, `Classical.choice`, `Quot.sound`. Module wired into `RHTower.lean`. Card: `docs/drafts/pipeline/3-formalized/theta-reflected-squared-bernstein-no-go.md`.