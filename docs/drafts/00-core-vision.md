# The Vision — why this field exists

> "Γ satisfies no algebraic differential equation — and neither does ζ. ξ is hypertranscendental." —
> Hölder, 1887.

A short, plain statement of what the field is for. No proofs here and none are claimed. The mathematics
is in the gatekeeper conjectures (`00-foundations-native-objects-and-gatekeepers.md`) and the buckets
(`door/`).

---

## 1. The reason

Almost every tool for proving deep facts about numbers is built for functions that obey a clean
differential rule of change. `ζ` does not. Hölder proved in 1887 that `ζ` satisfies no algebraic
differential equation at all — it is **hypertranscendental**. So the differential toolbox (differential
Galois theory, the `E`/`G`-function formalism, the period ring, Siegel–Shidlovsky) cannot reach `ζ`'s
values or zeros. The objects we most want to understand sit outside the country those tools survey, and
no theory is built for them.

## 2. The idea

If there is no differential rule of change, use a different kind of rule: one about **rescaling**, not
nudging. Mahler did this for functions with a *single* rescaling and reached transcendence facts the
differential toolbox could not. `ζ` is built from all the primes at once and carries **one rescaling per
prime** — `σ_p : x_p ↦ p^{-1}x_p`, for every prime `p`. It needs infinitely many rescalings running at
the same time.

The field widens Mahler's single rescaling into the simultaneous action of one per prime:
**multi-`q`-difference Galois theory.** Unique factorization keeps the lanes independent — the rescaling
for 2, for 3, for 5 never collapse together — which is the ground the construction stands on (the "free
flow").

## 3. What we are aiming for

In this setting two questions that look separate from the classical side may become two views of one
statement:
- **where** the zeros sit (the Riemann Hypothesis);
- **what kind** of numbers the zeros are — whether they are genuinely independent (the transcendence
  question).

The aim is a theory in which RH is a feature of the geometry rather than an external wall, and in which
RH and the independence of the zeros are one statement seen from two sides. The single object on which
both sides live and the precise form of the unification are developed in
`door/bucket-A1-A2-unification-the-carrier.md`.

## 4. What counts as progress

The deliverable is the theory: each road laid on this ground — a native object made precise, a
difficulty located exactly, a gatekeeper turned into a theorem — is progress whether or not RH itself
falls. RH is the hoped consequence, not the only measure. The gatekeeper conjectures and their current
status are in `door/00-status.md`.
