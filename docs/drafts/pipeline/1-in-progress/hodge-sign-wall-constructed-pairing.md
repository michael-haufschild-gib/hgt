# The Hodge sign of the constructed pairing on the reflection-odd carrier

- **ID:** hodge-sign-wall-constructed-pairing
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, unconditional survivors) + open core (the mass-zero law)
- **Source:** step 3 of the intersection-form programme; successors of
  `gauss-propagated-iterate-log-mean` and `gauss-multiplace-label-faithful-assembly`
- **Statement (what is now proved):** The pairing of the two retained reflection-odd components
  of the source-zero horizontal carrier, weighted by the assembled residue current, is an
  unconditionally positive-semidefinite, reflection-even, label-faithful current with the exact
  critical radical: `H(q,p) = (log 2/2)·current(p)·density(p)·t_q·(p^{t_q} − p^{−t_q}) ≥ 0`
  with `t_q = 2 Re(q) − 1`, `H = 0 ↔ Re(q) = 1/2`, and `H` invariant under the line-conjugate
  reflection.  **The Hodge sign of the constructed pairing holds.**  The Hodge-index
  application — total mass zero, forcing every copy onto the line — is proved equivalent to RH.
- **Open core `[OPEN CORE]`:** the mass-zero law: a trace identity evaluating the nonnegative
  `H`-mass through prime-side data and showing it vanishes.  This is the residual wall.

## The wall, well-posed

Step 3 asked for the Hodge sign of the assembled pairing on the reflection-odd carrier.  The
carrier retains two odd components per Xi copy (the cofinal tail log and the prime-labelled
Gamma Bockstein), both reversing under `ρ ↦ 1 − conj ρ` and both vanishing exactly on the line.
Their product — the natural quadratic pairing of the odd part with itself, weighted by the
strictly positive assembled residue current — is therefore an *odd-square*: nonnegative by
construction-level algebra, even under reflection, zero exactly on the line.  This is created
positivity in the corpus's sense (it is manufactured by pairing the two retained orientations,
not inherited from an ambient cone), and it converts the wall from a sign question into a mass
question:

```
RH  ⟺  the unconditionally nonnegative current H has zero total mass
     ⟺  every label of every copy sits at the bottom of the hyperbolic mass shell t·(p^t−p^{−t}).
```

## Attempts and pivots (this card's audit trail)

**Attempt 1 — self-dual operator subtraction (the conjectured mechanism).**  Finitize the
divergent raw positive corner by exchanging with its Poisson/Fourier dual instead of truncating.
On the theta side this reproduces exactly the classical self-dual representation of the
completed zeta (the `∫₀^∞ = ∫₁^∞ + dual + poles` exchange): it yields manifest FE symmetry at
operator level and reality on the critical line — but the sign of the exchanged remainder
against critical-line oscillation is equivalent to the mass-zero statement itself.  *Exact
failure point: the dual exchange preserves positivity only where the kernel does not oscillate;
making it global is the wall, not a route around it.*

**Attempt 2 — FE as an antiunitary intertwining of the actual compact operator (PT structure).**
An intertwiner implementing `ρ ↦ 1 − conj ρ` on the Hedenmalm theta-source inverse would make RH
an "unbroken-phase" statement.  Killed as a *producer* by the corpus's conjugation-blindness
no-go: any use of the intertwiner that factors through the divisor-level reflection yields no
sign.  Surviving requirement, recorded for future work: the intertwiner must come with a
definitizable Krein structure — which is again the missing positivity, now in Krein form.

**Attempt 3 — trace-identity evaluation of the H-mass.**  The explicit formula (Poisson on the
idele classes — the only ℤ-specific global identity in reach) evaluates holomorphic samples
`∑ g(ρ)²`; the H-mass is a non-holomorphic square (`|odd part|²`-type).  This is the corpus's
`∑g² vs ∑|g|²` gap in exact form.  *Sharpened Poisson conjecture (the successor of the step-3
mechanism conjecture): a bilinear/Poisson upgrade of the explicit formula that reaches one
positive-definite non-holomorphic sample of the divisor — equivalently one trace identity with
target the `H`-mass — closes RH.  Nothing weaker suffices, by the firewall below.*

**Pivot outcome.**  The sign itself is free once the two odd orientations are paired — proved
below.  All difficulty is the mass evaluation; the firewall shows it cannot come from the
pairing's own interface.

## Kill-tests passed and formalized

1. **Beurling/interface firewall (formalized).**  The sign, evenness, and radical laws of the
   pairing hold for arbitrary label sizes `s > 1` and arbitrary rate configurations — they are
   pure interface algebra.  An explicit reflection-closed off-line configuration (`t = ±1/2`,
   `s = 2`) has strictly positive mass.  Hence *no proof from the pairing's local interface,
   even assuming closure under the divisor reflection, can force mass-zero*: the step-3 proof
   must consume data distinguishing the actual Xi divisor — global Poisson/bilinear input.
   (`hodgeMass_interface_cannot_force_vanishing`.)
2. **Conjugation blindness (formalized inside the firewall).**  The positive-mass witness is
   closed under `t ↦ −t`: reflection symmetry of the configuration does not reduce the mass,
   because `H` is even.  So `conj ρ = 1 − ρ` alone can never force vanishing — matching the
   corpus's no-go, now at this exact pairing.
3. **Re-encoding audit.**  The mass-zero ⟺ RH equivalence is an RH-equivalent statement and is
   labeled as the open core, not as progress.  What is claimed as progress: the unconditional
   positivity/evenness/radical laws, the closed hyperbolic form, and the firewall — none of
   which were previously formalized for this object.

## Gates
- [x] 0 → 1  wall frozen for the constructed pairing; attempts 1–3 run and recorded
- [x] 1 → 2  unconditional survivors paper-proved (short algebra over the carrier's closed forms)
- [x] 2 → 3  formalized: `RHTower/GaussHodgeMassCurrent.lean`; umbrella-wired; axiom-clean
- [ ] `[OPEN CORE]` the mass-zero trace identity (sharpened Poisson conjecture above)

## Log
- 2026-08-11 — created; attempts 1–3 executed and recorded; Hodge sign proved for the
  constructed pairing (odd-square positivity); mass-zero ⟺ RH formalized; boost-square closed
  form formalized; interface firewall formalized with reflection-closed positive-mass witness.
