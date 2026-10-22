# Xi reflection incidence trace-one source convergence

- **Label:** `FRANK-TRACE1-SOURCE`
- **Route:** cross-route Frankenstein seam
- **Parents:** `XiReflectionIncidenceSchattenSpectrum`, rational-adelic fixed-Xi Gamma Bockstein
- **Stage:** 1-in-progress
- **Type:** theorem / exact source interface / producer reduction
- **Status:** `[PAPER-PROVED] [LEAN EXACT-LEAF GREEN] [NOT RH]`

## Question

Does endpoint Schatten-one admission merely repackage a divisor condition, or is it ordinary
convergence of a literal prime-labelled source quantity preserving multiplicity and both reflection
orientations?

## Construction

For a positive-height Xi divisor point `rho` and prime `p`, define trace-one rational-adelic cyclic
residue from the two actual fixed-Xi Gamma transports. Weight it by the literal reflection incidence
cardinality `m_rho^2` and the marked source norm. The resulting nonnegative source mass satisfies

```text
sourceMass(rho,p)
  = norm(first nonzero Xi jet at rho) * S_1(rho,p).
```

The scalar is strictly positive on divisor support. Therefore no coefficient cancellation,
reordering, or multiplicity erasure is available.

## Proved endpoint

Lean proves, for every retained divisor class:

```text
ordinary increasing-prime convergence of sourceMass
  iff summability of sourceMass
  iff summability of S_1
  iff Re(rho)=1/2.
```

Globally, ordinary source landing for every retained Xi divisor class is equivalent to endpoint
nuclear admission and hence to RH.

## Heavy-conjecture audit

- Completed prime-Gamma/Hedenmalm trace terms fail as producers: they use a rectangular-resolvent
  squared transform, not this undamped cyclic residue.
- Local Sonin prime-power tangent carriers are trace class, but the all-prime trace norm is
  nonsummable even at the neutral parameter; local trace class cannot be assembled globally.
- Hellinger/theta reconstruction converges in a different `L^2` source topology and has no
  loss-zero continuous map to this Kummer/log-prime trace-one residue.
- Generic nuclear Frechet landing and positive-chamber Stokes operators permit seminorm or height
  loss. Neither implies landing in one fixed Schatten-one ideal.

## Lean realization

`XiReflectionIncidenceTraceOneSourceConvergence.lean` defines the cyclic residue and positive source
mass, proves the exact scalar identity, converts nonnegative ordinary partial-sum convergence to
summability, and proves the local and global RH equivalences. Direct `lake env lean` and exact-module
`lake build` pass. Headline axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Module is wired into `RHTower.lean`.

## Honest boundary

This theorem supplies the exact source carrier but not its unconditional convergence. Remaining
producer must prove a loss-zero estimate in the literal undamped trace-one norm. Any damping,
`q>1`, variable ideal, conditional cancellation, or source-topology loss misses the theorem.

## Gates

- [x] 0 → 1: literal coefficient-faithful source mass constructed
- [x] 1 → 2: exact convergence/nuclearity equivalence proved
- [x] 2 → 3: Lean module, exact leaf build, forbidden-declaration scan, axiom audit, umbrella wiring
- [ ] 3 → 4: unconditional source convergence producer

## Log

- 2026-08-13 — exact trace-one source interface formalized. Producer audits eliminate cancellation,
  local trace class, and lossy source landing; loss-zero undamped convergence remains open.
