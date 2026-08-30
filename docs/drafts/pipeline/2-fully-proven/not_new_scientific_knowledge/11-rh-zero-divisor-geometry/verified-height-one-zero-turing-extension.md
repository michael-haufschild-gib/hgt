# Verified height extends by one Turing-counted zero

- **ID:** verified-height-one-zero-turing-extension
- **Stage:** 2-fully-proven
- **Type:** THEOREM (certified computation) / `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** Platt--Trudgian verified prefix; Arb Turing-method zero count;
  `VerifiedHeightAmplification.lean`
- **Statement:** `[PROVED]` Every nontrivial zero `rho` of the Riemann zeta function with
  `0 < Im rho <= 3,000,175,332,800.43359375` lies on the critical line.

## Goal

Decide whether Route D can produce a strict verified-height extension once certified computation is
allowed.  The endpoint is the exact dyadic rational

```text
T_1 = T_0 + 111/256
    = 768044885196911/256
    = 3,000,175,332,800.43359375.
```

## Inputs

`[SEARCH; PUBLISHED]` Platt and Trudgian proved that

```text
T_0 = 3,000,175,332,800,
N(T_0) = N_0 = 12,363,153,437,138,
```

and that every zero through `T_0` is simple and on the critical line.

`[CERTIFIED COMPUTATION]` Arb's `acb_dirichlet_zeta_nzeros` uses Turing's method to count all
nontrivial zeta zeros with `0 < Im rho <= T`, including multiplicity.  At the exact endpoint `T_1`,
192-bit ball arithmetic returns the exact integer

```text
N(T_1) = 12,363,153,437,139 = N_0+1.
```

The reproducible source is
`computations/2026-07-11-route-d-turing-height-extension-arb.c`; its captured output is in the
adjacent `.txt` file.  Arb's official API documentation states that the zero-count and individual
zero routines use Turing's method:
<https://arblib.org/acb_dirichlet.html#riemann-zeta-function-zeros>.

## Proof

There is exactly one zero counted with multiplicity in the increment `(T_0,T_1]`.  If that zero
were off the critical line, the functional equation and Schwarz symmetry would supply the distinct
zero

```text
rho |-> 1-conj(rho)
```

at the same positive ordinate and with the same multiplicity.  The count increment would then be at
least two, contradicting `N(T_1)-N(T_0)=1`.  Hence the unique new zero lies on the critical line.
All earlier zeros lie on the line by the Platt--Trudgian certificate, proving the statement.

This is the paper-level specialization of the axiom-clean Lean theorem
`RHTower.rhVerifiedThrough_amplify_of_increment_ncard_le_one`.  The external numerical count itself
has not been formalized in Lean.

## Independent boundary check

At 256 bits, Arb isolates the adjacent nontrivial zeros as

```text
rho_(N_0+1) = 1/2 + i *
  [3000175332800.286524182413025478326707081851708198936873971352041023810581745375833376428202901696507
   +/- 3.80e-65],

rho_(N_0+2) = 1/2 + i *
  [3000175332800.434527689105328273081765501600923663114740853282724213190790269688442533139617031447943
   +/- 3.80e-65].
```

Thus `rho_(N_0+1)` lies below `T_1` and `rho_(N_0+2)` lies above it.  This independently confirms
the chosen endpoint is strictly between consecutive zeros.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The result is a new certified finite-height endpoint, but the
mechanism is exactly published Turing zero counting plus the elementary reflection-pair argument.
It introduces no new analytic or arithmetic theorem and fails the parent-theory and anti-theatre
gates.  It is therefore stored in `not_new_scientific_knowledge`, not promoted as a research theorem.

The result does, however, answer an operational Route D question: once computation is authorized,
the one-zero consumer theorem yields a genuine strict amplification.  It does not address the
noncomputational source-to-divisor problem and does not prove RH.

## Gates

- [x] 0 -> 1 in-progress: exact endpoint and count certificate specified.
- [x] 1 -> 2 fully-proven: published prefix plus rigorous Turing count and reflection proof complete.
- [ ] 2 -> 3 formalized: the generic one-zero implication is in Lean; the external Arb count is not a
  Lean theorem or imported proof certificate.
- [ ] 3 -> 4 publication-ready: not a standalone scientific result; retain as a reproducible verified
  endpoint update.

## Log

- 2026-07-11 -- RunPod Arb certificate produced and independently bracketed by the adjacent zeros.

## Lean status update (2026-08-30) — consumer strengthened; the gate is a certificate, not a theorem

**Staleness audit.**  `RHTower.rhVerifiedThrough_amplify_of_increment_ncard_le_one` is present and
unconditional, exactly as the card claims:

```text
RHVerifiedThrough H → (stripZeroIncrement H U).ncard ≤ 1 → RHVerifiedThrough U
```

**New: the consumer is strengthened to a horizontal-fibre census.**
`formal/GaloisForLFunctions/RHTower/VerifiedHeightFiberAmplification.lean` (axiom-clean, wired,
exact leaf build clean):

* `stripZeroIncrementFiber H U t` — the increment's zeros at one ordinate, with finiteness and
  reflection-closure;
* **`rhVerifiedThrough_amplify_of_fiber_ncard_le_one`** —

  ```text
  RHVerifiedThrough H → (∀ t, (stripZeroIncrementFiber H U t).ncard ≤ 1) → RHVerifiedThrough U
  ```

* `stripZeroIncrementFiber_ncard_le_one_of_increment` — the whole-increment census implies the
  fibre census, so the new theorem **subsumes** the old one.

This is a genuine weakening of the required census: arbitrarily many new zeros are now allowed in
`(H, U]`, provided no two share an ordinate.  Reflection preserves the ordinate, so the pairing that
rules out an off-line zero always happens inside one fibre; requiring the whole increment to be a
singleton was throwing that away.  It also makes the connection to
`horizontal-singleton-zero-fibers.md` explicit: that card's predicate is exactly this census.

## Why this card cannot reach stage 3 by proof, and what would be required

`[ASSESSMENT]` The remaining inputs are **not open mathematics**; they are external certified
computations:

1. `RHVerifiedThrough T₀` for `T₀ = 3,000,175,332,800` — the Platt–Trudgian verification of
   `≈ 1.24 × 10¹³` zeros;
2. `(stripZeroIncrement T₀ T₁).ncard ≤ 1` — Arb's Turing-method count at `T₁ = T₀ + 111/256`.

Formalizing either inside Lean would require a verified numerical stack that does not exist:
rigorous Riemann–Siegel evaluation of `Z(t)` with certified error bounds, Turing's method for the
zero count, and kernel-executable interval arithmetic — then execution at height `≈ 3 × 10¹²`.  That
is a separate multi-year formalization project of a different character from this card, and it is
excluded by the session rule against computations.

The statement is true and provable in principle, so this is **not** a mathematical impossibility;
but by the available means the card's *mathematical* content is fully Lean-closed (and now
strengthened), while its *numerical* content remains an imported certificate.  The honest status is
therefore: **stage 2 with the mathematics complete**; a move to stage 3 requires either the verified
numerical stack above, or a decision that an externally certified computation counts as a
formalized input — which the pipeline's rules currently do not allow.

This is recorded so that no future session re-attempts the numerical route without first building
that stack.
