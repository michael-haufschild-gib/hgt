# BV--co-Poisson principal-normal connection law

- **ID:** `bv-copoisson-principal-normal-connection-law`
- **Stage:** 3-formalized / TERMINAL CONNECTOR / NOT NEW SCIENTIFIC KNOWLEDGE
- **Type:** KNOWN IDEAL-FACTORIZATION REFINEMENT / INTERNAL RH-ROUTE INTERFACE
- **Source:** `suzuki-terminal-frontier-ledger.md`,
  `bv-prime-window-decimation-boundary-contraction-rh.md`
- **Statement:** Pole-cancelled BV prime-window source is the canonical normal derivative of
  completed co-Poisson multiplier ideal; its square-index decimation character therefore lives on
  source quotient's conormal jet rather than on an adjoined divisor fibre.

## Goal

Refine the already-known co-Poisson ideal factorization used by the proposed BV-to-co-Poisson
singular graph. Burnol source vectors have
Mellin form `Lambda * g`; BV source has logarithmic pole `g * Lambda'/Lambda`. Multiplication by
`Lambda` gives `g * Lambda'`, which is not another source-ideal vector but exact normal class of
derivation across principal ideal `(Lambda)`.

Required theorem must be established before choosing zero. It does not prove metric sign. If
normal class admits source-canonical contractive quotient completion compatible with finite
square-decimation Stein defect, existing BV contraction endpoint proves RH.

## Anti-loop checkpoint

1. **Unresolved arrow changed:** concrete BV-to-co-Poisson graph typing, immediately before
   `COPOISSON-CRITICAL-BOUNDARY-DISSIPATION`.
2. **Rediscovery verdict:** quotient Berezin diagonal, BV residue character, pole cancellation,
   finite Stein defect, and the local co-Poisson ideal factorization were already closed. The
   derivation-induced normal-class formulation is a formal refinement of that known factorization,
   not new scientific knowledge.
3. **Falsifier:** cancelled source differs modulo completed multiplier from `2 M_W Lambda'`, or
   forward/inverse window normal jets fail exact Mellin-character covariance.
4. **Scientific payload:** source quotient identification only. No sign or RH-equivalent bound is
   asserted.

## Gates

- [x] 0 -> 1: source object, target quotient, collision set, and falsifiers fixed
- [x] 1 -> 2: universal principal-normal classification and BV specialization proved on paper
- [x] 2 -> 3: exact identities formalized and wired to existing dilation orientation
- [x] hostile metric audit: standard critical norm fails, logarithmic quotient collapses, and no
  nonzero compact multiplicative seed repairs extended-property-S resonance
- [x] external novelty audit against co-Poisson, model-space, and conormal literature
- [x] endpoint audit: no RH composition; universal noncompact completion is nonselective and the
  remaining source-canonical dagger positivity is the RH-bearing condition itself

## Candidate theorem

Let `A` be a commutative differential algebra, `Lambda` a non-zero-divisor, and
`I=(Lambda)`. Derivation induces an `A`-linear normal map

```text
beta_Lambda : I -> A/I,
beta_Lambda(Lambda*g)=[(Lambda*g)']=[Lambda'*g].
```

Thus `beta_Lambda` is multiplication by conormal class `[Lambda']`; interior derivative
`Lambda*g'` vanishes in quotient. In completed zeta/co-Poisson specialization, general compact-BV
cancelled source satisfies

```text
C_W
 = Lambda * (pole divided difference - 2 error)
   + 2 M_W * Lambda',

C_W mod (Lambda) = 2 M_W * Lambda'.
```

At zero of multiplicity `m`, this normal class has order `m-1` and leading coefficient
`2m M_W(rho+1/2)` times leading coefficient of `Lambda`. It is same multiplicity-aware Laurent
coordinate already used by BV tomography, now obtained as source-ideal normal jet.

For argument dilation `W(rx)` and expansion `W(x/r)`, normal classes transform by

```text
r^(rho-1/2),   r^(1/2-rho)
```

on divisor jet. Exact square-index coefficient decimation is therefore candidate boundary action
on this conormal quotient.

## Hostile metric audit

- Ordinary co-Poisson source ideal kills `Lambda*g` and cannot contain Laurent pole itself.
- Ordinary Dirichlet-Hardy coefficient norm is already excluded.
- Total derivative `(Lambda*g)'` is not allowed to be silently put back in source ideal; its
  quotient class is exact obstruction to derivative invariance.
- Multiplicity greater than one must use full quotient jet, not only point evaluation:
  `Lambda'(rho)=0` can coexist with non-zero order-`m-1` normal class.
- Any norm chosen from divisor residues is circular. Candidate metric must arise from compact
  co-Poisson seeds or finite coefficient Stein defect.

## Terminal metric verdict

The proposed compact co-Poisson metric provider is refuted unconditionally. Canonical sharp seed
has exact critical flux `(1/4) log T + o(log T)` and leaves standard `L2`; its logarithmic boundary
ideal is dense; critical eta seed misses both property-S parity lattices; and all compact
multiplicative resonance repairs vanish by moment rigidity. These statements are formalized in the
five `BVCoPoisson*` route-closure modules.

Allowing arbitrary noncompact completion does not help: Gamma--Gaussian property-S envelope exists
for every moderate datum and preserves off-line divisors. Completion and dualizability therefore
carry no RH discrimination. Only source-generated causal-dagger positivity on the normal class
remains. That is not missing connector infrastructure; combined with proved dilation character it
is exact RH-bearing orientation. This parent connector is closed without an RH claim.

## Log

- 2026-07-24 — terminal corpus audit found BV source and Burnol quotient were connected only by a
  conjectural singular graph. Burnol intertwining shows compact co-Poisson sources are completed
  multiplier multiples; BV pole cancellation exposes their derivation-normal class. Card created
  before formalization.
- 2026-07-24 — hostile collision audit found the stronger local co-Poisson ideal factorization
  already proved in `burnol-copoisson-berezin-diagonal-reflection-law.md`, equations (14)--(18).
  The conormal derivative formulation remains a checked internal connector but is demoted from
  novelty. The unchanged frontier is construction or refutation of the source-canonical
  scale-zero contractive metric.
- 2026-08-01 — metric-provider program terminalized. Sharp critical flux, dense quotient,
  half-weight resonance, and compact-seed rigidity no-gos are formalized; universal noncompact
  completion is nonselective. Remaining source-causal dagger is the RH-bearing endpoint, not a
  further generic completion problem.
