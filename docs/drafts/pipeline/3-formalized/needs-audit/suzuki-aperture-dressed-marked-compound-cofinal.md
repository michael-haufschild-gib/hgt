# Suzuki aperture-dressed marked compound cofinal law

- **ID:** `suzuki-aperture-dressed-marked-compound-cofinal`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM]`
- **Frontier:** `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/SuzukiApertureDressedMarkedCompoundCofinal.lean`

## Goal

Determine whether cubic aperture dressing that makes Suzuki's wall-light field square summable can
also carry the exact marked halfgap completion and division-free local--global compound numerator,
or whether those two obligations require another divergent copy of critical wall mass.

## Corpus audit

Corpus search was run before conjecturing. Closest established results were:

- bare wall amplitude supplies exact minimal `d^2` rooted completion;
- bare critical wall square is determinant-line far-hinge density;
- bare all-prime rooted wall mass is not summable;
- cubically aperture-dressed boundary atoms have summable norm squares;
- dressed positive/negative light fields satisfy exact Ward completion.

No declaration joined dressing to the marked rooted block or to the complete division-free
local--global compound numerator. Search also ruled out local capacity, bicausal splice, coherent
bounded-response, and raw all-prime Hilbert-vector repairs.

## Conjecturing loop

### Conjecture 1 — use bare rooted wall completion cofinally

**Falsified by corpus theorem.** Depth-zero squared wall amplitudes are not summable over primes;
no nonzero prime-independent scalar repair changes that. Bare completion cannot be assembled in an
ordinary all-prime Hilbert carrier.

### Conjecture 2 — light dressing solves only the reflected current

**Too weak.** Existing dressed-light completion proves summability and the local Ward identity,
but does not state that same atom pays marked halfgap debt or carries the compound determinant line.

### Conjecture 3 — pre-split cubic dressing preserves every quadratic wall role

**Proved.** For dressed atom `omega_pe`, sharp marked completion is

```text
MarkedForm(omega*r, omega*s) + d^2 (omega*s)^2
  = |omega|^2 (r-m*s)^2.
```

It is nonnegative and summable on `Primes x Nat`. For complex division-free marked compound term,
common degree-two homogeneity gives

```text
Compound_pe = omega_pe^2 * Compound_base.
```

The atom squares are absolutely summable, hence compound cells are absolutely summable and their
cofinal sum is exactly

```text
(sum_pe omega_pe^2) * Compound_base.
```

### Conjecture 4 — this already identifies actual rectangular trace

**Rejected as theatre.** The theorem treats one fixed marked base packet. It does not prove actual
Robin/Gamma/holonomy coordinates are a uniformly bounded base packet, nor that their rectangular
trace equals this compound sum. Those are precisely next occurrence and Schur-comparison gates.

## New knowledge

Cubic innovation is not merely a light-cone summability trick. Because it acts before projective
division, it simultaneously cofinalizes three quadratic faces of one source:

```text
negative/positive light Gram,
minimal marked halfgap completion,
division-free compound determinant line.
```

No duplicate wall coordinate or infinite subtraction is required. This removes a real
double-counting ambiguity in the frontier assembly. It does not prove RH and is not counted as
actual trace occurrence.

## Formal status

Lean proves unconditionally:

- absolute summability of dressed boundary-atom squares;
- exact nonnegative dressed marked rooted-completion square;
- all-prime/depth summability of that completion;
- exact dressed compound factorization;
- absolute summability and exact cofinal sum of fixed-base marked compound terms.

Direct Lean check passes. Module is umbrella-wired without an umbrella build. Target-only Olean and
axiom audits are pending until final targeted verification.

## Refined open core

Prove one source-occurrence theorem for actual rectangular data:

1. factor actual marked Robin/Gamma/holonomy local coordinates as dressed atom times a base response
   with enough uniform control for absolute cofinalization;
2. identify resulting compound sum with actual division-free rectangular Xi trace;
3. prove remaining holonomy Schur residual uniformly lower-semi-bounded.

## Log

- 2026-08-16 — Corpus-audited conjecture loop; paper proof and Lean formalization completed.
