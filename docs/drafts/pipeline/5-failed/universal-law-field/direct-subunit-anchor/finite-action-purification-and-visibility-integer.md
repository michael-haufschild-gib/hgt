# Finite-action purification and visibility-integer failure

- **ID:** `ULF-DSA-004-FAILED`
- **Stage:** 5-failed
- **Type:** retired source-to-completion mechanisms with exact positive survivor
- **RH used:** no
- **Parents:** `ULF-PHIN-001`, `ULF-PHPCF-001`, `ULF-SACWHT-001`, `ULF-INBSG-001`,
  `ULF-PBTIA-001`, `ULF-PHPTCIS-001`

## 1. Retired mechanism A: finite-action purification

The proposed closure was:

```text
construct K_form from literal integer/Poisson data,
length(K_form)<=B,
transport K_form through theta completion,
end at every off-line rank-one relation horizon.
```

`ULF-PHPCF-001` correctly proves that no such bounded path can reach a pure horizon: the endpoint
distance exceeds the whole primitive collision budget. But this does not create an RH
contradiction, because actual theta completion is not a bounded or trace-norm-continuous path.
Its canonical transfer is

```text
E_epsilon(T)=T(epsilon I+T)^(-1),
```

which converges strongly to the closed observer boundary while retaining a maximally nonuniform
norm germ. Fixed-cone results prove that scale lifts share one primary class and their relative
scale exponentials are null-homotopic. Thus requiring the source budget to remain a path-length
bound through this singular limit changes the completion category and has no corpus theorem
behind it.

**Verdict:** the finite-action transport clause is not an open lemma. It is the wrong model of
completion.

## 2. Retired mechanism B: visible charge is the integer

For the prime--Hodge integral--nuclear source `T`, define the off-wall visibility marginal

```text
T_vis(a)=V_a T V_a,
V_a(n,p)=sech(a log(p)/2).
```

The conjecture treated `Tr(T_vis(a))` as the formation integer and hoped to combine integrality
with a strict subunit estimate. `ULF-PHPTCIS-001` proves instead

```text
Tr(V_a T V_a)+Tr(C_a T C_a)=1,
C_a(n,p)=tanh(a log(p)/2),
```

and, for every `a!=0`, both terms lie strictly between zero and one. The visible marginal is
therefore genuinely fractional. Common recovery and the functional-equation lift are
information-neutral, so they cannot erase the complementary contrast marginal.

**Verdict:** marginal integrality is false; total integrality is true but nonselective.

## 3. Strongest positive survivor

The failures expose the correct carrier of any future integer:

```text
not endpoint distance,
not singular-completion scale,
not visible charge,
not total conserved charge,
but a prime-marked relative pairing of open contrast history with the completion ideal.
```

Such a pairing would have to be constructed before divisor specialization, be nonzero for every
off-wall obstruction, possess an integral index, and admit a nuclear representative bounded by
the literal Euler budget. The existing pure-state radius and two-channel conservation laws would
then become useful quantitative inputs without pretending singular completion is norm-continuous
or deleting information.

## 4. Carrier warning

Two corpus operators are easy to conflate:

- `ULF-PHIN-001` constructs the separable history--prime `T` with explicit norm bound;
- `ULF-POINH-001` constructs the physical Pluecker source used by actual singular boundary
  transfer.

No theorem identifies them or intertwines their completions. Any future relative-index law must
either be constructed directly on the physical Pluecker carrier or prove an explicit
prime/history/completion intertwiner. An arbitrary Hilbert-space unitary preserves pure-state
distance but not the source or completion structure.

## 5. Formal status

Failure is deduced from existing paper and Lean certificates for singular boundary transfer,
fixed-cone scale triviality, common-recovery information neutrality, and the positive
prime--Hodge object. The two-channel operator fusion is paper-proved in `ULF-PHPTCIS-001`; no Lean
module was written during this read-only audit.
