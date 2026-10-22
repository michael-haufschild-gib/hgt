# Essential CCM cusp realization and endpoint-concentration law

- **ID:** `ccm-essential-cusp-boundary-layer-sharpness`
- **Stage:** 3-formalized
- **Type:** THEOREM, sharpness witness
- **Scientific status:** `[UNCONDITIONAL] [LEAN] [CORPUS-NEW] [EXTERNAL NOVELTY OPEN] [NOT RH]`
- **Lean source:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMEssentialCuspBoundaryLayer.lean`
- **Depends on:**
  `ccm-meromorphic-cusp-laurent-charge-law.md`

## Result

The meromorphic one-loop exclusion is sharp in an infinite-dimensional Hilbert
target.  Let

```text
H = L2((0,1), dt),
f(z)(t) = 2 sqrt(2) exp(-t exp(-i z)).
```

Lean proves, without hypotheses on unformalized mathematical objects:

```text
f : C -> H is entire,
f(z + 2 pi) = f(z),
||f(i y)||^2 / (1 - exp(-exp(-y))) -> 4,
```

and the descended punctured-disk cusp

```text
F(q) = f(z),  q = exp(i z),
```

is not meromorphic at `q=0`.

The last conclusion is not asserted from an informal essential-singularity
argument.  It is discharged by the formal meromorphic charge law: a
meromorphic `2 pi`-periodic positive-density cusp would require an integer
Laurent charge `n` satisfying `2n=1`.

The packaged Lean theorem is

```text
exists_entire_twoPi_periodic_fourUnit_essential_Hilbert_cusp
```

and simultaneously supplies entire log-holomorphy, one-loop periodicity,
four-unit density, and nonmeromorphic descent.

## Exact boundary-layer law

Put

```text
B_u(t) = 2 sqrt(2) exp(-t/u),
E(u) = integral_(0,1] B_u(t)^2 dt.
```

For every `u>0`, Lean proves the exact identity

```text
E(u) = 4u(1-exp(-2/u)).                                  (1)
```

Consequently

```text
E(u)/(1-exp(-u)) -> 4.                                   (2)
```

For every fixed `0<delta<=1`, define the energy separated from the cusp
endpoint,

```text
E_delta(u) = integral_(delta,1] B_u(t)^2 dt.
```

Lean proves

```text
E_delta(u)
  = 4u(exp(-2 delta/u)-exp(-2/u)),                       (3)

E_delta(u)/(1-exp(-u)) -> 0.                             (4)
```

Equations `(2)` and `(4)` are an endpoint-concentration law: all four units of
normalized thermal energy escape into every shrinking neighborhood of
`t=0`; every region with positive distance from that endpoint loses all
normalized mass.

The Hilbert cusp realizes this profile exactly:

```text
||f(i y)||^2 = E(exp(-y)).                               (5)
```

No numerical computation enters `(1)`--`(5)`.

## Frontier consequence

C38 left four possible survivors:

1. a fixed essential/nonmeromorphic cusp;
2. a cofinal family with no fixed germ;
3. non-scalar monodromy;
4. graph-topological transport.

This theorem proves survivor 1 is nonempty even under stronger regularity on
the logarithmic cover: `f` is entire and has the ordinary `2 pi` deck period.
Therefore periodicity, log-holomorphy, Hilbert target structure, and exact
four-unit density do **not** exclude the essential category.

Any proof killing the CCM lane must use additional source-specific structure.
The remaining source claim cannot be replaced by another local cusp
regularity premise.  It must distinguish the published
von-Mangoldt--Gamma source from the explicit boundary-layer witness, for
example by proving or refuting a definition-level transport into

```text
D_Xi = closure(P_- M_(-2 Xi'/Xi))
```

with the four-unit extended Hilbert--Schmidt boundary bound, or by deciding
the actual active-even source coefficient sign in C29--C30.

## Collision audit

- C34 proves square-root boundary regularity but does not construct a
  periodic Hilbert-valued cusp.
- C35--C37 exclude fixed holomorphic/ramified/bounded logarithmic models.
- C38 excludes every meromorphic Laurent germ and explicitly leaves
  essential descent open.
- Existing mass-escape cards concern the Suzuki Möbius channel, not the CCM
  one-loop cusp and not the exact thermal density above.
- Corpus search found no prior construction proving all four clauses of the
  packaged existence theorem.

The exponential boundary layer is analytically elementary, so no external
priority claim is made without a dedicated literature audit.  Corpus novelty
is the sharp CCM connector: an entire one-loop Hilbert cusp realizes the exact
four-unit normalization precisely through essential descent.

## Scope

- `[PROVED]` Infinite-dimensional Hilbert target.
- `[PROVED]` Entire logarithmic-cover map.
- `[PROVED]` Exact `2 pi` periodicity.
- `[PROVED]` Exact four-unit thermal density.
- `[PROVED]` Endpoint concentration away from every fixed `delta>0`.
- `[PROVED]` Descended cusp is nonmeromorphic.
- `[NOT PROVED]` Witness is the published CCM arithmetic source.
- `[NOT PROVED]` Source-to-Xi graph transport.
- `[NOT PROVED]` RH or death of the CCM lane.
