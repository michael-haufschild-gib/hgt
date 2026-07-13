# Irrational circle order charge

- **ID:** `irrational-circle-order-charge`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`, `[RH CRITERION]`, `[BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/IrrationalCircleOrderCharge.lean`
- **Successor route:** `../../1-in-progress/irrational-circle-sem-holonomy-collapse.md`

## Theorem

Fix any prime `p`.  The circle-valued character

```text
m |-> [m log p] in R/Z
```

is injective on `m in Z`.  Equivalently,

```text
[m log p] = 0  iff  m = 0.                              (1)
```

This is the one-prime restriction of the already formalized injective circle charge on the full
prime-log lattice.  Its transcendence input is that no nonzero integral multiple of `log p` is an
integer.

For the local completed-zeta order define

```text
C_p(rho) = [ord_rho(Xi) log p].                           (2)
```

Then, for every fixed prime `p`,

```text
RH
  iff C_p(rho)=0 for every right-half Xi zero rho.        (3)
```

The completed symmetric Euler--Maclaurin contour index equals the same local order.  Therefore RH
is also equivalent to closure of this **single** circle phase on every actual right-half SEM
boundary.  No cofinal dyadic or arbitrary-modulus tower is required at the consumer end.

## Proof

`primeCircleHom_injective` sends equality of the one-prime circle charges to equality of the
corresponding finitely supported prime-exponent vectors, so `(1)` follows.  An Xi zero has positive
finite local order; hence `(1)` makes phase closure impossible at any right-half zero.  Conversely,
under RH there are no right-half zeros.

For an actual SEM split, `completedSEMContourIndexZ_eq_xiOrder` identifies its integral contour
index with `ord_rho(Xi)`.  The single-circle criterion then composes with the existing exact
completed-SEM charge criterion.

## Positive statement from finite-charge blindness

The bounded-exponent no-go has a sharp positive complement:

> a compact target can retain the real prime-flux channel if its exponent is unbounded; the circle
> `R/Z` does so, and one irrational prime-log phase is already faithful on integer multiplicity.

Thus the consumer does not intrinsically need a profinite tower.  It needs a source theorem that
closes one oriented irrational circle holonomy.

## Reflection-pair no-go

The full paired phase is automatically trivial:

```text
[m log p] + [-m log p] = 0                                (4)
```

for every integer `m`.  Hence functional-equation pair closure or the identity of the ordinary
completed ratio cannot imply `m=0`.  The positive successor must retain a half-polarized/right-half
relative phase and control its complementary contribution independently.

## Formal surface

- `primeOrderCircleCharge_eq_zero_iff`
- `primeOrderCircleCharge_reflectionPair_zero`
- `xiPrimeOrderCircleCharge_eq_zero_iff`
- `riemannHypothesis_iff_primeOrderCircleCharges_close`
- `completedSEMPrimeCircleCharge_eq_xiPrimeOrderCircleCharge`
- `riemannHypothesis_iff_all_completedSEMPrimeCircleCharges_close`

## Verification

`lake env lean GaloisForLFunctions/RHTower/IrrationalCircleOrderCharge.lean` passes on the repository
toolchain.

## Novelty and significance gate

This is a new project-level assembly of standard character faithfulness with existing Xi-order and
SEM interfaces.  It is not claimed as new scientific knowledge and does not prove the source
closure.  Its significance is gap compression: infinitely many dyadic closure obligations reduce
to one irrational circle phase.

## Gates

- [x] 0 -> 1: circle alternative to bounded-exponent charges stated
- [x] 1 -> 2: one-prime order faithfulness and RH equivalence proved
- [x] 2 -> 3: SEM composition formalized and checked
- [ ] 3 -> 4: not promoted; oriented source closure remains open
