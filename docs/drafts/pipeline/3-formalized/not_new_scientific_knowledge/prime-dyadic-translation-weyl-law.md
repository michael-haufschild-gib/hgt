# Prime dyadic translation--Weyl law

- **ID:** `prime-dyadic-translation-weyl-law`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeDyadicWeyl.lean`
- **Route:** `../../1-in-progress/dyadic-weld-weyl-multiplicity-route.md`

## Theorem

On functions of the spectral variable define

```text
T_t f(s) = f(s+t),
M_p f(s) = exp(-(log p)s) f(s).
```

Then, for every complex displacement `t`,

```text
T_t M_p = exp(-(log p)t) M_p T_t.                       (1)
```

For `p>1` and

```text
t_(p,k) = -2 pi i / (2^k log p),
```

the multiplier in `(1)` is exactly the coherent primitive phase

```text
exp(-(log p)t_(p,k)) = Bottcher.dyadicRoot k.            (2)
```

Consequently the actual prime--archimedean weld supplies a source-built global level-`k` Weyl
relation for every `k`.  The phase does not need to be imported from an unrelated carrier or
manufactured by arbitrary rescaling.

## Pinned-centre obstruction

Every `t_(p,k)` is nonzero.  Hence

```text
s + t_(p,k) != s
```

for every spectral point `s`.  The translation generator moves a local divisor germ to another
centre; it does not act internally on a pinned SEM hole algebra.  Thus `(1)` closes the global
source relation but not its descent to the finite object consumed by the Weyl multiplicity gate.

## Positive statement from the obstruction

The RH route no longer asks for a primitive phase.  It asks for one precise nonlocal theorem:

> construct a cutoff/incidence or crossed-product descent of the global prime-translation Weyl pair
> to the undoubled finite SEM hole algebra, preserving invertibility and the projective relation,
> without requiring a translated orbit of Xi zeros.

Literal translation descent is impossible at a pinned centre.  The surviving mechanism must carry a
cross-boundary defect, a global orbit quotient, or boundary inflow; it cannot be a local germ action.

## Formal surface

- `spectralTranslate`
- `primeEulerExpMultiply`
- `primeDyadicClockStep`
- `spectralTranslate_primeEulerExpMultiply`
- `primeDyadicClockPhase_eq_dyadicRoot`
- `primeDyadicWeylRelation`
- `primeDyadicClockStep_ne_zero`
- `primeDyadicClockStep_no_fixedPoint`

## Verification

`lake env lean GaloisForLFunctions/RHTower/PrimeDyadicWeyl.lean` passes on the repository toolchain.

## Novelty and significance gate

The exponentiated affine/Weyl commutation law is standard and not new scientific knowledge.  Its
value is architectural: it closes the source-phase gap in the RH detour and identifies the remaining
descent obstruction exactly.

## Gates

- [x] 0 -> 1: source operators and dyadic clock step stated
- [x] 1 -> 2: exact Weyl multiplier and nonzero-step obstruction proved
- [x] 2 -> 3: formalized and exact module check passes
- [ ] 3 -> 4: not promoted; internal SEM descent remains open

