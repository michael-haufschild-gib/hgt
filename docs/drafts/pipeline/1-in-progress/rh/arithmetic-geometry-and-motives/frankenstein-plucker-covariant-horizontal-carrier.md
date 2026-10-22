# Frankenstein Pluecker covariant horizontal carrier

- **ID:** `FR-PCHC-1`
- **Stage:** `1-in-progress`
- **Type:** transported source-horizontal carrier
- **Status:** `[BRIDGE] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/FrankensteinPluckerCovariantHorizontalCarrier.lean`

## Heavy-conjecture loop

1. **Original fixed-label current telescopes after local transport theorem. — FAIL.**  Existing
   current uses ordinary scalar fibre and does not apply transport to right endpoint.  Rewriting it
   as covariant current would change theorem.
2. **Normalize every reporter and sum universal scalars. — REJECTED.**  This erases physical metric
   density and is not coefficient-faithful.
3. **Transport right endpoint to next left chart before incidence, retaining vertex reporter and
   variable metric. — SURVIVES.**  Local transport theorem makes shared endpoint literally same
   source vector; weighted inverse incidence then telescopes without freezing reporters.

## Frozen finite construction

Fix base pair labels `(s,t)`.  Along adjacent-prime index let

```text
s_n = sigma6^n(s),   t_n = sigma6^n(t).
```

Lower and upper vertex reporters are

```text
V_n^0 = rhoLeft_(e,n,s_n,t_n,0),
V_n^1 = rhoLeft_(e,n,s_n,t_n,1).
```

Transport proves right reporter of edge `n`, after multiplication by its canonical positive
coefficient, equals `V_(n+1)^d`.  Define transported edge incidence

```text
E_n^d(a) = (n+1)(V_n^d a_(n,e+d) - V_(n+1)^d a_(n+1,e+d)).
```

For any finite `N`, weighted telescope gives

```text
sum_(n<N) E_n^d(a)
  = sum_(n<N) V_n^d a_(n,e+d) - N V_N^d a_(N,e+d).
```

Unlike P-G86 scalar layer sum, diagonal carrier retains every prime label in its transported
physical reporter.  Both reflection orientations and divisor depths survive.

## Paper proof

Iterated pair labels obey `(s_(n+1),t_(n+1))=(sigma6(s_n),sigma6(t_n))`.  Apply lower or upper
shared-prime transport theorem at edge `n` to identify transported right coefficient with next
vertex reporter.  Set `b_n=V_n^d a_(n,e+d)`.  Elementary induction proves

```text
sum_(n<N) (n+1)(b_n-b_(n+1)) = sum_(n<N)b_n - N b_N.
```

No reporter is treated as constant; cancellation occurs only because two occurrences represent
same shared source coordinate after canonical transport.

## Honest boundary

Finite and infinite carrier theorems are unconditional.  Independent arithmetic law must still
identify covariant diagonal carrier with completed Xi horizontal target and force reflected
annihilation.  This card does not claim RH.

## Infinite completion `[PROVED HERE]`

Every literal coordinate reporter is uniformly bounded by

```text
2 sqrt(D_cofinal) / log 2.
```

Proof uses P-G91 normalization, the pair-dispersion feature bound, P-G84 denominator mass, and
P-G92 reciprocal-node bound.  P-G86 Köthe index-weight summability then proves:

```text
sum_n ||V_n^d a_n|| < infinity,
sum_n (n+1)||V_n^d a_n|| < infinity,
N V_N^d a_N -> 0,
sum_n ||E_n^d(a)|| < infinity.
```

Passing finite telescope to limit gives exact unconditional identities

```text
T^0_(e,s,t)(a) = sum'_n V_n^0 a_(p_n,e),
T^1_(e,s,t)(a) = sum'_n V_n^1 a_(p_n,e+1).
```

This is source-zero-to-horizontal-carrier construction requested by frontier map: physical
weights are applied before incidence, shared prime is glued by source-derived transport, and only
then is cofinal sum taken.  Prime labels, divisor depth, P-G84 mass, P-G91 probabilities, P-G92
nodes, and both orientations remain visible.

## Hostile endpoint audit

Carrier input is still arbitrary `DeningerHeightKothe`.  Corpus has no unconditional map sending
each actual `XiZeroCopy` horizontal class into this Köthe source with coefficient identity.  Existing
`SourceZeroHorizontalCarrier` supplies multiplicity-exact Xi prime coefficients and proves their
reflection oddness, but its global annihilation is explicitly RH-equivalent.  Therefore declaring
our new carrier zero, or identifying reflected copies, would still assume missing producer.

Crossing with Gamma-six route sharpens gate: our physical frame connection is metric-isometric and
flat (two-step holonomy has only endpoint ratio), whereas Gamma-six reflection--Wold carrier has
curvature `(1/6)^(2 delta)`, trivial only at `delta=0`.  A coefficient-faithful theorem proving both
are same source connection would force RH, but no corpus theorem currently supplies that
identification.  Arbitrarily identifying one-dimensional fibres is rejected as theatre.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/FrankensteinPluckerCovariantHorizontalCarrier.lean
lake build GaloisForLFunctions.RHTower.FrankensteinPluckerCovariantHorizontalCarrier
```

Both pass; exact leaf build completed at `[12751/12751]`.  Umbrella was wired but not built.
Eight capstones use only `propext`, `Classical.choice`, and `Quot.sound`; targeted forbidden-
declaration scan is clean.  Repository-wide lint remains red only because concurrent unrelated
untracked Sieve/Suzuki/HTGeometry modules are not umbrella-reachable.
