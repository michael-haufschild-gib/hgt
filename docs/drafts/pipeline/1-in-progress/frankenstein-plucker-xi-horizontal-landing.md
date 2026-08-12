# Frankenstein Pluecker Xi horizontal landing

- **ID:** `FR-PXHL-1`
- **Stage:** `1-in-progress`
- **Type:** coefficient-faithful actual-Xi source landing
- **Status:** `[BRIDGE] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/FrankensteinPluckerXiHorizontalLanding.lean`

## Heavy-conjecture loop

1. **Insert the Xi horizontal coefficient into arbitrary selected-pair charts. — FAIL.**
   Universal incidence can vanish, so an arbitrary chart can erase an off-line class.
2. **Choose a positive chart after inspecting each zero. — REJECTED.**  This is not
   source-derived and does not preserve one uniform carrier.
3. **Use the involution-fixed charts `(1,4,0)` and `(4,1,1)`. — PROVED.**  Their universal
   incidence is literally `1`, their selected-pair labels are fixed under every adjacent-prime
   transport, and each physical reporter is exactly its strictly positive P-G84/P-G91/P-G92 scale.
4. **Obtain annihilation from Stokes-conditioned information coenergy. — FAIL.**  Existing
   coenergy is strictly positive throughout the physical strip.  Multiplying by the landed
   reflection-odd coefficient gives another faithful receiver, not a source zero.
5. **Glue valuation depth and adjacent-prime transport into a curvature contradiction. — FAIL.**
   Canonical reporter transports are endpoint scale ratios, hence exact-gradient and flat for every
   Xi grade.  Identifying them with nonflat Gamma-six reflection--Wold transport is precisely the
   missing coefficient-faithful source theorem.

## Exact construction

For every multiplicity-labelled `XiZeroCopy q`, valuation depth `e`, and nth-prime label `n`,
define

```text
L(q,e,n) = reporterScale((e,n),1,4,0) * sourceZeroHorizontalPrimeCarrier(q,p_n),
U(q,e,n) = reporterScale((e,n),4,1,1) * sourceZeroHorizontalPrimeCarrier(q,p_n).
```

Both scale factors are strictly positive.  Therefore Lean proves

```text
L(q,e,n)=0  iff Re(q)=1/2,
U(q,e,n)=0  iff Re(q)=1/2,
(L,U)(reflection q,e,n)=-(L,U)(q,e,n),
((e,n) |-> (L,U))=0 iff Re(q)=1/2.
```

No prime label, divisor multiplicity, depth label, or reflection orientation is quotiented out.

Define coefficient-faithful edge currents

```text
E_n^L=(n+1)(L_n-L_(n+1)),
E_n^U=(n+1)(U_n-U_(n+1)).
```

For every finite cutoff `N`,

```text
sum_(n<N) E_n^d = sum_(n<N) V_n^d - N V_N^d.
```

Both edge currents remain reflection-odd.

## Honest boundary

This closes actual Xi landing into both retained positive Pluecker orientations.  It does not prove
summability of these actual-Xi sequences, vanishing of their terminal flux, equality of same-source
reflected fibres, or an annihilating global source trace.  Pointwise/global zero remains exactly the
critical-line condition.

P-G95 proves the P-G94 physical-overlap operator globally injective: its only algebraically glued
local gauge is the linearly growing, non-square-summable Stokes-gap section. No current theorem
proves this Xi carrier square summable or places it in the overlap operator kernel. Claiming either
property without a source proof would be theatre; injectivity alone cannot supply annihilation.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/FrankensteinPluckerXiHorizontalLanding.lean
lake build GaloisForLFunctions.RHTower.FrankensteinPluckerXiHorizontalLanding
```

Both pass; exact leaf build completed at `[12752/12752]`.  Capstones use only `propext`,
`Classical.choice`, and `Quot.sound`; targeted forbidden-declaration scan is clean.  Umbrella was
wired but not built.
