# Transverse clocks decompactify in every locally uniform Xi approximation

- **ID:** `transverse-clock-decompactification`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / APPROXIMATION OBSTRUCTION
- **Scientific status:** `[PROVED HERE] [BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/BoundedClockZeroTransfer.lean`
- **Statement:** Let `F_n -> XiC` locally uniformly.  If `z_n -> z`, `T_n>0`, and every `F_n`
  vanishes on the full transverse lattice `z_n+k T_n i`, then `T_n -> +infinity`.

## Theorem

Assume

```text
F_n -> XiC locally uniformly,
z_n -> z,
T_n>0,
F_n(z_n+k T_n i)=0 for every n and every k in Z.
```

Then

```text
T_n -> +infinity.
```

The conclusion is cofinal, not merely unboundedness.  If it failed, some infinite subsequence of
periods would remain bounded.  Compactness gives a further subsequence `T_n -> T>=0`.

- If `T>0`, local uniform convergence transfers the full arithmetic progression to `XiC`.
- If `T=0`, choosing `k_n=floor(t/T_n)` for each real `t` transfers a dense transverse mesh and
  makes `XiC` vanish on a full vertical line.

The second branch contradicts analyticity and nontriviality.  In the first branch, a negative
integer step maps under `s=1/2+iz` into `Re(s)>=1`, where completed zeta is nonzero.  Hence no
bounded subsequence exists and the periods tend to infinity.

In the original `s` coordinate these are horizontal zero clocks.  Ordinary finite Euler clocks
are vertical in `s`, so they have the wrong orientation and do not instantiate the theorem.

## Lean certificate

The module proves:

```text
RHTower.periodic_zero_limit_of_period_tendsto
RHTower.shrinking_periodic_zero_limit_vertical
RHTower.bounded_periodic_zero_limit
RHTower.xiC_no_vertical_zero_progression
RHTower.xiC_transverse_clock_escape
RHTower.xiC_transverse_clock_tendsto_atTop
```

All declarations compile with the project toolchain and depend only on the standard logical
axioms reported by mathlib (`propext`, `Classical.choice`, and `Quot.sound`).

## RH-route consequence

The theorem retires bounded transverse clocks as a natural approximant mechanism.  Any surviving
source construction must explain the decompactification rate or replace exact periodicity by a
different source-side coercive defect.  The result itself does not locate a zero and does not prove
RH.

## Gates

- [x] positive-period subsequential limit transferred
- [x] shrinking-period dense-mesh branch proved
- [x] XiC transverse arithmetic progressions excluded
- [x] unboundedness strengthened to cofinal divergence
- [x] Lean build and axiom audit
- [x] bounded-clock RH mechanism separated and retired
