# Sublinear literal Möbius gradient energy: obstruction and positive survivor

- **ID:** BVI-SUBLINEAR-GRADIENT-2026-10-18
- **Stage:** 5-failed
- **Type:** NO-GO with formalized positive survivor
- **Rejected statement:** The unsigned gradient energy of the literal
  truncated Möbius source is o(N) on horizons M>=2N.

## Exact obstruction

Let E_N(M)=sum_{k=1}^M(s_N(k+1)-s_N(k))^2, where
s_N(k)=sum_{d<=N,d|k}mu(d). For every odd squarefree k in (N,2N],
the first-octave source has magnitude one. An adjacent multiple of four
has source zero. Choosing the left edge for k=1 mod 4 and the right edge
for k=3 mod 4 gives distinct edges, each contributing exactly one.

Thus E_N(M) dominates the odd-squarefree count whenever M>=2N.
That count divided by N tends to 4/pi^2. In particular, eventually

    E_N(M) >= (2/pi^2)N, simultaneously for all M>=2N.

Since 2/pi^2>0, E_N(2N)/N cannot tend to zero. The proposed sublinear
raw-gradient target fails before any Möbius sign-correlation estimate.
This does not rule out renormalized energies or different source weights.

## Positive survivor: sharp order on fixed linear windows

Complementary quotient compression gives |s_N(k)|<=B for
k<=(B+1)N, N,B>=1. Hence E_N(M)<=4B^2M and |R_N(M)|<=2B^2M
when M+1<=(B+1)N. Combining both mechanisms gives, for every fixed A>=2,
eventually uniformly for 2N<=M<=AN,

    (2/pi^2)N <= E_N(M) <= 4A^3N,
    -2A^3N <= R_N(M) <= -N/(2pi^2).

**New insight:** squarefree support already forces linear microscopic
oscillation energy, independently of sign cancellation in the cumulative
first moment. Renormalized defect is correspondingly negative of linear
order on fixed linear windows. The constants are not asserted optimal.

## Paper and Lean status

- Negative statement: dependency-closed paper consequence of the positive
  floor; no separate negative-only Lean wrapper is claimed.
- Exact positive floor, finite odd-squarefree budget, and polynomial-window
  negative defect: formalized in
  `CofinalMobiusGradientCoercivityAndRenormalizedDefect.lean`.
- Exact two-sided positive survivor: formalized in
  `CofinalLinearWindowMobiusEnergyAndDefectBounds.lean`.
- Both original-source audits and all 18 public axiom checks passed.
  Only standard Lean axioms; no MC/PM premises or computations.
- Stage-3 proof cards and audit logs document source hashes and limits.

The active research task continues toward uniform signed first-moment
cancellation and stronger estimates for genuinely renormalized quantities.
