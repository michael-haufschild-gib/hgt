# Polynomial-horizon Möbius gradient coercivity

- **ID:** BVI-POLYNOMIAL-GRADIENT-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Statement:** For every integer A>=2, eventually uniformly for 2N<=M<=N^A,
  the literal Möbius renormalized prefix defect satisfies R_N(M)<=-N/(2pi^2).

## Goal and scope

Produce an arithmetic estimate with moving cutoff and horizon, independent
of assumed MC/PM receiver budgets. This theorem controls the actual signed
renormalized defect. It does not prove a critical unsigned-energy bound or
an interior martingale cancellation estimate. The wider research task stays
active in `../1-in-progress/bvi-cofinal-arithmetic-defect-estimate-2026-10-18.md`.

## Definitions

For literal Möbius coefficients, write

    s_N(k) = sum_{d<=N, d|k} mu(d),
    E_N(M) = sum_{k=1}^M (s_N(k+1)-s_N(k))^2,
    R_N(M) = sieveRenormalizedPrefixDefect N M moebiusReal,
    O_N = { k : N<k<=2N, 2 does not divide k, k squarefree }.

The established exact source identity is

    2 R_N(M) + E_N(M) = s_N(M+1)^2 - s_N(1)^2.

## Theorems and proof

**1. Cutoff-independent endpoint control.** At every positive integer k,
the triangle inequality and |mu(d)|<=1 give |s_N(k)|<=tau(k). Therefore

    |2 R_N(M)+E_N(M)| <= tau(M+1)^2+1,
    max(0,R_N(M)) <= tau(M+1)^2/2.

The corpus's elementary divisor estimate implies that for every delta>0,
tau(k)^2+1<=C_delta k^delta. C_delta is independent of both N and M.

**2. Disjoint arithmetic edges.** Let N>=2 and k in O_N. Möbius inversion
gives s_N(k)=-mu(k), hence s_N(k)^2=1. Define

    e(k) = k-1 if k=1 mod 4;  e(k)=k if k=3 mod 4.

The neighboring endpoint divisible by four has response zero. When that
endpoint equals N, use the full sub-horizon Möbius divisor sum; otherwise
use first-octave reciprocity and nonsquarefreeness. Thus the gradient square
on e(k) is exactly one. Each selected edge lies in [N,2N-1]. The two branches
have residues 0 and 3 modulo four, respectively, and are individually
injective; all selected edges are distinct. Nonnegativity of the remaining
gradient squares yields

    #O_N <= E_N(M),                         M>=2N,
    2 R_N(M) + #O_N + 1 <= tau(M+1)^2,      N>=2, M>=2N.

This finite inequality is the arithmetic estimate underlying the cofinal
result; there is no period average or assumed cancellation input.

**3. Linear cofinal coercivity.** The existing prime-two-deleted squarefree
density theorem gives #O_N/N -> 4/pi^2. Consequently, eventually uniformly
for M>=2N,

    E_N(M) >= (2/pi^2)N.

Fix A>=2 and delta=1/(2A). If M<=N^A and N>=2,

    |2R_N(M)+E_N(M)| <= C_delta(M+1)^delta
                        <= C_delta*2^delta*sqrt(N).

The last expression is eventually less than N/pi^2. Subtract the energy
floor and divide by two to obtain R_N(M)<=-N/(2pi^2), uniformly throughout
the polynomial window. **[PROVED HERE]**, with no open paper dependency.

## Corpus comparison and limits

- Existing BVI/TransHorizon results supplied first-octave reciprocity,
  polarization, finite-band sign bounds, and conditional spike absorption.
- Existing generic arithmetic supplied the subpower divisor bound and
  odd-squarefree density. Neither is claimed as new.
- The additional result is the disjoint squarefree-to-zero edge injection,
  its all-longer-prefix energy floor, and the resulting uniform cofinal
  signed bound for the literal truncated Möbius source.
- Hybrid and deep corpus queries inspected candidate lemmas and source
  arguments. Several queries were partial and compiler coverage was largely
  source-only. These searches do not establish global publication novelty.
- No numerical experiments or external literature claims.
- This proof does not control the negative magnitude of R_N(M) uniformly
  by N. The accumulated energy can continue growing with M; no such stronger
  claim is made.

## Gates and audit

- [x] Paper proof dependency-closed.
- [x] Original-source `lake --old env lean -j 1` passes without warnings.
- [x] All 13 public declarations have only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Leaf wired into BVI umbrella; generated indexes refreshed.
- [x] Formal lint inspected; concurrent unrelated findings recorded below.
- [x] This result's proof jobs terminal; canonical audit evidence archived.

Canonical leaf:
`formal/GaloisForLFunctions/BezoutValuationIncidence/CofinalMobiusGradientCoercivityAndRenormalizedDefect.lean`.
Current source SHA-256: `b76bced42e329e2a1e50610d1f752be6b31c6bd82796a234fa38b45398a60765`.
Original-source audit session 86144: exit 0, empty diagnostics.
Axiom audit session 2916: exit 0; all 13 declarations checked.
Evidence: `logs/bvi-cofinal-2026-10-18-{manifest.json,canonical.txt,axioms.txt,index.txt,lint.txt}`.

Global lint exited 1 for concurrent, unrelated files: unreachable
`BiScaleUncertainty.SixthReadoutStability`,
`BezoutValuationIncidence.ArbitraryDepthBezoutShellsAndRoutePMSecondLayerProfile`,
`BezoutValuationIncidence.CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget`,
`BezoutValuationIncidence.PronicPotentialSelfCancellationAndInteriorGradientConservation`,
and root `TransHorizonIncidenceMechanics.lean` placement. No lint error names
the new leaf. Other work was preserved; the global gate is not claimed clean.

## Log

- 2026-10-18 — Prime-edge proof passed Lean; generalized before publication
  to all odd squarefree integers, replacing a logarithmic/PNT bound by a
  linear bound from elementary squarefree density.
- 2026-10-18 — Complete original leaf and every public axiom closure passed.
  Umbrella wired, index refreshed, global lint findings recorded. Research
  continues toward a matching energy upper bound on fixed linear windows.
