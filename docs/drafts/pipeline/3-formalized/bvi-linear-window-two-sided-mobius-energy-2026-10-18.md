# Two-sided Möbius energy and defect estimates on cofinal linear windows

- **ID:** BVI-LINEAR-WINDOW-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For every fixed integer A>=2, eventually uniformly for
  2N<=M<=AN, the literal Möbius gradient energy and negative renormalized
  defect both have linear order in N, independently of MC/PM budgets.

## Definitions and exact bounds

Let s_N(k)=sum_{d<=N,d|k}mu(d),
E_N(M)=sum_{k=1}^M(s_N(k+1)-s_N(k))^2, and
R_N(M)=sieveRenormalizedPrefixDefect N M moebiusReal.

For every N,B>=1 and M+1<=(B+1)N:

    E_N(M) <= 4 B^2 M,
    |R_N(M)| <= 2 B^2 M.

For every fixed A>=2, eventually uniformly for 2N<=M<=AN:

    (2/pi^2)N <= E_N(M) <= 4 A^3 N,
    -2 A^3 N <= R_N(M) <= -N/(2pi^2).

## Dependency-closed paper proof

If 2<=k<=(B+1)N, full Möbius inversion and the existing complementary
quotient identity express s_N(k) as minus the sum of mu(k/q) over
quotients q<=B satisfying q|k and N<k/q. Thus |s_N(k)|<=B.
At k=1, s_N(1)=1<=B. Both endpoints of each gradient lie in the same
window; each gradient has modulus at most 2B. Summing squares gives
E_N(M)<=4B^2M. The exact source identity

    R_N(M)=sum_{k=1}^M s_N(k)(s_N(k+1)-s_N(k))

then gives |R_N(M)|<=2B^2M.

Apply this with B=A and M<=AN. Eventually N>=A, so AN<=N^2.
The independently verified odd-squarefree edge lower bound and polynomial
cofinal defect estimate apply. Replace M by its upper bound AN in the
finite upper estimates. **[PROVED HERE]** with every dependency closed.

## Source comparison and scope

- Reuses the exact complementary quotient compression theorem from
  `TransHorizonIncidenceMechanics/ComplementaryQuotientAndSecondOctaveLaw.lean`.
- Reuses this task's verified odd-squarefree edge coercivity from
  `CofinalMobiusGradientCoercivityAndRenormalizedDefect.lean`.
- Fixed-band unit envelopes already existed through five horizons. This
  result supplies every fixed linear window and combines upper and lower
  estimates into a cofinal order statement. Constants are not sharp.
- The upper constants depend on A. No uniform upper estimate as M/N tends
  to infinity, critical unsigned-energy bound, or interior martingale
  cancellation theorem is asserted.
- No numerical experiments, assumed analytic budgets, or full-period
  averages. No external publication-novelty claim.

## Lean and audit

Canonical source:
`formal/GaloisForLFunctions/BezoutValuationIncidence/CofinalLinearWindowMobiusEnergyAndDefectBounds.lean`.
SHA-256: `33eb856daa1539210f1a3579c9fd290338fc05755f1d73150ab99a78009a93a0`.

- Scratch session 75004: exit 0, no diagnostics.
- Original-source `lake --old env lean -j 1`, session 50481: exit 0,
  no diagnostics; matching `.olean` and `.ilean` generated.
- All five public declarations audited, session 3889: exit 0, only
  `propext`, `Classical.choice`, `Quot.sound`.
- Leaf wired into BVI umbrella; index regeneration passed.
- Global lint exited 1 for concurrent unrelated unreachable leaves and
  root TransHorizon umbrella placement; no error names this task's two
  cofinal leaves. Complete diagnostics and source manifest are archived as
  `logs/bvi-linear-cofinal-2026-10-18-{lint.txt,manifest.json}` alongside
  canonical, axiom and index logs. Other work was preserved.
- Completed C1-C5 scratch proofs and API probes were removed after audit.

## Continuing research

The parent task remains active. C6 targets uniform sublinear signed
prefix discrepancy for all M>=N using actual corpus Möbius cancellation,
with no assumed receiver budget. See the active cofinal-estimate card.
