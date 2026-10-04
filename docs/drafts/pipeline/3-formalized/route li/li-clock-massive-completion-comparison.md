# Complete Gamma-dyadic moment contraction and massive cancellation

- **ID:** LI-CLOCK-MASSIVE-COMPLETION-COMPARISON
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [completed-clock sign attempt](../1-in-progress/li-clock-completed-forcing-direct-sign.md)
- **Statement:** Full completion moments have strict sharp ratio ceiling 4/25, a quantitative complete-clock curvature gap, and a positive massive envelope whose actual arithmetic partner approaches it with exponentially small two-sided relative error.

## Gates

- [x] Literal source, prior research and complete dependency-closed paper proof.
- [x] Root144 and independent210 full audits; stronger positive ratio boundary separately root-audited.
- [ ] Formalize the exact positive survivor, preserving all Gamma/dyadic terms and genuine derivatives.
- [ ] Direct/named builds, all-public axioms, independent complete source review and integration.

## No-go closure

- **Exact killing mechanism:** For actual E and V below, E/V tends to one and V grows at the completion scale, so the stronger proposed E<=0 is false eventually.
- **Strongest positive survivor:** Improved actual omega bound; all-order strict moment-ratio contraction with explicit gap and sharp limiting ceiling; full differentiated completion envelope; exact massive source decomposition and controlled cancellation.
- **New insight:** The wanted E<=V compares two large correlated source terms. Their exponentially small difference must be oriented directly.
- **Status:** PAPER PASS; Lean OPEN. No retired route or completed-clock/RH claim.

## Audited paper proof [PROVED HERE]

Frozen root144 certificate follows verbatim; its pending-audit wording is historical. Independent210 audit passed and was read completely by root: `/tmp/li_current_massive_completion_comparison_audit.md`, SHA256 `3d6fa6bfd2ebea4ba957ab804f49d468a23291b93f11f45ed286552f2af8a235`. Root certificate SHA256 `66f640e0e4a4eab1731e4aa8380002aa13bd4cd67cff42496a26e75da0cf5324`.

# Massive Dirichlet attempt: literal completion and arithmetic comparison

Status: root PAPER derivation, independent audit pending. Original signed
source S=F''-omega^2 F remains OPEN. No numerical experiment or Lean claim.

Use the literal infinite full-copy clock F, completion C, and arithmetic
partition clock P, with the admitted exact identity

    F=P-2sinh(2t)+C.

Every normalizer and all Gamma/dyadic atoms are those in the frozen source
reports. Put alpha=4/25, beta=1/64, c_j=Re CompletionMoment(j),
x_n=(2n+5/2)^(-2). Installed complete moments give

    c_j=sum_n x_n^(j+1)+d_j,
    |d_j|<=3 beta^(j+1), 0<x_n<=alpha.

Here d_j is the REAL full dyadic moment, not an absolute or deleted lattice.
The installed completion clock has the full odd factorial expansion
C(t)=sum_j c_j t^(2j+1)/(2j+1)!, with c_j>0. Uniform summable factorial
bounds license the two derivatives used below; all statements are for the
literal full completion, not a first-Gamma replacement.

## 1. Stronger actual mass coefficient

The first FIVE positive Gamma terms and the complete dyadic lower bound give

    c_0 >= 4/25+4/81+4/169+4/289+4/441-3/64.

Exact rational inequalities give respectively
4/81>49/1000, 4/169>23/1000, 4/289>13/1000, 4/441>9/1000.
Consequently c_0>1657/8000. The installed strict m_0<29/625 gives

    omega^2=c_0-m_0 >6429/40000
                         =4/25+29/40000.             (1)

Thus the actual omega is strictly greater than 2/5, not merely 1/4.
These are exact rational proof inequalities, not sampled source values.

## 2. Complete moment-ratio contraction

For every j>=0, full summability permits subtraction termwise:

    alpha c_j-c_(j+1)
      =sum_n x_n^(j+1)(alpha-x_n)+alpha d_j-d_(j+1)
      >=x_1^(j+1)(alpha-x_1)+x_2^(j+1)(alpha-x_2)
          -3 beta^(j+1)(alpha+beta).

x_1=4/81>beta and x_2=4/169>beta. Therefore this is at least

    beta^j [ (4/81)(4/25-4/81)+(4/169)(4/25-4/169)
                -(3/64)(4/25+1/64) ] >0.            (2)

For an entirely explicit check of the strict bracket, x_1>3/64,
alpha-x_1>7/64, x_2>3/128, alpha-x_2>17/128.
The two products exceed 135/16384; the subtracted term is 843/102400,
and 135/16384-843/102400=3/409600>0. Thus a uniform quantitative law is

    alpha c_j-c_(j+1) >(3/409600) beta^j.             (3)

Every discarded Gamma term is nonnegative; the dyadic lattice remains as
its justified complete two-sided error bound. No sign is assumed for d_j.
Coefficientwise summation of the genuinely differentiated entire series gives

    C''(t)<alpha C(t), t>0,
    alpha C(t)-C''(t) >=(3/51200)sinh(t/8), t>=0.     (4)

The second bound uses sum beta^j t^(2j+1)/(2j+1)!=8sinh(t/8).
The strict inequality in (4) follows already from any strictly positive
coefficient at positive t. At zero both sides vanish, as they should.

## 3. Test the concrete arithmetic upper comparison

Define the actual positive massive completion and arithmetic excess by

    V=omega^2 C-C'',
    E=P''-omega^2 P-2(4-omega^2)sinh(2t).

Differentiating the EXACT complete identity, with all endpoints/terms kept,
gives S=F''-omega^2 F=E-V. The independent inequality needed for S<=0 is
therefore E<=V. A tempting stronger estimate is E<=0, since V>0.

Equations(1),(4) and the installed full completion lower bound imply

    V(t) >=(29/40000)(181/640)sinh(2t/5), t>=0.       (5)

On the other hand the complete-copy sine derivative bound gives

    |S(t)| <= A(omega^2+1/150)t exp(t/300), t>=0.     (6)

For F'' this uses |w_q^3 sin(tw_q)|<=|w_q|^4 t exp(t/300)
and |w_q|^2<1/150; both full sums are admitted by squared mass A.
Since 2/5>1/300, (5),(6) prove

    E(t)=S(t)+V(t)>0 for every sufficiently large t. (7)

Thus the stronger arithmetic upper comparison E<=0 is FALSE for the actual
infinite source. Its failure is unconditional, not a generic countermodel.
The exact surviving needed inequality remains E<=V, where BOTH terms have
the completion scale and their difference has only the actual-clock scale.
Separate source envelopes cannot supply the sign of that difference.

More precisely (5),(6) give the exact relative cancellation survivor

    E(t)/V(t)->1,
    |E(t)/V(t)-1| <=
      A(omega^2+1/150)t exp(t/300)
         /[(29/40000)(181/640)sinh(2t/5)]             (8)

for t>0. This two-sided exponentially small relative error does not prove
which side of V the actual arithmetic E occupies. No relative estimate is
presented as the required one-sided orientation.

## 4. Source and scope ledger

Root read exact definitions and complete summability/dyadic bounds in
LiClockPairedEtaCompletionMoments:217-295; full source series, Gamma/dyadic
realness and coefficient positivity in LiClockPairedEtaPositiveCompletion:
227-321; installed completion lower bound at429-432. m_0 upper bound was
previously fully checked in XiOrderFourteenCornerSourceExclusion:179-215.
The full F derivative admission is in the root derivative report and is
independently audited by Current. The exact F/P/C split was fully checked
in the frozen literal-cycle report and Current completed-forcing report.

Prior direct corpus search is /tmp/li_root_massive_dirichlet_clock_research.json,
owned session81282, terminal0, partial=true, elapsed206.922544417s. Query:
"actual clock massive derivative Dirichlet Green cumulative forcing sine positive kernel"
--any --module Li --mode deep --budget-seconds 240 --no-refresh --json.
Inventory63533/63533, retrieval1164562, coverage1164617/current1164618;
semantic unmeasured; text/source interrupted and Qdrant deadline. Compiler
43compiled snapshots,2errors,47912pending,2660stale,38stale snapshots,
1umbrella source-only,2654unavailable. All20 candidate statements,20 source
argument statements,20 declaration names,10 prose paths,10 source passage
paths and the sole proposed ingredient set inspected; no proof ideas. The
actual sine-source/contour/contiguous-kernel hits are existing admission or
receiver inputs. The remaining BM, Deninger, Liouville-Green, Fourier,
Bottcher and unrelated scalar kernels do not supply this S orientation.
The ingredient set proposes unrelated BM sine differentiation and existing
reference-kernel multiplication; neither proves the actual signed source.
Long unrelated excerpts are not claimed fully read. The moment-ratio check
was additionally searched directly with rg restricted to Lean source files;
no absence/novelty or compiler claim is made. This report is not a retired
route: S<=0 and the original finite-window F_N>=0 remain OPEN. All new
positive survivors (1)-(8) remain Lean-open pending full independent audit.

## Strongest positive refinements [PROVED HERE]

The independent audit exposed the sharp boundary, and root rechecked the full argument. The Gamma n=0 term is alpha^(j+1). The complete remaining Gamma tail is bounded by (4/81)^j sum_(n>=1)x_n, and the complete dyadic error by 3 beta^(j+1). Since both 4/81 and beta are smaller than alpha, c_j/alpha^(j+1) tends to one. Therefore c_(j+1)/c_j tends to alpha, although every finite ratio is strictly smaller. No smaller uniform ceiling holds eventually.

The strict recurrence also gives c_j<c0 alpha^j for every j>=1. Summing the genuine positive factorial series yields C(t)<(5/2)c0 sinh(2t/5) for t>0; the linear term agrees and higher terms make the inequality strict. Finally the exact decomposition V=(omega^2-alpha)C+(alpha C-C'') retains the stronger lower bound

`V(t)>=(omega^2-alpha)C(t)+(3/51200)sinh(t/8)`,

and hence the explicit lower bound from (5) PLUS `(3/51200)sinh(t/8)`, with strictness for t>0. These refinements do not orient S=E-V and introduce no new source hypothesis.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.LiClockMassiveCompletionComparison`, `GaloisForLFunctions.HTGeometry.OddEvenFactorialSeriesCalculus`, `GaloisForLFunctions.RHTower.LiClockPairedEtaCompletionMoments`, `GaloisForLFunctions.RHTower.LiClockPairedEtaPositiveCompletion`, `GaloisForLFunctions.RHTower.LiClockPairedEtaArithmeticCancellation`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockDerivative`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the umbrellas):
`GaloisForLFunctions.RHTower.LiClockMassiveCompletionComparison` (new), `GaloisForLFunctions.HTGeometry.OddEvenFactorialSeriesCalculus` (new),
`GaloisForLFunctions.RHTower.LiClockPairedEtaCompletionMoments`, `GaloisForLFunctions.RHTower.LiClockPairedEtaPositiveCompletion`, `GaloisForLFunctions.RHTower.LiClockPairedEtaArithmeticCancellation`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockDerivative`.

| Claim | Declaration |
|-|-|
| `c_j=Σ_n x_n^{j+1}+d_j`, `|d_j|≤3β^{j+1}`, `0≤x_n≤α` | `liClockCompletionCoeff_eq`, `abs_liClockCompletionDyadicMoment_le`, `liClockCompletionGammaSquare_le` |
| (1) `c_0>1657/8000`, `ω²>6429/40000` | `liClockCompletionCoeff_zero_gt`, `liEvenCrossActualClockGreenRate_sq_gt` |
| (2)–(3) `αc_j−c_{j+1}>(3/409600)β^j` | `liClockCompletionCoeff_contraction` |
| (4) `C''<αC`, `αC−C''≥(3/51200)sinh(t/8)` (full completion clock, genuine derivatives) | `iteratedDeriv_two_liClockCompletionClock_lt`, `liClockCompletionClock_curvature_gap`, `liClockCompletionClock_eq_re`, `iteratedDeriv_two_liClockCompletionClock` |
| (5) `V≥(29/40000)(181/640)sinh(2t/5)` (+`(3/51200)sinh(t/8)`) | `liClockMassiveCompletionEnvelope_ge_sinh` |
| (6) `|S|≤A(ω²+1/150)te^{t/300}` | `abs_liEvenCrossActualClockMassiveSource_le` |
| `F=P−2sinh2t+C` with `P` the arithmetic eta clock plus pole term; `S=E−V` | `exists_liClockArithmeticPartitionClock_eq_arithmetic`, `liEvenCrossActualClockMassiveSource_eq` |
| (7) `E>0` eventually (`E≤0` false) | `eventually_liClockArithmeticExcess_pos` |
| (8) `E/V→1`, explicit two-sided relative error | `tendsto_liClockArithmeticExcess_div_envelope`, `abs_liClockArithmeticExcess_div_sub_one_le` |
| Sharp ceiling `c_j/α^{j+1}→1`, `c_{j+1}/c_j→α` | `tendsto_liClockCompletionCoeff_div_pow`, `tendsto_liClockCompletionCoeff_ratio` |
| `c_j<c_0α^j` (`j≥1`), `C<(5/2)c_0 sinh(2t/5)` | `liClockCompletionCoeff_lt_geometric`, `liClockCompletionClock_lt_sinh` |
| `V≥(ω²−α)C+(3/51200)sinh(t/8)` | `liClockMassiveCompletionEnvelope_ge` |

## Log

- 2026-10-01 — Complete root144/independent210 paper and source audits pass. Sharp coefficient-ratio boundary separately re-audited. Stage2; formalization remains mandatory. Actual signed massive source and original finite-window targets remain OPEN.
- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
