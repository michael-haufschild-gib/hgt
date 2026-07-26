# Exact-weight invariant descent of the analytic Milnor coefficient

- **ID:** `deninger-analytic-exact-weight-descent`
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Parent:** `deninger-rost-schmid-flow-realization`

## Retired claim

For the analytic Tate--Milnor complex \(C^\bullet_{\mathrm{an}}\), construct
a chain deformation retract onto rational-power invariants
\[
 C^\bullet_{\mathrm{an}}{}^{\mathbb Q_{>0}}
\hookrightarrow C^\bullet_{\mathrm{an}}
\]
so that
\[
 H^\bullet(C_{\mathrm{an}}^{\mathbb Q_{>0}})
\cong H^\bullet(C_{\mathrm{an}})^{\mathbb Q_{>0}}.                    \tag{1}
\]
Use this exact invariant complex as the coefficient on Deninger's coarse
suspension.

## Exact killing mechanism

`DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE` gives local cohomology
\[
 H^\bullet(C_{\mathrm{an}})
\cong\mathbb R\oplus V_F[-1].
\]
Power maps act on the degree-one Milnor symbols by
\[
 F_q=q.
\]
After Deninger's Tate normalization this action is trivial.  Therefore an
exact comparison `(1)` leaves only a pure scalar rational-power action on
the descended degree-one cohomology.

`DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO` then applies: a strongly
continuous flow agreeing with the scalar power action on the dense
subgroup \(\log\mathbb Q_{>0}\subset\mathbb R\) is scalar on all of
\(\mathbb R\).  Its generator has at most one point eigenvalue.  It cannot
be the infinite nonreal zero spectrum of completed zeta.

The finite-transfer projector attack fails for the same reason.  At fixed
transverse coordinate,
\[
 e_N=N^{-1}V_NF_N
\]
averages over the roots-of-unity deck group of a power isogeny.  The
intersection of its images on cylinder-holomorphic de Rham forms consists
of translation-invariant logarithmic forms.  Hence its limit is precisely
the pure exterior model that triggers the scalar-spectrum no-go.

## Strongest positive survivor

`[CONJECTURE] [DAC_DIAGONAL_ARITHMETIC_LOCALIZATION_DESCENT]`

Non-proper suspension descent and finite-place Rost--Schmid localization
must be one horizontal construction, not two successive exact functors.
On logarithmic transverse coordinate \(s=\log u\), the diagonal
rational-power action combines
\[
 F_q\quad\text{on the analytic leaf}
\qquad\text{with}\qquad
 s\longmapsto s-\log q.
\]
After analytic completion, its dense subgroup must be represented by a
closed diagonal generator
\[
 D_{\mathrm{diag}}=A_{\mathrm{leaf}}-\partial_s.                    \tag{2}
\]
The generic-to-prime boundary is the localization map for `(2)` with
twisted MW residues.  Its two-column totalization simultaneously records:

1. failure of exact coarse descent;
2. prime-packet residues;
3. the residual transverse flow commuting with the localization
   differential.

This leaves only one horizontal cohomological direction and is compatible
with total amplitude \([0,2]\).  Averaging the analytic factor away before
prime localization is forbidden.

## New insight

Deninger's group
\[
 H^1(\widetilde X,Q_0(1))^{\widetilde G}
\]
is a regulator target for algebraic units, not a declaration that the
entire spectral arithmetic \(H^1\) is exact invariant local cohomology.
The zeta-carrying part must live in the non-proper
descent/localization defect.

## Status

- Killing implication: paper-proved from
  `DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO`.
- Fixed-transverse transfer collapse: paper-proved by density of torsion
  translations on the finite complex tori.
- Positive survivor: active source conjecture in
  `deninger-diagonal-arithmetic-localization-descent`.
- Lean: scalar-spectrum theorem pending; analytic transfer-collapse
  formalization pending.

**Verdict:** `FAILED; DIAGONAL DESCENT/PRIME LOCALIZATION SURVIVES`.

## Log

- 2026-07-26 — Exact-invariants route retired after spectral hostile
  audit.
