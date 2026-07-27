# Pro-nuclear Kähler trace tower

- **ID:** `deninger-pro-nuclear-kahler-trace-tower`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE WITH PAPER-PROVED LIMIT THEOREM
- **Label:** `DAC_PRO_NUCLEAR_KAHLER_TRACE_TOWER`
- **Parent:** `deninger-arithmetic-lefschetz-determinant-comparison`
- **Statement:** finite Kähler--Riemann Lefschetz models converge in
  trace norm to the infinite arithmetic cohomological trace.

## Tower

Let \(I\) be a directed set and let
\[
 (S_a,\mathcal F_a,\phi_a^t,\omega_a),\qquad a\in I,
\]
be finite Kähler--Riemann laminated stages.  Write
\(\bar H_a^q\) for their harmonic Hilbert spaces and
\(\Theta_{a,q}\) for the flow generators.  Require:

1. compatible isometric maps
   \(\bar H_a^q\to\bar H_b^q\) for \(a\le b\);
2. the Hilbert completion of the algebraic colimit is
   \(H_{\mathrm{arith}}^q\);
3. the centered maps
   \(e^{-qt/2}e^{t\Theta_{a,q}}\) are compatible unitaries;
4. stage \(a\) contains a finite set \(P_a\) of prime packets, with
   \(\bigcup_aP_a\) all primes;
5. every finite stage satisfies the oriented leafwise Lefschetz formula.

For \(\varphi\in C_c^\infty(\mathbb R)\), set
\[
 K_{a,\varphi,q}
   =\int_{\mathbb R}\varphi(t)e^{t\Theta_{a,q}}\,dt.                 \tag{1}
\]

## Abstract limit theorem

`[PROVED HERE] [DAC_PRO_NUCLEAR_KAHLER_TRACE_LIMIT]`

Assume that after transport to \(H_{\mathrm{arith}}^q\), the operators in
`(1)` converge in trace norm:
\[
 K_{a,\varphi,q}\longrightarrow K_{\varphi,q}.                      \tag{2}
\]
Then \(K_{\varphi,q}\) is trace class and
\[
 \operatorname{Tr}K_{\varphi,q}
   =
 \lim_a\operatorname{Tr}K_{a,\varphi,q}.                            \tag{3}
\]

If the stage orbit side is
\[
 \sum_{p\in P_a}\sum_{k\ge1}
   (\log p)\,c_{p,k}\,\varphi(k\log p),                              \tag{4}
\]
then `(4)` is eventually constant for each compactly supported
\(\varphi\).  Indeed, if
\(\operatorname{supp}\varphi\subset[-B,B]\), a nonzero summand has
\[
 p^k\le e^B.
\]
Only finitely many positive integers satisfy this bound, hence only
finitely many prime powers occur.  Directed exhaustion eventually
contains all of them.

Consequently the finite-stage Lefschetz identities and `(2)` imply the
infinite arithmetic distributional trace identity.  Infinite-dimensional
\(H^1\) creates no orbit-side convergence problem on compact test support;
all analytic work is concentrated in trace-norm convergence `(2)` and the
archimedean term.

## Source conjecture

`[CONJECTURE] [DAC_PRO_NUCLEAR_KAHLER_TRACE_TOWER]`

The coefficient test domain restricts on logarithmic Kummer charts to
the nuclear LF space
`DAC_ADELIC_KUMMER_NUCLEAR_TEST_SCALE`.  Nuclearity of that domain is a
proved input.  Conjectural content is nuclearity/trace-norm control of
smoothed flow operators and compatibility with the Kähler finite-stage
limit.

The realization of
`DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION` admits a tower satisfying
the five structural requirements and trace-norm convergence `(2)`, with:

- \(c_{p,k}\) equal to Deninger's oriented local Lefschetz index;
- the finite-stage archimedean kernels converging in trace norm to the
  signature-boundary kernel;
- the limit operators independent of the chosen cofinal finite-stage
  system;
- no stage, norm, or convergence weight defined using Xi zeros or RH.

## Construction program

1. Filter rational-Witt correspondences by finite sets of primes and
   finite pro-Stein character lattices.
2. Construct compatible leafwise Hodge complexes and harmonic
   projectors at each stage.
3. Prove off-diagonal heat-kernel bounds uniform in the stage.
4. Show the trace norms of the complementary new-prime/new-character
   blocks form a Cauchy net for every test function.
5. Prove the real signature kernel has the matching Cauchy property.
6. Apply `DAC_PRO_NUCLEAR_KAHLER_TRACE_LIMIT`, then compare the resulting
   source distribution with the independently formalized explicit
   formula.

## Falsifiers

- Strong-operator convergence alone is insufficient; `(2)` must be
  trace-norm convergence or a proved nuclear analogue.
- Local finiteness of prime powers does not control the archimedean
  kernel.
- Finite-stage purity does not imply limit strong continuity without a
  uniform core theorem.
- A filtration selected from the zero divisor is circular.

## Current status

- Finite-stage Kähler purity and Leichtnam-type trace formula:
  literature-proved under their stated hypotheses.
- Trace-norm limit theorem and compact-support stabilization:
  paper-proved.
- Arithmetic tower construction, uniform heat bounds, trace-norm Cauchy
  theorem, and archimedean convergence: open.

**Verdict:** `ACTIVE SOURCE CONJECTURE; LIMIT PASSAGE REDUCED TO ONE
TRACE-NORM ESTIMATE`.

## Log

- 2026-07-26 — Extracted as positive survivor of
  `DAC_SINGLE_FINITE_TRANSVERSE_LAMINATION_NO_GO`.
