# Gaussian radial all-late hardness transfer law

- **ID:** gaussian-radial-all-late-hardness-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** static-local-complexity-law.md · O4 fixed-time transfer
- **Statement:** A radial static-Hamiltonian ensemble inherits every asymptotic fixed-shell
  capture upper bound at every sufficiently late laboratory time, not merely along an unbounded
  subsequence.

## Goal

Close the shell-to-ordinary-Gaussian transfer loss in the static-local complexity programme.  The
existing fixed-shell theorem controls the capture probability at all late shell times, while the
existing quenched-to-fixed-time theorem extracts only an unbounded sequence of common times.  The
positive Gaussian radius is itself a random clock and removes that subsequence loss.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted source check/build, axiom audit
- [ ] 3 → 4  publication-ready: integrated only after Brown first-onset closure

## Theorem

Let \((S,\sigma)\) be a probability space, let \(R\) be a strictly positive random variable with
law \(\nu\), and let \(E_t\subseteq S\) be a measurable family.  Put

\[
 a(t)=\sigma(E_t),\qquad
 p(T)=\int a(rT)\,d\nu(r).
\]

If \(0\le a\le1\) and

\[
 \limsup_{t\to\infty}a(t)\le b,
\]

then

\[
 \limsup_{T\to\infty}p(T)\le b.
\]

Consequently, for every \(\eta>0\), every sufficiently late laboratory time satisfies
\(p(T)<b+\eta\).

For a homogeneous static Hamiltonian family \(H_x=\sum_jx_jP_j\), standard Gaussian polar
disintegration writes \(x=R\theta\) with independent uniform direction \(\theta\) and positive chi
radius \(R\).  Since

\[
 e^{-iT H_{R\theta}}=e^{-i(RT)H_\theta},
\]

the theorem applies verbatim to every scale-invariant circuit-capture event.

## Proof

`[PROVED HERE]` Fix an arbitrary sequence \(T_k\to\infty\).  For every \(r>0\), also
\(rT_k\to\infty\), hence

\[
 \limsup_{k\to\infty}a(rT_k)\le b.
\]

The functions \(r\mapsto a(rT_k)\) are nonnegative and bounded by the integrable constant one.
Reverse Fatou, obtained by applying Fatou to \(1-a(rT_k)\), gives

\[
 \limsup_k\int a(rT_k)\,d\nu(r)
 \le \int\limsup_k a(rT_k)\,d\nu(r)
 \le b.
\]

If the asserted filter upper limit failed, some sequence \(T_k\to\infty\) would have
\(p(T_k)>b+\eta\) for a fixed \(\eta>0\), contradicting the displayed bound.  The Hamiltonian
specialization is the exact scaling identity above together with Gaussian polar disintegration.

## Critical-antagonist audit

- The theorem upgrades `there exist arbitrarily late common hard times` to `every sufficiently
  late common time has the same ensemble hardness floor`.
- It retains one ordinary time-independent Gaussian draw and needs no spectral-gap,
  pseudodeterminant, Haar-mixing, circuit-word multiplicity, or independence between late times.
- It does **not** bound when the all-late regime starts.  An asymptotic shell theorem may have an
  arbitrarily delayed transient.  Therefore this is not Brown--Susskind growth onset and cannot be
  advertised as the full growth--plateau--recurrence law.
- It does not by itself select one draw hard at every late time; it supplies the marginal bound
  needed for finite Brown grids.  Same-draw grid selection still pays the grid union.

## Novelty audit

The searched static-Hamiltonian literature proves stochastic growth/saturation/recurrence or
permanent non-Haar distinguishability, but not this all-late radial transfer for an ordinary
constant-local Gaussian ensemble.  In particular, arXiv:2205.09734 treats random circuits and
stochastic local Hamiltonians, while arXiv:2510.08434 proves that constant-local autonomous
dynamics never becomes Haar-random.  The transfer is compatible with that obstruction: it uses
the autonomous spectral shell, not Haar mixing.  Novelty claimed here is the radial-clock
application and removal of the common-time subsequence loss, not reverse Fatou itself.

## Frontier consequence

This retires common-time extraction as an open issue.  Exact Brown core is now narrower:
quantitatively bound the first time at which the fixed-shell capture law becomes small on the
Brown schedule.  Equivalently, prove finite-scale dephasing/undistortion for the ordinary local
shell; asymptotic occupation plus radial mixing cannot exclude an arbitrarily long initial
transient.

## Lean formalization

Formalized in
`formal/GaloisForLFunctions/HTGeometry/GaussianRadialAllLateHardnessTransferLaw.lean`.
The module proves the full-filter dilation theorem, Gaussian angular/product/radius
normalization, and the chi-radius specialization.  Targeted source check and module build pass.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for every exported
theorem.

## Log

- 2026-08-23 — Conjecture C1 (`Gaussian radius is an internal clock`) proved by reverse Fatou.
- 2026-08-23 — Hostile audit retained theorem but rejected it as Brown first-onset closure.
- 2026-08-23 — Formalized and wired into `GaloisForLFunctions.HTGeometry`; targeted build and
  axiom audit passed.
