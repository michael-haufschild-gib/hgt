# Matched phase-disk center gauge has exact cone-reversal obstruction

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseDiskCofinalGaugeNoGo`.
This sharply retires positive scalar finite-part assembly of the local matched phase-disk
completions. It does not prove the global completed source nonnegative and is not an RH proof.

## Conjecture and outcome

The preceding matched phase-disk theorem gives one pointwise nonnegative rotated Schur diagonal

\[
P_n(\xi)=w_n(1+\cos\theta_n)-q_n(\xi),
\qquad
q_n(\xi)=\cos\theta_n C_n(\xi)+\sin\theta_n S_n(\xi).
\]

A plausible global repair was to sum these local positive diagonals after subtracting their
divergent scalar center trace. The corpus instead forces the orthogonal half-angle diagonal

\[
Q_n(\xi)=w_n(1-\cos\theta_n)+q_n(\xi)\ge 0.
\]

Lean proves the fixed-trace law

\[
P_n(\xi)+Q_n(\xi)=2w_n
\]

and therefore the exact cone-reversal identity

\[
P_n(\xi)-2w_n=-Q_n(\xi)\le0.
\]

Thus center subtraction does not leave a weaker positive remainder. It lands exactly in the
negative of the complementary PSD channel. This closes the scalar trace-renormalization route,
not merely the unrenormalized summation route.

## Cofinal prime obstruction

At spectral center the two channels polarize completely:

\[
P_n(0)=2w_n,\qquad Q_n(0)=0.
\]

For a prime coordinate `p`, the CCM--Suzuki coefficient weld gives

\[
P_p(0)=2w_p=2\,\texttt{suzukiCriticalSharpPrimeMass}(p).
\]

The Suzuki sharp prime mass is already proved nonsummable in the corpus. Lean consequently proves

\[
\neg\operatorname{Summable}_{p\in\mathbb P} P_p(0).
\]

Using the corpus's universal cofinal finite-part theorem, Lean further proves:

- no finite-valued positive linear functional on all prime observables can preserve every finite
  cutoff of this center gauge;
- every finite-valued exact linear extension is unbounded below on the pointwise nonnegative cone.

These are unconditional theorems, with no continuity assumption and no chosen regulator.

## Higher principle and surviving route

Local positivity and global trace cancellation do not commute. The local Gram disk is a genuine
two-channel object with conserved trace. The global completed Gamma/Robin source cancels scalar
mass before positivity, while a primewise Schur diagonal consumes that same mass as positive trace.
Any successful global carrier must therefore be trace-cancelled and cross-prime coupled before a
positive compression is taken. Semifinite trace, signed gauge, or coherent off-diagonal covariance
remain possible; positive scalar finite part does not.

This redirects the next search toward corpus constructions where prime and archimedean channels
already share one coupled characteristic, quotient, or Hankel Gram object. Importing the local
disks independently and renormalizing afterward is formally impossible.

## Lean audit

- scratch conjecture/proof loop: passed;
- direct leaf check: passed;
- exact leaf-module build: passed;
- umbrella import: wired, umbrella not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in the new module.
