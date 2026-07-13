# Sonin--prime-archimedean adjacent norm tomography

- **ID:** `sonin-prime-arch-adjacent-norm-tomography`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Convergence of the all-prime Sonin trace-Hankel form on the two probe families
  `X^n` and `X^n + X^(n+1)` is equivalent to convergence of its complete moment germ to the
  normalized prime--Gamma moment germ, and therefore implies RH.

## Goal

Replace the abstract all-moment Sonin/prime--Gamma weld by a concrete source-value problem on two
families of finite Hilbert--Schmidt norm probes. This does not solve their convergence, but it
removes arbitrary polynomial tests, Gram matrices, and direct odd trace moments from the analytic
interface.

## Theorem

Let `Q_a` be the unconditional positive all-prime Sonin trace-Hankel functional and let `m_a(r)` be
its intrinsic Hankel moment sequence. Lean proves the exact identities

\[
Q_a(X^n)=m_a(2n)
\]

and

\[
Q_a(X^n+X^{n+1})
=m_a(2n)+2m_a(2n+1)+m_a(2n+2).
\]

Thus every odd moment is recovered by the finite polarization formula

\[
m_a(2n+1)
=\frac{Q_a(X^n+X^{n+1})-Q_a(X^n)-Q_a(X^{n+1})}{2}.
\]

For a single positive aperture sequence `a_j`, convergence of these two norm families to the same
expressions in the normalized prime--Gamma moments is equivalent to coordinatewise convergence of
the whole Sonin moment sequence. The existing cofinal moment transfer then gives

\[
\begin{aligned}
&Q_{a_j}(X^n)\longrightarrow M_{2n},\\
&Q_{a_j}(X^n+X^{n+1})
  \longrightarrow M_{2n}+2M_{2n+1}+M_{2n+2}
  \quad(\forall n)\\
&\hspace{4cm}\Longrightarrow \mathrm{RH}.
\end{aligned}
\]

The same aperture sequence is essential: unrelated per-degree approximants would not reconstruct a
common moment germ.

## Positive analytic target

Prove the two displayed source-value limits directly from the explicit all-prime Sonin residual
kernel and the normalized prime--Gamma source formula. The source quantities are squared
Hilbert--Schmidt norms of

\[
K_aT_a^n,
\qquad
K_aT_a^n+K_aT_a^{n+1},
\]

so the remaining problem is a norm-asymptotic/value-relation problem, rather than arbitrary Hankel
positivity or Xi-divisor control.

## Classification

The polarization argument is standard quadratic-form algebra, so this card is not new scientific
knowledge. Its value is the exact reduction of the live RH interface to two explicit canonical norm
families.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/SoninPrimeArchAdjacentNormTomography.lean`

Main declarations:

- `soninAllPrimeTraceHankel_monomial_eq_energyMoment`
- `soninAllPrimeTraceHankel_adjacent_eq_energyMoments`
- `SoninPrimeArchAdjacentNormCoupling`
- `soninPrimeArchSingleMomentCoupling_of_adjacentNormCoupling`
- `soninPrimeArchAdjacentNormCoupling_of_singleMomentCoupling`
- `soninPrimeArchAdjacentNormCoupling_iff_singleMomentCoupling`
- `riemannHypothesis_of_soninPrimeArchAdjacentNormCoupling`

Verification:

- `lake build GaloisForLFunctions.RHTower.SoninPrimeArchAdjacentNormTomography` passes.
- Formal lint passes.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1 in-progress: explicit source-pure probe families and reconstruction formula isolated
- [x] 1 → 2 fully-proven: complete polarization proof with a common aperture sequence
- [x] 2 → 3 formalized: equivalence and implication to RH proved in Lean
- [ ] 3 → 4 publication-ready: supply the analytic norm asymptotics/value relations
