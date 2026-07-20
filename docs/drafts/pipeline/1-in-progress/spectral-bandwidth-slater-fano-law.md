# Spectral-bandwidth Slater Fano law

- **ID:** spectral-bandwidth-slater-fano-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / UNIVERSAL HILBERT-SPACE LAW / NOVELTY GATE
- **Scientific status:** `[PAPER-PROVED] [LEAN OPEN]`
- **Novelty:** `[NOVELTY UNVERIFIED]`; no priority claim
- **Source:** positive survivor of the quartic Fock-stability conjecture
- **Statement:** Spectral bandwidth alone gives the sharp dimension-free threshold at which every
  Slater determinant has sub-Poisson additive spectral statistics.

## Goal

Replace the single-top and annihilation-invariance restrictions of the current Gaussian/Fock
phase laws by a theorem about an arbitrary finite subspace of an arbitrary spectrally graded
Hilbert space.  The theorem must expose an exact threshold, prove that the threshold is sharp, and
specialize to unconditional quartic stability without a graph decomposition or a completion
certificate.

## Gates

- [x] 0 -> 1 in-progress: well-posed, parent theory separated, hostile proof audit complete
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open mathematical dependency
- [ ] 2 -> 3 formalized: exact universal bound and quartic corollary compiled unconditionally
- [ ] 3 -> 4 publication-ready: independent novelty audit plus a genuine metric/application theorem

The checked paper proof is recorded here before Lean work.  The card remains in `1-in-progress`
until the theorem-shaped external novelty audit and the exact formal statement are both closed.

## The universal law

Let `H` be a finite-dimensional real or complex Hilbert space, let `A=A*` be a one-particle
observable with spectrum in the interval `[a,b]`, and assume `0 <= a <= b`.  Let `S subset H` be
an `r`-dimensional occupied subspace and let `Psi_S` be its normalized Slater determinant.  Write

\[
 X=d\Gamma(A)
\]

for the additive many-body observable on the exterior power.  Then

\[
 \boxed{\quad
 \mathbb E_{\Psi_S}X-\operatorname{Var}_{\Psi_S}(X)
 \ \ge\ r\left(a-\frac{(b-a-1)^2}{4}\right).
 \quad}                                                     \tag{SBF}
\]

If the spectral width `delta=b-a` is at most one, the stronger sharp bound is

\[
 \mathbb E_{\Psi_S}X-\operatorname{Var}_{\Psi_S}(X)\ge ra. \tag{SBF0}
\]

Consequently every occupied subspace is sub-Poisson whenever

\[
 \boxed{\quad b-a\le 1+2\sqrt a.\quad}                    \tag{ST}
\]

For positive integral degrees `1,...,M`, (ST) becomes `M <= 4`.  Thus every finite graded
subspace supported in positive degrees at most four has nonnegative mean-minus-variance, with no
annihilation invariance.  Conversely, degree five is the first possible degree of a negative
margin, already in a two-dimensional one-particle Hilbert space and a rank-one occupied subspace.

## Dependency-closed proof `[PROVED HERE]`

Choose an orthonormal basis `u_1,...,u_r` of `S` and put

\[
 \mu_i=\langle u_i,Au_i\rangle,
 \qquad \nu_i=\langle u_i,A^2u_i\rangle,
 \qquad C_{ij}=\langle u_i,Au_j\rangle.
\]

The standard Slater one-body moment identities give

\[
 \mathbb E X=\sum_i\mu_i,
 \qquad
 \operatorname{Var}(X)=\sum_i\nu_i-\sum_{i,j}|C_{ij}|^2. \tag{1}
\]

This identity is parent full-counting-statistics theory; it is not the proposed novelty.

Because `(x-a)(x-b) <= 0` on `[a,b]`, functional calculus gives

\[
 A^2\le(a+b)A-abI.
\]

Therefore

\[
 \nu_i\le(a+b)\mu_i-ab.                                  \tag{2}
\]

Keeping only the diagonal squares in (1), and then using (2), yields

\[
\begin{aligned}
 \mathbb E X-\operatorname{Var}(X)
 &\ge\sum_i(\mu_i-\nu_i+\mu_i^2)\\
 &\ge\sum_i\left(\mu_i^2-(a+b-1)\mu_i+ab\right)\\
 &=\sum_i\left[
   \left(\mu_i-\frac{a+b-1}{2}\right)^2
   +a-\frac{(b-a-1)^2}{4}\right].                       \tag{3}
\end{aligned}
\]

Dropping the squares proves (SBF).  If `b-a <= 1`, the vertex `(a+b-1)/2` lies at or below `a`,
while every `mu_i` lies in `[a,b]`.  The quadratic in the second line of (3) is then increasing
on `[a,b]` and its minimum is its value `a` at `mu_i=a`; this proves (SBF0).

For the nonnegative phase, (SBF) is nonnegative exactly when

\[
 (b-a-1)^2\le4a.
\]

When `b-a >= 1`, this is equivalent to (ST).  When `b-a <= 1`, (SBF0) is already nonnegative,
so (ST) again gives the unified threshold.

## Sharpness and equality

Assume `delta=b-a >= 1`, and let

\[
 p=\frac{\delta-1}{2\delta}.
\]

For each occupied direction choose orthonormal endpoint eigenvectors `e_i^-`, `e_i^+` satisfying
`Ae_i^-=ae_i^-` and `Ae_i^+=be_i^+`, with different pairs mutually orthogonal, and put

\[
 u_i=\sqrt{1-p}\,e_i^-+\sqrt p\,e_i^+.
\]

Then the `u_i` are orthonormal, all off-diagonal `C_ij` vanish, each spectral measure is supported
on the two endpoints, and

\[
 \mu_i=a+p\delta=\frac{a+b-1}{2}.
\]

Every inequality in (2)--(3) is therefore an equality.  Hence (SBF) is sharp in every rank once
both endpoint eigenspaces have multiplicity at least `r`.  If `delta <= 1`, taking `S` inside the
`a`-eigenspace attains (SBF0).  Thus the threshold cannot be enlarged using only `a`, `b`, and
`r`.

For integral positive degrees, `a=1`, `b=M`.  At `M=4`, equality is the endpoint mixture
`p=1/3` between degrees one and four.  At `M=5`, the minimizing mixture `p=3/8` has margin
`-1/4` per occupied direction.  These are symbolic consequences of the exact formula, not
numerical evidence.

## Metric and Fock connector

The canonical Pluecker degree law of a finite graded Hilbert subspace is exactly the spectral
measurement law of `dGamma(A)` in its Slater determinant.  Therefore (SBF) applies directly to
polynomial collision spaces in symmetric Fock space after splitting off any occupied vacuum
direction.  In particular it proves the former conjecture ACB-3 in the stronger form:

> Every finite graded Hilbert subspace supported in degrees `0,...,4` and containing the vacuum
> has nonnegative determinant-line degree Fano margin, without annihilation invariance.

Via the existing partition-curvature identity, this says that every such quartic collision model
has nonpositive logarithmic Gaussian Gram-determinant curvature.  The connector from the compiled
coordinate compression expression to the existing canonical Pluecker partition is a formalization
obligation, not an assumption to be hidden in the headline.

## Hostile attacks

1. **Known-ingredient attack.**  The Slater moment formula is standard in fermionic full counting
   statistics, and the scalar spectral estimate is the Bhatia--Davis secant bound.  Neither is new.
   The candidate content is only the sharp combined bandwidth/Fano threshold and its simultaneous
   interpretation for Slater states, projection determinantal processes, and Gaussian/Fock
   determinant curvature.
2. **Off-diagonal attack.**  Dropping `i != j` compression squares can only lower the margin;
   endpoint-pair extremizers make them vanish, so this loss does not weaken the universal constant.
3. **Small-width attack.**  Formula (SBF) is not sharp when `b-a<1`; (SBF0) closes that defect and
   gives the correct piecewise optimum.
4. **Rank attack.**  The bound is independent of ambient dimension and exact in every rank by
   orthogonal direct sums of endpoint pairs.
5. **Quartic-theatre attack.**  The number four is not fitted to the earlier example.  It is the
   exact integer point at which `1+2*sqrt(1)=3` allows the positive-degree width `M-1`; degree five
   violates the universal threshold and has an endpoint-pair equality witness.
6. **Publication attack.**  A short corollary of two parent facts is not automatically suitable for
   a general journal.  General-journal status remains open until the theorem has a formal Pluecker/
   Gaussian connector and at least one independently compelling consequence outside the originating
   construction.  No such status is claimed on this card.

## External novelty boundary

Searches checked theorem-shaped combinations of `Slater determinant`, `Bhatia--Davis`, `spectral
width`, `Fano factor`, `weighted determinantal process`, and `mean minus variance`.  They found:

- Klich's determinant/full-counting-statistics trace formula as parent theory;
- Bhatia--Davis variance bounds as parent theory;
- the standard variance formula for additive functionals of projection determinantal processes;
- extensive model-specific sub-/super-Poisson and free-fermion counting literature.

No exact spectral threshold (ST), sharp dimension-scaled inequality (SBF), or quartic Fock/Gaussian
corollary was found.  This is an exact-search boundary, not evidence that the theorem is absent from
all literature.  The novelty label remains `[NOVELTY UNVERIFIED]`.

## Lean target

Create `GaloisForLFunctions.HilbertMetric.SpectralBandwidthFano` with unconditional finite-coordinate
statements:

1. the secant square inequality on `[a,b]`;
2. the Slater compression mean, second moment, variance, and Fano margin;
3. the sharp interval lower bound (SBF);
4. the bandwidth nonnegativity criterion and the quartic `[1,4]` corollary;
5. if the existing exterior API permits it without a certificate layer, the canonical Pluecker
   moment connector.

## Log

- 2026-07-20 -- extracted from ACB-3 after the symmetric-shadow theorem; separated the Klich and
  Bhatia--Davis parents, proved the sharp interval law and equality construction, and retained the
  conservative `[NOVELTY UNVERIFIED]` label pending exact Lean and broader application work.
