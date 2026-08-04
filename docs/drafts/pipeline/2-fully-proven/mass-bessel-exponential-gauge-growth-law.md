# Mass-Bessel exponential-gauge growth law

**Stage:** 2 — fully proven on paper  
**Date frozen:** 2026-08-04  
**Label:** `[BRIDGE] [PAPER-PROVED]`  
**Origin:** positive survivor of the failed critical-gauge energy conjecture

## 1. Exact theorem

Let `a>\lambda>0`.  For `u,\xi\in\mathbb R`, set

\[
 m_{a,\lambda,u}(\xi)
 =\exp\!\left(-iu\sqrt{(\xi-i\lambda)^2+a^2}\right),
\]

where the square root is principal, and let `G_{a,\lambda}(u)` be the
corresponding Fourier multiplier on `L^2(\mathbb R)`.

Then:

1. `G_{a,\lambda}` is a strongly continuous group of bounded operators;
2. for every real `u`,
   \[
   \|G_{a,\lambda}(u)\|_{L^2\to L^2}=e^{\lambda|u|};
   \]
3. no Hilbert norm equivalent to `L^2` is invariant under every
   `G_{a,\lambda}(u)`.

For the mass-Bessel route, `\lambda=1/2` and `a>1/2`, so the exact norm is
`e^{|u|/2}`, independent of mass.

## 2. Dependency ledger

- Principal square root is continuous on
  `{(\xi-i\lambda)^2+a^2:\xi\in\mathbb R}` because `a>\lambda` keeps the
  curve away from the non-positive branch cut.
- An `L^2` Fourier multiplier has operator norm equal to the essential
  supremum of its symbol.
- Pointwise-continuous uniformly bounded multipliers on compact `u` intervals
  give strong continuity by dominated convergence.
- Equivalent norms turn an invariant group into a uniformly bounded group in
  the original norm.

No number-theoretic hypothesis enters.

## 3. Proof

Write

\[
 \sqrt{(\xi-i\lambda)^2+a^2}=p(\xi)+iq(\xi),\qquad p(\xi)>0.
\]

Then

\[
 q(\xi)^2
 =\frac{R(\xi)-(\xi^2+a^2-\lambda^2)}2,
\]

where

\[
 R(\xi)=\sqrt{(\xi^2+a^2-\lambda^2)^2+4\xi^2\lambda^2}.
\]

The identity

\[
 (\xi^2+a^2+\lambda^2)^2-R(\xi)^2=4a^2\lambda^2
\]

implies `|q(\xi)|<\lambda`.  Since
`2p(\xi)q(\xi)=-2\xi\lambda`, `q` has sign opposite to `\xi`.
Dividing the displayed formula for `q^2` by `\xi^2` and passing to infinity,
or rationalizing it first, gives

\[
 \lim_{\xi\to-\infty}q(\xi)=\lambda,
 \qquad
 \lim_{\xi\to+\infty}q(\xi)=-\lambda.
\]

Consequently

\[
 \operatorname*{ess\,sup}_{\xi\in\mathbb R}
 |m_{a,\lambda,u}(\xi)|
 =\operatorname*{ess\,sup}_{\xi}e^{u q(\xi)}
 =e^{\lambda|u|}.
\]

The multiplier norm theorem proves part 2.  The symbols multiply in the
`u` parameter, so the operators form a group.  For `|u|\le T`, their moduli
are bounded by `e^{\lambda T}`; pointwise convergence and dominated convergence
prove strong continuity.

Finally, suppose an equivalent Hilbert norm `\|\cdot\|_*` is invariant and

\[
 c\|f\|_2\le\|f\|_*\le C\|f\|_2.
\]

Then

\[
 \|G_{a,\lambda}(u)f\|_2
 \le c^{-1}\|G_{a,\lambda}(u)f\|_*
 =c^{-1}\|f\|_*
 \le (C/c)\|f\|_2
\]

uniformly in `u`, contradicting part 2.  This proves part 3.

## 4. Connection to the Bessel trace

For `\Re t>0`, the standard Fourier--Bessel identity is

\[
 \frac{2at}{\sqrt{t^2+x^2}}K_1\!\left(a\sqrt{t^2+x^2}\right)
 =\int_{\mathbb R}e^{-t\sqrt{\xi^2+a^2}}e^{i\xi x}\,d\xi
\]

up to Fourier normalization.  With `t=\sigma+iu`, every Bessel atom therefore
solves `U_{uu}-U_{xx}+a^2U=0`.  Exponential conjugation in `x` replaces `\xi`
by `\xi-i\lambda`, exactly producing the theorem's symbol.

## 5. Significance and limit

The theorem unifies two formerly separate observations:

- the prime source has critical spatial exponent `1/2`;
- complex-time Bessel estimates have unavoidable type `1/2`.

They are the same gauge invariant.  Mass affects finite-frequency dispersion
but cannot change the limiting imaginary part of the conjugated symbol.

This does **not** prove the uniform trace bound.  It proves that any successful
argument must remove the unstable `\lambda=1/2` modes by arithmetic cancellation
or a source-selected stable subspace.  Positive coercive Klein--Gordon energy
cannot do it.

## 6. Novelty audit

The exact calculation is likely standard within exponentially weighted
Klein--Gordon theory.  Its value here is the route-specific identification of
the Bessel `1/2` barrier with prime-source gauge.  Label remains `[BRIDGE]`, not
`[NOVEL]`, unless an external exact-collision search proves otherwise.

## 7. Lean target

Formalize the algebraic core without spectral computation:

1. define the real and imaginary parts of the principal square root on the
   curve `(\xi-i\lambda)^2+a^2`;
2. prove `|q(\xi)|<\lambda` and the two limits;
3. deduce the exact supremum `\sup_\xi e^{u q(\xi)}=e^{\lambda|u|}`;
4. prove the abstract equivalent-norm no-unitarization corollary.

Status: `[PAPER-PROVED]`; Lean module not yet written.
