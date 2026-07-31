# Xi relative-torsion integral-degree quantization — terminal record

- **ID:** `xi-relative-torsion-integral-degree-quantization`
- **Stage:** 5-failed
- **Type:** TERMINAL ROUTE RECORD / ALGEBRAIC NO-GO WITH POSITIVE CLASSIFICATION
- **Scientific status:** `[FALSIFIED] [PARENT ALGEBRA] [NOT RH]`
- **Source:** the anti-diagonal relative torsion
  \(\tau_p(\rho)=p^{2\operatorname{Re}\rho-1}\) in
  `../2-fully-proven/new_scientific_knowledge/gamma-copoisson-sonin-full-quotient-flatness-syzygy.md`

## Killed conjecture

The tempting argument was:
\[
 \tau_p(\rho)=p^{2\operatorname{Re}\rho-1},
 \qquad
 \text{integral source lattice}\Longrightarrow
 \tau_p(\rho)=p^n,\quad n\in\mathbb Z.
\]
Then the open-strip bound would give
\(-1<2\operatorname{Re}\rho-1<1\), hence \(n=0\) and RH.

The implication from the integral lattice to the displayed quantization is false.

## Exact counterexample and classification

Let
\[
 A=\mathbb Z[t,t^{-1}]
\]
and let \(L=Ae\) be the free rank-one integral Laurent module.  Multiplication by \(t\) is an
integral \(A\)-linear automorphism of \(L\), with determinant class \([t]\in K_1(A)\).

For every prime \(p\) and every real number \(\alpha\), base change along
\[
 \phi_{p,\alpha}:A\longrightarrow\mathbb C,
 \qquad
 t\longmapsto p^\alpha
\]
turns this same integral automorphism into multiplication by \(p^\alpha\).  Its positive
determinant modulus is therefore \(p^\alpha\), with no restriction that
\(\alpha\in\mathbb Z\).

More generally, the units of \(A\) are
\[
 A^\times=\{\pm t^n:n\in\mathbb Z\}.
\]
Thus integrality quantizes the Laurent exponent \(n\), while specialization gives
\[
 |\phi_{p,\alpha}(\pm t^n)|=p^{n\alpha}.
\]
It does not quantize the real specialization parameter \(\alpha\).  Equivalently, the
archimedean logarithmic regulator of an integral determinant class is real-valued:
\[
 \log |\phi_{p,\alpha}(t^n)|=n\alpha\log p.
\]

Taking \(n=1\) and
\(\alpha=2\operatorname{Re}\rho-1\) realizes the exact Sonin relative torsion for every point in
the critical strip.  The integral determinant class therefore coexists with arbitrary off-line
torsion.

## Why the route failed

The conormal character \(p^{2\operatorname{Re}\rho-1}\) is the value of a universal Laurent
coordinate after spectral specialization.  It is not the power of a fixed arithmetic scalar
whose exponent is forced to be integral.  Confusing these two roles turns an integral
\(K_1\)-class into a false discreteness statement about its archimedean regulator.

The existing integral Fitting charge does not repair the argument.  It reads Xi multiplicity,
not horizontal position, and can be nonzero at any hypothetical off-line zero.  Regularized
determinants are even less rigid: regularization can produce arbitrary real logarithmic values.

## Positive survivor

The exact positive classification is:

```text
integral Laurent determinant class:
  quantized algebraic exponent n;

spectral base change:
  arbitrary real regulator n alpha log p;

horizontal localization:
  requires an independent theorem constraining alpha.
```

Integrality can become RH-relevant only if the literal source proves, before taking the
archimedean regulator, that the Xi specialization factors through a discrete or unitary locus.
But for the rank-one conormal character that factorization is already the missing
source-dagger/tempered landing theorem.  It cannot be inferred from the existence of an integral
lattice.

The surviving invariant is therefore not an integral value of \(\tau_p\).  It is the
source-normal Stokes/Bockstein class whose regulator is
\(\log\tau_p\), together with a source theorem identifying Riemann inverse duality with Hilbert
adjunction on that same nonzero class.

## Corpus collision

- `../3-formalized/not_new_scientific_knowledge/sem-integral-fitting-charge.md` proves that the
  integral seam channel reads multiplicity and disappears after additive rational base change;
  it does not constrain \(\operatorname{Re}\rho\).
- `../2-fully-proven/not_new_scientific_knowledge/determinant-line-trivialization-zero-divisor-blindness.md`
  proves that determinant-line topology alone does not control a divisor.
- `../2-fully-proven/not_new_scientific_knowledge/thermodynamic-divisor-charge-finite-ancestor-or-boundary-index.md`
  shows that a genuine infinite charge must be a finite ancestor or a nonliftable boundary
  index; neither condition makes its real regulator integral.
- `../2-fully-proven/not_new_scientific_knowledge/source-linear-essential-superselection-no-sewing.md`
  identifies the live category: a relative source anomaly before closed boundary descent.

## Lean decision

The counterexample is elementary Laurent-module base change and the unit classification is
standard commutative algebra.  Formalizing only this abstract scalar specialization would not
formalize the analytic Sonin determinant line and would be theatre.  No Lean wrapper is added.

## Gates

- [x] proposed integral-degree implication isolated
- [x] explicit integral rank-one counterexample supplied
- [x] complete unit/regulator classification supplied
- [x] collisions with integral Fitting, determinant-line, and boundary-index corpus audited
- [x] positive survivor extracted
- [ ] no further work in this form
