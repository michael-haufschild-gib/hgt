# Route R variable-grade Euler boundary and fixed-fibre specialization

- **ID:** route-r-variable-grade-euler-boundary-specialization
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `docs/drafts/pipeline/1-in-progress/cofinal-bockstein-polarized-adelic-stokes.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/RouteRFixedTraceTailRoos.lean`
- **Statement:** The reflected-minus-forward Route R Fisher Bockstein is an exact reflection boundary on the pre-divisor variable-grade Euler source, and its fixed-tail specialization is null exactly at neutral grade.

## Goal

Separate two statements which previous formulations conflated: source exactness before fixing a
modular grade, and null-homology after evaluation in one fixed physical fibre.  The theorem
identifies the exact specialization commutator which the missing landing law must annihilate.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, hostile comparison with fixed-tail classification
- [x] 1 → 2 fully-proven: complete proof below, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted module build, axiom audit
- [ ] 3 → 4 publication-ready

## Exact theorem

Let
\[
  V=\{f:\mathbb R\to\mathbb C^{\mathbb N}\},\qquad
  (Rf)(t)=f(-t),\qquad d=R-1.
\]
Enumerate ordinary primes by \(p_n\), put
\[
  D(p)=\frac{p}{(p+1)^2},\qquad F(t)_n=p_n^tD(p_n),
\]
and define \(\beta_t=F(-t)-F(t)\).  Then:

1. \(dF=\beta\), so the class of \(\beta\) in \(V/\operatorname{im}d\) is zero
   unconditionally and retains both Gamma orientations as the two values \(F(-t),F(t)\).
2. Evaluation at a fixed grade gives
   \(\operatorname{ev}_t(dF)=\beta_t\).  For \(|t|<1\), its diagonal fixed-tail Roos
   class is zero if and only if \(t=0\).
3. The coefficient is the literal polarized Euler Fisher source column:
   \[
     \beta_t(p)=\frac{p^{-t}-p^t}{2}
       \left\langle e_p,s_{\rm Fisher}\right\rangle,
     \qquad
     \left\langle e_p,s_{\rm Fisher}\right\rangle
       =\frac{2p}{(1+p)^2}=2D(p).
   \]

At an Xi divisor point \(\rho\), with \(t=2\Re\rho-1\), the variable-grade source class remains
zero while the fixed-fibre class is zero exactly when \(\Re\rho=1/2\).

## Proof

For every \(t,n\), direct evaluation gives
\[
 (dF)(t)_n=(RF)(t)_n-F(t)_n
 =F(-t)_n-F(t)_n
 =p_n^{-t}D(p_n)-p_n^tD(p_n)=\beta_t(p_n).
\]
Thus \(dF\in\operatorname{im}d\), proving the first claim, and evaluation proves the second
identity.  The existing fixed-tail rigidity theorem says that the only unrestricted Roos
primitive of the diagonal mismatch is the negative literal tail.  Such a primitive lies in every
fixed summable tail ideal exactly when \(\beta_t\in\ell^1\).  The proved prime-Fisher threshold is
\[
  \beta_t\in\ell^1\quad\Longleftrightarrow\quad t=0
  \qquad (|t|<1),
\]
so the fixed-tail class has the asserted zero set.

The polarized Euler source theorem computes its test/score column at the real node \(p\) as
\[
  \langle e_p,s_{\rm Fisher}\rangle=\frac{2p}{(1+p)^2}.
\]
Multiplication by \((p^{-t}-p^t)/2\) gives \(\beta_t(p)\) exactly.  No division by \(t\), Xi,
or a divisor coefficient occurs.  Finally the corpus bound
\(|2\Re\rho-1|<1\) permits the fixed-tail classification, and elementary algebra identifies
\(2\Re\rho-1=0\) with \(\Re\rho=1/2\).

## Lean realization

`RouteRFixedTraceTailRoos.lean` contains:

- `routeRPrimeGammaVariableGradeCentralBocksteinClass_eq_zero`;
- `routeRPrimeGammaVariableGradeBoundary_apply`;
- `routeRPrimeGammaVariableGradeBoundary_fixedTailClass_eq_zero_iff`;
- `routeRPrimeGammaEulerFisherColumn_eq_sourcePairing`;
- `routeRPrimeGammaBockstein_eq_eulerFisherSourceColumn`;
- `routeRPrimeGammaVariableGradeBoundary_fixedXiSpecialization`;
- `routeRPrimeGammaVariableGradeBoundary_fixedXiClass_eq_zero_iff_hodgeMateCoefficient_eq_zero`.

Targeted module build completed successfully (`11297/11297`).  Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Hostile audit

This is a `[BRIDGE]`, not the missing landing theorem.  Source exactness occurs in the
variable-grade quotient because reflection moves the grade.  Fixed-fibre evaluation does not
descend through that quotient off neutral grade; the nonzero fixed-tail class measures precisely
this failure.  Therefore reflection coinvariants, twisted-coefficient renaming, or an absolute
source contraction cannot prove physical annihilation.  A successful landing must independently
show that the actual fixed completed-Xi lift has zero transverse specialization commutator.

## Log

- 2026-08-05 — `[PAPER-PROVED]`; dependency-closed proof and hostile specialization audit recorded.
- 2026-08-05 — `[LEAN-VERIFIED]`; source quotient, Euler coefficient provenance, fixed-Xi base
  change, exact physical endpoint, targeted build, and axiom audit complete.
