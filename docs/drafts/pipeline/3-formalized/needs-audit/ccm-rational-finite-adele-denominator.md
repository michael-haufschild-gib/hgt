# Compact finite-adele support confines diagonal rationals to one fractional lattice

- **ID:** `ccm-rational-finite-adele-denominator`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** arithmetic-orbit subproblem of `kreal-quaternionic-ccm-cokernel`
- **Statement:** every compact subset of \(\mathbb A_{\mathbb Q,f}\) has a common nonzero
  integer denominator; hence its intersection with diagonal \(\mathbb Q\) lies in
  \(d^{-1}\mathbb Z\).

## Theorem

Let \(K\subset\mathbb A_{\mathbb Q,f}\) be compact. There is a nonzero integer \(d\) such that
\[
  dK\subset\widehat{\mathbb Z}=\prod_p\mathbb Z_p.
\]
Consequently, if the diagonal finite adele of \(q\in\mathbb Q\) belongs to \(K\), then
\[
  dq\in\mathbb Z.
\]
In particular, for every compactly supported locally constant
\(\phi:\mathbb A_{\mathbb Q,f}\to\mathbb C\), one nonzero \(d\in\mathbb Z\) satisfies
\[
  \phi(q)\ne0\Longrightarrow dq\in\mathbb Z.
\]

## Proof

For one finite adele \(x=(x_p)_p\), only finitely many coordinates are nonintegral. At each
exceptional place, the local denominator-clearing theorem for the adic completion gives a nonzero
integer \(b_p\) for which \(b_px_p\in\mathbb Z_p\). The product of these finitely many \(b_p\)
clears every coordinate; multiplication by the remaining integer factors preserves local
integrality.

For each nonzero integer \(d\), set
\[
  U_d=\{x:d x\in\widehat{\mathbb Z}\}.
\]
The integral restricted product \(\widehat{\mathbb Z}\) is open in the finite adeles, and
multiplication by \(d\) is continuous, so \(U_d\) is open. The one-point argument proves that
the \(U_d\) cover \(\mathbb A_{\mathbb Q,f}\). A compact \(K\) has a finite subcover. The product
of its finitely many denominators is nonzero and is a common denominator, since an additional
integer factor preserves every \(\mathbb Z_p\).

If a diagonal rational \(q\) lies in \(K\), then \(dq\) is integral at every height-one prime of
\(\mathbb Z\). The Dedekind-domain intersection theorem therefore puts \(dq\) in the image of
\(\mathbb Z\to\mathbb Q\). Apply this to the compact topological support of \(\phi\).

## Hostile audit

- Compactness is essential: the full finite adele ring has no common denominator.
- The result confines denominators but does not make the supported diagonal set finite; numerators
  remain unbounded.
- No enumeration of primes, choice of rational prime representatives, numerical computation,
  Poisson formula, zero spectrum, positivity, or RH premise is used.
- The proof uses mathlib's actual restricted-product topology and adic-completion
  denominator-clearing theorem, not a surrogate product.

## Strongest positive survivor

Combined with archimedean Schwartz lattice summability and a global bound on the finite Bruhat
factor, this theorem yields the fixed-base \(\ell^1(\mathbb Q^\times)\) orbit estimate required
for trace class.

## Gates

- [x] exact conjecture
- [x] dependency-closed paper proof
- [x] formalize in Lean 4
- [ ] combine with archimedean lattice summability
- [ ] prove strong-Schwartz dependence in the idele-class parameter

## Lean realization

- **Module:** `GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteAdeleDenominator`
- **Capstones:**
  - `ccmRationalFiniteAdele_exists_integerDenominator`
  - `ccmRationalFiniteAdele_isCompact_exists_commonIntegerDenominator`
  - `ccmRationalFiniteAdele_isCompact_rationalDiagonalDenominator`
  - `ccmRationalFiniteBruhat_exists_integerDenominator`
- **Verification:** direct `lake env lean` check, cached leaf-module build, and `#print axioms`
  audit passed. Every capstone depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.

## Log

- 2026-07-25 — proved common-denominator confinement through open denominator stages and compact
  finite subcover; no computation or RH input used.
- 2026-07-25 — formalized against mathlib's actual finite adeles, restricted-product topology,
  adic completions, and Dedekind intersection theorem.
