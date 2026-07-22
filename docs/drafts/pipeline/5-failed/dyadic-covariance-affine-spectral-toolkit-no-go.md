# Dyadic covariance affine-spectral toolkit no-go

- **ID:** `DYADIC-COV-PREPRINT-NOGO-001`
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** Juan Moreno Borrallo, Zenodo record 20082725 (2026-05-08)
- **Statement:** The claimed unconditional square-root Mertens closure fails because its two decisive “external shifted-convolution” inputs are not theorems cited in the literature and are false for the coefficient classes stated.

## Goal

Audit the strongest located current claim of

```text
M(N) <<_epsilon N^(1/2+epsilon),
```

before opening another dyadic-covariance route.  Determine whether its packet law supplies the
missing source `OPEN-SOURCE-001` or merely assumes it in analytic language.

## Exact killing mechanisms

### 1. The formal `AnalyticToolkit` assumes the result-bearing branch bounds

The archived Lean file `RequestProject/ExternalAnalytic.lean` makes
`LSRBranchBoundStatement`, `NLSRBranchBoundStatement`, and the resulting per-packet bound fields
of an `AnalyticToolkit`.  The final Mertens theorem is conditional on an inhabitant of this
structure.  No construction of that inhabitant from published analytic theorems is formalized.

Worse, its purported `BDHStatement` is false.  It quantifies over every integer-valued function
supported on `(Y/2,Y]`, without a size condition and without subtracting an expected main term.
At `Y=2`, `q=1`, take `f(2)=5` and `f(n)=0` otherwise.  Its left side is `25`, while its right
side is

```text
2 * (1 + log_2 2)^3 = 16.
```

Thus `BDHStatement` is false and `AnalyticToolkit` has no inhabitant.  A theorem conditional on
that structure is vacuous.

### 2. The manuscript's terminal affine theorem has a constant-mode counterexample

Theorem `external-fixed-depth-divisor-coefficient-shifted-convolution-terminal-affine` claims,
for arbitrary stated fixed-depth divisor coefficients on a primitive shifted line,

```text
|sum_(ell_1 x - ell_2 z = h) alpha(x) beta(z) W_1(x/X) W_2(z/Z)|
  << (1 + ell_1 X + ell_2 Z)^(1/2+epsilon)
```

up to conductor, shift, and Sobolev factors.  Set `ell_1=ell_2=1`, `h=1`, use coefficient
sequences `alpha=beta=1`, and choose smooth nonnegative weights equal to `1` on a common dyadic
subinterval.  The sum has `asymp X` positive terms.  For every fixed `epsilon<1/2`, the claimed
right side is `O(X^(1/2+epsilon))`.  Contradiction.

The later theorem `external-blomer-harcos` is even less specified: it infers a power saving from
only a primitive affine relation, smooth compact support, and finite residue multiplicity.  The
same constant-coefficient packet refutes it.

### 3. The cited papers do not supply either statement

Blomer--Harcos prove a spectral decomposition for shifted convolutions of **Hecke eigenvalues of
holomorphic or Maass cusp forms**, not arbitrary divisor-bounded, sieve-generated, Vaughan, or
Heath--Brown coefficients.  Topacogullari proves asymptotic formulas for particular additive
divisor problems; these formulas contain arithmetic main terms rather than universal
square-root cancellation.  Expanding a coefficient into finitely many divisor variables does
not turn it into a cuspidal automorphic Fourier coefficient.

Primary sources:

- V. Blomer and G. Harcos, *The spectral decomposition of shifted convolution sums*,
  arXiv:math/0703246, Duke Math. J. 144 (2008), 321--339.
- B. Topacogullari, *On a certain additive divisor problem*, arXiv:1512.05770,
  Acta Arith. 181 (2017), 143--172.
- B. Topacogullari, *The shifted convolution of generalized divisor functions*,
  arXiv:1605.02364, IMRN 2018, no. 24, 7681--7724.

## No-go closure

- **Exact killing theorem/mechanism:** Constant/Eisenstein modes survive primitive affine
  restriction and smooth localization.  Neither primitivity nor divisor bounds imply
  cancellation.  Any universal square-root shifted-line theorem for this coefficient class is
  false.
- **Strongest positive survivor:** **Cusp-projection necessity law.**  A valid spectral packet
  closure must either (i) restrict coefficients to a proved cuspidal automorphic class, or (ii)
  display and subtract every Eisenstein/main-term projection, then prove cancellation for the
  centered remainder.  For sieve-generated Möbius packets, bounding the undisposed centered
  remainder is the binary Möbius/parity frontier itself; renaming it a spectral ledger does not
  discharge it.
- **New insight:** `OPEN-SOURCE-001` cannot enter through a coefficient-blind affine spectral
  envelope.  Exact signed recombination across all Möbius packets must occur **before** any
  coefficientwise absolute value.  This narrows future source attacks to a global cancellation
  identity or a genuinely Möbius-specific centered spectral theorem.
- **Status:** Counterexamples are dependency-closed on paper.  Survivor is a necessary-interface
  classification, not claimed as new scientific knowledge.  No Lean module is admitted because
  the falsified objects belong to an external toy formalization and do not occur in the HGT
  theorem graph.

## Literature audit

The preprint and archive were acquired from the primary Zenodo DOI
`10.5281/zenodo.20082725`.  The author explicitly identifies the packet law and terminal affine
branch as analytic bottlenecks.  The archive description also states that deep analytic inputs
are registered as axioms.  No peer-reviewed source for either false shifted-convolution theorem
was found.

## Log

- 2026-07-22 — primary archive acquired; manuscript, proof map, and Lean source audited.
- 2026-07-22 — formal `BDHStatement` refuted by finite supported function.
- 2026-07-22 — both manuscript shifted-convolution inputs refuted by constant/Eisenstein packet.
- 2026-07-22 — route retired; exact source remains `OPEN-SOURCE-001`.
