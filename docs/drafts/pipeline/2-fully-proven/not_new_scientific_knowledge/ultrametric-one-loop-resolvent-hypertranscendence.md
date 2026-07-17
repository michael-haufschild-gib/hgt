# Ultrametric one-loop resolvent hypertranscendence

- **ID:** `ultrametric-one-loop-resolvent-hypertranscendence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / QFT-COSMOLOGY BRIDGE
- **Scientific status:** `[PROVED] [PHYSICAL SOURCE-INTERNAL BRIDGE] [PARENT-DERIVED]`
  `[NOVELTY UNVERIFIED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Scope:** general hypertranscendence in a quantum effective action; no RH or distinguished
  special-function input
- **Statement:** The first ultraviolet-finite mass susceptibility of the one-loop determinant of
  the exact one-sided ultrametric boundary spectrum is hypertranscendental.  Its complete infinite
  shell tail is uniquely fixed by a two-shell rational defect and one contractive scale
  constraint.  Mode by mode, the same function is an exact source-internal de Sitter effective-
  action reporter.

## Source spectrum and reporter

Let `p >= 2` be prime.  The positive spectrum of the Neumann-to-Dirichlet operator on the
`p`-adic unit circle, in units of its overall energy scale, is

```text
E_n = p^n,                         n >= 0,
rho(0) = p-2,
rho(n) = (p-1)^2 p^(n-1),         n >= 1.                 (1)
```

For an integer `m >= 2`, define the higher resolvent trace

```text
Q_(p,m)(x)
  = (p-2)/(x+1)^m
    + (p-1)^2 sum_(n>=1) p^(n-1)/(x+p^n)^m.               (2)
```

On compact subsets avoiding the points `-p^n`, the tail is normally convergent because its
`n`-th term is `O(p^(-(m-1)n))`.  Hence `(2)` is meromorphic, and it is a holomorphic germ at
`x=0`.

The threshold `m=2` is physical rather than cosmetic.  If

```text
W_N(x) = (1/2) sum_(n=0)^N rho(n) log(x+p^n),              (3)
```

then `W_N` and `W_N'` diverge as `N -> infinity`, whereas

```text
W_N''(x) -> -(1/2) Q_(p,2)(x).                             (4)
```

The large-shell expansion of `(3)` shows that the divergent internal-shell counterterms are
constant and linear in `x`; all quadratic and higher coefficients converge.  Thus `(4)` is the
first cutoff-independent curvature of this one-sided internal determinant.

## Exact scale-defect theorem

The resolvent trace satisfies

```text
Q_(p,m)(x)
  = (p-2)/(x+1)^m + 1/(x+p)^m
    + p^(1-m) Q_(p,m)(x/p).                                (5)
```

**Proof.** Multiplying `Q_(p,m)(x/p)` by `p^(1-m)` changes the base-shell coefficient at
`(x+p)^(-m)` to `p(p-2)`.  For every `n >= 1`, it shifts the coefficient at shell `n` to

```text
p rho(n) = rho(n+1).                                      (6)
```

The missing coefficient at the first shifted shell is exactly

```text
(p-1)^2 - p(p-2) = 1.                                    (7)
```

Equations `(6)` and `(7)` give `(5)` term by term.  ∎

The constraint is rigid among formal germs at `x=0`.  If `Y` solves the homogeneous equation

```text
Y(x) = p^(1-m) Y(x/p),                                    (8)
```

then its coefficient `y_k` satisfies

```text
(1 - p^(1-m-k)) y_k = 0.                                  (9)
```

For `p >= 2`, `m >= 2`, and `k >= 0`, the factor in `(9)` is nonzero.  Hence every `y_k` vanishes,
so `(5)` uniquely determines `(2)` as a formal power series.  This is a static source constraint,
not a time-evolution law.

The Taylor coefficient forced by `(5)` is explicitly

```text
[x^k] Q_(p,m)
  = (-1)^k binom(m+k-1,k)
    ((p-2) + p^(-(m+k))) / (1-p^(1-m-k)).                 (10)
```

## Hypertranscendence theorem

Equation `(5)` is a first-order affine `q`-difference equation over `C(x)` with `q=1/p`.
It can be homogenized to a scalar linear `q`-difference equation.  The meromorphic continuation
of `(2)` has a pole of order `m` at every `-p^n` for `n >= 1`; the coefficient of that pole is
nonzero and no other summand has the same pole.  Therefore `Q_(p,m)` is not rational.

The `q`-difference rational-or-hypertranscendental theorem of
Adamczewski--Dreyfus--Hardouin now gives

```text
Q_(p,m) is hypertranscendental over C(x)                  (11)
```

for the Euler derivation `x d/dx`.  Thus the first ultraviolet-finite curvature of the
one-loop determinant already has no finite algebraic-differential law.

## Source-internal de Sitter realization

Put a scalar Gaussian sector on Euclidean de Sitter space with the ultrametric boundary Hilbert
space as a compact internal sector.  For a homogeneous mass source `x`, its quadratic Hessian is

```text
A_dS(x) tensor I + I tensor epsilon D_p.                   (12)
```

Fix a de Sitter harmonic with eigenvalue `lambda_l`.  Integrating out the internal Gaussian field
gives the mode-resolved determinant

```text
W_l,N(x)
  = (1/2) sum_(n=0)^N rho(n)
      log(lambda_l + x + epsilon p^n).                    (13)
```

Its cutoff-independent mass curvature is exactly

```text
lim_(N->infinity) d^2 W_l,N/dx^2
  = -1/(2 epsilon^2)
      Q_(p,2)((lambda_l+x)/epsilon).                       (14)
```

Affine changes of the independent variable preserve local differential algebraicity in both
directions.  Hence `(14)` is hypertranscendental in `x`.  Unlike the companion ideal-detector
bridge, the ultrametric tower now belongs to the field Hessian and effective action itself.

This is a **mode-resolved** theorem.  The full de Sitter trace also sums over `l` with de Sitter
degeneracies.  That extra sum does not preserve the simple constraint `(5)`, and no
hypertranscendence claim is made here for the full effective action or an in-in cosmological
correlator.

## Bilateral-shell fracture

The shell integral of a translation-invariant field theory on full `Q_p^d` is bilateral rather
than one-sided.  For a radial denominator it has the form

```text
F_m(x) = sum_(j in Z) p^(d j)/(p^(s j)+x)^m,               (15)
```

when the relevant convergence conditions hold.  Reindexing gives strict homogeneity,

```text
F_m(p^s x) = p^(d-sm) F_m(x).                             (16)
```

Equation `(16)` has no finite boundary defect.  It does not imply hypertranscendence and does not
fall under the one-sided germ argument above.  The physical selector in `(5)` is therefore not
discrete scale invariance alone: it is **one-sided shell completion plus the rational defect left
by the compact boundary**.

This fracture prevents the result from being misreported as a theorem that generic `p`-adic loop
integrals are hypertranscendental.

## Anti-theatre and novelty verdict

The ultrametric spectrum, shell multiplicities, one-loop determinant, and the general
`q`-difference hypertranscendence theorem are parent mathematics and physics.  Focused searches
found no paper stating `(5)`, `(11)`, or the mode-resolved de Sitter interpretation `(14)` for
this exact spectrum, but negative search evidence is not a novelty proof.  The derivation is short
once the parent spectrum and difference theorem are combined, so it is classified as a rigorous
source-internal bridge rather than new scientific knowledge.

The result nonetheless closes three real gaps:

1. it moves the ultrametric tower from an external detector into a field-theoretic Hessian;
2. it identifies the first finite quantum susceptibility and its exact scale defect;
3. it proves that strict scale covariance without a boundary defect is not the selector.

The companion no-go `gaussian-influence-wick-kolchin-collapse.md` proves that this source-internal
HT is still spectral/Gaussian rather than interaction-relative HT.

## Lean boundary

The reusable formal target is coefficientwise: define the Taylor series `(10)`, prove `(5)`, and
prove uniqueness from `(9)`.  Analytic convergence, meromorphic poles, the external
Adamczewski--Dreyfus--Hardouin theorem, the determinant interpretation, and de Sitter harmonic
analysis remain paper-level inputs.

That coefficientwise target is now formalized unconditionally in
`../../3-formalized/not_new_scientific_knowledge/ultrametric-resolvent-susceptibility-constraint.md`.
The exact module build and capstone axiom audit pass.

## Primary sources

- A. Huang and C. B. Jepsen, *A glimpse into the Ultrametric spectrum*,
  <https://arxiv.org/abs/2601.03738>.
- D. Ageev, A. Bagrov, and A. Iliasov, *Coleman-Weinberg potential in p-adic field theory*,
  <https://arxiv.org/abs/2004.03014>.
- R.-G. Cai and S. P. Kim, *One-Loop Effective Action and Schwinger Effect in (A)dS*,
  <https://arxiv.org/abs/1407.4569>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin,
  *Hypertranscendence and linear difference equations*,
  <https://arxiv.org/abs/1910.01874>.
