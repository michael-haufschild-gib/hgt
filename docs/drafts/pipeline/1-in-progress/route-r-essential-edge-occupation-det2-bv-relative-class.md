# Route R essential-edge occupation `det2` / BV relative class

- **ID:** `route-r-essential-edge-occupation-det2-bv-relative-class`
- **Stage:** 1 — in progress
- **Type:** SOURCE-DERIVED OPERATOR REALIZATION / RELATIVE SPECTRAL-ZETA CLASS
- **Status:** `[PAPER-PROVED CORE] [PRIMARY SOURCE MAP] [ANNIHILATION OPEN] [NOT RH]`
- **Parent:**
  `../3-formalized/new_scientific_knowledge/route-r-prime-essential-edge-schatten-threshold.md`

## Frontier correction

Directly flattening every coordinate of the strict-preclosure edge is not canonical action
condensation.  It retains the auxiliary Bertrand prime in the spectrum and cannot have the
reciprocal-positive-integer Wold--Gamma moments.  The source edge nevertheless contains the
canonical inverse-prime nome by an exact two-coordinate cancellation.

For an ordinary prime `p`, put `r_p = farPrime(p)` and let

```text
a_p = log(p) * primeHardyKernelMap(w_(p,r_p)) - e_1.
```

Freeze the source contraction

```text
epsilon_p(x) = x(2) - x(1) / r_p,
q_p = epsilon_p(a_p).
```

The candidate source-derived occupation spectrum is indexed by finite prime occupations
`nu : Primes ->_0 Nat`:

```text
q(nu) = product_p q_p^(nu_p),
N(nu) = product_p p^(nu_p),
Q_edge e_nu = q(nu) e_nu.
```

This primitive is risky: one wrong coordinate, sign, or normalization destroys the ordinary
integer spectrum.

## Frozen claims

`[CONJECTURE: ESSENTIAL_EDGE_EXACT_NOME_EXTRACTION]`

For every ordinary prime,

```text
a_p(1) = -p / r_p,
a_p(2) = 1/p - p/r_p^2,
q_p = a_p(2) - a_p(1)/r_p = 1/p.
```

`[CONJECTURE: ESSENTIAL_EDGE_OCCUPATION_DIAGONAL]`

Unique factorization gives `q(nu)=1/N(nu)`.  Hence `Q_edge` is Hilbert--Schmidt and not trace
class, and under the occupation/positive-integer equivalence it is exactly

```text
Q e_n = n^(-1) e_n.
```

On the Hilbert--Schmidt disk its regularized determinant is the genus-one occupation product:

```text
det2(I - t Q_edge)
  = product_(n>=1) (1 - t/n) exp(t/n)
  = exp(gamma t) / Gamma(1-t).
```

Its polarized ratio is the regular Wold--Gamma phase.

`[CONJECTURE: WOLD_SPECTRAL_ZETA_RELATIVE_CLASS]`

For a prime `p`, let `E_p` delete occupation modes whose represented integer is divisible by
`p`.  The single relative spectral-zeta character

```text
Z_p(s) = sum_(p does not divide n) n^(-s)
       = (1 - p^(-s)) zeta(s)
```

has both required boundary readings:

```text
regular grade k >= 2:
  Tr((E_p Q_edge)^k) = Z_p(k),
  log det2 coefficients = -Z_p(k)/k;

singular grade 1:
  Res_(s=1) Z_p(s) = 1 - p^(-1),
```

and the last coefficient is exactly the formalized adjacent Wold boundary mass and BV
off-multiple first-trace residue.  Thus regular Gamma anomaly and singular BV trace are different
grades of one relative spectral-zeta class, not numerically identical functionals.

`[CONJECTURE: SOURCE_RELATIVE_BOUNDARY_ANNIHILATION]`

There is a pre-specialization chain map from the strict source Bockstein totalization carrying
the class above to the existing arithmetic source-to-Xi/Green comparison, and its mixed boundary
annihilates the completed horizontal Green defect.  This claim is RH-strength.  It is not a
consequence of the scalar determinant or of the spectral-zeta identities alone.

## Dependency-closed paper proof of the unconditional core

The witness identity gives

```text
a_p = p * (primeHardyTail(p) - primeHardyTail(r_p)) - e_1.
```

The first Hardy-tail coordinate at a prime `q` is `q^(-1)`, and the second is `q^(-2)`.
Therefore

```text
a_p(1) = p * (p^(-1) - r_p^(-1)) - 1 = -p/r_p,
a_p(2) = p * (p^(-2) - r_p^(-2)) = 1/p - p/r_p^2.
```

Consequently the source-fixed two-coordinate contraction cancels the auxiliary prime exactly:

```text
epsilon_p(a_p)
  = (1/p - p/r_p^2) - (-p/r_p)/r_p
  = 1/p.
```

This is an equality at every prime, not an asymptotic extraction.

For a finite occupation `nu`, multiplicativity now gives

```text
q(nu) = product_p p^(-nu_p) = N(nu)^(-1).
```

Unique factorization identifies finite prime occupations bijectively with positive integers, so
the diagonal spectrum is exactly `{1/n : n >= 1}`.  Its squared norm sum is
`sum_(n>=1)n^(-2)`, hence finite, while its absolute trace is the harmonic series, hence divergent.
This proves that `Q_edge` is Hilbert--Schmidt and not trace class.

For `|t| * ||Q_edge||_2 < 1`, the diagonal Hilbert--Carleman product formula gives

```text
det2(I-t Q_edge)
 = product_(n>=1) (1-t/n) exp(t/n).
```

The already proved Gamma Weierstrass identity turns this into
`exp(gamma t)/Gamma(1-t)`.  Dividing its values at `t` and `-t` gives the exact polarized
Wold--Gamma phase.  Equivalently,

```text
log Phi_p(t)
 = -2 * sum_(j>=1) Z_p(2j+1) * t^(2j+1)/(2j+1),
```

where the prime Wold projection deletes exactly integers divisible by `p`.

For `Re(s)>1`, separate the Dirichlet series into multiples and nonmultiples of `p`:

```text
sum_(p|n) n^(-s)
  = sum_(m>=1) (pm)^(-s)
  = p^(-s) zeta(s).
```

Absolute convergence justifies subtraction, proving
`Z_p(s)=(1-p^(-s))zeta(s)`.  Therefore every integer `k>=2` is the trace moment
`Tr((E_pQ_edge)^k)=Z_p(k)` and supplies the corresponding `det2` coefficient.  Since zeta has
residue one at `s=1` and `1-p^(-s)` is holomorphic there,

```text
Res_(s=1) Z_p(s) = 1-p^(-1).
```

The finite cutoff identity

```text
sum_(n<=N, p does not divide n) 1/n
  = H_N - p^(-1) H_floor(N/p)
```

has logarithmic coefficient `1-p^(-1)` and finite part
`(1-p^(-1))*gamma + p^(-1)*log p`.  The formalized adjacent BV decimation theorem identifies
the same `1-p^(-1)` with its off-multiple residue and Wold boundary mass.  Thus the regular
`det2` moments and singular BV first trace are rigorously two grades of the same source-derived
spectral-zeta class.

No step in this proof constructs the mixed source-to-Xi boundary.  Moreover scalar `det2` is
nonzero and completed Gamma admission is conservative on Green provenance, so horizontal
annihilation cannot be appended to this proof without a new, nonseparable chain-level term.

## Audit boundary

Exact corpus search found no previous theorem recovering `1/p` from the first two coordinates of
the literal essential edge.  The occupation/Gamma and adjacent Wold--BV target identities already
exist separately; the source contraction connecting them is new internal content.

Primary-literature audit found the standard Hilbert--Schmidt product law
`det2((I-A)(I-B)) = det2(I-A) det2(I-B) exp(-Tr(AB))` and standard singular-trace/residue
machinery, but no source-specific essential-edge extraction or Xi annihilation theorem.  This
keeps novelty restricted to the exact source map and its corpus weld; it does not label parent
determinant or residue theory new.

## Hostile falsifiers

1. Kill exact nome extraction if the first coordinate is not `-p/r_p` or the displayed
   contraction is not source-fixed.
2. Kill the Gamma identification if action condensation does not enumerate every positive integer
   exactly once.
3. Kill the relative-class statement if regular moments and the BV coefficient require different
   local deletion operators.
4. Do not call the singular trace a bounded functional on the Hilbert--Schmidt ideal.  No
   continuous extension of the finite diagonal trace from `ell1` to `ell2` exists.
5. Do not derive Xi annihilation from `det2`: the current formal Fredholm determinant is an
   exponential and is everywhere nonzero; the updated Hellinger--Hodge Green theorem also makes
   Gamma admission conservative on the Green sector.
6. If no source-defined mixed differential produces an opposite term in the same completed grade,
   label annihilation open rather than declaring the diagonal realization an RH proof.

## Novelty target

Prime occupation products, regularized determinants, spectral zeta functions, and Wold
decomposition are parent mathematics.  Candidate corpus-new content is the exact recovery of the
canonical inverse-prime nome from the literal two coordinates of the strict-preclosure essential
edge, followed by its use as the source map into the already isolated Wold--Gamma/BV relative
class.  The RH-bearing mixed boundary remains a separate claim.

## Gates

- [x] competing direct-flattening and occupation-condensation realizations separated
- [x] exact claims and falsifiers frozen before proof
- [x] internal collision audit
- [x] targeted primary-literature audit
- [x] exact nome extraction paper-proof
- [x] diagonal Hilbert--Schmidt realization paper-proof
- [x] `det2` / Gamma operator identity paper-proof
- [x] regular Wold moments / singular BV residue weld paper-proof
- [ ] source-to-Xi mixed boundary constructed
- [ ] arithmetic annihilation proved
- [ ] Lean formalization of dependency-closed unconditional claims
