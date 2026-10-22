# Dyadic-prime Dirichlet high-line sign rigidity

- **ID:** `dyadic-prime-dirichlet-high-line-sign-rigidity`
- **Stage:** `3-formalized`
- **Type:** `[BRIDGE] [NO-GO] [POSITIVE CLASSIFICATION]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Route:** Route I, sharp dyadic prime window
- **Formalized companion:** `dyadic-prime-dirichlet-high-line-sign-rigidity-formalized.md`
- **Lean targets:**
  `GaloisForLFunctions.HTGeometry.DirichletHalfPlaneSignRigidity`,
  `GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowPassiveNoGo`

## Theorem

Let

```text
D(s)=sum_(n>=1) a_n n^(-s)
```

have real coefficients and finite absolute-convergence abscissa.  Suppose `m>=2` is the first
nonzero coefficient after the constant term.  For a real phase `t`,

```text
m^sigma (D(sigma-it)-a_1) -> a_m exp(i t log m),
m^sigma (D(sigma+it)-a_1) -> a_m exp(-i t log m).
```

If `a_m sin(t log m) != 0`, the imaginary parts on the two conjugate high lines eventually have
opposite strict signs.  Consequently the raw impedance-coordinate function

```text
z |-> D(1-i z)
```

cannot map any upper tail `{Im z>Y}` into either closed half-plane.  A real ordinary Dirichlet
series with a raw-coordinate scalar Herglotz or anti-Herglotz response on an upper tail must have no
nonconstant coefficient.

For Route I,

```text
S(n)=4(1-1/sqrt(2))*sqrt(n)
     -2*sum_(n/2<k<=n) Lambda(k)/sqrt(k),
F(s)=sum S(n)n^(-s)
```

on `Re s>3/2`.  Its first oscillatory coefficient is

```text
S(2)=4(sqrt(2)-1)-sqrt(2)log(2)>0.
```

Taking `t=1` gives, for all sufficiently large `sigma`,

```text
Im F(sigma-i)>0,
Im F(sigma+i)<0.
```

Thus `Z(z)=F(1-i z)` takes both signs above every prescribed upper-half-plane height and is neither
Herglotz nor anti-Herglotz on any upper tail.

## Proof

Twist coefficients by `n^(it)`, delete the prefix through `m-1`, and apply the ordinary Dirichlet
first-coefficient asymptotic.  The positive real normalization `m^sigma` does not change the sign.
The deleted prefix contributes only the real constant `a_1`; all indices `2,...,m-1` vanish.  The
conjugate twist gives the opposite sign.

For the dyadic source, the window at `2` contains only the prime `2`, so
`W(2)=log(2)/sqrt(2)`.  The displayed formula for `S(2)` follows.  Since `log 2<1` and
`3sqrt(2)>4`,

```text
S(2)>4(sqrt(2)-1)-sqrt(2)=3sqrt(2)-4>0.
```

Also `0<log 2<pi`, hence `sin(log 2)>0`.  Initial-half-plane equality between the ordinary series
and `dyadicSharpPrimeContinuedSource` transfers the two strict signs to the literal Route-I source.
The coordinate identities

```text
1-i( 1+i(sigma-1))=sigma-i,
1-i(-1+i(sigma-1))=sigma+i
```

put both witnesses arbitrarily high in the same upper half-plane.

## Novelty and anti-theatre audit

Samaris, *Dirichlet series with positive real part*, Bull. Aust. Math. Soc. 46 (1992), 159--166,
DOI `10.1017/S000497270001176X`, supplies parent theory for positive-real generalized Dirichlet
series.  First-coefficient extraction is classical Dirichlet-series rigidity.  This theorem is
therefore a `[BRIDGE]`, not publication-level new science.

Project-level knowledge is real and terminal: the no-go attacks the final scalar response value,
so arbitrary internal coupling, Schur complementation, nonlinear finite cells, and passive
normal-family exhaustion cannot rescue equality with `F` on the source overlap.  This is stronger
than the earlier atomwise raw-delay no-go.

Bellotti, arXiv:`2508.02041`, does not independently prove the Route-I source endpoint: the current
Korobov--Vinogradov PNT error becomes a square-root-weighted error of size `n^(1/2-o(1))`, not an
all-epsilon `n^epsilon` bound.

## Positive survivor

Exact classification: any future passive-network attack must first replace `F` by a nontrivial
Cayley or renormalized transform.  It must then prove a source-only inverse handoff recovering
holomorphy of `F`; otherwise it is a passive realization of a different function.  That is a new
route, not unfinished Route I infrastructure.

## Gates

- [x] dependency-closed paper proof
- [x] arbitrary first surviving Dirichlet mode treated
- [x] exact dyadic coefficient and phase sign treated
- [x] Herglotz and anti-Herglotz orientations both excluded above every height
- [x] external prior-art and current-PNT audit
- [x] positive survivor extracted
- [x] exact unconditional Lean formalization
- [x] phase selected for every nonzero first surviving real coefficient
- [x] direct source checks and focused final Route-I build
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`

## Lean closure

`realLSeriesRawImpedance_not_fixedSign_of_firstNonzero` proves the generic terminal claim for
every first nonzero real coefficient after the constant term, at every specified height.  Its
phase witness is constructed by
`exists_opposite_imaginary_phase_of_ne_zero`; the two quarter-turn lemmas prove the required
signs without any analytic or zero hypothesis.  The Route-I specialization then proves the
literal dyadic source has positive and negative raw-impedance witnesses above every height.

The formal certificate is `dyadic-prime-dirichlet-high-line-sign-rigidity-formalized.md`.
