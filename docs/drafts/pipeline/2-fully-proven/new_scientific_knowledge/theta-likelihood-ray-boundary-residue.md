# Theta-likelihood ray boundary residue and modular completion

- **ID:** `theta-likelihood-ray-boundary-residue`
- **Stage:** 2-fully-proven
- **Type:** `[CANDIDATE NEW SOURCE-SPECIFIC THEOREM] [UNCONDITIONAL] [NO RH CLAIM]`
- **Depends on:** `ThetaCuspLikelihoodSpectralMeasure.lean`,
  `ThetaCuspLikelihoodModularSeam.lean`, `ThetaCuspFinitePrimeSource.lean`
- **Formal target:** `formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodRayBoundaryResidue.lean`

## Statement

Put

```text
g_n=n^2-1,
A_n=exp(-3*g_n/2)*n^4,
R_n=exp(-3*g_n/2)*(3/2)*n^2*g_n,
L(B)=sum_(n>=2) [A_n exp(-B*g_n)+R_n exp(-B*g_n)/B].       (1)
```

This is the already formalized Laplace response of the positive higher-likelihood measure.  Its
ray boundary residue is

```text
R_*=sum_(n>=2) R_n > 0.                                    (2)
```

Then

```text
lim_(B downarrow 0) B*L(B)=R_*.                            (3)
```

The atomic likelihood masses make no contribution to `(3)`; only the Lebesgue-ray sector
survives.  Equivalently, `L` has a positive simple pole at the zero-likelihood boundary.

There is an exact source-level identification before any limiting argument.  Let `x_*` be the
unique real point with

```text
B(x_*)=pi*exp(2*x_*)-3/2=0,
```

and define the positive first-atom desingularizer

```text
C(x)=4*pi*exp(x/2)*exp(2*x)*exp(-pi*exp(2*x)).              (4)
```

For every natural `n`, atom by atom,

```text
thetaCuspSourceTerm(x_*,n)=C(x_*)*R_n.                     (5)
```

The `n=0,1` sides vanish.  Therefore

```text
thetaCuspFullSource(x_*)=C(x_*)*R_*>0.                     (6)
```

For `B(x)>0`, the first atom itself factors as

```text
thetaCuspSourceTerm(x,1)=B(x)*C(x),                        (7)
```

so the existing likelihood factorization becomes

```text
thetaCuspFullSource(x)=C(x)*B(x)*(1+L(B(x))).              (8)
```

Equations `(3)`, `(6)`, and `(8)` show exactly how modular completion crosses the endpoint:
the first-atom zero is cancelled by the positive ray pole.  No finite-mass positive likelihood
carrier can do this, because its Laplace transform has a finite limit at `B=0` and hence
`B*(1+L(B)) -> 0`, contradicting `(6)`.

## Proof

### 1. Atomwise boundary law

Write `y=pi*exp(2*x)`.  Directly from the theta-cusp seed,

```text
thetaCuspSourceTerm(x,n)
 =2*pi*exp(5*x/2)*n^2*(2*y*n^2-3)*exp(-y*n^2).             (9)
```

At `B(x_*)=0`, one has `y=3/2`, and `(9)` becomes

```text
6*pi*exp(5*x_*/2)*n^2*(n^2-1)*exp(-3*n^2/2).              (10)
```

On the other hand, substituting `y=3/2` in `(4)` and multiplying by `R_n` gives exactly `(10)`:

```text
C(x_*)*R_n
 =4*pi*exp(5*x_*/2)*exp(-3/2)
    *exp(-3*(n^2-1)/2)*(3/2)*n^2*(n^2-1)
 =6*pi*exp(5*x_*/2)*n^2*(n^2-1)*exp(-3*n^2/2).
```

This proves `(5)` without exchanging a limit and a series.  Polynomial-Gaussian summability
allows summation over `n`; the first two weights vanish, giving `(6)`.

### 2. Strict positivity

Every `R_n` is nonnegative for `n>=1`, and

```text
R_2=18*exp(-9/2)>0.
```

Gaussian summability proves `(2)` and `R_*>0`.  Since `C(x_*)>0`, `(6)` is strictly positive.

### 3. Laplace residue

For `B>0`, multiply each summand of `(1)` by `B`:

```text
B*[A_n exp(-B*g_n)+R_n exp(-B*g_n)/B]
 =B*A_n exp(-B*g_n)+R_n exp(-B*g_n).                       (11)
```

As `B downarrow 0`, the first term tends to zero and the second tends to `R_n`.  On
`0<B<=1`, both are dominated by the summable sequence `A_n+R_n`; Tannery's theorem yields `(3)`.
This is an exact Abelian boundary theorem, not a numerical asymptotic.

### 4. First-atom zero and finite-mass obstruction

The `n=1` specialization of `(9)` gives `(7)` by ring algebra.  Combining `(7)` with the existing
positive likelihood factorization proves `(8)`.  Now `(3)` gives `(6)` again by continuity.

If a replacement positive carrier `mu` had finite total mass, monotone convergence would give

```text
integral exp(-B*t) dmu(t) -> mu([0,infinity)) < infinity,
```

so multiplication by `B` would force zero at the boundary.  This contradicts the positive value
in `(6)`.  Thus infinite ray mass is load-bearing, not an artifact of the representation.

## Frontier consequence

This closes the attempted channelwise total-positivity/incomplete-Gamma shortcut.  Atomic gaps do
carry strictly oriented Eisenstein mass shells, but they vanish from the renormalized modular
endpoint.  Any proof of the Hedenmalm phase-current domination must retain the continuous ray
sector and its infinite-mass boundary renormalization.  A finite positive channel family, a finite
Hankel packet, or a positive Markov disintegration acting atom by atom cannot cross this seam.

The new live target is precise:

```text
Construct the Fourier/Bezoutian image of the renormalized ray response
    B * integral exp(-B*t) dmu_ray(t)
and prove that its modularly reflected phase current dominates the corrected product-fibre seam.
```

This card does **not** assert that domination or RH.

## Prior-art and novelty audit

- The internal corpus contained the positive atom-plus-ray likelihood measure, its Laplace law,
  strict Hankel hierarchy, and the seam barycenter.  Searches found no ray boundary residue,
  infinite-mass necessity theorem, or atomwise identity `(5)`.
- Haglund and DeFranco use incomplete-Gamma expansions of Xi.  Polson's 2018 GGC paper and June
  2026 incomplete-Gamma/Thorin abstract discuss Gaussian/incomplete-Gamma tiers.  The accessible
  statements do not use this nonlinear likelihood coordinate or identify the atomwise modular
  boundary residue `(5)`.
- The general facts that a constant-density ray has Laplace transform `exp(-Bg)/B` and that finite
  measures have finite zero-temperature limits are classical.  Candidate novelty is their exact
  source-specific assembly: ray coefficient `R_n` equals the desingularized theta atom at the
  likelihood endpoint, and the whole modular completion is forced by the resulting infinite-mass
  residue.

## Gates

- [x] Exact paper proof, including strict positivity and no-go closure
- [x] Internal corpus collision search
- [x] External parent/noncollision search
- [ ] Lean formalization of atomwise law, residue positivity, scaled-response identity, and limit
- [ ] Axiom/lint/index audit
- [ ] Fourier/Bezoutian ray-image theorem; this is the new open core
