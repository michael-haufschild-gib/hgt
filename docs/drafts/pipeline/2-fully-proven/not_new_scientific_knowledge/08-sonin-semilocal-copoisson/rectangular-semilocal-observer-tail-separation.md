# Rectangular semilocal observer continuity does not supply cofinal tail control

- **ID:** `rectangular-semilocal-observer-tail-separation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / COFINAL NO-GO WITH POSITIVE REDUCTION
- **Scientific status:** `[PAPER-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
  `[PROOF-ARCHITECTURE CORRECTION] [NOT AN RH PROOF]`
- **Parent:**
  `../../1-in-progress/rectangular-semilocal-finite-part-curvature-rh.md`
- **Child no-go:**
  `../needs-audit/semilocal-one-prime-harmonic-moment-defect.md`
- **Statement:** Prime-cutoff rectangular sources stabilize exactly in every fixed coordinate, and
  the rectangular integrated representation is a uniformly bounded trace-class observer.  Neither
  fact controls the moving cofinal tail.  A subpower trace-norm estimate for the compensated
  coherent defect is sufficient and is the exact remaining operator target.

## 1. Exact coordinate stabilization

Fix `L>0`.  Put

```text
A_L(n)=rectangularPrimePolarSourceCoefficient(L,log(n)/2).                 (1)
```

For `X>=2`, define `A_(L,X)(n)` by retaining only prime-power terms whose underlying prime is at
most `X`, while keeping the complete polar term.  The rectangular prime autocorrelation at
aperture `log(n)/2` is a finite von Mangoldt sum over integers `k<=n`.  Hence

```text
n<=X  implies  A_(L,X)(n)=A_L(n).                                         (2)
```

Indeed, if `Lambda(k) != 0`, then `k=p^m` and `p<=k<=n<=X`.  Thus every prime-power term visible
to the `n`-th rectangular observer is already present at cutoff `X`.

Consequently prime-cutoff convergence is eventually exact, not merely pointwise.  Any remaining
difficulty lies entirely in the moving region `n>X` and in interchange with the weighted infinite
negative-energy sum.

## 2. Uniform trace-class observer bound

Work in logarithmic coordinates for any unitary scaling representation `vartheta`.  Let
`g_(L,n)` be the symmetric two-edge rectangular profile and

```text
h_(L,n)=g_(L,n)*g_(L,n)^*.                                                   (3)
```

Each edge has length `L`, so

```text
||g_(L,n)||_1<=2L.                                                         (4)
```

The integrated unitary representation is contractive from `L1` to bounded operators.  Therefore

```text
vartheta(h_(L,n))=vartheta(g_(L,n)) vartheta(g_(L,n))^* >=0,
||vartheta(h_(L,n))||<=4L^2                                                (5)
```

uniformly in `n`.  Trace duality now gives, for every trace-class operator `K`,

```text
|Tr(K vartheta(h_(L,n)))|<=4L^2 ||K||_1.                                  (6)
```

Thus the rectangular observer contributes no aperture growth.  If an independently constructed
compensated defect has the form

```text
kappa_L(n)=Re Tr(K_n vartheta(h_(L,n)))+c_n,                               (7)
```

then

```text
kappa_L(n)^-<=4L^2 ||K_n||_1+c_n^-.                                       (8)
```

In particular, either a uniform bound or the weaker all-epsilon subpower estimate

```text
for every epsilon>0,
||K_n||_1+c_n^- = O_(L,epsilon)(n^(epsilon/4))                             (9)
```

makes the square of the right side summable against `n^(-1-epsilon)`.  Combined with a positive
bulk identity for `A_L(n)`, the existing rectangular negative-energy theorem then proves RH.
The observer inequality is closed; `(9)` for the actual compensated source defect is not.

## 3. Finite positivity cannot imply the tail estimate

Fix `delta>0` and let the cutoff index be `m`.  Define the abstract triangular array

```text
A_m(n)=-n^delta * 1_(n<=m),
B_m(n)= n^delta * 1_(n<=m),
R_m(n)=-2n^delta * 1_(n<=m).                                               (10)
```

Then

```text
A_m=B_m+R_m,
B_m>=0.                                                                   (11)
```

Enlarging `m` adds only positive bulk coordinates; every finite defect has finite Dirichlet
energy at every exponent; and each coordinate stabilizes exactly.  Nevertheless

```text
R_m(n) -> -2n^delta,
sum_n |2n^delta|/n^(1+epsilon)=infinity  for epsilon<=delta.               (12)
```

Therefore finite-level positivity, refinement compatibility, coordinate stabilization, compact or
Schatten membership at each cutoff, and finite-level summability do not imply the required cofinal
tail estimate.  Uniform weighted tightness such as `(9)`, or an equivalent source-relative
compactness theorem, must be proved before limit exchange.

## 4. The actual fixed-scalar Gamma architecture is impossible

The formal theorem `gammaConductorFiniteCapacity_of_quadratic_nonneg` gives a stronger source-side
no-go.  If independently resolved prime channels are coupled to one fixed scalar Gamma conductor
of capacity `B`, positivity forces

```text
B >= sum_(p in F) R_p,
R_p=(9/8)*p*(p-1)^2*(p+1)^4/(p^2+1)^4 >= 9/(512p).                         (13)
```

The right side diverges cofinally.  Nonzero diagonal damping cancels from this Schur cost.  Hence
the architecture

```text
orthogonal positive prime innovations + one fixed scalar Gamma boundary                         (14)
```

is false, not merely incomplete.

The same formal module supplies the positive alternative.  With normalized prime covariance `K`,
`u_p^2=R_p`, `S_F=sum_(p in F)R_p`, and fixed `B>0`, positivity forces

```text
sum_(p!=q) K_(p,q)u_pu_q >= S_F^2/B-S_F.                                  (15)
```

Thus bounded Gamma capacity requires cofinally coherent cross-prime covariance.  The alternatives
are a growing/infinite Gamma channel family, the Gauss-paired place-by-place factorization, a full
non-diagonal covariance, or a principal-relative trace that is not scalarized first.

There is a parallel exact obstruction in the normalized finite-local-factor moment Gram.  Adding
one prime lowers the quadratic value on the test `X`:

```text
delta_p=1/2-m_2(nu_p)
 =(3/2) *
   [sum_(m>=1) r^m phi(m*ell)tanh(m*ell)^2]
   /[1+2 sum_(m>=1) r^m phi(m*ell)]
 =3*sqrt(2)/(2p)+O(p^-2),                                      (15a)
```

where `r=p^(-1/2)`, `ell=log p`, and `phi(t)=(cosh t)^(-1/2)`.  Hence if a channelwise Gram change
is decomposed as

```text
Delta_p=I_p+R_p,  I_p>=0,
```

then testing on the unit vector `sqrt(2)X` forces `||R_p||_1>=2delta_p`; the trace-norm defects
cannot be summed over the primes.  This kills independent one-prime
`positive innovation + summable defect` schemes even before the rectangular observer is applied.
The exact proof, asymptotic, trace-class implication, and full-product positive survivor are recorded
in `semilocal-one-prime-harmonic-moment-defect`.  Only a genuinely joint
sequential/full-product covariance cancellation can survive.

## Consequence for the RH programme

The correct remaining theorem is not generic observer continuity and not pointwise convergence.
It is:

```text
construct the canonical coherent/growing-channel Connes--Sonin defect K_n,
identify its trace pairing with the exact rectangular finite part,
and prove ||K_n||_1 plus the cyclic anomaly has all-epsilon subpower growth.                    (16)
```

The Gamma-damped channel-resolved covariance already supplies a positive finite-level model with
the forced off-diagonal coherence, but its critical von Mangoldt Radon--Nikodym correction is
unbounded and its rectangular tail estimate is open.  Equation `(16)` is therefore a genuine
source theorem, not a restatement of negative energy.

## Lean boundary

The scalar Gamma capacity/coherence law is already formalized in
`formal/GaloisForLFunctions/RHTower/GammaConductorSchurCapacity.lean`.  Equations `(2)` and
`(4)--(9)` are elementary support and trace-duality bridges, but formalizing them without the
actual Connes integrated representation and the compensated defect `K_n` would add only wrappers.
No new Lean file is warranted until the source-defined defect in `(16)` is constructed.
