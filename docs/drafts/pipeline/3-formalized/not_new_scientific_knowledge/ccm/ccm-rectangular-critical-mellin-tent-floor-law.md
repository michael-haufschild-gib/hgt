# The rectangular RH detector is an adjacent critical-Mellin block imbalance

- **ID:** `ccm-rectangular-critical-mellin-tent-floor-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-EQUIVALENT SOURCE TARGET]`
- **Parents:** the corrected polar--prime critical Mellin defect, the positive digamma
  frame, and fixed-width rectangular Weil completeness

## Statement

Fix `L>0` and `a>=L`.  Put

```text
chi_(a,L)=1_[a-L,a]+1_[-a,-a+L]
```

and let

```text
A(h)=sum_(n<=exp(h)) Lambda(n)n^(-1/2),
R(h)=4sinh(h/2)-A(h).                                    (1)
```

Define the moving tent

```text
T_(a,L)(h)=max(0,L-|h-(2a-L)|).                          (2)
```

Then the rectangular Xi--Weil value has the exact decomposition

```text
Q_Xi(chi_(a,L))
 =Gamma_(a,L)+C_L+2 D_L(a),                              (3)

D_L(a)=integral_[0,2a] T_(a,L)(h)dR(h),                  (4)

C_L=4 integral_[0,L](L-h)dR(h).                          (5)
```

The archimedean digamma term `Gamma_(a,L)` is bounded above and below by constants depending only
on `L`, uniformly for `a>=L`.  Moreover, Stieltjes integration by parts gives

```text
D_L(a)
 =integral_[2a-L,2a] R(h)dh
  -integral_[2a-2L,2a-L] R(h)dh.                         (6)
```

Consequently, on the logarithmic samples `a_n=(log n)/2`, RH is equivalent to eventual lower
boundedness of the single source-defined adjacent-block imbalance

```text
integral_[log n-L,log n] R(h)dh
 -integral_[log n-2L,log n-L] R(h)dh.                    (7)
```

For `L=log m`, the two intervals in `(7)` are the adjacent multiplicative blocks

```text
[n/m,n]       and       [n/m^2,n/m]                     (8)
```

in logarithmic measure.  Thus the multiplicative midpoint curvature of the Xi screw profile is,
on the source side, an equal-scale imbalance of the completed critical Mellin error.

## Proof

### 1. The autocorrelation is a fixed tent plus one moving tent

For `h>=0`, let

```text
C_(a,L)(h)=integral_R chi_(a,L)(x+h)chi_(a,L)(x)dx.
```

The two same-edge overlaps each have length `max(0,L-h)`.  The only positive-lag cross-edge
overlap has centers separated by `2a-L` and therefore has length `(2)`.  Hence

```text
C_(a,L)(h)=2max(0,L-h)+T_(a,L)(h).                       (9)
```

The corrected polar--prime autocorrelation law is

```text
Q_(polar-prime,a)(chi,chi)
 =2 integral_[0,2a] C_(a,L)(h)dR(h).                    (10)
```

Substitution of `(9)` into `(10)` gives `(4)`--`(5)` and the polar--prime part of `(3)`.

### 2. The Gamma term is uniformly bounded

Write the digamma multiplier as

```text
m(xi)=m(0)+r(xi),       r(xi)>=0.                        (11)
```

The nonnegative multiplier `r` defines a translation-invariant positive quadratic form `q_r`.
If `f_L=1_[0,L]`, the two edges of `chi_(a,L)` are translates of `f_L`.  Therefore

```text
0<=q_r(chi_(a,L))<=4q_r(f_L)                             (12)
```

by the quadratic triangle inequality.  Also

```text
||chi_(a,L)||_2^2=2L.                                    (13)
```

The indicator has finite logarithmic-multiplier energy because its Fourier transform is
`O(1/|xi|)`.  Equations `(11)`--`(13)` therefore bound the full Gamma term uniformly:

```text
2Lm(0)<=Gamma_(a,L)<=2Lm(0)+4q_r(f_L).                   (14)
```

This proves the asserted two-sided bound without estimating the moving cross term separately.

### 3. The tent is an adjacent-block difference

The tent `(2)` is supported on `[2a-2L,2a]`, vanishes at both endpoints, has derivative `+1` on
the left half and `-1` on the right half.  Stieltjes integration by parts therefore gives

```text
integral T_(a,L)dR
 =-integral_[2a-2L,2a-L]R(h)dh
   +integral_[2a-L,2a]R(h)dh,
```

which is `(6)`.

### 4. Equivalence with RH

The formal rectangular completeness theorem proves, for every fixed `L>0`,

```text
RH
 iff Q_Xi(chi_((log n)/2,L)) is eventually bounded below. (15)
```

In `(3)`, `C_L` is fixed and `Gamma_((log n)/2,L)` is uniformly bounded above and below by
`(14)`.  Hence the sequence in `(15)` is eventually bounded below if and only if `D_L((log n)/2)`
is eventually bounded below.  Substitution in `(6)` gives `(7)`.  Finally, exponentiating the
endpoints for `L=log m` gives `(8)`.  `QED`

## Positive consequence of the cancellation no-go

The polar main term and the prime main term cancel at the same square-root scale, so separate
positive estimates cannot prove the rectangular floor.  The positive residue is now exact:

```text
completed prime--polar error R
  -> two adjacent equal logarithmic blocks
  -> their signed average imbalance
  -> one finite lower floor
  -> rectangular Weil lower floor
  -> RH.                                                  (16)
```

The source theorem no longer asks for positivity of a full Weil form, a global Gram kernel, or a
pointwise bound for `R`.  It asks for one fixed-scale adjacent-block lower bound.  Any proposed
Gamma covariance, Möbius projection, renewal contraction, theta correlation, or Sonin relative
trace can now be tested against the explicit scalar readout `(7)`.

## Möbius coisometry attack and its positive dual

Let

```text
eta_(c,L)=1_[c,c+L]-1_[c-L,c],       c=2a-L.             (17)
```

Then `(6)` is the Haar-type coefficient `integral R eta_(c,L)`.  In the complementary
floor--Möbius incidence, the boundary branch is `(I-P_d)1=1_[0,log d)`.  Since `eta_(c,L)` has
zero integral,

```text
inner(eta_(c,L),(I-P_d)1)=0
```

unless

```text
c-L<log d<c+L.                                           (18)
```

Thus the rectangular readout removes the non-`L2` constant boundary mode and localizes that branch
to one finite multiplicative shell.  This is the strongest positive statement obtainable from the
old parallelogram/complementary-projection construction without yet proving RH.

The direct coisometry bound nevertheless cannot be passed to the critical derivative.  To recover

```text
partial_omega E_omega(X)|_(0+)=2(psi(X)-X)
```

uniformly for the channels visible below `X=exp(c+L)`, one needs

```text
omega log X ->0.                                         (19)
```

But the normalized squarefree Möbius mass satisfies

```text
2omega log d => Exp(1).
```

Under `(19)`, the fraction of its norm carried by `d<=X` therefore tends to zero.  Hence the finite
shell selected in `(18)` sees asymptotically none of the contractive Möbius source norm in the
regime where the von Mangoldt derivative is valid.

This no-go has a positive dual.  A successful source operator must contain a genuinely cross-scale
synthesis

```text
remote Mobius channels log d asymp 1/omega
  -> near-aperture Haar shell log X=o(1/omega)
  -> critical derivative
  -> adjacent-block floor.                               (20)
```

The transfer must occur before the critical limit and cannot be a bounded compact synthesis,
because every fixed visible channel carries vanishing normalized mass.  The archimedean renewal,
Sonin relative compression, or an equivalent noncompact marked incidence must provide `(20)`.

## Boundary

Equation `(7)` is RH-equivalent, not an unconditional estimate.  Applying absolute values to the
prime error loses the adjacent-block cancellation and leaves an unbounded square-root-scale
remainder.  A valid proof must derive the lower floor from a positive source construction which
retains the polar and prime channels jointly.

## Lean decision

The divisor-side equivalence and screw-coordinate identity are formalized in
`CCMRectangularWeilCompleteness.lean` and `CCMRectangularScrewCurvature.lean`.  The formal tree does
not yet contain the distributional restricted Weil form, Stieltjes autocorrelation identity, or
the digamma form domain for indicators.  Formalizing only the elementary tent algebra would not
certify `(3)`, so no wrapper module is added before that source layer is represented.

## Gates

- [x] exact two-edge autocorrelation computed
- [x] moving prime--polar term isolated as one tent pairing
- [x] Gamma contribution proved uniformly two-sided bounded
- [x] tent pairing converted to adjacent equal-block imbalance
- [x] multiplicative block form identified for `L=log m`
- [x] composed with fixed-width rectangular completeness on paper
- [x] zero-mean Haar readout localized the complementary Möbius branch to one finite shell
- [x] direct Möbius coisometry transfer rejected by the critical mass-escape scale mismatch
- [x] positive cross-scale synthesis obligation isolated
- [ ] construct an unconditional positive source floor for `(7)`
- [ ] formalize the source-side Stieltjes/autocorrelation layer
- [ ] RH

## Lean status

`[FORMALIZED]` — supersedes the "no wrapper module is added" decision recorded above.  The
distributional Weil form and the Stieltjes autocorrelation law remain cited parents (and the
corresponding gate stays open), but the card's own geometric and algebraic steps are reachable and
are now proved.

Module: `formal/GaloisForLFunctions/RHTower/CCMRectangularTentFloor.lean`
(10 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired
into `formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `movingTent`, `movingTent_nonneg`, `movingTent_eq_zero_of_outside`, `movingTent_endpoint_left`,
  `movingTent_endpoint_right`, `movingTent_center` — **equation (2)**: the moving tent is
  nonnegative, supported in `[2a−2L, 2a]`, vanishes at both endpoints, and peaks at `L`.
- `interval_overlap_len` — the exact overlap length of two intervals of common length `L`:
  `max(0, min(u+L,v+L) − max(u,v)) = max(0, L − |u−v|)`.
- `autocorrelation_split` — **equation (9)**: the cross-edge overlap is exactly the moving tent
  (and by the same lemma each same-edge overlap is `max(0, L−|h|)`).
- `adjacent_block_readout` — **equations (6)–(7)**: with `c = 2a − L` the readout is exactly the
  difference of the two *adjacent equal* blocks `[c, c+L]` and `[c−L, c]`.
- `overlapLen`, `haar_overlap_eq_zero` — **equation (18)**: the zero-mean Haar readout is
  orthogonal to the boundary indicator `1_{[0,T)}` whenever `T ≤ c−L` or `T ≥ c+L`, i.e. the
  complementary Möbius branch is localized to the finite multiplicative shell.
- `quadratic_two_translate_bound` — **equation (12)**: a positive quadratic form on a sum of two
  equal-energy translates is at most four times its value on one of them, which is the uniform
  two-sided Gamma bound `(14)`.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the distributional restricted Weil form and the Stieltjes autocorrelation law `(10)`;
- the digamma form domain for indicators and the finiteness of their logarithmic-multiplier energy;
- the fixed-width rectangular completeness theorem `(15)`;
- the Möbius mass-escape scale analysis `(19)`–`(20)`.
