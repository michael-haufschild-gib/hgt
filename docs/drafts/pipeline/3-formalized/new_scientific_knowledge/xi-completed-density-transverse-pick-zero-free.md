# Xi completed-density transverse Pick cone and zero-free damped channel

- **ID:** `xi-completed-density-transverse-pick-zero-free`
- **Stage:** 3-formalized
- **Type:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [UNCONDITIONAL] [RH-FACING]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedDensityTransversePick.lean`
- **Parent:**
  `../../5-failed/xi-completed-density-projective-heteroclinic-barrier.md`

## Statement

Let

```text
rho(t)=4 T''(t),
F(z)=integral_(0,infinity) rho(t) exp(i t z) dt,
E(z)=(z^2+1/4)F(z)-1/4.
```

Corpus already proves `rho>0`, `integral rho=1`, `rho'<0`, and the exact positive completion

```text
G(z)=integral_(0,infinity) (-rho'(t))(1-exp(i t z)) dt=-i z F(z).
```

For every `Im z>0`, the new theorem is

```text
Im(z) |F(z)| <= Im(z F(z)).                         (1)
```

Consequently

```text
E(z) != 0                 for every Im z>0.          (2)
```

No Xi zero-location premise, divisor enumeration, numerical estimate, or computation enters.

## Paper proof

Write `z=x+i y`, `y>0`, and `p=exp(i t z)=a(c+i s)`, where

```text
a=exp(-t y), c=cos(t x), s=sin(t x), d=1-a c.
```

For `t>=0`, convexity of the exponential and `|sin u|<=|u|` give

```text
a t y <= d,
y |a s| <= |x| d.                                   (3)
```

Squaring `(3)` and using

```text
|1-p|^2=d^2+a^2 s^2,
|z|^2=x^2+y^2
```

yields the pointwise transverse cone

```text
|(i/z)(1-p)| <= (1-Re p)/y.                          (4)
```

Integrate `(4)` against `-rho'(t)>0`.  Norm convexity and the completion identity give

```text
|F(z)|=|(i/z)G(z)| <= Re G(z)/y=Im(zF(z))/y,
```

which is `(1)`.

Suppose `E(z)=0`.  Then

```text
(z^2+1/4)F(z)=1/4.                                   (5)
```

If `x!=0`, substituting `(5)` into `(1)` gives

```text
|z^2+1/4| <= 1/4-|z|^2.                              (6)
```

Both sides of `(6)` are nonnegative, while exact algebra gives

```text
|z^2+1/4|^2-(1/4-|z|^2)^2=x^2,                      (7)
```

a contradiction.  If `z=i y`, positivity and unit mass give

```text
0 <= F(i y) <= 1.
```

For `0<y<1/2`, equation `(5)` would require `F(i y)>1`; for `y>=1/2`, its left side is nonpositive.
This proves `(2)`.

## Exact frontier change

Put `E#(z)=(z^2+1/4)F(-z)-1/4` and

```text
H_tau=((1+tau)/2)E+((1-tau)/2)E#.
```

Formalization proves

```text
H_1=E,
H_(-1)=E#,
H_0=2 z^2 XiC.                                       (8)
```

Thus RH is a zero-transport problem from a proved upper-zero-free endpoint `H_1` to the Xi member
`H_0`.  Since `E` never vanishes in the upper half-plane, the projective ratio `E#/E` has no poles
there; the former zero/pole endpoint-separation clause disappears completely.  The regular-chart
hypothesis is also discharged from the formal theorem

```text
E#/E=-1 iff XiC=0
```

throughout the open upper theta strip.

## Hostile checks

1. `(1)` is one-sided.  It cannot be copied to the growing channel `F(-z)`: the sharp symmetry of
   this Fourier transform is `conj(F(conj z))=F(-z)`, not ordinary real-coefficient symmetry.
2. The bilateral cone for `(F(z)+F(-z))/2` would prove RH immediately but is not a consequence of
   monotonicity; it is rejected as circular/unproved.
3. Zero-freeness of `E` does not imply `|E|>|E#|`.  Corpus formally refutes global strict
   Hermite--Biehler gap on the critical half-strip.
4. Interior multiple-root collisions do not destroy total zeros in a holomorphic pencil.  The
   remaining transport obstructions are boundary entry and noncompact escape, not Wronskian
   regularity.

## Novelty audit

Searches against current primary literature found adjacent results on Wronskian criteria and
deformations of Xi, but no statement matching `(1)` for the completed theta-tail density or the
upper-half-plane zero-freeness `(2)` of this exact channel.  Relevant adjacent sources include
Dimitrov--Xu, *Wronskians of Fourier and Laplace transforms* (arXiv:1606.05011), and Suzuki,
*A family of deformations of the Riemann xi-function* (2016).  Priority remains
`[NOVELTY UNVERIFIED]`; no external novelty claim is made.

## Verification

- [x] exact paper proof dependency-closed;
- [x] scratch proof passed with `lake env lean /tmp/hgt_nevanlinna_pencil_scratch.lean`;
- [x] direct module check passed;
- [x] targeted
  `lake build GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityTransversePick`
  passed;
- [x] `#print axioms` on seven capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`;
- [x] source scan has no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration;
- [x] whole-tree `scripts/formal_tools.py lint` passed (large-file warnings only).
