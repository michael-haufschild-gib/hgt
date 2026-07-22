# Sharp Pólya-frequency order of the de Bruijn--Newman kernel

- **ID:** `debruijn-newman-sharp-polya-frequency-order-four`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / CANDIDATE THEOREM
- **Source:** Michałowski, arXiv:2602.20313v2, Problem 1
- **Statement:** The de Bruijn--Newman kernel `K(u) = Φ(|u|)` is strictly totally positive through order four; combined with the certified order-five counterexample, its exact Pólya-frequency order is four.
- **Scientific status:** `[CONJECTURE] [PF3 PAPER-PROVED] [PF4 SEAM PAPER-PROVED] [OPEN GLOBAL J4] [NOVELTY UNVERIFIED] [NO NUMERICAL EVIDENCE]`

## Goal

Resolve the published global `PF4` problem for the de Bruijn--Newman kernel.  This is outside the
Suzuki and Connes--Consani--Moscovici lanes.  The result would classify the exact finite total-
positivity order of the canonical Riemann--Jacobi kernel; it does not by itself prove RH.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, formal lint PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + novelty audit)

## Normalization

The formal source satisfies

```text
thetaCuspFullSource(2u) = 2 Φ(u).
```

Positive rescaling of the argument and value preserves every finite Pólya-frequency order, so the
problem is equivalent for `f = thetaCuspFullSource`.

## Attack

For a smooth translation kernel `T_f(x,y)=f(x-y)`, define the signed confluent Hankel jets

```text
J_m(t) = (-1)^(m(m-1)/2) det [ f^(i+j)(t) ]_(0<=i,j<m).
```

Karlin's extended-total-positivity theorem reduces strict `TP4` to `J_m(t)>0` for
`m=1,2,3,4` and every real `t`.  Reflection reduces to `t>=0`.

This implication is not an assumed local-to-global principle.  Karlin's definition of `ETP_r`
is exactly positivity of the fully coalesced determinant in both variables; his derivative
extension theorem gives `ETP_r => STP_r`.  Applied to `f(x-y)`, its fully coalesced determinant
is `J_m(x-y)`.  Thus the four scalar jet signs are sufficient for every nonconfluent admissible
configuration, not only for equally spaced Toeplitz minors.

The equal-spacing Toeplitz coefficient has the exact confluent form

```text
lim_(h→0) det[f(t+(i-j)h)] / h^(m(m-1))
  = J_m(t).
```

Here the two Vandermonde factors `Delta(0,...,m-1)` exactly cancel the two Taylor-factorial
products.  In particular the coefficient depends only on derivatives through order `2m-2`.  For
`m=5`, all apparent Taylor terms of orders
`9,...,14` in the uncollected Leibniz expansion cancel.  This corrects the nonminimal derivative
wall stated in Remark 3.3 and Section 5.1 of arXiv:2602.20313v2; the confluence identity itself is
classical and is not claimed as new science.

Existing corpus input:

- `thetaCuspFullSource_pos_all` gives `J_1>0`.
- `thetaCuspLogConcavityNumerator_neg_all` gives `J_2>0`.
- `thetaCuspLogSource_fourthTuran_gt_one_hundred_sixty` and the source derivative hierarchy are
  candidate inputs for `J_3`.
- Sixth logarithmic/source jets are available, but no theorem currently signs the full `J_4`.

## Universal three-curvature law `[BRIDGE]`

Let `f>0` be `C^6`, put `ell=log f`, and define

```text
q = -ell'',
r = 2q - (log q)'',
s = 2r - q - (log r)''.
```

Whenever the displayed logarithms are defined, the Desnanot--Jacobi/Toda identity gives the exact
factorization

```text
J_1 = f,
J_2 = f^2 q,
J_3 = f^3 q^2 r,
J_4 = f^4 q^3 r^2 s.                                  (1)
```

Indeed the signed Hankel jets obey

```text
J_(m+1) = -(J_m^2/J_(m-1)) (log J_m)'',
```

and `(1)` follows successively for `m=1,2,3`.  Consequently a positive smooth translation kernel
is `ETP_4`, hence `STP_4`, once `q,r,s` are positive everywhere.  The Toda identity and Karlin
extension are classical.  The compact curvature cascade is recorded as a reusable bridge, not as
the publication-level novelty claim.

## Global order-three theorem `[PAPER-PROVED]`

On `x>=0` write the complete source as `f=f_1 exp(epsilon)`, where `f_1` is its first theta atom.
Put

```text
d = 2*pi*exp(2x)-3 > 3,
Q = -(log f_1)'' = 2(d+3)(d^2+6)/d^2,
V = (log f_1)'''' = (d+3)(8+48/d^2+864/d^3+2592/d^4).
```

The exact atom inequalities are

```text
Q >= 19,                 V < (3/2) Q^2.                (2)
```

For the second inequality, after clearing the positive denominator the gap is

```text
6d^5+10d^4+72d^3+168d^2-648d-1944
 = 1836+5814y+2976y^2+732y^3+100y^4+6y^5,
y=d-3>0.
```

Existing exact tail estimates give, for `x>0`,

```text
epsilon'' < 13/10,       epsilon'''' > -17.             (3)
```

At a fixed point multiply `f` by an exponential gauge so that `ell'=0`; this does not change any
`J_m`.  With `a=ell''`, `b=ell'''`, and `c=ell''''`, direct expansion gives

```text
det[f^(i+j)]_(0<=i,j<3) / f^3 = a*c+2a^3-b^2.          (4)
```

Set `p=Q-epsilon''=-a`.  Equations `(2)`--`(4)` imply

```text
det_3/f^3
 < p(V+17-2p^2)
 < p((3/2)Q^2+17-2(Q-13/10)^2) < 0,
```

because, for `Q>=19`,

```text
2(Q-13/10)^2-(3/2)Q^2-17
 = Q^2/2-(26/5)Q-681/50 > 0.
```

The order-three sign convention is `J_3=-det_3`, hence `J_3(x)>0` for every `x>0`.
The seam value `x=0` is strict by the exact modular calculation below, and evenness covers the
negative half-line.  Thus the de Bruijn--Newman kernel is unconditionally strict `PF3`; no
sampling, interval arithmetic, or zero information enters.

For reference, the first atom itself has the stronger exact cascade

```text
R = 4d(d+3)(d^3+18d-24)/(d^2+6)^2 > 18,
S = 6(d+3)(1+6C/(d^3+18d-24)^2) > 36,
C = d^2(d-4)^2+8d^2+48d+156 > 0.
```

These are its `r` and `s` from `(1)`.

## Exact modular seam at order four `[PAPER-PROVED]`

Let

```text
H(x)=exp(x/2) theta_3(i exp(2x)),
M=H(0), R_0=pi*M^4, X=R_0^2.
```

The self-dual modular differential system already derived in the corpus yields, for
`f=thetaCuspFullSource=(H''-H/4)/2`,

```text
f_0 = M (X-6)/16,
f_2 = -M (X^2+90X-120)/128,
f_4 = M (51X^3+382X^2+14400X-9120)/1024,
f_6 = M (849X^4-51510X^3-173464X^2-3785760X+1418880)/8192.   (5)
```

The first three formulas follow by differentiating the autonomous system through order five.  The
last is equivalently obtained from its dependency-closed sixth-seam identity

```text
f_0^2 f_6-15f_0f_2f_4+30f_2^3 = M^3 Q_6(X)/131072,
Q_6(X)=99X^6+12X^5-3160X^4-544272X^3
       -1446144X^2-1509120X+276480.
```

Besides the existing lower bound `X>191/10`, the theta series gives `X<20`: if
`q_0=exp(-pi)`, the exponential Taylor lower bound gives `q_0<11/250`, whence

```text
M = 1+2 sum_(n>=1) q_0^(n^2)
  < 1+2(q_0+q_0^4/(1-q_0^3)) < 109/100,
X = pi^2 M^8 < 10(109/100)^8 < 20.                    (6)
```

At an even seam the fourth signed Hankel determinant factors as

```text
J_4(0)=(f_0 f_4-f_2^2)(f_2 f_6-f_4^2).               (7)
```

Using `(5)`, the first factor is `M^2/16384` times

```text
A(X)=50X^4-104X^3+4248X^2-73920X+40320 > 0           (8)
```

for `X>=19`; group `(8)` as
`X^3(50X-104)+X(4248X-73920)+40320`.
The second factor is `M^2/1048576` times

```text
B(X)=-3450X^6-63864X^5+3296520X^4+3144960X^3
     +118091520X^2-319334400X+87091200.               (9)
```

For `19<=X<20`, group `(9)` as

```text
X^4(3296520-63864X-3450X^2)
 +3144960X^3+X(118091520X-319334400)+87091200,
```

whose four summands are positive.  Therefore `J_4(0)>0`.  Equations `(7)`--`(8)` also give the
strict seam value needed above for `J_3(0)=-f_2(f_0f_4-f_2^2)>0`.

## Open core

`[OPEN CORE]` Prove globally, without computation,

```text
J_4(t) > 0  for every t>0.
```

The seam and all lower orders are closed.  The genuine frontier is now the positive-half `J_4`:
after exponential-gauge normalization it is one explicit differential polynomial in `(log f)''`
through `(log f)^(6)`.  The live attack is a sixth-order extension of the exact first-atom/tail
likelihood domination used above.  No Toeplitz sampling, RH assumption, zero simplicity, or
interval arithmetic may enter.

## Significance gate

- A proof resolves Michałowski's named Problem 1 and, with the published `PF5` failure, gives the
  sharp order `PF4 \ PF5`.
- A proof of only the confluence formula is `[REDISCOVERED]`, not publication significance.
- A proof only for equal-spaced Toeplitz minors is insufficient: global admissible configurations
  are required.
- If `J_4` is negative anywhere, the same route instead gives an analytic `PF4` counterexample and
  still resolves Problem 1.

## Literature audit

- I. J. Schoenberg, finite-order Pólya-frequency and zero-location theory (1955).
- S. Karlin, extended total positivity and confluent derivative criteria (1964; 1968 monograph).
- A. Khare, characterization of `TN_p` functions by largest minors under decay
  (arXiv:2008.05121v2, Theorem E).
- W. Michałowski, certified `PF5` failure and open global `PF4` problem
  (arXiv:2602.20313v2, Problem 1).

## Log

- 2026-07-22 — Created after corpus/literature audit.  Identified exact confluent-Hankel reduction,
  corrected order-eight rather than order-fourteen derivative wall for `C5`, and isolated global
  `J_4` positivity as the noncomputational frontier.
- 2026-07-22 — Proved global strict `PF3` on paper by first-atom/tail domination.  Derived the
  universal three-curvature factorization and exact first-atom `q,r,s` laws.  Closed `J_4(0)>0`
  symbolically through the self-dual modular system and the exact chamber `191/10<X<20`.  Only
  `J_4(x)>0` for `x>0` remains.
