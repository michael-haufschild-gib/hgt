# Suzuki causal-depth rectangular Carathéodory growth

- **ID:** `suzuki-causal-depth-rectangular-caratheodory-growth`
- **Stage:** 2 — fully proved on paper
- **Type:** THEOREM / FIXED-WIDTH SOURCE RECTANGLE / APERTURE ORDER
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `suzuki-causal-depth-frostman-transfer.md`
- **RH used:** no
- **Computation used:** no

## Frontier and competing conjectures

S63 proves causal valuation fusion creates exact height dependence, but does not control a fixed
observer-aperture rectangle.  The live restricted-Weil Ward route needs finite-width source mass
before FE light splitting.  Exact question is whether the source-selected depth resolvent has an
aperture order uniform in every real height phase.

Three incompatible possibilities were attacked.

1. Undemodulated fused rays have positive rectangular real part.  `[FALSIFIED]`: at a height with
   prime phase `z=-1`, every ray is negative real and the aperture increment points left.
2. Take norm squares before rectangularization.  Rejected as representation: it discards the
   division-free phase needed by the Robin/Weil carrier.
3. Remove exactly the forced half-prime-log phase before rectangularization.  This survives and
   gives the theorem below.

## Source normal form

Fix `h>0`, a prime `p`, and real height `t`.  Put

```text
z=z_p(t)=exp(i t log(p)/2),
c=exp(-log(p)/4),
x(a)=exp(-(h a/2)log(p)),
R(a,t)=suzukiCriticalApertureDepthFusedAtom(h,a,t,p).
```

For `a>0`, one has

```text
0<c<1,   0<x(a)<1,   |z|=1.                              (1)
```

At valuation depth zero, expand the actual cubic aperture innovation.  Since

```text
xiMobiusContinuousApertureDiskNode((h/2)a,p)=x(a),
xiTransversePrimeApertureDiskNode(1,p)=p^(-1),
```

there is an aperture-independent constant

```text
B_p(h)=sqrt(log(p)/p * exp(log(p)/2))
       * (h sqrt(h))^(-1) * [p^(-1)/(1+p^(-1))] > 0       (2)
```

such that the depth-zero endpoint amplitude is

```text
A_p(h,a)=B_p(h)(1-x(a))^2.                               (3)
```

The S63 causal Möbius law has radius

```text
r_p(h,a)=c x(a)^2.                                      (4)
```

Therefore exact phase demodulation gives

```text
conj(z)R(a,t)
 =B_p(h)(1-x(a))^2/(1-c x(a)^2 z).                      (5)
```

No quotient or phase has been selected from Xi data: `z` is the same source phase already
present in every depth atom.

## Uniform radial theorem

For `0<c<1`, `s<=1`, and `0<x<1`, define

```text
H_(c,s)(x)
 =(1-x)^2(1-c x^2 s)/(1-2c x^2 s+c^2 x^4).             (6)
```

The denominator is

```text
(1-cx^2)^2+2cx^2(1-s)>0,                                (7)
```

and `1-cx^2s>0`, so `H_(c,s)(x)>0`.

Set `b=cx^2`, so `0<b<1`.  Direct differentiation gives

```text
H'(x)/H(x)
 =-2/(1-x)+(2b/x) Phi(b,s),                             (8)

Phi(b,s)
 =[s(1+b^2)-2b]/[(1-bs)(1-2bs+b^2)].                   (9)
```

All denominators in `(9)` are positive.  The comparison with the extremal phase `s=1` is exact:

```text
1/(1-b)-Phi(b,s)
 = (1-s)(1+2b-b^2-2b^2s)
   /[(1-b)(1-bs)(1-2bs+b^2)].                          (10)
```

The second numerator factor satisfies

```text
1+2b-b^2-2b^2s
 >=1+2b-3b^2
 =(1-b)(1+3b)>0.                                       (11)
```

Thus `Phi(b,s)<=1/(1-b)`.  Substitute this into `(8)`:

```text
H'(x)/H(x)
 <=-2/(1-x)+2b/[x(1-b)]
 =2(b-x)/[x(1-x)(1-b)]<0,                              (12)
```

because `b=cx^2<x`.  Since `H>0`, `(12)` proves

```text
H_(c,s) is strictly decreasing on (0,1), uniformly in s. (13)
```

This proof includes phases `s=+-1`; more strongly, no lower bound on `s` is needed.  Lean exposed
this half-line extension during formalization, and the paper proof above uses only `s<=1`.

## Source theorem

### `SUZUKI-CAUSAL-DEPTH-RECTANGULAR-CARATHEODORY-GROWTH`

For `h>0`, prime `p`, real `t`, and `0<a<b`,

```text
Re[conj(z_p(t)) R(a,t)]
  < Re[conj(z_p(t)) R(b,t)].                            (14)
```

Indeed, `a -> x(a)` is strictly decreasing because `h log(p)/2>0`.  Equations `(5)--(6)` identify
the two real parts with `B_p(h)H_(c,cos(t log(p)/2))(x(a))`; `(2)` is positive, and `(13)` reverses
the strict order once more.

Equivalently, for every fixed width `L>0`,

```text
0 < Re[conj(z_p(t))(R(a+L,t)-R(a,t))].                 (15)
```

Equation `(15)` is an exact division-free rectangular sign law.  It is stronger than positivity
at central height and different from S63's norm-square profile: it preserves the causal phase and
holds before a Gram square.

## Gamma--Euler boundary pairing is the demodulator

The phase removal in `(15)` is not an auxiliary choice.  Define the positive depth-zero
Gamma--Euler amplitude

```text
G_p=sqrt(log(p)/p * exp(log(p)/2))>0.                    (16)
```

Expanding the corpus definition of the actual unstarred critical boundary coordinate gives

```text
xiGammaEulerHeightBoundaryFeature(-1/2,t,(p,0))
 =G_p conj(z_p(t)).                                      (17)
```

Therefore `(15)` is equivalent to the source-boundary statement

```text
0 < Re[xiGammaEulerHeightBoundaryFeature(-1/2,t,(p,0))
       (R(a+L,t)-R(a,t))].                               (18)
```

Thus source already supplies correct conjugate phase before any Xi-real projection: `(18)` is a
literal Gamma--Euler boundary pairing, not fitted demodulation.  Remaining issue is whether
restricted-Weil/Robin rectangular trace contains this exact bilinear pairing with correct
cross-prime, archimedean, marked-halfgap, and holonomy terms.

## Hostile audit and boundary

- **No RH input:** proof uses only explicit source recursion, prime positivity, and real algebra.
- **No target interpolation:** demodulation is forced by actual depth-zero Gamma--Euler boundary
  coordinate `(17)`.
- **No hidden phase restriction:** inequality `(10)` controls the whole half-line `s<=1`.
- **No uniform Ward conclusion:** `(15)` is one-prime scalar right-half-plane order.  It does not
  prove finite-height Loewner positivity or identify the restricted-Weil trace.
- **Cofinal limitation:** as `a` grows, `x(a)` tends to zero and the demodulated response approaches
  the finite ceiling `B_p(h)`.  Thus fixed-prime increments decay; this theorem cannot by itself
  provide the missing uniform Ward lower bound.
- **Representation lesson:** the aperture rectangle becomes positive only after source-forced
  primewise phase removal.  Any proposed Robin/Weil trace that squares first or keeps the leading
  phase unpaired misses this exact order.

## Frontier delta

The open core is no longer “show causal fused channel has finite-width source increment” or
“invent a phase that makes it positive.”  Actual Gamma--Euler boundary already supplies exact
phase and strict orientation.  Remaining exact question is:

> Prove concrete division-free Robin/Weil rectangular observation contains boundary pairing
> `(18)` as its primewise block before cross-prime sewing; then identify residual Gamma,
> marked-halfgap, and holonomy Schur block and prove Ward defect uniformly lower bounded.

## Collision and novelty audit

Internal corpus contains continuous-aperture Loewner growth of the unfused innovation Gram,
quarter-shift depth recursion, and the S63 Frostman diagonal.  It contains no demodulated causal
fusion rectangle `(14)--(15)`, boundary-paired law `(18)`, or uniform radial law `(10)--(13)`.

Targeted primary-source search checked Suzuki's 2023 screw-line work, the 2023/2025 Hilbert-source
construction, and the 2026 restricted-Weil operator paper, plus exact rational/Poisson-kernel
searches.  No matching source theorem was found.  This is not a complete priority proof; external
novelty remains unverified.

## Gates

- [x] exact source frontier and falsifiers recorded
- [x] undemodulated right-half-plane claim killed by phase `-1`
- [x] uniform radial derivative sign proved
- [x] exact Suzuki source normalization proved
- [x] demodulator identified with actual depth-zero Gamma--Euler boundary coordinate
- [x] hostile proof and circularity audit passed
- [x] formalize exact theorem in Lean; formalization strengthens phase range to `s<=1`
- [ ] identify boundary pairing `(18)` inside concrete Robin/Weil rectangular trace
- [ ] RH
