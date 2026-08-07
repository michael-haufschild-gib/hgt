# Suzuki coherent response has vanishing cofinal gain on the sharp wall source

- **ID:** `suzuki-coherent-response-gain-no-go`
- **Stage:** 1 — paper proof complete; Lean formalization complete
- **Type:** SOURCE-SPECIFIC NO-GO / SHARP BOUNDARY LAW
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:**
  `../3-formalized/new_scientific_knowledge/suzuki/suzuki-coherent-causal-depth-fusion.md`,
  `../2-fully-proven/new_scientific_knowledge/suzuki-rectangular-wall-gram-gate.md`
- **Attacks:** `suzuki-coherent-fusion-gamma-weld.md`
- **RH used:** no
- **Computation used:** no

## Theorem

Fix `h>0`. Let `B_p` be the observer-free depth-zero critical wall amplitude and let

```text
R_(a,t,p)=suzukiCriticalApertureDepthFusedAtom(h,a,t,p)
```

be the actual causal valuation-depth fused response. Put

```text
r_* = exp(-(1/4)log 2) < 1,
C_h = (h sqrt(h))^(-1) (1-r_*)^(-1).
```

For every `a>0`, every real height `t`, and every prime `p`,

```text
|R_(a,t,p)| <= C_h B_p/(p+1).                              (1)
```

Now take unit rectangular width and the prime-dependent moving-wall aperture

```text
a_p=(log p+1)/2.
```

For every prime `p>=3`, the exact sharp wall gate at the depth-zero lag is one:

```text
rectangularTwoEdgeAutocorrelation(1,a_p,log p)=1.           (2)
```

Consequently the sharp wall source norm at this cell is exactly `B_p`, whereas its causal fused
response satisfies `(1)`. Hence the cofinal source-to-response gain vanishes:

```text
|R_(a_p,t,p)|/B_p <= C_h/(p+1) -> 0.                       (3)
```

Equivalently, for every proposed finite inverse gain `M`, some prime satisfies

```text
B_p > M |R_(a_p,t,p)|.                                    (4)
```

At quadratic level, recovering the sharp diagonal from response energy requires amplification at
least `(p+1)^2/C_h^2` on these moving-wall cells.

## Proof

The source already proves the exact factorization

```text
EndpointAmplitude(h,a,p,0)
  =B_p * CubicInnovation(h,a,p,0).                         (5)
```

At depth zero, the innovation is

```text
(h sqrt(h))^(-1)
  * [p^(-1)/(1+p^(-1))]
  * (1-p^(-ha/2))^2.                                      (6)
```

The middle factor is exactly `1/(p+1)` and the last factor lies in `(0,1)`. Therefore

```text
EndpointAmplitude(h,a,p,0)
  <=(h sqrt(h))^(-1) B_p/(p+1).                            (7)
```

The exact causal Möbius law is

```text
R_(a,t,p)=EndpointAmplitude * z/(1-rz),
|z|=1, 0<r<=r_*<1.                                        (8)
```

Reverse triangle inequality gives `|1-rz|>=1-r_*`; combining `(7)` and `(8)` proves `(1)`.

For `(2)`, the four-tent formula has centers `0`, `2a_p-1=log p`, and `-(2a_p-1)=-log p`.
At lag `log p`, the moving tent equals one. For `p>=3`, `log p>1`, so both other tents vanish.
The exact wall diagonal theorem and `B_p^2=Lambda(p)/sqrt(p)` then identify the sharp source norm
with `B_p`.

Since primes are unbounded, `(1)` implies `(3)` and `(4)`.

## Consequence for the active Suzuki conjecture

The coherent causal field is a legitimate all-prime response, but it is not a uniformly
frame-equivalent image of the exact sharp wall source. Any Robin--Gamma trace weld recovering the
sharp rectangular diagonal from this field must contain an unbounded, cutoff-dependent inverse
weight. A bounded restricted-Weil response followed by a bounded trace functional cannot perform
the identification.

This does not kill Suzuki's full operator mechanism. It kills the bounded-gain interpretation of
`SUZUKI-COHERENT-FUSION-GAMMA-WELD` and sharpens its surviving form:

```text
construct a closed unbounded relative observation whose graph absorbs the forced p-growth,
then prove its completed rectangular finite part has a cutoff-uniform lower floor.
```

That graph estimate—not coherent covariance existence—is the first unresolved source theorem.

## Falsifiers and scope

- A bounded inverse or a uniform lower frame bound contradicts `(4)`.
- Cross-prime covariance does not alter the one-cell gain law; it may only support an unbounded
  collective reconstruction.
- No claim is made that every unbounded reconstruction fails.
- No completed lower floor, RH, RH disproof, or full Suzuki no-go is claimed.

## Gates

- [x] existing source formulas audited
- [x] exact paper proof
- [x] formalize `(1)` and `(2)` in Lean
- [x] formalize cofinal no-uniform-inverse theorem `(4)`
- [ ] decide closability and graph norm of the forced unbounded reconstruction
- [ ] prove or refute completed lower floor
- [ ] RH / disproof / full Suzuki no-go
