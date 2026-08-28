# HB source-FE real-cocycle and reflection-orbit extinction

- **ID:** HC53
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE RIGIDITY / CROSS-FIBRE NO-GO
- **Source:** HC52 arbitrary-kernel Ward classification; literal BM unit-source cocycle; reflected
  mixed-copy producer loophole
- **Statement:** Prove literal BM source cocycle is real exactly on critical line, then show every
  reflection-real Ward kernel vanishes on complete tilted reflection-orbit blocks.

## Corpus-led gap

HC52 proves a reflection-real Ward kernel has zero diagonal on a tilted Xi fibre. It does not
control the physically important mixed-copy entry `K(q,Rq)`. This leaves a precise loophole:
Hedenmalm/HB source analyses require mixed-copy terms, so a pure reflected-orbit pairing might
still evade diagonal rigidity.

Write `R` for Xi reflection and `kappa` for literal unit BM source FE cocycle. For a
reflection-real Ward kernel, nonzero `K(q,Rq)` forces

```text
kappa(q) kappa(Rq) = 1.
```

Cocycle involutivity independently gives

```text
kappa(Rq) conj(kappa(q)) = 1.
```

Since cocycle factors are nonzero, these equations force `kappa(q)=conj(kappa(q))`. HC53's hard
source theorem is

```text
Im(kappa(q)) = 0  <->  Re(q)=1/2.                 (REAL-KAPPA)
```

## Literal carrier factorization

Away from critical wall, source amplitude is nonzero. Real `kappa` and source transport make
the reflected/unreflected source product real. The common nonzero purely imaginary helicity factor
cancels, leaving reality of the carrier product.

For `s=q` and

```text
C(s) = (1+s/2)(s/2)^2,
t = s(1-s),
```

the exact identity

```text
64 C(s) C(1-s) = s^2(1-s)^2(s+2)(3-s) = t^2(t+6)
```

reduces its imaginary part to

```text
Im(t^2(t+6)) = v (3u^2-v^2+12u),
u = Re(t) = a(1-a)+b^2,
v = Im(t) = b(1-2a).
```

On actual Xi support, `0<a<1` and `b!=0`. Hence `u>0`, `v^2<u`, and
`3u^2-v^2+12u > 0`. Carrier-product reality therefore forces `v=0`, then `a=1/2`.

## Predicted kernel consequences

1. `Im(kappa(q))=0 <-> Re(q)=1/2`.
2. For reflection-real Ward `K`, nonzero `K(q,Rq)` forces criticality.
3. On every tilted reflection orbit, all four entries
   `K(q,q), K(q,Rq), K(Rq,q), K(Rq,Rq)` vanish.
4. For every reflection-real kernel nonzero on every reflected pair,

```text
B_K(Tx,Ty)=conj(B_K(x,y)) for every finite x,y  <->  RH.
```

This closes the mixed-copy orbit loophole, not merely diagonal terms. Any surviving off-RH fixed
Ward kernel must couple distinct functional-equation orbits.

## Hostile checks

- Do not divide by source on critical wall; split wall/off-wall first.
- Use only literal source transport and carrier formula already in corpus.
- Prove positivity of cofactor throughout full open strip, not numerically or by sampled zeros.
- No assumption that an off-line Xi zero exists.
- Distinguish reflection-pair support from arbitrary cross-orbit support; HC53 does not claim all
  off-diagonal kernels vanish.
- Final Lean theorems must be unconditional and axiom-audited.

## Novelty boundary as of 2026-08-28

Targeted corpus search found cocycle involutivity and square-one rigidity but no cocycle-reality or
reflection-pair kernel theorem. Targeted primary-literature search found conserved/reflection-based
QNM bilinear forms (Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935; Minucci--Macedo--
Pantelidou--Sberna, arXiv:2604.13182), but no Xi-source cocycle reality classification or
reflection-orbit RH rigidity. Search is bounded, not exhaustive.

## Formal result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFERealCocycleReflectionOrbitExtinction`.
Lean proves:

1. the exact carrier identity `C(1-s) C(s) = (s(1-s))^2 (s(1-s)+6) / 64`;
2. carrier-product reality forces `Re(s)=1/2` throughout the open strip at nonzero height;
3. `Im(kappa(q))=0 <-> Re(q)=1/2` for every actual Xi copy;
4. reflection-pair nonvanishing of a reflection-real Ward kernel forces criticality;
5. every tilted reflection orbit has a zero full `2 x 2` kernel block; and
6. reflection-real reflected-pair nondegeneracy makes full packet covariance equivalent to RH.

No off-line zero is assumed. Result uses literal corpus source amplitude and functional-equation
transport, not an abstract replacement cocycle.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: source-polynomial paper proof and obstruction audit
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC52 proved diagonal extinction but left reflection-pair entries open.
- 2026-08-28 — Closed the exact carrier factorization and positive-cofactor argument in Lean.
- 2026-08-28 — Proved real-cocycle critical-line rigidity and full tilted reflection-orbit block
  extinction. Direct `lake env lean` and target-only `lake build` passed (`11921/11921`). All six
  public theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint
  reports no HC53 failure; remaining errors are unrelated pre-existing umbrella reachability gaps.
