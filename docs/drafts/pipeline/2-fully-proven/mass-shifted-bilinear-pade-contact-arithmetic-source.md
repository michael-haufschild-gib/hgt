# Bilinear Padé-contact arithmetic source

- **ID:** mass-shifted-bilinear-pade-contact-arithmetic-source
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** mass-shifted spectral-face §9.3, post-(9.3.406)
- **Statement:** Every flat-shadow contact of order `d>=2` is produced exactly by completed adaptive bilinear source on two admitted null-ideal lifts whose lift degrees sum to `d-2`.

## Goal

Create missing admission-sensitive arithmetic producer for all parity lifts, before reflection
aggregation. Same-amplitude quadratic source sees only even top degree; bilinear source between
two independently admitted lifts removes that parity restriction.

## Gates

- [x] 0 → 1 in-progress: exact typed conjecture, internal/external audit, hostile parity attack
- [x] 1 → 2 fully-proven: complete proof below, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact Lean theorem and arithmetic capstone
- [ ] 3 → 4 publication-ready: independent priority audit

## Definitions

For polynomials `A,B`, define symmetric Euler-source shear

```text
BilShear(A,B)
 := (X A) * (X E_1 B) + (X B) * (X E_1 A),
E_1 F := X F' + F.
```

Let `crossPacket(A,B)` be finite coefficient packet of `A*B`. Define completed bilinear source by
applying one adaptive midpoint step to this packet at base order one, then forming rational-Gamma
aggregate minus von Mangoldt aggregate at base order two.

## Theorem `[PROVED HERE]`

### Source connection

For shifted-Xi moment form `L_y`, `y>0`,

```text
d/dy L_y(A X B) = -L_y(BilShear(A,B)).                 (BCS.1)
```

The adaptive completed packet and literal arithmetic source both equal right side without minus:

```text
Completed_2(midpoint_1(crossPacket(A,B)))
 = L_y(BilShear(A,B))
 = RationalGamma_2(...) - VonMangoldt_2(...).          (BCS.2)
```

### First-contact landing

Let `P` be terminal-normalized monic null polynomial of flat degree `n`; let `delta` be Padé defect
from canonical positive atomic flat shadow. Fix `d>=2` and natural `i,j` with `i+j=d-2`. Set

```text
A := P X^i,   B := P X^j,   K := 2*n+d.
```

If `delta_k=0` for all `k<K`, then

```text
ArithmeticCrossSource(w;A,B) = K * delta_K.            (BCS.3)
```

Thus at first contact, even `d` gives positive source and odd `d>=3` gives negative source under
right-cone contact orientation. Order `d=1` is uniquely source-inaccessible inside polynomial null
ideal and is already handled by direct odd-coupling preemption.

## Proof

Euler Leibniz identity is exact:

```text
X E_1(A X B)
 = (X A)(X E_1 B) + (X B)(X E_1 A).
```

Combine with shifted-Xi moment source connection `L_y(F)'=-L_y(X E_1F)` to prove (BCS.1).
Writing `A*B` by its finite coefficient packet identifies `L_y(A X B)` with base-one completed
aggregate. Existing midpoint derivative law has same derivative; uniqueness yields first equality
in (BCS.2). Generic completed-source decomposition yields second equality before reflection.

For (BCS.3), each summand of `BilShear(PX^i,PX^j)` has one explicit factor `P`, so canonical atomic
shadow annihilates it. Both lifts are monic of degrees `n+i` and `n+j`. Hence shear has degree

```text
(n+i)+(n+j)+2 = 2*n+d = K
```

and leading coefficient

```text
(n+j+1)+(n+i+1)=K.
```

Therefore moment functional of defect sequence sees only top monomial under vanishing below `K`,
and equals `K delta_K`. This proves (BCS.3).

## Hostile audit and conjecture loop

1. **Same-amplitude all-contact conjecture — FALSE.** Quadratic adaptive shear has even top degree,
   so first odd defect is inseparable from next even coordinate.
2. **Adjacent-lift conjecture — survives only for `d>=3`.** Degrees `(m-1,m)` produce odd contact;
   no predecessor lift exists for `d=1`.
3. **Universal bilinear null-ideal conjecture — PROVED.** Any `d>=2` splits as `i+j+2`; balanced
   lifts are optional. Same proof covers all splits and both parities.
4. **Attempt to include `d=1` — FALSE by degree.** Any nonzero pair in ideal `(P)` has degrees at
   least `n,n`; Euler source raises total degree by two, so top degree is at least `2n+2`.

External degenerate-Hamburger literature supplies kernel/flat-extension parent theory; Toda and
orthogonal-polynomial deformation literature supplies source-connection parents. Neither source
audited here states shifted-Xi rational-Gamma/von-Mangoldt pre-aggregation law (BCS.2)-(BCS.3).
Novelty claim remains provisional; theorem is at minimum a new corpus bridge and exact route delta.

## No-go closure

- **Exact killing mechanism:** polynomial null-ideal source has minimum contact order two.
- **Strongest positive survivor:** all orders `d>=2` have exact bilinear arithmetic producer; order
  one is uniquely geometric/preemptive.
- **New insight:** parity is not obstruction to source production; arity is. Quadratic diagonal
  reports only even top degree, while bilinear source spans every order from two upward.
- **Status:** paper-proved; Lean pending.

## Log

- 2026-08-11 — frozen after quadratic parity failure; dependency-closed proof completed.
