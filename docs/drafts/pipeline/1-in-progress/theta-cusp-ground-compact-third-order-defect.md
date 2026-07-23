# Theta-cusp ground compact third-order defect

- **ID:** TC-GC3D
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** exact all-shell third-order identity in
  `ThetaCuspShellIncompleteGammaCoordinate.lean`

## Statement

For `0<a<1/2`, `b>218/25`, and ground shell `n=1`, put

```text
f(x) = thetaCuspTiltedWardDensity a 1 x,
K3(u) = u(2+cos u)-3 sin u.
```

Prove

```text
0 <
  integral_(0,1/2] -f'''(x) K3(bx) dx
  + integral_(1/2,infinity) -f'''(x) K3(bx) dx.        (GC3D)
```

By the Lean-proved identity

```text
b^4 integral_(0,infinity) x f(x) sin(bx) dx = RHS(GC3D),
```

this proves `Re R'_1(b-ia)<0`.

## What is already proved

- `K3(u)>0` for every `u>0`.
- `f'''(x)<0` for every `x≥1/2`.
- Tail in `(GC3D)` is strictly positive.
- Exact head-plus-tail equality is formalized.
- Equivalent derivative-rotation split confines negative signed density to `x<1/3`.
- For every `n≥2`, stronger global law `f'''<0` closes derivative sign without this conjecture.
- There is a unique `tau(a) in (0,1/2)` with `f'''(tau)=0`; `f'''>0` before `tau` and
  `f'''<0` after `tau`.
- Splitting at `tau`, compact head is strictly negative and cofinal tail strictly positive.
- Signed zeroth/first masses and both absolute moments are exact boundary expressions:

  ```text
  integral |f'''|  = 2f''(tau)-f''(0),
  integral x|f'''| = f'(0)+2tau f''(tau)-2f'(tau).
  ```

- Fourth-order boundary identity is formalized:

  ```text
  b^4 integral x f(x) sin(bx) dx
    = -2b f'(0) + integral (4f'''(x)+x f''''(x)) sin(bx) dx.
  ```

- With

  ```text
  B4(a)=integral |4f'''+x f''''| / (-2f'(0)),
  ```

  Lean proves `b>B4(a)` implies ground horizontal derivative direction
  `Re R'_1(b-ia)<0`.

## Current attack

Primary target is now nonoscillatory uniform budget

```text
forall 0<a<1/2, B4(a) <= 218/25.                        (B4)
```

Use exact ground coefficient

```text
f'''(x)/f(x)
  = s(x)^3 - 6 q(x) s(x) - 4 q(x),
s(x)=a+5/2-q(x),
q(x)=2 pi exp(2x).
```

`(B4)` can be attacked through sign changes of
`4f'''+x f''''`, or by a direct polynomial-Gaussian majorant after `q=2*pi*exp(2x)`.
If `(B4)` is too crude, return to exact one-transition kernel comparison. Current directions:

1. classify zeros of `4f'''+x f''''` and evaluate its total variation from boundary/extremum data;
2. bound polynomial-Gaussian absolute integral uniformly in `0<a<1/2`;
3. combine third-order compact split with rotation-density split at `x=1/3`, retaining exact
   exponential score rather than absolute estimates.

## Falsifiers

- An admissible `(a,b)` for which exact ground first sine moment is nonpositive.
- A symbolic inequality forced by exact coefficient showing compact head dominates positive tail.

No numerical test is accepted as proof or disproof.

## Relation to RH chain

`(GC3D)` closes ground horizontal derivative direction only. Actual high-frequency Hedenmalm
current still needs scale-sensitive transverse derivatives and cofinal reflected product-fibre
orientation. This card is one live theorem target, not route closure and not an RH-equivalent
renaming.

## Gates

- [x] exact statement and source reduction
- [x] positive tail proved on paper and in Lean
- [x] unique transition and exact signed head/tail in Lean
- [x] exact total-variation identities in Lean
- [x] ground derivative theorem above explicit `B4(a)` in Lean
- [ ] prove uniform `B4(a) ≤ 218/25`, or replace with sharper signed-kernel bound
- [ ] use in actual reflected current
