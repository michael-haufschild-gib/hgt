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
- Lean proves exact fourth-coefficient and remainder geometry. The shifted quartic has exactly two
  roots and sign pattern `+,-,+`; a strict cubic--quartic Wronskian makes the remainder root phase
  strictly increasing; consequently `4f'''+x f''''` also has exactly two roots with sign pattern
  `+,-,+`.
- For `H=3f''+x f'''`, Lean proves exact total variation

  ```text
  integral |4f'''+x f''''| = 2H(sigma1)-2H(sigma2)-H(0).
  ```

- Exact symbolic rational bounds at `(a,x)=(1/4,1/5)` prove

  ```text
  218/25 < B4(1/4).
  ```

  Therefore uniform absolute budget `(B4)` is false.

## Current attack

Primary target returns to signed oscillatory cancellation:

```text
forall 0<a<1/2, forall b>218/25,
  0 < integral_(0,infinity) -f'''(x) K3(bx) dx.         (GC3D)
```

Absolute variation is no longer admissible: Lean proves it exceeds target cutoff at `a=1/4`.
Next proof must exploit phase. Available exact structures are:

1. `f'''` has exactly one transition `tau`; compare negative head and positive tail interval by
   interval using monotonicity of `K3(bx)`;
2. use exact identities for signed zeroth and first masses to cancel the affine part of `K3`;
3. retain the bounded oscillatory residual `u cos u-3 sin u` rather than majorizing it absolutely;
4. combine third-order transition with the two-transition fourth remainder to control variation
   on each phase cell.

## Falsifiers

- An admissible `(a,b)` for which exact ground first sine moment is nonpositive.
- A symbolic inequality forced by exact coefficient showing compact head dominates positive tail.
- Uniform `B4(a)≤218/25` is now a proved falsified mechanism, not an open falsifier.

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
- [x] classify fourth remainder roots and exact total variation in Lean
- [x] disprove uniform `B4(a) ≤ 218/25` in Lean at `a=1/4`
- [ ] prove sharper signed-kernel bound
- [ ] use in actual reflected current
