# Theta-cusp single-atom reflected Riccati contraction

- **ID:** `theta-cusp-single-atom-reflected-riccati-contraction`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Date:** 2026-07-23
- **Scientific status:** `[PROVED HERE] [SOURCE-PURE] [NO COMPUTATION] [NOT RH]
  [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../../1-in-progress/theta-cusp-reflected-correlation-angle-concavity.md`
- **Statement:** Every positive theta-cusp source atom has strict reflected Riccati contraction
  whenever both reflected arguments lie on the same modular half-line.

## Goal

For `n>=1`, `0<=t<=u`, and

```text
phi_n(x)=thetaCuspSourceTerm(x,n),
P_(n,u)(t)=phi_n(u+t)phi_n(u-t),
p_(n,u)(t)=P_(n,u)(t)/P_(n,u)(0),
S_(n,u)(t)=-log p_(n,u)(t),
q_(n,u)(t)=S_(n,u)'(t),
```

prove

```text
q_(n,u)''(t) < 2 q_(n,u)(t) q_(n,u)'(t)       for 0<t<=u,              (RC1)
```

with equality at `t=0`.  Consequently the atom's normalized reflected correlation angle

```text
arccos(p_(n,u)(t))
```

is strictly concave away from the reflection center on this chamber.

This theorem does not assert the corresponding property for the completed atom sum.  It proves
that any failure of the full conjecture must be caused by cross-atom interference or modular-seam
cancellation.

## Gates

- [x] 0 → 1 in-progress: exact source statement and parent audit
- [x] 1 → 2 fully-proven: dependency-complete symbolic proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact Lean source theorem, literal derivative chain, narrow elaboration,
  axiom audit, umbrella wiring, and lint green
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, and priority review

## Exact atom normal form

Put

```text
A=pi*n^2*exp(2u),                A>3,
z=cosh(2t)-1,                    z>=0,
lambda=3A/(A-3/2)^2,
r=1-lambda*z.
```

Since `0<=t<=u`, both atom arguments are nonnegative and

```text
A*exp(-2t)>=pi*n^2>3.
```

The literal polynomial--Gaussian source formula gives

```text
p_(n,u)(t)
  =(1-lambda*z)*exp(-2A*z)=r*exp(-2A*z),                (1)
```

so `r>0`.  Let

```text
B=2A,
h(z)=B+lambda/r.
```

Then

```text
S_(n,u)(t)=2A*z-log r,
q_(n,u)(t)=h(z)z',
z'^2=4z(z+2),       z''=4(z+1),       z'''=4z',
h'=lambda^2/r^2,    h''=2lambda^3/r^3.                 (2)
```

## Dependency-complete proof

For `t>0`, `z'>0`.  Substitution of `(2)` gives

```text
(2q q'-q'')/z'=4G,                                                   (3)
```

where

```text
G=
  lambda^2/r^2 * (2B*z*(z+2)-(z+1))
  +2B^2*(z+1)-B
  +(4B*(z+1)-1)*lambda/r.                              (4)
```

The cancellation behind `(4)` is exact:

```text
2h h'-h''=2B*lambda^2/r^2.
```

It remains only to prove `G>0`.

Because `A>3`,

```text
B>6,                  0<lambda<=4.                     (5)
```

The upper bound follows from

```text
3A<=4(A-3/2)^2
  iff 0<=4A^2-15A+9,
```

whose right side vanishes at `A=3` and has positive derivative for `A>=3`.

Split according to the first coefficient in `(4)`.

### Chamber I

If

```text
2B*z*(z+2)-(z+1)>=0,
```

then every summand in `(4)` is nonnegative and the middle summand is strictly positive:

```text
2B^2*(z+1)-B=B*(2B*(z+1)-1)>0.
```

Hence `G>0`.

### Chamber II

Suppose

```text
2B*z*(z+2)-(z+1)<0.
```

Since `B=2A` and `z(z+2)>=2z`,

```text
(8A-1)z<1.
```

Using `A>3` and `(5)` gives

```text
z<1/23,
lambda*z<4/23,
r>19/23.                                               (6)
```

The only negative contribution in `(4)` is therefore bounded in absolute value by

```text
(z+1)*lambda^2/r^2
 <(24/23)*16*(23/19)^2
 =8832/361
 <25.                                                   (7)
```

On the other hand,

```text
2B^2*(z+1)-B
 >=2B^2-B
 >66,                                                   (8)
```

and the last summand in `(4)` is positive.  Equations `(7)`--`(8)` give `G>41>0`.

Thus `(3)` proves `(RC1)` for `0<t<=u`.  At `t=0`, `q=0` and `q''=0`, so the non-strict
contraction holds with equality.

## Correlation-angle consequence

For any positive normalized profile `p=exp(-S)` with `q=S'`, define

```text
H=q^2-(1-exp(-2S))*q'.
```

Then

```text
H(0)=0,
H'=(1-exp(-2S))*(2q q'-q'').                             (9)
```

The atom has `0<p<=1`, `S>=0`, and strict `(RC1)`.  Hence `H>=0`.  Direct differentiation gives

```text
(arccos p)''
 =p/(1-p^2)^(3/2)*((1-p^2)q'-q^2)<=0.                  (10)
```

The limiting center value is controlled by the already known negative second logarithmic jet.
Therefore the normalized reflected atom angle is concave throughout `[0,u]` and strictly concave
on `(0,u]`.

## Hostile audit and positive classification

1. **No atom sum was replaced by its first term.**  The theorem is deliberately atomwise.  It
   identifies what survives before summation.
2. **No numerical estimate occurs.**  Only `pi>3` and exact rational inequalities enter.
3. **The coalesced fourth-Turán sign is visible but not assumed.**  Differentiating `(RC1)` at
   `t=0` recovers the atom's strict fourth-Turán inequality.
4. **The modular seam remains real.**  A standalone positive-half-line atom has a cusp after even
   reflection.  The completed source becomes smooth only through higher-atom seam cancellation.
5. **Cross terms are the exact new open core.**  Expanding

   ```text
   k(u+t)k(u-t)=sum_(m,n) phi_m(u+t)phi_n(u-t)
   ```

   shows that the diagonal terms `m=n` satisfy the theorem.  Only symmetrized `m!=n` terms and the
   seam can obstruct the completed-source contraction.

This is a non-trivial positive survivor: the global order-three problem is not blocked by any
single theta atom on one modular half-line.  It is an interference theorem.

## Literature boundary

The correlation-angle implication uses the classical `3 x 3` criterion of
Castano--Paksoy--Zhang, arXiv:1407.2800.  Searches of Hedenmalm's theta-source paper, theta-kernel
log-concavity work, finite-order Pólya-frequency results, and correlation-angle literature found
no atomwise reflected Riccati contraction of the form `(RC1)`.  Novelty remains provisional.

## Lean realization

`RHTower/ThetaCuspSingleAtomReflectedRiccatiContraction.lean` formalizes:

- the exact source atom normal form and normalized reflected product;
- the reflected action as the negative logarithm of that model;
- literal first, second, and third derivative identities for the displayed jets;
- the exact Riccati-margin factorization and rational two-chamber positivity proof;
- the unconditional source capstone
  `thetaCuspSourceTerm_reflectedRiccatiMargin_pos`.

The module is imported by `RHTower/RiemannHypothesisSOTA2026.lean`.

## Log

- 2026-07-23 — isolated during hostile attack on global reflected correlation-angle concavity.
  The exact polynomial--Gaussian normal form produced a two-case symbolic proof.  Promoted to
  Stage 2 because all dependencies are closed and no computation, RH hypothesis, matrix
  positivity, or completed-source sign is assumed.
- 2026-07-23 — formalized exact source theorem, source/model connector, derivative chain, margin
  identity, and strict positivity.  Promoted to Stage 3 and wired into the RHTower frontier
  umbrella.
