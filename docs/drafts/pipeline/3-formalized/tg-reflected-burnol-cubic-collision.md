# TG reflected Burnol cubic at a clock collision

- **ID:** TG-C4-REFLECTED-COLLISION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / source-budget obstruction and exact finite part
- **Route:** TG, arithmetic source-to-Hardy cubic transgression

## Candidate and exact task

Replacing `G tensor I` by separate orthogonal reflected sectors still fixes the neutral
projection, so the existing sigma-trace cancellation applies. Instead test the complete
coherent Gram of the two literal columns with clocks `kappa` and `-kappa` at one prime-depth
label. This retains their cross term. It is a finite source pressure test, not an identification
with the required four-leg Euler/continuum carrier or completed Hardy pair.

Write `lambda=log(p^(e+1))>0`, `d=|amplitude|^2/(4 lambda^3)` and
`z=(lambda/(lambda-i kappa))^3`. The literal Gram is
`c=d [[1,z],[conj z,1]]`. At nonzero kappa it is invertible; at zero the two columns coincide.
Let `p0=diag(1,0)`, `q=[[u,v],[v,1-u]]`, with the actual theta rotation giving
`u=visibility^2`, `v=visibility*contrast`, and `v^2=u(1-u)`.

Test whether the weighted cubic
`Tr(c*((c^-1 q c-p0)^3-(c^-1 q c-q)^3-(q-p0)^3))`
can inherit a uniform source budget through the collision. The proposed exact formula is

```
d*v*(z+conj z)*(z*conj z*(1-2*u)+v*(z-conj z))/(1-z*conj z).
```

Its proposed real part is
`-2*d*v*Re(z)*|z|^2*(2*u-1)/(1-|z|^2)`. Since
`1-|z|^2=kappa^2*(3*lambda^4+3*lambda^2*kappa^2+kappa^4)/(lambda^2+kappa^2)^3`,
the unrenormalized response appears to have a second-order pole whenever `v*(2*u-1)!=0`.
The scalar formulas and limits below have a dependency-closed paper derivation and pass the
direct production Lean audit. No completed Hardy comparison is asserted.

## Paper proof and positive survivor

For arbitrary complex `z,w,u,v`, set `G=[[1,z],[w,1]]`, `q=[[u,v],[v,1-u]]` and
`p0=diag(1,0)`. If `1-zw!=0`, use `G^-1=(1-zw)^-1 [[1,-z],[-w,1]]`.
Every traceless two-by-two matrix `X` satisfies
`X^3=(X00^2+X01*X10) X`. Apply this to `r-p0`, `r-q`, and `q-p0`, where
`r=G^-1 q G`; each has trace zero. Cyclicity gives
`Tr(G(r-q))=0` and `Tr(G(r-p0))=Tr(G(q-p0))=v(z+w)`.
The difference of the first and third square coefficients is
`u-r00=(zw(1-2u)+v(z-w))/(1-zw)`. This proves the proposed cubic formula.
In fact no idempotence condition on q is needed. Lean has checked this matrix identity.

For the literal reflected coefficient, put `S=lambda^2+kappa^2`,
`H=3lambda^4+3lambda^2 kappa^2+kappa^4`, and `J=H*S^3`. Then

```
Re z = lambda^4*(lambda^2-3kappa^2)/S^3,
Im z = lambda^3*kappa*(3lambda^2-kappa^2)/S^3,
|z|^2 = lambda^6/S^3,
1-|z|^2 = kappa^2*H/S^3.
```

Consequently the normalized response F (literal response is dF) has

```
Re F = -2v(2u-1)lambda^10*(lambda^2-3kappa^2)/(kappa^2*J),
Im F = 4v^2*lambda^7*(lambda^2-3kappa^2)*(3lambda^2-kappa^2)/(kappa*J).
```

Subtracting both principal poles leaves exact regular rational functions:

```
Re F + 2v(2u-1)lambda^2/(3kappa^2)
 = 2v(2u-1)lambda^2*(21lambda^8+19lambda^6 kappa^2
     +15lambda^4 kappa^4+6lambda^2 kappa^6+kappa^8)/(3J),
Im F - 4v^2*lambda/kappa
 = -4v^2*lambda*kappa*(22lambda^8+16lambda^6 kappa^2
     +15lambda^4 kappa^4+6lambda^2 kappa^6+kappa^8)/J.
```

Their limits at zero are `14v(2u-1)/3` and zero. Also
`kappa*Im F -> 4v^2*lambda>0` for v nonzero. Thus `Im F -> +infinity`
as kappa approaches zero from above, including the balanced rotation u=1/2 where the
second-order real pole vanishes. This rules out a uniform raw sub-unit budget even at one
literal prime-depth cell. The positive survivor is the exact two-pole counterterm and regular
finite remainder. It identifies what any proposed completion countercurrent must cancel;
it does not prove that the actual Gamma/continuum countercurrent cancels it.

## Why this attacks the open problem

The previous finite source had identically zero neutral charge. Coherent reflection moves the
reference and can evade that cancellation. The test decides whether the new charge can satisfy
TG's required sub-unit estimate, or identifies the precise arithmetic counterterm needed before
any such estimate is possible. No arbitrary Xi-dependent source parameter is introduced.

## Gates

- [x] Literal source and candidate formula fixed before divisor specialization.
- [x] Exact cubic identity proved and checked in Lean.
- [x] Exact collision coefficient and budget consequence proved.
- [x] Candidate fails; exact two-pole subtraction and finite part formalized.
- [ ] Construct actual four-leg relative boundary and Hardy index comparison (still open).

## Search audit

Two corpus searches run directly with 120-second budgets. Reflected-source search completed
with full inventory but mostly source-only compiler metadata. Existing common/opposite vertical
shift identities and Krein producer retain signed source data but supply no norm bound across
the balanced wall. Exhaustive source-text search found no reflected Burnol cubic collision
formula; bipolar Gram drift anomaly handles a different quadratic commutator.

## Lean artifact and audit

Module: `formal/GaloisForLFunctions/RHTower/PrimeBurnolReflectedCubicCollision.lean`.
Public results identify the literal Gram and inverse, compute its actual theta cubic trace,
prove both finite-part limits, and prove imaginary trace tends to positive infinity for every
nonzero theta parameter. All data are supplied before divisor specialization. The rotation
parameter in the divergence theorem is a real unit; no analytic or RH premise is supplied.

Production audit, exit 0 with no warnings:

```
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PrimeBurnolReflectedCubicCollision.olean GaloisForLFunctions/RHTower/PrimeBurnolReflectedCubicCollision.lean
```

Wired into `GaloisForLFunctions/RHTower.lean`; no umbrella build. Separate import audit of all
seven public theorems exited 0. Each depends only on `propext`, `Classical.choice`, and
`Quot.sound`. No added axioms, proof holes, computation oracle, or heartbeat increases.

`scripts/formal_tools.py index` exited 0 and registered the leaf and public declarations.
`scripts/formal_tools.py lint` exited 1 for fourteen unrelated unwired modules and existing
large-file warnings; neither TG leaf appears among the errors. Exact list is in the working log.
Scoped `git diff --check` passed. Temporary search and Lean scratch artifacts were cleaned after
recording their outcomes. No commit, push, full build, or umbrella build.

## Remaining hard problem

The local counterterms do not construct the actual Gamma/continuum countercurrent. Nor may
one sum the one-cell finite parts and silently discard cross-prime inverse-Gram terms. The
next source target is the complete mixed-prime collision expansion and an arithmetic identity
matching its principal part to the four-leg completion. Its residual must then carry the actual
Hardy index and obey a sub-unit bound. None of those producer statements follows here.
