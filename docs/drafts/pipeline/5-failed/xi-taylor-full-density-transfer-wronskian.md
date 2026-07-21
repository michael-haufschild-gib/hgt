# Xi Taylor/full-density pure-transfer Wronskian

- **ID:** `xi-taylor-full-density-transfer-wronskian`
- **Stage:** 5-failed
- **Type:** `[FALSIFIED CONJECTURE] [EXACT NO-GO] [POSITIVE SURVIVOR EXTRACTED]`
- **Parent:**
  `../3-formalized/new_scientific_knowledge/full-theta-density-monotone-completion-current.md`
- **Successor:**
  `../1-in-progress/xi-completed-density-antipodal-crossing-barrier.md`

## Conjecture tested

Let

```text
F(z)=integral_(0,infinity) rho(t) exp(i t z) dt,
P_d(z)=P_(2d+3)(z),
W_d(z)=P_d'(z)F(z)-P_d(z)F'(z).
```

The proposed mechanism asserted that after inserting the exact theta-source integral for `P_d`,
the full exponential channel cancels identically and `W_d` consists only of a Taylor-remainder
covariance plus a remote row tending to zero.

## Exact falsification

For two full positive phases the pointwise Wronskian kernel is

```text
(i x exp(i x z)) exp(i t z)-exp(i x z)(i t exp(i t z))
  =i(x-t)exp(i(x+t)z).                                 (1)
```

It vanishes exactly on the diagonal `x=t`, not identically.  Antisymmetric integration cancels
`(1)` only when both transform legs carry the same source measure.  Here the Xi section carries
the completed source `Phi` and an even cosine phase, while `F` carries

```text
rho=4 T''=T+4 Phi
```

and a one-sided exponential phase.  Both source and phase are mismatched.

Put

```text
R_d=XiC-P_d,
Omega_F=XiC' F-XiC F'.                                (2)
```

Direct algebra gives the exact decomposition

```text
W_d=Omega_F-(R_d'F-R_dF').                            (3)
```

Local-uniform Taylor convergence, including derivatives, gives at every fixed `z`

```text
W_d(z) -> Omega_F(z).                                 (4)
```

The background is genuinely nonzero.  At the reflection center,

```text
XiC'(0)=0,
F'(0)=i integral_(0,infinity) t rho(t) dt,
integral t rho(t) dt>0,
XiC(0)!=0,

Omega_F(0)=-XiC(0)F'(0)!=0.                          (5)
```

Thus `W_d` cannot be a vanishing Taylor-remainder object.  This kills the conjecture before any
estimate, arithmetic fibre split, or anisotropic limit.

## Stronger reflected-source identity

Write `F_-=F(-z)`, `D=F'(z)`, `D_-=F'(-z)`, and `q=z^2+1/4`.  Existing completed reflection and
its derivative imply the newly isolated exact connection

```text
C_F(z)
 =2z(F+F_-)F-q(D_-F+F_-D)+(1/2)D
 =8z XiC F+4z^2 Omega_F.                              (6)
```

At a simple Xi zero in the open upper theta strip,

```text
C_F(z)=4z^2 XiC'(z)F(z)!=0,                           (7)
```

because the monotone-completion theorem proves `F(z)!=0`.  The full Wronskian survivor is therefore
the reflected growing channel plus the central seam.  It is exactly the zero signal the proposed
cancellation would have erased.

## Positive survivor: transfer is not truncation

Define

```text
Q(z)=XiC(z)/F(z).
```

Then, pointwise,

```text
T_d=P_d/F -> Q,
T_d' -> Q'=Omega_F/F^2,
J(T_d) -> J(Q).                                       (8)
```

Moreover, for `Im z>0`,

```text
Q(z)=0 <-> XiC(z)=0.                                  (9)
```

So the transfer predicate formalized in the parent is a correct RH-equivalent gauge bridge, but it
does not isolate a finite-truncation defect.  It converges to a quotient with exactly the Xi
divisor.  The actual unsolved problem remains exclusion of the full reflected-source collision,
not decay of a Taylor remainder.

## Why nearby known routes do not repair it

- `XiCTaylorThetaTailCompletedDensityDeBrangesNoGo.lean` proves the natural global
  Hermite--Biehler norm gap is false on the open critical half-strip.
- Dimitrov--Xu identify Wronskians of a single transform with correlation kernels.  Same-source
  antisymmetry is consistent with `(1)`; it does not cancel this mixed-source Wronskian.
- Griffin--Ono--Rolen--Zagier prove eventual fixed-degree Jensen hyperbolicity, not cancellation of
  the full Xi quotient background.
- Sondow--Dumitrescu give horizontal Xi-modulus reformulations inside zero-free half-planes, not a
  source theorem controlling `F(-z)` from `F(z)`.

## No-go scope

Retired:

1. any claim that the full phase in this scalar comparison cancels pointwise;
2. any representation of all `W_d` as a remainder tending to zero at fixed `z`;
3. the interpretation of `T_d` as carrying only finite truncation;
4. any repair by the already refuted global completed-density de Branges gap.

Not retired: a collision-only projective barrier for the reflected pair.  That successor may let
the completed-density gap change sign away from the antipodal phase and therefore is strictly
weaker than global Hermite--Biehler orientation.

## Lean status

Paper proof and Lean formalization closed in
`XiCTaylorThetaTailFullDensityWronskianNoGo.lean`.  Direct check and targeted module build pass.
Axiom audit of nine capstones reports only `propext`, `Classical.choice`, and `Quot.sound`; formal
lint passes.

## Literature

- D. K. Dimitrov and Y. Xu, *Wronskians of Fourier and Laplace Transforms*,
  <https://arxiv.org/abs/1606.05011>.
- M. Griffin, K. Ono, L. Rolen, and D. Zagier, *Jensen polynomials for the Riemann zeta function
  and other sequences*, <https://arxiv.org/abs/1902.07321>.
- J. Sondow and C. Dumitrescu, *A monotonicity property of Riemann's xi function and a
  reformulation of the Riemann Hypothesis*, <https://arxiv.org/abs/1005.1104>.

## Log

- 2026-07-21 — Conjecture created from zero-free full-density factorization.
- 2026-07-21 — First exact kernel test falsified full-channel cancellation.  Extracted `(3)`--`(9)`
  as positive survivor and retired route before estimates.
