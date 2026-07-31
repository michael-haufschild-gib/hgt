# Suzuki coherent completion is the weighted negative spectral projector

- **ID:** `suzuki-negative-projector-coherent-completion`
- **Stage:** 2 — fully proved on paper
- **Type:** exact operator theorem / coherent finite-node completion target
- **Status:** `[PROVED] [UNCONDITIONAL] [SOURCE-SPECTRAL]`
- **Parents:** `suzuki-affine-resolvent-krein-defect.md`,
  `suzuki-xireal-fe-bipolarization-completion.md`,
  `suzuki-krein-schur-holonomy-tax.md`
- **RH used:** no
- **Computation used:** no

## 1. Gap closed

Xi-real/FE bipolarization identifies amount and light-line direction of minimal completion at one
spectral coordinate.  Pointwise completion does not by itself assemble a positive kernel on
several spectral nodes.  This theorem identifies unique coherent all-node completion forced by
restricted-Weil spectral calculus.

## 2. Operator setup

Let `A` be lower-bounded self-adjoint operator, let

```text
alpha<beta<0,     alpha,beta<inf spec(A),     0 in rho(A). (1)
```

Put `R_lambda=(A-lambda I)^(-1)` and

```text
D_(alpha,beta)
=R_0-[beta R_alpha-alpha R_beta]/(beta-alpha).          (2)
```

Define positive scalar weight on spectrum

```text
omega_(alpha,beta)(t)
=alpha beta/[|t|(t-alpha)(t-beta)].                     (3)
```

By `(1)`, denominator is positive and separated from zero on spectrum.  Thus `omega(A)` is a
bounded positive operator.

## 3. Signed functional-calculus theorem `[PROVED]`

Scalar affine-resolvent identity and continuous functional calculus give

```text
D_(alpha,beta)
=alpha beta A^(-1)(A-alpha I)^(-1)(A-beta I)^(-1)
=sgn(A) omega_(alpha,beta)(A).                          (4)
```

Let

```text
P_+=1_(0,infinity)(A),
P_-=1_(-infinity,0)(A),
W=omega_(alpha,beta)(A).
```

Since `P_±` commute with `W`, equation `(4)` has canonical Jordan decomposition

```text
D=D_+-D_-,
D_+=P_+W>=0,
D_-=P_-W>=0,
|D|=W.                                                  (5)
```

In particular

```text
D+D_-=D_+>=0,                                           (6)
D+2D_-=|D|>=0.                                         (7)
```

### Proof

Spectral theorem reduces every identity to scalar spectrum.  Exact scalar theorem gives
`D(t)=sgn(t)omega(t)`.  Multiplication by positive and negative spectral indicators gives `(5)`;
`(6)--(7)` are immediate.

## 4. Minimality and uniqueness `[PROVED]`

Among nonnegative corrections `C=c(A)` in commutative functional calculus of `A`,

```text
D+C>=0  iff  c(t)>=omega(t) on negative spectrum.       (8)
```

Therefore

```text
C>=D_-;                                                 (9)
```

and `D_-` is unique Loewner-minimal commuting positive correction.  This is operator-level
version of local Xi-real/FE minimal rate.  It fixes coefficient **and** spectral support.

## 5. Coherent finite-node Gram kernel `[PROVED]`

Let `Gamma(z)` be any family of source/evaluation vectors in Hilbert space of `A`.  Define

```text
K_D(z,w)=<D Gamma(w),Gamma(z)>,
K_-(z,w)=<D_- Gamma(w),Gamma(z)>.                       (10)
```

Then

```text
K_-(z,w)
=<W^(1/2)P_-Gamma(w),W^(1/2)P_-Gamma(z)>               (11)
```

is positive semidefinite on every finite node set.  Moreover

```text
K_D+K_-=K_(D_+)>=0.                                    (12)
```

Equation `(11)` solves coherent assembly abstractly: off-diagonal coefficients are not free or
chosen by geometric means; they are fixed Gram entries of weighted negative spectral projection.

At fixed Suzuki aperture, `P_-` has finite rank because restricted-Weil operator has discrete
spectrum accumulating only at `+infinity`.  Thus `K_-` is finite-rank source kernel.  Its rank is
exact aperture Morse charge, already known to exhaust off-line divisor count cofinally.

## 6. Exact analytic source conjecture

### `SUZUKI-NEGATIVE-PROJECTOR-TRIANGLE-IDENTITY` `[CONJECTURE]`

For one curvature-selected aperture and negative shift pair, place reflected Euler--Gamma triangle
and Neumann projective holonomy in one characteristic gauge.  Let `K_completion^src` be their
global/local correction in fixed Xi-real/FE negative-light channel.  Prove division-free source
identity

```text
K_completion^src(z,w)
=K_-(z,w)+K_extra(z,w),      K_extra>=0,                (13)
```

where `K_-` is explicit weighted negative-projector Gram `(11)` of actual restricted-Weil
operator.  No Xi zero or divisor may enter definition.

Then `(12)--(13)` give full sewn jump Pick positivity and existing pole tomography proves RH.

This is narrower than prior conjectures:

- amount: exact `omega(t)`;
- support: negative spectral projector `P_-`;
- direction: fixed Xi-real/FE `(J-R)/2` channel;
- off-diagonal assembly: exact Gram law `(11)`;
- remaining freedom: only positive kernel `K_extra`.

## 7. Holonomy alignment test

If actual source correction equals `(13)`, it is block diagonal relative to `P_+ direct_sum P_-`
and Schur holonomy tax vanishes.  If projective holonomy produces a cross block, exact theorem in
`suzuki-krein-schur-holonomy-tax.md` requires additional diagonal payment

```text
C_-+(D_++C_++)^(-1)C_+-.                               (14)
```

Thus analytic source calculation has two possible successful outcomes:

1. prove spectral alignment with `(J-R)/2`, hence cross block zero and `(13)`;
2. retain cross block and prove stronger Schur inequality including `(14)`.

One off-diagonal source coefficient inconsistent with `(11)` falsifies minimal identity, but may
still satisfy stronger taxed alternative.

## 8. Why this advances RH frontier

Earlier “coherent assembly” was an unnamed infinite matrix problem.  It is now one explicit
finite-rank operator identity `(13)`.  Prime--Gamma/Neumann triangles must reconstruct weighted
negative spectral projector of `A_a`.  This is exact source theorem to attack; no estimate or
arbitrary factor `B` remains.

## 9. Formal status

Scalar identity, sign, exact debt, local Xi-real/FE completion, and Schur tax are formalized in
current Lean modules.  Unbounded self-adjoint functional calculus and concrete Suzuki source
operator are not yet represented, so `(4)--(13)` remain dependency-closed paper proofs/conjecture
at analytic source boundary.

## 10. Projective/physical-source correction (2026-07-22)

Sections 6--8 are retained as valid **linear** completion theorem and sufficient external
majorant.  They are superseded as canonical physical-triangle producer.

Actual response is a projective quotient, so rank-one resolvent scaling cancels and one negative
eigenvalue can have nonzero `P_-W` while source quotient has zero shift motion.  Exact physical
triangle further identifies source operator as Volterra phase

```text
H_g=-i(V_g-V_g^*),
Omega=H_g-H_r*A,
```

with `H_r` rank-one on odd sources.  See
`suzuki-homogeneous-projective-resolvent-plucker-lift.md` and
`suzuki-volterra-cartesian-phase-defect.md`.

Therefore conjecture `(13)` is retired as an identity forced by source.  It remains usable only
in conditional form: if concrete relative-phase Plucker kernel dominates `(11)`, then projector
completion proves positivity.  Exact live source theorem is
`SUZUKI-RELATIVE-VOLTERRA-PHASE-CD-WELD`.
