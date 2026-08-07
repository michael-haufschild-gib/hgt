# Suzuki coherent completion is the weighted negative spectral projector

- **ID:** `suzuki-negative-projector-coherent-completion`
- **Stage:** 3 — formalized in Lean 4
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

`formal/GaloisForLFunctions/RHTower/SuzukiNegativeProjectorCoherentCompletion.lean` formalizes
Sections 3--5 unconditionally.  The device that removes the unbounded-operator obstruction is the
card's own hypothesis `0 in rho(A)`: the inverse `B = A^(-1)` is a *bounded* self-adjoint operator,
and in the inverse coordinate `x = 1/t` the affine defect is the rational function

`d(x) = alpha*beta*x^3 / ((1 - alpha*x)*(1 - beta*x))`,

regular and vanishing at the spectral accumulation point `x = 0`.  So the whole signed
functional-calculus theorem is continuous functional calculus of one bounded operator.  No spectral
projection and no Borel calculus are needed, because the two spectral halves of the defect are
exactly its positive and negative parts.

- `suzukiInverseKreinDefect_inv`: spectral bridge, `d(1/t)` is the affine Krein defect at `t`.
- `suzukiInverseKreinWeight_eq_abs`: the weight `omega` of `(3)` is exactly `|d|`, so the paper's
  `|D| = W` is an identity of continuous functions.  The hypotheses `alpha*beta > 0` and positivity
  of the two shift factors are exactly the below-spectrum condition `(1)`.
- `(5)`: `suzukiInverseDefect_posPart_sub_negPart`, `suzukiInverseDefect_posPart_nonneg`,
  `suzukiInverseDefect_negPart_nonneg` — the canonical Jordan decomposition `D = D_+ - D_-` with
  both parts positive operators, obtained as the positive/negative parts of `D`.
- `(6)`: `suzukiInverseDefect_add_negPart`, `suzukiInverseDefect_add_negPart_nonneg` —
  `D + D_- = D_+ >= 0`.
- `(7)`: `suzukiInverseDefect_add_two_negPart` — `D + 2 D_- = |D|`.
- `(8)`: `suzukiInverseDefect_add_nonneg_iff` — a commuting correction completes `D` to a positive
  operator exactly when it dominates `d` pointwise on the spectrum, proved through `cfc_nonneg_iff`.
- `(4)` product form: `suzukiInverseShiftFactor`, `suzukiInverseKreinDefect_eq_product` and
  `suzukiInverseDefectOperator_eq_product` — read in the inverse coordinate the shifted resolvent
  `(A - alpha)^(-1)` is the symbol `x/(1 - alpha x)`, so `D = alpha*beta * A^(-1)(A-alpha)^(-1)(A-beta)^(-1)`
  becomes a functional-calculus factorization of the defect symbol.
- `(5)` at symbol level: `posPart_cfc`, `posPart_suzukiInverseDefect`,
  `negPart_suzukiInverseDefect` — each spectral half of `D` is the functional calculus of the
  corresponding half of its symbol, not merely an abstract order-theoretic part.
- `(12)` kernel identity: `gram_add_negPart_eq_posPart` — `K_D + K_- = K_(D_+)` as an identity, with
  positivity then automatic.
- `(4)` modulus identity: `abs_cfc` and `abs_suzukiInverseDefect_eq_weight` — the absolute value of
  a continuous function of a self-adjoint operator is the functional calculus of the absolute value
  of the function, hence `|D| = W` at operator level.
- `(9)`: `negPart_le_of_add_nonneg` is the scalar core, and `negPart_cfc` together with
  `negPart_le_of_cfc_add_nonneg` give the operator statement — a commuting positive correction that
  completes the defect dominates `D_-`, which is therefore the Loewner-minimal such correction.
- `(11)` square-root factorization: `inner_eq_inner_sqrt` and `inner_negPart_eq_inner_sqrt` — the
  completion kernel is the Gram kernel of `sqrt(D_-)`, so the off-diagonal entries are genuine inner
  products of one family of vectors, not merely a positive form.
- `(10)`--`(12)`: `gram_re_nonneg_of_nonneg`, `gram_defect_add_negPart_nonneg`,
  `gram_negPart_nonneg` — every positive operator has a positive semidefinite Gram kernel on
  arbitrary finite node families, applied to `D + D_-` and to `D_-`.  This is the coherent assembly
  law: the off-diagonal entries are not free, they are Gram entries of the operator.

Targeted build green; axiom audit `[propext, Classical.choice, Quot.sound]` for every declaration
above.

Not formalized, and explicitly not proved here: the concrete Suzuki restricted-Weil source operator,
and the conjecture `(13)`, which Section 10 retires as a forced source identity in any case.

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

## Log

- 2026-08-01 — Sections 3-5 formalized unconditionally.  The unbounded-operator obstruction recorded
  in the old Section 9 is removed by working in the inverse coordinate on the bounded operator
  `A^(-1)`, which the card's own hypothesis `0 in rho(A)` supplies; the two spectral halves are the
  positive and negative parts, so no Borel calculus is needed.
- 2026-08-01 — equation-level sweep of Sections 3-5 found three displayed equations that the earlier
  card-level check had missed; `(4)`, `(9)` and `(11)` are now formal at operator level, so those
  sections are complete rather than merely represented.

### Lean progress — Section 4's uniqueness claim FORMALIZED

Section 9 mapped every numbered display to a declaration, but Section 4 makes one assertion beyond
`(9)`: that `D_-` is the **unique** Loewner-minimal commuting positive correction. The corpus had
only the lower bound `negPart_le_of_cfc_add_nonneg` (`C >= D_-`), which alone does not say `D_-`
belongs to the admissible class, and so does not give minimality or uniqueness. Now closed in
`RHTower/SuzukiNegativeProjectorCoherentCompletion.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `suzukiCommutingCompletions` : the admissible class — `C = c(B)` with `c` continuous on the
  spectrum, `c >= 0`, and `d + c >= 0` there. This is exactly the class quantified in `(8)`.
- `negPart_mem_commutingCompletions` : `D_-` is itself admissible (`negPart_cfc` for the
  representation, `d + d⁻ = d⁺ >= 0` for the domination).
- `negPart_isLeast_commutingCompletions` : `IsLeast (suzukiCommutingCompletions alpha beta B) D_-`
  — membership plus the existing lower bound, i.e. `D_-` is the least element, not merely a bound.
- `eq_negPart_of_minimal_commutingCompletion` : any Loewner-**minimal** admissible correction equals
  `D_-`. (Minimal is a priori weaker than least; the two coincide here precisely because a least
  element exists.)
- `isLeast_commutingCompletion_unique` : the least admissible correction is unique, by antisymmetry
  of the Loewner order.

Same pattern as the other cards in this folder: the inequality was formalized and the
membership-plus-uniqueness half of the extremality claim was not. Section 9's remaining explicit
exclusions (the concrete restricted-Weil source operator; the finite-rank statement for `P_-`;
conjecture `(13)`) are unchanged.
