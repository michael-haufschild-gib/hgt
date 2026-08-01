# Suzuki Volterra Cartesian phase defect

- **ID:** `suzuki-volterra-cartesian-phase-defect`
- **Stage:** 2-fully-proven
- **Type:** FRONTIER REPRESENTATION THEOREM / FAILED PRODUCER / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `suzuki-homogeneous-projective-resolvent-plucker-lift`
- **RH used:** no
- **Computation used:** no
- **Primary source inputs:** Suzuki 2023, arXiv:2206.03682v4, Theorem 1.1(1); Suzuki 2026,
  arXiv:2606.09096v1, Sections 2, 6, and 8.2--8.3

## Problem attacked

For an odd compact Suzuki source `nu_lambda`, the physical right triangle is

```text
T_(lambda,R)(z)
 =integral_(-a)^a nu_lambda(y)e^(izy)
    integral_0^(a-y) k_lambda(t)e^(izt)dt dy,
k_lambda=g-lambda r_0,       r_0(t)=-|t|/2.             (1)
```

The corpus had treated admissible positivity of the symmetric pencil and the unresolved
one-sided triangle as if they were two views of the same positive operator.  They are not.  The
theorems below give the exact Cartesian decomposition and identify which component carries the RH
obstruction.

## Theorem A: physical right triangle is a causal Volterra observation `[PAPER-PROVED]`

For a real even locally integrable kernel `k` on `(-2a,2a)`, define on `I=(-a,a)`

```text
(V_k u)(x)=integral_(-a)^x k(x-y)u(y)dy,
(C_k u)(x)=integral_(-a)^a k(x-y)u(y)dy.                (2)
```

Then the right triangle in `(1)` is exactly

```text
T_(k,R)[u](z)=Fourier_I[V_k u](z).                      (3)
```

Moreover,

```text
(V_k^*u)(x)=integral_x^a k(x-y)u(y)dy,
V_k+V_k^*=C_k.                                         (4)
```

### Proof

In `(1)` put `x=y+t`.  The inequalities `0<=t<=a-y` become `-a<=y<=x<=a`.  Fubini gives

```text
integral_(-a)^a e^(izx)
  integral_(-a)^x k(x-y)u(y)dy dx,
```

which is `(3)`.  The adjoint formula follows by interchanging the lower triangle
`y<=x`; adding the two complementary triangles fills `I^2`.  Their common diagonal has measure
zero, proving `(4)`.

`(4)`'s integral content is formal as `causal_add_anticausal`, with `anticausal_eq_sub` its
subtractive form.  `causal_eq_indicator_integral` records the reduction `(3)` needs: writing the
moving upper limit as an indicator inside a fixed interval turns the causal triangle into an ordinary
product region, so the Fubini step there is a plain product-measure swap rather than a change of
variables.  What is still missing for `(3)` itself is the Fourier transform on the interval.  Stated on interval integrals the shared endpoint contributes nothing
automatically, so the measure-zero-diagonal step is not a separate argument — additivity over
adjacent intervals already carries it.

## Theorem B: exact Cartesian split `[PAPER-PROVED]`

Define the self-adjoint Volterra phase operator

```text
H_k:=-i(V_k-V_k^*).                                    (5)
```

Then

```text
V_k=(C_k+i H_k)/2,
-i V_k=(H_k-i C_k)/2.                                  (6)
```

For Suzuki's shifted kernel this gives

```text
C_lambda=C_g-lambda C_(r0),
H_lambda=H_g-lambda H_(r0),                            (7)

-i T_(lambda,R)(z)
 =1/2 Fourier_I[H_lambda nu_lambda](z)
  -i/2 Fourier_I[C_lambda nu_lambda](z).               (8)
```

The first term in `(8)` is not a positivity remainder chosen after the fact.  It is the canonical
skew-Cartesian coordinate of the actual time-ordered prime--Gamma convolution.

**`(5)`--`(6)` are formal as identities**, in
`formal/GaloisForLFunctions/RHTower/SuzukiVolterraCartesianPhaseDefect.lean`:
`isSelfAdjoint_volterraSymmetric` and `isSelfAdjoint_volterraPhase` show both Cartesian coordinates
are self-adjoint for *any* bounded operator, and
`two_smul_eq_volterraSymmetric_add_I_smul_volterraPhase` is `(6)`.  The response theorems in this
module previously took the split as a hypothesis; it is a theorem, so the Cartesian coordinates exist
for every causal observation and the phase is a genuine self-adjoint coordinate.

`inner_volterra_cartesian` closes the loop: reading the three responses as pairings of a fixed
observation vector against the operator's Cartesian coordinates, the hypothesis those theorems carry
*is* the operator identity, so it never has to be assumed.

### Proof

The kernel of `V_k-V_k^*` is `sgn(x-y)k(x-y)`.  It is real antisymmetric, hence skew-adjoint;
therefore `(5)` is self-adjoint.  Solving `(4)--(5)` for `V_k` gives `(6)`.  Equations `(7)--(8)`
follow by linearity and `(3)`.

## Theorem C: admissible positivity and the RH carrier are complementary components
`[PAPER-PROVED]`

Let `R u(x)=u(-x)`.  Evenness of `k` gives

```text
R V_k R=V_k^*.                                         (9)
```

If `u` is odd, then `C_k u` is odd and `H_k u` is even.  Consequently `(8)` separates by
reflection parity:

```text
Even_z[-i T_(lambda,R)]
 =1/2 Fourier_I[H_lambda nu_lambda],                   (10)

Odd_z[-i T_(lambda,R)]
 =-i/2 Fourier_I[C_lambda nu_lambda].                  (11)
```

**`(9)`'s parity consequence is formal.**  `volterraSymmetric_reflection` and
`volterraPhase_reflection` show that a reflection conjugating the operator to its adjoint fixes the
symmetric coordinate and *negates* the phase, via `reflection_adjoint_conj`.  So the two coordinates
have opposite reflection parity — which is exactly why `(10)` and `(11)` separate, and why a
positivity statement about one parity sector carries no information about the other.

The transfer to vectors is formal too: `volterraSymmetric_apply_odd` and `volterraPhase_apply_odd`
show that on an odd vector the symmetric coordinate stays odd while the phase becomes even, which is
the card's "if `u` is odd, then `C_k u` is odd and `H_k u` is even" — the statement `(10)`--`(11)`
are read off from.

Suzuki admissibility `lambda<lambda_a` makes the compressed symmetric pencil

```text
S_(a,lambda)=G_a-lambda(-Delta_N)^(-1)                 (12)
```

positive.  It therefore controls `(11)`, the already classified sine-clock parity.  The complete
even Carleman pole carrier in `(10)` is instead the boundary response of self-adjoint
`H_lambda`.  Positivity of `(12)` supplies no sign for it.

More explicitly, if `P_0` is projection to zero-mean functions, then

```text
P_0 C_g P_0=G_a,
P_0 C_(r0) P_0=(-Delta_N)^(-1),                        (13)
```

because the inverse Neumann kernel differs from `r_0(x-y)` by

```text
x^2/(4a)+y^2/(4a)+a/6.                                 (14)
```

On zero-mean inputs `(14)` produces only a constant, killed by `P_0`.  Thus the tempting
`Volterra accretivity -> triangle Pick positivity` producer is false at operator-coordinate
level: accretivity belongs to `C_lambda=V_lambda+V_lambda^*`, while the unknown even response is
`H_lambda=-i(V_lambda-V_lambda^*)`.

### Proof

From `(9)` and `Ru=-u`,

```text
V_k^*u=R V_k R u=-R V_k u.
```

Hence `(V_k+V_k^*)u` is odd and `(V_k-V_k^*)u` is even.  Fourier transformation preserves these
reflection parities, proving `(10)--(11)`.  Formula `(13)` for `g` is Suzuki's definition of
`G_a`.  For `r_0`, subtract its kernel from the Neumann kernel and use `integral_I u=0`; the
`x^2` and constant terms vanish, while the `y^2` term is constant in `x` and is removed by
`P_0`.  This proves `(13)`.

## Theorem D: Neumann phase is exactly rank-one projective holonomy `[PAPER-PROVED]`

Let

```text
mu_j=integral_I y^j u(y)dy.
```

For `r_0(t)=-|t|/2`, direct substitution in the antisymmetric kernel gives

```text
(V_(r0)-V_(r0)^*)u(x)=-x mu_0/2+mu_1/2.               (15)
```

For odd `u`, `mu_0=0`, so

```text
H_(r0)u=-i mu_1/2,                                    (16)
```

a constant.  If `W(z)=Fourier_I[u](z)`, then `W'(0)=i mu_1`, and `(10)` becomes

```text
Even_z[-i T_(r0,R)](z)
 =-W'(0) sin(az)/(2z).                                 (17)
```

After division by `W`, `(17)` is exactly the already proved full-frequency Neumann holonomy

```text
-W'(0) sin(az)/(2z W(z)).                              (18)
```

Thus the Neumann comparison contributes no hidden infinite-dimensional positive operator to the
RH carrier.  Its entire phase sector is the first-moment-to-constant rank-one channel, and its
nontrivial two-shift effect is projective motion of `W_lambda`.

### Proof

Since `sgn(t)r_0(t)=-t/2`, the kernel of `V_(r0)-V_(r0)^*` is `-(x-y)/2`.  Integration gives
`(15)`.  Oddness gives `(16)`.  Fourier transformation of the constant on `(-a,a)` is
`2 sin(az)/z`; substitute `W'(0)=i mu_1` to obtain `(17)--(18)`.

## Theorem E: relative phase defect and homogeneous Plucker chord `[PAPER-PROVED]`

Let the shift states be an ordinary resolvent orbit

```text
A u_lambda-lambda u_lambda=e.                          (19)
```

Let `H_g,H_r` now denote the two Volterra phase operators in the same source coordinate and put

```text
Omega:=H_g-H_r A.                                      (20)
```

Then the shifted phase response homogenizes exactly:

```text
(H_g-lambda H_r)u_lambda
 =Omega u_lambda+H_r e.                                (21)
```

For a Fourier boundary observation `D_z`, define

```text
n_lambda(z)=1/2 D_z((H_g-lambda H_r)u_lambda),
d_lambda(z)=D_z(u_lambda).                             (22)
```

For distinct shifts `alpha,beta`, put

```text
v=(A-alpha)^(-1)(A-beta)^(-1)e.                        (23)
```

The division-free projective chord of the actual even Volterra carrier is

```text
n_beta d_alpha-n_alpha d_beta
 =(beta-alpha)/2 *
   { D_z(Omega v)D_z(A v)
    -D_z(Omega A v)D_z(v)
    -D_z(H_r e)D_z(v) }.                               (24)
```

Equation `(24)` is the concrete source specialization of the homogeneous resolvent Plucker lift.
It identifies two and only two live objects:

1. the Euler--Gamma relative phase defect `Omega` on spectral pairs;
2. the rank-one Neumann homogeneous coordinate `H_r e`.

### Proof

Apply `H_r` to `(19)` and rearrange to obtain `(21)`.  In the notation of the homogeneous
Plucker theorem, take

```text
B=(1/2)D_z Omega,       c=(1/2)D_z(H_r e),       D=D_z.
```

The resolvent identities give

```text
u_beta=A v-alpha v,       u_alpha=A v-beta v.
```

Expanding the alternating minor yields `(24)`.

## Theorem F: actual affine jump carrier is marked Volterra secant `[PAPER-PROVED]`

Equation `(24)` controls projective difference, but Suzuki jump uses weighted affine intercept

```text
I_(alpha,beta)q=[beta q_alpha-alpha q_beta]/(beta-alpha). (25)
```

Set

```text
B_z=(1/2)D_z Omega,       c_z=(1/2)D_z(H_r e),
x=B_z(v), X=B_z(Av),      y=D_z(v), Y=D_z(Av).          (26)
```

Then the exact division-free source identity is

```text
beta n_alpha d_beta-alpha n_beta d_alpha
 =(beta-alpha)Q_(alpha,beta),                           (27)

Q_(alpha,beta)
 =(X+c_z)Y-(alpha+beta)xY+alpha beta x y.              (28)
```

Away from endpoint characteristic divisors,

```text
I_(alpha,beta)q
 =Q_(alpha,beta)/[(Y-beta y)(Y-alpha y)].              (29)
```

Thus `Omega` is the physical source operator, but its complete jump carrier is marked tensor
`(28)`, not alternating blade `(24)` alone.  It retains diagonal, symmetric-pair, alternating-pair,
and homogeneous Neumann sectors.

### Proof

Equations `(21)` and `(26)` give

```text
n_alpha=X-beta x+c_z,       n_beta=X-alpha x+c_z,
d_alpha=Y-beta y,           d_beta=Y-alpha y.
```

Direct expansion proves `(27)--(28)`; division proves `(29)`.  This is the Volterra-phase
specialization of `suzuki-projective-affine-secant-tensor-lift.md`.

## Hostile audit

### C1. Symmetric-pencil accretivity produces the right-sheet Pick kernel `[FALSIFIED]`

Admissibility proves positivity of `C_lambda`, hence of `V_lambda+V_lambda^*`.  Equations
`(10)--(11)` show this is the wrong reflection coordinate: it controls the known odd clock, while
the RH-bearing even carrier is the independent self-adjoint operator `H_lambda`.

**Positive survivor:** exact Cartesian split `(8)` and phase carrier `(10)`.

### C2. Neumann positivity supplies the missing completion `[FALSIFIED]`

Equation `(16)` proves its phase operator is only the moment-to-constant rank-one map on the odd
source sector.  Its complete contribution is already `(18)`.

**Positive survivor:** exact projective holonomy and homogeneous coordinate in `(24)`.

### C3. Weighted negative projector of `A` is the canonical source producer `[FALSIFIED]`

That projector repairs a signed *linear* resolvent defect.  Actual Suzuki motion is the
projective phase chord `(24)`.  It is blind on one invariant spectral line and depends on the
boundary Plucker orientation of `Omega`; a nonzero negative spectral coordinate therefore need
not create any projective phase debt.

**Positive survivor:** finite-Morse/projector completions remain valid sufficient external
majorants if independently dominated by the source, but they are not identities forced by the
physical triangle.

### C4. Homogeneous Plucker blade is complete affine-sewn carrier `[FALSIFIED]`

Replace `B_z` by `B_z+delta D_z`.  Every alternating minor `(24)` is unchanged, but every quotient
`q_lambda` and affine intercept `(25)` increases by `delta`.  Equivalently, marked tensor `(28)`
changes by `delta (Y-beta y)(Y-alpha y)`.  Therefore exterior-square positivity cannot determine
the actual jump even after physical phase operator is known.

**Positive survivor:** exact marked Volterra secant `(28)`.

## Exact frontier the corpus cannot solve

### `SUZUKI-MARKED-SECANT-CD-WELD` `[CONJECTURE]`

For one recurrence-selected aperture and admissible shift pair, use the actual prime--Gamma
kernel `g`, its canonical causal order, and the physical odd deficiency sources.  Prove a
Christoffel--Darboux/Green identity whose left side is gauged Pick polarization of marked phase
tensor `(28)` plus global Xi multiplier, and whose right side is a positive source Gram.

The source marking is fixed by

```text
relative phase operator Omega=H_g-H_(r0)A
+ rank-one moment coordinate H_(r0)e,
+ affine secant marks (alpha+beta, alpha beta).          (30)
```

This is not abstract finite-aperture positivity.  `H_g` is explicitly source-defined by

```text
(H_g u)(x)=-i integral_I sgn(x-y)g(x-y)u(y)dy.          (31)
```

Writing `q_g(t)=g(t)/|t|` off the diagonal gives the further exact commutator form

```text
H_g=-i[X,Q_g],                                         (32)
```

where `X` is multiplication by `x` and `Q_g` has kernel `q_g(x-y)`.  Thus the missing identity is
a prime--Gamma causal commutator theorem, not a free Gram completion.

One negative principal minor of polarized marked tensor `(28)` falsifies conjecture.  A rational
functional-equation--Schwarz orbit insertion must also fail the source identity because it changes
the global Xi pole carrier without changing the finite local symmetric shell.

If this identity is proved, existing Loewner-gap connector gives full jump Pick kernel; existing
pole tomography excludes every nonreal Xi zero and proves RH.

## New scientific conclusion

The actual frontier is now localized to one operator:

```text
known admissible energy:       C_lambda=V_lambda+V_lambda^*
known Neumann holonomy:        H_(r0), rank one on odd sources
unknown RH-bearing phase:      H_g=-i(V_g-V_g^*)
physical source invariant:     Omega=H_g-H_(r0)A
complete jump carrier:         marked secant Q_(alpha,beta). (33)
```

No estimate is missing.  Missing theorem is an exact positive Green identity for the
prime--Gamma causal commutator `(32)` evaluated in marked secant `(28)`.

## Formal target

Formalize Cartesian response algebra, phase homogenization, rank-one Neumann orientation,
complex marked-secant specialization, and RH source-germ connector in
`RHTower/SuzukiVolterraCartesianPhaseDefect.lean`.

## Log

- 2026-08-01 — `(5)`--`(6)` formalized as identities.  The module's response theorems carried the
  Cartesian split `2V = C + iH` as a *hypothesis*, so the fact justifying it — that `V + V*` and
  `-i(V - V*)` are self-adjoint and recombine to `2V` — was assumed rather than proved.  It is an
  identity for any bounded operator: `isSelfAdjoint_volterraSymmetric`,
  `isSelfAdjoint_volterraPhase`, `two_smul_eq_volterraSymmetric_add_I_smul_volterraPhase`.  This is
  what entitles the card to call the phase "the canonical skew-Cartesian coordinate" rather than a
  remainder.  Three new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the response hypothesis discharged (`inner_volterra_cartesian`).  Pairing the operator
  identity `(6)` against a fixed observation vector reproduces exactly the Cartesian hypothesis the
  response theorems carry, so those theorems now rest on a proved identity rather than an assumption
  about the observation.  Pairing on the *right* avoids the conjugation that mathlib's
  conjugate-linear-in-the-first-argument convention would introduce.  One new declaration, targeted
  build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(9)`'s parity consequence formalized.  A reflection conjugating the operator to its
  adjoint fixes the symmetric Cartesian coordinate and negates the phase
  (`volterraSymmetric_reflection`, `volterraPhase_reflection`), so the two coordinates have opposite
  reflection parity.  That is the mechanism behind the separation `(10)`--`(11)`, and it makes
  precise the card's central point: positivity of the admissible symmetric pencil controls one parity
  sector and therefore supplies no sign for the other.  The whole argument follows from the single
  relation `R T R = T*` — evenness of the kernel is used nowhere else.  Three new declarations,
  targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the parity separation completed on vectors.  `volterraSymmetric_comm_reflection` and
  `volterraPhase_anticomm_reflection` turn the operator parities into a commutation and an
  anticommutation with the reflection, and `volterraSymmetric_apply_odd` /
  `volterraPhase_apply_odd` then give the card's "if `u` is odd, then `C_k u` is odd and `H_k u` is
  even" — the sentence `(10)`--`(11)` are read off from.  With the Cartesian identity and `(9)`'s
  parity from the previous entries, Theorem C's separation mechanism is formal end to end; what the
  card leaves open is whether any positivity reaches the even sector.  Four new declarations,
  targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(4)`'s integral content formalized (`causal_add_anticausal`, `anticausal_eq_sub`):
  the causal and anticausal halves of the convolution recombine into the full one.  Worth recording
  that the card's "their common diagonal has measure zero" is not needed as a separate step once the
  statement is phrased on interval integrals — additivity over adjacent intervals already handles the
  shared endpoint.  With Theorems A `(4)`, B `(5)`--`(6)` and C `(9)`--`(11)` now formal, this card's
  algebraic content is complete; what remains is the Fourier identification `(3)` and the open source
  frontier.  Two new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the reduction `(3)` needs is formal (`causal_eq_indicator_integral`,
  `anticausal_eq_sub_indicator`): the moving upper limit becomes an indicator factor inside a fixed
  interval, so the card's change of variables `x = y + t` followed by Fubini is replaceable by an
  ordinary product-measure swap on a fixed square.  That reformulation is the part worth having —
  what remains for `(3)` is the Fourier transform on the interval, which is a construction rather
  than an identity.  Two new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
