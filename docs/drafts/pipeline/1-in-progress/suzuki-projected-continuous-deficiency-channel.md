# Suzuki projected continuous deficiency channels and source-exact exterior sewing

- **ID:** `suzuki-projected-continuous-deficiency-channel`
- **Stage:** 1-in-progress
- **Type:** SOURCE CORRECTION / CONJECTURE / FRONTIER ATTACK
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, Sections 8.2--8.3
- **Parents:** `suzuki-exterior-pole-tomography-neumann-boundary`,
  `suzuki-admissible-two-shift-affine-sewing`
- **RH used:** no
- **Computation used:** no

## Actual corpus frontier

The corpus has removed source-shift selection, gauge, pair choice, and characteristic-divisor
ambiguity.  Its remaining RH-bearing statement is:

```text
construct one affine-sewn exterior observable from two actual admissible
finite-aperture Suzuki source channels, independently of the Xi quotient,
and prove that its continuation is holomorphic at every nonreal point.       (F)
```

The first clause of `(F)` still depends on Suzuki's claimed passage from the projected operator
`G_a=P_a G P_a` to an unprojected convolution equation.  This card audits and repairs that passage
before attacking the holomorphy clause.

## Source inconsistency

Let

```text
L0 = {u in L2(-a,a) : integral u=0},
G_a=P_a G P_a : L0 -> L0,
K_a=(-Delta_N)^(-1) : L0 -> L0,
S_(a,eta)=G_a-eta K_a.                                  (1)
```

Therefore every ordinary `L2` value of `S_(a,eta)` has zero mean.  Section 8.3 instead writes

```text
S_(a,eta)v_+ = e^x+i,
S_(a,eta)v_- = e^(-x)-i.                                (2)
```

Both right sides have nonzero mean for every `a>0`.  Thus `(2)` cannot hold in `L0`.  The raw TeX
also replaces `G_a=P_aGP_a` by the kernel `g(x-y)` without the output projection.  This is the
exact source of the mismatch.

## Conjecture A: projected deficiency normalization

Put

```text
s_a=sinh(a)/a.                                           (3)
```

The correctly normalized ordinary continuous-kernel deficiency vectors should satisfy

```text
S_(a,eta) w_+ = e^x-s_a,
S_(a,eta) w_- = e^(-x)-s_a.                              (4)
```

More generally, if the exponential coefficient of an adjoint solution at `z!=0` is normalized to
one, its projected image must be

```text
S_(a,eta)w_z
 = e^(-izx)-m_a(z),
m_a(z)=(1/(2a)) integral_(-a)^a e^(-izt) dt.             (5)
```

The constant in the adjoint equation is then `z m_a(z)`, not an independently normalizable `1`.
Applying `-d^2/dx^2` to `(5)` gives

```text
T_(a,eta)w_z=z^2 e^(-izx).                               (6)
```

Hence, whenever comparison with the distribution-kernel vector is domain-valid, the multiplier is
`z^2`; at `z=+-i` it is `-1`.  The printed factor `-lambda^2` has the wrong sign if `lambda` denotes
the adjoint spectral variable, and is unrelated to the form shift if it denotes `eta`.

## Conjecture B: rank-one interior correction

Let

```text
r0(x-y)=-|x-y|/2,
N_a(x,y)=(x^2+y^2)/(4a)-|x-y|/2+a/6.                    (7)
```

For `v in L0`, set `M2(v)=integral y^2 v(y)dy`.  Then

```text
K_a v = r0*v + M2(v)/(4a),                              (8)
P_a(g*v)=g*v-avg_a(g*v).                                (9)
```

Consequently the global shifted convolution `k_eta*v=(g-eta r0)*v` satisfies on `[-a,a]`

```text
k_eta*v
 =S_(a,eta)v+c_(a,eta)(v),
c_(a,eta)(v)=avg_a(g*v)+eta M2(v)/(4a).                 (10)
```

For the corrected deficiency vectors `(4)`, the actual interior channels are therefore

```text
k_eta*w_+ = e^x+c_+,
k_eta*w_- = e^(-x)+c_-,                                (11)
```

with two source-computable scalars.  Thus the projection error is finite rank, but the constants
are not the universal `+-i` printed in the source.

## Conjecture C: source-exact affine exterior observable

Use the compactly supported characteristic distributions built from `w_+`, `w_-`, their endpoint
traces, and a unit phase.  Split each global shifted convolution into its interval restriction and
its exterior restriction.  For two arbitrary admissible shifts, apply the already proved affine
sewing law to these actual exterior distributions.  Fourier multiplication becomes convolution,
so the sewn distribution is defined entirely from

```text
g, r0, P_a, K_a, w_(alpha,+-), w_(beta,+-),             (12)
```

without evaluating or dividing by Xi.  Its meromorphic Fourier continuation, wherever defined,
must equal the canonical affine-sewn germ modulo the explicit entire interval terms from `(10)`.

If proved, this closes the source-identification clause of `(F)`.  The sole remaining theorem is
then nonreal holomorphy of this concrete exterior distribution.

## Pre-registered hostile tests

- [x] **T1 range:** printed right sides in `(2)` must have zero mean.  They do not; printed system
      is falsified as an ordinary `L0` Fredholm equation.
- [x] **T2 projection:** raw source defines `G_a=P_aGP_a` and later omits the output projection.
- [ ] **T3 domain:** derive `(4)` from the `D^*S D=T` form identity without applying an unbounded
      operator outside its domain.
- [ ] **T4 normalization:** verify the signs in `(5)`--`(6)` under Suzuki's Fourier and `D=i d/dx`
      conventions.
- [ ] **T5 Neumann correction:** prove `(8)` pointwise for every zero-mean source.
- [ ] **T6 source purity:** construct the sewn exterior distribution without Xi or its divisor.
- [ ] **T7 continuation:** distinguish distributional boundary Fourier identities from genuine
      meromorphic continuation.
- [ ] **T8 novelty:** search Suzuki/Krein--Langer and boundary-triplet literature for this exact
      projection correction and two-shift exterior construction.
- [ ] **T9 Lean:** formalize only the dependency-closed exact survivor; no analytic placeholder.

## Falsified stronger conjecture and positive survivor

**Falsified:** Suzuki's displayed ordinary Fredholm system `(2)` and the universal phase-`-1`
interior cancellation derived from its constants.

**Killing mechanism:** zero-mean range of `P_aGP_a-eta K_a`.

**Positive survivor:** the corrected channel is not uncontrolled.  Output projection and the
finite Neumann inverse introduce exactly one scalar per deficiency channel, as in `(10)`--`(11)`.
All nonconstant interior structure remains the two exponentials.  This finite-rank correction can
be carried explicitly through affine sewing rather than estimated.

## Gates

- [x] 0 -> 1: source-pure statement, precise contradiction, replacement conjectures, hostile tests
- [ ] 1 -> 2: dependency-closed proof of `(4)`--`(11)` and source-exact exterior construction
- [ ] 2 -> 3: exact survivor formalized; direct Lean check, module build, lint, axiom audit
- [ ] 3 -> 4: external referee-level novelty audit and standalone note

## Log

- 2026-07-21 -- source range mismatch discovered; printed continuous Fredholm equations falsified;
  projected exponential and rank-one interior correction conjectured.
