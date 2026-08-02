# Route J: arbitrary two-atom reflection rigidity

**Status:** dependency-closed paper proof and unconditional Lean 4 formalization.

## Exact source problem

Let two distinct positive source times `t_1,t_2` carry nonzero real weights `a_1,a_2`.
At `z=u+iy`, define

```text
G(z)=sum_j a_j(1-exp(i t_j z)),
H(z)=sum_j a_j(-i t_j)exp(i t_j z).
```

A scalar horizontal screen has

```text
G(z)=1,       H(z)=i q,       q real.                  (1)
```

This is the literal signed atomic source law used by Route J. No abstract replacement matrix is
introduced.

## Theorem 1: scalar two-atom jets phase-lock

Write

```text
p_j=exp(-t_j y)>0,       s_j=sin(t_j u).
```

Imaginary value and real derivative parts of `(1)` give

```text
a_1 p_1 s_1+a_2 p_2 s_2=0,
a_1 t_1 p_1 s_1+a_2 t_2 p_2 s_2=0.                    (2)
```

Subtracting `t_2` times the first equation from the second gives

```text
a_1 p_1(t_1-t_2)s_1=0.
```

All factors except `s_1` are nonzero, hence `s_1=0`. Equation `(2)` then gives `s_2=0`.
Therefore every distinct, genuinely two-active-atom scalar screen lies on the half-turn lattice:

```text
sin(t_1 u)=sin(t_2 u)=0.                               (3)
```

This removes the quarter-turn support choice from the earlier result. It is a classification, not
an existence ansatz.

## Theorem 2: exact limiting fingerprints

Put

```text
g_t(u,y)=1-exp(-ty)cos(tu),
d_t(u,y)=-t exp(-ty)cos(tu).                           (4)
```

For mesh width `delta`, the real value and imaginary derivative equations are exactly

```text
(delta a_1)g_(t_1)+(delta a_2)g_(t_2)=delta,
(delta a_1)d_(t_1)+(delta a_2)d_(t_2)=delta q.          (5)
```

Suppose all geometric parameters and normalized weights converge,

```text
delta -> 0,   t_j -> t_(j,0),   u -> u_0,   y -> y_0,
delta a_j -> b_j,   delta q -> m.
```

Continuity in `(4)` and uniqueness of limits give

```text
g_(t_1)(u_0,y_0)b_1+g_(t_2)(u_0,y_0)b_2=0,
d_(t_1)(u_0,y_0)b_1+d_(t_2)(u_0,y_0)b_2=m.             (6)
```

If `m!=0`, the pair `(b_1,b_2)` is nonzero. Thus nonvanishing of the projective ray is forced by
the divisor charge; it is not an auxiliary coordinate assumption.

Equation `(3)` also passes to the limit for moving supports:

```text
sin(t_(1,0)u_0)=sin(t_(2,0)u_0)=0.                     (7)
```

## Theorem 3: reflected projective rigidity

Let

```text
epsilon_j=cos(t_(j,0)u_0),       epsilon_j^2=1.
```

The value coefficient has the exact reflection law

```text
g_t(u_0,-y_0)=-epsilon_t exp(t y_0) g_t(u_0,y_0).       (8)
```

For `t>0`, `y_0!=0`, and `epsilon_t^2=1`, the coefficient
`g_t(u_0,y_0)` cannot vanish: vanishing would imply
`exp(-t y_0)epsilon_t=1`; squaring and positivity give `exp(-t y_0)=1`, hence `y_0=0`.

Now let `(b_1,b_2)` and `(c_1,c_2)` be nonzero limiting charge rays at `y_0` and `-y_0`,
respectively. Assume projective coherence:

```text
b_1 c_2=c_1 b_2.                                      (9)
```

Both vectors lie in kernels of their value rows by `(6)`. Away from `y_0=0`, both row
coefficients are nonzero, so `(9)` forces the two value rows to be proportional. Using `(8)`,

```text
epsilon_1 exp(t_(1,0)y_0)
  =epsilon_2 exp(t_(2,0)y_0).                          (10)
```

Squaring `(10)` and using `epsilon_j^2=1` gives equality of the two positive exponentials.
Injectivity of the real exponential yields

```text
(t_(1,0)-t_(2,0))y_0=0.
```

The limiting times are distinct, hence

```text
y_0=0.                                                 (11)
```

## Xi consequence

For an Xi fibre `sigma`,

```text
u_0=Im sigma,             y_0=1/2-Re sigma.
```

Its functional-equation mate `1-conj(sigma)` has the same `u_0` and reflected height `-y_0`.
Therefore one coherent source law with two common convergent distinct positive support times,
two exact nonzero scalar charges, and a common projective normalized weight direction forces

```text
Re sigma=1/2.                                          (12)
```

Unlike the quarter-turn theorem, `(12)` is independent of support spacing. It closes the entire
convergent, separated, two-active-atom scalar subclass.

## Novelty and theatre audit

Prony/Vandermonde reconstruction and finite exponential interpolation are classical. For context,
Chunaev, *Interpolation by generalized exponential sums with equal weights*
(arXiv:1906.01332), studies general Padé/Prony interpolation, and Cuyt--Hou--Lee,
*Sparse Exponential Analysis from a Numerical Analysis Perspective* (JCAM 413, 2022), reviews
classical recovery of distinct exponentials from samples. Those works do not state the
source-specific conjunction `(3)`--`(12)`: scalar source-connection phase locking, anisotropic
divisor-charge normalization, and functional-equation reflection of the projective source ray.

No external priority is claimed from this search. New knowledge asserted here is corpus-specific:
quarter-turn geometry is unnecessary, nonzero ray status follows from charge, and every coherent
convergent separated two-atom scalar screen is already a critical-line selector.

This is not target-fitting theatre. Supports and weights form one pre-divisor law at both reflected
fibres; neither zero location nor multiplicity is inserted into a pointwise inverse. Conversely,
the theorem does not construct that coherent law and is not a proof of RH.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedTwoAtomReflectionRigidity.lean
```

Principal declarations:

```text
signedTwoAtomScalarJet_forces_halfTurns
tendsto_signedTwoAtomFingerprints
signedTwoAtomNormalizedPair_ne_zero_of_charge
tendsto_signedTwoAtomScalarPhaseLock
signedTwoAtomReflectionProjectiveFingerprint_rigid
signedTwoAtomCrossMeshReflection_rigid
xiReflectionCoherent_signedTwoAtom_profile_forces_criticalLine
```

Direct verification:

```text
lake env lean \
  GaloisForLFunctions/RHTower/XiCTaylorSignedTwoAtomReflectionRigidity.lean
```

No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs.

## Survivors not closed

Route J remains open. This theorem does not cover:

1. three or more asymptotically active signed atoms;
2. coalescing, escaping, or nonconvergent support times;
3. a source law whose leading normalized weights break reflection projectivity;
4. singular boundary terms;
5. relation-valued channels without a scalar logarithmic derivative.

These survivors remain Route J obligations rather than being reassigned.
