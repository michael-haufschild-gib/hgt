# Xi radial-Jensen Schur-capacity exact norm-gap law

- **ID:** `xi-radial-jensen-schur-capacity-rigidity`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE] [BRIDGE] [NOT AN RH PROOF]`
- **Parents:** `xi-radial-jensen-mass-central-curvature`,
  `prime-arch-scaled-hausdorff-divisor-value-law`,
  `shifted-reciprocal-moments-determine-divisor`,
  `xi-global-reflection-defect-energy`,
  `xi-endpoint-strong-height-gap`,
  `xi-offline-quartet-thermal-orientation-one-eighty-four`
- **Statement:** The disk-Schur norm of the fixed prime--Gamma moment functional is not an open
  RH-sized quantity.  It is unconditionally equal to the central prime--Gamma curvature, with
  constant extremizer `1`.  Its deficit from radial Jensen mass is exactly one half of the global
  Xi reflection-defect energy.

## Setup

For a multiplicity copy `q` of the Xi divisor, put

```text
u_q = xiZeroCopyReciprocalSquare(q) = xiSpectralPoint(q)^(-2).
```

The formal corpus proves

```text
sum_q |u_q| < infinity,
m_n := normalizedPrimeArchMoment(n) = sum_q u_q^(n+1),
J_Xi := xiCenteredRadialJensenMass = sum_q |u_q|,
m_0 = primeArchCentralCurvature > 0.                         (1)
```

For a polynomial `P` in `C[X]`, define

```text
L_Xi(P) = sum_n coeff(P,n) m_n = sum_q u_q P(u_q).           (2)
```

Let

```text
||P||_D = sup_(|z|<=1) |P(z)|,
S_Xi = sup { |L_Xi(P)| : P in C[X], ||P||_D <= 1 }.          (3)
```

The immediate triangle bounds are

```text
m_0 <= S_Xi <= J_Xi
```

The narrow-sector theorems already in the corpus determine `S_Xi` exactly.

## General narrow-sector Schur lemma

Let `(u_j)` be a countable complex family satisfying

```text
sum_j |u_j| < infinity,
|u_j| <= R < 1,
M := sum_j u_j is positive real.
```

Write

```text
A := sum_j |u_j|^2.
```

Assume the small-sector balance

```text
2 A <= (1-R) M.                                               (4)
```

Then every Schur function `f`, and in particular every disk-contractive polynomial, satisfies

```text
|sum_j u_j f(u_j)| <= M.                                     (5)
```

Consequently the norm of the weighted evaluation functional on the disk algebra, and on
`H^infinity`, is exactly `M`; the constant function `1` is an extremizer.

### Proof

Rotate `f` by a unimodular scalar so that its weighted value is nonnegative real.  This does not
change the Schur norm.  Put

```text
c=f(0),  t=|c|.
```

If `t=1`, the maximum-modulus principle makes `f` constant and `(5)` is immediate.  Suppose
`t<1`.  Schwarz--Pick, written through the disk automorphism carrying `c` to zero, gives

```text
|f(z)-c| <= |z| (1-t^2)/(1-t|z|).                            (6)
```

Therefore

```text
|sum_j u_j f(u_j)|
 = Re(sum_j u_j f(u_j))
 <= t M + (1-t^2) A/(1-tR).                                  (7)
```

For `0<=t<1`,

```text
(1+t)/(1-tR) <= 2/(1-R).
```

Using `(4)`,

```text
(1-t^2) A/(1-tR)
 = (1-t) A(1+t)/(1-tR)
 <= (1-t) M.
```

Substitution in `(7)` proves `(5)`.  The constant function `1` has value `M`, proving exactness.

This lemma is a direct Schwarz--Pick consequence.  It requires neither a normal-family limit nor
an interpolant for the atom phases.

## Verification for the Xi atom family

Set

```text
R = 2/41,
J = sum_q |u_q|,
A = sum_q |u_q|^2,
M = m_0.
```

### 1. Small radius

`xiZeroCopy_fortyOne_div_two_lt_im_sq` proves

```text
41/2 < Im(rho_q)^2.
```

Since the centered modulus dominates the absolute ordinate,

```text
|u_q| < 2/41 = R.                                             (8)
```

Hence

```text
A <= R J.                                                     (9)
```

### 2. Narrow positive sector

The formal laws `xiThermalNode_pos` and
`xiThermalOrientationTerm_le_one_over_eightyFour_node_sq` say

```text
x_q := Re(u_q) > 0,
Im(u_q)^2 <= x_q^2/84.
```

Thus

```text
|u_q|^2 <= (85/84) x_q^2,
(84/85)|u_q| <= x_q.                                         (10)
```

Summing `(10)` and using the real zeroth-moment identity gives

```text
(84/85) J <= M.                                              (11)
```

### 3. Small-sector balance

Equations `(9)` and `(11)` give

```text
2A <= (4/41)J
   <= (39/41)(84/85)J
   <= (1-R)M.                                                 (12)
```

The general lemma applies.  Therefore

```text
S_Xi = m_0 = primeArchCentralCurvature.                       (13)
```

This is unconditional.

## Exact reflection-energy norm gap

The formal radial Jensen and reflection-defect laws give

```text
J_Xi = xiReciprocalHermitianMass,
xiGlobalReflectionDefectEnergy
  = 2 (xiReciprocalHermitianMass-primeArchCentralCurvature).
```

Combining these identities with `(13)` yields the exact value relation

```text
J_Xi-S_Xi =
  xiCenteredRadialJensenMass-primeArchCentralCurvature
  = xiGlobalReflectionDefectEnergy/2.                         (14)
```

Consequently

```text
S_Xi = J_Xi
  <-> xiGlobalReflectionDefectEnergy = 0
  <-> RiemannHypothesis.                                     (15)
```

The significant point is not the final equivalence, which was already known through the mass--
curvature law.  It is the exact decomposition `(14)`: the analytic Schur functional reads only
the holomorphic source curvature, and its missing trace-norm mass is precisely the anti-holomorphic
reflection energy.

## Boundary quotient form

Define

```text
G_Xi(w)=sum_(n>=0) m_n w^n
       =sum_q u_q/(1-wu_q),
g_Xi(e^(it))=G_Xi(e^(-it)).                                  (16)
```

The radius bound `(8)` gives uniform convergence on the closed unit disk.  Coefficient pairing
gives

```text
L_Xi(P)=integral_T P(zeta) g_Xi(zeta) dm(zeta).               (17)
```

The standard `L^1/H^1_0`--`H^infinity` duality and `(13)` now give the previously open quotient
norm exactly:

```text
||[g_Xi]||_(L^1(T)/H^1_0(T)) = primeArchCentralCurvature.     (18)
```

The even normalized continued prime--Gamma germ has the same coefficients:

```text
normalizedTraceMomentGerm(continuedPrimeArchSourceRelativeTrace)(z)
  = G_Xi(z^2)
```

as a germ at zero.  Thus `(18)` is a fixed source value relation, not a divisor-phase
interpolation statement.

## Operator form

Let

```text
D_Xi = xiReciprocalSquareOperator.
```

It is the product of two Hilbert--Schmidt operators and hence trace class.  It is diagonal with
eigenvalues `u_q`.  On paper,

```text
Tr(D_Xi) = m_0,
||D_Xi||_1 = J_Xi,
Phi_Xi(P) := Tr(D_Xi P(D_Xi)) = L_Xi(P).                      (19)
```

Therefore `(13)`--`(14)` become

```text
||Phi_Xi||_(A(D)^*) = Tr(D_Xi) = primeArchCentralCurvature,
2 (||D_Xi||_1-||Phi_Xi||_(A(D)^*))
  = xiGlobalReflectionDefectEnergy.                          (20)
```

This gives a positive structural description: the complete orientation datum is the excess of
the trace norm over the norm visible to the analytic functional calculus.  Any successful
operator proof must positively couple `D_Xi` to its adjoint, absolute value, or polar phase; the
analytic algebra generated by `D_Xi` alone has the exact norm in `(20)` even off RH.

## Finite Caratheodory--Fejer exhaustion

Let a Schur function have Taylor series

```text
f(z)=sum_(k>=0) a_k z^k
```

and define

```text
S_Xi,N = sup { |sum_(k=0)^N m_k a_k| : f is Schur }.          (21)
```

Caratheodory--Fejer identifies the admissible prefixes with the vectors for which the associated
lower-triangular coefficient Toeplitz matrix is contractive.  Moreover, `(8)` gives

```text
|m_k| <= J_Xi R^k.
```

Since every Schur coefficient has modulus at most one, `(13)` implies the corrected finite bound

```text
0 <= S_Xi,N-primeArchCentralCurvature
   <= J_Xi R^(N+1)/(1-R).                                    (22)
```

Thus the finite Toeplitz/trace-norm dual certificates converge to the central curvature, not to
the radial Jensen mass.  Constructing certificates with limiting norm `J_Xi` is impossible unless
RH is already true.

## Consequence for top-down proof search

The chain

```text
source quotient-norm computation -> Schur saturation -> RH
```

does not supply an independent open producer because the quotient norm is already forced by the
narrow source sector and equals `m_0`.  The positive theorem is the exact constraint--orientation
split

```text
analytic source norm = central curvature,
trace norm-analytic source norm = reflection energy/2.        (23)
```

The live input is therefore not another holomorphic value relation in the same disk algebra.  It
must be a source theorem that controls the trace norm or couples the analytic source to the
anti-holomorphic reflection channel.

## Explicit circle-state descendant

The companion paper theorem
`prime-arch-explicit-circle-state-reflection-law.md` now realizes the complete normalized moment
sequence as the Fourier coefficients of one explicit source density

```text
w_Xi(e^(it))=primeArchCentralCurvature
  +2*sum_(n>=1) normalizedPrimeArchMoment(n)*cos(n*t).
```

It proves the unconditional bounds

```text
(734/819)*primeArchCentralCurvature <= w_Xi
  <= (904/819)*primeArchCentralCurvature
```

and constructs the canonical unitary/reflection carrier on `L^2(T,w_Xi dm)`.  This positively
closes carrier existence and ordinary Toeplitz positivity.  The reflected Gram matrix is exactly
the prime--Gamma Hankel matrix, so the remaining input is not a metric-completion problem: it is
the weighted cosine--sine orientation inequality, equivalently radial Poisson disintegration of
`w_Xi`.  An exact analytic-density counterfamily shows that the large Schur/coercivity margin
cannot imply that transverse inequality by norm continuity alone.

## Literature calibration

The Schwarz--Pick estimate used in `(6)` is classical; a modern operator treatment is Anderson--
Rovnyak, [On Generalized Schwarz--Pick Estimates](https://doi.org/10.1112/S0025579300000085).
The quotient-duality setting in `(18)` is standard; see Hensgen,
[Extremal Problems for the Vector-Valued L1/H01, H-infinity Duality](https://doi.org/10.1006/jath.1996.0013).
For the finite coefficient realization, see Ball--Gohberg--Rodman,
[J Contractive Matrix Functions, Reproducing Kernel Hilbert Spaces and Interpolation](https://bookstore.ams.org/CBMS/71),
Chapter 6.  The contribution here is the corpus-specific combination of the exact Xi radius,
sector, moment, radial-Jensen, and reflection-energy laws.

## Gates

- [x] 0 -> 1: fixed prime--Gamma moment functional placed in one disk-algebra chart
- [x] 1 -> 2: general small-sector constant-extremizer lemma proved on paper by Schwarz--Pick
- [x] 1 -> 2: Xi radius and sector bounds verified from existing formal declarations
- [x] 1 -> 2: quotient norm and reflection-energy deficit identified exactly
- [x] 1 -> 2: finite Caratheodory--Fejer target corrected to convergence toward central curvature
- [ ] 2 -> 3: formalize the reusable small-sector Schur lemma and its Xi specialization
- [ ] proof input: find a source theorem controlling `||D_Xi||_1`, or coupling `D_Xi` to its
  adjoint/polar phase, beyond the analytic algebra whose norm is already fixed by `(13)`

## Static formal-corpus reuse boundary

A source-only audit of the current formal tree finds the following exact boundary.

- `XiReciprocalSquareSourceCore.lean`, `XiReciprocalSquareOneCauchySource.lean`, and
  `XiReciprocalSquareCountableCauchySource.lean` reduce RH to reality of reciprocal-square
  quadratic values on progressively smaller continued-Cauchy source families.  Their hypotheses
  are already RH-equivalent orientation conditions; they do not evaluate `||D_Xi||_1` from the
  prime--Gamma source.
- `XiThermalQuadraticReflectionDefectSpectrum.lean` identifies an anti-Hermitian Hilbert--Schmidt
  defect and makes the reverse source inequality equivalent to RH.  This is a different quadratic
  norm gap and supplies no unconditional reverse inequality for `(20)`.
- `HTGeometry/OperatorAbsoluteValue.lean`, `PolarDecomposition.lean`, and the trace-norm modules
  provide the abstract absolute value, polar map, and Schatten-one infrastructure.  What is absent
  is a Xi-specific source realization of the positive residual

  ```text
  |D_Xi|-Re(D_Xi),
  ```

  whose diagonal entries are `|u_q|-Re(u_q)` and whose trace is the left side of `(14)`.
- `GammaConductorSchurCapacity.lean` concerns a finite scalar Schur complement, not the
  disk-Schur functional used here.

Thus the abstract operator library is reusable for formalizing `(19)`--`(20)`, but no current
declaration closes the source-to-absolute-value step.  Naming the positive residual, its trace, or
its polar decomposition is only a reformulation of the exact gap; a new predecessor must identify
that residual with a prime--Gamma, theta, co-Poisson, or other source-positive object without first
using Xi zero orientation.
