# Xi radial Jensen mass and central-curvature saturation

- **ID:** `xi-radial-jensen-mass-central-curvature`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Scientific status:** `[PROVED HERE] [CLASSICAL COMBINATION] [NOT AN RH PROOF]`
- **Source:** top-down whole-corpus RH sweep
- **Statement:** The integrated central circle-average excess of `log |XiC|` is exactly the
  Hilbert--Schmidt mass of the reciprocal Xi operator, and RH is equivalent to that radial mass
  being no larger than the zeroth prime--Gamma central moment.

## Goal

Replace the divisor-indexed terminal condition

```text
the reciprocal Xi operator is self-adjoint
```

by one explicit inequality between two scalar quantities that both admit source-value
descriptions.  The result does not prove the inequality.  Its positive content is an exact
local-to-global budget law: central prime--Gamma curvature is always bounded above by global
radial Jensen mass, and it exhausts that mass exactly when every Xi spectral point is real.

## The theorem

Let `t_q = xiSpectralPoint q`, with one index `q` for every Xi zero and every analytic
multiplicity copy.  Put

```text
A(r) = circleAverage(theta |-> log |XiC(r exp(i theta))|)
       - log |XiC(0)|,

J_Xi = 4 integral_(0,infinity) A(r) r^(-3) dr,

m_0 = normalizedPrimeArchMoment 0.
```

Then all displayed quantities converge and

```text
J_Xi
  = sum_q |t_q^(-1)|^2
  = hsNormSq xiReciprocalDiagonalKernel,                       (1)

m_0
  = Re sum_q t_q^(-2)
  = Re opTrace (xiReciprocalOperator comp xiReciprocalOperator), (2)

J_Xi - m_0
  = 2 sum_q (Im (t_q^(-1)))^2 >= 0.                            (3)
```

Consequently the following are equivalent:

```text
RiemannHypothesis;
J_Xi = m_0;
J_Xi <= m_0.                                                   (4)
```

Thus the exact top-down chain is

```text
source proof that radial Jensen mass <= central prime--Gamma curvature
  -> vanishing reciprocal transverse energy
  -> real reciprocal Xi spectrum
  -> RiemannHypothesis.                                        (5)
```

## Proof

Jensen's formula at the nonzero center of `XiC` gives, for every `r > 0`,

```text
A(r) = sum_(|t_q| <= r) log(r / |t_q|).                        (6)
```

Every summand is nonnegative.  Tonelli therefore permits interchange of the `q`-sum and the
radial integral.  For `a > 0`, direct integration gives

```text
4 integral_a^infinity log(r/a) r^(-3) dr = a^(-2).             (7)
```

Applying `(7)` termwise in `(6)` proves

```text
4 integral_0^infinity A(r) r^(-3) dr = sum_q |t_q|^(-2).       (8)
```

The right side is finite by reciprocal-square summability of the Xi divisor.  This also proves
convergence of the nonnegative integral without requiring a separate large-circle estimate.
The infinite diagonal Hilbert--Schmidt identity now gives `(1)`.

The prime--archimedean central-moment germ is already identified with the centered reciprocal
Xi moment germ.  At order zero this says

```text
m_0 = Re sum_q t_q^(-2).                                       (9)
```

The sum in `(9)` is absolutely convergent and real by Schwarz symmetry.  The trace weld for the
reciprocal diagonal operator gives the second equality in `(2)`.

For every complex number `lambda`,

```text
|lambda|^2 - Re(lambda^2) = 2 (Im lambda)^2.                  (10)
```

Sum `(10)` with `lambda = t_q^(-1)`.  Reciprocal-square summability justifies all sums and yields
`(3)`.  Hence `J_Xi <= m_0` forces equality in `(3)`.  A sum of nonnegative terms can vanish only
if every term vanishes, so every `t_q^(-1)` and therefore every `t_q` is real.  The established
real-spectral-point criterion gives RH.  Conversely RH makes every `t_q` real, so `(3)` vanishes.
This proves `(4)`.

## Existing Lean interfaces

The proof deliberately splices declarations from different parts of the corpus:

- `xi_circleAverage_log_norm` in `LittlewoodXi.lean`: Jensen circle-average identity;
- `xiSpectralPoint_inv_sq_summable` in `XiCanonicalProduct.lean`: convergence;
- `hsNormSq_diagMul_infinite` in `FredholmDeterminantInfinite.lean`: first equality in `(1)`;
- `primeArchSourceMoment_eq_xiCentralReciprocalMoment` in
  `PrimeArchCentralMomentGerm.lean`: source identity `(9)`;
- `opTrace_toOperator_comp` in `HilbertSchmidtTrace.lean`: trace weld in `(2)`;
- `xiReciprocalOperator_isSelfAdjoint_iff_rh` in
  `XiHedenmalmReciprocalOperator.lean`: terminal operator criterion.

The full radial integration and scalar saturation criterion are formalized in
`GaloisForLFunctions/RHTower/XiRadialJensenMassCentralCurvature.lean`.

## Lean formalization

The wired formal chain is:

- `integral_Ioi_log_div_cube`: the exact scalar kernel integral `(7)`;
- `xiCenteredRadialJensenExcess_div_cube_eq_supportProfile`: Jensen's circle average
  rewritten as the finite multiplicity-weighted divisor profile at every positive radius;
- `tsum_xiRadialJensenKernel_eq_ofReal_supportProfile`: exact regrouping from divisor support
  to the multiplicity-copy Xi zero index;
- `xiCenteredRadialJensenMassENNReal_eq_divisorMass`: Tonelli transfer from the source circle
  average to the nonnegative divisor mass;
- `xiCenteredRadialJensenMass_eq_hermitianMass`: identity `(8)`;
- `xiCenteredRadialJensenMass_eq_centralCurvature_iff_rh` and
  `xiCenteredRadialJensenMass_le_centralCurvature_iff_rh`: the exact equivalences `(4)`.

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Literature boundary

Voros's superzeta framework makes holomorphic symmetric sums of centered Riemann zeros explicit;
in particular, its standard centered variable is `rho = 1/2 + i tau`, with `tau` real for every
zero exactly under RH.  Arias de Reyna likewise stresses that the secondary-zeta parameters are
generally complex unless RH is assumed.  These source-side continuations therefore control powers
such as `sum tau^(-2)`, matching the central prime--Gamma curvature, but do not supply the
nonholomorphic Hermitian sum `sum |tau|^(-2)`.  Replacing the former by the latter is exactly the
orientation assertion isolated by this card, not a consequence of superzeta continuation.

- André Voros, [Zeta functions over zeros of Zeta functions and an exponential-asymptotic view
  of the Riemann Hypothesis](https://arxiv.org/abs/1403.4558), especially Sections 2--3.
- Juan Arias de Reyna, [Computation of the secondary zeta
  function](https://arxiv.org/abs/2006.04869), Section 1.

## Non-circularity gate

The theorem is a terminal reduction, not an unconditional RH proof.  A proof of the missing
inequality in `(5)` counts as progress only if it derives

```text
4 integral_0^infinity A(r) r^(-3) dr <= normalizedPrimeArchMoment 0
```

directly from a completed theta, Euler--Gamma, or other source constraint.  It may not assume
real zeros, self-adjointness, Weil positivity, an anti-Herglotz sign, or a positive measure whose
existence is already equivalent to RH.  Expanding `A(r)` by Jensen and then asserting the desired
termwise inequality is also circular: the expansion is permitted for the terminal transfer, not
as the producer of the reverse inequality.

## Positive research problem

Construct a source-side anisotropy law showing that the central second directional curvature of
`log XiC` dominates the full integrated radial divisor mass.  Equivalently, find a completed
theta/Euler constraint that forces the circular Jensen mass to concentrate in the real spectral
direction.  This is a constraint problem, not a zero-flow problem.

The formulation is unusually small: it asks for one global scalar inequality, not an all-order
Hankel cone or pointwise upper-half-plane sign.  Its danger is equally precise: generic even real
entire functions satisfy the opposite inequality in `(3)` and have no reason to saturate it.
Any successful proof must use a source-specific coupling absent from generic functional equation,
reality, growth, and positive-definiteness data.

## Gates

- [x] 0 -> 1 in-progress: well-posed, exact source-value statement, non-circularity gate stated
- [x] 1 -> 2 fully-proven: complete paper proof of `(1)`--`(4)`
- [x] 2 -> 3 formalized: radial integral identity and scalar saturation criterion in Lean
- [ ] 3 -> 4 publication-ready: only if a non-circular source proof of the inequality is found

## 2026-07-15 Schur exact norm-gap predecessor

The paper theorem
`../../2-fully-proven/not_new_scientific_knowledge/xi-radial-jensen-schur-capacity-rigidity.md`
inserts a source-defined Hardy-space junction before the mass comparison.  If `u_q` denotes the
reciprocal-square Xi coordinate and `L_Xi(P)` the normalized prime--Gamma polynomial moment
functional, then

```text
S_Xi = sup { |L_Xi(P)| : P in R[X], sup_(|z|<=1) |P(z)| <= 1 }
```

satisfies the stronger unconditional identity

```text
S_Xi = primeArchCentralCurvature.
```

The source height gap gives `|u_q|<2/41`, and the one-eighty-fourth orientation law gives a narrow
positive sector.  A direct Schwarz--Pick estimate then makes the constant `1` extremal; no normal-
family passage is needed.  The reflected source boundary symbol consequently has exact
`L^1/H^1_0` quotient norm `primeArchCentralCurvature`, while

```text
xiCenteredRadialJensenMass-S_Xi
  = xiGlobalReflectionDefectEnergy/2.
```

Thus the Hardy-space norm computation is closed.  The remaining RH-sized input is positively
anti-holomorphic: control the reciprocal-square trace norm or couple the analytic functional to
the adjoint, absolute value, or polar phase.
