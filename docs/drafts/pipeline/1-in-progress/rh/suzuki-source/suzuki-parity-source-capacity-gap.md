# Suzuki Parity Source-Capacity Gap

- **ID:** `suzuki-parity-source-capacity-gap`
- **Stage:** 1 — in progress
- **Type:** THEOREM / EXACT SUZUKI FIRST-JET FRONTIER
- **Source:** Suzuki's closed restricted-Weil form and its even/odd exponential deficiency sources
- **RH used:** no
- **Computation used:** no
- **Scientific status:** `[PAPER-PROVED CORE] [LEAN CORE IN PROGRESS]`
  `[LITERAL FORM INSTANTIATION EXPLICIT] [PRIORITY UNVERIFIED] [NOT ROUTE CLOSURE]`

## Why this is the frontier

The remaining two-angle route does not first ask for an arbitrary pair of positive spectral
measures.  It asks whether Suzuki's **literal centered restricted-Weil form** admits the exact
even-over-odd source polarization forced by the Xi Livsic carrier.  Spectral measures obscure this
because they are outputs of the unbounded Friedrichs operator.  The form and its source moments are
the predeclared arithmetic inputs.

This card removes the spectral-measure intermediary.  Xi first-jet admission is exactly one strict
comparison between two constrained capacities of the explicit prime--Gamma Weil form.  Ground-pole
selection and finite-shift interior selection are not different mechanisms at this level: both are
instances of the same capacity gap.

## Literal setup

Fix an aperture `a>0`.  Let `Q_a` be Suzuki's closed restricted-Weil form, `lambda_a` its spectral
floor, and let `lambda<lambda_a`.  On the even and odd real form domains put

```text
q_(a,lambda)(f)=Q_a(f)-lambda ||f||_2^2.                 (1)
```

This is coercive.  Define the fixed source functionals

```text
ell_e(f)=integral_(-a)^a cosh(x) f(x) dx,
ell_o(f)=integral_(-a)^a sinh(x) f(x) dx.               (2)
```

Their Riesz representers for `(1)` are exactly Suzuki's parity deficiency vectors

```text
u_e=(A_(a,e)-lambda)^(-1) cosh,
u_o=(A_(a,o)-lambda)^(-1) sinh.                          (3)
```

Write their source energies

```text
E=q_(a,lambda)(u_e)=ell_e(u_e)>0,
O=q_(a,lambda)(u_o)=ell_o(u_o)>0.                        (4)
```

Define the two **literal source capacities**

```text
Cap_e(a,lambda)
 =inf {q_(a,lambda)(f): f even, ell_e(f)=1},

Cap_o(a,lambda)
 =inf {q_(a,lambda)(f): f odd, ell_o(f)=1}.              (5)
```

No Xi zero, fitted measure, or post-scalar selector appears in `(1)`--`(5)`.  `Q_a` is the
prime--Gamma form assembled in `SuzukiRestrictedWeilForm.lean`.

## Theorem A: exact reciprocal-capacity law

The infima in `(5)` are attained uniquely, and

```text
Cap_e(a,lambda)=1/E,       minimizer f_e=u_e/E,
Cap_o(a,lambda)=1/O,       minimizer f_o=u_o/O.           (6)
```

### Proof

We prove the even statement; the odd statement is identical.  The Riesz identity is

```text
q_(a,lambda)(u_e,f)=ell_e(f).                            (7)
```

If `ell_e(f)=1`, Cauchy--Schwarz in the Hilbert form gives

```text
1=q(u_e,f)^2 <= q(u_e,u_e)q(f,f)=E q(f,f),              (8)
```

so `q(f,f)>=1/E`.  The vector `u_e/E` has source moment one and energy `1/E`, proving attainment.
Coercivity makes the form norm definite, hence equality in Cauchy--Schwarz gives uniqueness.

## Theorem B: sharp Xi capacity-gap criterion

Let

```text
kappa_Xi=2i Theta_Xi'(i),
R_Xi=(1+kappa_Xi)/(1-kappa_Xi).                          (9)
```

The unconditional first-defect theorem gives

```text
77/85<kappa_Xi<1,        R_Xi>81/4.                     (10)
```

Suzuki's finite-aperture defect polarization is

```text
kappa_(a,lambda)=(E-O)/(E+O).                           (11)
```

Then, exactly,

```text
kappa_Xi<kappa_(a,lambda)
iff R_Xi<E/O
iff R_Xi Cap_e(a,lambda)<Cap_o(a,lambda).                (12)
```

Likewise,

```text
kappa_(a,lambda)=kappa_Xi
iff Cap_o(a,lambda)=R_Xi Cap_e(a,lambda).                (13)
```

### Proof

Positive denominators turn `(11)` into

```text
(1+kappa_Xi)O<(1-kappa_Xi)E,
```

which is `R_Xi<E/O`.  Substitute `(6)` and multiply by `EO>0` to obtain `(12)`.  The same algebra
with equality gives `(13)`.

## Ground-centered form: the actual cofinal object

For fixed `tau>0`, Suzuki's unconditional ground-centered shift is

```text
lambda=lambda_a-tau,
q_(a,tau)^0(f)
 =Q_a(f)-lambda_a||f||_2^2+tau||f||_2^2.                (14)
```

Thus the class-complete first-jet source question is the literal constrained inequality

```text
R_Xi inf_{ell_e(f)=1} q_(a,tau)^0(f)
 <     inf_{ell_o(g)=1} q_(a,tau)^0(g).                 (15)
```

This is the first statement still missing in scientific knowledge.  It is neither a generic
positivity assertion nor an arbitrary-measure comparison.  Every term in `(15)` is fixed by
Suzuki's prime--Gamma source and the spectral floor of that same form.

## Theorem C: exact capacity transport in the ground gap

Let `C_p(tau)` denote either capacity in `(14)` and `f_(p,tau)` its normalized minimizer.  For
`0<tau_1<tau_2`,

```text
(tau_2-tau_1)||f_(p,tau_2)||_2^2
 <= C_p(tau_2)-C_p(tau_1)
 <= (tau_2-tau_1)||f_(p,tau_1)||_2^2.                   (16)
```

Consequently `C_p` is increasing and concave.  At every differentiability point,

```text
C_p'(tau)=||f_(p,tau)||_2^2.                            (17)
```

### Proof

Use `f_(p,tau_1)` as a competitor at `tau_2`:

```text
C_p(tau_2)
 <=q_(tau_2)(f_(p,tau_1))
 = C_p(tau_1)+(tau_2-tau_1)||f_(p,tau_1)||_2^2.
```

Use `f_(p,tau_2)` as a competitor at `tau_1` for the reverse bound.  Divide by
`tau_2-tau_1`; uniqueness plus the standard envelope argument gives `(17)`.  Monotonicity is
immediate.  The secant slopes decrease because the right endpoint minimizer supplies the next
lower bound and the left endpoint minimizer supplies the preceding upper bound, proving concavity.

## Corollary: capacity turning wall

Define the exact Xi capacity margin

```text
D_a(tau)=Cap_o(a,tau)-R_Xi Cap_e(a,tau).                 (18)
```

At a differentiable interior stationary point,

```text
D_a'(tau)=0
iff ||f_(o,tau)||_2^2=R_Xi||f_(e,tau)||_2^2
and therefore ||f_(o,tau)||_2^2>(81/4)||f_(e,tau)||_2^2. (19)
```

Every interior admission loop with sub-Xi endpoints must cross this normalized-minimizer norm
wall.  This is the form-domain dual of the previously proved spectral credit/debt turning law, but
it is stronger as an attack surface: the minimizers solve constrained problems for the explicit
restricted-Weil form, so prime and Gamma terms can be estimated before any spectral measure is
constructed.

## Class-complete first-jet no-go and survivor

For any cofinal aperture family, either:

1. there are admissible shifts with `(15)` and ultimately a schedule on which `(13)` and all higher
   Clark/Livsic data converge to Xi; or
2. for every sufficiently large aperture and every admissible shift,

   ```text
   Cap_o(a,lambda)<=R_Xi Cap_e(a,lambda),                (20)
   ```

   which kills the entire Suzuki two-angle route at the necessary first jet.

Equation `(20)` is class-complete in the shift variable.  Proving it only for the ground edge, a
compact shift window, or the far-negative boundary is not enough.  Conversely, proving one strict
gap does not identify Xi; it only admits the first jet.  Full Route G still requires selected
cofinal equality `(13)`, higher-jet tightness, labeled Clark-measure convergence, and unique
meromorphic-inner identification.

## Hostile audit

- The theorem does not construct `A_a` by assuming a spectral measure.  It starts from Suzuki's
  closed form; `(6)` is Riesz duality in its coercive completion.
- No pointwise derivative of a Friedrichs-domain vector is used.  Suzuki explicitly warns that
  point values need not exist on `D(A_a)`; a tempting differentiated-convolution proof was rejected
  for this reason.
- Capacities are not fitted after observing Xi.  Their constraints are the fixed functions
  `cosh` and `sinh`; Xi enters only through the independently fixed scalar `R_Xi`.
- The `81/4` factor is necessary, not a convenient sufficient constant.  Exact threshold is
  `R_Xi`; `81/4` is its unconditional strict lower bound.
- Ground-pole and interior-excursion branches are not declared solved.  `(12)` proves that both must
  pay the same capacity gap, removing a false dichotomy only at first order.
- Abstract Hilbert-space reciprocal capacity is classical.  Candidate novelty is restricted to
  the Suzuki/Xi identification `(12)`--`(15)` and the capacity turning wall `(19)`.

## Novelty audit

The reciprocal norm/capacity identity is classical Riesz--Thomson duality and is not claimed new.
Suzuki constructs `A_a`, its shifted energy space, and the exponential deficiency sources, but
does not formulate the two constrained capacities, the exact Xi capacity ratio, or the
ground-centered transport wall.  Targeted arXiv searches for Suzuki restricted-Weil parity
capacity, truncated-convolution parity capacity, and the exact `81/4` source gap found no matching
statement.  Priority remains unverified pending specialist review.

## Lean target

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiParitySourceCapacityGap.lean` will prove:

```text
suzukiSourceNormalizedEnergySet_isLeast
primeArchSuzukiDefectAngle_gt_iff_sourceCapacityGap
primeArchSuzukiDefectAngle_eq_iff_sourceCapacityGap_eq
suzukiSourceCapacity_secant_sandwich
suzukiXiCapacityMargin_stationary_iff
```

The generic reciprocal-capacity core is unconditional.  The explicit form-side connector must cite
`restrictedWeilForm`, not an invented operator interface; until that connector is formalized, this
card remains Stage 1.

## Log

- 2026-08-07 — primary-source audit rejected direct differentiation of Friedrichs resolvent vectors;
  exact source frontier moved to constrained capacities on Suzuki's closed form.
- 2026-08-07 — reciprocal-capacity law, sharp Xi gap, ground-centered transport, and stationary
  minimizer-norm wall proved on paper without computation or RH.
