# Exponential-Fock prime Toeplitz carrier should have Riemann--von Mangoldt singular scale

- **ID:** `exponential-fock-prime-toeplitz-rvm-carrier-conjecture`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / DIRECT HILBERT--POLYA CARRIER
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED] [DEPRIORITIZED AS HP BOTTLENECK]`
- **Statement:** A rapidly increasing radial Fock weight with adapted radius `tau(x) asymp exp(-ax)`
  turns the normalized critical-prime incidence into a positive compact Toeplitz operator.  Its
  eigenvalues should satisfy `lambda_n~C_a(log n)/n`; the signed doubling would then be a
  self-adjoint genus-one carrier with the Riemann--von Mangoldt leading spectral density.

## Goal

Construct from the marked prime-log source, without zeta-zero input, a compact self-adjoint operator
in the exact logarithmically enhanced weak-trace ideal forced by an `Xi` determinant.  The target is
not merely the right Schatten exponent.  It is the exact singular scale

```text
s_n asymp (log n)/n                                        (1)
```

proved in `xi-determinant-logarithmic-singular-value-law.md` to be necessary for every exact compact
Hilbert--Polya realization.

### Direct-route priority update

`prime-indexed-rvm-trace-class-hp-normal-form.md` now constructs this ideal and the full smooth
Riemann--von Mangoldt law exactly on the marked prime Hilbert space.  Therefore the Toeplitz Weyl
law below is no longer load-bearing for the direct Hilbert--Polya route.  If proved, it would give
an additional analytic RKHS realization and might help couple prime evaluation to the theta trace;
failure would not kill the prime-indexed trace-class normal form.

## Rapid analytic carrier

Fix `0<a<13/30`.  Choose a smooth radial subharmonic potential `phi_a` which agrees for large `r` with

```text
phi_a(r)=exp(2ar).                                          (2)
```

Let

```text
H_a={f entire:int_C |f(z)|^2 exp(-2phi_a(z))dA(z)<infinity}.  (3)
```

Its natural local scale is

```text
tau_a(r)=(Delta phi_a(r))^(-1/2) asymp exp(-ar).             (4)
```

The weight belongs to the rapidly increasing radial class used in large-Fock embedding theory;
exponential weights are explicit parent examples.  Unlike the polynomial weights, `(2)` is not a
globally doubling-Fock weight.  The rapid-weight kernel and Carleson theorems, rather than the
doubling theory, must be used.

Let `K_a` be the reproducing kernel and define

```text
(S_a f)_p
 =sqrt((log p)^2/p) f(log p)/sqrt(K_a(log p,log p)),
T_a=S_a^*S_a.                                               (5)
```

The construction uses only the marked prime nodes and the critical explicit-formula weights.

## First proved reduction: relative local mass profile

Let `P=exp x`.  The adapted logarithmic window corresponds to a prime interval of length
`P^(1-a+o(1))`.  Since `1-a>17/30`, the uniform short-interval prime number theorem of
Guth--Maynard applies.  Partial summation gives, uniformly at the adapted scale,

```text
sum_(|log p-x|<=c tau_a(x)) (log p)^2/p
 ~2c x tau_a(x)
 asymp x exp(-ax).                                         (6)
```

The rapid-Fock kernel diagonal and adapted-disk embedding theorem apply and prove

```text
S_a compact,
T_a positive compact.                                      (7)
```

The complete paper proof is in
`../2-fully-proven/not_new_scientific_knowledge/12-prime-theta-fock-incidence/critical-prime-exponential-fock-compact-incidence.md`.

The trace-class endpoint is already excluded without any kernel asymptotic:

```text
||S_a||_2^2=sum_p (log p)^2/p=infinity,
T_a notin S_1.                                             (8)
```

## Candidate Weyl law `[CONJECTURE]`

The adapted metric has approximately

```text
dn(x) asymp dx/tau_a(x) asymp exp(ax)dx                    (9)
```

independent cells along the prime-log axis up to location `x`.  The Toeplitz mass in one cell is

```text
q(x) asymp x tau_a(x) asymp x exp(-ax).                    (10)
```

Eliminating `x` between

```text
n asymp exp(ax),
q(x) asymp x exp(-ax)
```

gives

```text
q_n asymp (log n)/n.                                       (11)
```

The load-bearing conjecture is the precise operator version:

```text
[CONJECTURE]
There is C_a>0 such that
lambda_n(T_a)~C_a (log n)/n.                               (12)
```

Equivalently, the eigenvalue counting function should satisfy

```text
#{n:lambda_n(T_a)>=s}
 ~C_a s^(-1)log(1/s).                                      (13)
```

This is not supplied by a Carleson boundedness theorem.  It requires a one-dimensional Toeplitz
Weyl law for a discrete prime-supported measure in a rapidly varying two-dimensional analytic
metric.

## Signed self-adjoint RVM carrier `[CONDITIONAL CONSEQUENCE]`

Assuming `(12)`, put

```text
A_a=c_a (T_a directSum (-T_a)),                             (14)
```

where `c_a>0` is chosen from the proved constant `C_a` so that

```text
s_n(A_a)~(log n)/(pi n)                                    (15)
```

under the two-sided convention.  Then:

1. `A_a` is compact and self-adjoint;
2. `A_a in S_q` for every `q>1`, but `A_a notin S_1`;
3. `det_2(1-zA_a)` is a genus-one entire function with only real zeros;
4. its zero counting has the Riemann--von Mangoldt leading term;
5. its prime phase carrier is not supplied by the finite Gamma completion: it is explicitly the
   all-prime incidence `(5)`.

This would produce a source-defined all-line spectral model with the correct ideal and leading
density.  It would not yet identify its individual zeros with the zeta zeros.

## Coupling to the exact completed trace

The completed theta source decays like `exp(-pi exp(|u|)+O(|u|))`.  Since `2a<26/30<1`, this dominates
the exponential-Fock evaluation growth `exp(phi_a(u))=exp(exp(2a|u|))`.  The same estimate used in
`theta-prime-pointed-doubling-fock-carrier.md` therefore makes the functional

```text
T_a^theta(f)(z)
 =int_R f(u) xiThetaLogSource(u) exp(-2pi Iuz)du            (16)
```

continuous and entire on `H_a`.  At the distinguished vector `one`, its real
trace is exactly the completed zeta function by `XiThetaCriticalTrace.lean`.

Thus `(H_a,one,S_a,T_a^theta,A_a)` would carry

```text
infinite marked prime phase
+ exact completed trace and moments
+ self-adjoint genus-one RVM-scale spectrum.               (17)
```

For this optional RKHS realization, the remaining Hilbert--Polya theorem would be an incidence
identity relating the signed prime Toeplitz determinant in `(14)` to the theta trace in `(16)`.
The main direct route instead asks for the source-defined trace-class correction `K` in the
prime-indexed RVM normal form.

## Candidate moves and attacks

### A. Rapid-Fock Carleson route `[LEADING]`

Starting from the proved compact embedding `(7)`, construct adapted peak functions and an
almost-diagonal decomposition of `T_a`.  Prove matching upper and lower eigenvalue counts by
bracketing each adapted prime-log cell.

**Attack:** Standard Carleson theory controls only the operator norm and compactness.  Off-diagonal
kernel correlations could change the constant or even the asymptotic in `(12)`.  A genuine Weyl
estimate is required.

### B. Lattice discretization route

Choose an adapted lattice for `tau_a`, compare normalized prime kernels with the lattice frame, and
reduce `T_a` to a positive banded matrix whose diagonal is `(10)`.

**Attack:** The prime nodes are much denser than the adapted lattice in Euclidean coordinates but
have critical aggregate mass per cell.  Replacing a cell by its total mass must be justified in
operator norm at the eigenvalue scale, not only weakly.

### C. Berezin distribution route

Prove a Szego-type formula for the counting function of a positive Toeplitz operator with a
one-dimensional singular symbol:

```text
n(s,T_a)~metric-volume{z:Berezin(mu_prime)(z)>=s}.           (18)
```

Insert `(6)` and `(9)` to obtain `(13)`.

**Attack:** Available large-Fock Schatten theorems characterize integrability of averaging
functions, not the exact distribution formula `(18)`.  The measure is singular and supported on a
curve, so smooth-symbol semiclassics do not apply directly.

### D. Direct min--max packets

Build mutually almost-orthogonal normalized kernels at adapted points and use prime mass in their
cells for the lower bound.  For the upper bound, partition the tail into adapted cells and dominate
the residual operator by a diagonal majorant.

**Attack:** This is the most source-pure route, but the required uniform off-diagonal decay for
exponential radial weights must be checked in the exact rapid-weight class.

## Exact open core

`[OPTIONAL OPEN CORE]` Prove the two-sided eigenvalue counting law `(13)` for the prime-supported
normalized Toeplitz operator `(5)`.  The first falsifiable subclaims are:

1. `[PROVED]` the exponential radial weight admits the diagonal kernel estimate required for the
   compact embedding;
2. `[PROVED]` the normalized prime measure is vanishing Carleson, so `T_a` is compact;
3. adapted cell compression changes `n(s,T_a)` by `o(s^(-1)log(1/s))`;
4. the cell masses have the uniform asymptotic `(6)`;
5. upper and lower min--max bounds have the same constant `C_a`.

Failure of subclaim 1 kills this precise analytic carrier.  Failure of subclaim 3 or 5 leaves only
the Schatten-exponent statement and does not produce the RVM-scale operator.

## Scientific novelty gate

The rapid-Fock embedding theory and the PNT window estimate are `[SEARCH]`.  A mere proof of
compactness is a `[BRIDGE]`.  Candidate new scientific content, if proved, is confined to the exact
prime-supported Toeplitz Weyl law `(12)`--`(13)` and its source-derived RVM spectral consequence.

A serious literature audit has not located this arithmetic singular-symbol asymptotic.  Scientific
novelty remains unverified until the exact statement and proof are compared with Toeplitz Weyl laws
for singular measures and rapidly increasing Fock weights.

Primary adjacent sources:

- O. Constantin and J. A. Pelaez, *Integral operators, embedding theorems and a Littlewood--Paley
  formula on weighted Fock spaces*, Journal of Geometric Analysis 26 (2016), 1109--1154,
  `https://arxiv.org/abs/1304.7501`;
- A. Borichev, R. Dhuez, and K. Kellay, *Sampling and interpolation in large Bergman and Fock
  spaces*, Journal of Functional Analysis 242 (2007), 563--606;
- H. Arroussi, G. Asghari, and J. Virtanen, *Toeplitz operators on large vector-valued Fock spaces*,
  `https://arxiv.org/abs/2504.15239`, for adjacent averaging/Schatten machinery in a different
  admissible-weight class.
- L. Guth and J. Maynard, *New large value estimates for Dirichlet polynomials*, Annals of
  Mathematics 203 (2026), 623--675, `https://arxiv.org/abs/2405.20552`, for the uniform
  short-interval PNT above exponent `17/30`.

## Lean status

No rapid-Fock kernel, Carleson embedding, compact-operator min--max, or singular-value counting
infrastructure is present.  The conjecture is not ready for Lean.  The first formal target would be
the exact ideal consumer in `xi-determinant-logarithmic-singular-value-law.md`, but only after a
paper proof supplies an operator theorem rather than a heuristic interface.

## Gates

- [x] source-pure prime incidence defined
- [x] correct local scale and prime cell mass identified
- [x] uniform relative prime cell asymptotic discharged for `a<13/30`
- [x] target singular-value ideal derived independently from `Xi`
- [x] competing proof moves and falsifiers recorded
- [x] rapid-Fock diagonal kernel estimate verified for the chosen potential
- [x] compactness of `S_a` and `T_a` proved
- [ ] exact eigenvalue counting law `(13)` proved
- [ ] signed doubled carrier and determinant growth proved
- [ ] full literature and independent proof audit
- [ ] exact determinant/trace incidence with `Xi`
