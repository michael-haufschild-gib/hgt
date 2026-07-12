# Xi Taylor anisotropic rational-mesh sublinear flux criterion

- **ID:** `xi-taylor-anisotropic-rational-mesh-sublinear-flux`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CLASSICAL ANALYTIC BRIDGE] [NOT AN RH PROOF]`
- **Source:** top-down whole-corpus RH sweep
- **Statement:** Along any super-polynomially accurate source-selected subsequence of the canonical
  Xi Taylor polynomials, RH is equivalent to sublinear upper growth of their logarithmic
  derivatives on an explicit `1/n` by `1/n^2` Gaussian-rational mesh in every compact left
  half-strip.

## Goal

Strengthen the existing fixed-rational-point Taylor criterion into a diagonal finite-polynomial
criterion whose allowed bound grows with the mesh resolution.  A false-RH pole grows linearly on
the anisotropic mesh.  Therefore an `o(n)` estimate, rather than one uniform constant, suffices.

The positive top-down chain is

```text
canonical Xi Taylor series
  -> source-selected super-polynomial compact approximation schedule
  -> sublinear finite-polynomial flux on anisotropic rational meshes
  -> no transverse completed-source pole
  -> RiemannHypothesis.                                        (1)
```

The first two arrows are unconditional.  The finite-polynomial `o(n)` estimate is the isolated
open producer.

## Definitions

Let

```text
F(z)   = XiC(z),
P_N(z) = xiCTaylorApprox N z,
z(s)   = (s - 1/2)(-i).
```

For an integer `R >= 4`, let

```text
K_R = {s : 1/R <= Re(s) <= 1/2 - 1/R and |Im(s)| <= R}.
```

At mesh resolution `n >= 1`, put

```text
G_(n,R) = K_R intersect {a/n + i b/n^2 : a,b in Z}.           (2)
```

A strictly increasing map `N : N -> N` is a **super-accurate Taylor schedule** if for every
integer `R >= 1` and every `k >= 0`,

```text
n^k sup_(|z| <= R)
  (|P_(N(n))(z)-F(z)| + |P_(N(n))'(z)-F'(z)|) -> 0.           (3)
```

Such a schedule exists unconditionally.  Indeed, local uniform convergence of `P_N` and `P_N'`
allows a diagonal choice with error at most `n^(-n)` on the ball of radius `n`.  The least index
meeting these source-value inequalities gives a canonical noncomputable choice and uses no zero
of `F`.

For a super-accurate schedule define the finite mesh maximum

```text
M_(n,R) = max { Im(P_(N(n))'(z(s))/P_(N(n))(z(s))) :
                s in G_(n,R), P_(N(n))(z(s)) != 0 },          (4)
```

with value zero if the displayed finite set is empty.

## Theorem

For every super-accurate Taylor schedule `N`,

```text
RiemannHypothesis
  <-> for every integer R >= 4,
      limsup_(n -> infinity) M_(n,R)/n <= 0.                  (5)
```

It is enough in the reverse implication to assume `M_(n,R) <= g_R(n)` eventually for functions
with `g_R(n)/n -> 0`.

## Proof

### RH implies sublinear mesh flux

Assume RH and fix `R`.  The compact set `K_R` lies strictly inside `0 < Re(s) < 1/2`.
Consequently `F(z(s))` has no zero there.  Compactness gives a positive lower bound for
`|F(z(s))|`.  Local uniform convergence of `P_(N(n))` and their derivatives therefore upgrades to
uniform convergence of the logarithmic derivatives on `z(K_R)`:

```text
P_(N(n))'/P_(N(n)) -> F'/F uniformly on z(K_R).               (6)
```

The continuous function `F'/F` is bounded on that compact set.  Hence `M_(n,R)` is bounded above
independently of `n`, and division by `n` proves the right side of `(5)`.

### A reflected off-line zero forces linear mesh growth

Assume RH is false.  Functional-equation reflection supplies a Xi zero `sigma` with

```text
0 < Re(sigma) < 1/2.
```

Choose `R` so that `sigma` is in the interior of `K_R`, and let its analytic multiplicity be
`m >= 1`.  For every sufficiently large `n`, choose

```text
a_n = ceil(n Re(sigma)) + 1,
b_n = floor(n^2 Im(sigma)),
s_n = a_n/n + i b_n/n^2.                                    (7)
```

Then `s_n` belongs to `G_(n,R)` and, writing `delta_n=s_n-sigma=x_n+i y_n`,

```text
1/n <= x_n < 2/n,      |y_n| < 1/n^2.                       (8)
```

Factor Xi at the zero:

```text
xi(sigma+delta) = delta^m h(delta),       h(0) != 0.          (9)
```

On a fixed punctured neighborhood,

```text
logDeriv xi(sigma+delta) = m/delta + h'(delta)/h(delta).      (10)
```

The second term is bounded.  Equations `(8)` and `(10)` give

```text
Re logDeriv xi(s_n)
  >= m x_n/(x_n^2+y_n^2) - O(1)
  > (m/5)n - O(1).                                            (11)
```

Under the centered coordinate, `z_n=z(s_n)` tends to the zero `z(sigma)` and

```text
Im logDeriv F(z_n) = Re logDeriv xi(s_n).                     (12)
```

### Transfer to the finite Taylor polynomials

From `(9)` and `(8)`, `|F(z_n)|` has size comparable to `n^(-m)` and `|F'(z_n)|` is
`O(n^(1-m))`.  Super-accuracy `(3)`, used with an exponent larger than `m+2`, gives

```text
P_(N(n))(z_n) / F(z_n) -> 1,

(P_(N(n))'/P_(N(n)) - F'/F)(z_n) = o(n).                    (13)
```

In particular `P_(N(n))(z_n) != 0` eventually.  Combining `(11)`--`(13)` yields

```text
M_(n,R)/n >= m/5 - o(1),                                     (14)
```

contradicting the right side of `(5)`.  Therefore the sublinear mesh condition implies RH.

## Why the anisotropic mesh matters

An isotropic `1/n` by `1/n` grid need not approach a pole in a direction with a controlled positive
real reciprocal.  The `1/n^2` vertical mesh makes the transverse error negligible compared with
the forced positive horizontal displacement.  The elementary bound in `(11)` is then uniform and
does not depend on Diophantine properties of the zero ordinate.

## Existing Lean interfaces

The current corpus already supplies:

- `xiCTaylorApprox_tendstoLocallyUniformly`;
- `xiCTaylorApprox_deriv_tendstoLocallyUniformly`;
- `xiCTaylorApprox_logDeriv_tendsto` at fixed pole-free points;
- `exists_xiCTaylorSuperaccurateSchedule`: an axiom-clean source-selected schedule satisfying
  the simultaneous expanding-ball value and derivative estimate `(3)`;
- `xiTaylorAnisotropicRightApprox_re_sub_bounds` and
  `abs_xiTaylorAnisotropicRightApprox_im_sub_lt`: the explicit `1/n` by `1/n^2` mesh geometry
  `(8)`;
- `nat_div_five_lt_inv_re_of_anisotropic`: the linear reciprocal amplifier behind `(11)`;
- `norm_logDeriv_sub_logDeriv_le_of_two_norm_sub_le`: explicit nonvanishing and
  logarithmic-derivative perturbation control, the algebraic core of `(13)`;
- `eventually_xiOrder_div_ten_lt_logDeriv_anisotropicMesh_re_div`: an actual Xi zero of
  multiplicity `m` forces normalized mesh growth greater than `m/10`, the formal version of
  `(11)`;
- `XiAnisotropicLogDerivSublinearUpper`: the zero-free source premise that the normalized Xi
  logarithmic derivative is eventually below every positive rate on each explicit mesh fibre;
- `riemannHypothesis_of_xiAnisotropicLogDerivSublinearUpper`: the axiom-clean formal endpoint
  `sublinear anisotropic Xi mesh flux -> RiemannHypothesis`;
- `xi_normalizedLogDeriv_tendsto_order` for the local pole residue;
- `continuedPrimeArchSourceRelativeTrace_eventuallyEq_logDeriv_XiC`;
- `riemannHypothesis_of_xiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove` for the older
  uniform-bound/fixed-rational quantifier pattern.

The direct Xi endpoint is formalized.  The remaining Lean infrastructure for the finite-polynomial
criterion is the finite compact-mesh maximum and the specialization of the generic quotient bound
to the super-accurate Xi schedule near a zero.  The diagonal selector, the decisive one-point
anisotropic mesh geometry, its linear reciprocal amplifier, the exact Xi linear pole-growth
theorem, and the generic quotient perturbation estimate are formalized.

## Non-circularity gate

The bridge theorem is not an RH proof.  A successful producer must prove the `o(n)` upper estimate
for the finite polynomials from their theta-moment coefficients, a finite matrix inequality, or
another source construction.  It may not use locations of Xi zeros, real-rootedness of the Taylor
polynomials, the anti-Herglotz property of the limiting source, or a measure whose positivity is
already equivalent to RH.

Unlike a pointwise limiting criterion, the open statement concerns only finite polynomials at
finite rational sets.  Unlike a zero-fibre energy criterion, it does not quantify over polynomial
zeros.  This is the potential gain of the reformulation.

## Positive research problem

Prove a finite coefficient theorem of the form

```text
sup_(s in G_(n,R)) Im(P_(N(n))'(z(s))/P_(N(n))(z(s))) = o(n) (15)
```

for one source-selected super-accurate schedule.  The all-order theta cumulant recurrences provide
the coefficients of `P_N`; the missing content is a finite-polynomial logarithmic-derivative bound
that retains the completed prime--archimedean orientation.

## Gates

- [x] 0 -> 1 in-progress: explicit source objects, mesh, and non-circularity gate
- [x] 1 -> 2 fully-proven: complete paper proof of schedule existence and equivalence `(5)`
- [ ] 2 -> 3 formalized: compact mesh maximum and Xi-specific asymptotic specialization remain;
  selector, one-point mesh geometry, reciprocal amplifier, Xi pole growth, and generic quotient
  perturbation complete
- [ ] 3 -> 4 publication-ready: only after a non-circular proof of `(15)`

## Formalization log

- 2026-07-12 — Formalized `XiCTaylorSuperaccurateSchedule` and
  `exists_xiCTaylorSuperaccurateSchedule` in
  `formal/GaloisForLFunctions/RHTower/XiCTaylorSuperaccurateSchedule.lean`; exact module build
  passes and the theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-12 — Formalized the anisotropic Gaussian-rational mesh and its sharp one-sided
  approximation bounds, together with the linear reciprocal amplifier `n/5 < Re(delta⁻¹)`, in
  `formal/GaloisForLFunctions/RHTower/XiTaylorAnisotropicMesh.lean`; direct Lean and axiom checks
  pass.
- 2026-07-12 — Formalized the generic quotient and logarithmic-derivative perturbation bounds in
  `formal/GaloisForLFunctions/RHTower/LogDerivQuotientPerturbation.lean`; direct Lean and axiom
  checks pass.
- 2026-07-12 — Formalized exact multiplicity recovery and the eventual `m/10` normalized linear
  lower bound for the Xi logarithmic derivative along the mesh in
  `formal/GaloisForLFunctions/RHTower/XiAnisotropicPoleGrowth.lean`; direct Lean and axiom checks
  pass.
- 2026-07-12 — Formalized the zero-free, unbounded sublinear source premise
  `XiAnisotropicLogDerivSublinearUpper` and the terminal implication
  `riemannHypothesis_of_xiAnisotropicLogDerivSublinearUpper` in
  `formal/GaloisForLFunctions/RHTower/XiAnisotropicSublinearGate.lean`.  This closes a direct
  `x -> RH` interface before the remaining finite-Taylor transfer.
