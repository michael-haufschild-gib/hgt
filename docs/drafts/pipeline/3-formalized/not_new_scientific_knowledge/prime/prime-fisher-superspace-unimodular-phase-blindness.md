# Prime Fisher superspace is blind to unimodular Euler phases and therefore to the zero divisor

- **ID:** `prime-fisher-superspace-unimodular-phase-blindness`
- **Stage:** 3-formalized
- **Type:** THEOREM / TERMINAL NO-GO FOR THE METRIC-ONLY RH REFORMULATION
- **Source:** `zeta-fisher-superspace-global-negative-curvature`; separate from RHTower Routes A--D
- **Lean:** `formal/GaloisForLFunctions/RHTower/ProjectiveFisherBlindness.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeFisherSuperspaceBlindness.lean`

## Statement

The zeta Fisher metric, its globally negative curvature, its Poincare boundary at `beta=1`, and
the Born/KMS thermodynamics do **not** determine the zero divisor of a scalar Euler--Dirichlet
amplitude. They are invariant under every fixed coordinatewise unimodular phase twist, while
Helson zeta functions with exactly such twists can have prescribed zeros and poles away from the
critical line.

Consequently the inner scale factor does force a hyperbolic external clock, but that clock does not
force RH. Any successful superspace proof must add a phase-sensitive source constraint on the
unnormalized completed-zeta section.

## 1. Coherent-state calculation

Let `chi : N -> T` be completely multiplicative and unimodular, and for
`s=sigma+i t`, `sigma>1/2`, put

```text
Psi_(chi,s) = sum_(n>=1) chi(n) n^(-s) |n> in ell^2(N).
```

Then

```text
||Psi_(chi,s)||^2
  = sum_n |chi(n)|^2 n^(-2 sigma)
  = zeta(2 sigma).                                      (1)
```

The normalized Born probabilities are therefore

```text
P_(chi,s)(n) = n^(-2 sigma) / zeta(2 sigma),            (2)
```

independent of `chi` and `t`. If `U_chi |n> = chi(n)|n>`, then `U_chi` is a fixed diagonal unitary
and

```text
Psi_(chi,s) = U_chi Psi_(1,s).                          (3)
```

Thus every projective/Hilbert invariant of this family is unchanged by `chi`. In particular, with
`beta=2 sigma` and energy `E_n=log n`, the Fisher scale is

```text
Var_beta(E) = (log zeta)''(beta),                       (4)
```

and the complete negatively curved Fisher superspace proved in
`zeta-fisher-superspace-global-negative-curvature` is identical for all unimodular twists.

The Lean theorem `bornVariance_phase_twist` proves the abstract statement behind `(2)`--`(4)`:
coordinatewise multiplication of any complex state by norm-one phases preserves every Born
probability, every Born expectation, and the variance/Fisher scale.

## 2. The scalar amplitude contains information absent from the metric

The associated Helson zeta function is

```text
zeta_chi(s) = sum_(n>=1) chi(n) n^(-s)
            = product_p (1-chi(p)p^(-s))^(-1)           (5)
```

in `Re(s)>1`. Its scalar value depends on the phases discarded by `(1)`--`(4)`.

Andersson proves that a Helson zeta function can be meromorphically continued with an arbitrary
prescribed discrete signed zero/pole multiset in `Re(s)<1` inside a chosen continuation domain:

- J. Andersson, [Mittag-Leffler type theorems for Helson zeta-functions](https://arxiv.org/abs/2408.15713),
  Theorem 4 and Corollary 3.

Earlier constructions already gave essentially arbitrary zero and pole sets in
`21/40<Re(s)<1` unconditionally:

- I. Bochkov and R. Romanov,
  [On zeroes and poles of Helson zeta functions](https://arxiv.org/abs/2106.15949), Theorem 2.

Therefore there are Euler products with the same coefficient magnitudes, the same coherent-state
norm, the same Born distribution, the same Fisher scale factor, and the same global curvature sign,
but radically different divisors, including zeros in `Re(s)>1/2`.

## 3. Exact point of death

Formally,

```text
zeta_chi(s) = <Omega, Psi_(chi,s)>,
Omega = (1,1,1,...).                                   (6)
```

But `Omega` is not in `ell^2(N)`. Hence `(6)` is not a bounded Hilbert-space observable on the
coherent-state phase space. It is a distributional summation functional, initially defined only in
`Re(s)>1`, whose analytic continuation can acquire divisor data invisible to the Hilbert norm and
its Fisher metric.

This is where the proposed RH proof dies:

```text
negative Fisher curvature
  -> constrains normalized magnitudes and the beta clock
  -/-> constrains the distributional scalar projection zeta_chi(s)
  -/-> localizes its zeros.                             (7)
```

The Bost--Connes/KMS factor-type transition does not repair `(7)`: it is likewise determined by
`beta` and the thermodynamic partition data, so a scalar zero does not by itself change the GNS
factor type or force normal equivalence across reflected sectors.

## 4. Why the functional equation is not yet the missing source

Helson zeta functions do not generally satisfy the Riemann functional equation, so the functional
equation remains genuinely zeta-specific information. But functional-equation symmetry alone also
does not couple the divisor to the Fisher metric. If `Xi(z)=xi(1/2+z)` is even and real under
conjugation, then for any nonreal `a` with `Re(a) != 0`,

```text
H_a(z)=(z^2-a^2)(z^2-conj(a)^2)
```

has the same even and reality symmetries and inserts the off-axis quartet
`{+a,-a,+conj(a),-conj(a)}` into `H_a Xi`. The Fisher metric, defined from the positive Euler
partition, does not see this scalar multiplier.

Thus:

- Fisher geometry alone is insufficient;
- Fisher geometry plus a unimodular Euler product is insufficient;
- Fisher geometry plus functional-equation symmetry is insufficient.

Using the exact Riemann Euler factors and exact functional equation simultaneously specifies the
actual completed zeta function, but no positivity principle has yet been extracted from that joint
source which forbids a bulk divisor. At that point the reformulation has returned to RH unless a new
constraint is found.

## 5. Wheeler--DeWitt conformal cancellation

The most direct quantum-gravity completion also fails. For the Euclidean metric

```text
g_ab = G(beta) diag(1,1),
sqrt(det g)=G,
g^ab=G^(-1) diag(1,1),
```

the scalar Laplace--Beltrami operator is

```text
Delta_g f
  = 1/sqrt(det g) partial_a(sqrt(det g) g^ab partial_b f)
  = G^(-1) (partial_beta^2+partial_tau^2) f.           (8)
```

After Wick rotation the Lorentzian superspace metric gives

```text
Box_g f = G^(-1) (partial_beta^2-partial_tau^2) f.     (9)
```

Thus the massless Wheeler--DeWitt equations `Delta_g f=0` and `Box_g f=0` are independent of the
scale factor. This is the special conformal invariance of the scalar wave equation in dimension
two. A holomorphic completed-zeta section is already Euclidean harmonic away from its divisor, so
placing it in the negatively curved Fisher metric adds no equation capable of moving or excluding
its zeros.

The same conclusion survives a conformally covariant spinor/supercharge rewrite: conformal weights
can rescale the section away from zeros but cannot select its divisor. Supersymmetry becomes
relevant only if the Euler--Gamma source determines an additional connection, potential, boundary
condition, or positivity-improving operator.

## 6. The missing theorem an RH proof would require

`[OPEN CORE / SOURCE CONJECTURE]` Construct from the **joint** completed Euler--Gamma source a
phase-sensitive operator or line-bundle constraint whose bulk positivity implies

```text
xi(s) != 0 for Re(s)>1/2.                             (10)
```

It must satisfy all of the following:

1. depend on Euler phases, not only on `|n^(-s)|` or `zeta(2 sigma)`;
2. survive analytic continuation from `Re(s)>1` into `Re(s)>1/2`;
3. couple the unnormalized scalar section `xi(s)` to the Fisher/KMS geometry;
4. be coercive or positivity-improving strongly enough to exclude bulk nodes;
5. not assume normal KMS-sector equivalence or zero-freeness as an input.

Equations `(8)`--`(9)` add a sixth requirement: the source constraint must break the two-dimensional
massless conformal cancellation. A bare Fisher scale factor cannot do so.

In divisor language, Poincare--Lelong records the zeros as delta sources of
`dd^c log|xi|`. The missing statement is a non-circular **no-bulk-source law** derived from the
completed Euler--Gamma constraint. Neither negative curvature nor the scale factor supplies that
law.

## Verdict

`[PROVED TERMINAL VERDICT FOR THIS FORMULATION]` The scale-factor/Fisher-superspace construction is
mathematically real and globally hyperbolic, but it does not carry to a proof of RH. It dies exactly
at the passage from projective probability geometry to the phase-sensitive, distributional scalar
section whose divisor is the RH object.

## 2026-08-19 — unconditional Lean formalization (stage 3)

`formal/GaloisForLFunctions/RHTower/PrimeFisherSuperspaceBlindness.lean`, on top of the existing
`RHTower/ProjectiveFisherBlindness.lean`; all declarations axiom-clean
(`propext, Classical.choice, Quot.sound`).  The open source conjecture of §6 is deliberately not
formalized: it is the open problem the card isolates.

| Card item | Lean declaration |
|---|---|
| the coherent state `Ψ_{χ,s}` of a completely multiplicative unimodular phase | `dirichletCoherentState` (with `phaseChar`) |
| eq. (1), `‖Ψ_{χ,s}‖² = ζ(2σ)` | `tsum_norm_sq_dirichletCoherentState` |
| eq. (2), the Born law `n^{-2σ}/ζ(2σ)` | `bornProbability_dirichletCoherentState_eq` |
| eq. (3), the twist is a fixed diagonal unitary | `dirichletCoherentState_eq_twist` |
| **eqs. (2)–(4), Born and Fisher blindness to the phases** | `bornProbability_dirichletCoherentState`, `bornVariance_dirichletCoherentState` (abstract core: `bornProbability_phase_twist`, `bornExpectation_phase_twist`, `bornVariance_phase_twist`) |
| eq. (5)–§2, a Helson zeta with a prescribed off-line zero | `exists_phase_fisher_blind_with_prescribed_zero`, built on the corpus formalization of Andersson's Theorem 2 (`exists_continuable_phase_with_prescribed_multiplicities`) |
| **the exact point of death (6)–(7): identical Fisher data, different divisor** | `exists_phase_fisher_blind_with_prescribed_zero` (all four conclusions together) |
| `Ω = (1,1,…) ∉ ℓ²`, so the scalar projection is not a bounded observable | `not_summable_constant_state` |
| §4, the even reality-symmetric quartet multiplier and its zero set | `quartetMultiplier`, `quartetMultiplier_even`, `quartetMultiplier_conj`, `quartetMultiplier_eq_zero_iff` |
| eqs. (8)–(9), two-dimensional conformal cancellation of the massless equation | `conformalLaplacian`, `conformalLaplacian_eq_zero_iff`, `conformalLaplacian_eq_zero_iff_flat` |

The off-line zero is produced unconditionally inside the corpus rather than quoted from the
literature: the prescribed-divisor sequences are `ρ − nI` (zeros) and `−1 − (n+1)I` (poles), and the
resulting Helson zeta continuation has a simple zero at every `ρ` with `0 < Re ρ < 1`, in
particular to the right of the critical line, while its coherent state has exactly the Born law and
Fisher variance of the untwisted zeta state.
