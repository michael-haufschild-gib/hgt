# Theta-cusp atom Liouville Schwinger--Dyson Ward reduction

- **ID:** `theta-cusp-liouville-schwinger-dyson-ward`
- **Stage:** 3-formalized
- **Type:** `[PROVEN] [PHYSICS VALUE BRIDGE] [LEAN]`
- **Source:** Schwinger--Dyson integration by parts for a zero-dimensional Gibbs state;
  hypervirial moment recurrences; `ThetaCuspFinitePrimeDerivatives.lean`;
  `PrimeArchThetaSourceAtomDomination.lean`.
- **Statement:** Every integer theta-cusp source atom is the first-order Ward image of a positive
  Liouville Gibbs atom. Consequently its even raw moments equal explicit adjacent Gibbs moments
  plus the boundary charge at the origin, reducing the two remaining first-atom Hankel hypotheses
  to inequalities for one pure log-gamma Gibbs density.

## Goal

Simplify the two explicit first-atom inequalities that currently imply every linear-polynomial
prime--Gamma source Hankel test. The existing atom contains a polynomial sign factor. The Ward
factorization removes that factor and replaces it with differentiation of a strictly positive
Gibbs atom whose logarithmic potential has elementary exponential curvature.

## Physics identity `[PROVEN IN LEAN]`

For `n : Nat`, define

```text
b_n(x) = exp(x/2) (n exp x)^2 exp(-pi (n exp x)^2).
```

This is a one-dimensional Liouville Gibbs weight. Its logarithmic derivative is

```text
(log b_n)' = 5/2 - 2 pi (n exp x)^2.
```

The exact theta source atom should therefore factor as

```text
thetaCuspSourceTerm(x,n) = -2 pi (d/dx + 1/2) b_n(x).       (W)
```

Equation `(W)` is the zero-dimensional Schwinger--Dyson/Ward operator: integration against a test
function transfers the derivative from the Gibbs density to the test and leaves the half-line
boundary charge.

Primary physics background:

- Bogojević--Popović, *Path Integral Measure Via the Schwinger-Dyson Equations*:
  <https://arxiv.org/abs/hep-th/9509081>.
- Li--Zhang--Chen, *Virial Theorem and Hypervirial Theorem in a spherical geometry*:
  <https://arxiv.org/abs/1012.5391>.

The project-specific factorization and its moment consequences are to be proved directly; neither
paper is used as an axiom.

## Moment consequence `[PROVEN IN LEAN]`

Put

```text
B_k(n) = integral_(0,infinity) x^k b_n(x) dx,
a_j(n) = thetaCuspAtomRawEvenMoment(j,n).
```

Integration by parts in `(W)` predicts

```text
a_0(n) = 4 pi b_n(0) - 2 pi B_0(n),
a_(j+1)(n) = 8 pi (j+1) B_(2j+1)(n) - 2 pi B_(2j+2)(n).   (M)
```

For the dominant atom `n=1`, `b_1(0)=exp(-pi)`. Define

```text
U_0 = 2 exp(-pi) - B_0(1),
U_1 = 4 B_1(1) - B_2(1),
U_2 = 8 B_3(1) - B_4(1),
U_3 = 12 B_5(1) - B_6(1).
```

Then `a_j(1)=2 pi U_j`. The two existing buffered first-atom hypotheses become

```text
14 (3005/2997)^2 U_2^2 <= 9 U_1 U_3,
16 (3005/2997)^2 U_0 U_2 <= 45 U_1^2.                    (G)
```

Thus `(G)` directly implies every linear-polynomial prime--Gamma source Hankel test through the
already-formalized first-atom domination theorem.

## Attack

- The full-source second-order theta-tail integration-by-parts identity already exists in
  `XiCTaylorThetaTailTelescope.lean`; reproducing it is not progress.
- The useful distinction is atomwise first-order factorization and the removal of the polynomial
  source factor.
- Generic Schwinger--Dyson identities do not sign `(G)`. The remaining analytic content is still
  a pair of source-specific inequalities for the truncated log-gamma Gibbs state.
- The factorization is useful only if Lean proves `(W)`, `(M)`, the exact first-atom rewrite, and a
  direct consumer reducing the existing Hankel theorem to `(G)`.

## Formalization

`formal/GaloisForLFunctions/RHTower/PrimeArchThetaLiouvilleWard.lean` proves:

- the pointwise Ward factorization `(W)`;
- weighted integrability and both half-line endpoint limits;
- the integration-by-parts identities `(M)` for every positive integer atom;
- `a_j(1) = 2 pi U_j` at every order and `0 <= U_j`;
- the all-order enclosure
  `2 pi U_j <= thetaCuspRawEvenMoment j <= (3005/2997) (2 pi U_j)`;
- a direct theorem from the two inequalities `(G)` to every linear-polynomial prime--Gamma source
  Hankel test.

## Gates

- [x] Live-corpus duplicate check: the full tail recurrence exists; the atomwise Ward reduction
  does not.
- [x] Direct consumer identified: `forall_primeArchSourceTraceHankel_linear_nonneg_of_first_atom`.
- [x] Prove the pointwise Ward factorization in Lean.
- [x] Prove weighted integrability, endpoint limits, and the moment identities in Lean.
- [x] Rewrite the two first-atom hypotheses as Gibbs-moment inequalities in Lean.
- [x] Connect the Gibbs inequalities directly to all linear-polynomial source Hankel tests.
- [ ] Prove the two Gibbs inequalities.
- [ ] RH.
