# Mass-shifted recession connection and terminal trace law

- **ID:** `mass-shifted-recession-connection-terminal-trace`
- **Stage:** 3-formalized
- **Route:** mass-shifted spectral face / exact open core
- **Type:** THEOREM + CROSS-GAUGE BRIDGE + GLOBAL TERMINAL SIGN LAW
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Lean:** `RHTower.XiShiftedCanonicalAdmissionRecessionConnection`

## Public sentence

Normalized far-right admission and actual moving inverse-Hankel admission are exactly one flag in
two mass gauges; consequently every fixed-degree actual trace coefficient is negative and strictly
increases to zero on its complete terminal positive chamber.

## Exact theorem

Let

`Q_(n,w)=monicMomentAdmissionPolynomial(xiShiftedFarRightNormalizedMoment w,n)`

and let `P_n(y)` be actual canonical admission for shifted-Xi reciprocal moments at mass `y`.
Whenever both degree-`n` solves are nonsingular and `w>1`,

`P_n(w^2;X)=w^(-2n) Q_(n,w)(w^2 X)`.                    (A)

Thus, for `n>0`,

`[X^(n-1)]P_n(w^2)=w^(-2)[X^(n-1)]Q_(n,w)`.             (B)

Coefficientwise arcsine recession of `Q_(n,w)` and the weight `w^(-2)` imply

`[X^(n-1)]P_n(y) -> 0` as `y -> +infinity`.              (C)

Every fixed degree has a complete terminal positive chamber. Combining (C) with the adjacent
connection's strict velocity law gives the unconditional capstone

`exists A>=0, forall y>A,
  [X^(n-1)]P_n(y)<0 and d/dy [X^(n-1)]P_n(y)>0`.          (D)

Hence the actual trace coefficient approaches zero strictly from below throughout the whole
terminal chamber, not merely along an eventual subsequence.

## Dependency-closed proof

Normalized and actual moment functionals obey

`L_norm,w(R)=(2w/log w) L_(w^2)(R(w^2 X))`.              (E)

The polynomial on the right side of (A) is monic of degree `n`. For `i<n`, substitute
`R=X^i Q_(n,w)` into (E). Normalized admission gives `L_norm,w(R)=0`; the nonzero scalar and mass
weights then give

`L_(w^2)(X^i w^(-2n)Q_(n,w)(w^2X))=0`.

Uniqueness of the nonsingular monic Hankel solve proves (A). Coefficient transport gives (B).
Fixed-degree coefficientwise convergence of `Q_(n,w)` makes its `n-1` coefficient converge to a
finite shifted-Chebyshev coefficient, while `w^(-2)->0`; this proves the square-mass form of (C).
Composing with `sqrt` proves (C) in actual mass.

Far-right positivity supplies `A>=0` such that the `(n+2)` moment block is positive definite for
every `y>A`. The adjacent-connection theorem gives a strictly positive derivative of the first
coefficient at every point of that ray. Therefore the coefficient is strictly increasing there.
If it were nonnegative at one point, strict increase would keep it bounded below by a positive
number farther right, contradicting (C). This proves (D).

## Conjecture -> proof/failure loop

1. `[CONJECTURE]` Recession only controls a separately normalized admission and cannot constrain
   actual connection dynamics. `[FALSIFIED]` Exact functional dilation plus uniqueness proves (A).
2. **Stronger replacement:** normalized and actual admissions are gauge-equivalent pointwise in
   every nonsingular chamber. `[LEAN-PROVED]` Equation (A).
3. `[CONJECTURE]` Positive subleading velocity permits the actual coefficient to approach zero
   from either side. `[FALSIFIED ON THE TERMINAL CHAMBER]` Strict increase plus limit zero forces
   the negative side, equation (D).
4. `[CONJECTURE]` Eventual negativity alone is the strongest available statement. `[FALSIFIED]`
   Complete terminal positivity transports the sign backward across the whole terminal chamber.
5. `[OPEN CORE]` Trace orientation is now rigid, but it does not sign terminal Riccati defect
   `D_n^term=2n alpha_n^2+alpha_n F_n-alpha_n'` and does not compare adjacent degrees at their
   changing first-contact masses.

## Higher universal principle

Recession normalization and moving inverse-Hankel transport are not separate constructions. They
are two gauges of one flat mass connection. Coordinate weight `-2` turns finite arcsine shape into
an actual terminal trace boundary condition; positive half-density velocity then propagates that
boundary condition through the entire terminal chamber. Remaining obstruction is transverse to
this mass gauge: curvature accumulated when degree changes.

## Novelty and theatre audit

- General covariance of orthogonal polynomials under coordinate dilation is classical.
- New corpus knowledge is exact identification of these two previously separate shifted-Xi
  admission constructions, followed by the global terminal sign consequence (D).
- The result changes proof state: actual connection dynamics now has a boundary condition at
  infinity. It is not a restatement of positivity, an orientation map, or a fixed reporter.
- It does not prove RH. Terminal Riccati curvature and degree-changing compatibility remain open.

## Lean certificate

- `sourceCoordinateAdmission_monic`
- `sourceCoordinateAdmission_natDegree`
- `sourceCoordinateAdmission_eq_actualAdmission`
- `sourceCoordinateAdmission_coeff_prev`
- `tendsto_xiShiftedCanonicalAdmissionFirstCoeff_squareParam_zero`
- `tendsto_xiShiftedCanonicalAdmissionFirstCoeff_zero`
- `exists_xiShiftedCanonicalAdmissionFirstCoeff_terminal_neg_increasing_to_zero`

## Verification

- Scratch and direct tree `lake env lean` checks: PASS.
- Targeted
  `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionRecessionConnection`: PASS.
- Capstone `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`.
- Module is reachable from `GaloisForLFunctions.RHTower`; full repository lint remains red on 18
  unrelated pre-existing umbrella-reachability errors.
- No computation, `sorry`, `admit`, custom axiom, `opaque`, `unsafe`, RH premise, orientation map,
  or fixed reporter.

## Log

- 2026-08-11 — Exact cross-gauge admission identity paper-proved and formalized.
- 2026-08-11 — Actual first coefficient recession and terminal negative increasing trace law
  paper-proved and formalized.
