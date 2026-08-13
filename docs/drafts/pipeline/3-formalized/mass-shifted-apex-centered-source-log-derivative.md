# Mass-shifted apex-centered source/log-derivative landing

- **ID:** mass-shifted-apex-centered-source-log-derivative
- **Stage:** 3-formalized
- **Type:** THEOREM + EXACT FRONTIER
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 exact open core
- **Statement:** De-resisted completed `P^sharp` source admits an exact moving-apex signed Cauchy
  landing in the current admission logarithmic derivative plus intrinsic degree/trace counterterms.

## Goal

Construct signed adaptive producer left by normalization--fidelity no-go.  Center each faithful
completed-source atom before aggregation, retain exact node poles, and identify endogenous vacuum
counterterms.  Door passport: finite positive block only; no representing measure, infinite
extension, RH premise, fixed reporter, orientation map, or computation.

## Frozen conjecture C1

For current Gauss nodes `x`, mass `y`, and nonreal aperture `z`, define

`C_m(y,z) = sum_x (((y*x)^2-1)/(z-x))`.

Then

`C_m(y,z) = (y^2*z^2-1) P_(m+1)'(z)/P_(m+1)(z)
             - y^2 ((m+1)z + sum_x x)`.

The identity must first be proved for literal finite nodes and only then coupled to de-resisted
current/adjacent Padé-residue/completed-capacity source.

## Hostile tests

1. **Pole fidelity:** residue at every current node must remain exactly `(y*x)^2-1`; no resistance
   share may remain.
2. **Apex sign:** positive residue must be exactly `y*x>1` or `y*x<-1`; on positive nodes this is
   the super-apex sector.
3. **Vacuum removal:** degree and first-root-trace terms must be derived algebraically, not inserted
   as a reporting convention.
4. **Budget:** signed aggregate may still lack finite total variation.  Do not infer a cross-degree
   bound from cancellation.

## Attack

Use `x^2/(z-x)=z^2/(z-x)-(z+x)` pointwise, sum over finite Gauss nodes, substitute exact node
cardinality and existing unit-pole/log-derivative theorem, then specialize through coefficient-one
de-resisted completed source.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, finite-block passport, hostile tests
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: unconditional Lean, targeted build green, standard-only axiom audit
- [ ] 3 → 4 publication-ready: standalone novelty audit and integration into full route

## Paper proof `[PROVED HERE]`

For each current node and nonreal aperture,

`x^2/(z-x)=z^2/(z-x)-(z+x)`.

Multiplication by `y^2` and subtraction of `1/(z-x)` gives

`((y*x)^2-1)/(z-x)
 = (y^2*z^2-1)/(z-x)-y^2(z+x)`.

Summing over current nodes yields

`C_m(y,z)=(y^2*z^2-1)L_m(z)-y^2(card(X_m)z+sum_x x)`,

where `L_m(z)=sum_x 1/(z-x)`.  Finite positive-block root splitting and differentiation give
`L_m=P_(m+1)'/P_(m+1)`, while exact Gauss-node cardinality gives `card(X_m)=m+1`.  This proves C1.

For shifted-Xi admission, terminal source law gives

`r_(n,x) * (Padé residue * completed P^sharp capacity)=w^2*x^4*h_(n-1)`.

Dividing only under explicit nonvanishing hypotheses makes de-resisted coefficient exactly one.
Multiplying this already-formed literal source coefficient by `(w^2*x)^2-1` therefore gives same
centered residue before aggregation.  This proves literal source/log-derivative landing.

For positive `w^2` and positive node `x`, factorization

`(w^2*x)^2-1=(w^2*x-1)(w^2*x+1)`

proves residue positivity iff `1<w^2*x`, exactly super-apex condition.

Finally define positive null-flag shear nodewise by

`max(0,(w^2*x)^2-1) * eta / ((a-x)^2+eta^2)`.

At `eta>0`, every Poisson factor is strictly positive and every sheared residue is nonnegative.
Finite-sum positivity therefore holds iff at least one centered residue is positive.  Under positive
current nodes this is equivalent to existence of super-apex node.  Shearing occurs before
aggregation, so signed cancellation cannot erase defect.

No representing measure, infinite extension, limit, computation, or RH premise is used.

## Hostile audit and exact frontier

- Pole fidelity passes: every current residue is exactly `(y*x)^2-1`; resistance has vanished.
- Apex sign passes on positive nodes: positive residue iff `1<y*x`.
- Vacuum removal passes: degree and first-root-trace counterterms are forced by polynomial division.
- Fixed-reporting audit passes: source coefficient and apex cut depend on current admission/mass;
  positive shear is applied nodewise before Cauchy/Poisson aggregation.
- Cross-degree budget remains open.  Pointwise positivity and exact detection do not imply
  summability or telescoping across changing admissions.  Claiming otherwise would be theorem
  laundering.

Thus missing producer is complete.  Exact remaining theorem is an arithmetic budget/coboundary for
the positive null flags across a cofinal degree--mass schedule, or direct proof they vanish on every
actual positive shifted-Xi face.

## Lean certificate

- `HTGeometry/GaussApexCenteredSourceLogDerivative.lean` proves exact signed/log-derivative
  landing, degree form, apex-sign law, and null-flag positivity iff a positive centered residue
  exists.
- `RHTower/XiShiftedCanonicalAdmissionCenteredCompletedSourceLogDerivative.lean` proves literal
  completed-source residue law, aggregate landing, and source-first null-flag iff current
  super-apex-node theorem.

Both modules pass `lake env lean`; targeted `lake build` passes.  `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.  Global lint reaches these umbrellas but currently
fails on pre-existing unreachable `Sieve`, `CCMConnesConsani`, `XiReflectionIncidence`,
`BoundedPerturbedCompactResolvent`, and `FiniteSmoothCompression` modules unrelated to this card.
Route-specific coupling remains `[NOVELTY UNVERIFIED]`.

## Log

- 2026-08-13 — created after exact source renewal proved sharp normalization--fidelity boundary.
- 2026-08-13 — C1, literal shifted-Xi source coupling, and pre-aggregation positive null-flag shear
  proved unconditionally in Lean; cross-degree budget isolated as exact remaining frontier.
