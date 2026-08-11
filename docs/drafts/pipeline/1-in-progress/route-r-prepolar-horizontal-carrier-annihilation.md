# Route R pre-polar horizontal-carrier annihilation

- **ID:** `route-r-prepolar-horizontal-carrier-annihilation`
- **Stage:** 1 — in progress
- **Type:** CONJECTURE / SOURCE PRODUCER
- **Route:** R
- **Scientific status:** `[OPEN CORE] [NOT RH PROOF]`
- **Statement:** Derive `BurnolXiCartierDividedShiftHeadFluxDissipativity` from a literal
  pre-divisor Euler--Gamma--Stokes law acting before polar completion, without importing an
  RH-equivalent annihilation, sewing, norm, or critical-line premise.

## Exact frontier

`SourceZeroHorizontalCarrier.lean` constructs and orients the multiplicity-exact, prime-labelled,
reflection-odd horizontal carrier and proves that its global vanishing is equivalent to RH.
`BurnolBocksteinLimit.lean` proves the Bockstein limit, forward/reflected residue landing, fixed
head-flux landing, and same-fibre Stokes transgression. These are closed receivers.

For every hypothetical right-half Xi divisor, Lean proves the landed current is strictly positive.
Consequently the desired nonpositive current cannot be obtained from post-landing positivity or
from an identity that already factors through critical-line placement. A valid producer must
independently make the hypothetical right-half source configuration inadmissible.

## Open claim

Construct a source-defined, pre-polar operation or pairing `A` on the two retained ordered cofinal
orientations such that:

1. `A` is defined from Euler, Gamma, rational-adelic/Stokes source data before Xi scalarization;
2. `A` retains prime, depth, divisor, multiplicity, and reflection provenance;
3. source exactness/positivity forces the fixed Burnol two-head defect to be nonpositive;
4. comparison with the already-formalized Bockstein/Stokes landing yields
   `BurnolXiCartierDividedShiftHeadFluxDissipativity`;
5. construction does not use RH, `Re rho = 1/2`, source-horizontal vanishing, source-dagger or
   same-fibre norm identity, forward/reflected sewing, or an equivalent endpoint predicate.

## Hostile falsifiers

- Completed-collar moment zero is insufficient: its kernel differs from Bockstein kernel and acts
  after the residue has been erased.
- Common determinant correction preserves the Bockstein zero radical and cannot create it.
- Fourier/reflection-invariant scalar readers erase the required odd orientation.
- Any claimed inequality obtained only after substituting an actual Xi divisor must be audited for
  equivalence to RH rather than accepted as source derivation.

## Gates

- [x] 0 → 1: exact source-pure question and circularity exclusions isolated
- [ ] conjecture survives internal and external audit
- [ ] complete dependency-closed paper proof
- [ ] Lean formalization
- [ ] RH

## Conjecture / proof-or-failure ledger

Active loop begins from the constructed horizontal carrier and the exact Burnol Bockstein/Stokes
landing. Each failed conjecture must record its killing mechanism and a stronger replacement.

## Log

- 2026-08-09 — reoriented after carrier construction and full Bockstein/Stokes formalization;
  independent pre-polar annihilation isolated as sole Route-R source producer.

## Heavy-loop ledger — 2026-08-09

### C1. Separate Stokes zero-moment laws

**Conjecture.** Forward and reflected orientations have independent zero-moment Stokes laws whose
difference forces the fixed two-head current to be nonpositive.

**Failure.** A prescribed forward head and a prescribed reflected head can each be cancelled by an
independent tail. Separate scalar exactness therefore imposes no comparison between the two head
norms. The missing statement is intrinsically cross-orientation.

**Pivot.** Couple the orientations before either scalar landing.

### C2. Kernel-only positive factorization

**Conjecture.** The Bockstein kernel is a completed Stokes boundary minus a positive square, making
its retained current nonpositive.

**Failure.** The completed collar has half-rate moment zero, whereas the Bockstein kernel has
half-rate moment `1/2`. Such a factorization would give a nonpositive half-rate moment on the right,
contradicting the exact positive moment on the left.

**Pivot.** Any valid annihilator must use the arithmetic source correlation, not only the universal
Gamma--Stein kernel.

### C3. Positive all-prime diagonal cancellation

For the prime window `[1/p,1]`, the two retained head sizes are `p-1` and `log p`. If
`1/2 < Re rho < 1`, then `|rho| > |1-rho|`, and for every prime `p`, `p-1 > log p`. Hence

```text
(p-1)^2 / |1-rho|^2 - (log p)^2 / |rho|^2 > 0.
```

**Failure.** Every nonzero nonnegative diagonal combination of ordinary-prime channels is strictly
positive at a hypothetical right-half point. Adding primes cannot cancel the dyadic defect.

**Pivot.** A surviving producer must be signed and off-diagonal, or a singular domain-admission
law; positive prime-diagonal energy is excluded.

### C4. Completion-current budget

**Conjecture.** Strict negativity of the completed Euler--Gamma current, together with negativity
of its completion-normal component, descends to nonpositivity of the bare Burnol head current.

**Failure.** The completed current is `A + J`. From `A+J<0` and `A<0`, no sign of `J` follows.
Indeed the already-proved right-half calculation gives `J>0` while the dressed current remains
negative. Completion hides the positive pre-polar channel instead of annihilating it.

**Pivot.** Work before polar completion and do not subtract two unrelated negative currents.

### C5. Source-blind regular Euler--Gamma operator

Let `phi(u)=exp(-u/2)` be the stable residue profile and `A = d/du + 1/2`, so `A phi=0`.
Let `tau_L` be translation by `L`; then `tau_L phi=exp(-L/2) phi`. Every finite operator
`Q(A,tau_L)` in the commuting regular Gamma--Stein/translation algebra therefore restricts on the
stable residue line to the scalar

```text
q = Q(0, exp(-L/2)).
```

If `q=0`, the operator kills the entire stable residue line and therefore erases every coefficient,
including the constructed carrier. If `q != 0`, it is coefficient-faithful but cannot annihilate a
nonzero carrier coefficient.

**Classification.** No source-independent finite regular Euler--Gamma Stein/dilation operator can
both retain and annihilate the constructed horizontal carrier.

**Pivot.** Remaining candidates are source-dependent cross-orientation pairings and singular,
unbounded domain-admission laws. Regular scalar functional calculus is closed.

### C6. Residue-Gram positivity

For arbitrary two-head coefficients `a,b`, put `B=(b-a)/2`. The two exterior residues are
`r=-a*conj(B)` and `rDual=b*conj(B)`. Directly,

```text
r + rDual = |a-b|^2 / 2 >= 0,
2 Re(r-rDual) = |a|^2 - |b|^2.
```

**Failure.** The positive Gram channel is the orientation-even sum. The desired current is the
orientation-odd difference and has no sign for arbitrary heads. Positivity of the residue Gram
matrix cannot orient it.

**Pivot.** A valid law must link the odd channel to a source boundary before endpoint evaluation;
endpoint positivity alone is structurally blind to the sign.

## Surviving producer class

After C1--C6, a valid independent producer must simultaneously be:

1. pre-polar and source-dependent;
2. cross-orientation and signed/off-diagonal;
3. coefficient-faithful on the stable residue line;
4. singular or domain-sensitive rather than finite regular Gamma--Stein functional calculus;
5. derived without assuming the Xi landing/sewing equality whose consequence is sought.

The concrete surviving realization already visible in the corpus is all-prime singular unsewing:
the sewn rational-adelic conormal is unconditionally square-summable, while membership in the
domain of the fixed inverse-completion operator is exactly the missing source admission. The next
conjecture must derive that domain admission from a pre-divisor source topology or Cartier boundary,
not restate it at Xi divisors.

## Same-carrier heavy loop -- 2026-08-09

### C7. Identify the two cyclic faces on the retained atom

**Conjecture.** The two ordinary cyclic faces have the same source trace, so the analytic dagger
must transport the retained coefficient through the same face.

**Failure.** The source face pair is diagonal `(c,c)`, while the analytic paracyclic face pair is
`(c, delta*c)`. Identifying these pairs is equivalent to `(delta-1)c=0`; coefficient faithfulness
then makes this the critical-line conclusion. Cyclicity does not identify the analytic dagger.

### C8. Symmetrize the ordinary-prime atom into a Hochschild cycle

**Conjecture.** Adding the cyclic rotation removes the ordinary Hochschild boundary and makes the
two transports chain-equal.

**Failure.** Symmetrization can close the source chain, but the physical landing is not known to be
a chain map for the analytic dagger. Adding that naturality square is the same missing equality.

### C9. Use prime--infinity product-formula cancellation

**Conjecture.** The adelic product formula identifies forward and reflected scale transports on one
source carrier.

**Failure.** The product formula gives reciprocal compatibility `alpha*beta=1` for every grade.
Physical annihilation needs `alpha=beta`. The two conditions meet only after the desired neutral
grade has already been supplied.

### C10. Compare multiplicative source clock and additive analytic response

**Conjecture.** The raw source clock law has a quadratic correction absent from the analytic
response, forcing the response to be neutral.

**Failure.** The logarithmic coordinate linearizes the multiplicative formal group exactly at
every grade. The raw correction is a coordinate artifact, not a source anomaly.

### C11. Transport the positive-shell conormal through finite ramified ambidexterity

**Conjecture.** The source Koszul conormal and finite ramified top-conormal adjunction canonically
identify the two physical Gamma transports.

**Failure.** Both conormals exist before the Xi divisor, but the strict coefficient-faithful map
from ramified power conormal to the singular physical Gamma dagger is absent. Finite
ambidexterity alone does not survive the all-prime singular landing.

### C12. Fisher-deconvolved fixed carrier

**Conjecture.** Move the universal Euler--Fisher density into the source topology instead of
inverting it after passage to the ordinary `ell^1` quotient. The remaining forward and reflected
half-character transports should then act coefficient-faithfully on one fixed carrier in opposite
horizontal chambers.

**Verdict.** `[PAPER-PROVED] [BRIDGE] [NOT RH PROOF]`.

Let `S = C^P`, where `P` is the set of ordinary primes, let

```text
d(p) = p/(p+1)^2,
I_d = {x in S : p |-> d(p)x(p) is summable},
Q_d = S/I_d.
```

This carrier is fixed before any spectral parameter. For a real centered grade `t`, define the
normalized forward and reflected transports

```text
u_t(p) = 1 + p^(-t),
u_t^vee(p) = u_(-t)(p) = 1 + p^t.
```

Every coefficient is strictly positive. The exact same-carrier theorem is

```text
M_(u_t) descends to a coefficient-faithful automorphism of Q_d  iff  0 <= t,
M_(u_t^vee) descends to a coefficient-faithful automorphism of Q_d  iff  t <= 0,
both descend on Q_d                                      iff  t = 0.
```

At `t=0` both transports are literally the same scalar multiplier `2`, not merely conjugate under
reflection.

#### Paper proof

For any prime sequence `m`, diagonal multiplication by `m` preserves `I_d` exactly when `m` is
bounded. If `m` is bounded, multiplication by `m` preserves summability and commutes with
multiplication by `d`. Conversely, suppose it preserves `I_d`. Given an arbitrary summable
sequence `y`, define `x(p)=y(p)/d(p)`. Positivity of `d(p)` gives `d*x=y`, hence `x in I_d`; the
preservation hypothesis gives `m*y=d*(m*x)` summable. Thus `m` preserves every `ell^1` sequence,
and the already-formalized diagonal multiplier theorem forces `m` bounded.

If `t>=0`, then `0<p^(-t)<=1`, so `1<=u_t(p)<=2`. Therefore both `u_t` and `u_t^-1` are bounded;
their descended maps are inverse automorphisms. If `t<0`, put `a=-t>0`. Ordinary primes tend to
infinity, so `p^a` and hence `u_t(p)=1+p^a` are unbounded. This proves the first equivalence. The
second follows after replacing `t` by `-t`; conjunction gives `t=0`. At zero both formulas reduce
pointwise to `2`.

The original comparison coefficient satisfies

```text
r_t(p) = d(p)u_t(p),
b_t(p) = -d(p)u_t(p)(p^t-1).
```

Thus the construction preserves the literal prime coefficient and divisor multiplicity scalar;
it changes only where the universal Fisher damping is stored. On `S/ell^1`, `M_(r_t)` is
surjective but noninjective and its reciprocal does not descend. On `Q_d`, the normalized
transport is an automorphism exactly in its oriented half-space. This is the required
coefficient-faithful, non-equivariant same-carrier classification.

#### Hostile audit and exact remaining producer

This theorem holds for every real `t` and uses no Xi zero, line placement, or vanishing premise.
It does **not** show that an actual Xi divisor supplies both quotient actions. Source involution
only moves an orientation-dependent carrier to its reflected carrier; it does not prove that both
normalized analytic actions preserve this fixed `I_d` carrier. Claiming simultaneous descent at
every Xi divisor would be equivalent to RH by the theorem above.

The remaining source law is therefore narrower and literal:

`[OPEN CORE] FISHER_DECONVOLVED_TWO_ORIENTATION_SOURCE_DESCENT` -- construct, from the
pre-divisor rational-adelic/Cartier source and before Xi scalarization, both normalized operations
on `Q_d`; prove their representative actions are `u_t` and `u_-t` while retaining prime labels,
divisor multiplicity, and the two reflection orientations. Equivariance, product formula, or an
orientation-dependent norm is insufficient.

### C13. Put both normalized coefficient fields in the carrier before asking for endomorphisms

**Conjecture.** The C12 endomorphism formulation asks too much: each orientation need not preserve
`I_d` separately in order for both coefficient fields to be compared inside `Q_d`. Define

```text
U_t = [p |-> 1 + p^(-t)] in Q_d,
U_t^vee = U_(-t) = [p |-> 1 + p^t] in Q_d.
```

Both classes exist unconditionally for every real `t` in the same fixed carrier. Their difference
is not an abstract comparison:

```text
d(p) * (U_t(p) - U_t^vee(p)) = b_t(p)
```

prime by prime, where `b_t` is the literal signed Gamma Bockstein.

**Verdict.** `[LEAN-PROVED] [BRIDGE] [NOT RH PROOF]`.

Because membership in `I_d` is summability after multiplication by `d`, equality in `Q_d` gives

```text
U_t = U_t^vee
  iff p |-> b_t(p) is absolutely summable
  iff t = 0.
```

The last equivalence is the already proved sharp all-prime Gamma-Bockstein trace wall. This is
strictly stronger than C12 as a representation result: both transports are now present on one
fixed carrier for every grade, and their coefficient-wise difference is identified without
inverting Fisher density in the ordinary quotient. Prime labels are never summed; a later nonzero
Xi leading-jet scalar may be attached without changing the equality radical, so divisor
multiplicity is retained.

Lean module:
`formal/GaloisForLFunctions/RHTower/FisherDeconvolvedSameCarrierOrientationLaw.lean`.
Principal theorem: `fisherDeconvolvedOrientationClass_eq_reflected_iff`.

**Exact remaining source producer.** C13 removes carrier and coefficient-identification gaps. The
only missing statement is now a non-equivariant pre-divisor relation proving `U_t=U_t^vee` for the
two analytic transports attached to each actual Xi divisor. Source involution gives
`U_t at rho` corresponding to `U_-t at J(rho)`; it does not identify them in one fixed fibre.
Any theorem making that final identification globally is RH-equivalent by C13 and must be derived
from new rational-adelic/Cartier boundary input, not asserted as naturality.

## Formalization extraction -- 2026-08-11

### C14. Ordinary-prime diagonal cone

The C3 pointwise sign is now `[LEAN-PROVED]`, including closure under every nonempty finite positive
prime-diagonal combination. Module:
`RHTower/BurnolPrimeWindowDiagonalHeadFluxNoGo.lean`. Stage-3 card:
`3-formalized/new_scientific_knowledge/burnol-prime-window-diagonal-head-flux-no-go.md`.

This closes the whole finite positive diagonal cone, not only the dyadic channel. It does not
annihilate the carrier; it proves that this producer class has the wrong strict sign.

### C15. Finite regular Gamma--Stein/translation algebra

The C5 classification is now `[LEAN-PROVED]`. A free finite expression syntax retains scalar
leaves, the Stein generator, arbitrary translations, addition, and noncommutative composition.
Every expression restricts to its recursively computed scalar gain on the stable residue line.
Annihilation is equivalent to zero gain and coefficient faithfulness to nonzero gain, so both are
incompatible. Module:
`RHTower/BurnolStableResidueRegularOperatorClassification.lean`. Stage-3 card:
`3-formalized/new_scientific_knowledge/burnol-stable-residue-regular-operator-classification.md`.

### C16. Functional-equation partner current

The reflection partner `rho^dagger=1-conj(rho)` exchanges the two reciprocal heads. The exact odd
current is

```text
(1+(log 2)^2)(2 Re rho-1)/(|rho|^2 |1-rho|^2),
```

while the bare pair sum is strictly positive. Completion cancels from the odd coordinate because
the partner preserves imaginary part. Therefore bare or dressed scalar partner equality on all Xi
divisors is exactly RH, not an independent functional-equation law. This is `[LEAN-PROVED]` in
`RHTower/RouteRBurnolReflectionPartnerCurrent.lean`; stage-3 card:
`3-formalized/new_scientific_knowledge/route-r-burnol-reflection-partner-current-classification.md`.

**Open core unchanged.** C14--C16 close three false producer classes and make their exact positive
survivors reusable. They do not supply the missing non-equivariant, singular pre-divisor
rational-adelic/Cartier relation identifying the two fixed-carrier orientations. The parent card
therefore remains stage 1.
