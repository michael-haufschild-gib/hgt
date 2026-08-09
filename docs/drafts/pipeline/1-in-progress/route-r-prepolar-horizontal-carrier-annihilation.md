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
