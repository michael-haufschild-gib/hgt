# Route P primitive Gamma--Julia physical Stokes Hellinger ordinary determinant

- **ID:** `route-p-primitive-gamma-julia-physical-stokes-hellinger-ordinary-determinant`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105N]`
- **Parents:** `route-p-primitive-gamma-julia-physical-stokes-hellinger-cofinal-determinant.md`,
  `route-p-primitive-gamma-julia-stokes-cofinal-child-trace-class.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryDeterminant.lean`

## Goal

Restore ordinary determinant for full physical Hellinger channel, retain literal finite physical
pencils, and determine whether indefinite channel destroys trace class.

## Conjecturing loop

### Conjecture 1 — finite signed Hellinger channel prevents trace class

**Falsified by canonical positive difference.** For `r >= 0`, physical channel has exact
decomposition

```text
A_r = (diag(65, 1) + v_r v_r*) - (64 + r) I,
v_r = (sqrt(r), 8 delta),   delta^2 = 63/64.
```

Both channel matrices on right are positive semidefinite. Tensoring each with positive trace-class
child gives positive trace-class operators; their difference is the full physical operator.

### Conjecture 2 — entrywise channel tensor positivity is enough without finite-block audit

**Rejected.** Positivity of infinite represented tensor was proved from every finite product block,
then operator-norm cofinal limit. Each finite product block is a principal submatrix of a finite
Kronecker product of two positive semidefinite matrices. This keeps proof tied to actual kernel.

### Conjecture 3 — ordinary determinant is `exp(z Tr T) det2(I-zT)`

**Falsified by sign audit.** Corpus `entireDet2 K(z)` represents `det2(I-zT)`, while physical pencil
is `I+zT`. Correct ordinary determinant is reflected:

```text
D(z) = exp(z Tr T) entireDet2 K(-z).
```

Missing reflection would give wrong finite pencils and is not a harmless normalization.

### Conjecture 4 — trace-restored finite functions may only match spectrally

**Falsified exactly.** For every finite packet `s`, finite trace compensation and finite det2
identity cancel to the literal determinant

```text
exp(z Tr(T_s)) det2(I+zT_s) = det(I+zT_s).
```

No limiting argument or fitted scalar enters this equality.

### Conjecture 5 — ordinary trace loses completed-current normalization

**Falsified.** Basis-diagonal trace theorem gives `Tr(T_{d,r})=(1-r) Stokes(d)`. At forced polar
ratio this is exactly completed prime--Gamma current. Finite traces converge to this operator trace,
and finite ordinary determinants converge pointwise to full ordinary determinant.

## Paper proof

Exact defect identity verifies positive-difference channel decomposition. Generic channel tensor
kernel is Hilbert--Schmidt and Hermitian. Finite Kronecker positivity followed by cofinal
operator-norm limit proves each positive channel component positive; P-G105M's diagonal criterion
makes each Schatten-one. Linearity gives physical trace-class membership and exact diagonal trace.

Define ordinary determinant with reflected argument. Exponential factor is entire and nonvanishing,
so zero set is unchanged from self-adjoint det2 and hence real. Finite-dimensional det2 restoration
gives literal finite physical determinant. Cofinal trace sums converge by absolute summability;
continuity of exponential and P-G105L det2 convergence yield pointwise convergence. `QED`

## Novelty and anti-theatre audit

This materially changes route state:

- indefinite physical operator is now proved trace class, not merely Hilbert--Schmidt;
- decomposition is canonical and exact, retaining all channel and cross-prime incidence;
- ordinary determinant sign is audited against actual pencil convention;
- every finite approximant is literal `det(I+zT_s)`;
- ordinary trace recovers source-forced completed current exactly;
- full ordinary determinant has only real zeros.

Result is not RH. Pointwise finite convergence is insufficient for divisor passage; local-uniform
ordinary convergence, aperture-wall convergence, nontrivial divisor retention, and Xi divisor
identification remain open.

## Formal status

Lean proves unconditionally:

- exact positive-shift-minus-counter channel decomposition;
- generic positive channel tensor positivity and Schatten-one membership;
- physical operator Schatten-one membership for positive aperture and nonnegative ratio;
- generic trace-equals-basis-sum theorem for Schatten-one operators;
- exact physical trace and forced-ratio completed-current specialization;
- differentiability and real-zero law for reflected ordinary determinant;
- exact finite literal determinant identity;
- finite-trace and pointwise finite-determinant cofinal convergence;
- P-G105N capstone over full physical parameter domain.

Direct Lean and axiom audit pass; only `propext`, `Classical.choice`, and `Quot.sound` are reported.
Target-only Olean audit is pending serialized cache stabilization. Module is umbrella-wired; no
umbrella build was run.

## Refined open core

Upgrade pointwise ordinary determinant convergence to local uniform convergence on compact sets.
Then prove `d -> 0+` local-uniform convergence with a nonzero limiting determinant, establish
nontrivial divisor retention at wall, and identify wall divisor with Xi using source transport rather
than target fitting.

## Higher universal principle

Signed Eulerian limits need not be positive; they need finite positive variation in operator order.
Physical channel is a Jordan decomposition over source-positive child, and trace class is stable
under that finite variation. Earlier nuclearity obstruction was shadow of demanding positivity from
signed colligation instead of decomposing its finite channel measure. Reflection in determinant
parameter is second categorical shadow: additive pencil orientation and regularized determinant
orientation are contravariant and must be matched before taking limits.

## Log

- 2026-08-16 — Physical trace class, exact ordinary trace, reflected ordinary determinant, finite
  literal determinant identity, real-zero law, and pointwise cofinal convergence paper-proved and
  formalized.
