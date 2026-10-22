# Suzuki safe-shift transverse-charge budget and strict dispersion

- **ID:** `suzuki-safe-shift-transverse-charge-budget`
- **Stage:** 3-formalized
- **Type:** THEOREM / QUANTITATIVE SUZUKI TWO-JET FRONTIER
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL]`
  `[SOURCE-SPECIFIC] [NOVELTY-BOUNDARY-AUDITED] [NOT AN RH PROOF]`
- **Parent:** `suzuki-safe-shift-response-charge-cancellation`
- **RH used:** no

## Exact frontier

The complete safe-shift decomposition is

```text
AC-B^2 = H_1-Q_1,

H_1=A sum_q a_q tau_q^2-(sum_q a_q tau_q)^2 >= 0,
Q_1=A sum_q chi_q >= 0,
Q_1=0 iff RH.
```

It left both magnitudes uncontrolled.  A generic positivity argument cannot compare them:
one off-line atom contributes a negative minor, while arbitrarily concentrated positive response
packets can have arbitrarily small dispersion.

## Competing conjectures

### SR-62A: safe shifting quantitatively damps transverse charge `[PROVED]`

Let

```text
N_q=xiSquaredNode(q),
r_q=N_q^(-1),
lambda_q=(1+N_q)^(-1).
```

Then

```text
xiShiftedResponseMass(1,q) < Re(r_q),                    (SR-62.1)

chi_q <= (4/85) Im(r_q)^2.                               (SR-62.2)
```

Consequently, with

```text
mu_0 = normalizedPrimeArchMoment(0),
E    = sum_q Im(r_q)^2,
```

the complete charge satisfies

```text
Q_1 <= (4/85) mu_0 E.                                    (SR-62.3)
```

The existing exact cubic endpoint estimate and source bounds imply

```text
Q_1 <= (4/85) mu_0 xiThermalExactCubicEndpointBudget,
Q_1 < 116/7,968,750,000.                                 (SR-62.4)
```

### SR-62B: infinite divisor support forces strict response dispersion `[PROVED]`

At every `y>0`, the shifted slopes tend to zero off finite sets and are all positive.  Hence they
cannot be constant.  The exact centered-energy identity is

```text
H_y = M_0(y) sum_q a_q (tau_q-bar_tau_y)^2 > 0,           (SR-62.5)

bar_tau_y=M_1(y)/M_0(y).
```

This strengthens nonnegativity to strict positivity without RH.

### SR-62C: the explicit dispersion floor `[OPEN CORE]`

The single unconditional source inequality

```text
116/7,968,750,000 <= H_1                                (SR-62.6)
```

would imply the strict Suzuki wall `AC-B^2>0`.  The corpus currently proves `(SR-62.5)` but not
the quantitative floor `(SR-62.6)`.  No claim that strict positivity alone dominates charge is
allowed.

## Complete paper proof

### 1. Pointwise charge damping

Write

```text
N_q=(A-1)+iB,   A=1+Re N_q.
```

The critical strip and endpoint height gap give

```text
Re N_q>81/4,   hence A>85/4.
```

Put

```text
D_0=(A-1)^2+B^2,   D_1=A^2+B^2.
```

Then

```text
r_q=N_q^(-1),       Im(r_q)^2=B^2/D_0^2,
lambda_q=(1+N_q)^(-1),
Re(lambda_q)=A/D_1,
Im(lambda_q)^2=B^2/D_1^2,
|lambda_q|^2=1/D_1.
```

Therefore

```text
chi_q
 =Im(lambda_q)^2 |lambda_q|^2/Re(lambda_q)
 =B^2/(A D_1^2)
 <=(1/A) B^2/D_0^2
 <=(4/85) Im(r_q)^2,
```

which proves `(SR-62.2)`.

For the mass comparison,

```text
Re(lambda_q)=A/D_1,
Re(r_q)=(A-1)/D_0.
```

The shifted sector theorem gives `84B^2<A^2`.  Since `A>85/4`,

```text
A^2<84A(A-1),
```

and hence `B^2<A(A-1)`.  Cross multiplication now gives

```text
A D_0 < (A-1)D_1,
```

which is `(SR-62.1)`.

### 2. Complete charge budget

All relevant sequences are absolutely summable.  Summing `(SR-62.1)` and using the exact central
source identity gives

```text
M_0(1)=sum_q Re(lambda_q)
      <=sum_q Re(r_q)
      =mu_0.
```

Summing `(SR-62.2)` gives

```text
sum_q chi_q <=(4/85)E.
```

Both factors are nonnegative, so multiplication proves `(SR-62.3)`.

The already formalized source bounds are

```text
mu_0<29/625,
E<1/150000,
E<=xiThermalExactCubicEndpointBudget.
```

Substitution yields

```text
Q_1
 <(4/85)(29/625)(1/150000)
 =116/7,968,750,000,
```

proving `(SR-62.4)`.

### 3. Cofinal slope separation

For `z=lambda_q(y)` and `a=Re z>0`,

```text
tau_q(y)=Re(z^2)/a=(a^2-Im(z)^2)/a.
```

Thus

```text
0<tau_q(y)<=a<=|z|.
```

Absolute summability of the shifted atoms implies `|z| -> 0` on the cofinite filter, so
`tau_q(y)->0` there.  Since every slope is strictly positive and the Xi multiplicity-copy type is
infinite, two slopes differ.

### 4. Exact centered energy and strictness

Set

```text
A_y=sum_q a_q,
B_y=sum_q a_q tau_q,
bar_tau_y=B_y/A_y.
```

Absolute summability permits expansion of the centered square:

```text
A_y sum_q a_q(tau_q-bar_tau_y)^2
 =A_y sum_q a_q tau_q^2-B_y^2
 =H_y.
```

At least one slope differs from the mean, every mass is positive, and every squared centered term
is nonnegative.  Hence the centered sum is strictly positive.  Since `A_y>0`, `(SR-62.5)` follows.

### 5. Quantitative last step

From the parent cancellation theorem and `(SR-62.4)`,

```text
AC-B^2=H_1-Q_1
      >H_1-116/7,968,750,000.
```

Therefore `(SR-62.6)` implies `AC-B^2>0`.  This is a sufficient source floor, not a proved
inequality and not a necessary reformulation.

## Hostile audit

1. **No RH smuggling.**  Inputs are critical-strip confinement, endpoint height/sector bounds,
   infinite Xi divisor support, summability, and already-proved prime--Gamma endpoint estimates.
2. **No numerical evidence.**  Every constant is obtained by exact rational inequalities in Lean.
3. **Not a renamed moment bound.**  `(SR-62.2)` compares the actual safe Möbius charge with the
   central RH-exact orientation energy atom by atom; `(SR-62.5)` proves strict complete-divisor
   dispersion through cofinite slope decay.
4. **No false closure.**  A positive number need not exceed the explicit charge cap.
   `(SR-62.6)` remains unproved.
5. **No Suzuki convergence claim.**  Common-gauge normality, source-selected aperture convergence,
   and Xi/de Branges identification remain independent open gates.
6. **No illicit source-horizon transfer.**  Finite shell support for differential-field
   observables does not control locally uniform or weak limits with growing supports.

## Novelty boundary

- Classical content: elementary inverse-coordinate algebra, summation of pointwise inequalities,
  centered variance identity.
- Existing corpus: the parent card proves only `H_y>=0`, `Q_y>=0`, and the signed decomposition.
  Thermal modules bound central orientation energy but do not transport that bound through
  Suzuki's safe Möbius shift or prove strict shifted response dispersion.
- Suzuki's 2026 paper constructs the finite screw/extension family and conjectures its limiting
  operator.  It does not contain `(SR-62.1)--(SR-62.6)`.
- Targeted theorem and current arXiv searches found generic Xi/Turán, Hankel, and moment literature,
  but no collision with this safe-shift damping law, absolute charge cap, or strict complete-divisor
  response theorem.  Priority remains subject to specialist review.

Candidate new knowledge is the pair of source-specific quantitative facts: Suzuki's complete
safe-shift transverse obstruction is smaller than an explicit rational scale, while its positive
response channel is genuinely nondegenerate.  The surviving hard core is no longer qualitative
positivity but the explicit dispersion floor `(SR-62.6)`.

## Lean formalization

Module:

```text
formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiSafeShiftTransverseChargeBudget.lean
```

Capstones:

```text
xiShiftedResponseMass_one_lt_xiThermalNode
xiShiftedTransverseChargeDensity_one_le_four_div_eightyFive_mul_orientation
tendsto_xiShiftedResponseSlope_cofinite_zero
xiShiftedResponseHilbertDispersion_eq_centeredSlopeEnergy
xiShiftedResponseHilbertDispersion_pos
xiShiftedTransverseCharge_one_le_centralOrientationBudget
xiShiftedTransverseCharge_one_le_exactCubicEndpointBudget
xiShiftedTransverseCharge_one_lt_absoluteBudget
primeArchSafeShiftHankelMinor_pos_of_absoluteBudget_le_dispersion
```

All statements are unconditional.  The final theorem assumes only the explicit open floor
`(SR-62.6)` and exposes it in its type.

## Gates

- [x] Paper proof dependency-closed
- [x] Unconditional Lean proof
- [x] Imported by `RHTower.lean`
- [x] `#print axioms` audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] Targeted module build
- [x] Formal lint for this module; global lint reports five unrelated un-wired dirty-worktree
  modules (`DeningerPoissonMoebius`, `StaticChoiQuantitativeRecurrenceUpperLaw`,
  `PhysicalObserverSpectralLeafExtension`, `PhysicalObserverSpectralRealization`,
  `PhysicalTwoQubitGraphSeed`)
- [x] Route G, ledgers, and manuscript updated

## Log

- 2026-08-01 — SR-62A/B conjectured after exact response/charge cancellation.
- 2026-08-01 — Pointwise damping, complete charge cap, centered-energy identity, strict
  dispersion, and explicit sufficient floor proved on paper and in Lean.
