# Burnol stable-residue regular-operator classification

- **ID:** `burnol-stable-residue-regular-operator-classification`
- **Stage:** 3 — formalized
- **Type:** THEOREM (Lean) / EXACT NO-GO CLASSIFICATION
- **Route:** R
- **Scientific status:** `[LEAN-PROVED] [NO-GO CLOSED] [NOT RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/BurnolStableResidueRegularOperatorClassification.lean`

## Statement

Let

```text
phi(u) = exp(-u/2),       A = d/du + 1/2,       tau_L f(u) = f(u+L).
```

For every finite expression `Q` generated from real scalars, `A`, the translations `tau_L`,
addition, and composition, there is an explicitly recursive scalar `gain(Q)` such that

```text
Q(c phi) = gain(Q) c phi
```

for every real coefficient `c`. Moreover,

```text
Q(phi)=0                         iff gain(Q)=0,
Q is coefficient-faithful on R phi iff gain(Q) != 0.
```

Therefore no such finite regular operator can both annihilate the literal stable carrier and retain
its coefficient.

Principal Lean theorems:

```text
BurnolRegularResidueOperator.act_stableResidueCarrier
BurnolRegularResidueOperator.annihilatesStableResidue_iff_stableGain_eq_zero
BurnolRegularResidueOperator.coefficientFaithfulOnStableResidue_iff_stableGain_ne_zero
BurnolRegularResidueOperator.not_annihilatesStableResidue_and_coefficientFaithful
```

## Dependency-closed paper proof `[PROVED HERE]`

Direct differentiation gives `A phi=0`. Translation gives

```text
tau_L phi(u)=exp(-(u+L)/2)=exp(-L/2) phi(u).
```

Define the gain recursively: a scalar leaf has that scalar as gain, the Stein leaf has gain zero,
translation by `L` has gain `exp(-L/2)`, addition adds gains, and composition multiplies gains.
Structural induction on the expression proves `Q(c phi)=gain(Q)c phi`. Since `phi(0)=1`, the
function `c phi` is zero exactly when `c=0`. The two equivalences and incompatibility follow.

The syntax retains noncommutative composition rather than assuming a commutative polynomial normal
form, so the result covers a larger finite regular operator class than the original conjecture.

## No-go closure

- **Exact killing mechanism:** the stable residue line is a joint one-dimensional eigenspace for
  every regular generator. Finite regular functional calculus cannot create a coefficient-sensitive
  radical inside that line.
- **Strongest positive survivor:** exact gain classifier for every finite expression, including
  addition and arbitrary composition.
- **New insight:** a valid Route-R annihilator cannot be a source-blind finite regular
  Gamma--Stein/translation operator. It must use source-dependent cross-orientation data or a
  singular/domain-sensitive operation.
- **Exact frontier:** this theorem excludes a producer class; it does not construct the remaining
  singular source law and does not imply horizontal carrier annihilation.

## Gates and verification

- [x] well-posed source-facing operator class
- [x] dependency-closed paper proof
- [x] unconditional Lean formalization; no RH or Xi premise
- [x] wired into `RHTower.lean`
- [x] direct `lake env lean` check
- [x] targeted `lake build GaloisForLFunctions.RHTower.BurnolStableResidueRegularOperatorClassification`
- [x] axiom audit: `[propext, Classical.choice, Quot.sound]`
- [x] corpus formal lint

## Log

- 2026-08-11 — paper proof extracted from Route-R heavy-loop conjecture C5.
- 2026-08-11 — formalized and promoted to stage 3.
- 2026-08-11 — targeted build, axiom audit, and lint passed.
