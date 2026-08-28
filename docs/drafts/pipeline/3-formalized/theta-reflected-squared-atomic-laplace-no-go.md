# Theta reflected squared-profile atomic Laplace obstruction

- **ID:** C5-ATOMIC-LAPLACE-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `theta-reflected-squared-bernstein-no-go.md` · signed/cancellation survivor
- **Statement:** No fixed absolutely summable signed or complex atomic Laplace series with a finite,
  noncancelled lowest-frequency shell represents
  `x ↦ Φ(u+sqrt x) Φ(u-sqrt x)` on `x ≥ 0`.

## Goal

Hostile-test the discrete signed survivor left by the positive Bernstein no-go.  Literal theta
atom--ray constructions naturally produce countable exponential pencils.  If such a pencil has an
`ℓ¹` coefficient family and a finite first active frequency shell, cancellation cannot erase its
leading exponential scale.

## Gates

- [x] 0 → 1 in-progress: exact source-pure claim and corpus mechanism identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: exact Lean theorem and targeted build
- [ ] 3 → 4 publication-ready: standalone priority audit and exposition

## Internal frontier

- `[CORPUS]` `tendsto_exp_sq_mul_thetaCuspReflectedSourceProduct_atTop_zero` proves faster-than-every-
  exponential decay after the squared-displacement substitution.
- `[CORPUS]` `not_tendsto_tsum_normalizedExponentialPencil_zero_of_dominantFinset` proves that a
  summable exponential pencil cannot hide a finite nonzero dominant mode packet.
- Corpus search found no application of this dominant-packet theorem to the completed-theta
  reflected squared profile.

## External frontier

Classical Laplace asymptotics recover behavior from the transform's lowest active spectral region;
see NIST DLMF §2.3 for Watson-type Laplace expansions.  The present theorem uses the discrete
`ℓ¹` version with complex coefficients and repeated-frequency cancellation.  Search through
August 2026 found no source applying this obstruction to the completed-theta reflected squared
profile.

## Conjecture loop

`[CONJECTURE A]` A fixed `ℓ¹` signed atomic Laplace representation may survive despite the positive
measure obstruction.

Hostile mechanism: after multiplying by the exponential rate of the lowest active shell, every
higher shell vanishes by dominated convergence while the finite lowest shell remains.  Theta's
squared profile instead vanishes after multiplication by every nonnegative exponential rate.

**Verdict: FALSE.**  The hostile mechanism closes with complex coefficients and already from
integer squared-scale samples.

## Complete paper proof

Let `cᵢ∈ℂ` be absolutely summable, let `λᵢ≥0`, and suppose a finite set `D` is the lowest
frequency shell:

```text
λᵢ=N       for i∈D,
λᵢ>N       for i∉D,
Σ_{i∈D} cᵢ ≠ 0.
```

Assume

```text
P_u(sqrt x)=Σᵢ cᵢ exp(-x λᵢ),       x≥0.
```

Sampling at `x=n` and multiplying by `exp(Nn)` gives

```text
exp(Nn)P_u(sqrt n)=Σᵢ cᵢ exp(-n(λᵢ-N)).
```

Absolute summability dominates every normalized term by `|cᵢ|`.  For `i∉D` its factor tends to
zero, so dominated convergence kills the complement.  Every mode in `D` is identically one, hence
the normalized series tends to the nonzero shell aggregate `Σ_{i∈D}cᵢ`.  Equivalently, the corpus's
finite dominant-packet theorem rules out convergence to zero even when repeated modes are combined
first.

But the formalized theta tail gives

```text
exp(Nx)P_u(sqrt x) → 0
```

for every `N≥0`, hence also along `x=n`.  Contradiction.

## No-go closure

- **Exact killing theorem:** no fixed `ℓ¹` complex atomic Laplace series with a finite noncancelled
  lowest shell represents the profile, even on integer squared scales.
- **Strongest positive survivor:** any viable cancellation representation must evade at least one
  structural hypothesis: it must have no finite first active shell, fail fixed `ℓ¹` summability,
  depend on scale, use a continuous carrier without an isolated onset, or act before `t↦t²`.
- **New invariant:** first-active-shell survival after squared-scale exponential normalization.
- **Status:** `[LEAN-PROVED]`; generic dominant-packet survival is `[CORPUS]`, while its exact
  completed-theta application is novelty-unverified.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.ThetaCuspReflectedSquaredAtomicLaplaceNoGo`

- `tendsto_exp_mul_thetaCuspReflectedSquaredProduct_atTop_zero`
- `not_summableDominantPencil_represents_thetaCuspReflectedSquaredProduct`
- `not_summableAtomicLaplace_represents_thetaCuspReflectedSquaredProduct_at_nat`
- `not_summableAtomicLaplace_represents_thetaCuspReflectedSquaredProduct`

Audit: direct `lake env lean` passed; targeted module build passed; all four public results use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-28 — conjecture extracted from positive Bernstein no-go survivor; dominant finite-packet
  corpus theorem identified as hostile mechanism.
- 2026-08-28 — conjecture falsified at integer squared scales; exact complex `ℓ¹` theorem and
  continuous-ray Laplace corollary formalized, wired, built, and axiom-audited.
