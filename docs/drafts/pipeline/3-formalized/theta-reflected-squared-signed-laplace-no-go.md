# Theta reflected squared-profile finite signed Laplace obstruction

- **ID:** C5-SIGNED-LAPLACE-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `theta-reflected-squared-atomic-laplace-no-go.md` · continuous-carrier survivor
- **Statement:** No finite signed Borel measure on `[0,∞)` represents
  `x ↦ Φ(u+sqrt x) Φ(u-sqrt x)` as a fixed Laplace transform.

## Goal

Hostile-test the strongest finite signed-measure survivor left by the positive and atomic no-go
theorems.  The carrier may be continuous, accumulate at zero, have no first active spectral shell,
and cancel arbitrarily through its Jordan decomposition.

## Gates

- [x] 0 → 1 in-progress: exact signed-measure claim and half-plane rigidity mechanism identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: exact Lean theorem and targeted build
- [ ] 3 → 4 publication-ready: standalone priority audit and exposition

## Internal frontier

- `[CORPUS]` `tendsto_exp_mul_thetaCuspReflectedSquaredProduct_atTop_zero` proves faster-than-every-
  exponential decay in squared displacement.
- `[CORPUS]` `measure_eq_of_laplace_eq` proves uniqueness of finite positive half-line measures from
  their real Laplace transforms by exponential compactification and compact moment determinacy.
- Current Mathlib supplies right-half-plane Phragmén--Lindelöf quasi-analyticity for holomorphic
  functions with superexponential real-axis decay.
- Corpus search found no finite signed-measure obstruction for the completed-theta reflected square.

## External frontier

The generic ingredients are classical: finite signed measures admit Jordan decomposition, Laplace
transforms are bounded and holomorphic on the right half-plane, Phragmén--Lindelöf gives a
quasi-analyticity principle there, and Laplace transforms determine finite measures.  Search through
August 2026 found literature on those separate mechanisms, but no source applying their combination
to the completed-theta reflected squared profile.  The generic rigidity mechanism is therefore not
claimed as new; its exact source-pure application is novelty-unverified.

## Conjecture loop

`[CONJECTURE A]` A continuous finite signed carrier with support accumulating at zero can cancel all
finite leading exponential scales and represent the squared theta profile.

Hostile mechanism: the difference of the positive and negative Jordan transforms is bounded on the
closed right half-plane, holomorphic inside, and bounded on the imaginary axis.  If it decays faster
than every exponential on the positive real axis, Phragmén--Lindelöf forces the difference to vanish
on the whole closed half-plane.  Laplace uniqueness then identifies the Jordan measures.

**Verdict: FALSE.**  No support-onset or local noncancellation hypothesis is needed.

## Complete paper proof

Let `μ` and `ν` be finite positive measures carried by `[0,∞)` and set

```text
F(z)=∫ exp(-zr)dμ(r),       G(z)=∫ exp(-zr)dν(r).
```

For `Re z≥0`, both kernels have modulus at most one.  Thus `F` and `G` are continuous on the closed
right half-plane, bounded there by total mass, and uniformly bounded on the imaginary axis.  For
`Re z>0`, differentiation under the integral is valid: on a ball whose real parts stay above
`b>0`, the derivative kernel is bounded by

```text
r exp(-br) ≤ b⁻¹.
```

Hence both transforms are holomorphic in the open right half-plane and have order-zero growth.

Assume their difference decays superexponentially on the positive real axis:

```text
exp(nx) |F(x)-G(x)| → 0                         for every n∈ℕ.
```

Right-half-plane Phragmén--Lindelöf rigidity gives `F=G` throughout the closed half-plane.  In
particular their real Laplace transforms agree for every `x>0`; finite-measure Laplace uniqueness
gives `μ=ν`.  Therefore a finite signed measure whose Laplace transform has this decay is zero.

Now assume

```text
Φ(u+sqrt x)Φ(u-sqrt x)=F(x)-G(x),               x≥0.
```

The formal theta tail supplies the required superexponential decay, so `μ=ν` and the right-hand side
is identically zero.  At `x=0`, however, the left-hand side is `Φ(u)²>0`.  Contradiction.

## No-go closure

- **Exact killing theorem:** no fixed finite signed Borel measure on `[0,∞)` represents the squared
  reflected completed-theta profile.
- **Strongest positive survivor:** superexponential signed-Laplace rigidity for arbitrary finite
  half-line measures, with continuous support and unrestricted Jordan cancellation.
- **Route classification:** any viable transform route must leave finite signed measures: use
  infinite variation or distributions, depend on scale, use a nonlinear transform, or act before
  the `t↦t²` pullback.
- **New invariant:** right-half-plane quasi-analyticity converts all-order exponential cancellation
  on the real ray into equality of the full carrier measures.
- **Status:** `[LEAN-PROVED]`; exact completed-theta application is novelty-unverified.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedSquaredSignedLaplaceNoGo`

- `finiteComplexLaplace`
- `diffContOnCl_finiteComplexLaplace`
- `finiteComplexLaplace_rightHalfPlane_growth`
- `finiteMeasures_eq_of_superexponential_laplace_difference`
- `not_exists_finiteSignedLaplaceRepresentation_thetaCuspReflectedSquaredProduct`

Audit: direct `lake env lean` passed; targeted module build passed; public capstone and rigidity
theorem use only standard quotient/extensionality/classical-choice axioms.

## Log

- 2026-08-28 — continuous/no-isolated-onset survivor extracted from atomic no-go; corpus
  Phragmén--Lindelöf and Laplace-uniqueness mechanisms combined.
- 2026-08-28 — arbitrary finite signed carrier falsified; exact generic rigidity and theta no-go
  formalized, wired, built, and axiom-audited.
