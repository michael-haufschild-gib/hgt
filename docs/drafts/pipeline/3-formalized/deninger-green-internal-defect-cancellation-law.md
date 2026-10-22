# Deninger Green internal-defect cancellation law

- **ID:** HGT-deninger-green-internal-defect-cancellation
- **Stage:** 3-formalized
- **Type:** THEOREM / FRONTIER-LOCALIZATION
- **Source:** `DeningerArithmeticSourceGreen`, `RiemannBoundaryGreenFractureLaw`,
  `DerivedPolarizationLaw`, and the Euler common-test polarized chain
- **Statement:** The unconditional covariance of the finite Deninger source Green map is exact
  cancellation of two generally nonzero anti-linear covariance defects.  Each factor defect is
  multiplication by the signed Riemann boundary fracture; reflection reverses that fracture, so
  the composite linear Green map loses it identically.

## Theorem DGIC

On multiplicity-exact finite divisor jets let

```text
Theta       = ordinary Frobenius,                 eigenvalue rho,
Theta_c     = compact-support Frobenius,           eigenvalue 1-rho,
C           = coefficientwise conjugate Riesz map,
J           = oriented anti-linear Hodge map,
G           = oriented source Green map = -J C,
kappa(rho)  = rho + conjugate(rho) - 1
            = 2 (Re rho - 1/2).
```

Define the two internal covariance defects

```text
delta_C = Theta C - C Theta_c,
delta_J = Theta J - J Theta.
```

Then, at every divisor copy `q`,

```text
(delta_C a)_q = kappa(q) (C a)_q,                         (DGIC.1)
(delta_J b)_q = kappa(q) (J b)_q.                         (DGIC.2)
```

Since functional-equation reflection sends `kappa` to `-kappa` and `J` is anti-linear and
reflection-indexed,

```text
delta_J(Ca) + J(delta_C a) = 0.                           (DGIC.3)
```

Consequently

```text
Theta G = G Theta_c                                      (DGIC.4)
```

holds unconditionally even when both internal defects are nonzero.  For the basis source at `q`,
`delta_C=0` is equivalent to `Re rho_q=1/2`; the analogous Hodge statement is the existing purity
gate.  Thus composite covariance contains no zero-exclusion information.

## Proof

Coefficientwise conjugation gives

```text
(Theta C a)_q       = rho_q conjugate(a_q),
(C Theta_c a)_q     = conjugate((1-rho_q)a_q)
                    = (1-conjugate(rho_q)) conjugate(a_q),
```

whose difference is (DGIC.1).  The divisor Ward/fracture identity is (DGIC.2).  At the reflected
copy `Rq`, `kappa(Rq)=-kappa(q)`.  Applying `J` to (DGIC.1) therefore gives
`J delta_C=-delta_J C`, proving (DGIC.3).  Expanding the defect of `G=-JC` proves (DGIC.4).

## New frontier consequence

The missing source-to-divisor theorem is not existence or covariance of a completed Green map;
both already exist in the comparison model.  It is a **factor-retaining graph factorization**:

1. retain `C` and `J` as separately labelled anti-linear arrows;
2. place their defects in distinct source grades (head/tail, exterior incidence, or cofinal
   Hodge-graph degree), so (DGIC.3) cannot cancel after scalarization;
3. prove the source-selected Xi approximants land in the common closed graph domain;
4. keep a nonzero mixed cup/common-test incidence.

Under grade separation, unconditional total covariance forces each internal defect to vanish;
the Ward identity then puts every divisor point on the critical line.  This explains why the
Euler polarized chain, singular Hodge scale, adjacent-grade cofaces, and nondegenerate mixed trace
are structural requirements rather than alternative decorations.

## Universal factor-retention theorem

Let `r : X -> Y` and `j : Y -> Z` be composable arrows with generators `A_X,A_Y,A_Z`.  Write

```text
delta_r = A_Y r - r A_X,
delta_j = A_Z j - j A_Y.
```

The composite defect always satisfies

```text
delta_(jr) = delta_j r + j delta_r.                     (DGIC.5)
```

Assume `delta_(jr)=0`, `r` is surjective, `j` is injective, and there are disjoint submodules
`P,Q` of `Z` such that `delta_j(r x)` lies in `P` while `j(delta_r x)` lies in `Q` for every `x`.
Then both terms in (DGIC.5) vanish separately; surjectivity and injectivity give

```text
delta_j=0,   delta_r=0.                                 (DGIC.6)
```

This is the **factor-retention law**.  In the existing ungraded Deninger comparison carrier the
two terms occupy the same grade and are exact negatives, so (DGIC.6) cannot be inferred.  The
Euler head/tail source supplies the required disjoint source grades; the remaining theorem is that
the singular source-native graph transport preserves them through the Gamma/co-Poisson boundary.

The source grades are not hypothetical.  On the explicit Euler feature pair define

```text
H = {(f,0)},   T = {(0,g)}.
```

Then `H ∩ T = 0`; the pole-centered four-unit score belongs to `H`; the fracture augmentation
minus that score belongs to `T`; and the singular odd Hodge rotation exchanges `H` and `T` on its
open source domain.  Therefore only **grade preservation across global graph landing** remains,
not construction of the grading or its polarization.

## Hostile audit

- This does not prove graph landing or RH.
- It is stronger than another RH equivalence: it proves why an already-constructed unconditional
  transport is blind and identifies the exact information it cancels.
- A scalar, ungraded, or completed-only Green map cannot meet the factor-retention condition.
- Positivity after composing `J C` is too late; separation must occur before composition.
- `[NOVELTY UNVERIFIED]` External comparison is deferred by instruction.

## Status labels

- `[CORPUS]` Total Green covariance, Hodge fracture identity, polarized Euler head/tail source.
- `[FORMALIZED]` Riesz/Hodge defect formulas, reflected-fracture sign, internal cancellation,
  total Green covariance, the factor-retention criterion, and the Euler complementary-grade laws.
- `[OPEN CORE]` Source-native closed graph factorization retaining the two defect grades.

## Formal certificates

- `formal/GaloisForLFunctions/HTGeometry/FactorRetainingCovariantSolderLaw.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerGreenInternalDefectCancellationLaw.lean`
- `formal/GaloisForLFunctions/RHTower/EulerPrimitiveBoundaryDefectGrades.lean`

## Gates

- [x] 0 -> 1: exact statement, proof, corpus nonduplication search, hostile audit
- [x] 1 -> 2: direct formal certificate
- [x] 2 -> 3: axiom and lint audit
- [ ] 3 -> 4: derive a source-native graph consequence, not only comparison-model cancellation

## Log

- 2026-08-02 — identified unconditional Green covariance as exact cancellation of the two
  critical-displacement defects; replaced “find a transport” by factor-retaining graph descent.
- 2026-08-02 — direct `lake env lean` checks and targeted three-module `lake build` passed.
  Banned-declaration search was empty.  Axiom audit found only `propext`, `Classical.choice`, and
  `Quot.sound`.  No Lean process remained after audit.
