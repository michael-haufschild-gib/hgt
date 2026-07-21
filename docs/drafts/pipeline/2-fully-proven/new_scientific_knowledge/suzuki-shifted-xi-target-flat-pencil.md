# Suzuki shifted Xi target flat pencil and multiplicity fingerprint

- **ID:** `suzuki-shifted-xi-target-flat-pencil`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Lane:** Suzuki continuous-kernel limit; finite-shift target identification
- **Parents:** `suzuki-finite-shift-flat-projective-resolvent-holonomy`,
  `suzuki-residual-overcrowding-entire-pair-closure`
- **Source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  [arXiv:2606.09096](https://arxiv.org/abs/2606.09096), Section 8
- **RH used:** no
- **Computation used:** no

## Frontier problem

Suzuki derives the displayed boundary-free target only after setting the form shift to
`lambda=0` under RH.  The project therefore treated convergence of an admissible finite-aperture
shift to that distinguished value as part of the cofinal wall.  Section 8 contains more structure:

```text
S_a = G_a - lambda (-Delta_N)^(-1),
hat(g)(z) = z^(-2) xi'(1/2-iz)/xi(1/2-iz).             (1)
```

After removal of the finite-interval Neumann boundary terms, the inverse-Laplacian symbol is
`z^(-2)`.  Hence the boundary-free shifted inverse multiplier is, up to one nonzero constant,

```text
R_eta(z) = z^2 XiC(z)/(XiC'(z)-eta XiC(z)),             (2)
eta = -i lambda.                                        (3)
```

Formula `(2)` is not asserted as an exact finite-`a` identity: the finite Neumann inverse is not a
whole-line convolution operator.  The theorem below identifies the exact pencil forced after that
remaining boundary passage and proves that its RH-bearing divisor is independent of the limiting
finite shift.

## Setup

Put

```text
D_eta(z) = XiC'(z)-eta XiC(z),
N(z)     = z^2 XiC(z),
R_eta(z) = N(z)/D_eta(z).                               (4)
```

All quotients are meromorphic.  At a common numerator/denominator zero, `R_eta` means its canonical
removable continuation.

## Theorem A: affine secant recovery `[PROVED HERE]`

For every `alpha,beta,z in C`,

```text
D_alpha(z)-D_beta(z)=(beta-alpha)XiC(z).                (5)
```

Consequently, whenever `alpha != beta`,

```text
XiC(z)=(D_alpha(z)-D_beta(z))/(beta-alpha).              (6)
```

Thus two distinct normalized shift fibres recover Xi itself by an affine secant.  No limiting
derivative and no choice of the zero-shift fibre are required.

### Proof

Expand both definitions.  The `XiC'` terms cancel and the remaining coefficient is
`-alpha+beta`.  Division by `beta-alpha` proves `(6)`.

## Theorem B: exact flat shift transport `[PROVED HERE]`

Where the displayed denominators are nonzero, define

```text
T_(alpha,beta)(z)=D_alpha(z)/D_beta(z).                  (7)
```

Then

```text
T_(alpha,beta) R_alpha = R_beta,
T_(alpha,beta) T_(beta,gamma)=T_(alpha,gamma).           (8)
```

Equivalently, the targets obey the division-free Mobius law

```text
[z^2-(beta-alpha)R_alpha(z)]R_beta(z)=z^2R_alpha(z),     (9)
```

and, away from `z=0` and the Xi divisor, the reciprocal translation law

```text
z^2/R_beta(z)-z^2/R_alpha(z)=alpha-beta.                (10)
```

### Proof

The first identity in `(8)` cancels `D_alpha`; the second cancels `D_beta`.  Substitution of
`D_beta=D_alpha-(beta-alpha)XiC` gives `(9)`.  Finally

```text
z^2/R_eta = D_eta/XiC = XiC'/XiC-eta,                   (11)
```

and subtraction gives `(10)`.  These are exact rational identities, not perturbation formulas.

## Theorem C: every Xi multiplicity becomes one `[PROVED HERE]`

Let `z_0` be any Xi zero and let

```text
m=ord_(z_0)(XiC)>=1.                                    (12)
```

Since `XiC(0) != 0`, every such `z_0` is nonzero.  For every shift `eta`,

```text
ord_(z_0)(D_eta)=m-1,
ord_(z_0)(R_eta)=1.                                     (13)
```

In particular:

1. the complete Xi zero set survives every finite shifted target;
2. every surviving target zero is simple even if the Xi zero is multiple;
3. shift choice changes companion poles and normalization, not the Xi divisor.

### Proof

Write the local analytic factorization

```text
XiC(z)=(z-z_0)^m g(z),   g(z_0)!=0.                     (14)
```

Differentiation gives

```text
D_eta(z)=(z-z_0)^(m-1)
  [m g(z)+(z-z_0)(g'(z)-eta g(z))].                     (15)
```

The bracket has value `m g(z_0)!=0`, proving the first equality in `(13)`.  The numerator
`z^2 XiC(z)` has order `m` because `z_0!=0`; subtracting orders proves the second.

## Theorem D: exact inverse-multiplicity fingerprint `[PROVED HERE]`

The removable target germ has expansion

```text
R_eta(z)=(z-z_0)[z_0^2/m+O(z-z_0)].                    (16)
```

Equivalently its meromorphic trailing coefficient at `z_0` is

```text
TC_(z_0)(R_eta)=z_0^2/m,                                (17)
```

independent of `eta`.  For a simple Xi zero this is the exact first jet

```text
R_eta'(z_0)=z_0^2.                                      (18)
```

### Proof

Divide the numerator factorization

```text
z^2 XiC(z)=(z-z_0)^m z^2g(z)                            (19)
```

by `(15)`.  One factor `z-z_0` remains.  Evaluation of the analytic nonzero quotient at `z_0`
gives `z_0^2 g(z_0)/(m g(z_0))=z_0^2/m`.  This proves `(16)`--`(18)`.

This is the exact compatibility law missing from a naive simple-spectrum reading of Suzuki:
self-adjoint extension spectra may remain simple without assuming simplicity of Xi zeros, while
the lost Xi multiplicity remains recoverable from the target's first coefficient.

## Theorem E: shift parameter is a Riccati flow `[PROVED HERE]`

At fixed `z`, wherever `D_eta(z)!=0`,

```text
d R_eta(z)/d eta = z^2 XiC(z)^2/D_eta(z)^2.             (20)
```

For `z!=0`, this is

```text
d R_eta(z)/d eta = R_eta(z)^2/z^2.                     (21)
```

### Proof

Differentiate `N/(XiC'-eta XiC)` in `eta`; the denominator derivative is `-XiC`.  Formula `(20)`
follows by the quotient rule, and `(21)` is the definition of `R_eta` squared.

## What this changes at the RH frontier

The old cofinal target demand was too strong:

```text
choose lambda_a -> 0, then identify R_0.                (22)
```

The exact replacement is

```text
choose an intrinsic non-erasing schedule with a finite shift cluster,
control the finite-aperture Neumann boundary term in a common gauge,
identify any cluster target R_eta.                      (23)
```

Every finite `eta` in `(23)` carries the same Xi zero set and the same multiplicity fingerprint.
The schedule need not converge to zero, need not have a unique finite cluster point for divisor
recovery, and need not preserve Xi multiplicities as zero multiplicities.  The finite-shift
projective holonomy already formalized in the parent module now has the exact infinite target
`(8)`--`(10)`.

There is also a second attack unavailable in the one-fibre formulation: prove common-gauge
normality for two distinct finite shift fibres and recover Xi directly by the secant `(6)`.  This
turns target identification into an affine two-fibre problem instead of a distinguished-shift
problem.

## Remaining open core

This theorem does **not** prove RH.  It removes shift normalization and multiplicity compatibility
from the open core.  What remains is:

1. construct an intrinsic cofinal schedule that avoids both classified erasing boundaries and has
   a finite shift cluster (or two normalized finite fibres);
2. prove common-gauge entire-pair normality and zero linear Nevanlinna mass;
3. control the finite-interval Neumann boundary term strongly enough to identify the limiting
   pair with `(N,D_eta)` for one finite `eta`, or with two denominators in `(6)`.

These are source/operator convergence statements.  No estimate, zero simplicity assumption, RH
assumption, or numerical evidence has been inserted.

## Hostile audit

1. **Finite aperture versus whole line.** Equation `(2)` is the boundary-free target forced by
   the symbols in Suzuki Section 8.  It is not claimed for finite `a`; Neumann boundary control is
   explicitly retained as open core 3.
2. **Coordinate factor.** Suzuki uses `xi(1/2-iz)`.  Since centered Xi is even,
   `xi'(1/2-iz)-lambda xi(1/2-iz)=i D_(-i lambda)(z)`.  Suzuki's literal target is therefore
   `-i R_(-i lambda)`, a fixed nonzero scalar multiple.  Divisor statements are unchanged; the
   literal trailing coefficient is multiplied by `-i`.
3. **No hidden simple-zero premise.** Theorems C--D start with arbitrary multiplicity `m>=1`.
4. **No malformed entire convergence.** `R_eta` is meromorphic.  The intended convergence object
   remains the common-gauge pair `(N,D_eta)`, not ordinary entire convergence to a meromorphic
   quotient.
5. **Unbounded shifts still erase data.** The theorem concerns finite shift clusters.  It does not
   contradict the proved far-negative collapse.
6. **Generic versus source-specific novelty.** Local factorization and Riccati algebra are
   classical.  Candidate novelty is their exact synthesis with Suzuki's continuous-kernel shift:
   removal of the zero-shift convergence requirement, the two-fibre Xi secant, and the
   shift-independent multiplicity fingerprint.  Specialist priority review remains required.

## Literature and priority audit

Targeted searches covered Suzuki's paper, its characteristic-function references, and exact
queries for `xi'-lambda xi`, `f'-a f`, and Laguerre--Polya derivative pencils.  Classical sources
study location/interlacing of derivative-combination zeros; no located source states the
Suzuki-specific flat target, affine two-shift recovery, or the resulting frontier reduction.
Repository search found only the unshifted quotient `z^2 XiC/XiC'` and the separate Hedenmalm
order-drop theorem.  The present theorem connects and strengthens those ingredients rather than
duplicating them.

## Lean target

Formalize exactly:

```text
suzukiShiftedXiDenominator_sub
XiC_eq_suzukiShiftedXiDenominator_secant
suzukiXiShiftTransport_target
suzukiXiShiftTransport_cocycle
suzukiShiftedXiTarget_mobius_cross
suzukiShiftedXiTarget_reciprocal_translation
analyticOrderAt_suzukiShiftedXiDenominator_eq_pred_of_XiC_zero
meromorphicOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero
meromorphicTrailingCoeffAt_suzukiShiftedXiTarget_of_XiC_zero
hasDerivAt_suzukiShiftedXiTarget_parameter_riccati
hasDerivAt_suzukiShiftedXiTarget_of_simple_XiC_zero
```

## Gates

- [x] source formula and coordinate conversion audited
- [x] competing zero-shift and finite-shift conjectures attacked
- [x] exact paper proof for affine/flat flow
- [x] arbitrary-multiplicity local proof
- [x] hostile audit closed
- [x] exact Lean module and axiom audit
- [ ] finite-aperture Neumann boundary convergence
- [ ] common-gauge pair normality and zero linear mass
- [ ] RH

## Log

- 2026-07-21 — discovered shifted reciprocal-logarithmic pencil in Suzuki Section 8; rejected an
  overclaim of exact finite-aperture Fourier diagonalization because the Neumann inverse has
  boundary terms.
- 2026-07-21 — proved affine secant recovery, flat Mobius transport, arbitrary-multiplicity collapse,
  inverse-multiplicity fingerprint, and Riccati parameter flow; promoted through Stage 1 to Stage 2.
- 2026-07-21 — formalized the complete theorem, including arbitrary-multiplicity trailing
  coefficient, in `SuzukiShiftedXiTargetFlatPencil.lean`; exact build and axiom audit passed.
