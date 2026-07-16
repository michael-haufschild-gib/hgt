# The sheared seam is split-equivalent; cutoff alignment is the missing datum

- **ID:** sheared-seam-gauge-trivialization
- **Stage:** 3-formalized
- **Type:** THEOREM / INTERFACE CORRECTION / ROUTE NO-GO, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parents:** `../../3-formalized/new/sheared-seam-coordinate-criterion.md`,
  `weld-krein-rate-blindness.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/ShearedSeamGaugeTrivialization.lean`
- **Statement:** `[PROVED]` The sheared torsion matrix `[[X^m,1],[0,1]]` is unimodularly
  row-equivalent to the split matrix `diag(X^m,1)`.  The Fitting boundary is unchanged when the
  defect is transported by the inverse row gauge.  Under that transport the standard lower
  cutoff-crossing acquires a nonzero diagonal entry and is no longer a standard cutoff-crossing.
  Thus the sheared chart is not a non-split module extension; its extra content is the relative
  alignment between the presentation and a cutoff/defect.  Functional-equation coefficient parity
  canonically supplies that cutoff flag, and no row gauge preserving the FE flag can split the
  sheared presentation.  However, after the required semilinear action `X -> -X` is included, the
  sheared presentation either fails FE equivariance (if source and target parity are held fixed) or
  is explicitly equivalent to the split presentation (if target parity is transported).  The
  current shear therefore supplies no simultaneous-gauge-invariant completed obstruction.

## 1. Explicit gauge trivialization

Write

`A_0 = [[X^m,0],[0,1]]`,

`A_s = [[X^m,1],[0,1]]`,

`U = [[1,1],[0,1]]`, and `U^(-1)=[[1,-1],[0,1]]`.

Direct multiplication gives

`U U^(-1)=U^(-1) U=I`,                                            (1)

`A_s=U A_0`, and `A_0=U^(-1) A_s`.                               (2)

Therefore `A_s` and `A_0` present isomorphic cokernel modules.  In particular, the off-diagonal
unit in `A_s` does not define a nontrivial extension class of the torsion module.

## 2. Fitting transport law

For an arbitrary defect matrix `Delta`, the existing sheared-coordinate formula is

`tr(adj(A_s) Delta)=Delta_00-Delta_10+X^m Delta_11`.               (3)

Set `Delta_0=U^(-1) Delta`.  Its relevant entries are

`(Delta_0)_00=Delta_00-Delta_10`,

`(Delta_0)_11=Delta_11`.

Since `adj(A_0)=diag(1,X^m)`,

`tr(adj(A_0) Delta_0)=Delta_00-Delta_10+X^m Delta_11`.             (4)

Equations (3)-(4) prove

`Fitting_m(A_s,Delta)=Fitting_m(A_0,U^(-1)Delta)`                 (5)

both before and after reduction modulo `X^m`.

## 3. What changes under splitting

Let

`Delta_lower=[[0,0],[1,0]]`.

It is a standard lower cutoff-crossing for `e=diag(1,0)`.  But

`U^(-1) Delta_lower=[[-1,0],[1,0]]`.                              (6)

Every standard defect `(1-e) sigma e` has zero `(0,0)` entry, while the matrix in (6) has entry
`-1`.  Hence no `sigma` satisfies

`U^(-1) Delta_lower=(1-e) sigma e`.                               (7)

The nonzero Fitting boundary survives the gauge by (5); what fails is the claim that the transported
defect remains a crossing for the unchanged standard cutoff.

## 4. Attack on the prior interpretation

The earlier split-versus-sheared comparison changed `A_0` to `A_s` while holding
`Delta_lower` and `e` fixed.  It therefore compared two differently aligned pairs, not two
inequivalent torsion modules.  Calling `A_s` “non-split” hid the actual datum.

This matters for the completed-obstruction program.  The sheared presentation alone cannot supply
the non-factorwise extension data required by `weld-krein-rate-blindness.md`; it is gauge-trivial.
The only potentially surviving information is the relative position of:

1. the divisor presentation,
2. the cutoff flag/idempotent, and
3. the arithmetic defect action.

If that flag is obtained by building an Euler-Maclaurin, Sonin, or spectral carrier through a
cutoff parameter, the construction is a flow in disguise and does not answer the pinned constraint
question.

## 5. FE parity supplies the static flag

On the affine coefficient plane `(D,I)`, functional-equation reflection is the involution

`R_FE=diag(-1,1)`.                                                (8)

Its odd projector is

`e_FE=(I-R_FE)/2=diag(1,0)`,                                      (9)

exactly the `standardCutoff` used by the lower-crossing algebra.  Thus this flag need not be built
by a carrier: it is fixed by FE parity.

Say a row gauge `V` preserves coefficient parity when `V R_FE=R_FE V`.  Comparing upper-right
entries shows every such `V` has `V_01=0`.  But any equality

`A_s=V A_0`                                                       (10)

would force `V_01=1`, because the upper-right entry of `A_s` is `1` and that of `A_0` is supported
only on the second diagonal entry.  Contradiction.  Therefore

> no FE-coefficient-parity-preserving row gauge splits `A_s`.     (11)

At coefficient level, the shear is trivial in the ordinary polynomial-module category but cannot
be split by an automorphism of one fixed FE-flagged target.  This is a valid relative statement, but
it is not yet an invariant statement about an FE-semilinear presentation.

## 6. Full local FE audit: the provisional survivor collapses

For paired points `rho` and `1-rho`, the local coordinates obey

`((1-s)-(1-rho))=-(s-rho)`.                                      (12)

Hence FE acts on the polynomial germ by `X -> -X`.  For a presentation matrix `A(X)`, source parity
`R_s`, and target parity `R_t`, the correct intertwining equation is

`R_t A(-X)=A(X) R_s`.                                            (13)

Both `R_t` and `R_s`, combined with `X -> -X`, must square to the identity.

The split presentation satisfies (13) with target parity `R_FE` and the forced order-dependent
source parity

`R_s(m)=diag(-(-1)^m,1)`.                                        (14)

The factor `(-1)^m` is not optional: it is the FE sign of `X^m`.

Now test the sheared presentation.  If one uses `R_FE` on both source and target, its upper-right
entry makes (13) read `-1=1`; the presentation is not an FE-semilinear object.  Thus the
coefficient-level no-splitting theorem cannot be promoted by simply freezing the same parity on
both sides.

Alternatively transport target parity through the splitting gauge:

`R_t^shear=U R_FE U^(-1)`.                                       (15)

This is again a semilinear involution, and `U` intertwines `R_FE` with `R_t^shear`.  With (14)-(15),
the sheared presentation satisfies (13).  But now the same `U` is an explicit FE-semilinear
isomorphism from the split presentation to the sheared one.  The relative class vanishes under
simultaneous transport.

Therefore the current sheared presentation gives a strict dichotomy:

1. keep the canonical target parity fixed: the shear is not an FE object;
2. transport target parity with the shear: the object is FE-equivariant but split-equivalent.

There is no third, gauge-invariant obstruction in the present matrix.

## Corrected open core

The current Fitting shear is exhausted as a completed-obstruction candidate.  A replacement would
have to satisfy a stronger specification from the outset.  The upper-unit-shear family is now fully
exhausted in `fe-semilinear-upper-shear-exhaustion.md`: FE compatibility makes its splitting gauge
FE-compatible too.  The first algebraic survivor is the two-torsion extension constructed in
`fe-semilinear-two-torsion-extension.md`.

> `[OPEN CORE]` Attach the genuine two-torsion FE extension functorially to the completed
> FE-plus-Schwarz divisor germ and test its joint-involution descent on and off the critical-line
> fixed locus, without defining its residue from `analyticOrderAt xi` or a carrier-built cutoff.

The moduli problem is one of genuine equivariant extension classes, not coordinate relative
position inside a presentation whose FE action is allowed to move with the gauge.

## Novelty and significance gates

- **NOVEL:** The repository had formulas showing that the sheared chart detects a lower crossing
  while the split chart does not.  It had not tested whether the two presentations were genuinely
  inequivalent or transported the defect through the splitting gauge.  The exact transport theorem
  identifies the omitted datum.  The FE projector theorem then derives the flag intrinsically and
  proves coefficient-level relative non-splitting.  The semilinear audit is the decisive additional
  step: it proves that the proposed survivor is either not an FE object or is equivariantly split.
- **SIGNIFICANT:** This prevents a coordinate shear from being mistaken for completed arithmetic
  extension data and closes the current Fitting-shear route.  It replaces an ill-posed relative
  chart calculation with the exact requirement of a nontrivial FE-semilinear extension class.
- **FLOW TEST:** The proof concerns fixed polynomial matrices and a fixed gauge.  No cutoff limit,
  carrier construction, or evolution parameter is used.

## Gates

- [x] 0 -> 1: explicit gauge and the omitted transport question identified.
- [x] 1 -> 2: gauge inverse, presentation splitting, Fitting transport, crossing failure, canonical
  FE projector, coefficient-relative non-splitting, local-coordinate reflection, semilinear
  equivariance failure, and transported splitting proved.
- [x] 2 -> 3: theorem family formalized in Lean with targeted module and axiom checks.
- [ ] 3 -> 4: a genuinely non-split FE-semilinear divisor presentation, then a non-tautological map
  from its extension class to FE-Witt activation.
