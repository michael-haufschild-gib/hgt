# Integral cofinal Tate Gamma base-change law

- **ID:** `ULF-ICTGBC-1`
- **Stage:** 3-formalized
- **Type:** unconditional global source/physical completion fusion law
- **Status:** dependency-closed paper proof; Lean-certified in
  `GaloisForLFunctions.RHTower.IntegralCofinalTateGammaBaseChange`

## Statement

Let `D_T` be the globally assembled integral cofinal Tate operator over `Z[T,T^-1]`. For real `a`,
apply the Gamma character `T -> exp(a)` coefficientwise to every finite-support reciprocal
orientation packet. Let `D_a` act at every stage by the curved suspension `C_a=R_a-R`.

Then the global square commutes:

`ev_a(D_T x)=D_a(ev_a x)`

for every integral cofinal packet `x`. Moreover

`D_a^2=-K(a) id`,

where `K(a)=2(cosh a-1)` is paired positive Gamma curvature.

## Proof

`ULF-IRRCF-1` proves entrywise evaluation of `C_T` is `C_a`. Ring-hom evaluation commutes with the
two-term matrix-vector sums. Applying this at every finite-support stage gives the global
intertwining square. The physical square law follows stagewise from `C_a^2=-K(a)I`.

## Meaning

Source object, cofinal completion object, and physical Gamma realization are now one literal
base-change system. Remaining RH issue is not construction or coefficient recovery. It is whether
actual Xi associated-grade completion preserves the canonical integral top-coordinate module of
this already-intertwined system.

## Boundary

No Xi comparison, integral physical landing, compactness, or RH conclusion is asserted.
Coefficientwise evaluation is not claimed injective and does not turn arbitrary complex values
into integers.

## Dependency audit

- `ULF-ICTRRA-1` global integral assembly.
- `ULF-IRRCF-1` entrywise Gamma evaluation.
- Finite-support coefficientwise maps and two-by-two matrix multiplication.
- No Xi zero, RH premise, positivity assumption, numerical computation, added axiom, or lattice
  landing premise.
