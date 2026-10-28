# Explicit balanced basis of the arithmetic wandering space

## Statement

Let ell_a=log((a+1)/a), alpha_a=sqrt(ell_(2a)/ell_a), and
beta_a=sqrt(ell_(2a+1)/ell_a). For actual W=logCellShift 2,

W e_a=alpha_a e_(2a)+beta_a e_(2a+1),
d_a=beta_a e_(2a)-alpha_a e_(2a+1),
alpha_a^2+beta_a^2=1.

The first cell e_1 and all d_a form a Hilbert basis of K=(range W)^perp.
The basis construction retains these literal vectors.

## Proof

The established block-mass identity supplies the unit weight identity.
The exact block operator formula gives W e_a and each coordinate of W f.
The two products cancel in inner(d_a,W f), while W f has zero first coordinate.
Disjoint cell pairs and the unit identity prove orthonormality.

If x lies in K and all generator readouts vanish, its first coordinate vanishes.
Testing against W e_a and d_a gives the equations

alpha_a*x_(2a)+beta_a*x_(2a+1)=0,
beta_a*x_(2a)-alpha_a*x_(2a+1)=0.

The unit weight identity inverts this system. Every coordinate vanishes.
The orthogonal-complement criterion constructs the Hilbert basis on the
completed wandering submodule; completeness of that submodule follows from
closedness of the actual orthogonal complement.

## Lean

Module:
formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/BalancedCellDetailsFormTheWanderingBasis.lean

Capstones:

- logCellDyadic_single
- logCellDyadicDetail_mem
- inner_logCellDyadicDetail_detail
- eq_zero_of_logCellDyadic_coordinates
- logCellDyadicGenerator_total
- logCellDyadicWanderingBasis

Final individual no-olean audit passes. All capstones depend only on propext,
Classical.choice and Quot.sound. The module is wired into its umbrella.

## Scope

The basis identifies the actual weighted cell-clock wandering space. It supplies
explicit Hilbert coordinates, without an unidentified orthogonal remainder.
Finite-source expansion, comparison with the existing physical balanced-Haar
normalization, one-reserve Gamma control and selective Weil sign require their
own exact theorems.
