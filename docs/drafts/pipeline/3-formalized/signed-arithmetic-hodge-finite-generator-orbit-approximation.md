# Finite generator families approximate the actual cell source

For every natural cutoff A>=1, retain the root generator and each Haar
generator a<A, together with every dyadic level j>=0 of each retained
generator. This generator-label set is finite. The actual cell-space cutoff
P_A preserves each retained orbit vector exactly and kills each omitted one.

Let U be the whole-line cell embedding. Every compact real bounded-variation
source f satisfies

norm(U U* f - U P_A U* f)^2 <=32 Gamma(f)/(1+log A).

For every finite original wholeCellProfile(c,X), the source lies exactly in
the range of U, so this controls the entire original source:

norm(f - U P_A U* f)^2 <=32 Gamma(f)/(1+log A).

Both estimates use Gamma of the original source. No decrease of Gamma under
projection is assumed. The proof identifies actual source coordinates with
normalized Haar readouts, removes the retained root coordinates exactly,
and applies the all-level tail estimate through the coordinate isometry.
Finite cell realization follows from the physical images of weighted cell
basis vectors and the exact adjoint identity U*U=1.

The approximation space retains infinitely many level directions. This is
an L2 estimate; full-Weil mixed terms, poles and generator-orbit signs remain
separate research obligations.

Lean: `SignedArithmeticHodgeTheory/FiniteGeneratorOrbitsApproximateThePhysicalCellSource.lean`.
Capstones: `finite_retainedLogCellGenerators`,
`logCellGeneratorHead_orbit`, `logCellGeneratorHead_root`,
`logCellGeneratorHead_low_detail`,
`norm_physical_cell_component_sub_head_sq_le`,
`realSourceLp_wholeCellProfile`,
`norm_wholeCellSource_sub_generatorHead_sq_le`.
Final individual no-olean audit passes. Printed capstone dependencies contain
only `propext`, `Classical.choice`, `Quot.sound`.
