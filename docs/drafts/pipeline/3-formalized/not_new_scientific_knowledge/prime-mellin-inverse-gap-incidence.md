# Prime--Mellin source incidence for inverse-gap observability

- **ID:** `prime-mellin-inverse-gap-incidence`
- **Stage:** 3-formalized
- **Type:** EXACT VALUE RELATION / OBSERVABILITY DIRICHLET FORM / BRIDGE
- **Scientific status:** `[PROVED IN LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-BLIND SIGN]`
- **Lean:** `GaloisForLFunctions.HTGeometry.InverseGapCauchyCommutator` and
  `GaloisForLFunctions.RHTower.PrimeMellinInverseGapEnergy`

## Statement

For boundary nodes `w_i=epsilon+i x_i`, a value packet `v_i`, and the universal Cauchy Gram

\[
 C_{ij}=\frac1{w_i+\overline{w_j}},
\]

the commutator with `diag(v)` has entries

\[
 [C,\operatorname{diag}v]_{ij}
   =\frac{v_j-v_i}{2\epsilon+i(x_i-x_j)}.
\]

Hence its finite Hilbert--Schmidt entry energy is exactly

\[
 \sum_{i,j}\frac{|v_j-v_i|^2}{(2\epsilon)^2+(x_i-x_j)^2}.       \tag{1}
\]

At every positive regularization scale the live CCM colligation gives the source identity

\[
 C=G_{\rm prime}-G_{\rm shifted\ polar}+G_{\rm Mellin\ defect}.
\]

Commuting with `diag(v)` and taking the squared entry energy proves that `(1)` is the norm square
of one signed prime--polar--Mellin incidence packet.  The cross terms remain inside the norm; the
identity does not split into three unrelated positive energies.

## Static observability meaning

At `epsilon=0` and for pairwise distinct real nodes, `(1)` is the complete-graph Dirichlet form

\[
 \mathcal E_x(v)=\sum_{i,j}\frac{|v_j-v_i|^2}{(x_i-x_j)^2}.
\]

It is nonnegative and vanishes exactly on constant value packets.  Thus it measures whether the
chosen node packet distinguishes a chosen observable.  It is an observability seminorm, not a
temporal Hamiltonian and not by itself a clock: both the nodes and the readings are external
inputs.

## What the mquantum residue supplied

The zero-log-gas Hessian suggested the inverse-square Dirichlet-form shape.  Mquantum constructs
that generic positive graph Laplacian only after importing a tabulated zero set.  The RHTower
advance is the exact prime--polar--Mellin source incidence before any zero packet is chosen.

## Exhaustion and no-go

1. Positivity is unconditional for every real injective node packet, so its sign cannot
   distinguish Xi zeros from an unrelated real spectrum and cannot imply RH.
2. Specializing `x_i` to zero ordinates imports the divisor; it does not derive the nodes from the
   prime source.
3. The source identity is exact but supplies no lower bound, coercivity estimate, or orientation
   for its signed prime--polar--defect packet.
4. Determinants, discriminants, simple-zero criteria, pair correlation, and quantum-metric
   reinterpretations only repackage `(1)` unless they add a source-derived estimate.  None in the
   current corpus does.
5. The zero-regularization limit is therefore a useful consumer only after another theorem
   supplies a source-selected node packet and a nonconstant observable with quantitative control.

The residue is fully applied as a bridge and exhausted as an RH route.  Its only live successor is
an independently justified source-side coercivity or orientation theorem; mquantum supplies
neither.

## Lean surface

- `gramValueCommutator_eq_matrixCommutator`
- `norm_sq_gramValueCommutator_cauchyBoundary_apply`
- `orderedInverseGapEnergy_nonneg`
- `orderedInverseGapEnergy_eq_zero_iff_of_injective`
- `cauchyBoundaryValueCommutator_eq_prime_sub_shiftedPolar_add_mellinDefect`
- `regularizedInverseGapCommutatorEnergy_eq_primePolarMellinIncidence`

The direct source files and the exact target
`lake build +GaloisForLFunctions.RHTower.PrimeMellinInverseGapEnergy` pass.  No full build or
numerical computation was run.

## Gates

- [x] zero-importing generic physics object separated from the source-pure identity
- [x] exact Cauchy-commutator realization proved
- [x] exact prime--polar--Mellin source incidence proved
- [x] positivity kernel characterized
- [x] RH-blindness and missing quantitative consumer isolated
- [x] novelty rejected as a generic commutator bridge plus corpus specialization
