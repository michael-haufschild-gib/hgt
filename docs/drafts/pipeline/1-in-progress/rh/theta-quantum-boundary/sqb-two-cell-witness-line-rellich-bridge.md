# SQB two-cell witness-line Rellich bridge

## New mechanism

Let `F` be a finite-deck `C¹` equivariant field, with hyperbolic form energy

\[
E(F)=\int_{\mathcal D}\bigl(\|\operatorname{hypGradX}F\|^2+
\|\operatorname{hypGradY}F\|^2\bigr)\,d\mu.
\]

The bounded-core Rellich step reduces to two concrete, local assertions:

1. The height-squared two-component derivative density is invariant under
   integral Möbius action.
2. A `C¹` finite-deck field on a Euclidean rectangle of mesh at most `h` is
   within `C h² E` in squared `L²` distance of some rectanglewise constant
   finite-dimensional field.

The first assertion transports the derivative energy from the modular cell to
the complete strip

\[
\Sigma=\{z:|\Re z|\leq \tfrac12,\;3\leq4(\Im z)^2\}.
\]

`SelbergModularStripComparison` proves exactly that `Σ` is contained in the
union of the modular cell and one inversion preimage, and that inversion
preserves hyperbolic volume. Consequently, invariance gives the sharp uniform
two-cell bound

\[
 \int_\Sigma e_F\,d\mu\leq2\int_{\mathcal D}e_F\,d\mu.
\]

This covers every bounded fundamental-domain core by a fixed Euclidean
rectangle without a boundary-extension theorem.

For (A=\begin{psmallmatrix}a&b\\c&d\end{psmallmatrix}), it is enough to
formalize the pointwise chain-rule identity

\[
D F_{A z}\!\left((cz+d)^{-2}v\right)=U_A D F_z(v),
\]

where (U_A) is the finite regular deck unitary. Writing
`(cz+d)⁻² = r + i s`, the two directions become
`r·u₀+s·u₁` and `−s·u₀+r·u₁`. This has a coordinate-free proof in every real
inner-product space:

\[
\|r u_0+s u_1\|^2+\|-s u_0+r u_1\|^2
=(r^2+s^2)(\|u_0\|^2+\|u_1\|^2).
\]

The two cross terms cancel after two applications of the parallelogram
expansion. Thus the finite deck need not be decomposed coordinatewise. The
unitary removes `U_A`, and `Im(Az)=Im(z)/|cz+d|²` proves assertion 1 exactly.

## Witness-line tensorization

For one complex coordinate `f` on a cell `I × J`, let `m_y` be the horizontal
cell mean of `f(·,y)`. The existing cell-mean inequality bounds both terms in
the pairwise estimate

\[
 |f(x,y)-f(x_0,y)|^2\leq
 2|f(x,y)-m_y|^2+2|f(x_0,y)-m_y|^2.
\]

After integrating in `x,x₀,y`, it bounds the average horizontal witness error
by a constant times `|I|²` times horizontal energy. For each `x₀`, let
`c(x₀)` be the vertical cell mean of `f(x₀,·)` and apply the same theorem in
`y`. Averaging over `x₀` produces one witness with

\[
 \int_{I\times J}|f-c(x_0)|^2
 \leq C\max(|I|,|J|)^2
 \int_{I\times J}(|\partial_x f|^2+|\partial_y f|^2).
\]

Thus no differentiation under a cell-average map and no uncontrolled point
trace are required. The pairwise comparison itself is coordinate-free in the
finite deck Hilbert space; only the available one-dimensional cell-mean input
remains scalar. On the strip,
`hypGradX = y ∂x` and `hypGradY = y ∂y`, while `dμ = dx dy / y²`; therefore the
right side is exactly Euclidean Dirichlet energy.

## Consequence for SQB

For a form-norm bounded family, choose the cusp height first using the completed
cuspidal tail estimate, then choose the grid mesh. The two-cell energy bound and
witness-line approximation make the core image totally bounded; tail plus core
then makes the full cuspidal form embedding compact. This feeds the existing
Friedrichs compact-resolvent theorem.

## Formal status

The strip-cover theorem and the scalar complex one-dimensional cell-mean
Poincaré theorem already exist in source. The finite-deck local energy bridge
is now formalized and target-built in
`GaloisForLFunctions.RHTower.MaassFiniteDeckRellichCore`:

- `chartDeriv_modular` proves the full reciprocal-square derivative covariance
  for every `formPreDomain` vector;
- `rotation_scale_normSq` proves the coordinate-free two-direction rotation law;
- `chartGradientNormSq_modular` proves the exact pre-energy transport law;
- `hyperbolicChartGradientDensity_modular` combines it with
  `ModularGroup.im_smul_eq_div_normSq` to prove invariant height-squared
  finite-deck gradient density.
- `hyperbolicChartGradientDensity_eq_hypGradNormSq` identifies that density
  with the sum of the squared `hypGradX` and `hypGradY` norms;
- `hyperbolicChartGradientDensity_integrable_fd` obtains fundamental-domain
  integrability from the existing `MemLp` gradient fields;
- `hyperbolicChartGradientDensity_strip_le_twice` proves the complete
  two-cell strip estimate.

`GaloisForLFunctions.HTGeometry.WitnessLinePoincare` is also formalized and
target-built. It supplies:

- `normSq_sub_le_two_center`, the coordinate-free pairwise bound used to
  compare two horizontal witnesses through one cell mean;
- `continuous_horizontalCellAverage`, continuity of a horizontal cell mean in
  the transverse coordinate;
- `horizontal_cell_mean_iterated_le`, the two-dimensional iterated estimate
  bounding horizontal mean error on a rectangle by horizontal Dirichlet
  energy.
- `exists_mem_Ioc_le_of_integral_le`, which turns a normalized interval
  integral budget into an actual witness coordinate;
- `horizontal_witness_average_iterated_le` and
  `vertical_cell_mean_iterated_le`, the respective averaged horizontal and
  vertical Dirichlet bounds;
- `rectangle_error_to_vertical_witness_le`, the fixed-line reduction;
- `exists_rectangle_witness_line`, the assembled scalar rectangle theorem:

  \[
  \exists x_0\in I,\qquad
  \int_{I\times J}|F-c(x_0)|^2
  \leq8|I|^2\int_{I\times J}|\partial_xF|^2+
       2|J|^2\int_{I\times J}|\partial_yF|^2,
  \]

  where \(c(x_0)\) is the vertical mean of \(F(x_0,\cdot)\). Its proof
  closes the Fubini order explicitly through integrability on the finite
  product cell, so it does not conceal a trace or differentiation argument.
- `exists_common_witness_of_finite_budget`, which selects one coordinate for a
  whole finite family after summing its horizontal and vertical budgets;
- `horizontal_witness_integral_le`, which puts the horizontal two-witness
  estimate in the selector's `x₀,y,x` integration order;
- `exists_rectangle_witness_line_finset`, the finite-deck version. For any
  finite index type it returns one common `x₀` and the vector of vertical
  component means, with squared error bounded by

  \[
  8|I|^2\sum_i E_{x,i}+2|J|^2\sum_i E_{y,i}.
  \]

  This is a simultaneous finite-family statement, not independent
  coordinatewise witness choices.

`IntervalPoincare` and `CellAveragePoincare` now also expose local variants
whose differentiability and derivative-continuity hypotheses are restricted to
the closed cell:

- `integral_sub_left_sq_le_of_hasDerivAt_on_Icc`;
- `integral_normSq_sub_left_le_of_hasDerivAt_on_Icc`;
- `integral_normSq_sub_average_le_of_hasDerivAt_on_Icc`.

They preserve the prior constants. This is required because an actual Maass
chart is regular only on the positive-imaginary open set; extending it below
the real axis would not be a source-faithful step.

The active Lean leaf is the local rectangle lift and its actual deck
instantiation: rebuild the witness-line argument with cell-local regularity,
then identify each coordinate derivative of `DeckSpace N` with the actual
`chartDeriv` component on a positive-height rectangle. Finite-grid assembly
and bounded-core total boundedness follow only after that lift. No compact
embedding or compactness theorem is claimed here.
