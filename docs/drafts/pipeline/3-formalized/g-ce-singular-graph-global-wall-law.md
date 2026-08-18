# G-CE singular-graph global wall law

- **Stage:** formalized in Lean 4
- **Routes:** G-exterior, G-CE
- **Date:** 2026-08-18
- **Frontier object:** clock-normalized coupled floor--Möbius/Gamma complement defect
- **Status:** dependency-closed finite-packet theorem; Lean formalization complete

## Corpus-first frontier audit

The corpus already proves that the critical graph-normal source/complement defect converges to

\[
  m(u)d,\qquad m(u)=(1+u)^{-1},\qquad
  d=\mathcal W_{\Xi}^{\mathrm{anti}}(1/2),
\]

and that `d = 0` is equivalent to RH. It also proves the sharp obstruction: positivity of the
mass-perturbed Hardy--Fisher wall at bottom budget `b` on canonical two-node packets forces

\[
  b\ge 4+|d|^2.
\]

What was missing was the converse, hence an intrinsic graph norm and a global lower wall rather
than an RH-equivalent positivity demand at budget four.

## Frozen conjecture

Escaped mass is a missing graph leg, not a contraction defect. Adjoining the critical zero-node
Cauchy feature should pay exactly `|d|^2`, make every finite wall packet positive, and leave a
sharp lower bound `-|d|^2` after deleting that leg.

Falsifiers were:

1. a nonzero Fisher/zero-node cross term;
2. a coefficient conjugation incompatible with the actual coupled-error column;
3. failure of finite-packet positivity at budget `4 + |d|^2`;
4. a canonical saturation packet detecting a larger debt.

None occurs.

## Theorem

For inward nodes `u_i` let

\[
 K(u,v)=\frac1{1+v+\bar u},\quad
 s(u)=\frac{2u}{(1+u)^2},\quad
 m(u)=\frac1{1+u}.
\]

For `d in C` and real `b`, define the coupled wall matrix

\[
 G_{d,b}(u)=
 \begin{pmatrix}
   (K(u_i,u_j)) & (\overline{s(u_i)+d m(u_i)})\\
   (s(u_j)+d m(u_j)) & b
 \end{pmatrix}.
\]

Then:

1. `G_{d,4+|d|^2}(u)` is positive semidefinite for every finite inward packet.
2. `G_{d,b}(u)` is positive semidefinite for every finite inward packet iff
   `b >= 4 + |d|^2`.
3. At uncompleted budget four, for every coefficient packet `c`,

   \[
   \operatorname{Re}\langle c,G_{d,4}(u)c\rangle
   \ge -|d|^2|c_{\mathrm{div}}|^2.
   \]

4. The coefficient `|d|^2` is sharp: canonical two-node saturation packets with
   `c_div = -1` have quadratic forms converging to `-|d|^2`.

For the actual G-CE coefficient `d = W_Xi^anti(1/2)`, graph debt is zero iff RH.

## Proof

The unperturbed critical Hardy--Fisher matrix is already an unconditional Gram matrix. Write its
vectors as `k_u` and `F`, with

\[
 \langle k_u,k_v\rangle=K(u,v),\qquad
 \langle F,k_u\rangle=s(u),\qquad \|F\|^2=4.
\]

At the critical zero node,

\[
 \langle k_0,k_u\rangle=K(0,u)=m(u),\quad
 \langle F,k_0\rangle=s(0)=0,\quad \|k_0\|^2=K(0,0)=1.
\]

Because the complex inner product is conjugate-linear in its first coordinate, set

\[
  F_d=F+\bar d\,k_0.
\]

Then

\[
 \langle F_d,k_u\rangle=s(u)+d m(u),\qquad
 \|F_d\|^2=4+|d|^2.
\]

Thus `G_{d,4+|d|^2}` is the literal Gram matrix of `(k_{u_i},F_d)`, proving item 1.
For larger `b`, adjoin one orthogonal scalar leg of squared norm `b-(4+|d|^2)`. Conversely, the
already-proven canonical two-node saturation law forces `b >= 4+|d|^2`. This proves item 2.

Changing only the bottom diagonal from `4` to `4+|d|^2` adds
`|d|^2|c_div|^2` to every quadratic form. Positivity of the completed form gives item 3. The
existing exact two-node formula tends to `-|d|^2` with `c_div=-1`, proving item 4.

## Scientific consequence

G-CE now has an intrinsic singular graph norm. The contour seam does not destroy global
lower-semiboundedness; it contributes one exactly classified negative-light debt. Fixed-four
positivity asks for disappearance of that debt and is therefore RH-equivalent, while graph-completed
positivity is unconditional. Remaining RH-bearing problem is source-native boundary transport that
pays or cancels the `|d|^2` leg without assuming its vanishing.

## Literature audit

Suzuki's 2026 finite-interval Friedrichs realizations establish lower-bounded self-adjoint finite
models but leave the cofinal resolvent passage heuristic. Connes--Consani--Moscovici construct finite
self-adjoint rank-one perturbations and report numerical convergence. Neither source supplies this
coupled-error singular graph completion, its exact minimal debt, or the sharp global lower wall.

No priority claim is made pending specialist review.

## Lean realization

Formal module:

- `formal/GaloisForLFunctions/RHTower/MobiusGammaXiCoupledErrorSingularGraphGlobalWall.lean`

Capstones:

- `mobiusCriticalMassPerturbed_exactGraphBudget_posSemidef`
- `mobiusCriticalMassPerturbed_fixedFour_quadratic_lower`
- `all_mobiusCriticalMassPerturbedWithBudget_posSemidef_iff`
- `mobiusGammaXiCoupledErrorSingularGraphWall_posSemidef`
- `mobiusGammaXiCoupledErrorUncompletedWall_quadratic_lower`
- `all_mobiusGammaXiCoupledErrorWallWithBudget_posSemidef_iff`
- `tendsto_mobiusGammaXiCoupledErrorUncompletedWall_saturation`
- `mobiusGammaXiCoupledErrorSingularGraphDebt_eq_zero_iff_rh`

Verification:

- leaf check: `lake env lean GaloisForLFunctions/RHTower/MobiusGammaXiCoupledErrorSingularGraphGlobalWall.lean`
- targeted build: `lake build GaloisForLFunctions.RHTower.MobiusGammaXiCoupledErrorSingularGraphGlobalWall`
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- forbidden declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella build intentionally not run
