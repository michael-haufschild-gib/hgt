# Defect Grassmannian descends to the Kummer isogeny core

- **ID:** schanuel-defect-grassmannian-kummer-core
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** integral defect independence + separable Kähler base change + integral isogenies
- **Statement:** Every normalized Plücker coordinate of a Schanuel defect-kernel subspace lies in
  the scalar Kummer core, and the full integral-isogeny core equals that scalar core.

## Goal

Identify the higher-dimensional object shadowed by the stage-two defect slope.  The result must
remain correct when defect forms do not span the full Kähler module; assuming that equality would
silently import part of Schanuel.

## Gates

- [x] 0 -> 1  in-progress: projective-kernel conjecture stated and dimension trap removed
- [x] 1 -> 2  fully-proven: base-change, isogeny action, and core equality proved below
- [ ] 2 -> 3  formalized: full/scalar core equality is Lean-proved; general Kähler base-change and
  Plücker field-of-definition layer remain
- [ ] 3 -> 4  publication-ready: independent proof and external novelty audits pending

## Setup

Let `A=Qbar`, let `x=(x_1,...,x_n)` be rationally linearly independent, put `y_i=exp(x_i)`, and

\[
 K=A(x_1,\ldots,x_n,y_1,\ldots,y_n).
\]

Write

\[
 \epsilon_i=d\log y_i-dx_i\in\Omega_{K/A}
\]

and define the defect map

\[
 \Delta_K:K^n\longrightarrow\Omega_{K/A},\qquad
 (u_i)\longmapsto\sum_i u_i\epsilon_i. \tag{1}
\]

Let `W=ker Delta_K` and put `s=rank_K(im Delta_K)`.  Then `dim_K W=n-s`.  Integral defect
independence says `W` contains no nonzero vector in `A^n`, but it does **not** imply
`s=trdeg_A K`; the theorem uses the actual rank `s`.

For a full-rank matrix `M in Mat_n(Z)`, define

\[
 K_M=A\bigl(Mx,y^M\bigr), \tag{2}
\]

where row `j` of `M` gives `(Mx)_j=sum_i M_ji x_i` and
`(y^M)_j=prod_i y_i^{M_ji}`.  For `m>=1`, write `K_m=K_{mI}`.

## Theorem 1: full core equals scalar core

\[
 \bigcap_{\det M\ne0}K_M=\bigcap_{m\ge1}K_m. \tag{3}
\]

### Proof

The left intersection is contained in the right because every `mI` occurs among the full-rank
matrices.  Conversely, fix `M` and set `D=det M`.  The adjugate identity recovers `x` rationally
from `Mx`, so every `x_i` belongs to `K_M`.  Applying the adjugate to the Laurent monomials `y^M`
shows that `y_i^D` belongs to `K_M`; replacing `D` by `|D|` only inverts when necessary.  Hence

\[
 K_{|D|}\subseteq K_M. \tag{4}
\]

An element of every scalar field lies in `K_|D|` and therefore in this arbitrary `K_M`, proving
the reverse inclusion in `(3)`.  The same argument shows `K/K_M` is finite: `x` already lies in
`K_M`, while each `y_i` is algebraic over its nonzero `|D|`-th power. **[PROVED HERE]**

## Theorem 2: Grassmannian core descent

Choose a nonzero Plücker coordinate `p_I(W)` and normalize the Grassmannian point of `W` by it.
Then every ratio

\[
 \frac{p_J(W)}{p_I(W)}
\]

belongs to every `K_M`, hence to the common core `(3)`.

### Proof

The transformed defects in `Omega_(K_M/A)` are

\[
 \epsilon'_j=d\log (y^M)_j-d(Mx)_j.
\]

After extension to `K`, Laurent differentiation gives

\[
 \epsilon'_j=\sum_i M_{ji}\epsilon_i. \tag{5}
\]

Characteristic zero makes the finite extension `K/K_M` separable.  Kähler base change therefore
identifies

\[
 K\otimes_{K_M}\Omega_{K_M/A}\;\simeq\;\Omega_{K/A}. \tag{6}
\]

Fields are flat, so the kernel `W'_M` of the transformed defect map over `K_M` base-changes to the
kernel of the same map over `K`.  Equation `(5)` gives, with column-vector conventions,

\[
 K\otimes_{K_M}W'_M=(M^T)^{-1}W,
 \qquad W=M^T(K\otimes_{K_M}W'_M). \tag{7}
\]

Since `M^T` has rational entries, `(7)` exhibits `W` as a subspace defined over `K_M`.  Its
normalized Plücker ratios therefore lie in `K_M`.  This holds for every full-rank `M`; `(3)` puts
them in the scalar Kummer core. **[PROVED HERE]**

For `n=2` and `s=1`, `W` is a projective line and one affine Plücker ratio is exactly the canonical
defect slope up to the chosen sign/convention.  Thus finite-isogeny slope descent is the first
Grassmannian case, not an isolated Möbius trick.

## No-go closure

The stronger conjecture that the defect kernel descends to the additive field `A(x)` is false for
the same quadratic function-field model as the stage-two isogeny-core no-go: the scalar Kummer core
can equal all of `K`.  Grassmannian descent therefore preserves, rather than removes, the
coefficient wall.

- **Exact killing mechanism:** finite torus isogenies erase only torsion conjugacy.  A generically
  birational value curve retains every Plücker coefficient.
- **Strongest positive survivor:** core equality `(3)` and all-dimensional Grassmannian descent.
- **New insight:** every earlier slope, Möbius, and trace obstruction is a chart of one projective
  defect-kernel invariant.  Failure at higher Schanuel stages is controlled by a Kummer-core-valued
  Grassmannian point, not a collection of unrelated scalar coefficients.
- **Status:** dependency-closed paper proof.  The `n=2` affine chart is Lean-proved by
  `schanuelDefect_slope_mem_of_integral_isogeny`; its concrete generated full-matrix field and
  `trdeg=1` rank transfer are Lean-proved by
  `schanuelDefect_slope_mem_integral_isogeny_valueField`.  The all-dimensional transformation law
  `(5)` is Lean-proved by `schanuelDefect_integer_linearCombination`.  Core equality `(3)` is
  Lean-proved by `fullIntegralIsogenyCore_eq_scalarPowerIsogenyCore` in
  `RHTower/SchanuelIntegralIsogenyCoreIntersection.lean`.  The **Plücker field-of-definition layer is now Lean-proved** in
  `HTGeometry/PlueckerFieldOfDefinition.lean` (new, umbrella-wired, axiom-clean):
  `pluecker` defines the Grassmannian coordinates as the maximal minors of a spanning matrix,
  `pluecker_mul` shows a basis change scales every coordinate by one determinant,
  `pluecker_ratio_mul` shows the normalized ratios are basis-independent, and
  `pluecker_mem_range` / `pluecker_ratio_mem_range` prove the descent: a subspace spanned over a
  subfield has every minor and every normalized Plücker ratio in that subfield.  That is exactly
  the last step of Theorem 2 -- once `(7)` exhibits `W` as spanned over `K_M`, its ratios lie in
  `K_M`.

  Equation `(6)` -- the **separable Kähler base change** -- is now Lean-proved as well, in
  `HTGeometry/SeparableKaehlerBaseChange.lean` (new, umbrella-wired, axiom-clean):
  `kaehlerBaseChangeOfSeparable` is the isomorphism `K (x)_F Omega[F/A] = Omega[K/A]` for a
  separable `K/F`, `kaehlerBaseChangeOfIsAlgebraic` is its characteristic-zero form for any
  algebraic extension, and `mapBaseChange_injective_of_separable` /
  `mapBaseChange_surjective_of_separable` record the two halves.  The mathlib inputs are
  `Algebra.FormallyEtale.of_isSeparable` and
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`.

  The kernel bookkeeping `(7)` is Lean-proved in the same module:
  `ker_lTensor_eq_range_subtype` and `exists_of_mem_ker_lTensor` show that the kernel of a base-
  changed map is exactly the extension of the small-field kernel -- flatness of a field extension,
  via mathlib's `Module.Flat.ker_lTensor_eq`.

  **What remains:** only the instantiation -- naming the concrete defect map `Delta_K` of `(1)` as
  the base change of `Delta_{K_M}` through `(5)`, and reading its kernel basis as a matrix over
  `K_M` so that `pluecker_ratio_mem_range` applies.  Every mathematical input of Theorem 2 --
  base change `(6)`, kernel descent `(7)`, Plücker field of definition -- is now formal.

## Big-picture consequence

Any successful coefficient argument must act on the Kummer-core Grassmannian point using data not
visible to finite algebraic isogenies.  The only structure discarded by all current descent maps is
the selected Archimedean exponential branch.  This locates the missing universal principle as a
Betti/de Rham comparison constraint on the defect Grassmannian, not another field intersection.

## Novelty audit

Kähler base change, Plücker descent, and Kummer adjugate identities are classical separately.
Targeted searches found no Schanuel-defect Grassmannian or isogeny-core statement.  Treat the
combination as a new internal theorem; external novelty unconfirmed and no priority claimed.

## Log

- 2026-08-14 -- stage-two slope reinterpreted as first affine chart of a general defect-kernel
  Grassmannian; core equality and Plücker descent proved on paper.
- 2026-08-14 -- all-dimensional integral transformation law for numerical Schanuel defects
  scratch-proved, axiom-audited, copied into the isogeny module, and covered by existing umbrella.
- 2026-08-14 -- full integral-isogeny core/scalar-power core equality scratch-proved,
  axiom-audited, and umbrella-wired.
