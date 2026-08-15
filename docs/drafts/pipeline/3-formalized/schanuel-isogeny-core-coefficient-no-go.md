# Isogeny-core invariance and coefficient-descent no-go for stage-two Schanuel defects

- **ID:** schanuel-isogeny-core-coefficient-no-go
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) + FALSIFIED DESCENT CONJECTURE
- **Source:** `schanuel-defect-coefficient-descent.md`; stage-two defect-slope normal form
- **Statement:** A hypothetical stage-two defect slope belongs to every finite-isogeny value
  subfield, but their intersection need not descend at all; integer isogenies preserve the exact
  coefficient wall rather than breaking it.

## Goal

Exploit the largest algebraic operation that preserves numerical exponentiation exactly:

\[
  (x,y)\longmapsto (Mx,y^M),\qquad M\in\operatorname{Mat}_2(\mathbb Z),\quad\det M\ne0.
\]

The initial conjecture was that invariance under all such isogenies forces the canonical
stage-two defect slope into the additive-coordinate field, where algebraic-coefficient descent
might apply.  The conjecture is false.  The surviving theorem identifies the exact isogeny core
and proves that the endpoint exponential branch, not finite-isogeny algebra, is the missing datum.

## Gates

- [x] 0 -> 1  in-progress: exact statement, proof, hostile countermodel, and pivot identified
- [x] 1 -> 2  fully-proven: core membership and exact normal-closure classification proved
- [x] 2 -> 3  formalized: scalar-power fixed-field core, finite-Galois power-primitive
  stabilization, rank-one value-field slope descent, every concrete two-dimensional full-matrix
  isogeny field, and full-matrix/scalar-core intersection equality are Lean-proved
- [ ] 3 -> 4  publication-ready: external novelty audit; elementary mechanism likely a bridge

## Setup

Assume a stage-two counterexample and write

\[
 K=\overline{\mathbb Q}(x_1,x_2,y_1,y_2),\qquad y_i=e^{x_i},\qquad
 \epsilon_2=\rho\epsilon_1,
\]

where `trdeg K=1`, `epsilon_i=dlog(y_i)-dx_i`, and `rho` is transcendental over `Qbar`.
For an integral matrix

\[
 M=\begin{pmatrix}a&b\\c&d\end{pmatrix},\qquad \det M\ne0,
\]

put

\[
 K_M=\overline{\mathbb Q}(ax_1+bx_2,cx_1+dx_2,
                           y_1^ay_2^b,y_1^cy_2^d).
\]

Since `M` is invertible over `Q`, `K_M` contains `x_1,x_2`.  The adjugate identities show that
fixed nonzero powers of `y_1,y_2` lie in `K_M`; hence `K/K_M` is finite and `trdeg K_M=1`.

## Theorem: finite-isogeny core membership

For every such `M`,

\[
  \rho\in K_M.
\]

Consequently

\[
  \rho\in K_{\mathrm{iso}}:=\bigcap_{\det M\ne0}K_M. \tag{IC}
\]

### Proof

The transformed tuple `(Mx,y^M)` is again a numerical exponential tuple and remains
`Q`-linearly independent.  Its defect forms pull back to

\[
 \epsilon'_1=a\epsilon_1+b\epsilon_2=(a+b\rho)\epsilon_1,
 \qquad
 \epsilon'_2=c\epsilon_1+d\epsilon_2=(c+d\rho)\epsilon_1.
\]

The integral defect-lattice theorem makes `epsilon'_1` nonzero.  Since `K_M` has transcendence
degree one, there is a unique `sigma_M in K_M` with

\[
 \epsilon'_2=\sigma_M\epsilon'_1.
\]

After pullback to `K`,

\[
 \sigma_M=\frac{c+d\rho}{a+b\rho}.
\]

The denominator is nonzero, again by integral defect independence.  Solving the fractional-linear
identity gives

\[
 \rho=\frac{c-a\sigma_M}{b\sigma_M-d}.
\]

Here `b sigma_M-d` cannot vanish because its product with `a+b rho` is `bc-ad=-det(M)`.
Thus `rho in K_M`, proving `(IC)`. **[PROVED HERE]**

The scalar-power special case is already informative:

\[
 \rho\in\bigcap_{m\ge1}
 \overline{\mathbb Q}(x_1,x_2,y_1^m,y_2^m).
\]

## Theorem: exact Kummer-core classification

Let

\[
 F=\overline{\mathbb Q}(x_1,x_2),
\]

so `K=F(y_1,y_2)` is finite over `F`, and let `N/F` be a finite Galois normal closure.  Write
`G=Gal(N/F)` and `H=Gal(N/K)`.  For `sigma in G` define its toric conjugacy ratio

\[
 r_\sigma=\left(\frac{\sigma(y_1)}{y_1},
                  \frac{\sigma(y_2)}{y_2}\right)\in(N^*)^2
\]

and put

\[
 T=\{\sigma\in G:r_\sigma\in\mu_\infty^2\}.
\]

Then `T` is a subgroup containing `H`, and

\[
 K_{\mathrm{iso}}=N^T. \tag{KC}
\]

Indeed, `F` contains all roots of unity, so every `sigma in G` fixes `mu_infty`.  The cocycle identity

\[
 r_{\sigma\tau}=r_\sigma\,\sigma(r_\tau)=r_\sigma r_\tau
\]

makes `T` a subgroup.  For each full-rank `M`, let `H_M=Gal(N/K_M)`.  If `sigma in H_M`, then
`r_sigma^M=(1,1)`; multiplication by `adj(M)` gives
`r_{sigma,i}^{det M}=1`, so `sigma in T`.  Conversely, if `sigma in T`, one common exponent `m`
kills both ratio coordinates, hence `sigma` fixes `y_1^m,y_2^m` and belongs to `H_{mI}`.  Therefore

\[
 \bigcup_{\det M\ne0}H_M=T.
\]

The intersection/fixed-field correspondence now gives

\[
 \bigcap_M K_M
 =N^{\langle\cup_M H_M\rangle}
 =N^T.
\]

This proves `(KC)`. **[PROVED HERE]**  In particular:

- `K_iso=K` exactly when no `F`-conjugacy outside `H` rotates both `y_i` by roots of unity;
- `K_iso=F` exactly when all of `G` consists of such torsion conjugacies.

Moreover `H` is normal in `T`: every element of `T` maps
`K=F(y_1,y_2)` to itself.  The ratio map induces an injection

\[
 T/H\hookrightarrow\mu_\infty^2.
\]

Thus `K/K_iso` is a finite abelian Kummer extension of rank at most two.  The slope `rho` is fixed
by this entire torsion-holonomy quotient.

## Theorem: power-primitive counterexample normal form

Every stage-two counterexample has an integer isogenous counterexample with the same defect slope
whose toric value extension is power-primitive.

For `r>=1`, set

\[
 L_r=F(y_1^{r!},y_2^{r!}).
\]

This is a descending chain of intermediate fields of the finite separable extension `K/F`.  A
finite separable extension has only finitely many intermediate fields, so `L_r` stabilizes.  Choose
`r_0` after stabilization and put `m=r_0!`, `K'=F(y_1^m,y_2^m)`.  For every `k>=1`, choose `r`
with `mk` dividing `r!`.  Then

\[
 K'=L_r\subseteq F(y_1^{mk},y_2^{mk})\subseteq F(y_1^m,y_2^m)=K',
\]

so

\[
 F((y_1^m)^k,(y_2^m)^k)=K'\qquad(k\ge1). \tag{PP}
\]

The transformed numerical tuple `(mx_1,mx_2,y_1^m,y_2^m)` is still `Q`-linearly independent,
still has transcendence degree one, and its defect forms are `m epsilon_i`; hence its canonical
slope is still `rho`.  The core-membership theorem places `rho` in `K'`.  This proves the
power-primitive normal form. **[PROVED HERE]**

In normal-closure language, `(PP)` says that no nontrivial conjugacy outside the pointwise
stabilizer rotates both torus coordinates by roots of unity.  Scalar powering has removed all
finite Kummer ambiguity before the hard arithmetic step begins.

## Failed conjecture: the isogeny core descends

The conjecture

\[
 K_{\mathrm{iso}}\subseteq\overline{\mathbb Q}(x_1,x_2)
\]

is false from algebraic and differential data alone.

Let `F=Qbar(t)`, `K=F(u)` with `u^2=t`, and choose

\[
 x_1=t,\quad x_2=t^2,\quad y_1=1+u,\quad y_2=2+u.
\]

The nontrivial `F`-automorphism sends `u` to `-u`.  Set

\[
 r_1=\frac{1-u}{1+u},\qquad r_2=\frac{2-u}{2+u}.
\]

For a full-rank matrix `M`, if both monomials `y_1^a y_2^b` and `y_1^c y_2^d` were fixed, then
`r^M=(1,1)`.  The adjugate identity would make both `r_i` roots of unity.  This is impossible
because each `r_i` is a nonconstant rational function.  At least one monomial therefore generates
the quadratic extension, so `K_M=K` for every `M` and

\[
 K_{\mathrm{iso}}=K\ne F.
\]

The associated defect ratio is a nonconstant element of `K`, so the model retains the full
one-dimensional differential geometry.  What it deliberately lacks is a complex specialization
at which both `y_i=e^{x_i}`.  Therefore no argument using only finite isogenies, Kähler
differentials, traces, norms, or abstract function-field Galois theory can finish the descent.

## No-go closure

- **Exact killing mechanism:** finite torus isogenies are generically birational on the chosen
  curve/function field.  Powering coordinates often loses no field information, so intersection
  over powered subfields need not shrink.
- **Strongest positive survivor:** theorems `(IC)`, `(KC)`, and `(PP)`: the slope is a simultaneous
  rational function of every finite-isogeny transform; their exact intersection is the fixed field
  of coordinatewise torsion conjugacies; and every counterexample is integer-isogenous to a
  power-primitive one with identical slope.
- **New insight:** the slope is an isogeny-core invariant.  Earlier trace/norm failure and current
  core failure are the same phenomenon: algebraic functoriality preserves the coefficient wall but
  erases the selected analytic exponential branch.  A successful next invariant must be
  branch-sensitive while remaining arithmetic under specialization.
- **Status:** dependency-closed paper proofs.  The scalar-power group/fixed-field classification is
  formalized by `iSup_powerTupleStabilizer_eq_torsionRatioClosure` and
  `iInf_fixedField_powerTupleStabilizer_eq_torsionRatioClosure` in
  `HTGeometry/SchanuelIsogenyCore.lean`; scratch axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  The finite-Galois stabilization underlying `(PP)` is
  formalized by `exists_powerTupleStabilizer_primitive_core`: one positive exponent realizes the
  full scalar-power stabilizer core, every further positive multiple has the same stabilizer, and
  its fixed field equals the stable fixed field.  The coefficient-descent core of `(IC)` is
  formalized by
  `schanuelDefect_slope_mem_intermediateField_of_finrank_one` in
  `RHTower/SchanuelDefectValueField.lean`: any rank-one intermediate field carrying both
  exponential pairs contains their ambient defect slope.  Its scratch axiom audit again reports
  only `propext`, `Classical.choice`, and `Quot.sound`.  Full-matrix inversion is formalized by
  `mobius_slope_mem_intermediateField`: descent of
  `(c+d*rho)/(a+b*rho)` through a nonzero-determinant integral matrix forces descent of `rho`.
  Their exact combination is formalized by
  `schanuelDefect_slope_mem_of_integral_isogeny` in the umbrella-wired module
  `RHTower/SchanuelDefectIsogeny.lean`: any rank-one intermediate field carrying the transformed
  exponential pair contains the original slope.  The concrete generated field `K_M`, adjugate
  recovery of both additive coordinates and determinant powers, finite/separable descent, and the
  deduction of its Kähler finrank from `trdeg=1` are formalized by
  `finiteDimensional_integral_isogeny_valueField` and
  `schanuelDefect_slope_mem_integral_isogeny_valueField` in the umbrella-wired module
  `RHTower/SchanuelIntegralIsogenyValueField.lean`.  Their scratch axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  The exact cofinality statement `(3)` is
  formalized by `fullIntegralIsogenyCore_eq_scalarPowerIsogenyCore` in
  `RHTower/SchanuelIntegralIsogenyCoreIntersection.lean`, using the explicit determinant-power
  containment and scalar-matrix realization; its scratch axiom audit has the same standard list.
  Targeted external
  search found Kummer subfield results (for example Stacks Project, Tag `0EXP`) but no statement
  coupling finite-isogeny value fields to Schanuel defect slopes.  No priority claim.

## Next conjecture

Rule out the power-primitive normal form using a branch-sensitive invariant.  Compatible division
points

\[
 \left(\frac{x_i+k_i\tau}{m},\;\zeta_m^{k_i}y_i^{1/m}\right),
 \qquad \tau=2\pi i,
\]

whose selected member still satisfies exponentiation do not by themselves help: one-variable
solutions of `exp(2x)=x` already exhibit genuine quadratic torsion conjugacy.  After `(PP)`, the
required invariant must instead distinguish an isolated common exponential specialization on a
torically primitive algebraic curve; ordinary field intersection is proved insufficient.

## Log

- 2026-08-14 -- isogeny-core membership proved; naive core descent killed by an explicit quadratic
  function-field model; branch-sensitive Kummer tower isolated as next open mechanism.
- 2026-08-14 -- normal-closure audit produced exact Kummer-core fixed-field classification `(KC)`;
  core collapse is now equivalent to abundance of coordinatewise torsion conjugacies.
- 2026-08-14 -- factorial-power stabilization removed every finite Kummer layer and produced the
  power-primitive counterexample normal form `(PP)` without changing the canonical slope.
- 2026-08-14 -- scalar-power Kummer-core fixed-field classification formalized and umbrella-wired.
- 2026-08-14 -- finite-automorphism power-primitive stabilization formalized in scratch, copied
  exactly into `HTGeometry/SchanuelIsogenyCore.lean`, and axiom-audited; no project build run.
- 2026-08-14 -- full integral-matrix core/scalar-power core equality formalized in scratch,
  axiom-audited, and umbrella-wired as `RHTower/SchanuelIntegralIsogenyCoreIntersection.lean`.
- 2026-08-14 -- rank-one intermediate-value-field slope descent formalized and axiom-audited in
  scratch, then copied into already-wired `RHTower/SchanuelDefectValueField.lean`.
- 2026-08-14 -- nondegenerate integral Möbius slope inversion formalized with explicit ring
  identities after retiring a tactic-heavy elaboration; scratch axiom audit clean.
- 2026-08-14 -- full nondegenerate integral-isogeny slope descent combined in
  `RHTower/SchanuelDefectIsogeny.lean`, scratch-verified, axiom-audited, and umbrella-wired.
- 2026-08-14 -- concrete `K_M` construction closed in Lean: adjugate coordinate/power recovery,
  finite separable extension, `trdeg=1` Kähler-rank transfer, transformed exponential law and
  rational independence, and original-slope membership all scratch-verified and umbrella-wired.

## Lean certificate

Modules (all wired into their umbrellas and built green):
`GaloisForLFunctions.HTGeometry.SchanuelIsogenyCore`,
`GaloisForLFunctions.RHTower.SchanuelDefectValueField`,
`GaloisForLFunctions.RHTower.SchanuelDefectIsogeny`,
`GaloisForLFunctions.RHTower.SchanuelIntegralIsogenyValueField`,
`GaloisForLFunctions.RHTower.SchanuelIntegralIsogenyCoreIntersection`.

| Card statement | Lean declaration |
|---|---|
| scalar-power group classification | `iSup_powerTupleStabilizer_eq_torsionRatioClosure` |
| scalar-power fixed-field core | `iInf_fixedField_powerTupleStabilizer_eq_torsionRatioClosure` |
| `(PP)` power-primitive stabilization | `exists_powerTupleStabilizer_primitive_core` |
| rank-one slope descent | `schanuelDefect_slope_mem_intermediateField_of_finrank_one` |
| full-matrix Möbius descent | `mobius_slope_mem_intermediateField` |
| `(IC)` integral-isogeny slope membership | `schanuelDefect_slope_mem_of_integral_isogeny` |
| concrete isogeny value field | `finiteDimensional_integral_isogeny_valueField`, `schanuelDefect_slope_mem_integral_isogeny_valueField` |
| `(3)` core intersection equality | `fullIntegralIsogenyCore_eq_scalarPowerIsogenyCore` |

Every listed declaration reports exactly `propext`, `Classical.choice`, `Quot.sound`.
