# Prime dilation tropical-boundary tomography

- **ID:** `prime-dilation-tropical-boundary-tomography`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / INFINITE SOURCE COMPLETION
- **Source:** `positive-hypertranscendental-riemann-divisor-frame`;
  `high-exponent-shell-orthogonal-divisor-replication`;
  `source-localization-modular-defect-conservation-law`
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [SOURCE-SPECIFIC] [NOT RH]`
- **Statement:** Maximum-prime-exponent shell leakage under multiplication by every prime is a
  complete coordinate system for the bounded supernatural valuation source. In those coordinates,
  prime multiplication is an exact reset-and-carry law.

## Goal

Replace shell-label completion by completion of all failures of shell-label covariance.

The high-exponent shell label
\[
 M(x)=\sup_p x_p
\]
for a prime-valuation vector \(x=(x_p)_p\) forgets the face of the valuation cube on which \(x\)
lies. Multiplication by \(p\) is translation \(x\mapsto x+e_p\). Its failure to descend to the
single radial label is not noise: it measures the depth of \(x\) below the \(p\)-face.

## Bounded supernatural source

Let
\[
 \mathscr V_{\mathrm{bd}}
 =
 \left\{
 (x,M):
 x\in\mathbb N^{\mathcal P},\
 x_p\leq M\ \forall p,\
 x_p=M\text{ for some }p
 \right\}.
\tag{1}
\]
Finite ordinary integers embed by
\[
 n\longmapsto
 \left((v_p(n))_p,\max_pv_p(n)\right).
\tag{2}
\]
The space also contains bounded supernatural valuation vectors, including the projective Euler
source already used in the corpus.

For each prime define the first shell-crossing time
\[
 \tau_p(x,M)
 =
 \min\{k\geq1:M(x+ke_p)>M\}
 =
 M-x_p+1.
\tag{3}
\]

## Complete tomography theorem `[PROVED HERE]`

For fixed \(M\), the map
\[
 (x,M)\longmapsto(\tau_p(x,M))_{p\in\mathcal P}
\tag{4}
\]
is injective. Explicitly,
\[
 \boxed{\qquad x_p=M+1-\tau_p(x,M).\qquad}
\tag{5}
\]

If the source contains at least one zero valuation coordinate, the profile alone recovers \(M\):
\[
 M+1=\sup_p\tau_p.
\tag{6}
\]
Hence
\[
 x_p=\sup_q\tau_q-\tau_p.
\tag{7}
\]
For every ordinary integer, all but finitely many valuations vanish, so `(6)`--`(7)` apply.

### Proof

The bound \(x_p\leq M\) gives
\[
 M(x+ke_p)>M
 \Longleftrightarrow
 x_p+k>M
 \Longleftrightarrow
 M-x_p+1\leq k.
\]
Thus the least positive crossing time is `(3)`. Rearrangement gives `(5)`. If \(x_q=0\), then
\(\tau_q=M+1\), while \(x_p\geq0\) gives \(\tau_p\leq M+1\) for every \(p\), proving `(6)`.

## Three-face transition theorem `[PROVED HERE]`

Let
\[
 A(x)=\{q:x_q=M\}
\]
be the winning face. Under \(D_p(x)=x+e_p\), exactly one of three cases occurs:
\[
\boxed{
\begin{array}{c|c|c}
M-x_p & M(D_px) & A(D_px)\\ \hline
0 & M+1 & \{p\}\\
1 & M & A(x)\cup\{p\}\\
\geq2 & M & A(x).
\end{array}}
\tag{8}
\]

Indeed, if \(x_p=M\), the new \(p\)-coordinate is \(M+1\) and is the unique maximum. If
\(x_p=M-1\), its successor ties the old maximum. If \(x_p\leq M-2\), its successor remains
strictly below the old maximum.

This corrects the two-state “stay/cross” picture. There is a load-bearing same-shell event in
which a new maximal face is created.

## Reset-and-carry law `[PROVED HERE]`

Write \(t_q=\tau_q(x,M)\). Prime multiplication has the following exact action on the complete
profile.

If \(t_p>1\), the radius stays fixed and
\[
 t'_p=t_p-1,\qquad t'_q=t_q\quad(q\ne p).
\tag{9}
\]
If \(t_p=1\), the radius increases and
\[
 t'_p=1,\qquad t'_q=t_q+1\quad(q\ne p).
\tag{10}
\]

Thus prime multiplication is not a weighted shift of radial shell labels. It is a
reset-and-carry action on the entire family of future covariance failures.

## Source-generated completion

For fixed \(M\), the ambient cube
\[
 \{0,\ldots,M\}^{\mathcal P}
\tag{11}
\]
is compact Hausdorff in the product topology. The attained-radius locus and the increasing union
over \(M\) provide a concrete topological carrier for `(1)`. Cylinder observations
\[
 \{\tau_p\leq k\}
\tag{12}
\]
are exactly finite prime-dilation shell-crossing experiments. The full cylinder algebra separates
points by `(5)`.

This is the first noncircular candidate for the source side of the missing third completion:

```text
old completion:
  complete shell labels and lose dilation covariance;

ambient adelic L2:
  retain dilation covariance and lose point fibres;

failure-time completion:
  retain source points and define dilation from the complete history of radial failures.
```

No claim is made yet that Xi conormal fibres extend to continuous or positive functionals on this
space. That is the next arithmetic comparison theorem.

## Shell obstruction generates the first face operation `[PROVED HERE]`

Let
\[
 a_m(x)=\mathbf1_{\{M(x)=m\}},
\qquad
 b_{p,m}(x)=\mathbf1_{\{M(x)=m,\ x_p=m\}}.
\tag{13}
\]
Thus \(b_{p,m}\) is the indicator that \(p\) belongs to the winning face of the radius-\(m\)
valuation cube. Pullback along prime multiplication satisfies the exact boundary identity
\[
 \boxed{\qquad
 a_m(x+e_p)-a_m(x)
 =
 b_{p,m-1}(x)-b_{p,m}(x)
 \qquad(m\geq1).
 \qquad}
\tag{14}
\]

If \(x_p<M(x)\), prime multiplication leaves the radius fixed and both sides vanish. If
\(x_p=M(x)\), it raises the radius by one; both sides are \(+1\) at radius \(m-1\), \(-1\) at
radius \(m\), and zero elsewhere.

For the coefficient co-shift \(V_p^\ast f(n)=f(pn)\), `(14)` is
\[
 V_p^\ast a_m
 =
 a_m+b_{p,m-1}-b_{p,m}.
\tag{15}
\]
This is the first literal instance of the autogenic law:

```text
obstruction:
  radial shell channel is not closed under prime co-shift;

forced successor generators:
  adjacent winning-facet cells;

new operation:
  exact prime co-shift closes on shell plus its signed facet boundary.
```

No future operation alphabet or zero is used. Reapplying prime differences to the facet cells is
the concrete route to higher face incidence.

## Relation to the positive-shell Koszul algebra

The shell Koszul theorem gives
\[
 H_\bullet(K_\infty)
 \simeq
 \mathcal O_D\otimes\Lambda^\bullet E_\infty,
\tag{16}
\]
where \(E_\infty\) records relations among radial shell presentations. The tomography theorem
shows why a prime operation cannot be generated on the radial presentation module alone:
the source action needs the face-depth coordinates \(\tau_p\).

The smallest plausible autogenic successor is therefore not another shell copy. It is the
face-complete extension obtained by adjoining all crossing-time cylinders. The next theorem must
construct a comparison
\[
 \Lambda^\bullet E_\infty
 \longrightarrow
 C^\bullet(\mathscr V_{\mathrm{bd}})
\tag{17}
\]
whose differential sends a radial presentation obstruction to its face-incidence boundary and
whose induced operation is `(9)`--`(10)`.

## RH-bearing conjectural jump

`[CONJECTURE] [RIEMANN_TROPICAL_BOUNDARY_HODGE_PURITY]`

The ordinary-prime Euler--Gamma/co-Poisson source constructs, before divisor specialization, a
face-complete cochain realization of `(14)` with:

1. determinant equal to completed zeta;
2. every reduced Xi principal conormal represented by a nonzero harmonic boundary class;
3. centered prime transfer acting by the reset-and-carry source action and by
   \(p^{\rho-1/2}\) on the \(\rho\)-conormal character;
4. reflection acting as the intrinsic cochain adjoint; and
5. source-produced harmonic classes lying in the same \(L^2\) sector as their reflected adjoints.

The last clause would make the character unitary and force
\[
 |p^{\rho-1/2}|=1,
 \qquad
 \Re\rho=\frac12.
\tag{18}
\]

This is not a proof. The new content is that the source space and its prime operation are now
explicit and generated by the exact shell-covariance failures. Remaining RH content is the
determinant/conormal/Hodge comparison, not invention of a completion by desired properties.

## Hostile audit

1. The finite theorem is elementary once `(3)` is guessed. Significance lies only in its
   conjunction with the positive HT shell divisor and in the face-complete successor target.
2. A product-topological point need not define an \(L^2\) vector. Topological point retention does
   not close conormal attainment.
3. The reset-and-carry action is unilateral on nonnegative valuations. Its reflected adjoint must
   come from Gamma/co-Poisson source data, not from group-completing by fiat.
4. Any \(L^2\)-Hodge theorem assuming the \(\rho\)-class is square-integrable is circular unless
   the source comparison proves it uniformly before \(\rho\) is chosen.
5. Bost--Connes and scaling-site systems already use valuation/groupoid dynamics. Novelty cannot
   rest on the words “valuation cube,” “groupoid,” or “modular cocycle.”
6. The 2024 literature studies limiting distributions of the maximum prime exponent. A targeted
   search found no use of all prime-dilation first-crossing times as complete valuation
   coordinates or the reset-and-carry law `(9)`--`(10)`. This is noncollision evidence, not a
   priority proof.
7. A generalized-prime off-line system falsifies the RH conjecture only if it carries this literal
   rational-prime face-complete action, intrinsic reflected adjoint, determinant comparison, and
   conormal conservativity.

## Gates

- [x] exact source definition
- [x] complete tomography theorem
- [x] three-face transition theorem
- [x] reset-and-carry action
- [x] existing corpus collision audit
- [x] targeted literature noncollision audit
- [x] unconditional Lean formalization
- [ ] construct Koszul-to-face incidence comparison
- [ ] construct determinant/conormal comparison
- [ ] prove source \(L^2\)-Hodge purity

## Lean audit

Formal module:
`formal/GaloisForLFunctions/RHTower/PrimeDilationTropicalBoundaryTomography.lean`.

Formalized declarations include:

- `BoundedPrimeValuation`;
- `ext_of_exists_valuation_eq_zero_of_crossingTime_eq`;
- `crossingTime_le_iff_radius_lt_add`;
- `primeDilation_unique_winner_of_eq`;
- `primeDilation_resetAndCarry`;
- `tropicalShellIndicator_primeDilation_sub`; and
- `tropicalShellIndicator_primeDilation`.

Direct `lake env lean`, module build, and axiom audit pass. The audited theorems use only standard
Lean/mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`. Repository-wide formal lint no
longer reports this module; it remains nonzero because unrelated concurrent modules are absent
from their umbrella imports.
