# Soldered graded Ambrose--Singer--Spencer conjecture

- **ID:** `nhg-soldered-graded-ass`
- **Stage:** 1 — in progress
- **Status:** `[CONJECTURE] [OPEN CORE] [FLAGSHIP FIELD PROBLEM] [NOT RH]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Proved base cases:** strict binary nilpotent Atiyah algebroids; abelian differential characters;
  flat nonabelian lower transport acting on an abelian higher module; fake-flat strict 2-groups with
  nonzero crossed-module boundary; semistrict two-term `L_infinity` connections with nonzero
  Jacobiator; first surviving cohomological curvature layer in every finite length; canonical
  secondary curvature and recursive partial-flattening obstruction spectra.

## 1. Geometric input

Let `M` be connected and real analytic. Let `mathcal A` be a complete filtered transitive analytic
cyclic `L_infinity`-algebroid with exact anchor sequence

\[
 0\longrightarrow\mathcal K\longrightarrow\mathcal A
 \xrightarrow{\rho}TM\longrightarrow0.
\tag{SG.1}
\]

Assume:

1. a source-canonical horizontal splitting `s:TM->mathcal A` and vertical projection `pr_K`;
2. a filtration-preserving compatible connection `nabla`;
3. a perfect fixed-degree cyclic pairing;
4. nilpotent finite-type vertical fibres;
5. integration to a source-simply-connected smooth nilpotent infinity-groupoid with higher parallel
   transport;
6. a formally integrable principal-parts/Spencer tower.

For the binary bracket define

\[
 \Omega_2(X,Y)=
 \operatorname{pr}_{\mathcal K}
 \bigl(\ell_2(sX,sY)-s[X,Y]\bigr).
\tag{SG.2}
\]

For `n>=3`, define the soldered horizontal curvature components

\[
 \Omega_n(X_1,\ldots,X_n)=
 \operatorname{pr}_{\mathcal K}
 \ell_n(sX_1,\ldots,sX_n).
\tag{SG.3}
\]

Retain all mixed horizontal--vertical components of `ell_n`; the horizontal forms alone need not be
closed under higher brackets.

## 2. Restricted higher holonomy

Let `Hol_x^0(mathcal A)` be the identity component of vertical higher holonomy at `x`, and let
`hol_x^0(mathcal A)` denote its tangent filtered cyclic `L_infinity` algebra. This object is assumed
to exist under the integration hypothesis; constructing it in sufficient generality is part of the
field programme.

For a path `gamma:x->y`, let `tau_gamma` denote higher parallel transport. Let `G_x` be the smallest
closed filtered cyclic `L_infinity` subalgebra of the vertical fibre at `x` containing:

- every parallel transport of every value of every `Omega_n`;
- every transported mixed curvature component;
- every surviving class and secondary transgression in the curvature Postnikov tower;
- closure under all vertical `L_infinity` brackets.

## 3. Conjecture

### Soldered graded Ambrose--Singer--Spencer

\[
 \boxed{
 \mathfrak{hol}_x^0(\mathcal A)=\mathfrak G_x.}
\tag{SG.4}
\]

Under analyticity, `(SG.4)` is equivalent to generation by the full covariant Spencer-jet tower at
`x`:

\[
 \mathfrak{hol}_x^0(\mathcal A)=
 \left\langle
 (\nabla^k\Omega_n)_x,
 \text{all mixed jets}:n\geq2, k\geq0
 \right\rangle_{L_\infty}.
\tag{SG.5}
\]

Ordinary loop holonomy is the binary two-form sector. An `n`-form contributes to
`(n-1)`-dimensional higher holonomy or, after transgression by an `(n-2)`-probe, to loop holonomy on
a mapping space.

For each fixed degree `n>2`, the closed higher-holonomy group is abelian. Nonabelian structure in
`hol_x^0` means the coupled graded `L_infinity` structure: lower-degree transport acts on higher
homotopy, and mixed brackets/Postnikov operations couple degrees. It does not mean two closed
`(n-1)`-holonomies in one fixed homotopy group fail to commute.

Full higher holonomy is an extension of the restricted object by independent global monodromy of
the fundamental infinity-groupoid. No local curvature theorem can remove that term.

## 4. Proved base cases

### 4.1 Strict binary case

For an analytic principal bundle with connected simply connected finite-dimensional nilpotent
structure group, the Atiyah-algebroid splitting gives `(SG.2)`. Classical Ambrose--Singer and
analytic jet generation prove `(SG.4)`--`(SG.5)` for `n=2` and restricted loop holonomy.

### 4.2 Abelian higher case

For a degree-`n` differential character, its integral closed `n`-form is local curvature and its
character value on `(n-1)`-cycles is higher holonomy. Transgression over an `(n-2)`-manifold gives
ordinary degree-two differential-character holonomy on a mapping space. Flat character ambiguity is
the independent global term.

### 4.3 Strict crossed-module case

For a fake-flat strict 2-connection, the higher Bianchi identity forces `H_3` into `ker t`, and
closed surface holonomy also lands in the central abelian group `ker t=pi_2`. More strongly, fake
flatness makes the induced connection on `ker t` flat and makes `H_3` covariantly closed. The lifted
restricted surface-holonomy algebra is exactly the span of transported `H_3` values and, analytically,
their Spencer jets. Thus the strict 2-group sector is closed even when `t` is nonzero.

### 4.4 Twisted-module generation

When `t=0`, fake flatness makes the lower `G`-connection flat and the higher coefficient bundle a
flat `G`-module. Small-cube and Riemann-sum arguments prove that transported higher-curvature values
generate exactly the identity-component higher-period algebra; analyticity identifies it with the
full covariant Spencer-jet span. The nonzero-`t` theorem above shows that the same mechanism survives
after kernel reduction for every strict crossed module.

### 4.5 Semistrict two-term generation

For a two-term `L_infinity` algebra `V_{-1}->V_0`, fake flatness makes `ker mu_1` an honest flat
module over `coker mu_1`. The complete homotopy Bianchi identity forces the Jacobiator-corrected
3-curvature into this kernel and makes it covariantly closed. The transported curvature, lifted
period, and analytic Spencer-jet spans therefore agree. A genuine nonzero `mu_3` is now included.

### 4.6 Leading curvature in every finite length

For any finite nilpotent nonpositively graded `L_infinity` algebra, suppose curvature components
below form degree `r` vanish. The universal Bianchi identity makes `F_r` an internal cycle and makes
its class a closed `r`-form in the flat internal-homology local system. Transported values, lifted
periods, and analytic jets have the same span. This proves the leading page of the curvature
Postnikov tower in arbitrary length.

## 5. Exact open core

The first unproved implication is now a length-three-or-higher, genuinely multigraded nonlinear
generation theorem for the **Massey-indeterminate later** curvature Postnikov layers:

1. define smooth higher transport on sufficiently small `n`-cubes from the integrated nilpotent
   `L_infinity` algebroid;
2. prove its first nonzero infinitesimal term is the soldered component `Omega_n`, with all mixed
   terms required by the higher Jacobi identities;
3. prove subdivision and higher nonabelian Stokes place every restricted higher-holonomy tangent in
   the `L_infinity` algebra generated by transported curvature components;
4. use analyticity to replace transported values by the Spencer-jet tower.

Step 2 is not enough. The reverse inclusion in Step 3 is the genuine Ambrose--Singer content.

## 6. Hostile failures already closed

1. **Raw primary operation generates loops — false/ill-typed.** `q_n` has no base-cotangent input.
2. **First nonzero operation suffices — false.** Mixed and later operations may be needed for
   closure.
3. **Local curvature determines full holonomy — false.** Flat global monodromy survives.
4. **One finite jet order suffices uniformly — false.** Binary analytic connections can postpone
   first nonzero curvature jet arbitrarily far.
5. **Unanchored product works — false.** Zero anchor supplies no history transport.
6. **Any filtration is Spencer geometry — false.** Principal-parts origin and formal integrability
   are load-bearing.
7. **Curvature form alone defines nonabelian surface transport — false.** Fake-flatness, gluing, and
   higher transport data are required.
8. **Cyclic pairing implies properness — false.** Gauge-orbit nonproperness persists before
   reduction.

## 7. Falsifiers

The conjecture fails if any example satisfying all six hypotheses has a restricted higher-holonomy
tangent not contained in `G_x`, or a transported curvature generator not realized infinitesimally by
higher holonomy. It is also falsified if `(SG.4)` changes under structured cover-Morita equivalence.

## 8. Parent boundary

Higher parallel transport for filtered `L_infinity` connections, nonabelian gerbe surface holonomy,
and integrations of singular-foliation `L_infinity` algebroids exist separately. No located theorem
establishes `(SG.4)` in the stated relative filtered cyclic Spencer setting. This is a claim about an
exact missing synthesis and theorem, not about novelty of the machinery.
