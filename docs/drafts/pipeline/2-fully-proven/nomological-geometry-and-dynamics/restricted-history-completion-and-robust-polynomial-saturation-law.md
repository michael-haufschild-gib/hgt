# Restricted-history completion and robust polynomial-saturation law

- **ID:** `restricted-history-completion-and-robust-polynomial-saturation-law`
- **Stage:** 2 — fully proved on paper
- **Type:** THEOREM / FIELD-CALIBRATION / NO-GO
- **Status:** `[PAPER-PROVED] [ROUTE-INDEPENDENT HISTORY LAW] [HURWITZ REALIZATION]`
  `[NOT RH] [NO LEAN WRITTEN OR BUILT THIS TURN]`
- **Formal parent, used read-only:**
  `formal/GaloisForLFunctions/Hurwitz/PowerOrbitAdditiveSaturation.lean` and
  `formal/GaloisForLFunctions/Hurwitz/IntegerTranslationDifferentialMatroid.lean`

## 1. Why this theorem is needed

A scalar summary of local holonomy is not a model of hypertranscendence.  The corpus contains
ordinary Hurwitz pairs which are jointly differentially algebraically independent although their
common local monodromy orbit is finite.  The full **marked** holonomy closure does encode the exact
Hurwitz differential partition through its coordinate characters, but does not prove its analytic
realization.  The missing proof coordinate is **history support**: arbitrarily many branch columns
may be looped independently, while every fixed finite observer remains compact or even periodic.

This card isolates two exact, source-independent mechanisms:

1. finite-support histories have a compact product completion with boundary histories not present
   in the source;
2. sufficiently robust independent history columns annihilate every polynomial relation of a
   prescribed degree.

The combination is the first precise CLG law in which closed observer behaviour and open lifted
history coexist without metaphor.

## 2. Restricted histories and observer completion

Let `J` be countably infinite.  For each `j in J`, let `K_j` be a compact Hausdorff group and let
`Gamma_j <= K_j` be a dense subgroup.  Put

\[
 G_{\mathrm{fin}}=\bigoplus_{j\in J}\Gamma_j,
 \qquad
 \widehat G=\prod_{j\in J}K_j .
\tag{1}
\]

Give `G_fin` the initial group topology for all finite-coordinate observers

\[
 \pi_F:G_{\mathrm{fin}}\longrightarrow\prod_{j\in F}K_j,
 \qquad F\Subset J.
\tag{2}
\]

### Theorem 2.1 — compact observers, open history

The canonical map `i:G_fin -> Ghat` has dense image.  Its closure, and hence its two-sided
Hausdorff (Raikov) uniform completion, is `Ghat`.  If infinitely many `Gamma_j` are nontrivial,
then `i(G_fin)` is proper and nonclosed.

More explicitly, choose distinct indices `j_1,j_2,...` and nonidentity
`g_n in Gamma_(j_n)`.  Define `h_N` to have coordinate `g_n` at `j_n` for `n<=N` and identity
elsewhere.  Then:

1. every fixed finite observer `pi_F(h_N)` is eventually constant;
2. the support cost `c(h_N)=|supp(h_N)|` tends to infinity;
3. `h_N` converges in `Ghat` to the infinite-support point `h_infty=(g_n)_n`, which does not belong
   to `G_fin`.

#### Proof

A basic open set in the product topology constrains only finitely many coordinates.  Density of
each `Gamma_j` lets a finite-support element meet those constraints, proving density of `i`.
If infinitely many chosen coordinates are nonidentity, their product point has infinite support
and is outside the direct sum, so the image is proper; a proper dense subgroup is nonclosed.
The initial topology in `(2)` is the subspace topology induced by `i`.  A dense uniform embedding
into the complete compact group `Ghat` has completion `Ghat`.  The three claims for `h_N` follow
directly from its support. ∎

### Corollary 2.2 — recurrence does not control history cost

No observer through one fixed finite `pi_F`, nor any function of that observer alone, can be
coercive for `c`: the sequence `h_N` is eventually constant in that observer while `c(h_N)->infty`.
Thus compactness, exact recurrence, or convergence after projection supplies no bound on lifted
history cost without an additional properness theorem.

## 3. Robust polynomial saturation

Let `Sigma` and `B` be finite sets, `V=C^Sigma`, and let

\[
 u_b:\mathbb N\longrightarrow V \qquad (b\in B)
\tag{3}
\]

be independently sampled history columns.  For `m:B->N` and a base point `x_0 in V`, define

\[
 x(m)=x_0+\sum_{b\in B}u_b(m_b),
 \qquad
 \Delta_b(r)=u_b(r+1)-u_b(r).
\tag{4}
\]

For `S subseteq B`, let `W_S` be the linear span of all `Delta_b(r)` with `b notin S` and
`r>=0`.

### Theorem 3.1 — degree-robust history saturation

Fix `D>=0`.  Assume

\[
 W_S=V
 \quad\text{for every }S\subseteq B\text{ with }|S|\le D.
\tag{5}
\]

If a polynomial `P in C[V]` of total degree at most `D` satisfies

\[
 P(x(m))=0\qquad\text{for every }m:B\longrightarrow\mathbb N,
\tag{6}
\]

then `P=0`.

#### Proof

Induct strongly on `D`.  For `D=0`, `P` is constant and `(6)` kills it.  Suppose `D>0`.
For a column `b` and step `r`, form the translation difference

\[
 Q_{b,r}(X)=P(X+\Delta_b(r))-P(X).
\tag{7}
\]

If `P` is nonconstant then `deg Q_(b,r)<deg P<=D`.  Freeze the `b`-th column at `r`; the remaining
grid still satisfies the induction hypothesis because deleting at most `D-1` further columns,
together with `b`, deletes at most `D` columns from `(5)`.  Equation `(6)` gives `Q_(b,r)=0` on that
reduced grid, hence `Q_(b,r)=0` identically.

Therefore `P` is invariant under every consecutive increment.  Condition `(5)` with `S=empty`
says those increments span `V`.  If `P(X+v)=P(X)`, iteration gives invariance under every integer
multiple of `v`; the polynomial `t->P(X+tv)-P(X)` then vanishes at all integers and hence for every
`t in C`.  Invariance is therefore closed under complex linear span.  All directional derivatives
of `P` vanish, so `P` is constant, and `(6)` makes it zero. ∎

### Exact interpretation

The theorem does not say that history is analytically noncompact.  It says that no degree-`D`
algebraic observer survives a history atlas whose increments remain spanning after any `D`
columns are lost.  Hypertranscendence can therefore be generated by **support-depth robustness**
even when every individual orbit is finite or compact.

## 4. Hurwitz realization and exact differential matroid

Let `I` be finite, let `s_i in C\Z`, and put

\[
 q_i=e^{-2\pi i s_i}.
\tag{8}
\]

For jet height `N` and proposed relation degree `D`, take `N+D+1` independent branch columns.  At
an upper-half-plane shift `a`, their value coordinates are

\[
 W_{b,(i,k)}=(b+a)^{-s_i-k},
 \qquad
 u_b(m)_{(i,k)}=W_{b,(i,k)}q_i^m,
\tag{9}
\]

for `0<=k<=N`.  If the `q_i` are pairwise distinct, then after deletion of any `D` columns the
remaining consecutive increments span every coordinate `(i,k)`: Vandermonde separation in the
distinct `q_i` isolates the exponent labels, and `N+1` surviving branch points give the invertible
jet Vandermonde block.

Theorem 3.1 therefore kills every degree-`D` relation among the joint `N`-jet rectangle.  Varying
`N,D` proves for the continued nonintegral Hurwitz family

\[
 \bigl(\widetilde\zeta(s_i,a)\bigr)_{i\in I}
 \text{ is differentially algebraically independent over }\mathbb C(a)
 \iff
 i\longmapsto q_i\text{ is injective}.
\tag{10}
\]

The reverse implication is exact: if `q_i=q_j`, then `s_i-s_j in Z`; the derivative ladder

\[
 \partial_a^k\widetilde\zeta(s,a)=(-1)^k(s)_k\widetilde\zeta(s+k,a)
\tag{11}
\]

gives a differential relation between the two labels.  The same formula holds for ordinary
Hurwitz zeta in its convergence chamber.  When every `Re(s_i)>1`, `(10)` transfers to
the ordinary convergent Hurwitz series.  This is the exact corpus theorem
`continued_hurwitz_intrinsic_residue_differentialMatroid_law` and its convergent specialization
`hurwitz_intrinsic_residue_differentialMatroid_law`.

### Countertheorem 4.1 — local holonomy dimension is not HT rank

Take `s_1=3/2` and `s_2=4/3`.  Their monodromy values have orders `2` and `3`, so the common local
cyclic orbit is finite of order `6` and its Zariski-closure dimension is zero.  Yet `q_1!=q_2`, so
`(10)` proves that the two ordinary Hurwitz functions are jointly differentially algebraically
independent.

There are also noncompact monomial-resonant examples.  Take

\[
 s_1=2+\frac{i\log2}{2\pi},
 \qquad
 s_2=2+\frac{i\log4}{2\pi}.
\]

Then `q_1=2,q_2=4`.  The local cyclic orbit lies in the one-dimensional subtorus
`q_2=q_1^2`, while `(10)` again gives differential rank two because the two monodromy values are
distinct.

Compare `q=(2,2)`: its orbit closure is also one-dimensional and its resonance lattice also has
rank one, but the equality partition has one class and differential rank one.  Thus `q=(2,2)` and
`q=(2,4)` have the same closure dimension and resonance-lattice rank but different DA ranks.

Consequently neither local orbit dimension, local recurrence type, nor the **rank** of the
monomial resonance lattice computes Hurwitz differential rank.  The full marked lattice together
with the coordinate characters does recover the equality partition, since
`q_i=q_j` iff `e_i-e_j in R_q`; the exact differential rank is the number of its classes.

## 5. Polar observer, recurrence, and open lift

The history law has a second exact finite-dimensional calibration.  Let
`T=(\mathbb C^\times)^I` carry its standard Hermitian compact form
`K_ph=(S^1)^I` and positive part `A=(\mathbb R_{>0})^I`.  Polar decomposition
gives

\[
 T/K_{\rm ph}\cong A,
 \qquad
 \operatorname{pol}(z)=(|z_i|)_i.
\tag{12}
\]

This is the precise sector in which positivity is a phase quotient.

### Theorem 5.1 — polar/prolongation/history separation

1. Let `K_0=V/Lambda` be a flat compact torus and `v in V` be nonzero.  The projected path
   `gamma_v(t)=tv mod Lambda` has compact recurrent closure, while its marked lift `t->tv` is
   proper and has length `|t| norm(v)`.  Exact projected recurrence occurs precisely when
   `Tv in Lambda` for some `T>0`.
2. No real-valued continuous endpoint observable on `K_0` recovers this lifted length: every such
   observable is bounded, while the length is unbounded.
3. For an automorphism `h` of a Hermitian line, put

   \[
    r(h)=\frac{\|hx\|}{\|x\|},
    \qquad
    E(h)=r(h)+r(h)^{-1}-2
        =4\sinh^2\!\left(\frac{\log r(h)}2\right).
   \tag{13}
   \]

   Then `E>=0`, `E(h)=0` exactly when `h` is unitary, and
   `E(uh)=E(h)=E(h^(-1))` for every unitary phase `u`.  Thus this positive energy forgets phase,
   winding, Berry holonomy, and time orientation.

#### Proof

The closure of a one-parameter subgroup in a compact group is compact, and translation on that
closure is recurrent.  The lift is a straight line in `V`; its properness and length formula are
immediate.  Periodicity is exactly the deck-lattice condition.  Continuous real observables on a
compact space are bounded.  Formula `(13)` and its invariances follow by direct calculation. ∎

### Countertheorem 5.2 — HT determines neither exact phase periodicity nor radial escape

The single Hurwitz functions with exponents

\[
 s_0=\frac32,
 \qquad s_1=\sqrt2,
 \qquad s_2=\sqrt2+i
\tag{14}
\]

are all hypertranscendental in the shift variable.  The first phase is exactly periodic.  The
second phase is recurrent but aperiodic, with constant positive projection.  The third has the
same aperiodic phase type as the second but modulus `e^(2 pi)` and escapes radially.  Hence the
same maximal differential-prolongation profile determines neither periodicity nor radial escape.

The Stokes--Mertens determinant energy is an arithmetic instance of `(13)`, with
`h=delta_p(s)^M`.  This statement applies to that rank-one determinant-holonomy sector only;
positive coarea, Rees positivity, and general Hodge or Witt forms are not automatically phase
quotients.

The exact no-mixing laws are therefore

\[
 \boxed{
 \begin{aligned}
 \text{prolongation growth}&\not\Rightarrow\text{radial escape},\\
 \text{positive radial data}&\not\Rightarrow\text{phase periodicity or holonomy},\\
 \text{compact phase recurrence}&\not\Rightarrow\text{lifted history cost}.
 \end{aligned}}
\tag{15}
\]

For the middle nonimplication, `q=2` and `q'=2e^(2 pi i alpha)` with irrational `alpha` have the
same positive radial history.  The first phase is exactly periodic; the second is aperiodic and
recurrent.  Both arise from nonintegral Hurwitz exponents with real part greater than one.

These organs may be coupled only by an independently proved constitutive morphism.

## 6. Constitutive-lawstack consequence

The local marked quotient `[T/Z]` computes the character-incidence partition but does not realize
the analytic proof or its history cost.  The required realization therefore also carries the
filtered history system

\[
 \mathfrak H_F=[T^F/\mathbb Z^F],\qquad F\Subset\mathbb N,
\tag{16}
\]

with action `(m*c)_(i,b)=q_i^(m_b)c_(i,b)`.  It is equipped with its support filtration,
branch-value realization `(9)`, and degree-sensitive conservativity law `(5)`.  When the local
image cyclic group `Gamma=<q>` has compact Hausdorff closure `K`, Theorem 2.1 applies to
`direct-sum Gamma`, not automatically to the marked `direct-sum Z`: the kernel of `Z->Gamma`
remains a separate winding/isotropy organ.  Noncompact local images require a different
completion.  Differential freedom is analytically proved by arbitrarily deep independent support
plus robust spanning, not by noncompactness of one local orbit.

This forces a field-level correction:

> A CLG chart must carry both an observer completion and a source-history filtration.  Local
> isotropy, coarse quotient, curvature, or recurrence cannot replace the filtration.  An
> observer is conservative only relative to a declared complexity class, here polynomial degree
> `D`, and the required history depth may grow with that complexity.

## 7. Falsifiable predictions

1. **Scalar local-holonomy falsifier.** Any proposed universal HT invariant depending only on
   orbit-closure dimension, resonance-lattice rank, or compact/torsion recurrence type is false by
   Countertheorem 4.1.  The full marked closure with coordinate characters does recover the
   Hurwitz partition, but not its analytic realization.
2. **Finite-window falsifier.** Any proof architecture claiming that one fixed finite branch window
   detects differential relations of all degrees must supply a different global mechanism;
   robust additive saturation itself uses a window growing with `D`.
3. **Recurrence/cost prediction.** A physical recurrence model cannot infer path length, circuit
   cost, or interior growth from compact endpoint recurrence alone.  It must specify a lifted
   history filtration or a proper action functional.
4. **Positivity-scope prediction.** A positive or phase-quotiented observer may certify a projected
   state while remaining blind to support cost.  A valid positivity-to-history theorem must prove
   coercivity across the support filtration, not only nonnegativity at every finite stage.
5. **Unitary-twist falsifier.** Any attempt to recover Berry phase, winding, or time orientation
   from the determinant energy `(13)` is false because arbitrary unitary twists leave it fixed.
6. **Finite-carrier physics falsifier.** A bounded finite Krylov coordinate cannot equal an
   additive lifted-history length through arbitrarily many recurrences.  Such a dictionary needs
   a growing carrier, a universal-cover variable, or another noncompact sector.

## 8. Scope and hostile limits

1. The history-completion theorem is topological; the polynomial-saturation theorem needs the
   independent robust-spanning hypothesis.
2. Compact recurrence does not cause hypertranscendence.  Their coexistence is explained by
   different local-observer and lifted-history coordinates.
3. The Hurwitz realization supplies a complete non-RH analytic chart.  No theorem here selects Xi
   zeros or proves RH.
4. Equation `(16)` records the exact filtered action system.  A universal 2-stack with transport
   among unrelated corpus routes remains unconstructed.
