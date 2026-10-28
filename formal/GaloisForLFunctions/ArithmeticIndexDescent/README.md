# Arithmetic Index Descent

**One question.** Can positive arithmetic section spaces be assembled and refined while controlling
the negative index of the complete Weil form, including its mixed prime interactions, infinite
place and two pole moments?

Arithmetic Index Descent studies source-defined presentations of signed arithmetic forms and the
cost of passing between them. Its basic object is a finite family of arithmetic tests together
with its complete Gram matrix. Its basic invariant is the number of negative squares. Its central
problem is to derive a bound on that number from arithmetic relations that survive overlap,
refinement and passage to the required test family.

The arithmetic endpoint is concrete. For the fixed cubic spline `B`, let

\[
  W_S=(W(B(\cdot-s),B(\cdot-t)))_{s,t\in S},
  \qquad S\subset\{\log n:n\ge1\}\text{ finite}.
\]

The corpus identifies the largest negative index of these matrices with the number of distinct
zeros right of the critical line. An upper bound of one on every such matrix already forces RH,
because right zeros occur in conjugate pairs. This is a receiver, not an available arithmetic
bound. The programme must construct and transport the bound without assuming it.

Namespace: `GaloisForLFunctions.ArithmeticIndexDescent`.
Umbrella: `ArithmeticIndexDescent.lean`.

## Motivation

Weil's curve argument joins a positive direction, a primitive negative form, correspondences and
an arithmetic count on one surface. Over the integers, the corpus supplies the complete
intersection form, exact correspondence identities, positive local sections and several
exhaustive spectral criteria. Their assembly remains substantive mathematics.

The spacing-scale theorem illustrates what an arithmetic assembly can achieve. The prime kernel
and archimedean cross kernel attain their worst behavior on different vectors. A tilted weight
compares them jointly and pays their interaction. The independent-section theorem retains enough
weighted reserve to pay the entire pole product. These proofs create positive spaces from the
actual source. Their shrinking supports do not establish positivity on a common exhaustive span.

Index descent asks which part of that success persists when spaces are joined. A positive lower
bound independent of aperture is unnecessarily strong and is obstructed by the known ground-energy
decay. A bounded negative index can survive without such a lower bound. Conversely, bounded rank
of a counterterm for the prime form alone is obstructed by its valuation-class divergence. The
quantity to control is the index of the completed form after all places are combined.

Scale refinement of arithmetic source work provides a second form of descent. The actual
zero-free height gap makes every reflected pair-work increase with its damping scale. A new
off-line zero in a doubled height annulus therefore forces a fixed increment of completed work.
This separates the cost of high defects from the accumulated contribution of low zeros and
opens a local target for arithmetic cancellation estimates.

Three distinctions organize the programme:

1. **Construction:** an arithmetic operation produces a reserve or an index bound.
2. **Identification:** the constructed form equals, or compares in the required direction with,
   the complete target form.
3. **Descent:** that comparison survives a specified transition or exhaustion.

A theorem about an abstract positive matrix addresses none of the arithmetic identifications by
itself. An RH-equivalent condition identifies the desired endpoint but does not construct it.

ACS now supplies a concrete source exhaustion: `CompleteWeilSourceTransfer` recovers the
full Weil form and every mixed entry of a finite compact C² family on one common logarithmic
cell system. Its step profiles retain the Gamma energy, prime interactions and both poles.
The open transfer problem is therefore specific: carry a proved arithmetic signature bound
to these complete cells, or directly to the exhaustive spline family. The positive thin-cell
carriers constructed here do not yet provide that bound.

The programme's complete-cell index-capture theorem makes this transfer exact in the needed
direction. For every finite smooth family `G`, one common cell system satisfies

\[
 \nu_-(W_G)\le\nu_-(C_{N,G})
 \quad\text{for every sufficiently large }N.
\]

Here `C_{N,G}` is the complexification of the actual polarized complete-cell source form.
Its mixed-entry convergence is proved from the arithmetic source. The theorem supplies an
exhaustive index receiver; the upper bound on these cell matrices still has to be produced.

## Objects and language

| Object | Required mathematical data |
|---|---|
| Arithmetic presentation | A finite test family and its linear map into the actual test space |
| Overlap Gram | The `L²` or completed energy Gram of that family; it can have a kernel |
| Completed Weil Gram | Prime-lag entries, archimedean entries, diagonal normalization and both pole rows |
| Index | Hermitian negative index of a Weil Gram; distinguished from positive index of the intersection form |
| Reserve | A nonnegative quadratic contribution proved from the source, with its domain and constants |
| Polar anchor | A positive direction, its polar row and its primitive hyperplane |
| Gluing defect | Mixed entries and polar dispersion introduced by assembling presentations |
| Transition | A linear map, an exact pullback identity or comparison, and its quantified remainder |
| Charged incidence | Successor, cell or non-ratio relations with their transformation under prime gauges |
| Renormalization | Regulator, divergent form, finite part, survival space and correspondence anomaly |
| Exhaustion | Approximation of every required finite test family controlling all mixed form entries |
| Source work | A damped arithmetic reading of transverse energy, with multiplicities and exterior rows retained |
| Scale increment | `W(S)-W(R)`, with a nonnegative reflected-pair decomposition and a quantified annular defect cost |

An *index budget* bounds negative directions, not their amplitudes. A *payment* is a proved
inequality absorbing an adverse interaction in a source reserve. *Descent* transports the specified
form rather than replacing it by a corrected form. A family is *exhaustive* only through a proved
testing or approximation theorem. *Computed*, *bounded*, *selected* and *excluded* describe
different achievements.

On an overlapping family, coefficient norm and test norm differ. If the overlap Gram is singular,
the presentation has relations. These relations must be quotiented or retained explicitly;
inverting the Gram without addressing its kernel changes the problem.

## Mechanisms

### Full-form refinement

The source reserve can be kept quantitative before refinement. For independent profiles `G_n`, put

\[
 M(G)=\int\Bigl|\sum_{1\le n\le N}G_n(u-\log n)\Bigr|^2du,\qquad
 Q_N(G)=\sum_{1\le n\le N}\left(1+\frac nN(1+\log N)\right)\int|G_n|^2.
\]

The existing Markov estimate retains `Q_N/8` beyond square mass. The programme keeps the pole
payment at its actual value `c(N,w)=wN(exp(w)+1)`, giving the full-source inequality

\[
 W(f,f)\ge M(G)+\bigl(\tfrac18-c(N,w)\bigr)Q_N(G).
\]

If the width is at most fraction `a` of the full allowed section width, with `0<a<=1`, then
`c(N,w)<=a/8`. Hence

\[
 W(f,f)\ge M(G)+\frac{1-a}{8}Q_N(G).
\]

At half width, `Q_N/16` remains after both pole moments are paid. The unrounded pole cost gives
a further improvement even at the original full width. Put `r=fullSectionRatio`. The allowed
geometry gives `wN<=r` and `w<=r`, hence

\[
 c(N,w)\le r(e^r+1)<\tfrac18,\qquad
 \rho=\tfrac18-r(e^r+1)>0.
\]

The strict inequality uses `r<1` and the existing bound `r(e+1)<=1/8`. Therefore the whole
original section space retains

\[
 W(f,f)\ge M(G)+\rho Q_N(G)\ge(1+\rho)M(G).
\]

This reserve requires no further reduction of the section width. The fraction-dependent
estimate remains useful at smaller widths, where it can supply a larger reserve.

For a Hermitian extension

\[
  G=\begin{pmatrix}A&B\\B^*&C\end{pmatrix},
\]

the Schur complement `C-B* A⁻¹B` records the new negative directions when `A` is positive definite.
The difficult arithmetic expression is the whole complement. Separate absolute bounds on its
three ingredients can erase the compensation. Singular positive blocks require a range condition
or an explicit treatment of their radical; a formal inverse is insufficient.

For finite families in a narrow arithmetic section space, the programme proves the range
condition from the source. If `S` synthesizes the actual test and `A` is its Weil Gram, then

\[
  \ker A=\ker S.
\]

Indeed, a Gram null vector has zero Weil square, and the arithmetic floor `W >= L²` forces its
actual test to vanish. Its mixed pairing with every ambient real test therefore vanishes.
Consequently every such mixed block has the form `B=A X`, even for redundant old families.
Different coefficient lifts of the same column synthesize the same actual section. The singular
range condition is discharged here; the sign of the new Schur complement remains an arithmetic
question.

The synthesized lift defines an actual projection `P_F g` onto the finite old section span.
It is unique, linear and idempotent, even when its coefficients are nonunique. The completed
pairing satisfies

\[
 W(g-P_Fg,h-P_Fh)=W(g,h)-W(P_Fg,P_Fh).
\]

For every old section combination `q`, its variational property retains an actual square-mass gap:

\[
 W(g-P_Fg,g-P_Fg)+\|P_Fg-q\|_{L^2}^2\le W(g-q,g-q).
\]

The removed energy is nonnegative. Consequently a negative witness survives this removal; descent
isolates the signed obstruction in a smaller space. It does not by itself pay that obstruction.

At the matrix level, `B=A X` gives an exact triangular congruence with diagonal blocks
`A` and `C-X* A X`, without an inverse of `A`. Positive, negative and null indices all add.
The complement is independent of the chosen lift `X`, so presentation relations do not create
an arbitrary choice in the refinement law.

This identity is realized in the literal completed Weil Gram. For an old narrow section family
`F` and arbitrary real probe family `G`, write `G-P_FG` for the family of actual residual tests.
Then

\[
 \nu_-\bigl(W_{(F,G)}\bigr)=\nu_-\bigl(W_{G-P_FG}\bigr).
\]

Complex coefficients are retained through real/imaginary splitting. Every negative square of
the extension belongs to its actual residual Gram; none is an artifact of an old presentation
relation. The remaining arithmetic task is to control this residual's sign or index.

### Local source duality

For a fixed compact real `C²` probe `g`, reflect it by `gᵛ(u)=g(-u)` and set

\[
 K_g(u)=\mathcal W(\tau_u g^\vee),\qquad
 W(p,g)=\operatorname{Re}\int p(u)K_g(u)\,du.
\]

Here `𝒲` is the complete arithmetic functional: two pole readings, the prime comb and the
Gamma integral. The corpus's averaging identity gives this representation. Its translation
continuity lemmas, together with absolute Gamma integrability for compact `C²` probes, make
`K_g` continuous. Hence every fixed window has a finite constant `C(g,R)` with

\[
 |W(p,g)|\le C(g,R)\int |p(u)|\,du,
 \qquad \operatorname{supp}p\subset[-R,R].
\]

The estimate is independent of the varying test's derivatives and coefficient presentation.
Its role is to control mixed readings of a fixed probe. Growth of the constant with the window
remains part of the arithmetic problem.

The exact support cells give a sharper source bound. Set

\[
 U_{N,w}=\bigcup_{1\le n\le N}[\log n,\log n+w],\qquad
 D_U(g)=\int_U |K_g(u)|^2\,du.
\]

Every old section vanishes outside this compact union, including the gaps between cells.
The exact source representation and Cauchy–Schwarz imply

\[
 |W(p,g)|^2\le\|p\|_2^2 D_U(g).
\]

For the actual projection, `W(p,g)=W(p,p)` and `W(p,p)>=||p||_2^2`. Hence

\[
 W(P_Fg,P_Fg)\le D_U(g),\qquad
 D_V(g)\le D_U(g),\qquad
 W(g,g)-D_U(g)\le R_V(g,g).
\]

Here `D_V` is the completed removal energy defined below, and `R_V` is the completed residual.
The estimates hold for every finite old presentation and the entire completed profile space.
The full prime, Gamma and pole contributions are combined inside `K_g` before squaring; their
cancellation is retained. Using the actual cell union preserves gaps that an enclosing interval
would erase. The estimate supplies a concrete Schur cost; positivity still requires the actual
new diagonal to pay it.

The retained arithmetic reserve improves this dual estimate. At width fraction `a<=1`, set

\[
 A_n=1+\frac{1-a}{8}\left(1+\frac nN(1+\log N)\right),\qquad
 D_a(g)=\sum_{1\le n\le N}\frac{1}{A_n}
       \int_{\log n}^{\log n+w}|K_g(u)|^2\,du.
\]

The full source floor is `W(p,p)>=sum A_n M_n`. Applied separately on each cell,
Cauchy–Schwarz and Young give `2W(p,g)<=sum A_n M_n+D_a(g)`.
For `p=P_Fg`, the exact projection identity therefore yields

\[
 W(P_Fg,P_Fg)\le D_a(g),\qquad D_V(g)\le D_a(g),\qquad
 W(g,g)-D_a(g)\le R_V(g,g).
\]

The cells are disjoint, so `D_a(g)<=D_U(g)`. At `a=1` the costs coincide.
The improvement retains the cell-dependent arithmetic weights and the complete source kernel;
it does not split that kernel into absolute estimates for separate places.

The strict full-width mass floor independently gives
`D_V(g)<=D_U(g)/(1+rho)` on the original allowed spaces. Thus even the full-width projection
has a smaller cost than the first square-mass bound, without changing its source carrier.

For narrow arithmetic sections, this already yields an upper estimate uniform over all finite
presentations. Put `L=log N+w` and `p=P_F g`. Orthogonality gives `W(p,g)=W(p,p)=E`, while
the source floor and support Cauchy–Schwarz give

\[
 \|p\|_2^2\le E,\qquad
 E\le C(g,L)\|p\|_1,\qquad
 \|p\|_1^2\le2L\|p\|_2^2.
\]

Therefore

\[
 0\le W(P_Fg,P_Fg)\le 2L\,C(g,L)^2
\]

for every finite family `F` in the same narrow section space. Dimension, redundancy and profile
derivatives do not enter the bound. This controls the intrinsic Schur cost even when coefficient
Grams become ill-conditioned. The estimate is local in `(N,w)`; its growth under an arithmetic
exhaustion still requires a sharper source argument.

### Control in the actual source graph

The complete CHMD source graph already exists in the corpus. For a literal compact real C²
test `f`, use its inverse Doob lift `Jf`. The programme identifies

\[
 \mathsf W_{\rm graph}(Jf)=W(f,f),\qquad
 \|\operatorname{source}(Jf)\|^2
   =\int f(u)^2\frac{\cosh(u/2)}{\Phi(u)}\,du,
\]

where `Phi` is the actual positive theta kernel. On a fixed window `[-R,R]`, its continuous
positive weight has a finite maximum. The graph norm identity and Cauchy–Schwarz on the
global polar directions therefore give a source-derived constant `C_R>0` with

\[
 \|Jf\|_{\rm graph}^2\le W(f,f)+C_R\|f\|_2^2.
\]

This does not assume a sign for `W(f,f)`. On an actual narrow arithmetic section, the proved
floor absorbs the mass remainder:

\[
 \|Jp\|_{\rm graph}^2\le(1+C_R)W(p,p).
\]

The bound holds for every independently profiled section and every difference of sections.
It provides the norm control needed for literal completion in the original source graph,
rather than only in square mass. Its constant depends on the fixed window and can grow
sharply with aperture; no uniform growing-window estimate is asserted.

### Completion of the source space

Fix `(N,w)` and direct the finite subsets `F` of the entire narrow section space by inclusion.
The projection energies

\[
 E_F(g)=W(P_Fg,P_Fg)
\]

increase and are bounded above by the local source estimate. If `F` is contained in `H`, then

\[
 W(P_Hg-P_Fg,P_Hg-P_Fg)=E_H(g)-E_F(g),\qquad
 \|P_Hg-P_Fg\|_2^2\le E_H(g)-E_F(g).
\]

The graph-norm estimate upgrades these increments to a Cauchy net in the original complete
source graph. Consequently there is an actual vector

\[
 P_Vg=\lim_F J(P_Fg)\in\overline{J(V)}.
\]

The closed old carrier retains the same graph coercivity. Continuity of the original Weil
pairing identifies its diagonal and all mixed entries:

\[
 \mathsf W(P_Vg,P_Vh)=B_V(g,h),\qquad
 \mathsf W(Jg-P_Vg,Jh-P_Vh)=R_V(g,h).
\]

Moreover `Jg-P_Vg` is Weil-orthogonal to the entire closed carrier `closure(J(V))`.
The limit is a vector of the existing source graph; no smoothness of that vector is asserted.

The same arithmetic coercivity constructs a bounded linear projection on the entire source
graph. If `K=closure(J(V))`, `T` is the bounded operator of the original Weil form and `Pi_K`
is the ordinary graph-orthogonal projection onto `K`, then

\[
 P_K=\iota_K(\Pi_KT\iota_K)^{-1}\Pi_KT.
\]

The compressed operator is invertible by the proved source floor and the inherited Hilbert
coercive-inverse theorem. This projection fixes `K`, is idempotent and is uniquely characterized
by `x-P_Kx` being Weil-orthogonal to `K`. For every graph vector pair,

\[
 \mathsf W(x-P_Kx,y-P_Ky)=\mathsf W(x,y)-\mathsf W(P_Kx,P_Ky).
\]

On literal tests, `P_K(Jg)=P_Vg`. Thus the finite-section limit and the bounded graph projection
give the same source removal, while the complementary form retains its sign problem.

Let `D_V(g)=sup_F E_F(g)`. Polarization along this same net gives a symmetric positive semidefinite
bilinear form

\[
 B_V(g,h)=\tfrac14\bigl(D_V(g+h)-D_V(g-h)\bigr),\qquad
 R_V(g,h)=W(g,h)-B_V(g,h).
\]

Every actual section is reproduced once its singleton occurs in the finite family. Consequently
`R_V` annihilates the whole old section space on both sides. The resulting source-defined
residual form has every mixed finite Gram entry obtained as a limit of the
original completed pairing. Each negative square of a finite limiting residual Gram already
occurs at all sufficiently large finite refinements.

The index statement is exact. Since the completed removal dominates each finite removal,
`R_V(g,g)<=W(g-P_Fg,g-P_Fg)` for every `F` and `g`. Real/imaginary splitting carries this
quadratic order to the complex Gram matrices. Thus no finite residual has more negative squares
than the completed residual. Combined with finite detection, this proves

\[
 \nu_-(R_V|_G)=\nu_-(W_{G-P_FG})
 \quad\text{for every sufficiently large finite }F,
\]

for each fixed finite probe family `G`. In particular, its completed index is exactly realized
by an actual smooth Weil Gram. Completion introduces no unattainable finite negative index.

This completes the fixed positive source space without a coefficient norm or a uniform matrix
eigenvalue gap. The residual remains signed, and `R_V(g,g) <= W(g,g)`. A bound uniform under
growing windows, or an arithmetic sign estimate on this residual, is a further theorem to prove.

Shrinking a fixed arithmetic pattern has a precise limit. The cells occupy at most `Nw` of
Lebesgue measure. For `0<=w<=1`, their source kernel is bounded on the common interval
`[0,log N+1]`. Consequently, for each fixed `N` and probe `g`, a finite constant `B(N,g)` satisfies

\[
 0\le D_V(g)\le D_{U_{N,w}}(g)\le B(N,g)w.
\]

Thus the energy removed by the entire positive profile space tends to zero as `w` tends to zero,
and `R_V(g,g)` returns to `W(g,g)`. This is uniform over all finite families and all old profile
shapes. Narrowing a fixed pattern can improve its internal positivity while reducing its action
on a fixed ambient probe. The theorem leaves growing and translated arithmetic patterns open;
their source constants and form approximation require separate estimates.

### Separated mixed sources

The archimedean interaction has a direct source bound over arbitrary signed profiles.
If `d>0` and `d<|u-v|` whenever `f(u)` and `g(v)` are nonzero, set

\[
 J(d)=\int_d^\infty\frac{e^{-x/2}}{1-e^{-2x}}\,dx.
\]

The mixed spectral Gamma term satisfies

\[
 \left|\frac1{2\pi}\int
   \operatorname{Re}(\widehat f(r)\overline{\widehat g(r)})A(r)\,dr\right|
 \le J(d)\bigl(\|f\|_2^2+\|g\|_2^2\bigr).
\]

Polarization of the scalar Lévy identity identifies the left side with the absolute value
of the signed collar. Every jump of length at most `d` vanishes. The two remaining oriented
correlations are paid by the two square masses, and the actual Lévy tail is integrable.
The bound is uniform over profile derivatives and presentation dimension.

The same support window `[-R,R]` gives a uniform finite prime horizon: any integer
`N>exp(2R)` cuts off every shifted mixed correlation. Cauchy–Schwarz bounds each surviving
correlation, while both squared pole moments are bounded by `2R exp(R)` times square mass.
Combining these estimates with the signed Gamma collar gives an actual constant

\[
 C=2Re^R+\sum_{2\le n<N}\frac{\Lambda(n)}{\sqrt n}+J(d),\qquad
 |W(f,g)|\le C\bigl(\|f\|_2^2+\|g\|_2^2\bigr).
\]

Rescaling only the first profile then allocates any chosen positive charge `epsilon` to it:

\[
 2|W(f,g)|\le \varepsilon\|f\|_2^2+
       \frac{4(C+1)^2}{\varepsilon}\|g\|_2^2.
\]

Every term here belongs to the complete source. The estimate is uniform over both profile
spaces; the gap and common window determine its constant. It supplies an extension payment
without an assumed mixed-block bound. The reciprocal new-mass charge must still be paid by
the new diagonal.

The inherited one-site section estimate pays the new charge quantitatively. For a profile
supported on `[0,w]`, with `w` below the spacing allowance and one,

\[
 W(g,g)\ge
 \bigl(2\theta'(0)+\log(1/w)-C_{\rm spacing}-(e+1)\bigr)\|g\|_2^2.
\]

Consequently every fixed charge `L` has a positive width threshold below which all profiles
satisfy `W(g,g)>=L||g||_2^2`. Translation preserves both the full Weil diagonal and square
mass, so the same threshold works at every centre. This is an explicit consequence of the
existing arithmetic single-cell estimate, with both pole moments retained.

These two source estimates produce an exact extension law. Fix a bounded old support with
positive distance from a new centre, a loss `epsilon>0`, and a new charge `L`. A positive
new-width threshold ensures, uniformly over all old and new profiles,

\[
 W(p+g,p+g)\ge W(p,p)-\varepsilon\|p\|_2^2+L\|g\|_2^2.
\]

The old diagonal is retained literally; no sign of it is assumed. This form of the estimate
permits successive extensions with separately tracked reserve losses. Disjoint profiles have
exactly additive square mass, so the charge is measured in the actual synthesized test norm.

For the actual narrow arithmetic space `V(N,w)`, the old source floor is already proved.
Every centre outside its compact cell union has a positive geometric gap. Hence a constructed
new cell gives

\[
 W(p+g,p+g)\ge(1-\varepsilon)\|p\|_2^2+\|g\|_2^2
 \quad(p\in V(N,w)),
\]

uniformly over the entire old infinite profile space and every new compact C² profile in that
cell. All old widths remain fixed. Taking `epsilon=1/2` retains half the old mass and all new
mass. The new width, rather than a premise about the mixed form, pays the interaction.

The extension can be iterated without changing any previous width. For every strictly
increasing sequence of real centres `b_n`, there is one sequence `0<w_n<=1` such that, for
all finite prefixes and all independently chosen real compact C² profiles,

\[
 \operatorname{supp}G_n\subset[b_n-w_n/2,b_n+w_n/2]
 \quad\Longrightarrow\quad
 W\!\left(\sum_{n<N}G_n,\sum_{n<N}G_n\right)
 \ge\left\|\sum_{n<N}G_n\right\|_2^2.
\]

The arithmetic specialization is `b_n=log(n+1)`. A zero new profile embeds each prefix into
the next, so these are nested positive spaces with fixed old widths.

The construction first chooses canonical envelope widths
`e_n=min(1,(b_(n+1)-b_n)/2)`. The next centre lies outside the compact union of all earlier
envelopes. This supplies its mixed-source window and gap before any actual widths are chosen.
Choose the actual new width below its envelope, gap and source threshold. The reserve
`a_N=1+1/(N+1)` pays loss `a_n-a_(n+1)>0` at step `n`; the new diagonal pays `a_(n+1)`.
Exact disjoint mass addition then proves the stronger prefix floor `a_N` throughout the induction.

These widths need not be comparable to the arithmetic spacing. The result uses local coercivity
and a finite mixed-source payment, and also holds for nonarithmetic increasing centres. It
therefore establishes stable assembly on a restricted domain; it does not supply the critical
arithmetic cancellation needed for larger overlapping cells or fixed-spline exhaustion.

The corpus also supplies stronger control at a sharp boundary. Its actual Gamma boundary
operator has `L²` norm at most `2π`, and sharp interval restrictions are uniformly bounded
on the complete arithmetic graph and land in the exact aperture completion. The growth of
the elementary constant `J(d)` as the gap closes is therefore not an intrinsic Gamma
obstruction. These tools make cumulative signed assembly cost the central issue in a
cell-based exhaustion; domain admission of each sharp cut is already available.

### Polar compatibility

For symmetric `Q_i` with a common anchor `e` and `a_i=Q_i[e]>0`, put

\[
 R_i(x)=\frac{Q_i(e,x)^2}{a_i}-Q_i[x],\qquad
 V_e(x)=\sum_i a_i\left(\frac{Q_i(e,x)}{a_i}
       -\frac{\sum_jQ_j(e,x)}{\sum_j a_j}\right)^2.
\]

The existing gluing identity is

\[
 R_{\sum_iQ_i}(x)=\sum_iR_i(x)-V_e(x).
\]

Local reserves therefore have a precise compatibility cost. Subtracting the dispersion matrix
constructs a hyperbolic form from appropriate local forms, but the result is a different form.
An arithmetic application must identify that correction inside the completed pairing or pay it
there. The two global pole moments cannot be independently allocated to every local piece.

### Charged overlap

For a completely multiplicative sign gauge, the prime-lag discrepancy contains

\[
 \omega(k)-\omega(m)\omega(n).
\]

It vanishes when `n=km` or `m=kn`. Non-ratio near-incidences and successor cells retain information
that exact multiplicative ratios forget. Their presence does not determine their sign. The target
is a quantitative estimate using that information at the actual arithmetic source.

The diamagnetic inequality remains a constraint: on a family closed under absolute value,
Markov lower bounds transfer to dominated twists. A selective argument must specify how its signed
domain, poles or charged relations enter the full estimate.

### Finite-Gram limits

The limiting object needed for the spline criterion is each fixed finite Gram. An exhaustion must
approximate its diagonal and mixed entries simultaneously. An index bound should be transported
through this convergence without requiring a uniform positive gap. A family of positive finite
pieces does not provide that convergence or control its cross terms automatically.

The finite-Gram transfer tool combines existing negative-subspace persistence and rectangular
pullback monotonicity. If `C_t A_t C_t*` converges entrywise to a fixed finite `H`, then eventually
`nu_-(H) <= nu_-(A_t)`, even when the source dimension varies and coefficient maps are singular.
This isolates the source task: construct the approximants and prove their full mixed convergence.

### Rigidity of equality

Incommensurable Gabor Pinching retains off-diagonal Gram slack and proves that the old scalar
extremizer cannot occur at the available density. Index descent seeks analogous source constraints
on equality or near equality in mixed-form estimates. Larger blocks and several windows must share
their normalization and tail estimates; separately obtained gains cannot be added without a joint
identity.

### Index and work

Negative index counts spectral defects, while transverse energy assigns a quantum to every
off-line reflection pair. For every finite family of compactly supported `C²` tests, the programme
proves

\[
  \nu_-(W_f)\le \mathcal E_{\mathrm{distinct}}
       \le \mathcal E_{\mathrm{copies}}.
\]

The first inequality doubles a finite right-hand packet by critical-line reflection, then applies
the angular quantum to every member. The second selects one analytic-multiplicity copy of each
distinct zero. Both inequalities allow infinite total energy. The arithmetic intersection Gram
has at most `1 + E_distinct` positive squares; its extra square belongs to the pole plane.

Existing source-work exhaustion now has a quantitative index consequence. Every positive finite
negative-index witness is eventually exceeded, including its whole integer value, by rationally
damped arithmetic source work, and then by finite tapered source work at each sufficiently large
damping scale.
The order of the two limits matters. Exterior rows, analytic multiplicities, the Laurent source
and its archimedean completion remain present.

The distinct-energy inequality is strict whenever the index is positive. Besides the horizontal
partner, every off-line zero has the different reflected neighbour `1-rho`. Writing
`rho = beta + i gamma`, the latter contributes the additional angle

\[
  \frac{(2\beta-1)^2}{(2\beta-1)^2+(2\gamma)^2}>0.
\]

Xi has no real zeros, so these two neighbours are distinct. Each nonempty right packet costs
strictly more than its cardinality. Conjugation gives two right zeros whenever one exists, hence

\[
  \mathrm{RH}\quad\Longleftrightarrow\quad\mathcal E_{\mathrm{distinct}}\le2.
\]

This is the global half-ordered-pair energy, distinct from the existing unhalved unit-window
criterion. The same closed threshold holds for copied energy. It also gives an exact arithmetic
target: RH holds if and only if, for every integer `M`, some `n >= M` has damped source work at
scale `n+4` at most two. The work itself vanishes under RH. No bound of two is proved here.
No uniform extra margin above an integer index is asserted: the displayed angle can approach zero.

These are lower bounds on the work forced by defects. An arithmetic upper estimate must still be
constructed. A global finite work bound and a bound below an exclusion quantum are different
research targets.

The finiteness boundary is exact. Multiplicity-weighted transverse energy is finite if and only if
the off-line support is finite. Equivalently, damped source work is eventually bounded. With
infinitely many off-line zeros, that work tends to infinity in the extended nonnegative reals.
A uniform finite bound on the fixed-spline integer-log negative indices describes this same
finite stratum. Thus index and work agree on finiteness, while a generic finite budget supplies
no exclusion of the remaining defects.
The proof retains the infinitely many critical zeros: they interact only with the finitely many
off-line rows, and each such row is bounded by a summable Cauchy height weight.

### Scale increments and quantized escape

Write

\[
 h_R(t)=\frac{R^4}{(R^2+t^2)^2},\qquad
 W(R)=\frac14\sum_{p,q}\operatorname{reflectedWork}_{p,q}(h_R),\qquad
 \Delta W(R)=W(2R)-W(R).
\]

Here `p,q` range over all analytic-multiplicity copies of the actual Xi divisor, and `W` is
the limit of the completed arithmetic Laurent-source work with compact height tapers.
The unconditional gap `|Im ρ| ≥ 4` supplies more than separation from the real axis. For

\[
 v_R(t)=\frac{t^2}{(R^2+t^2)^3},\qquad \partial_R h_R(t)=4R^3v_R(t),
\]

it gives

\[
 2|v_R(t)-v_R(u)|\le |t-u|\bigl(v_R(t)+v_R(u)\bigr).
\]

The near-collision and far-field estimates from Arithmetic Electrostatics absorb the derivative's
mixed term. Each actual reflected pair-work is consequently monotone for `R ≥ 0`, and absolute
summability makes the completed work monotone for `R ≥ 4`. This is stronger than positivity of
work at each separate scale: it permits subtraction without losing control of the other pairs.

For any finite packet `P` of right-hand zero copies and `4 ≤ R ≤ S`, its disjoint reflection
quartets give the exact weighted payment

\[
 \sum_{p\in P}\bigl(h_S(\gamma_p)-h_R(\gamma_p)\bigr)\le W(S)-W(R).
\]

Every quartet retains all four ordered pairs, including the diagonal entries of the reflected
kernel. If `R ≤ |γ_p| ≤ 2R` throughout the packet, this yields

\[
 \boxed{\quad \frac{21}{100}|P|\le\Delta W(R).\quad}
\]

The coefficient `21/100` is the sharp scalar damping minimum on that annulus, attained at
`|γ|=2R`; optimality for the full arithmetic work is not asserted. Multiplicities are counted
separately. The same lower payment, with any positive tolerance, eventually holds for the
difference of the two finite tapered arithmetic source works, with exterior rows still present.

Local finiteness of the divisor now gives an unconditional escape alternative: either off-line
support is finite, or arbitrarily large scales satisfy `ΔW(R) ≥ 21/100`. In particular, a proved
arithmetic estimate making these increments eventually smaller than that quantum would exclude
all sufficiently high off-line zeros. Establishing such an upper estimate remains open; neither
monotonicity nor the lower payment supplies it.

The full conjugate and reflection packet strengthens this payment. For one off-line zero
\(\rho=\beta+i\gamma\), put

\[
 a_\rho=\frac{(2\beta-1)^2}{(2\beta-1)^2+(2\gamma)^2}>0.
\]

The four distinct zero copies have equal absolute height. Their sixteen ordered interactions
give, for \(4\le R\le S\),

\[
 2\bigl(h_S(\gamma)-h_R(\gamma)\bigr)(1+a_\rho)\le W(S)-W(R).
\]

Their unequal-weight mixed terms vanish exactly. Every remaining pair has a nonnegative
increment, so the estimate retains the full exterior field. At the zero's own height,

\[
 h_{2|\gamma|}(\gamma)-h_{|\gamma|}(\gamma)=\frac{39}{100},
 \qquad \Delta W(|\gamma|)>\frac{39}{50}.
\]

Thus control at the closed threshold \(39/50\) has two distinct strengths: eventual control
at every sufficiently large real scale is equivalent to finite off-line support; control
at every scale \(R\ge4\) is equivalent to RH. The strict surplus makes the thresholds closed,
but it has no asserted uniform positive margin. Optimality for the full source is not claimed.

The scale classification is exact over all real scales. Monotonicity and the existing cofinal
source limit give `W(R)<=E_copies` for every `R>=4`. If the off-line support is finite,

\[
 W(R)\longrightarrow \mathcal E_{\mathrm{copies}}<\infty
 \quad(R\to\infty).
\]

Consequently the following conditions are equivalent:

\[
 \text{finite off-line support}
 \quad\Longleftrightarrow\quad
 \Delta W(R)\longrightarrow0
 \quad\Longleftrightarrow\quad
 \Delta W(R)<\tfrac{21}{100}\ \text{eventually for every real scale}.
\]

The converse uses the fixed annular quantum, so arbitrarily sparse escape cannot evade it.
This is stronger than the implication supplied by monotonicity for a general increasing
function: here the arithmetic divisor's local finiteness and reflected work enforce a gap.
The eventual quantifier is essential. A bound along a selected unbounded subsequence is
not supplied as an equivalent condition. Finite exceptions remain compatible with the
vanishing-increment condition; their exclusion requires a further estimate.

## Questions the programme aims to answer

1. Which arithmetic operation joins positive sections while paying their mixed Schur or polar
   defect in the original form?
2. Can a stable negative-index budget survive repeated signed overlap and reach the fixed-spline
   integer-log family?
3. Which non-ratio incidence or successor relation produces a form margin at the Euler point,
   rather than only selecting that point algebraically?
4. Which norms control refinement errors in the presence of cancellation and a singular overlap
   Gram?
5. How can the fixed-class horizon finite parts be extended to growing arithmetic presentations
   without replacing signed energy by absolute coefficient mass?
6. Which arithmetic constraints force strict Gram inequalities beyond the presently retained
   disjoint-pair slack?
7. Can the actual same-profile signed prime surplus at bandwidth `4/3` be bounded by `1/18` of
   the zero count, giving the `3/4` simple-critical target?
8. Which arithmetic source estimate bounds global off-line index, and which quantum bound or paid
   propagation eliminates the finite remainder?
   Can cancellation in the scale difference `W(2R)-W(R)` instead prove eventual work below the
   annular quantum, or convergence of that difference to zero?
9. Can terminal geometry support a boundary-to-interior estimate for the regularized arithmetic
   field with its singularities and archimedean background accounted for?
10. Which construction recovers the curve case from actual arithmetic sections or incidence, with
    bounded genus cost, and rejects the corresponding fake data for a proved reason?

The RH-strength questions remain open until their arithmetic estimates are proved. The list is
not discharged by defining interfaces whose fields assume those estimates.

## Foundational pillars and ownership

The starting pillars belong to existing programmes and are reused rather than copied.

| Pillar | Existing result | Owner |
|---|---|---|
| Source-defined positive spaces | Full Weil form dominates square mass on sufficiently narrow independent arithmetic sections | ArithmeticCastelnuovoSeveri |
| Joint local payment | Constant-one self-energy and tilted prime rows reach a fixed fraction of the spacing | SpacingScaleHarmonicAnalysis |
| Exact gluing price | Reserve of a sum equals sum of reserves minus polar dispersion | ArithmeticLorentzianGeometry |
| Exhaustive index receiver | Fixed-spline orbit index counts distinct right zeros; index at most one forces RH | ArithmeticOrientationGeometry; SpacingScaleHarmonicAnalysis |
| Complete-cell source exhaustion | One common logarithmic cell system recovers every diagonal and mixed full Weil entry of any finite compact C² family | ArithmeticCastelnuovoSeveri, `CompleteWeilSourceTransfer` |
| Matrix inertia and aperture reduction | Hermitian congruence, block Schur identities, finite-rank boundary formulas and an exact finite Schur reduction of the actual completed aperture form | HTGeometry; RHTower.CCM |
| Sharp source localization | The actual Gamma boundary operator is bounded on `L²`; sharp intervals have uniform full-graph bounds and belong to the exact aperture completion | HTGeometry; RHTower.CCM; CHMD |
| Renormalization domains | Survival equals the counterterm nullspace; coupled survival is constrained by partner rank | RenormalizedBiarithmeticGeometry; RenormalizedArithmeticPotentialTheory |
| Charged arithmetic | Gauge defects on non-ratio lags; successor and cell gauge laws | SpacingScaleHarmonicAnalysis; BiarithmeticGaugeGeometry; RenormalizedBiarithmeticGeometry |
| Signed averaged receiver | One-profile trans-threshold surplus certificates | TransThresholdPairCorrelation |
| Strict Gram slack | Non-lattice kernel geometry produces an unconditional zero-proportion gain | IncommensurableGaborPinching |
| Quantized defect | Window energy below two excludes off-line zeros; damped source work exhausts global energy | ArithmeticElectrostatics |

The programme's own pillars must add a source estimate, a stronger exact transfer, a quantitative
comparison of these invariants, or a construction not already supplied by this table. Abstract
matrix tools should be used to isolate the arithmetic input, not presented as its solution.

Quantitative pillars supplied by this programme:

| Pillar | Mathematical content | Module |
|---|---|---|
| Index is paid by energy | Every finite smooth Weil negative index is at most distinct transverse energy; intersection positive index is at most one plus that energy | `TheIndexIsPaidByTransverseEnergy` |
| Source work detects finite index witnesses | Distinct energy embeds in copied energy; damping and taper limits detect every amount below a finite negative index | `TheArithmeticSourcePaysTheIndex` |
| Exact finiteness boundary | Copied energy is finite iff off-line support is finite, iff damped source work is eventually bounded | `BoundedSourceWork` |
| Positive scale refinement | The actual zero-free height gap controls derivative weights, making every reflected pair-work monotone; the doubled annulus has sharp scalar damping quantum `21/100` | `DampingIncrementPositivity` |
| Annular arithmetic payment | Full source-work increments pay right-zero packets with multiplicity; finite source cutoffs retain the payment; infinite off-line support forces arbitrarily high quantum increments | `SourceWorkIncrementsPayForNewZeros` |
| Exact scale-increment stratum | Work at every real scale is at most copied energy; finite support gives its real limit and is equivalent to vanishing doubled increments or eventual increments below 21/100 | `VanishingScaleIncrementsCharacterizeFiniteSupport` |
| Full quartet scale quantum | Sixteen actual ordered pairs pay twice the damping increment times one plus a positive diagonal angle; eventual closed bound 39/50 means finite exceptions, while every-scale control is equivalent to RH | `EveryOffLineQuartetCostsAStrictScaleQuantum` |
| Strict energy surplus | Every positive finite index lies strictly below distinct energy; the closed global threshold two is equivalent to RH | `TheEnergyStrictlyExceedsTheIndex` |
| Closed source-work threshold | RH iff cofinally damped source work is at most two; every positive finite index is eventually exceeded by finite source work | `TheSourceWorkHasAClosedQuantumThreshold` |
| Common finite stratum | Fixed-spline integer-log indices are uniformly bounded iff damped source work is eventually bounded | `TheWorkAndIndexHaveTheSameFiniteStratum` |
| Arithmetic range compatibility | A narrow section Gram has exactly the synthesis kernel; every ambient mixed block lies in its range, with coefficient lifts unique as actual tests | `ArithmeticSectionsHaveOnlyPresentationRadicals` |
| Actual section projection | Unique linear idempotent projection despite coefficient relations; exact residual pairing and a variational gap measured by actual square mass | `ArithmeticSectionProjection` |
| Singular refinement | Range-compatible mixed blocks admit exact positive, negative and null index splitting; the complement is independent of its lift | `SingularRefinement` |
| Exact actual-form descent | The literal Weil Gram of old narrow sections plus arbitrary real probes has exactly the negative index of the actual projected residual Gram | `TheSectionComplementCarriesAllNegativeSquares` |
| Local source duality | Each fixed compact C² probe gives a continuous complete source kernel; on every fixed window the mixed Weil reading is bounded by absolute test mass | `TheSourceKernelIsLocallyBounded` |
| Uniform intrinsic projection cost | On fixed `(N,w)`, the energy of every finite section projection of a fixed probe is bounded independently of presentation dimension and conditioning | `TheProjectionCostIsBoundedOnEachWindow` |
| Growing-presentation transfer | A fixed finite limiting negative index survives in sufficiently late source presentations, without a coefficient bound or uniform positive gap | `FiniteGramDescent` |
| Canonical source completion | Bounded monotone projection energies give an actual square-mass Cauchy net, a bilinear residual annihilating the entire old source space, and convergence of every mixed finite residual Gram | `TheSectionProjectionHasACanonicalLimit` |
| Completed index retains its arithmetic cost | Every finite index of the completed residual is witnessed by actual smooth Weil tests; positive index remains strictly below transverse energy and is eventually exceeded by finite source work | `TheCompletedSourceComplementIsPaidByWork` |
| Source energy pays the Schur cost | Kernel square energy on the exact old logarithmic cells bounds finite and completed removal and gives an explicit lower bound on the signed residual | `TheSourceKernelEnergyBoundsTheSchurCost` |
| Fixed-pattern shrinking boundary | Completed removal is `O(w)` at fixed `N`, uniformly over every old profile family; the signed residual returns to the original form on each fixed diagonal | `ShrinkingCellsRemoveVanishingEnergy` |
| Unused width retains reserve | Keeping the actual pole charge proves that width fraction `a` leaves `(1-a)/8` of the weighted arithmetic profile reserve beyond square mass | `ThePolePaymentRetainsTheUnusedWidthReserve` |
| Exact finite attainment | Every finite residual index is at most the completed index; for each fixed probe family equality holds at all sufficiently large finite source stages | `TheCompletedIndexIsReachedAtAFiniteStage` |
| Separated Gamma payment | The exact signed Gamma cross term is bounded by the actual Lévy tail times the two square masses, uniformly over all compact C² profiles across a gap | `SeparatedSupportsRemoveTheGammaSingularity` |
| Finite prime horizon | A common support window truncates all mixed prime shifts uniformly over signed profiles and bounds their full sum by square masses | `BoundedWindowsHaveFinitePrimeInteraction` |
| Full separated-source payment | Prime, Gamma and both pole contributions yield an adjustable old-mass charge with a finite reciprocal new-mass charge | `TheSeparatedMixedSourceIsBounded` |
| Arbitrary short-cell charge | The inherited logarithmic section gain, with the full pole cost retained, pays every fixed mass charge below a profile-independent and translation-independent threshold | `EveryShortCellPaysAnyFixedMassCharge` |
| Exact-diagonal extension | A constructed new width pays the full interaction, retaining `W(p,p)-epsilon*mass(p)` and any prescribed new-mass coefficient without an old sign premise | `AShortNewCellPaysItsOwnInteraction` |
| Adaptive arithmetic extension | At every exterior centre, a new small cell preserves any chosen fraction below one of the entire old section floor, with old widths fixed and arbitrary new profiles | `AnAdditionalCellPreservesTheOldSections` |
| Nested fixed-width positive sections | One width sequence at `log(n+1)` supports every finite independently profiled prefix with full Weil form at least square mass; earlier widths never change | `FixedCellWidthsSupportNestedPositiveSections` |
| Actual graph coercivity | The C² inverse Doob lift preserves the full Weil diagonal; on a fixed window, the arithmetic section floor controls its complete source-graph norm | `TheGraphNormIsControlledBySectionEnergy` |
| Literal graph completion | The full finite-subset projection net converges in the existing complete source graph; its original Weil pairings equal the completed removal and residual forms, with residual orthogonal to the whole closed old carrier | `TheSectionProjectionConvergesInTheSourceGraph` |
| Weighted source cost | Unused arithmetic reserve divides each exact cell's source-kernel energy by its mass weight; the resulting smaller cost bounds finite and completed removal and the signed residual | `TheUnusedReserveReducesTheSourceCost` |
| Complete-cell index capture | One common actual logarithmic grid eventually carries every negative square of a fixed finite smooth Weil family; all mixed-entry convergence premises are discharged from the source | `TheCompleteCellsCaptureEveryFiniteIndex` |
| Bounded projection on the full graph | Actual arithmetic coercivity constructs a unique bounded Weil projection onto the closed section carrier; it agrees with the finite-section limit and gives exact signed Schur subtraction on all graph vectors | `TheClosedSectionHasABoundedWeilProjection` |
| Strict full-width reserve | Keeping the true width inside the exponential pole factor leaves a positive uniform weighted reserve on the original section spaces and improves completed source cost by the factor `1+rho` | `TheFullWidthStillRetainsArithmeticReserve` |

## Tools to develop and research topics

**Completed-form refinement calculus.** Track the complete Weil matrix, overlap relations, polar
rows, Schur reserve and inertia through finite arithmetic extensions. Treat radicals explicitly.
The first arithmetic objective is an interacting family beyond the existing narrow-section space.

**Weighted source estimates.** The unused-width reserve now gives a proved dual kernel bound
with cell weight `1+(1-a)(1+(n/N)(1+log N))/8`. Determine which growing or translated patterns
have controlled weighted kernel tails and sampling errors. In particular, estimate the combined
prime–pole cancellation before squaring. The fixed-window estimate does not answer these questions.

**Quantitative adaptive carriers.** Single-cell extension and a nested infinite family with
fixed widths are established. Quantify the widths and enlargement costs.
Determine whether widths can remain comparable to local logarithmic spacing when the global
pole directions are retained as an index cost. The current absolute mixed bounds supply no such
width lower bound. A controlled family must then approximate the required tests in the completed
form; separated-cell positivity alone does not give this transfer.

**Charged near-incidence estimates.** Preserve signed successor and near-ratio terms through
stabilizer decompositions. Seek estimates at the actual source and identify the precise test
vectors that use the charge.

**Limits in the completed energy norm.** Relate absolute profile error budgets to the signed Gram
norm under specified refinements. Prove finite-family approximation with all mixed entries.
Retain possible escape to infinite height until a theorem controls it.
The canonical arithmetic-section projection is now realized in the existing complete source graph,
with its original full Weil pairing and closed-carrier orthogonality, and extends to a bounded
projection on the entire graph. Quantify how this projection changes under arithmetic enlargement. Relate this
construction to the existing completed aperture domain, whose actual bounded source remainder
already gives `||u||_arch^2 <= W_a(u)+||B_a||*||u||_2^2`.
Fixed-window graph convergence does not supply uniform control as the aperture grows.

**Gram equality and multi-window rigidity.** Develop joint block inequalities retaining
off-diagonal energy. Determine which incompatibilities of kernel zero sets can supply strict
inequalities with a macroscopic gain after arithmetic transfer.

**Signed prime surplus.** Prove a common-profile budget for the actual prime pairs. Preserve parity,
oscillatory lobes, prime-power reductions, collar losses and the conductor range. A saving in a
different averaged model is not the required estimate.

**Index–work comparison.** The quantitative lower comparison and finiteness classification are
established, as is the strict surplus above every positive index. Construct arithmetic upper bounds. Distinguish a
bounded number of exceptions from their absence.

**Terminal field estimates.** Combine the zero-free lens and lower reserve with an independently
proved arithmetic upper estimate on a common domain. Subtract singular self-terms without
discarding reflected-partner or exterior contributions.

**Cancellation across scales.** Estimate the actual completed Laurent-source work against
`h_(2R)-h_R`, retaining its signed source coefficients and all exterior interactions. The
nonnegative reflected representation supplies a lower count; an arithmetic upper estimate must
come from the source. Fixed low-height contributions lose weight in this difference. Determine
whether this permits a vanishing or uniformly subcritical increment estimate even when absolute
source-field bounds grow with the observation height. Control the removal of the compact taper
at both scales together; separate absolute estimates can destroy the desired cancellation.

**Finite-field realization.** Derive the required signatures from actual section or incidence
structure. Explain both the bounded genus loss and the failure of golden or complex fake data.

## Foundational principles and traps

| Principle | Invalid shortcut it excludes |
|---|---|
| Fix the completed pairing | Proving positivity of a different corrected matrix |
| Keep the poles global | Spending the same pole reserve in several local estimates |
| Retain mixed entries | Inferring positivity on a span from positivity of its generators |
| Separate source selection from sign | Treating gauge rigidity or coefficient positivity as a Weil inequality |
| State the surviving domain | Passing positivity through a divergent subtraction off its nullspace |
| Preserve quantifiers | Replacing all signed vectors by a height average, or changing smoothing profile between estimates |
| Distinguish ranks and indices | Applying a prime-counterterm no-go to the completed form's index |
| Prove exhaustion | Using increasing dimension or shrinking support as a density theorem |
| Preserve defect quanta | Treating a power-sparse exceptional set as empty |
| Extract positive survivors | Retiring a mechanism without its sharp boundary or replacement statement |

The fixed-spline index, unit-window energy bound and all-aperture Weil positivity are RH-strength
endpoints. Finite total energy or a finite global index controls exceptions but does not eliminate
them. Endpoint Mertens or exact genus statements can require more than RH; their extra strength
must not be introduced accidentally.

## Relation to the wider research

ArithmeticIndexDescent owns the transport of source-derived signature bounds between arithmetic
presentations. ACS supplies the sections and intersection target. AOG supplies orbit visibility and
index receivers. ALG supplies polar compatibility. SSHA supplies the joint estimates and overlap
kernels. RAPT and RBG supply counterterms, finite parts and survival domains. BGG and the correlation
programmes supply charged relations. TTPC supplies explicit averaged consumers. IGP supplies
rigidity of Gram equality. AES and CDG supply source currents, work and localized defect measures.
The zero-free height gap in RHTower combines with AES's near/far reflected estimates to give the
positive scale refinement used here; local divisor finiteness converts its annular quantum into
the high-scale escape alternative.

This connects the critical-sign wall, the transfer wall and the realization wall. It does not
identify their missing constructions merely because their endpoints lead to the same RH statement.

## Success criteria and contributions

A contribution proves an unconditional statement about explicitly constructed objects. It names
the actual source, full form, domain, scale range, normalization and comparison map. Structural
conditions in a general theorem must be proved in every arithmetic application. An unknown
estimate cannot be hidden in an assumption, typeclass, structure field or helper theorem.

Substantial intermediate contributions include a larger positive arithmetic section space, a
mixed-term payment stable under extension, a finite-Gram transfer preserving an index bound, a
controlled growing-class finite part, a better signed surplus budget, or a quantitative index–work
comparison. New definitions and equivalent endpoints alone do not answer the programme's questions.

Every obstruction must state its scope and retain its strongest positive boundary, classification,
decomposition or replacement construction. Calibration uses the relevant members of the existing
battery with matching assumptions: curves, golden and complex fake data, sign twins, finite-prime
flips, shifted pairs, pole-budget relaxations and escape models.

Full success requires the source estimates and transfer theorems described above, culminating in
an exhaustive signature bound or an individual-defect exclusion theorem. A foundational calculus
without the missing arithmetic payment is infrastructure, not completion.
