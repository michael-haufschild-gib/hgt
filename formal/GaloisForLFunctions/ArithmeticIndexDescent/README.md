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
| Critical source rate | `R²(W(2R)-W(R))`, monotone in scale and retaining height-square charges of finite index witnesses |
| Critical source energy | The nonnegative extended sum of the exact height-square reflected kernel over all multiplicity-copy pairs |

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

### Moving arithmetic bands

A growing translated family has a stronger, different boundary. Retain only the profiles
with \(N/2\le n\le N\), then translate the section by \(-\log N\):

\[
 p_N(u)=\sum_{N/2\le n\le N}G_n(u+\log N-\log n).
\]

At every original full allowed width, this test is supported in the fixed interval
\(I=[-\log2,1]\). The retained weighted reserve gives

\[
 W(p_N,p_N)\ge A_N\|p_N\|_2^2,\qquad
 A_N=1+\rho\left(1+\frac{1+\log N}{2}\right)\longrightarrow\infty.
\]

For a fixed compact probe \(g\), let \(D_I(g)=\int_I|K_g(u)|^2\,du\). The exact combined
source representation proves

\[
 A_N|W(p_N,g)|^2\le D_I(g)\,W(p_N,p_N).
\]

Thus the energy unit balls of these moving bands become uniformly invisible to every fixed
probe, at rate \(O((\log N)^{-1/2})\). The estimate allows every independent profile and every
admissible width; its source budget depends only on the fixed probe and interval. The number
of available arithmetic cells grows, while their normalized action still vanishes.
Wider interlaced carriers require control of their signed mixed terms.

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

The same arithmetic extension pays any prescribed continuous spatial weight
\(\omega\ge1\), even when it is unbounded. Choose a bound \(c_n\) for \(\omega\) on
\([b_n-1,b_n+1]\), and make the new diagonal pay \(a_{n+1}c_n\) times ordinary mass.
The old loss is at most its weighted mass loss. Exact weighted mass addition then gives
one fixed width sequence satisfying

\[
 \int f(u)^2\omega(u)\,du\le W(f,f)
 \quad\text{for every independently profiled finite prefix }f.
\]

This removes aperture dependence from a restricted carrier's complete graph bound.
The exact source mass of the inverse Doob lift is

\[
 \|(Jf)_{\mathrm{source}}\|^2
 =\int f(u)^2\rho(u)\,du,\qquad
 \rho(u)=\frac{\cosh(u/2)}{\operatorname{riemannKernelReal}(u)}.
\]

Put \(B=2(1+\|\tanh(\cdot/2)\|_{\mathrm{mass}}^2)\). The original full polar identity
gives \(\|Jf\|^2\le W(f,f)+B\|(Jf)_{\mathrm{source}}\|^2\). For any
\(\varepsilon>0\), choose \(\omega=1+(B/\varepsilon)\rho\). Weighted payment yields

\[
 \|Jf\|^2\le(1+\varepsilon)W(f,f)
\]

on all prefixes of one fixed carrier. In particular, integer logarithms admit fixed positive
widths with the universal factor two. No graph-mass estimate or mixed-form sign is assumed;
the chosen widths pay the actual source density and both global pole rows.

These widths need not be comparable to the arithmetic spacing. The result uses local coercivity
and a finite mixed-source payment, and also holds for nonarithmetic increasing centres. It
therefore establishes stable assembly on a restricted domain; it does not supply the critical
arithmetic cancellation needed for larger overlapping cells or fixed-spline exhaustion.

Let \(K\) be the closure in the original source graph of all finite independently profiled
sums on this one integer-log carrier. The same bound \(\|p\|^2\le2W(p,p)\) holds
on \(K\). Compressing the actual Weil operator \(A\) to \(K\) gives an invertible
operator and hence a unique bounded Weil projection \(P\) from the whole graph to \(K\).
It fixes \(K\), satisfies \(W(k,x-Px)=0\), and retains the exact signed identity

\[
 W(x-Px,y-Py)=W(x,y)-W(Px,Py).
\]

The cost is uniform over the unbounded carrier:

\[
 W(Px,Px)\le2\|Ax\|^2,\qquad \|Px\|^2\le4\|Ax\|^2.
\]

This is a proper closed carrier. The actual normalized cusp escape has graph norm squared
tending to two and full Weil energy tending to zero, so it eventually leaves \(K\).
The existing infinite independent theta radical is killed by \(P\) and survives unchanged
in the residual. Zero-energy modes do not count as negative squares. Thus a uniform positive
carrier supplies a global projection calculus while its complementary sign remains an
independent arithmetic problem; its existence is not an exhaustion theorem.

The corpus also supplies stronger control at a sharp boundary. Its actual Gamma boundary
operator has `L²` norm at most `2π`, and sharp interval restrictions are uniformly bounded
on the complete arithmetic graph and land in the exact aperture completion. The growth of
the elementary constant `J(d)` as the gap closes is therefore not an intrinsic Gamma
obstruction. These tools make cumulative signed assembly cost the central issue in a
cell-based exhaustion; domain admission of each sharp cut is already available.

This boundary bound now transfers to the literal C² spectral form. If \(f\) vanishes
to the right of \(b\) and \(g\) to its left, their supports may touch at \(b\), and

\[
 \left|\int_0^\infty\omega(h)
   \int_{\mathbb R}\bigl(f(u)g(u+h)+f(u+h)g(u)\bigr)\,du\,dh\right|
 \le\pi\bigl(\|f\|_2^2+\|g\|_2^2\bigr).
\]

The collar bound holds for arbitrary signed continuous compact profiles. For C² profiles,
polarizing the original spectral Lévy identity identifies the full Gamma cross term with
the negative collar exactly. Both integral normalization and source domain are retained.
The constant is independent of the boundary, support widths and profile derivatives.

The actual Gamma boundary operator admits a sharper normalization. For
\(k(t)=e^{-t/2}/(1-e^{-2t})\), its positive Schur weight

\[
 w(t)=\frac{e^{-t/2}}{\sqrt{1-e^{-2t}}}
\]

satisfies the exact row identity

\[
 \int_0^\infty k(s+t)w(t)\,dt=\frac\pi2w(s),\qquad s>0.
\]

An explicit arctangent primitive proves both integrability and normalization.
Weighted Cauchy–Schwarz and Tonelli then give
\(\|H_\Gamma\|_{L^2\to L^2}\le\pi/2\) for the existing boundary operator,
improving its inherited upper bound by four. Boundary truncations below prove
that this operator constant is sharp. The displayed profile and full-source
bounds above retain their previously proved constants.
Kernel normalization supplies no sign for the remaining prime and pole terms.

The same weight retains the whole mixed reserve. For arbitrary complex
positive-half-line `L²` inputs \(f,g\),

\[
 \frac\pi4(\|f\|_2^2+\|g\|_2^2)-\Re\langle g,H_\Gamma f\rangle
 =\frac12\int_0^\infty\!\int_0^\infty
   k(s+t)w(s)w(t)
   \left|\frac{g(s)}{w(s)}-\frac{f(t)}{w(t)}\right|^2\,dt\,ds.
\]

The integrand is nonnegative and integrable on the actual product carrier.
The exact Schur rows pay its two diagonal pieces, and the existing absolutely
convergent Gamma pairing pays the cross term. Setting \(g=f\) expresses the
quadratic deficit from \(\pi/2\) as this same square energy. Thus a mixed
estimate can retain profile-dependent reserve rather than spending the whole
norm bound. The identity supplies neither a uniform strict gap nor a signed
prime-surplus estimate.

Equality in the quadratic bound is now classified. The weight satisfies
\(w(t)^2=e^{-t}/(1-e^{-2t})\), with
\(e^{-1}/(2t)\le w(t)^2\le1/t\) on \((0,1]\); the upper bound holds on
the whole positive ray. Its square is therefore not integrable at zero.
If the quadratic reserve vanishes, positivity of the kernel forces
\(f(s)/w(s)=f(t)/w(t)\) almost everywhere. Fubini fixes this ratio to one
constant, and square integrability forces that constant to vanish. Hence

\[
 \Re\langle f,H_\Gamma f\rangle=\frac\pi2\|f\|_2^2
 \quad\Longleftrightarrow\quad f=0.
\]

Each nonzero profile leaves a strict quadratic reserve. This statement is
pointwise in the profile: it gives no uniform margin over growing families.

The mixed reserve vanishes exactly when both inputs vanish. The same ratio
argument forces the first input to be zero; the exact mixed identity then
forces the other input to be zero. Apply this classification to the pair
\(((\pi/2)f,H_\Gamma f)\). Equality in the operator bound would give zero
mixed reserve, so

\[
 f\ne0\quad\Longrightarrow\quad
 \|H_\Gamma f\|_2<\frac\pi2\|f\|_2.
\]

This is strict norm inequality for each individual vector. It does not imply
a uniform improvement of the operator constant.

The critical boundary can be approached within the actual carrier. For
\(a>0\), the vector \(f_a=1_{(a,1]}w\) belongs to the original half-line
`L²` space and has the exact square mass

\[
 \|f_a\|_2^2=\int_a^1w(t)^2\,dt
 \ge\frac{e^{-1}}2\log(1/a),\qquad 0<a\le1.
\]

In particular, \(a=e^{-(n+1)}\) gives masses at least
\(e^{-1}(n+1)/2\). These are literal compactly supported indicator profiles.
Their lost interaction across both cutoff boundaries is uniformly bounded:

\[
 0\le \frac\pi2\|f_a\|_2^2-\Re\langle f_a,H_\Gamma f_a\rangle\le16.
\]

The reserve vanishes wherever both arguments are inside the cutoff or both
are outside. On the remaining region, \(k(s+t)\le2/(s+t)\) and
\(w(t)\le t^{-1/2}\) bound it by four power rectangles. Each has integral
\((2a^{-1/2})(2a^{1/2})=4\), with unit scale used for the outer boundary.
Thus the reserve stays bounded while square mass diverges. Consequently

\[
 \|H_\Gamma\|=\frac\pi2,
 \qquad
 \forall\delta>0\ \exists n:\quad
 \Re\langle f_{e^{-(n+1)}},H_\Gamma f_{e^{-(n+1)}}\rangle
 >(\pi/2-\delta)\|f_{e^{-(n+1)}}\|_2^2.
\]

The operator norm is sharp and no nonzero vector attains it. This settles the
uniform scalar improvement question on the original half-line `L²` carrier.
It leaves joint estimates retaining diagonal Gamma energy open: the cutoff
vectors are not asserted to nearly saturate the full arithmetic form. The
square reserve and explicit near-critical profiles are the useful surviving
tools; signed prime payment remains separate.

The actual finite prime horizon and both pole moments then give one constant \(C_R\)
for every boundary in a fixed window \([-R,R]\):

\[
 |W(f,g)|\le C_R(\|f\|_2^2+\|g\|_2^2),\qquad
 2|W(f,g)|\le\varepsilon\|f\|_2^2+D_{R,\varepsilon}\|g\|_2^2.
\]

These constants are constructed from the complete source. The second bound follows by
rescaling, with \(D_{R,\varepsilon}=4(C_R+1)^2/\varepsilon\). Consequently, for any
prescribed new charge \(L\), a sufficiently short cell \((b,b+\delta)\) adjacent to
the old left region satisfies

\[
 W(p+g,p+g)\ge W(p,p)-\varepsilon\|p\|_2^2+L\|g\|_2^2.
\]

The old diagonal is exact and need not be positive. No gap, profile derivative bound or
mixed-sign assumption is present. The remaining assembly problem is cumulative: these
absolute estimates still charge old mass at each extension and supply no width lower
bound or exhaustive signature bound.

Before estimating an ordered cross block, one pole product can be canceled exactly.
With \(C_{f,g}(h)=\int f(u)g(u+h)\,du\), the Gamma recursion is

\[
 k(h)=e^{-h/2}+e^{-2h}k(h),\qquad
 \int_0^\infty e^{-h/2}C_{f,g}(h)\,dh=A(f)B(g).
\]

Consequently the original mixed form satisfies

\[
 W(f,g)=B(f)A(g)-P(f,g)-T_\Gamma(f,g),\qquad
 T_\Gamma(f,g)=\int_0^\infty e^{-2h}k(h)C_{f,g}(h)\,dh,
\]

where \(P\) is the literal prime source. Exponentially tilting the two profiles
identifies the tail with the same Gamma operator, giving

\[
 |T_\Gamma(f,g)|\le\pi\left(
   \int e^{-4(b-u)}f(u)^2\,du+
   \int e^{-4(u-b)}g(u)^2\,du\right).
\]

The ordered supports make these decaying boundary-distance weights. Thus Gamma
can charge mass near the cut after its polar cancellation is retained. This
identity concerns one ordered block; its surviving polar product is not one
global rank-one correction under arbitrary assembly. Repeated cuts still need
a proved allocation of their costs, and the signed pole–prime remainder remains.

That remainder has an exact arithmetic description on the same profiles. Set
\(q(h)=e^{-h/2}C_{f,g}(h)\) and \(E(h)=e^h-\psi(e^h)\). For compact `C²`
profiles ordered about the cut, \(q\) is `C¹`, has a finite support horizon,
and vanishes on nonpositive lags. The actual prime term is
\(\sum_n\Lambda(n)q(\log n)\), with no extra factor of two, and the surviving
pole is \(\int_0^\infty e^h q(h)\,dh\). Abel summation therefore gives, for
every real constant \(c\),

\[
 W(f,g)=-\int_0^\infty (E(h)-c)q'(h)\,dh-T_\Gamma(f,g).
\]

All regularity, finite-horizon and integrability requirements follow from the
actual test profiles. Constant centering is free because \(\int q'=0\).
Taking absolute values only after cancellation bounds the full cross term by
\(\int |E-c||q'|\) plus the localized Gamma charge above. This identifies the
required derivative-weighted discrepancy; it does not bound it uniformly.
Independent centering on different lag intervals would create boundary terms.
The prime number theorem alone supplies no exhaustive signed index budget.

The Gamma square reserve transfers to this original arithmetic identity.
The actual half-line profiles are represented by
\(F(s)=e^{-2s}f(b-s)\) and \(G(t)=e^{-2t}g(b+t)\) for positive \(s,t\).
Translation, reflection and restriction preserve their full square masses:
\(\|F\|_2^2=M_b^-(f)\) and \(\|G\|_2^2=M_b^+(g)\), where these are the
left and right boundary masses above. Let \(\mathcal R_b(f,g)\) be the exact
mixed Gamma square integral of \(F,G\). Then

\[
 \begin{aligned}
 T_\Gamma(f,g)
   &=\frac\pi4\bigl(M_b^-(f)+M_b^+(g)\bigr)-\mathcal R_b(f,g),\\
 W(f,g)
   &=-\int_0^\infty(E(h)-c)q'(h)\,dh
     -\frac\pi4\bigl(M_b^-(f)+M_b^+(g)\bigr)+\mathcal R_b(f,g),
 \end{aligned}
 \qquad \mathcal R_b(f,g)\ge0.
\]

These identities use the same original tests, source normalization and global
pairing. Dropping only the nonnegative reserve gives a signed lower bound
that leaves the arithmetic discrepancy intact. When either input is zero,
the reserve refunds the entire displayed mass allocation. Its retention is
therefore relevant to extension costs that would otherwise charge old mass
at every step. A cumulative allocation across many cuts and a quantitative
bound on the signed Chebyshev pairing are still required.

### Arithmetic detail and average coupling

Complete adjacent cells have two independent coordinates: the weighted average `q_a`
and the balanced detail `d_a`. Write `C(q,X)` and `D(d,Y)` for their actual half-line
Hilbert vectors, `m_a=haarMass(a)` and `ell=vonMangoldt(2)/sqrt(2)`.
The opposite mixed prime orientations behave differently. ACS proves that the
coarse-to-detail orientation vanishes for every integer prime lag. At lag `log 2`,
the programme identifies the surviving orientation exactly:

\[
 \langle S_{\log2}D(d,Y),C(q,X)\rangle_{\mathbb R}
   =\sum_{a=1}^{Y}m_a d_a(q_{2a}-q_{2a+1}),\qquad 2Y+1\le X.
\]

The original mixed prime-two coefficient is therefore
`B₂=2 ell sum m_a d_a(q_(2a)-q_(2a+1))`. It reads adjacent coarse differences,
not the whole coarse mass. For every positive `epsilon`,

\[
 |B_2|\le\epsilon\sum_{a\le Y}m_ad_a^2
       +\frac{\ell^2}{\epsilon}\sum_{a\le Y}m_a(q_{2a}-q_{2a+1})^2.
\]

At a common odd horizon `X=2Y+1`, all detail indices above `Y` translate
beyond the coarse support, so the same formula accounts for the entire mixed
block without a terminal remainder. Both coarse and detail coefficients remain
arbitrary. This is an exact partial-source identity and an adjustable payment;
it does not supply an all-prime estimate or preserve the whole coarse Weil form
through a Schur elimination.

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

### Work at the critical decay rate

The scale difference has a distinguished normalization:

\[
 Q(R)=R^2\Delta W(R),\qquad
 R^2\bigl(h_{2R}(t)-h_R(t)\bigr)\longrightarrow\frac32t^2.
\]

The actual quartet payment therefore gives, for every off-line zero and every
\(b<3\gamma^2(1+a_\rho)\), the eventual lower bound \(b<Q(R)\).
One fixed exception is visible at every sufficiently large scale, even when there are only
finitely many exceptions. The limit is taken for that fixed quartet; no uniform limit over
an unbounded collection of zeros is assumed.

The corpus's optimized order-23 arithmetic source theorem supplies the off-line height floor
\(\gamma^2\ge H\), where

\[
 H=\frac{431349}{2000},\qquad
 \lambda=\frac32H,\qquad q_*=3H=\frac{1294047}{2000}.
\]

The positive diagonal angle makes the quartet charge strictly greater than \(q_*\).
Consequently

\[
 \mathrm{RH}\quad\Longleftrightarrow\quad
 \forall T\ \exists R\ge\max(T,4):\ Q(R)\le q_*.
\]

Under RH the work is identically zero. Under its negation, \(Q(R)>q_*\) eventually.
If off-line support is infinite, choosing arbitrarily high fixed quartets proves the stronger
conclusion \(Q(R)\to+\infty\). Sparse escape cannot hide in the critical normalization.
Finite tapered Laurent-source readings retain each strict lower bound: first choose the
damping scale, then remove the height taper. All exterior source fields remain present.

The height floor is inherited from
`RHTower.PrimeArchLogHeightDefectOrderTwentyThreeEndpointOptimization`; the critical-rate
forcing is the contribution here. No optimality of this exclusion constant is asserted.
An independent arithmetic upper bound for \(Q\) remains required.

The critical rate has an additional order law. In the inverse-square coordinate
\(a=R^{-2}\), write

\[
 g_a(t)=(1+at^2)^{-2},\qquad
 v_a(t)=\frac{t^4}{(1+at^2)^4},\qquad
 \partial_a^2g_a(t)=6v_a(t).
\]

For \(a\ge0\) and actual zero heights, the height gap proves

\[
 2|v_a(t)-v_a(u)|\le |t-u|\bigl(v_a(t)+v_a(u)\bigr).
\]

The reflected near-collision and far-field estimates therefore make each pair-work
\(F_{p,q}(a)\) convex. Its critical increment is the secant expression

\[
 R^2\bigl(F_{p,q}(a/4)-F_{p,q}(a)\bigr)
 =\frac{F_{p,q}(a/4)-F_{p,q}(a)}a.
\]

Convex secant comparison makes this expression nondecreasing in \(R>0\).
The pair increments are absolutely summable for \(R\ge4\), so the full arithmetic
rate \(Q(R)\) is nondecreasing there. The proof differentiates each finite pair
expression, then sums an established order inequality. It does not interchange an
infinite sum with differentiation.

The finite stratum has an exact source formula. Let \(F\) contain every off-line
analytic-multiplicity copy, let \(d_p=\operatorname{Re}\rho_p-1/2\), and let \(S_p\) be its
completed arithmetic Laurent-source field. If \(F\) is finite, then for every \(R\ge4\),

\[
 W(R)=\sum_{p\in F}d_p h_R(\gamma_p)S_p,\qquad
 Q(R)\longrightarrow M_2=\frac32\sum_{p\in F}\gamma_p^2d_pS_p.
\]

Every \(S_p\) retains the entire exterior divisor and archimedean completion. The reduction
to \(F\) uses zero displacement on critical copies, not a truncation of their interactions.
The individual source coefficients \(d_pS_p\) may be signed. Positivity of the complete
moment follows from its identification with the source rate and the quartet payment.

The resulting classification is unconditional:

| Off-line support | Critical-rate behavior |
|---|---|
| Empty, equivalently RH | \(Q\) is identically zero |
| Finite and nonempty | \(Q\to M_2\), with \(M_2>q_*\) |
| Infinite | \(Q\to+\infty\) |

Thus eventual boundedness of \(Q\), or existence of any finite real limit for \(Q\), is
equivalent to finite off-line support. This identifies the exact \(O(R^{-2})\) boundary for
the unscaled increment. Every finite exception also satisfies

\[
 3\gamma^2(1+a_\rho)\le M_2,\qquad 3\gamma^2<M_2.
\]

A finite critical-rate budget therefore gives finitely many exceptions and controls their
heights. A budget at or below \(q_*\) excludes them all; no such
independent upper budget is proved by this classification.

The critical rate also measures every finite smooth Weil negative index. A finite packet
\(P\) of right-hand multiplicity copies carries the charge

\[
 C_2(P)=\frac32\sum_{p\in P}\gamma_p^2\ge\lambda|P|.
\]

The completed source increment eventually exceeds every number below \(C_2(P)\).
The actual Pontryagin bound supplies a packet of cardinality \(k=\nu_-(W_f)\) for every
finite compact C² test family. Consequently every \(b<\lambda k\) satisfies
\(b<Q(R)\) eventually. The same payment holds in finite Laurent-source readings, with
the damping scale chosen before the height taper. On finite off-line support this gives

\[
 \lambda\,\nu_-(W_f)\le M_2.
\]

The packet is extracted from the actual divisor; no spectral witness or source estimate
is assumed. This is a quantitative transfer from negative index to arithmetic work,
while an upper budget on that work remains a separate research problem.

An existing arithmetic resolvent budget strengthens this cost from linear to quadratic.
At the strip edge, the full Xi divisor has positive spectral mass at most \(3/50\).
A right-hand packet and its disjoint critical-line reflections spend twice the packet's
mass. The per-copy lower bound therefore gives

\[
 \sum_{p\in P}\frac1{\gamma_p^2+1}\le\frac3{100}.
\]

Weighted Cauchy–Schwarz yields

\[
 |P|^2\le\frac3{100}\left(\sum_{p\in P}\gamma_p^2+|P|\right),
 \qquad C_2(P)\ge50|P|^2-\frac32|P|.
\]

Thus, for every finite smooth Weil index \(k\), the critical source rate eventually
exceeds every number below \(50k^2-3k/2\). On finite off-line support,

\[
 \max\!\left(\lambda k,\,50k^2-\frac32k\right)\le M_2.
\]

This uses the actual strip-edge arithmetic budget, with all copies and reflections
accounted for. That budget controls reciprocal heights; its consequence here is a
stronger lower cost for normal work. It does not supply an upper bound on \(M_2\).

The critical rate also has a canonical energy without a finite-support assumption. Define

\[
 K_2(p,q)=\frac38\operatorname{reflectedWork}
 (d_p-d_q,d_p+d_q,\gamma_p-\gamma_q;\gamma_p^2,\gamma_q^2),
 \qquad \mathcal E_2=\sum_{p,q}K_2(p,q)\in[0,+\infty].
\]

Each summand is nonnegative and is the limit of its normalized pair increment.
Pair monotonicity supplies a pointwise majorant by \(K_2\). Summable domination handles
finite energy; arbitrarily large finite subsums handle infinite energy. Consequently, along
the actual real damping scale,

\[
 0\le Q(R)\le\mathcal E_2\quad(R\ge4),\qquad Q(R)\longrightarrow\mathcal E_2.
\]

This construction keeps the exact cancellation in critical exterior rows. If \(d_q=0\), then

\[
 K_2(p,q)=\frac34\gamma_p^2
 \frac{d_p^2}{d_p^2+(\gamma_p-\gamma_q)^2},
\]

with the corpus's zero-denominator convention. The critical row's own height weight cancels.
Replacing this expression by an absolute bound weighted by both heights can lose summability.

The energy is finite exactly when off-line support is finite; on that stratum it equals the
full Laurent-source moment \(M_2\). Every finite smooth Weil index \(k\) satisfies

\[
 \max\!\left(\lambda k,50k^2-\frac32k\right)\le\mathcal E_2,
 \qquad \mathrm{RH}\ \Longleftrightarrow\ \mathcal E_2\le q_*.
\]

The extended formulation retains infinite energy instead of imposing a summability premise.
Nonnegative pair values do not assert a positive semidefinite Gram kernel. This canonical
identification and its lower charges still require an independent arithmetic upper estimate
to exclude a defect.

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
   Can its critically rescaled value `R^2*(W(2R)-W(R))` be bounded cofinally by the proved
   exclusion quantum, which would also eliminate finite exceptions?
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
| Critical-rate detection | A fixed quartet forces an eventual height-square charge in `R^2*DeltaW`; the certified arithmetic height floor gives a closed cofinal RH threshold, and infinite off-line support forces divergence | `TheQuadraticScaleWorkDetectsEveryException` |
| Exact critical-rate classification | Finite off-line support gives an exact finite full-source moment limit; zero, finite exceptional and infinite support have distinct rate regimes, with strict height bounds for each finite exception | `TheCriticalRateClassifiesAllOffLineSupport` |
| Critical-rate index payment | Actual right-copy packets witness every finite smooth Weil index and force its height-square source charge; each negative square costs the certified arithmetic unit, also in finite Laurent readings | `TheCriticalRatePaysEveryNegativeSquare` |
| Quadratic arithmetic index cost | The certified full strip-edge budget bounds each right packet's reciprocal-height mass by 3/100; weighted Cauchy forces critical-rate cost at least 50k²−3k/2 for every finite Weil index | `TheSourceBudgetMakesTheIndexCostQuadratic` |
| Inverse-scale curvature | Reflected work is convex in inverse-square scale above the actual height gap; convex secants make each normalized pair increment and the completed critical source rate monotone | `TheCriticalSourceRateIsMonotone` |
| Canonical critical source energy | The real-scale critical rate converges to the nonnegative extended height-square pair sum; its finite stratum is the full Laurent-source moment and it retains every finite Weil index charge | `TheCriticalSourceRateHasACanonicalEnergy` |
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
| Touching Gamma supports | The literal half-line operator gives a gap-independent square-mass bound for signed compact profiles; the exact C² spectral collar identity retains the original Gamma normalization | `TouchingSupportsHaveBoundedGammaInteraction` |
| Exact Gamma boundary weight | An explicit arctangent primitive gives the exact Schur row and the actual boundary operator norm bound `π/2` | `GammaBoundaryHasAnExactSchurWeight` |
| Exact mixed Gamma reserve | The unused `π/4` two-mass bound is an integrable weighted square difference on the original half-line `L²` carrier | `TheGammaBoundaryReserveIsAnExactSquare` |
| Gamma equality rigidity | The critical Schur weight is not square integrable; only the zero actual `L²` vector attains the quadratic `π/2` bound | `TheGammaBoundaryBoundHasNoNonzeroEqualityCase` |
| Actual boundary truncations | Compact indicator truncations lie in the original `L²` carrier, retain exact square mass and have an explicit logarithmic mass lower bound | `TruncatedGammaWeightsHaveLogarithmicMass` |
| Mixed Gamma norm rigidity | Zero mixed reserve forces both inputs to vanish; every nonzero vector has strict norm deficit below `π/2` | `TheGammaBoundaryOperatorHasNoNormMaximizer` |
| Sharp Gamma norm and near-critical profiles | Actual cutoff reserves are at most `16` while masses diverge, proving norm exactly `π/2` and explicit near-critical Rayleigh vectors | `BoundaryTruncationLosesOnlyBoundedGammaEnergy` |
| Actual prime-two mixed differences | The full mixed block at odd horizons reads adjacent coarse differences, with an adjustable weighted-square payment | `ThePrimeTwoMixedBlockReadsCoarseDifferences` |
| Full separated-source payment | Prime, Gamma and both pole contributions yield an adjustable old-mass charge with a finite reciprocal new-mass charge | `TheSeparatedMixedSourceIsBounded` |
| Full touching-cell payment | A gap-independent ordered-window source bound pays any old-mass allowance; a sufficiently short adjacent cell retains the exact old diagonal and any prescribed new charge | `TouchingCellsPayTheFullMixedSource` |
| Ordered pole cancellation | The first Gamma exponential cancels its precise polar product in the full mixed Weil form; the remaining Gamma tail costs exponentially localized boundary masses | `TheOrderedGammaTailRetainsPolarCancellation` |
| Centered arithmetic source | The literal ordered mixed Weil form equals centered Chebyshev error against the derivative of its own lag profile, minus the localized Gamma tail | `TheOrderedWeilSourceIsACenteredChebyshevDefect` |
| Gamma reserve in the original source | Actual translated and reflected tilted tests retain a nonnegative square reserve inside the centered Weil identity, with exact `π/4` boundary-mass allocation | `TheOrderedWeilSourceRetainsItsGammaSquareReserve` |
| Arbitrary short-cell charge | The inherited logarithmic section gain, with the full pole cost retained, pays every fixed mass charge below a profile-independent and translation-independent threshold | `EveryShortCellPaysAnyFixedMassCharge` |
| Exact-diagonal extension | A constructed new width pays the full interaction, retaining `W(p,p)-epsilon*mass(p)` and any prescribed new-mass coefficient without an old sign premise | `AShortNewCellPaysItsOwnInteraction` |
| Adaptive arithmetic extension | At every exterior centre, a new small cell preserves any chosen fraction below one of the entire old section floor, with old widths fixed and arbitrary new profiles | `AnAdditionalCellPreservesTheOldSections` |
| Nested fixed-width positive sections | One width sequence at `log(n+1)` supports every finite independently profiled prefix with full Weil form at least square mass; earlier widths never change | `FixedCellWidthsSupportNestedPositiveSections` |
| Actual graph coercivity | The C² inverse Doob lift preserves the full Weil diagonal; on a fixed window, the arithmetic section floor controls its complete source-graph norm | `TheGraphNormIsControlledBySectionEnergy` |
| Uniform graph coercivity on a fixed carrier | A single width sequence pays any continuous spatial weight; the exact inverse Doob mass gives a full graph bound with any factor above one across every finite prefix | `FixedCellsControlTheCompleteSourceGraph` |
| Unbounded-carrier projection and its exact boundary | The fixed integer-log carrier has a bounded full Weil projection with universal operator-energy cost; cusp escape proves properness and an infinite exact theta radical survives in its signed residual | `TheUnboundedCellCarrierHasAWeilProjection` |
| Literal graph completion | The full finite-subset projection net converges in the existing complete source graph; its original Weil pairings equal the completed removal and residual forms, with residual orthogonal to the whole closed old carrier | `TheSectionProjectionConvergesInTheSourceGraph` |
| Weighted source cost | Unused arithmetic reserve divides each exact cell's source-kernel energy by its mass weight; the resulting smaller cost bounds finite and completed removal and the signed residual | `TheUnusedReserveReducesTheSourceCost` |
| Complete-cell index capture | One common actual logarithmic grid eventually carries every negative square of a fixed finite smooth Weil family; all mixed-entry convergence premises are discharged from the source | `TheCompleteCellsCaptureEveryFiniteIndex` |
| Bounded projection on the full graph | Actual arithmetic coercivity constructs a unique bounded Weil projection onto the closed section carrier; it agrees with the finite-section limit and gives exact signed Schur subtraction on all graph vectors | `TheClosedSectionHasABoundedWeilProjection` |
| Strict full-width reserve | Keeping the true width inside the exponential pole factor leaves a positive uniform weighted reserve on the original section spaces and improves completed source cost by the factor `1+rho` | `TheFullWidthStillRetainsArithmeticReserve` |
| Moving-band source decoupling | The translated upper arithmetic half-band has a growing logarithmic mass floor; its energy unit ball couples to every fixed compact probe by O((log N)^(-1/2)), with an explicit complete-source kernel budget | `MovingArithmeticBandsDecoupleFromFixedTests` |

## Tools to develop and research topics

**Completed-form refinement calculus.** Track the complete Weil matrix, overlap relations, polar
rows, Schur reserve and inertia through finite arithmetic extensions. Treat radicals explicitly.
The first arithmetic objective is an interacting family beyond the existing narrow-section space.

**Weighted source estimates.** The unused-width reserve now gives a proved dual kernel bound
with cell weight `1+(1-a)(1+(n/N)(1+log N))/8`. Determine which growing or translated patterns
have controlled weighted kernel tails and sampling errors. In particular, estimate the combined
prime–pole cancellation before squaring. The fixed-window estimate does not answer these questions.

**Quantitative adaptive carriers.** Single-cell extension and a nested infinite family with
fixed widths are established. A prescribed spatial weight can also be paid on one such family,
giving a uniform complete-graph bound across all its prefixes. Quantify the widths and enlargement costs.
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
