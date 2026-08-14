# Laplace formation, forced defect history, recovery reconstruction, and passive selection

- **ID:** ULF-CDM-2
- **Stage:** 2 — fully proven on paper
- **Type:** SOURCE-GENERATED CONSERVATIVE DILATION / HISTORY-RECONSTRUCTION THEOREM
- **Source:** ULF-SRSM-10 complete Laplace-response atlas; ULF-CDM-1 passive-cycle mechanics;
  ULF-PFM-2 common-recovery information isometry
- **Statement:** Every nontrivial positive half-line formation generates, from its complete Laplace
  response alone, a unique marked positive shift-intertwining defect history.  Its squared
  amplitudes form a common geometric recovery kernel; the kernel reconstructs the formation and
  the formation reconstructs the source measure.  Visible formation plus the forced hidden channel
  is an isometric passive split cycle, while visible-only passive recovery is possible only for the
  zero response.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL CORE]`
  `[SOURCE-GENERATED THREE-ORGAN FUSION] [JOINT STATE RECONSTRUCTION]`
  `[CONVOLUTION DEFECT CONSERVATION] [RECOVERY KERNEL NOT INDEPENDENT]`
  `[CLASSICAL JULIA/WOLD/HAUSDORFF COMPONENTS] [EXACT CORPUS COUPLING]`
  `[LEAN CORPUS AUDITED READ-ONLY; NO LEAN WRITE/BUILD] [PRE-RH] [NOT RH]`

## 1. Higher pivot

The functional-equation packet theorem assumes a common Markov recovery kernel.  The passive-cycle
theorem assumes a passive reconstruction.  Either datum can be theatre if supplied independently
of the positive source formation.

For the complete Laplace-response formation discovered by Source-Response Signature Mechanics,
neither datum is independent.  The positive formation coefficient forces its defect amplitude;
shift covariance forces the whole history; isometry fixes its normalization; squaring gives the
Markov kernel; and the family of kernels reconstructs the source measure.

The mechanism is

\[
 \boxed{
 \text{source law}
 \Longleftrightarrow
 \text{complete formation response}
 \Longleftrightarrow
 \text{forced defect history}
 \Longleftrightarrow
 \text{common recovery kernels}.}
 \tag{LFD.1}
\]

This does not identify all RH-route organs.  It closes one missing formation law and changes the
selection target from an unexplained equality `reflection = formation` to a precise question:
does the source functional equation recover the physical current from the **visible formed leg
alone**, or does it necessarily use the forced hidden history?

## 2. Complete Laplace formation

Let `nu` be a Borel probability measure on `[0,infinity)` and assume

\[
 \nu\ne\delta_0.
 \tag{LFD.2}
\]

For `n>=1`, set

\[
 a_n=L_\nu(n)=\int_0^\infty e^{-nx}\,d\nu(x),
 \qquad
 d_n=\sqrt{1-a_n^2}.
 \tag{LFD.3}
\]

Then

\[
 0<a_n\le a_1<1,
 \qquad
 0<d_1\le d_n<1.
 \tag{LFD.4}
\]

Indeed `e^{-nx}<=e^{-x}<=1`, and equality in the integral defining `a_1` would force `nu=delta_0`.

Use the response space

\[
 \mathscr R=\ell^\infty(\mathbb N_{\ge1};\mathbb C)
 \tag{LFD.5}
\]

and the fibre-Hilbert sum

\[
 \mathscr R^{[2]}
 =\ell^\infty(\mathbb N_{\ge1};\mathbb C^2),
 \qquad
 \|(u,v)\|_{[2]}
 =\sup_n\sqrt{|u_n|^2+|v_n|^2}.
 \tag{LFD.6}
\]

Define diagonal visible and hidden formations

\[
 (A_\nu b)_n=a_nb_n,
 \qquad
 (D_\nu b)_n=d_nb_n.
 \tag{LFD.7}
\]

For a finite signed source current `J`, ULF-SRSM-10 proves

\[
 \mathcal T(J*\nu)=A_\nu\mathcal TJ,
 \qquad
 (\mathcal TJ)_n=\int e^{-nx}\,dJ(x).
 \tag{LFD.8}
\]

Thus `A_nu` is not a fitted diagonal contraction.  It is the literal representation of positive
half-line convolution on the complete source-character atlas.

## 3. One-step conservative split cycle

Define the split encoder

\[
 C_\nu:\mathscr R\longrightarrow\mathscr R^{[2]},
 \qquad
 C_\nu b=(A_\nu b,D_\nu b),
 \tag{LFD.9}
\]

and decoder

\[
 Q_\nu:\mathscr R^{[2]}\longrightarrow\mathscr R,
 \qquad
 (Q_\nu(u,v))_n=a_nu_n+d_nv_n.
 \tag{LFD.10}
\]

### Theorem 3.1 — source-generated passive split cycle

For every $b\in\mathscr R$,

\[
 \boxed{
 \|C_\nu b\|_{[2]}=\|b\|_\infty,
 \qquad
 \|Q_\nu\|=1,
 \qquad
 Q_\nu C_\nu b=b.}
 \tag{LFD.11}
\]

Consequently positive formation, hidden defect, and passive reconstruction form an exact
source-generated split cycle.  This reconstructs the state, not only its scalar work.

#### Proof

Coordinatewise,

\[
 |a_nb_n|^2+|d_nb_n|^2
 =(a_n^2+d_n^2)|b_n|^2=|b_n|^2.
\]

Taking the supremum proves that `C_nu` is an isometry.  Cauchy--Schwarz in each `C^2` fibre gives

\[
 |a_nu_n+d_nv_n|
 \le\sqrt{a_n^2+d_n^2}\sqrt{|u_n|^2+|v_n|^2},
\]

so `Q_nu` is contractive.  Finally,

\[
 (Q_\nu C_\nu b)_n=(a_n^2+d_n^2)b_n=b_n.
\]

The norm of `Q_nu` is one because it is a left inverse of an isometry.  QED.

### Corollary 3.2 — hidden formation is uniformly proper

The visible and hidden legs obey the sharp uniform bounds

\[
 \boxed{
 \|A_\nu b\|_\infty\le a_1\|b\|_\infty,
 \qquad
 \|D_\nu b\|_\infty\ge\sqrt{1-a_1^2}\|b\|_\infty.}
 \tag{LFD.12}
\]

Thus the visible leg is a strict contraction, while the forced hidden leg is bounded below.

### Corollary 3.3 — visible-only passive recovery no-go

Let $R:\mathscr R\to\mathscr R$ be any contraction.  If

\[
 R(A_\nu b)=b,
 \tag{LFD.13}
\]

then `b=0`.

#### Proof

If `b` were nonzero, then

\[
 \|b\|=\|R(A_\nu b)\|
 \le\|A_\nu b\|
 \le a_1\|b\|<\|b\|,
\]

a contradiction.  QED.

This is the exact difference between source-generated passive reconstruction and arbitrary
deconvolution.  The decoder `Q_nu` recovers every state, but only because the hidden defect is
retained.

## 4. Canonical conservative sheet involution

Define

\[
 \mathcal J_\nu(u,v)
 =\bigl(A_\nu u+D_\nu v,\;D_\nu u-A_\nu v\bigr).
 \tag{LFD.14}
\]

### Theorem 4.1 — unique marked reflection completion

The map `mathcal J_nu` is an isometric involution and

\[
 \boxed{
 \mathcal J_\nu^2=I,
 \qquad
 \mathcal J_\nu(b,0)=C_\nu b.}
 \tag{LFD.15}
\]

It is the unique fibrewise self-adjoint unitary whose first column is the marked positive vector
`(a_n,d_n)`.

#### Proof

Each fibre matrix is

\[
 J_n=
 \begin{pmatrix}a_n&d_n\\d_n&-a_n\end{pmatrix},
 \qquad J_n^2=I_2.
\]

Hence it is self-adjoint and unitary.  Conversely, a self-adjoint `2 x 2` matrix with first column
`(a_n,d_n)` has the form

\[
 \begin{pmatrix}a_n&d_n\\d_n&c_n\end{pmatrix}.
\]

Orthogonality of its columns gives `d_n(a_n+c_n)=0`.  Since `d_n>0`, `c_n=-a_n`.  QED.

The positivity and marking are load-bearing.  Arbitrary unitary completions of a contraction have
phase gauges.  The theorem does not claim uniqueness after those data are forgotten.

### No-go consequence

A positive contractive involution cannot be a nontrivial formation.  If `0<=A<=I` and `A^2=I` on
a Hilbert space, spectral calculus forces `A=I`.  Therefore the source functional equation cannot
literally be the one-sided positive `A_nu` off the neutral formation.  It can act on the conservative
double `mathcal J_nu`, or on a larger packet, but not on the positive compression alone.

## 5. Forced infinite history

Let

\[
 \mathscr H_\infty
 =\ell^\infty\bigl(\mathbb N_{\ge1};\ell^2(\mathbb N_0)\bigr)
 \tag{LFD.16}
\]

with norm `sup_n ||-||_{ell^2}`.  Define

\[
 (W_\nu b)_{n,j}=d_na_n^j b_n,
 \qquad j\ge0.
 \tag{LFD.17}
\]

Let `S*` be the backward shift in the history coordinate:

\[
 (S^*y)_{n,j}=y_{n,j+1}.
 \tag{LFD.18}
\]

### Theorem 5.1 — unique positive shift-intertwining history

The map `W_nu` is an isometry and

\[
 \boxed{S^*W_\nu=W_\nu A_\nu.}
 \tag{LFD.19}
\]

Moreover, suppose a diagonal map $V:\mathscr R\to\mathscr H_\infty$ has nonnegative amplitudes
`v_(n,j)`,

\[
 (Vb)_{n,j}=v_{n,j}b_n,
 \tag{LFD.20}
\]

is isometric, and satisfies `S*V=VA_nu`.  Then

\[
 \boxed{V=W_\nu.}
 \tag{LFD.21}
\]

#### Proof

For every `n`,

\[
 \sum_{j=0}^\infty d_n^2a_n^{2j}
 ={1-a_n^2\over1-a_n^2}=1,
\]

so `W_nu` is isometric.  Its intertwining identity is immediate.

For uniqueness, the intertwining identity gives

\[
 v_{n,j+1}=a_nv_{n,j},
 \]

hence `v_(n,j)=a_n^jv_(n,0)`.  Isometry gives

\[
 1=\sum_{j\ge0}v_{n,j}^2
 ={v_{n,0}^2\over1-a_n^2}.
\]

Nonnegativity forces `v_(n,0)=sqrt(1-a_n^2)=d_n`.  QED.

Thus homogeneous source-time covariance plus conservative normalization does not merely permit a
Wold history.  It determines the marked history exactly.

### State decoder and finite conservation

Define

\[
 (Q_\nu^\infty y)_n
 =\sum_{j=0}^\infty d_na_n^j y_{n,j}.
 \tag{LFD.22}
\]

Cauchy--Schwarz gives `||Q_nu^infty||=1` and

\[
 \boxed{Q_\nu^\infty W_\nu=I.}
 \tag{LFD.23}
\]

At every finite horizon `N`,

\[
 \boxed{
 |b_n|^2
 =a_n^{2N}|b_n|^2
 +\sum_{j=0}^{N-1}d_n^2a_n^{2j}|b_n|^2.}
 \tag{LFD.24}
\]

Terminal visible work and ordered hidden-history work jointly reconstruct initial work.  Letting
`N->infinity` reconstructs the state through `(LFD.23)`.

## 6. Recovery kernel is generated, and generates the source

Square the unique history amplitudes:

\[
 \boxed{
 K_\nu(n,j)=(1-a_n^2)a_n^{2j}.}
 \tag{LFD.25}
\]

### Theorem 6.1 — formation--recovery mutual reconstruction

For every `n`, `K_nu(n,-)` is a probability measure on $\mathbb N_0$.  It is the unique nonnegative
probability law satisfying the homogeneous survival equation

\[
 K(n,j+1)=a_n^2K(n,j).
 \tag{LFD.26}
\]

Conversely,

\[
 \boxed{a_n=\sqrt{1-K_\nu(n,0)}.}
 \tag{LFD.27}
\]

The full family `{K_nu(n,-):n>=1}` uniquely determines `nu`.

#### Proof

The geometric series proves normalization.  Any law satisfying `(LFD.26)` has
`K(n,j)=a_n^(2j)K(n,0)`; normalization forces `K(n,0)=1-a_n^2`.  Positivity of the Laplace
transform gives `(LFD.27)`.

Push `nu` forward under `x |-> y=e^{-x}` to a probability `rho` on `[0,1]`.  Then

\[
 a_n=\int_0^1 y^n\,d\rho(y),
 \qquad a_0=1.
 \tag{LFD.28}
\]

If two source laws have the same kernel family, `(LFD.27)` gives equality of every moment,
including the common zeroth moment.  Their integrals agree on all polynomials.  Density of
polynomials in `C([0,1])` and Riesz uniqueness give equality of the pushed-forward measures.
The inverse map `y |-> -log y` on `(0,1]` then gives equality of the original half-line measures.
QED.

The common recovery kernel in packet formation is therefore no longer an independent fitting
parameter for this class.  It is common across all observer laws formed with one fixed `nu`, not
across different source formations.  Fixing the source formation fixes the kernel; measuring all
coordinate recovery kernels recovers the source formation.

## 7. Convolution fusion law

Let `mu` be another nontrivial probability law and put

\[
 c_n=L_\mu(n),\qquad e_n=\sqrt{1-c_n^2}.
 \tag{LFD.29}
\]

Convolution gives

\[
 L_{\nu*\mu}(n)=a_nc_n.
 \tag{LFD.30}
\]

### Theorem 7.1 — ordered defect conservation under source fusion

At every response coordinate,

\[
 \boxed{
 1-(a_nc_n)^2
 =(1-a_n^2)+a_n^2(1-c_n^2).}
 \tag{LFD.31}
\]

Consequently the three-channel cascade

\[
 b_n\longmapsto
 \bigl(a_nc_nb_n,\;a_ne_nb_n,\;d_nb_n\bigr)
 \tag{LFD.32}
\]

is isometric.  Its fibrewise row map

\[
 (u_n,v_n,w_n)\longmapsto
 a_nc_nu_n+a_ne_nv_n+d_nw_n
 \tag{LFD.32a}
\]

is a contractive exact decoder.  No Hilbert-space adjoint on the ambient $\ell^\infty$ sum is
being asserted.

For a chain `nu_1,...,nu_k`, with `a_(r,n)=L_(nu_r)(n)`, the exact ledger is

\[
 \boxed{
 1-\prod_{r=1}^ka_{r,n}^2
 =\sum_{r=1}^k
 \left(\prod_{i<r}a_{i,n}^2\right)(1-a_{r,n}^2).}
 \tag{LFD.33}
\]

#### Proof

Equation `(LFD.31)` is the telescoping identity
`1-a^2c^2=(1-a^2)+a^2(1-c^2)`.  It makes the squared norm of `(LFD.32)` equal to `|b_n|^2`.
The finite formula follows by induction.  QED.

This is a genuine fusion law: source convolution multiplies visible survival, while hidden defect
is transported in ordered first-failure layers.  It is not a scalar determinant analogy.

## 8. Fourth-organ consequences

### 8.1 Information geometry

For any probability law `pi` on the response index, form the joint observer/history packet

\[
 \widehat\pi(n,j)=\pi(n)K_\nu(n,j).
 \tag{LFD.34}
\]

ULF-PFM-2 now applies with a **source-generated** common recovery kernel:

\[
 D_{\rm KL}(\widehat\pi\|\widehat\eta)
 =D_{\rm KL}(\pi\|\eta),
 \tag{LFD.35}
\]

and every measurable functional-equation action on the observer lifts by recovery, action, and
regeneration without changing KL or Jeffreys information.  The new content is not the sufficiency
identity; it is that `K_nu` is forced by the same source formation and reconstructs it.

### 8.2 Completion topology

Let `alpha=nu({0})`.  On `ell^2` or `c_0`,

\[
 \boxed{
 A_\nu\text{ is compact}
 \Longleftrightarrow\alpha=0.}
 \tag{LFD.36}
\]

In that chamber,

\[
 D_\nu-I\text{ is compact},
 \qquad
 D_\nu^{-1}\text{ is bounded}.
 \tag{LFD.37}
\]

Indeed `a_n->alpha` by dominated convergence.  If `alpha=0`, the visible diagonal tends to zero,
while `d_n->1`; finite truncations give compactness.  The uniform lower bound in `(LFD.12)` gives
invertibility.  Conversely a compact diagonal must send its coordinate unit vectors to a norm-null
sequence, forcing `a_n->0` and hence `alpha=0`.

When `alpha=0`, every `a_n` is nonzero, so the visible range contains all finitely supported
sequences and is dense.  The coordinate unit vectors show that `A_nu` is not bounded below.  An
injective bounded map with closed range has bounded inverse on its range; hence the visible range
is not closed.

Thus a zero-delay-free visible formation has dense nonclosed range, but its forced hidden
complement is Fredholm-trivial and uniformly reconstructive.  Formation nonproperness is not lost
information; it is information displaced into a proper complementary history.

### 8.3 Passive source selection schema

Let `J` be a finite zero-mass signed measure and $b=\mathcal TJ$.  Suppose a literal source operation
produces a contraction `R` on the complete response space satisfying

\[
 R\,\mathcal T(J*\nu)=\mathcal TJ.
 \tag{LFD.38}
\]

Then `(LFD.8)`, Corollary 3.3, and complete Laplace-response reconstruction give

\[
 \boxed{J=0.}
 \tag{LFD.39}
\]

This is the sharpened RH-facing gate.  It does not demand the unexplained identity
`reflection = positive formation`.  It asks whether the physical source gives passive recovery
from the visible formed response without access to the forced defect history.  If it does, every
nonzero vertical current is impossible.  If the source action uses the hidden history, no selection
follows.

## 9. Hostile conjecture loops

### Loop A — positive formation itself is the functional-equation involution

**False.**  A positive contractive involution is the identity; here `||A_nu||=a_1<1`.

**Survivor.**  The unique marked two-sheet conservative completion is `mathcal J_nu`.

### Loop B — a source contraction merely permits many unrelated histories

**False under the declared law.**  Positivity, diagonal source marking, isometry, and
`S*V=VA_nu` force `V=W_nu` coefficient by coefficient.

**Boundary.**  Remove marking, positivity, or the shift intertwiner and unitary gauges return.

### Loop C — packet recovery remains an external parameter

**False in the homogeneous Laplace class.**  The forced history squares to `K_nu`; its zeroth
mass reconstructs every `a_n`; Hausdorff determinacy reconstructs `nu`.

**Boundary.**  Arbitrary Markov kernels unrelated to the formation remain possible outside this
class.

### Loop D — nonproper visible formation means irreversible source loss

**False.**  For `nu({0})=0`, `A_nu` is compact and nonproper, while `D_nu` is boundedly invertible
and the full history map is isometric.

### Loop E — conservative completion forces the hidden history to vanish

**False.**  The split cycle reconstructs every response with generally nonzero hidden history.
Selection requires the additional visible-only passive recovery law `(LFD.38)`.

### Loop F — information-neutral functional equation selects the center

**False.**  KL and Jeffreys isometry preserve separation.  They certify that the common kernel loses
no information; they do not make the defect zero.

### Loop G — this theorem is a new dilation theory

**False.**  Julia/Halmos dilation, Sz.-Nagy--Foias/Wold Poisson kernels, geometric survival laws,
and Hausdorff moments are classical.  The defensible delta is their exact, source-forced coupling
through the complete Laplace formation and the resulting replacement of an independent recovery
premise by mutual reconstruction.

## 10. Literature and significance audit

Occupied parent mathematics:

- Robinson, *Julia operators and Halmos dilations*, proves Julia-operator unitarity and the defect
  intertwining identity: <https://arxiv.org/abs/1803.09329>.
- Shalit, *Dilation theory: a guided tour*, surveys isometric/unitary dilation and modern
  multivariable extensions: <https://arxiv.org/abs/2002.05596>.
- Bhattacharyya--Das--Sarkar, *The Defect Sequence for Contractive Tuples*, studies defect growth
  and pure tuples: <https://arxiv.org/abs/1211.5898>.
- Popescu, *Unitary invariants on the unit ball of `B(H)^n`*, uses noncommutative Poisson kernels
  and defect operators as unitary invariants: <https://arxiv.org/abs/1208.4266>.
- Wang, *A new functional model for contractions* (2025), gives a current intrinsic model through
  marked Nevanlinna discs and confirms that marked contraction models remain active territory:
  <https://arxiv.org/abs/2503.13977>.
- Liu--Pego, *On generating functions of Hausdorff moment sequences*, develops the Hausdorff
  moment/Pick-function interface: <https://arxiv.org/abs/1401.8052>.
- Salazar, *Determinacy Witnesses in the Completely Monotone--Stieltjes--Bernstein Hierarchy*
  (2026), organizes current Laplace/Hausdorff witness and transport rules:
  <https://arxiv.org/abs/2607.09868>.

The paper does not claim priority for any component.  The exact corpus contribution is a
five-way constitutive equivalence:

\[
 \text{positive source convolution}
 \leftrightarrow
 \text{complete Laplace multiplier}
 \leftrightarrow
 \text{marked Julia defect}
 \leftrightarrow
 \text{Wold/Markov recovery history}
 \leftrightarrow
 \text{Hausdorff source reconstruction}.
 \tag{LFD.40}
\]

It produces unconditional leverage: a literal source-visible passive decoder would annihilate the
complete physical current, while any nonzero current proves that its functional-equation recovery
must use hidden history, leave the common work doctrine, or fail passivity.

## 11. Lean audit and next gate

Lean corpus was audited read-only.  Relevant certified components exist separately:

- `ConstitutivePassiveCycleMechanics.lean` — passive split-cycle rigidity;
- `DepthOneJuliaDefect.lean` — scalar Julia defect factorization;
- `ConstitutiveInvariantPositivityKMSWall.lean` — geometric history-layer mass and normalization;
- `ConstitutiveThetaHasseKMSExecutionBalance.lean` — recovery-ratio reconstruction;
- ULF-SRSM modules — complete response and formation properness;
- `ConstitutiveFunctionalEquationPacketLift.lean` — common-kernel information isometry.

No existing declaration packages `(LFD.1)`--`(LFD.40)`.  No Lean file was written and no Lean
process or build was started in this research pass.  Formalization is queued only after independent
paper audit, as required by the research pipeline.

The next source theorem is now exact:

> Construct, before Xi or zero specialization, the physical complete current and prove either a
> passive visible-only recovery `(LFD.38)` or a theorem forcing its hidden history to vanish.  The
> present theorem then gives zero current without assuming reflection equals positive formation.

## Gates

- [x] literal source formation, not fitted diagonal contraction
- [x] passive split cycle with state reconstruction
- [x] unique marked history and recovery kernel
- [x] mutual recovery-kernel/source reconstruction
- [x] convolution fusion and exact defect conservation
- [x] fourth-organ information and topology predictions
- [x] visible-only passive selection no-go
- [x] hostile classical-component audit
- [x] Lean corpus audited read-only; no write/build
- [x] hostile correctness/significance audit with classical-component boundary
- [ ] Lean formalization after audit
- [ ] literal physical current and visible-only recovery theorem

## Log

- 2026-08-14 — pivoted from independent packet recovery to source-generated defect history.
- 2026-08-14 — proved unique positive shift-intertwining history, Markov-kernel generation, mutual
  source reconstruction, convolution fusion, passive cycle, and visible-only recovery no-go.
- 2026-08-14 — audited classical Julia/Wold/Hausdorff parents and Lean corpus read-only; no Lean
  write or build.
