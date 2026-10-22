# Conservative character support and singularity law

- **ID:** `conservative-character-support-singularity-law`
- **Stage:** `1-in-progress`
- **Type:** MASTER THEOREM CANDIDATE
- **Paper target:** `../4-publication-ready/riemann-source-modular-superselection/main-universal.tex`
- **Status:** `[CONJECTURE]` frozen statement under hostile priority and whole-corpus audit

## Public sentence

> A positive conserved completion retains exactly the unitary characters of a source; every
> nonunitary character can survive only through a reciprocal indefinite pairing or a singular
> channel, and a filtered source measures the unavoidable singularity of that survival.

## Frozen theorem candidate

Let `G` be an abelian group and let

\[
  V=\bigoplus_{\chi\in\Sigma}V_\chi,
  \qquad U_gv=\chi(g)v\quad(v\in V_\chi)
\]

be a finite-dimensional complex character representation.  Assume that `Σ` is closed under
the Hermitian reciprocal involution

\[
  \chi^\vee(g)=\overline{\chi(g)}^{-1}.
\]

Then:

1. **Character conservation.** Every invariant multilinear functional vanishes on a homogeneous
   tuple unless the product of its characters is trivial.  Every invariant Hermitian form pairs
   `V_χ` only with `V_(χ^∨)`.
2. **Positive support.** Every invariant positive-semidefinite Hermitian form has every
   nonunitary sector in its radical.  Consequently the maximal positive conservative quotient is
   the direct sum of the unitary character sectors, with equal characters grouped into their
   positive blocks.
3. **Reciprocal survivor.** On a nonunitary reciprocal pair with equal multiplicity `r`, every
   nondegenerate invariant Hermitian form is a hyperbolic block and has inertia `(r,r)`.  Thus the
   negative index is not a choice of metric; it is the multiplicity of reciprocal nonunitary
   character pairs.
4. **Minimal positive correction.** If a Hermitian form of negative index `r` is made
   positive-semidefinite by adding a positive-semidefinite Gram correction on the same carrier,
   that correction has rank at least `r`.  The bound is sharp: the negative spectral part gives a
   rank-`r` correction.  Consequently any auxiliary-channel completion whose induced Gram
   correction has rank at most the auxiliary dimension needs at least `r` independent channels.
5. **Filtered singularity.** Let one reciprocal pair be represented by filtered source germs
   `x_N,y_N` at a scale `a_N -> 0`, where `x` is flat beyond every `a`-order and `y` has a nonzero
   finite `a`-grade.  Every exact sewing `R_N x_N = y_N` satisfies
   \[
      a_N^{-K}=o(\|R_N\|)\qquad(K\geq0).
   \]
   Hence a source realization of a reciprocal nonunitary sector carries two independent defects:
   finite negative index across reflection breadth and essential (infinite) Rees order along
   source depth.

The intended Riemann specialization uses

\[
  \chi_\rho(t)=\exp\!\bigl(t(\rho-\tfrac12)\bigr),
  \qquad
  \chi_{1-\bar\rho}=\chi_\rho^\vee.
\]

Then `χ_ρ` is unitary exactly when `Re ρ = 1/2`.  Every off-line reflected pair is one
hyperbolic block; on a finite packet its negative index is the existing Weil index and its Ward
charge is `4π` times that index (`8π` per strict-right quartet).  In the actual prime-valuation
realization, the same pair has all-orders-flat versus half-normal reflected sectors, so exact
source-internal sewing is beyond every finite Rees order.

## Why this is stronger than the killed candidate

`[REDISCOVERED] [BRIDGE]` The statement “a faithful positive conserved representation has only
unitary characters” is routine: invariance of a diagonal entry gives
`|χ(g)|² H(v,v)=H(v,v)`.  The two-channel real version is already formalized locally.

The replacement does not advertise that fact as novelty.  It joins three independently measured
parts of the same source character:

- character-selection support;
- Witt/Krein negative index across reciprocal sectors;
- essential Rees order of exact filtered sewing.

The exact Riemann claim is that the `8π` Ward quantum and the beyond-all-orders Wold/Rees fracture
are not parallel obstructions: they are respectively the breadth and depth coordinates of one
nonunitary source character.  This assertion is falsifiable by any mismatch of the character,
multiplicity, reflection, index, or filtered sector in the existing exact formulas.

## Paper proof status

### Character support

For homogeneous vectors `v_j in V_(χ_j)` and an invariant `n`-linear functional `T`,

\[
 T(v_1,\ldots,v_n)
 =T(U_gv_1,\ldots,U_gv_n)
 =\Bigl(\prod_j\chi_j(g)\Bigr)T(v_1,\ldots,v_n).
\]

If the product character is nontrivial, choose `g` where it differs from one; the coefficient
vanishes.  For a Hermitian form the scalar is `χ(g) overline(ψ(g))`; nonzero pairing therefore
forces `ψ=χ^∨`.

### Positive support

For `v in V_χ`, invariance gives

\[
 H(v,v)=|\chi(g)|^2 H(v,v).
\]

If `χ` is nonunitary, choose `g` with `|χ(g)| != 1`; hence `H(v,v)=0`.  Cauchy--Schwarz for a
positive-semidefinite form gives `H(v,w)=0` for all `w`, so `V_χ` lies in the radical.  Conversely,
the ordinary positive orthogonal sum on unitary character sectors is invariant.  This proves the
maximal positive conservative quotient classification.

### Reciprocal inertia

On `V_χ direct-sum V_(χ^∨)` with `χ` nonunitary, character support kills both diagonal blocks.
An invariant Hermitian form has matrix

\[
  \begin{pmatrix}0&B\\B^*&0\end{pmatrix}.
\]

If the form is nondegenerate, `B` is square and invertible.  Singular-value decomposition and
unitary congruence reduce the matrix to a direct sum of blocks
`[[0,s_j],[s_j,0]]`, `s_j>0`.  Each has eigenvalues `s_j,-s_j`, proving inertia `(r,r)`.

### Minimal positive correction

Let `A` be Hermitian with a negative subspace `N` of dimension `r`, and let `C >= 0` satisfy
`A+C >= 0`.  If `rank C < r`, then `N intersect ker C` is nonzero by dimension counting.  For
`0 != v` in that intersection,

\[
  \langle(A+C)v,v\rangle=\langle Av,v\rangle<0,
\]

contradicting positivity.  Thus `rank C >= r`.  Conversely, in the spectral decomposition
`A=A_+-A_-` with orthogonal positive and negative parts, `A_- >= 0`, `rank A_-=r`, and
`A+A_-=A_+ >= 0`.  The bound is sharp.  If an auxiliary feature space `W` contributes a Gram
correction `T^*T`, then `rank(T^*T) <= dim W`, so `dim W >= r`.

The scalar two-channel Schur tax in the corpus is the magnitude refinement of this rank law; it
must be presented as a specialization, not as proof of the rank theorem.

### Filtered singularity

Assume `||x_N||=o(a_N^m)` for every `m`, `||y_N||=Theta(a_N^d)`, and `R_Nx_N=y_N`.  For any `K`,
all-orders flatness at `K+d` gives `a_N^{-K}||x_N||=o(a_N^d)=o(||y_N||)`.  Since
`||y_N|| <= ||R_N|| ||x_N||`, division yields `a_N^{-K}=o(||R_N||)`.  This proof is
dimension-free.

## Exact corpus specializations to audit

| Family | Required shadow map | Current exact anchor |
|---|---|---|
| centered Xi divisor | `rho -> χ_rho` | `RiemannComplexModularCharacterLaw`; `XiSourceModularTypeSuperselectionLaw` |
| Weil/Ward index | reciprocal block -> negative index/charge | `finiteQuartet_eulerWardWeil_index_law` |
| Wold/valuation/Rees | same real character -> reflected type fracture | `CriticalActivationReesSourceLaw`; `XiSourceModularTypeSuperselectionLaw` |
| Julia positivity | PSD null diagonal -> null row; odd tangent before squaring | `TwoChannelRelativeCapacityNoGo`; pointed Fisher--Ward transgression |
| Hedenmalm | nonunitary modes cannot live in regular positive full-source graph | dense-radical and nonclosability modules |
| Deninger | complementary weights pair in cup; positivity only after Hodge/relative reduction | oriented Hilbert Hodge and ambient positivity no-go modules |
| Sonin/Calkin | reciprocal carrier survives only with unbounded/order-one boundary channel | Sonin coupling-energy and Calkin seam modules |
| recurrence | purely unitary character branch -> compact annihilator hull | protected-relation and countable future laws |
| bifiltration | breadth and depth cannot be faithfully scalarized | `BifilteredScalarizationNoGo` |
| reflection orientation | odd sector is torsion for symmetric channel | `ReflectionOrientationSingularSupportLaw` |

No row may be called a corollary until its hypotheses are explicitly instantiated in the paper.

## External parent theories and preliminary priority verdict

- `[LITERATURE]` Weight selection and purity of unitary finite-dimensional representations are
  classical representation theory.
- `[LITERATURE]` Krein/Pontryagin inertia and Schur-complement completion are classical operator
  theory.
- `[LITERATURE]` Deninger's program expects a weight-one pairing and positivity to force the
  Riemann line; it does not supply the arithmetic source completion.
- `[LITERATURE]` Connes--Consani identify positivity and the absorption/emission sign as central in
  the scaling/Sonine program; their construction does not give this prime-valuation filtered
  character classification.
- `[LOCAL-RESEARCH]` The exact prime reflected type fracture, essential Rees sewing, Ward index,
  source-character equality, and orientation singular-support laws are already separately proved.

**Preliminary verdict:** `SURVIVES PRELIMINARY ATTACK` only as an exact Riemann-source synthesis and
no-go classification.  The abstract character theorem is `[BRIDGE]`.  Novelty and general-journal
significance fail unless the whole-corpus audit proves that the index and essential-order
coordinates explain the named route families without importing their conclusions independently.

## Open core

`[OPEN CORE]` Complete the finite-dimensional spectral proof of the sharp correction-rank clause
in the exact field/form convention used by the paper, then complete every shadow map in the table and run a primary
literature collision audit for the combined index--essential-order Riemann specialization.

## Gates

- [x] Stage 1: frozen exact claim and killed elementary predecessor recorded
- [ ] Stage 2: dependency-closed proof including sharp border and every advertised specialization
- [ ] Stage 3: exact unconditional formal theorem(s), direct foreground checks, axiom/lint gates
- [ ] Stage 4: one-main-law paper, complete claim trace, hostile general-journal review

## 2026-08-01 strengthening: the common-divisor fusion exact sequence

The preceding character theorem is necessary but not yet the strongest statement exposed by the
positive high-shell frame.  A hostile check rules out the tempting but false claim that shell
replication multiplies the physical Ward charge.  The shell labels replicate the **source
conormal**, not the divisor.  Common-divisor scalarization retains one reciprocal block and sends
all transverse label blocks to its kernel.  This gives an exact conservation law rather than an
index overcount.

### Public law

> **Conservative divisor fusion cannot destroy source signature.  It splits that signature into
> the common-divisor quotient and a transverse kernel; at infinite multiplicity, a unit-residue
> quotient is necessarily singular in every stable Hilbert realization.**

### Universal finite fusion theorem

Let `I` be a finite nonempty label set, put `L = C^I`, and let

\[
  \epsilon_I(x)=\sum_{i\in I}x_i,
  \qquad
  K_I=\ker\epsilon_I.
\]

Let `u=|I|^{-1/2}(1,...,1)`, so `L=C u direct-sum K_I`.  On the reciprocal double
`L_+ direct-sum L_-` define

\[
  H_I((x,y),(x',y'))
   =\langle x,y'\rangle+\langle y,x'\rangle .             \tag{F1}
\]

For a real modular rate `a`, let

\[
  U_t(x,y)=(e^{at}x,e^{-at}y).                            \tag{F2}
\]

Then:

1. `H_I` is `U_t`-invariant.
2. If `a != 0`, no nonzero positive-semidefinite `U_t`-invariant Hermitian form is
   nondegenerate on either homogeneous sector.
3. `H_I` is nondegenerate and has inertia `(|I|,|I|)`.
4. The orthogonal label split gives an exact hyperbolic decomposition
   \[
     (L_+\oplus L_-,H_I)
       \cong
     (C u_+\oplus C u_-,H_{\rm div})
       \perp
     (K_{I,+}\oplus K_{I,-},H_{\rm tr}).                 \tag{F3}
   \]
   The common-divisor block has inertia `(1,1)` and the transverse kernel has inertia
   `(|I|-1,|I|-1)`.
5. The scalar fusion map
   \[
     E_I=|I|^{-1/2}(\epsilon_I\oplus\epsilon_I)
   \]
   is equivariant, its kernel is `K_{I,+} direct-sum K_{I,-}`, and its quotient carries exactly
   the single hyperbolic block in `(F3)`.  Hence negative index obeys the exact conservation law
   \[
     |I| = 1 + (|I|-1).                                  \tag{F4}
   \]

**Proof.**  Invariance follows from cancellation of `e^(at)` and `e^(-at)` in every cross term.
For positivity, invariance of a diagonal entry in a homogeneous sector gives
`h=e^(2at)h`; if `a != 0`, choose `t != 0` and obtain `h=0`, after which the
positive-semidefinite Cauchy--Schwarz inequality kills its full row.  For inertia, the unitary
change of variables

\[
  (x,y)\longmapsto 2^{-1/2}(x+y,x-y)
\]

sends `(F1)` to `||v_+||^2-||v_-||^2`.  Finally, the decomposition
`L=C u orthogonal-sum K_I` makes both cross terms split with no mixed contribution.  Since
`dim K_I=|I|-1`, `(F3)`--`(F4)` follow.  `QED`

### Infinite fusion theorem

Let `c_00(N)` carry its standard embedding into `ell^2(N)`, and put

\[
  \epsilon(x)=\sum_m x_m .                               \tag{F5}
\]

Then `epsilon` is not sequentially closable.  Indeed,

\[
  x_N={1\over N}\sum_{m=1}^N e_m,
  \qquad ||x_N||_2=N^{-1/2}\to0,
  \qquad \epsilon(x_N)=1.                                \tag{F6}
\]

More generally, if the source modes form a Bessel family in a Hilbert space, no bounded Hilbert
vector has one fixed nonzero response against every mode.  Thus abandoning diagonal weights does
not regularize a stable infinite frame.  A diagonal weighted repair exists only after assigning
weights whose reciprocal sum converges; that repair makes the unit shell responses increasingly
expensive and is not the uniform source normalization.

### Riemann-shell specialization

For `m >= 12`, put

\[
  F_m(s)=\zeta(s)H_m(s),
  \qquad
  H_m(s)=\zeta((m+1)s)^{-1}-\zeta(ms)^{-1}.
\]

The established high-shell theorems give, on `Re s > 1/2`:

1. every `H_m` is holomorphic and zero-free;
2. `ord_rho(F_m)=ord_rho(zeta)` at every point of that half-plane;
3. the family `(H_m)_(m>=12)` is jointly differentially algebraically independent even over the
   differential field generated by `C(s)` and `zeta`;
4. the arithmetic shell sources are pairwise coefficient-disjoint and nonnegative.

Consequently, at any hypothetical strict-right zero `rho` of multiplicity `d`, every logarithmic
shell conormal has the same residue:

\[
  Res_{s=rho}{F_m'(s)\over F_m(s)}=d.                    \tag{F7}
\]

After division by `d`, principal-conormal scalarization on every finite shell packet is exactly
the augmentation `epsilon_I`.  Differential independence proves that the transverse labels in
`K_I` are genuine source directions, not repeated formulas for one multiplier.

Attach the centered character

\[
  chi_rho(t)=\exp(t(rho-1/2)),
  \qquad chi_{1-\bar rho}=chi_rho^vee.                   \tag{F8}
\]

One reflected pair on an `N`-shell packet has source inertia `(N,N)`.  Its common-divisor quotient
has inertia `(1,1)` and its transverse shell kernel has inertia `(N-1,N-1)`.  Schwarz conjugation
doubles these numbers for a full off-line quartet.  Therefore the physical quotient has negative
index `2`, exactly the existing finite-quartet Weil index, and Ward charge

\[
  4\pi\,ind_- = 8\pi.                                    \tag{F9}
\]

The shell source itself has negative index `2N`; the missing `2N-2` directions lie in the
transverse fusion kernel.  Equation `(F9)` is therefore the quotient charge of the replicated
source, not a charge replicated once per shell.

As `N -> infinity`, the unit-residue conormal row is `(F5)` and is nonclosable by `(F6)`.  This
identifies the exact singularity of any source-faithful common-test passage from the positive
hypertranscendental frame to a finite Ward packet.

### Depth refinement of the same character

The shell-transfer theorem gives the source-normalized adjacent-label character

\[
  z(s)=2^{1/2-s},\qquad |z(s)|=2^{1/2-Re s}.              \tag{F10}
\]

The prime-valuation realization of the same centered real rate has reflected quotient

\[
  {J_{1-a}(p^k)\over J_a(p^k)}=p^{2k(a-1/2)}.            \tag{F11}
\]

Thus label breadth and valuation depth are two independent amplifiers of one modular drift.
Breadth sends nonzero drift into arbitrarily large source signature before common-divisor fusion;
depth sends it into exponential and, for the actual flat/half-normal pair, beyond-all-finite-Rees
sewing cost.  On the neutral line both characters are unitary.  Off it, no bounded
finite-negative-index, finite-Rees-moderate realization can be simultaneously source-label
faithful, common-divisor faithful, and positive conservative.

### Exact shadow classification

The fusion sequence, not a list of thematic similarities, is the proposed organizer:

| Corpus theorem | Exact place in fusion law |
|---|---|
| positive relative-HT common divisor frame | constructs independent label module and common quotient |
| shell codiagonal nonclosability | infinite augmentation `(F5)` fails Hilbert closure |
| Hedenmalm dense proper radical | a source orbit erased by a proper conservative quotient cannot have a closed radical |
| Wold--Poisson ancestry | supplies label/depth source coordinates before augmentation |
| Gamma whitening divergence | weighted attempt to normalize the augmentation/primitive fibre |
| Sonin/Calkin no-gos | bounded or compact consumers cannot implement the nonclosable augmentation |
| Deninger reciprocal Hodge pair | Hermitian realization of the reciprocal block in `(F1)` |
| four-unit Ward positivity | positivity requested only on the one-block divisor quotient |
| `8pi` Ward law | topological charge of the full-quartet quotient block `(F9)` |
| finite-Rees superselection | depth realization `(F11)` of the same nonunitary character |
| unitary recurrence theorems | the `a=0` branch, where positive conservative recurrence is allowed |

Each paper corollary must instantiate its hypotheses explicitly.  Rows whose source map is not
proved are explanatory comparisons, not logical corollaries.

### Antagonistic verdict

The finite decomposition `(F3)` and the nonclosability sequence `(F6)` are elementary parent
mathematics.  The candidate-new result is their exact application to a positive, coefficient-
orthogonal, relatively hypertranscendental family carrying one replicated Riemann divisor, and
the identification of the physical `8pi` packet as the quotient index while the transverse
source signature becomes a singular radical.

This is materially stronger than the primitive--fibre paper: it supplies a genuine universal
object, the fusion exact sequence, and makes the HT frame load-bearing.  It still does not exclude
zeros.  Its honest proof-route consequence is precise: a successful source theorem must act on
the fusion sequence before augmentation and prove that its one-block quotient is a positive
conservative character; any finite consumer introduced after augmentation has already lost the
transverse source data and cannot derive that positivity from a bounded Hilbert lift.

General-journal significance remains provisional until three gates close:

1. formalize the finite fusion decomposition and the shell specialization without identifying
   shell labels with physical zero multiplicity;
2. complete a primary-literature collision audit for common-divisor conormal fusion, indefinite
   index splitting, and nonclosable uniform-residue rows;
3. rewrite the paper with one main theorem and prove every advertised Hedenmalm, Wold, Sonin,
   Calkin, Deninger, Rees, and Ward specialization, deleting any row that remains only analogous.
