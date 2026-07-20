# Gaussian Hilbert ambient-completion budget

- **ID:** gaussian-hilbert-ambient-completion-budget
- **Stage:** 1-in-progress
- **Type:** COMPETING CONJECTURES / DIMENSION AUDIT / FAILURE-DRIVEN CONNECTOR
- **Scientific status:** `[LEAN-FORMALIZED SINGLE-TOP LAW] [CONJECTURAL GENERAL-METRIC FRONTIER]`
- **Novelty:** `[NOVELTY UNVERIFIED]`; no priority claim
- **Source:** continuation of the Gaussian Fano-curvature and transverse-degree programme

## The dimension correction that owns this card

The full-top transverse construction uses a base one-particle space `E` and an orthogonal
completion space `W`.  If

\[
 T=\operatorname{Sym}^M(E),\qquad k=\dim T,
\]

then the construction requires an isometry `T -> W`, hence `dim W >= k`.  Consequently the
ambient Hilbert dimension of the resulting Gaussian configuration is at least

\[
 \dim E+\dim\operatorname{Sym}^M(E),
\]

not merely `dim E`.  In particular, the formalized degree-five example has one-particle space

\[
 \mathbb R^{16}\oplus\mathbb R^{\binom{20}{5}},
\]

of dimension `16 + 15504 = 15520`.  The parameter `d=16` in the lowering-charge formula is the
base dimension only.  It is not an ambient-dimension threshold.

This correction retires the premature reading that the existing construction proves sign
reversal in every ambient dimension at least four.  It proves a finite-dimensional reversal,
but leaves the least ambient dimension completely open.

## Exact metric question

For distinct points `X=(x_1,...,x_N)` in a real Hilbert space put

\[
 K_X(t)_{ij}=\exp(-t\lVert x_i-x_j\rVert^2),\qquad t>0.
\]

Define the **Gaussian curvature rank**

\[
 d_*:=\inf\left\{d:\ \exists X\subset\mathbb R^d,\ \exists t>0,\quad
 (\log\det K_X)''(t)>0\right\}.
\]

The compiled example proves only `d_* < infinity`.  The line theorem proves `d_* >= 2`, and the
current low-ambient conjecture would give `d_* >= 4`.  No exact value is claimed.

## Competing conjectures

### ACB-1 -- three-mode stability

`[CONJECTURE]` For every finite family of distinct points in a real Hilbert space of affine
dimension at most three,

\[
 (\log\det K_X)''(t)\le 0\qquad(t>0).
\]

Equivalently, for every finite-dimensional subspace of symmetric Fock space over at most three
real modes that is invariant under all annihilators, the determinant-line number variable `D`
satisfies

\[
 \operatorname{Var}(D)\le \mathbb E D.
\]

The invariant-subspace formulation covers ordinary coherent spans and their collision limits at
once.  Ordinary commuting-matrix inequalities do not prove it: artificial weighted symmetric
modules can violate the Fano inequality, but they omit the Fock completion channels.

### ACB-2 -- finite critical dimension

`[CONJECTURE]` The infimum `d_*` is attained and is governed by a sharp completion-budget law,
not by the number of points.  A valid theorem must both prove concavity below the threshold and
construct an actual injective Euclidean configuration at the threshold.

This is intentionally hostile: the current construction supplies neither the value of `d_*` nor
a useful upper bound close to it.

### ACB-3 -- quartic Fock stability

`[CONJECTURE]` Every finite annihilation-invariant polynomial subspace of maximal homogeneous
degree at most four has nonnegative Fano defect.  Degree five is the first degree at which the
compiled transverse mechanism can reverse the sign, but that does not yet prove sharpness among
arbitrary multilevel inverse systems.

An exact cubic or quartic counterexample retires ACB-3.  A proof must classify the nonhomogeneous
graph couplings rather than only the graded Hilbert function.

## Unequal-gap multichannel connector

`[PAPER-PROVED] [LEAN-FORMALIZED] [PARENT ALGEBRA, NOT A NOVELTY CLAIM]` Let `I` be finite.  Fix a deterministic
lowering charge `B`, lower degrees `ell_i`, upper degrees `m_i`, and set

\[
 g_i=m_i-\ell_i>0.
\]

Suppose an orthogonal graph decomposition has determinant partition

\[
 Z(t)=t^{B+\sum_i\ell_i}\prod_{i\in I}(t^{g_i}+\mu_i),
 \qquad \mu_i\ge0.
\]

Put

\[
 p_i(t)=\frac{t^{g_i}}{t^{g_i}+\mu_i}.
\]

Then its degree variable is

\[
 D=B+\sum_i\ell_i+\sum_i g_iX_i,
\]

where the `X_i` are independent Bernoulli variables of parameters `p_i(t)`.  Therefore

\[
 \mathbb ED-\operatorname{Var}(D)
 =B+\sum_i\ell_i-\frac14\sum_i(g_i-1)^2
  +\sum_i\left(g_ip_i-\frac{g_i-1}{2}\right)^2.       \tag{UG}
\]

Indeed, channel by channel,

\[
 g_ip_i-g_i^2p_i(1-p_i)
 =\left(g_ip_i-\frac{g_i-1}{2}\right)^2
  -\frac{(g_i-1)^2}{4}.
\]

Thus the sharp phase minimum over independent channel strengths is

\[
 \inf(\mathbb ED-\operatorname{Var}(D))
 =B+\sum_i\ell_i-\frac14\sum_i(g_i-1)^2.              \tag{UGmin}
\]

The existing transverse channel-square law is the specialization `ell_i=1` and `g_i=M-1`.
Formula (UG) is needed to audit multilevel attempts honestly: a large gap earns a quadratic
variance credit, while its entire lower endpoint and the common lowering skeleton remain charged.

## Symmetric-shadow Fano isoperimetry

`[PAPER-PROVED] [LEAN-FORMALIZED FOUNDATION] [CANDIDATE NEW COMBINED LAW]
[NOVELTY UNVERIFIED]` Let `E` have dimension `e`, let
`0 != T subset Sym^M(E)` have dimension `k`, and let `R_n(T)` be its degree-`n` lowering closure.
Put

\[
 H_n=\dim\operatorname{Sym}^n(E)=\binom{e+n-1}{n},
 \qquad h_n=\dim R_n(T).
\]

Write `a_i : Sym^{n+1}(E) -> Sym^n(E)` for the canonical normalized annihilators.  They obey the
two exact Hilbert-energy identities

\[
 \sum_i\lVert a_i x\rVert^2=(n+1)\lVert x\rVert^2,
 \qquad
 \sum_i\lVert a_i^*y\rVert^2=(n+e)\lVert y\rVert^2.     \tag{CCR}
\]

For an arbitrary subspace `U subset Sym^{n+1}(E)`, put
`partial U=span_i(a_i U)`.  Choose orthonormal bases `(u_p)` of `U` and `(v_q)` of `partial U`.
Parseval in `partial U`, adjointness, and Bessel in `U` give

\[
\begin{aligned}
 (n+1)\dim U
 &=\sum_{i,p}\lVert a_i u_p\rVert^2\\
 &=\sum_{i,p,q}|\langle v_q,a_i u_p\rangle|^2\\
 &=\sum_{i,p,q}|\langle u_p,a_i^*v_q\rangle|^2\\
 &\le\sum_{i,q}\lVert a_i^*v_q\rVert^2
  =(n+e)\dim(\partial U).                              \tag{HS}
\end{aligned}
\]

Thus the sharp one-step normalized-shadow law is a direct universal Hilbert-space theorem; it
does not require a monomial degeneration, generic position, or Macaulay's theorem.  Applying
(HS) to consecutive lowering closures and using
`H_{n+1}/H_n=(n+e)/(n+1)` gives

\[
 \frac{h_n}{H_n}\ge \frac{h_{n+1}}{H_{n+1}}
 \qquad(0\le n<M).                                      \tag{NS}
\]

Since `h_M=k`, every lower level therefore obeys

\[
 h_n\ge \frac{k}{H_M}H_n.                               \tag{SD}
\]

For the lowering charge `B_T=sum_{n<M} n h_n`, (SD) and the binomial identity

\[
 \frac1{H_M}\sum_{n=0}^{M-1}nH_n=\frac{M(M-1)}{e+1}
\]

give the sharp **symmetric-shadow charge law**

\[
 \boxed{\ \frac{B_T}{k}\ge\frac{M(M-1)}{e+1}\ }.       \tag{SC}
\]

Equality is attained by `T=Sym^M(E)`.  Thus the full top space is not merely a convenient example:
it minimizes the forced lowering charge per top direction among all top-symbol subspaces.

Now let `L:T -> W` be an arbitrary transverse completion of rank `r`.  The compiled rank-budget
law gives

\[
 \mathbb ED-\operatorname{Var}(D)
 \ge B_T+(k-r)M-\frac{rM(M-4)}4.                         \tag{RB}
\]

Because `r<=k` and

\[
 M+\frac{M(M-4)}4=\frac{M^2}{4}\ge0,
\]

substituting (SC) into (RB) yields the sharp universal bound

\[
 \boxed{\ \mathbb ED-\operatorname{Var}(D)
 \ge k\left(\frac{M(M-1)}{e+1}-\frac{M(M-4)}4\right).\ } \tag{SFI}
\]

Retaining the transverse rank gives a second universal law.  If the margin is negative and
`M>0`, then necessarily

\[
 \boxed{\ 4k(M+e)<(e+1)rM.\ }                           \tag{CB}
\]

Indeed, multiply the rank-sensitive lower bound by `4`; its right-hand side factors as

\[
 M\bigl(4k(M+e)-(e+1)rM\bigr).
\]

Thus curvature reversal has a quantitative **completion budget**: the number `r` of independent
transverse directions must exceed the fraction

\[
 \frac{r}{k}>\frac{4(M+e)}{(e+1)M}.
\]

Since any realization needs `dim W >= r`, (CB) is an ambient Hilbert-dimension obstruction, not
only a sign criterion.  Combining `r<=k` with (CB) recovers the strict phase threshold

\[
 4e<(e-3)M.                                               \tag{PT}
\]

The bound is attained by the full top space, a full-rank completion, equal nonzero singular
values, and the balancing phase.  Consequently, among **all** single-top transverse completions
with fixed base-mode count `(e,M)`, a super-Poisson phase exists exactly when

\[
 (e+1)(M-4)>4(M-1).                                     \tag{SFT}
\]

This strengthens the previous full-top calculation from an existence example to an extremal
classification.  The one-step shadow law (HS) is treated as parent theory: its equivalent
Hilbert-function and normalized-matching forms are classical enough that no novelty is claimed
for it.  The candidate scientific contribution is the sharp combination of this law with the
Gaussian determinant-line rank budget, namely (SFI)--(SFT).  That combined phase classification
has not been located in the inspected literature and remains `[NOVELTY UNVERIFIED]` rather than a
priority claim.

The phrase **base-mode count** is essential.  A rank-`r` transverse completion also needs at
least `r` orthogonal completion modes.  Thus the theorem does not identify `e` with the ambient
Hilbert dimension and does not by itself prove ACB-1.  What it proves is the sharp phase law after
the ambient completion cost has been separated from the active symmetric-power modes.

### Dependency audit for (NS)

The proof above closes the formerly hidden dependency.  The only inputs are the canonical
orthonormal monomial model for finite symmetric powers, the two matrix identities (CCR), Parseval,
Bessel, and the elementary recurrence for `H_n`.  The Lean module
`GaloisForLFunctions.HilbertMetric.SymmetricFockShadow` proves the matrices, both energy
identities, a general tight-operator-family subspace theorem, and (HS) for every finite mode type
and every real subspace.  The same module proves the weighted telescoping identity and the actual
graded-family charge bound.  `GaloisForLFunctions.HilbertMetric.SymmetricFockPhase` then proves
the rank-sensitive phase law, the rank-free universal bound (SFI), the nonnegative regime, and
the exact strict crossing criterion (SFT).  The remaining bridge is not algebraic: it is the
classification of arbitrary multilevel annihilation-invariant spaces or actual low-ambient
Gaussian configurations beyond the single-top normal form.

### Exact formal theorem surface

- `symmetricFockAnnihilation_energy`
- `symmetricFockAnnihilation_adjoint_energy`
- `tightOperatorFamily_subspace_finrank`
- `symmetricFockLoweringShadow_finrank`
- `weightedFockShadow_telescope`
- `gradedFockLoweringCharge_lower_bound`
- `gradedFockTransverseFanoMargin_rank_bound`
- `gradedFockTransverseFanoMargin_universal_bound`
- `gradedFockTransverse_negative_forces_rank_budget`
- `gradedFockTransverse_negative_forces_phase`
- `gradedFockTransverseFanoMargin_nonnegative_of_phase`
- `threeMode_gradedFockTransverseFanoMargin_nonnegative`
- `fullTopTransverse_phase_at_balance_lt_zero_iff`
- `singleTopFock_phase_threshold_rewrite`

The `threeMode` declaration refers to three active base modes in this normal form; the transverse
channel type is separate.  It must not be cited as a theorem about total ambient dimension three.

## Hostile symbolic attacks

### Sparse two-branch reuse

Coupling one high monomial chain to one low monomial chain gives one Bernoulli gap.  At the balanced
phase its forced-chain margin is `(M+L)^2/4>0`; this is already recorded on the parent Fano card.
It cannot reverse curvature.

### Many channels along one transverse variable

`[KILLED]` Distinct powers of a single transverse variable cannot provide several independent
frontier channels while reusing one chain.  The powers are totally ordered by divisibility.  The
lowering closure of the largest power already contains every smaller proposed endpoint, so the
corresponding graph vectors split and the apparent Bernoulli channels disappear.

### Parallel monomial antichains in three variables

`[OPEN, CURRENTLY POSITIVE UNDER THE LEX-SEGMENT CHARGE]` Pairing a high antichain in two variables
with a lower antichain using the third variable does create genuine unequal-gap channels.  For
consecutive lex segments, however, the lowering shadows have dimension `min(k,n+1)` across most
degrees.  Their degree charge has leading term one half of the squared endpoint degrees per
channel, whereas the balanced variance credit in (UGmin) has coefficient one quarter.  The naive
parallel-antichain family therefore remains sub-Poisson.  A proof for all three-variable inverse
systems requires the exact Macaulay-shadow inequality; a counterexample must beat it with a
non-lex multilevel coupling.

### Arbitrary commuting tuples

`[KILLED AS A PARENT THEORY]` Commutativity alone does not own the sign.  Radially weighted
symmetric modules permit decreasing inter-level weights and can make

\[
 \operatorname{tr}(Q^2)-\sum_{i,j}\lVert A_iA_j\rVert_{HS}^2
\]

negative.  Such tuples need not be restrictions of the canonical annihilators to a Fock-invariant
subspace.  Any proof of ACB-1 must use the positive CCR completion block, not simultaneous
triangularisation or a generic matrix norm inequality.

## Literature boundary checked so far

- Schoenberg infinite divisibility and Hadamard exponentials establish positive definiteness, not
  the sign of the second bandwidth derivative.
- Total positivity of the one-dimensional Gaussian kernel explains a strong ordered base case but
  does not supply a multivariate ambient-dimension theorem.
- Flat-limit Gaussian RBF work identifies polynomial interpolation ranks and asymptotics, not the
  Fano sign away from the limit.
- Arveson curvature, Hilbert polynomials of symmetric Fock modules, and trace inequalities for
  commuting tuples are adjacent operator theories.  No inspected statement gives (UG), ACB-1, or
  the least ambient dimension.
- Operator scaling supplies a parent interpretation of the one-step shadow inequality: the
  annihilation Kraus map has scalar left and right marginals, and rank-nondecreasing completely
  positive maps are established theory.  This further confirms that (HS) is infrastructure, not
  the novelty claim; the curvature and completion-budget combination remains the candidate.
- Exact searches for `Gaussian kernel determinant bandwidth log concavity`, `det exp(-t distance
  squared)`, and rank-constrained Hadamard-exponential determinant curvature found no matching
  theorem.  This is search noncollision only, not evidence of priority.

Primary adjacent sources currently in the audit:

1. Barthelme and Usevich, *Spectral properties of kernel matrices in the flat limit*,
   arXiv:1910.14067.
2. Schaback, *Limit problems for interpolation by analytic radial basis functions*.
3. Alpay, Colombo, Diki, and Sabadini, *An approach to Gaussian RBF kernels via Fock spaces*,
   arXiv:2210.14167.
4. Belton, Guillot, Khare, and Putinar, *Totally positive kernels, Polya frequency functions,
   and their transforms*, arXiv:2006.16213.
5. Fang, *Hilbert polynomials and Arveson's curvature invariant*, J. Funct. Anal. 198 (2003).
6. Misra, Pramanick, and Sinha, *A trace inequality for commuting tuple of operators*,
   arXiv:2012.11115.
7. Franks, *Operator scaling with specified marginals*, arXiv:1801.01412.

## Exact open core

1. Prove or refute ACB-1 using the CCR completion/Koszul structure of canonical annihilation
   restrictions.
2. Use the now-proved all-dimensional lowering-shadow inequality to close the remaining
   nonhomogeneous graph-coupling boundary, or exhibit an exact multilevel inverse-system falsifier.
3. Determine a rigorous upper and lower bound for the true ambient critical dimension `d_*`, with
   the completion space counted.
4. Classify equality in (HS) and (SC).  The expected rigidity statement is that, for at least two
   modes, a nonzero subspace has equality only when it is the whole symmetric-power level.  This
   would make the full-top extremizer unique rather than merely sharp.

## Anti-theatre gate

This card is not complete if it merely renames the existing degree-five construction, reports a
base dimension as an ambient dimension, or proves (UG) without using it to settle a frontier claim.
The publishable endpoint must contain a sharp universal stability/instability theorem for actual
Hilbert configurations, a dependency-closed proof, and an unconditional Lean statement matching
that theorem exactly.
