# All-replica incidence-normalized local-word leakage law

- **ID:** `all-replica-incidence-normalized-local-word-leakage-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** quantitative theorem / conditioning boundary / positive no-go survivor
- **Parents:** `all-replica-one-step-local-pauli-hall-saturation-law.md`,
  `../3-formalized/all-replica-local-casimir-hall-expansion.md`
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NO LEAN DURING ACTIVE REFACTOR]`
- **Date:** 2026-08-10

## Public sentence

Exact local expansion can be arbitrarily ill-conditioned even when every generator frame is
uniformly coercive.  For replicated qubit commutators the obstruction disappears after at most
linear local-word depth: normalized leakage across every dimension-losing incidence cut has a
constant lower bound at every replica order, with every synthesis sheet retained.

## 1. Why the one-step Casimir proposal fails

For `0 < epsilon <= 1` define two real symmetric matrices

\[
 A_1=\begin{pmatrix}\epsilon&0&1\\0&0&0\\1&0&0\end{pmatrix},
 \qquad
 A_2=\begin{pmatrix}0&0&0\\0&\epsilon&1\\0&1&0\end{pmatrix}.             \tag{1}
\]

Put `eta_epsilon(X)=A_1 X A_1+A_2 X A_2` and use Gurvits' square capacity

\[
 \operatorname{cap}(\eta_\epsilon)
 =\inf\{\det\eta_\epsilon(X):X>0,\ \det X=1\}.                           \tag{2}
\]

### Theorem A -- uniform frame coercivity and Hall do not control capacity

For every `0 < epsilon <= 1`:

1. `A_1+A_2` is invertible, so the tuple is rank nondecreasing on every subspace;
2. its quadratic frame operator `K_epsilon=A_1^2+A_2^2` obeys

   \[
   {1\over2}I\ \le K_\epsilon\le 4I;                                     \tag{3}
   \]

3. nevertheless

   \[
   \boxed{
   {\epsilon^2\over2}
   \le \operatorname{cap}(\eta_\epsilon)
   \le 2\epsilon^2.}                                                       \tag{4}
   \]

Hence no positive capacity bound can depend only on an exact Hall law and fixed upper and lower
Casimir bounds.

### Proof

The determinant of `A_1+A_2` is `-2 epsilon`.  Therefore for every subspace `U`,

\[
 (A_1+A_2)U\subseteq A_1U+A_2U
\]

has dimension `dim U`; this proves Hall.

Direct multiplication gives

\[
 K_\epsilon=
 \begin{pmatrix}
 1+\epsilon^2&0&\epsilon\\
 0&1+\epsilon^2&\epsilon\\
 \epsilon&\epsilon&2
 \end{pmatrix}.                                                            \tag{5}
\]

On the antisymmetric first-two-coordinate line its eigenvalue is `1+epsilon^2`.  On the remaining
two-dimensional space the determinant is `2` and the trace is `3+epsilon^2<=4`.  Positivity then
gives `(3)`.

For any tuple `(B_i)`, coefficient vector `c`, and invertible pencil
`B=sum_i c_i B_i`, Cauchy--Schwarz gives

\[
 BXB^*\le \|c\|_2^2\sum_i B_iXB_i^*\qquad(X>0).                            \tag{6}
\]

Determinant monotonicity therefore gives the general pencil certificate

\[
 \operatorname{cap}\!\left(X\mapsto\sum_iB_iXB_i^*\right)
 \ge { |\det B|^2\over\|c\|_2^{2d}}.                                     \tag{7}
\]

Apply `(7)` with `c=(1,1)` and `d=3` to obtain the lower bound in `(4)`.  For
`X_t=diag(t,t,t^{-2})`, `det X_t=1` and

\[
 \det\eta_\epsilon(X_t)=2(\epsilon^2+t^{-3}).                             \tag{8}
\]

Letting `t` tend to infinity proves the upper bound. `square`

This explicit degeneration kills the proposed inference

```text
uniform stacked Casimir gap + exact one-step Hall
    => replica-uniform operator-scaling capacity.
```

The missing datum is quantitative distance from a shrunk-subspace boundary, not minimum vector
energy.

## 2. Sharp bi-tight incidence leakage

Let `B=(B_a)_(a in A)` be a finite square matrix tuple on a `d`-dimensional complex Hilbert space
satisfying

\[
 \sum_aB_a^*B_a=I,
 \qquad
 \sum_aB_aB_a^*=I.                                                         \tag{9}
\]

For subspaces `U,V`, with orthogonal projectors `P_U,P_V`, define

\[
 \operatorname{Leak}_B(U,V)
 =\sum_a\|(I-P_V)B_aP_U\|_{\rm HS}^2.                                    \tag{10}
\]

### Theorem B -- dimension loss is quantitative leakage

For every `U,V`,

\[
 \boxed{
 \operatorname{Leak}_B(U,V)\ge \dim U-\dim V.}                            \tag{11}
\]

In particular every dimension-losing incidence cut leaks at least one full unit of normalized
Hilbert--Schmidt mass.

### Proof

The first equality in `(9)` gives total source energy

\[
 \sum_a\|B_aP_U\|_{\rm HS}^2=\dim U.                                     \tag{12}
\]

Removing `P_U` can only increase captured energy, while the second equality in `(9)` gives

\[
 \sum_a\|P_VB_aP_U\|_{\rm HS}^2
 \le\sum_a\|P_VB_a\|_{\rm HS}^2
 =\dim V.                                                                 \tag{13}
\]

Subtract `(13)` from `(12)`. `square`

## 3. Full-Pauli Casimir has a replica-uniform gap

Put `D=2^n`, `n>=1`, and let `R` be any finite replica set.  On
`End((C^D)^(tensor R))`, let

\[
 A_q=\operatorname{ad}\!\left(\sum_{j\in R}P_q^{(j)}\right),
 \qquad q\in\mathcal P_n\setminus\{I\},                                  \tag{14}
\]

where the phase-free Pauli matrices obey `Tr(P_qP_p)=D delta_(q,p)`.  Let

\[
 K=\sum_{q\ne I}A_q^2,
 \qquad
 \mathcal N=\bigcap_{q\ne I}\ker A_q,
 \qquad
 \mathcal Q=\mathcal N^\perp.                                             \tag{15}
\]

### Lemma C -- exact Casimir window

On `Q`,

\[
 \boxed{
 2D^2 I_\mathcal Q\le K|_\mathcal Q
 \le 4|R|^2(D^2-1)I_\mathcal Q.}                                         \tag{16}
\]

### Proof

The matrices `P_q/sqrt(D)` form an orthonormal Hermitian basis of `su(D)` after omitting the
identity.  The diagonal commutator action in `(14)` is a unitary `SU(D)` representation.  Because
it is a conjugation representation, every irreducible summand has trivial central character; its
highest weight lies in the `A_(D-1)` root lattice.  The least nonzero quadratic Casimir among
dominant root-lattice weights is the adjoint highest weight `omega_1+omega_(D-1)`, whose value in
this normalization is `2D`.  Restoring the unnormalized Pauli basis multiplies the Casimir by `D`,
giving the lower bound `2D^2` on every nontrivial summand.  The trivial summands are exactly `N`.

For the upper bound, the collective physical matrix in `(14)` has operator norm at most `|R|`, so
`||A_q||<=2|R|`.  Sum this squared bound over `D^2-1` labels. `square`

The centrality already proved for this family implies that on `Q`

\[
 B_q=K^{-1/2}A_q                                                        \tag{17}
\]

is self-adjoint and exactly bi-tight.  Theorem B and `(16)` therefore imply the unscaled estimate

\[
 \boxed{
 \sum_{q\ne I}\|(I-P_V)A_qP_U\|_{\rm HS}^2
 \ge 2D^2(\dim U-\dim V)}                                                 \tag{18}
\]

for every `U,V<=Q` with `dim U>=dim V`.  To pass from `(11)` to `(18)`, apply `(11)` to `U` and
`K^(-1/2)V`, then use

\[
 \operatorname{dist}(K^{-1/2}x,K^{-1/2}V)
 \le\|K^{-1/2}\|\operatorname{dist}(x,V).                                \tag{19}
\]

## 4. Local-word synthesis retains the full leakage mass

Let `G_2` contain the identity and every replicated Pauli commutator of physical weight one or two.
A word is a product of members of `G_2`.

### Lemma D -- unit-mass local synthesis

For every nonidentity physical Pauli label `q` there are coefficients `c_(q,w)` on words of length
at most `n` such that

\[
 A_q=\sum_w c_{q,w}W_w,
 \qquad
 \sum_w|c_{q,w}|=1.                                                        \tag{20}
\]

Words shorter than `n` may be padded by the identity.

### Proof

Weight-one and weight-two labels are generators.  For a Pauli label of weight `k>2`, use the exact
Pauli decomposition from the local Lie-generation proof:

\[
 P_q={1\over\zeta}[P_t,P_u],
 \qquad \operatorname{wt}(t)=k-1,
 \qquad \operatorname{wt}(u)=2,
 \qquad |\zeta|=2.                                                        \tag{21}
\]

The commutator representation preserves brackets, so

\[
 A_q={1\over\zeta}(A_tA_u-A_uA_t).                                       \tag{22}
\]

If the synthesis of `A_t` has coefficient `ell^1` mass one, `(22)` makes two copies, each scaled
by `1/2`; its total mass remains one.  Strong induction on physical Pauli weight proves `(20)`.
`square`

### Theorem E -- incidence-normalized local-word leakage

For every finite replica set, every `n>=1`, and every `U,V<=Q` with `dim U>=dim V`, choose the
unit-mass sheets in `(20)`.  Then

\[
 \boxed{
 {1\over D^2-1}
 \sum_{q\ne I}\sum_w |c_{q,w}|
 \|(I-P_V)W_wP_U\|_{\rm HS}^2
 \ge {2D^2\over D^2-1}(\dim U-\dim V).}                                  \tag{23}
\]

The right side is strictly larger than `2(dim U-dim V)` and is independent of replica order.

### Proof

The quotient norm and weighted Cauchy--Schwarz give, using `(20)`,

\[
 \|(I-P_V)A_qP_U\|_{\rm HS}^2
 \le\sum_w|c_{q,w}|
       \|(I-P_V)W_wP_U\|_{\rm HS}^2.                                    \tag{24}
\]

Sum `(24)` over `q`, apply `(18)`, and divide by `D^2-1`. `square`

Equation `(23)` is incidence-normalized rather than label-quotiented.  Equal words and equal
endpoints reached through different `(q,w)` sheets remain separate summands.  The target is the
actual chosen occupied subspace `V`; no ambient worst-case target replaces it.

## 5. Meaning for the static-H frontier

Theorem A retires the proposed one-step implication from rank plus a group/Casimir gap to
operator-scaling capacity.  The obstruction is real even in dimension three and cannot be repaired
by better replica bookkeeping.

Theorem E is the strongest positive survivor.  It upgrades the previous linear-depth Hall theorem
from nonzero rank to an exact constant normalized leakage budget, simultaneously for every finite
replica order.  It supplies a quantitative, multiplicity-preserving local-word invariant without a
minimum spectral-gap hypothesis.

It does **not** yet prove Brown growth.  A shallow circuit endpoint set can have full linear span, in
which case `(23)` is vacuous after replacing that set by its span.  The remaining open step is
nonlinear and Bellman-structured: transfer the sheetwise word leakage to the bounded complete
circuit-tube reporter before span scalarization.  This is narrower than the former capacity problem:
conditioning of local word generation is now closed; compatibility with recursive target
preparability is not.

## 6. Hostile audit

1. **Not a one-step theorem.**  The quantitative bound uses products of at most `n` all-to-all
   two-local generators.  One-step local-Pauli capacity remains uncontrolled and Theorem A shows why
   frame coercivity cannot control it.
2. **All-to-all two-local alphabet.**  The current unit-mass depth bound uses every physical
   weight-two Pauli direction.  A geometrically local connected graph needs a separate
   coefficient-controlled synthesis theorem; Lie generation without coefficient control is not
   enough.
3. **No circuit-union escape.**  `(23)` controls every dimension-losing linear incidence cut.  It
   does not control a nonlinear union whose occupied span is full, nor the max-plus Bellman
   reporter.
4. **No static-ensemble probability.**  The theorem is deterministic representation theory.  A
   quenched transfer from fixed random coefficients to the complete reporter is still absent.
5. **Casimir normalization is physical only up to polynomial condition.**  Equation `(16)` bounds
   that condition by `O(|R|^2)`, but a final approximate-tube theorem must propagate this distortion
   explicitly.
6. **Novelty status.**  Bi-tight leakage `(11)`, operator capacity, and Pauli Lie generation are
   individually standard.  Targeted searches found no statement combining unit-`ell^1`
   linear-depth local-Pauli synthesis, full-Casimir normalization, arbitrary replica order, and the
   incidence-normalized bound `(23)`.  This negative search is not proof of priority; specialist
   audit remains required.

## 7. Exact next conjecture

Freeze the following stronger statement; do not replace it by another span theorem.

> **Bellman-compatible sheet transfer conjecture.**  For the bounded complete circuit-incidence
> reporter and the unit-mass local-word sheets in `(20)`, the return-excised quenched static-shell
> average of the reporter's word-direction carré du champ is bounded below by a fixed fraction of
> `(23)` until Brown saturation.  The max-plus Bellman recursion then converts that dissipation into
> aggregate word-metric escape without enumerating circuit targets.

A proof must act on the complete reporter before occupied-span projection.  A counterexample must
exhibit a full-span shallow endpoint union that absorbs the normalized word carré du champ while
remaining Bellman-generated.

## 8. Immediate conjecture attack: first-order Bellman dissipation is false

Let

\[
 \mathcal B_{r,k}(u)=\sum_{j=k}^r{r\choose j}u^j(1-u)^{r-j}              \tag{25}
\]

be the bounded binomial reporter used by the complete-incidence theorem.  At an exact occupied
target `u=1`,

\[
 1-\mathcal B_{r,k}(u)
 ={r\choose k-1}(1-u)^{r-k+1}
   +O((1-u)^{r-k+2}).                                                       \tag{26}
\]

For a smooth unit-state displacement `v(delta)` through the target ray,
`1-|<v(0),v(delta)>|^2=O(delta^2)`.  Hence

\[
 1-\mathcal B_{r,k}(|\langle v(0),v(\delta)\rangle|^2)
 =O(\delta^{2(r-k+1)}).                                                     \tag{27}
\]

All derivatives of order below `2(r-k+1)` vanish at an exact shortcut.  In particular the ordinary
carré du champ is zero precisely at every exact target, independent of the transverse local-word
leakage from Theorem E.  A universal first-order Bellman-compatible lower bound is therefore
false.  This is not a technical loss: bounded-threshold reporting deliberately suppresses rare
exact-return sheets.

The first attempted positive replacement was a contact-order-matched coarea jet of order
`ell=2(r-k+1)`.  A later conjecture attack found a cleaner representation-level survivor.  The
discounted first-entrance reporter is the equilibrium potential of the target tube for the inverse
gate walk.  Its one-step Dirichlet energy is exactly discounted gate capacity, so it is not flattened
at an exact hit by the binomial reporter's contact order.  This is proved in
`first-entrance-gate-capacity-discrepancy-law.md`.

The contact-order problem is therefore retired **on the gate graph**, but the static transfer is
still open.  The live conjecture is now:

> **Directional capacity-transfer conjecture.**  After one target-independent return/carrier cut,
> transfer the incidence-normalized local-word leakage `(23)` through the first-entrance equilibrium
> potential and bound its single signed pairing with the quenched static endpoint law strongly
> enough to survive the complete circuit union.

No global resolvent norm is admissible: the capacity child proves it lower-bounds chi-squared
distance and is incompatible with low-support or singular static laws.  A valid proof must retain
the exact directional pairing, fibre sheets, and occupied endpoint image.  It must still reconcile
antisymmetric local commutator words with symmetric Fréchet jets of one static coefficient pencil;
treating the static path as a free word source remains forbidden by the crossing-memory no-go.

## Lean progress -- Theorem B, sharp bi-tight incidence leakage

`formal/GaloisForLFunctions/HTGeometry/IncidenceLeakageDimensionLoss.lean` (new, umbrella-wired,
axiom-clean) proves `(11)` in full, unconditionally.

| Card item | Declaration |
|---|---|
| the real Hilbert--Schmidt energy, and its nonnegativity from the entrywise sum | `hsSqRe`, `trace_conjTranspose_mul_self`, `hsSqRe_eq_sum`, `hsSqRe_nonneg` |
| for a projector `Q`, `‖YQ‖² = tr(Y*Y Q)` and `‖QX‖² = tr(X*QX)` | `hsSqRe_eq_trace_right`, `hsSqRe_eq_trace_left` |
| a projector splits the energy on either side -- the Pythagoras step | `hsSqRe_split_right`, `hsSqRe_split_left` |
| **`(12)`**: total emitted energy is the source dimension, from `∑ Bₐ*Bₐ = 1` | `sum_hsSqRe_mul_source` |
| **`(13)`**: total capturable energy is the target dimension, from `∑ BₐBₐ* = 1` | `sum_hsSqRe_target_mul` |
| **`(11)`**: `Leak_B(U,V) ≥ dim U − dim V` | `leak_ge_dim_sub` |

Two points the formalisation makes explicit.  The "removing `P_U` can only increase captured
energy" step of the paper proof is not a monotonicity principle but the *same* Pythagoras split
applied on the right, so the two halves of `(13)` are one lemma used twice.  And no spectral
theory, positivity ordering, or trace inequality for products of positive operators is needed
anywhere: every step is an identity between traces of explicit products, plus `hsSqRe ≥ 0`.

### What remains

Theorem A (uniform frame coercivity and Hall do not control capacity) and section 3's
replica-uniform Casimir gap, which rest on the replica tensor construction rather than on this
two-projector identity.

### Addendum -- the general pencil certificate `(6)`

`formal/GaloisForLFunctions/HTGeometry/PencilCauchySchwarz.lean` (new, umbrella-wired,
axiom-clean) proves `(6)` outright, with no hypothesis beyond `X > 0`:

| Card item | Declaration |
|---|---|
| the scalar Cauchy--Schwarz bound `‖∑ᵢ cᵢwᵢ‖² ≤ ‖c‖₂² ∑ᵢ‖wᵢ‖²` in any complex normed space | `norm_sum_smul_sq_le` |
| its unit-coefficient corollary `‖∑ᵢwᵢ‖² ≤ k ∑ᵢ‖wᵢ‖²` | `norm_sum_sq_le_card_mul` |
| the quadratic form of `NᴴN` is the squared length of `Nv` | `quadForm_conjTranspose_mul_self` |
| a congruence through a squared factor: `⟨v, MXMᴴv⟩ = ‖S Mᴴ v‖²` for `X = SS`, `Sᴴ = S` | `quadForm_congruence` |
| the pencil's square-root image is the pencil of square-root images | `sqrt_pencil_mulVec` |
| **`(6)` on quadratic forms**: `⟨v, BXBᴴv⟩ ≤ ‖c‖₂² ∑ᵢ⟨v, BᵢXBᵢᴴv⟩` for `B = ∑ᵢcᵢBᵢ`, `X > 0` | `quadForm_pencil_le` |
| **`(6)` in Loewner order**: `‖c‖₂²∑ᵢBᵢXBᵢᴴ − BXBᴴ` is positive semidefinite | `posSemidef_pencil_bound` |

The positive square root is the corpus continuous-functional-calculus root
(`positiveMatrixSqrt_posDef`, `positiveMatrixSqrt_mul_self` in
`ConstitutivePositiveConeMidpointRecovery`), so nothing spectral is assumed.

What `(7)` still needs on top of this is determinant monotonicity on the positive cone,
`0 ⪯ A ⪯ C ⟹ det A ≤ det C`, and the definition of `cap` as an infimum over the state.
