# All-replica incidence-normalized local-word leakage law

- **ID:** `all-replica-incidence-normalized-local-word-leakage-law`
- **Stage:** 3 -- formalised in Lean 4
- **Type:** quantitative theorem / conditioning boundary / positive no-go survivor
- **Parents:** `all-replica-one-step-local-pauli-hall-saturation-law.md`,
  `../3-formalized/all-replica-local-casimir-hall-expansion.md`
- **Status:** `[LEAN-PROVED] [FRONTIER ADVANCE] [NOVELTY PROVISIONAL]`
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

### Addendum -- `(7)` is now closed

`(7)` needed determinant monotonicity on the positive cone, which mathlib does not carry.  Two new
umbrella-wired, axiom-clean modules supply it and then finish the certificate.

`formal/GaloisForLFunctions/HTGeometry/PositiveConeDeterminantMonotone.lean`:

| Step | Declaration |
|---|---|
| a nonzero vector has positive squared length | `dotProduct_star_self_pos` |
| **below the identity every eigenvalue is at most one** | `eigenvalues_le_one_of_one_sub_posSemidef` |
| hence a matrix squeezed between `0` and `1` has determinant at most `1` | `det_le_one_of_le_one` |
| the kernel of the larger matrix sits inside the kernel of the smaller | `mulVec_eq_zero_of_loewner` |
| **`0 ⪯ A ⪯ C ⟹ det A ≤ det C`** | `det_le_det_of_loewner` |

The singular and invertible cases are both handled: if `det C = 0` the shared kernel forces
`det A = 0`, and otherwise `C = S S` for the positive square root `S`, `T = S⁻¹AS⁻¹` satisfies
`0 ⪯ T ⪯ 1`, and `det A = det C · det T ≤ det C`.

`formal/GaloisForLFunctions/HTGeometry/PencilCapacityCertificate.lean`:

| Step | Declaration |
|---|---|
| nonnegative real multiples preserve positive semidefiniteness | `posSemidef_real_smul` |
| a Kraus sum of a positive state is positive | `posSemidef_krausSum` |
| **`(7)`**: at every `X > 0` with `det X = 1`, `det(∑ᵢBᵢXBᵢᴴ) ≥ \|det B\|²/‖c‖₂^{2d}` | `pencil_capacity_bound` |

Since Gurvits' square capacity `(2)` is the infimum of `det η(X)` over exactly that competitor set,
`pencil_capacity_bound` is the assertion `cap ≥ |det B|²/‖c‖₂^{2d}` of `(7)`, with no hypothesis
beyond `X > 0`, `det X = 1` and `c ≠ 0`.

### Addendum -- Theorem A is closed

`formal/GaloisForLFunctions/HTGeometry/LocalPauliCapacityDegeneration.lean` (new, umbrella-wired,
axiom-clean) proves every clause of Theorem A for the explicit seed pair `(1)`.

| Card item | Declaration |
|---|---|
| the seeds `A₁`, `A₂` of `(1)` and their self-adjointness | `hallSeedA₁`, `hallSeedA₂`, `hallSeedA₁_conjTranspose`, `hallSeedA₂_conjTranspose` |
| **clause 1**: `det(A₁+A₂) = -2ε`, so the sum is invertible and the tuple is rank nondecreasing | `hallSeedSum_det` |
| the frame operator `K_ε` in the closed form `(5)` | `hallSeedFrame`, `hallSeedFrame_eq` |
| **clause 2, `(3)`**: `½I ⪯ K_ε` and `K_ε ⪯ 4I` for `0 < ε ≤ 1` | `hallSeedFrame_lower`, `hallSeedFrame_upper` |
| **clause 3, lower half of `(4)`**: `ε²/2 ≤ det η_ε(X)` at every `X > 0` with `det X = 1` | `hallSeedCapacity_lower` |
| the competitor family `Xₜ = diag(t,t,t⁻²)`, positive of unit determinant | `hallSeedState`, `hallSeedState_posDef`, `hallSeedState_det` |
| **`(8)`**: `det η_ε(Xₜ) = 2(ε² + t⁻³)` exactly | `hallSeedKraus_det` |
| **clause 3, upper half of `(4)`**: competitor values reach into every `(2ε², 2ε²+δ)` | `hallSeedCapacity_upper` |

Two pieces of reusable infrastructure came out of it:

- `posSemidef_arrow3` -- a symmetric arrow matrix `!![a,0,b; 0,a,b; b,b,c]` is positive semidefinite
  as soon as `a > 0` and `ac ≥ 2b²`.  The certificate is the rank-one decomposition by the two arrow
  rows plus the corner remainder, so it needs no square root and no eigenvalue computation.
- `det_arrow3` -- the determinant of that shape is `a(ac - 2b²)`.

The lower bound is `pencil_capacity_bound` at `c = (1,1)`, `d = 3`: the pencil is `A₁+A₂` with
`‖det‖² = 4ε²` and `‖c‖₂^{2d} = 8`, giving exactly `ε²/2`.  The Casimir window uses `posSemidef_arrow3`
twice, with `ac - 2b² = ¾ - ½ε²` for the lower bound and `2(3-ε²) - 2ε²` for the upper.

Card status: Theorem A, Theorem B, `(6)` and `(7)` are all formal.  Lemma C (the replica-uniform
full-Pauli Casimir window), Lemma D (unit-mass local synthesis) and Theorem E (incidence-normalized
local-word leakage) remain.

### Addendum -- Lemma D's engine, `(24)`, `(23)`, and the upper half of `(16)`

Two further umbrella-wired, axiom-clean modules.

`formal/GaloisForLFunctions/HTGeometry/UnitMassWordLeakage.lean`:

| Card item | Declaration |
|---|---|
| unit-mass Jensen in any complex normed space: `‖∑cᵢxᵢ‖² ≤ ∑‖cᵢ‖‖xᵢ‖²` when `∑‖cᵢ‖ = 1` | `norm_sum_sq_le_weighted` |
| the same for Hilbert--Schmidt energy | `hsSqRe_sum_le_weighted` |
| **`(24)`**: `‖(I-P_V)(∑c_w W_w)P_U‖²_HS ≤ ∑_w \|c_w\| ‖(I-P_V)W_wP_U‖²_HS` | `leak_sum_le_weighted` |
| **`(23)`**: the label-summed lower bound transfers to the normalized word-level sum | `incidenceNormalized_leakage_ge` |
| the notion of a unit-mass synthesis over a word set, `(20)` | `HasUnitMassSynthesis`, `hasUnitMassSynthesis_of_mem` |
| **the inductive step of Lemma D**: unit mass survives `ζ⁻¹(ab-ba)` when `‖ζ‖ = 2` and the word set is product-closed | `hasUnitMassSynthesis_bracket` |

`hasUnitMassSynthesis_bracket` is exactly the card's argument for `(22)`: the bracket makes two
copies of the product family and `‖ζ⁻¹‖ = ½` halves each, so the total mass `½·1·1 + ½·1·1` is again
one.  Strong induction on Pauli weight is then a finite recursion over this step, and the base cases
are `hasUnitMassSynthesis_of_mem` for weight-one and weight-two labels.

`formal/GaloisForLFunctions/HTGeometry/OperatorSquareNormBound.lean`:

| Card item | Declaration |
|---|---|
| the quadratic form of the identity | `quadForm_one` |
| a self-adjoint operator of norm `≤ M` has `A² ⪯ M²` | `posSemidef_sq_le_of_bound` |
| **the upper half of `(16)`**: a family of `card` such operators has `∑A_q² ⪯ card·M²` | `posSemidef_sum_sq_le_of_bound` |

With `M = 2\|R\|` and `card = D²-1` this is `K ⪯ 4\|R\|²(D²-1)`, the upper Casimir bound of `(16)`.

### What remains on this card

Only the **lower** half of `(16)`, `2D²I_Q ⪯ K|_Q`.  The card derives it from the least nonzero
quadratic Casimir of `SU(D)` on the root lattice, which is Lie-theoretic input mathlib does not
carry.  Everything downstream of it -- `(18)` via Theorem B, `(19)`, and `(23)` via `(24)` -- is
already formal, as is the whole of section 1 (Theorem A) and section 2 (Theorem B).

For the one-replica case the lower bound is elementary rather than Lie-theoretic: the Pauli
depolarizing identity gives `K = 2D²·id - 2D·tr(·)I` exactly, so `K` is exactly `2D²` on the
traceless space.  The corpus already carries the Pauli basis, orthogonality, involution and
tracelessness facts (`FiniteQubitPauliBasisLaw`) and the collective-Casimir centrality
(`AllReplicaCollectivePauliCasimir`), so that specialization is the natural next step.

### Addendum -- the one-replica lower half of `(16)`, exactly

`formal/GaloisForLFunctions/HTGeometry/FinitePauliDepolarizing.lean` (new, umbrella-wired,
axiom-clean) proves the elementary route the card names: at one replica the Casimir is not merely
bounded below by `2D²` on `Q`, it *equals* `2D²` there.

| Card item | Declaration |
|---|---|
| the single-qubit swap identity `∑_p p_{ab} p_{cd} = 2 δ_{ad} δ_{bc}` | `sum_boolPauliOption_entry_mul` |
| its register form `∑_L (P_L)_{ru}(P_L)_{vc} = 2^n δ_{rc} δ_{uv}` | `sum_finitePauliMatrix_entry_mul` |
| **the Pauli depolarizing identity** `∑_L P_L X P_L = 2^n (Tr X) I` — the exact one-design property of the full Pauli family | `sum_finitePauliMatrix_conj` |
| the commutator action and its square `ad(P)²X = 2X − 2PXP` for an involution | `pauliAd`, `pauliAd_sq` |
| **the full-Pauli Casimir at one replica**: `K X = 2D² X − 2D (Tr X) I` | `sum_pauliCasimir_eq` |
| **`(16)`, lower half at one replica**: `K X = 2D² X` on the traceless operators | `sum_pauliCasimir_traceless` |

The identity Pauli label contributes `ad(1) = 0`, so summing over *all* `4^n` labels is the same as
summing over the `D²−1` nonidentity ones; that is what makes the depolarizing identity applicable
without excising a label.  Since `N = ⋂_q ker A_q` is the scalar line and `Q = N^⊥` is the traceless
space, `sum_pauliCasimir_traceless` is exactly `2D² I_Q = K|_Q`, with the sharp constant.

The register form is proved by turning the label sum into a product of local sums
(`Finset.prod_univ_sum` over `Fintype.piFinset`), so no representation theory and no root-lattice
input is used at one replica.

### What remains on this card

The lower half of `(16)` for a general replica set `R`.  The collective generator
`∑_{j∈R} P_q^{(j)}` is not an involution, so the depolarizing route above does not transfer
verbatim; the card's own derivation from the least nonzero quadratic Casimir of `SU(D)` on the root
lattice is Lie-theoretic input mathlib does not carry.  Everything else on the card -- Theorem A,
Theorem B, `(6)`, `(7)`, the upper half of `(16)`, `(23)`, `(24)`, Lemma D's engine, and now the
one-replica lower half of `(16)` -- is Lean-proved and axiom-clean.

### The remaining item, stated exactly

Under the isomorphism `End(V^{⊗R}) ≅ End(V)^{⊗R}` the collective adjoint action is `Ad(U)^{⊗R}`,
so with `W = End(V) = triv ⊕ ad` the whole space grades as `⊕_{S ⊆ R} ad^{⊗S}` and `K` restricted
to `ad^{⊗S}` is the total Casimir of `|S|` adjoint factors.  The one-replica module
`FinitePauliDepolarizing` already gives the single-factor value exactly:
`sum_pauliCasimir_traceless` says `K = 2D²` on `ad`, i.e. `c = 2D²(id − Π_scalar)` on `W`.

So the *only* open statement is:

> for every `m ≥ 1`, every nonzero eigenvalue of the total Casimir on `ad^{⊗m}` is at least `2D²`.

Equivalently: every nonzero dominant weight of `su(D)` lying in the root lattice has quadratic
Casimir at least that of the highest root.  That is a weight-theoretic fact -- the dominance order
puts the highest root below every other nonzero dominant root-lattice weight, and `⟨λ,λ+2ρ⟩` is
monotone for that order -- and mathlib carries neither highest-weight theory for compact groups nor
the Casimir eigenvalue formula.  Building it is the remaining Lean dependency of this card; nothing
else on the card is open.

The two-factor case is already tight, so no slack is available: for `su(2)` the spectrum of `K` on
`ad ⊗ ad` is `{0, 2D², 3·2D²}` with `D = 2`, so any proof must produce the constant `2D²` exactly
rather than an estimate.

## Lean progress -- the lower half of `(16)` at every replica order

The card's last open mathematical item is closed.  Six new umbrella-wired, axiom-clean modules
prove that every nonzero eigenvalue of the full-Pauli collective Casimir is at least `2D²`, at every
finite replica order and for every `D = 2^n`.

`formal/GaloisForLFunctions/HTGeometry/WeightCasimirGap.lean`:

| Card item | Declaration |
|---|---|
| the Casimir value of a weight: sum of squares plus the sum of ordered differences | `weightCasimir` |
| **the weight gap**: a nonzero decreasing zero-sum integer weight has Casimir value at least `2D` | `two_mul_card_le_weightCasimir` |

`formal/GaloisForLFunctions/HTGeometry/MatrixUnitCasimir.lean`:

| Card item | Declaration |
|---|---|
| the coordinate inner product and square norm, and the adjoint law | `cinner`, `cnormSq`, `cinner_mulVec`, `cinner_self`, `cnormSq_eq_zero_iff` |
| the bracket relations of a matrix-unit family and its quadratic Casimir | `IsMatrixUnitFamily`, `familyCasimir`, `familyCasimir_conjTranspose` |
| **the Casimir is central**, by the index cancellation of the structure constants | `familyCasimir_commute` |
| **the Casimir energy is the total family energy** | `cinner_familyCasimir` |

`formal/GaloisForLFunctions/HTGeometry/MatrixUnitWeightSystem.lean`:

| Card item | Declaration |
|---|---|
| one raising step of a weight, and its involutivity | `shiftWeight`, `shiftWeight_involutive` |
| a weight system: diagonal Cartan, one-step shift, zero total weight | `IsWeightSystem` |
| pure-weight vectors, weight projections, and the weight decomposition | `HasWeight`, `wproj`, `weightSet`, `sum_wproj` |
| **a generator moves a pure weight by one step** | `hasWeight_mulVec` |
| **the Casimir preserves pure weights** | `hasWeight_casimir` |

`formal/GaloisForLFunctions/HTGeometry/MatrixUnitCasimirGap.lean`:

| Card item | Declaration |
|---|---|
| a strictly antitone integer ranking of the alphabet, and the induced weight functional | `alphaRank`, `alphaRank_lt`, `weightRank`, `weightRank_shiftWeight` |
| **weight components of an eigenvector are eigenvectors** | `wproj_eigen` |
| **the spectral gap**: every nonzero Casimir eigenvalue is at least twice the alphabet size | `casimir_eigenvalue_gap` |

`formal/GaloisForLFunctions/HTGeometry/CollectiveReplicaWeightGap.lean`:

| Card item | Declaration |
|---|---|
| the one-copy matrix unit, its adjoint and its product law | `unitMatrix`, `unitMatrix_conjTranspose`, `unitMatrix_mul`, `unitMatrix_bracket` |
| the letter counts of a replica word, and their total | `siteCount`, `siteCount_erase`, `sum_siteCount` |
| the collective lift of a matrix unit | `collUnit`, `collUnit_apply`, `collUnit_conjTranspose`, `collUnit_bracket` |
| **the Cartan lift is diagonal with the letter counts as entries** | `collUnit_diag` |
| **a raising lift shifts the letter counts by one step** | `collUnit_shift` |
| the vectorized collective family and its adjoint law | `collGen`, `collGen_apply`, `collGen_conjTranspose` |
| **it is a matrix-unit family with a weight system** | `isMatrixUnitFamily_collGen`, `collWeight`, `isWeightSystem_collGen` |
| **the collective Casimir gap** | `collectiveCasimir_eigenvalue_gap` |

`formal/GaloisForLFunctions/HTGeometry/FullPauliCasimirGap.lean`:

| Card item | Declaration |
|---|---|
| **single-qubit Pauli completeness** `∑_m (σ_m)_{ab}(σ_m)_{cd} = 2δ_{ad}δ_{bc}` | `sum_pauli1_entry_mul` |
| its register and reindexed forms, with the factor `2^n` | `sum_pauliStr_entry_mul`, `sum_pauliMat_entry_mul` |
| the collective commutator representation and its expansion in matrix units | `collRho`, `matrix_expand`, `collRho_expand`, `collRho_mul_expand` |
| the identity label contributes nothing | `collRho_one`, `pauliMat_zero_eq_one` |
| **`K = D · C`**: the full-Pauli Casimir is the matrix-unit Casimir scaled by the one-copy dimension | `fullPauliCasimir_eq_smul` |
| **`(16)`, lower half**: every nonzero eigenvalue of `K` is at least `2D²`, at every replica order | `fullPauliCasimir_eigenvalue_gap` |

The card derives the lower half of `(16)` from the least nonzero quadratic Casimir of `SU(D)` on the
root lattice.  The formalisation replaces that Lie-theoretic input by an elementary three-step
argument that mathlib can carry:

1. **Highest weight without highest-weight theory.**  The Casimir commutes with every generator, so
   each eigenspace is graded by the integer weights `count(row) − count(column)`.  Among the weights
   realised in one eigenspace, a strictly antitone ranking functional has a maximiser, and a vector
   of that weight is annihilated by every raising generator -- because its image would carry a
   strictly larger rank inside the same eigenspace.

2. **The eigenvalue is the weight's own Casimir value.**  For such a vector the bracket relation
   `[E_ab, E_ba] = E_aa − E_bb` turns the energy of each lowering generator into the corresponding
   ordered weight difference, so the Casimir eigenvalue is `∑_a μ_a² + ∑_{a<b}(μ_a − μ_b)` and the
   weight is decreasing with zero total.

3. **The gap is a counting inequality.**  For a nonzero decreasing zero-sum integer vector, the
   squares contribute at least twice the positive mass `A`, and the ordered differences at least
   `(D + z)A` where `z` counts the zeros; since `2A` is at least the number of nonzero entries, the
   two contributions add to at least `2D`.

No root system, no highest-weight module, and no invariant measure appears.  Step 1 uses only the
commutation of the Casimir with the family, which is itself the index cancellation
`familyCasimir_commute`.  Passing from the matrix-unit Casimir to the card's Pauli Casimir is the
completeness relation `∑_q (P_q)_{ij}(P_q)_{kl} = D δ_{il} δ_{jk}`, proved from the sixteen-case
single-qubit identity by taking products over the register.

`#print axioms` on all of these: `propext`, `Classical.choice`, `Quot.sound` only.

### What remains on this card

A correction to the previous entry, which recorded `(18)` as already formal.  Auditing the tree
shows that `(18)` itself is *not* a Lean theorem: its ingredients are --
`IncidenceLeakageDimensionLoss.leak_ge_dim_sub` for `(11)`,
`CentralCasimirComplementHallExpansion.completedHermitianFamily_scaled_biTight` for the exactly
bi-tight scaled family, and `UnitMassWordLeakage.incidenceNormalized_leakage_ge`, which consumes
`(18)` as a hypothesis and produces `(23)` -- but the assembly between them is missing.

That assembly is exactly `(19)`: with `B_q = K^{-1/2}A_q`, apply `(11)` to `U` and `K^{-1/2}V`, then
transfer through `dist(K^{-1/2}x, K^{-1/2}V) ≤ ‖K^{-1/2}‖ dist(x, V)` and the operator-norm bound
`‖K^{-1/2}‖² ≤ (2D²)^{-1}` on `Q`, which is what the eigenvalue gap above supplies.  The scalar route
is not available: bounding the captured energy by `Tr(P_V K P_V)` costs the *upper* Casimir constant
`4|R|²(D²−1)` instead of `2D²`, so the inverse-square-root normalisation is genuinely required.

So the card's mathematical content is complete -- Theorem A, Theorem B, `(6)`, `(7)`, both halves of
`(16)` at every replica order, `(23)`, `(24)` and Lemma D's engine are all Lean-proved -- and the
only remaining Lean work is the continuous-functional-calculus transfer `(19)` that turns the
now-proved gap into the leakage estimate `(18)`.

## Lean progress -- `(19)`, `(18)`, Lemma D and Theorem E: the card is closed

Eight further umbrella-wired, axiom-clean modules complete the card.  `#print axioms` on every
declaration below returns `propext`, `Classical.choice`, `Quot.sound` only.

### The spectral upgrade: from an eigenvalue gap to an operator inequality

`formal/GaloisForLFunctions/HTGeometry/SpectralGapQuadraticForm.lean`

| Card item | Declaration |
|---|---|
| the coordinate inner product is the Euclidean one | `cinner_eq_inner` |
| **eigenvalue gap ⟹ form gap**: if every eigenvalue of a Hermitian `T` is `0` or `≥ g`, then `g‖z‖² ≤ ⟪z,Tz⟫` at every `z ⊥ ker T` | `cnormSq_le_of_eigenvalue_gap` |

The proof expands `z` in `Matrix.IsHermitian.eigenvectorBasis`: the coefficients along kernel
eigenvectors vanish because `z` is orthogonal to the kernel, and every surviving coefficient is
weighted by an eigenvalue past `g`.  This is the step that converts `fullPauliCasimir_eigenvalue_gap`,
which constrains eigenvalues one at a time, into a statement usable on a whole subspace.

`formal/GaloisForLFunctions/HTGeometry/CoordinateInnerProductToolkit.lean`

| Card item | Declaration |
|---|---|
| Hilbert--Schmidt energy is the total column square norm | `hsSqRe_eq_sum_col` |
| **a vectorwise contraction rescales Hilbert--Schmidt energy**: `cnormSq(Mv) ≤ c·cnormSq v` for all `v` gives `hsSqRe(MY) ≤ c·hsSqRe Y` | `hsSqRe_mul_le` |
| Pythagoras for a Hermitian idempotent | `cnormSq_split_of_hermitian_idem` |
| **the Casimir form is the family energy**: `Re⟪v,Kv⟫ = ∑_q ‖A_q v‖²` | `cinner_casimir_re` |

### `(19)`: transporting the target along the normalization

`formal/GaloisForLFunctions/HTGeometry/ImageProjectionTrace.lean`

| Card item | Declaration |
|---|---|
| the trace of an idempotent is the dimension of its range | `trace_eq_finrank_range` |
| the orthogonal projector onto `R·V` | `imageProjection` |
| it is a self-adjoint idempotent | `imageProjection_conjTranspose`, `imageProjection_mul_self` |
| **the key annihilation** `(I-P_W)·R·P_V = 0` | `one_sub_imageProjection_mul` |
| **transport costs no dimension**: `Tr P_W = Tr P_V` for invertible `R` | `imageProjection_trace` |

This is the exact content of `(19)`.  The card phrases it as the distance inequality
`dist(K^{-1/2}x, K^{-1/2}V) ≤ ‖K^{-1/2}‖ dist(x,V)`; in the matrix formulation the same fact is the
pair "the complementary image projector annihilates `R P_V`" and "the image projector has the same
trace", which is what the leakage bound actually consumes.

`formal/GaloisForLFunctions/HTGeometry/ScaledCasimirCompletion.lean`

| Card item | Declaration |
|---|---|
| the family completed by `√g` times its kernel projector | `scaledCompletedFamily` |
| its Casimir is `g·P_N + K`, central, with trivial simultaneous kernel | `scaledCompletedFamily_casimir`, `_central`, `_commonKernel_eq_bot` |
| **`(17)`**: the normalized completion is exactly bi-tight | `scaledCompletedFamily_biTight` |
| the completed Casimir dominates `g` on the *whole* space | `scaledCompletedFamily_form_ge` |
| **the operator-norm bound `‖K^{-1/2}‖² ≤ g^{-1}`** | `cnormSq_invSqrtScale_mulVec_le` |

Completing with `√g·P_N` rather than `P_N` is what removes the restriction to `Q` from the norm
bound: on the singlet sector the completed Casimir is `g` exactly, so the inverse square root is a
uniform contraction by `g^{-1/2}` everywhere, and no separate `Q`-restriction has to be threaded
through the leakage estimate.

### `(18)`: the gap is a leakage budget

`formal/GaloisForLFunctions/HTGeometry/NormalizedCasimirLeakage.lean`

| Card item | Declaration |
|---|---|
| the Casimir of a Hermitian family is Hermitian | `matrixFamilyCasimir_isHermitian` |
| `Kw = 0` puts `w` in the simultaneous kernel | `commonKernelProjection_mulVec_eq_self_of_casimir_zero` |
| **eigenvalue gap ⟹ form gap off the simultaneous kernel** | `commonKernelProjection_form_ge_of_eigenvalue_gap` |
| `P_N P_U = 0` is exactly `U ≤ Q` | `commonKernelProjection_mul_eq_zero_iff` |
| **`(18)`, abstractly**: `g(dim U − dim V) ≤ ∑_q ‖(I−P_V)A_qP_U‖²_HS` | `hermitianCentralFamily_leak_ge_gap_mul_dim_sub` |

`formal/GaloisForLFunctions/HTGeometry/AllReplicaPauliLeakageLaw.lean`

| Card item | Declaration |
|---|---|
| **`(18)`**: `2D²(dim U − dim V) ≤ ∑_{q≠I} ‖(I−P_V)A_qP_U‖²_HS` at every replica order | `finiteAllReplicaFullPauli_leak_ge_dim_sub` |
| **`(23)` from a synthesis, at any positive normalization** | `finiteAllReplicaFullPauli_incidenceNormalized_leakage_ge` |
| **`(23)` at the label count `D²−1`** | `finiteAllReplicaFullPauli_leakage_budget` |

The formal `(18)` is slightly stronger than the card's: the target projector `V` need not lie in
`Q`.  Only the source condition `P_N P_U = 0` is used, to kill the adjoined kernel term.

### Lemma D, in full

`formal/GaloisForLFunctions/HTGeometry/LocalPauliUnitMassSynthesis.lean`

| Card item | Declaration |
|---|---|
| enlarging the word set preserves a synthesis | `hasUnitMassSynthesis_mono` |
| **`(22)` with word length added**: unit mass survives `ζ⁻¹(ab−ba)` from a length-`k` and a length-`l` factor into length `k+l` | `hasUnitMassSynthesis_bracket_of_mem` |
| padding by the identity embeds shorter words among longer | `setPow_subset_setPow` |
| **`(21)`**: the replicated commutator directions close under the bracket with the physical Pauli phase as the single coefficient | `replicaCommutatorMat_bracket` |
| `\|ζ\| = 2` for anticommuting strings | `norm_pauliPhase_sub` |
| **Lemma D, `(20)`**: every replicated Pauli direction of physical weight `w` is a unit-mass combination of words of length at most `w` | `replicaCommutatorMat_hasUnitMassSynthesis` |
| **Lemma D at the uniform depth `n`** | `finiteReplicaFullPauliCommutatorMatrix_hasUnitMassSynthesis` |

The word set is `G₂ = {I} ∪ {A_s : s ≠ 0, wt(s) ≤ 2}` and word length is the pointwise set power
`G₂^k`.  Strong induction on physical Pauli weight uses the corpus's own decomposition
`exists_pauliWeightTwo_anticommuting_decomposition` (a strictly lighter `t` and a weight-two `u`
with `ω(t,u) = 1` and `t ⊕ u = s`), so the depth increases by exactly one per weight step and the
final bound is `wt(s) ≤ n` -- the card's linear depth, retained.

### Theorem E, unconditionally

`formal/GaloisForLFunctions/HTGeometry/AllReplicaIncidenceNormalizedWordLeakage.lean`

| Card item | Declaration |
|---|---|
| one index set serving every label at once | `exists_uniformUnitMassSynthesis` |
| **Theorem E, `(23)`**, with no synthesis hypothesis | `finiteAllReplicaFullPauli_incidenceNormalized_wordLeakage` |

Lemma D produces a separate index set per label; summing them over the label set and extending each
coefficient family by zero off its own fibre gives one index set carrying every synthesis at once,
with unit mass preserved.  Theorem E is then a statement with no hypotheses beyond `n ≥ 1`, the
idempotency of the two projectors, self-adjointness of the source, and `P_N P_U = 0`:

> there are coefficients `c_{q,w}` on words `W_{q,w}` of length at most `n` in the identity and the
> replicated one- and two-local Pauli commutator directions, with `∑_w |c_{q,w}| = 1` and
> `A_q = ∑_w c_{q,w} W_{q,w}` for every label, such that
> `2D²(dim U − dim V)/(D²−1) ≤ (∑_q ∑_w |c_{q,w}| ‖(I−P_V)W_{q,w}P_U‖²_HS)/(D²−1)`.

### Card status

Closed.  Theorem A, Theorem B, `(6)`, `(7)`, Lemma C `(16)` (both halves, every replica order),
`(17)`, `(18)`, `(19)`, Lemma D `(20)`--`(22)`, `(24)` and Theorem E `(23)` are all Lean-proved and
axiom-clean.  Nothing on the card is open; the open items named in section 5 and section 7 are the
card's forward conjecture, not part of its own statement.
