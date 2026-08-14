# Character-twisted coinvariants, complete Laplace--Fisher reconstruction, and origin-atom properness

- **ID:** ULF-SRSM-10
- **Stage:** 2 — fully proven on paper
- **Type:** FUSION THEOREM / RECONSTRUCTION LAW / FORMATION-PROPERNESS CLASSIFICATION
- **Sources:** ULF-SRSM-8 base-norm probability formation; ULF-SRSM-9 normalized-jet and
  Markov-coinvariant law; Generative Response Mechanics; positive inverse-Gram mechanics
- **Statement:** Universal Markov invariance sees only mass, but source-character covariance
  produces a complete spectral cotangent atlas.  On the additive half-line, the countable integer
  Laplace characters jointly reconstruct every finite zero-mass signed current.  For an `L^2`
  score current, the supremum of the finite inverse covariance-Gram response energies is exactly
  Fisher information.  Convolution acts diagonally on this response atlas, and its action on the
  `c_0` response completion is bounded below exactly when the formation law retains positive mass
  at zero delay.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [MECHANISM LEVEL]`
  `[THREE-ORGAN FUSION + FOURTH-ORGAN PREDICTION] [COMPLETE VERTICAL RECONSTRUCTION]`
  `[EXACT FISHER CONSERVATION] [ORIGIN-ATOM PROPERNESS CLASSIFICATION]`
  `[LEAN CORPUS AUDITED READ-ONLY; NO LEAN WRITE/BUILD] [PRE-RH] [NOT RH]`

## 1. Higher pivot: covariance, not invariance

ULF-SRSM-9 proves that a linear reporter invariant under **every** Markov refinement factors
through total mass.  It therefore annihilates every normalized shape tangent.  The failed move was
to search for a more ingenious universally invariant scalar.

The source already supplies a smaller and richer symmetry: additive formation time.  Its
one-dimensional characters are

\[
 \chi_z(x)=e^{-zx}\qquad (z\ge0).
 \tag{CTL.1}
\]

They are not invariant under convolution.  They are covariant eigen-reporters.  The correct
replacement for the Markov coinvariant is therefore a **character-twisted coinvariant**.

This change is load-bearing.  Universal invariance collapses the whole normalized vertical fibre
to zero; the complete character family reconstructs that fibre and its Fisher metric exactly.

## 2. Algebraic character-twisted coinvariants

Let `M` be a commutative monoid with identity written `0`, `k` a field, and let `chi` be a unital
monoid homomorphism from `M` to the multiplicative monoid of `k`.  Let `k[M]` have basis
`(e_m)_(m in M)`.  The
regular action is

\[
 \rho(a)e_m=e_{a+m}.
 \tag{CTL.2}
\]

For a character `chi:M->k` define

\[
 N_\chi=operatorname{span}\{\rho(a)v-\chi(a)v:a\in M,\ v\in k[M]\}
 \tag{CTL.3}
\]

and the character reporter

\[
 \tau_\chi\!\left(\sum_ma_me_m\right)=\sum_ma_m\chi(m).
 \tag{CTL.4}
\]

### Theorem 2.1 — exact regular twisted quotient

For every character,

\[
 \boxed{\ker\tau_\chi=N_\chi,\qquad k[M]/N_\chi\simeq k.}
 \tag{CTL.5}
\]

More generally, a linear functional `tau` satisfies

\[
 \tau\rho(a)=\chi(a)\tau\quad(a\in M)
 \tag{CTL.6}
\]

if and only if it factors through the twisted quotient `k[M]/N_chi`.

### Proof

Multiplicativity of `chi` gives

\[
 \tau_\chi(\rho(a)e_m-\chi(a)e_m)
 =\chi(a+m)-\chi(a)\chi(m)=0,
\]

so `N_chi` is contained in the kernel.  Conversely,

\[
 e_m-\chi(m)e_0=\rho(m)e_0-\chi(m)e_0\in N_\chi.
\]

For `v=sum a_m e_m`,

\[
 v-\tau_\chi(v)e_0=\sum_ma_m(e_m-\chi(m)e_0)\in N_\chi.
\]

If `tau_chi(v)=0`, this says `v in N_chi`.  Equation `(CTL.6)` is equivalent to annihilating every
generator of `(CTL.3)`.  QED.

### Finite-support reconstruction

For `M=N^d` and `k=C`, the family of all characters jointly reconstructs `k[M]`: a finite vector
is a polynomial, and its values on all `z in C^d` determine every coefficient.  A single twisted
quotient is one-dimensional; the complete character spectrum is coefficient-faithful.

This algebra is classical.  Its role here is structural: it identifies exactly why one invariant
reporter is too small and what source-generated replacement can be complete.

## 3. Complete integer-Laplace tomography of vertical currents

Let `J` be a finite real signed Borel measure on `[0,infinity)` with

\[
 J([0,\infty))=0.
 \tag{CTL.7}
\]

Define its integer character responses

\[
 b_n(J)=\int_0^\infty e^{-nx}\,dJ(x),\qquad n\ge1.
 \tag{CTL.8}
\]

### Theorem 3.1 — countable complete vertical reporter

\[
 \boxed{b_n(J)=0\ \text{for every }n\ge1\quad\Longrightarrow\quad J=0.}
 \tag{CTL.9}
\]

Thus

\[
 \mathcal T:J\longmapsto (b_n(J))_{n\ge1}
 \tag{CTL.10}
\]

is injective on the full space of finite zero-mass signed currents.  No absolute continuity,
moment condition, or analyticity hypothesis is required.

### Proof

Push `J` forward by the homeomorphism

\[
 q:[0,\infty)\longrightarrow(0,1],\qquad q(x)=e^{-x},
\]

and extend the resulting finite signed measure `eta` to `[0,1]` by assigning zero mass to `{0}`.
Equation `(CTL.7)` is the zeroth moment and `(CTL.8)` gives every positive integer moment:

\[
 \int_0^1y^n\,d\eta(y)=0\qquad(n\ge0).
\]

Hence `eta` annihilates every polynomial.  By Stone--Weierstrass, polynomials are uniformly dense
in `C([0,1])`; finiteness of total variation implies that `eta` annihilates every continuous
function.  Riesz uniqueness gives `eta=0`, hence `J=0`.  QED.

### Sharp boundaries

1. Zero mass is load-bearing if the `n=0` response is omitted.
2. One reporter is never complete on an infinite-dimensional current space.
3. Any infinite set of nonnegative integer exponents containing zero and generating a uniformly
   dense polynomial algebra after compactification works; the consecutive integer family is the
   canonical countable choice.
4. The theorem reconstructs a signed current, not merely a probability law.

## 4. Exact Fisher reconstruction from inverse response Grams

Let `P` be a probability measure on `[0,infinity)`.  Put

\[
 L_P(n)=\int e^{-nx}\,dP(x),
 \qquad
 \phi_n(x)=e^{-nx}-L_P(n).
 \tag{CTL.11}
\]

Let

\[
 H_P=L^2_0(P)=\{u\in L^2(P):\mathbb E_Pu=0\}.
\]

A normalized differentiable statistical current has the form `J=uP`; its Fisher mass is

\[
 \mathcal I_P(J)=\|u\|_{L^2(P)}^2.
 \tag{CTL.12}
\]

The character response is

\[
 b_n(J)=\langle u,\phi_n\rangle_{L^2(P)}.
 \tag{CTL.13}
\]

For a nonempty finite set `F subset N_(>=1)`, define

\[
 G_F(m,n)=\langle\phi_m,\phi_n\rangle
 =L_P(m+n)-L_P(m)L_P(n),
 \tag{CTL.14}
\]

and let `b_F=(b_n)_(n in F)`.  Write `G_F^dagger` for the Moore--Penrose inverse.

### Theorem 4.1 — Laplace--Fisher conservation identity

The centered integer characters span a dense subspace of `H_P`, and for every `u in H_P`,

\[
 \boxed{
 \|u\|_{L^2(P)}^2
 =\sup_{F\Subset\mathbb N_{\ge1}}
 b_F^*G_F^\dagger b_F.}
 \tag{CTL.15}
\]

The finite quantities are monotone under inclusion of reporter sets.  Equivalently, the complete
twisted response map is an isometry when its range is given the intrinsic norm

\[
 \|b\|_{\mathrm{resp}}^2
 :=\sup_Fb_F^*G_F^\dagger b_F.
 \tag{CTL.16}
\]

This is an exact conservation law, not a lower bound or asymptotic approximation.

### Proof: density

Suppose `u in H_P` is orthogonal to every `phi_n`.  The finite signed measure `J=uP` exists because
`L^2(P)` embeds in `L^1(P)`.  It has zero mass, and

\[
 b_n(J)=\langle u,\phi_n\rangle=0
\]

for every `n>=1`.  Theorem 3.1 gives `uP=0`, hence `u=0` in `L^2(P)`.  Therefore the orthogonal
complement of the centered-character span is zero.

### Proof: finite inverse-Gram energy

Let

\[
 \Phi_F:\mathbb R^F\longrightarrow H_P,
 \qquad c\longmapsto\sum_{n\in F}c_n\phi_n.
\]

Then `G_F=Phi_F^*Phi_F` and `b_F=Phi_F^*u`.  If `c in ker G_F`, then `Phi_F c=0`, so
`c^*b_F=0`; hence `b_F in ran G_F`.  The orthogonal projection of `u` onto `ran Phi_F` is

\[
 \Pi_Fu=\Phi_FG_F^\dagger b_F,
\]

and

\[
 \|\Pi_Fu\|^2=b_F^*G_F^\dagger b_F.
\]

Projection norms increase under inclusion.  Density of the union of the finite spans gives
`Pi_F u -> u` along the directed set of finite reporter families, proving `(CTL.15)`.  QED.

### Corollary 4.2 — one-character Fisher lower bound

Whenever

\[
 V_n=L_P(2n)-L_P(n)^2>0,
\]

\[
 \boxed{\mathcal I_P(J)\ge\frac{|b_n(J)|^2}{V_n}.}
 \tag{CTL.17}
\]

Equality holds exactly when the score is proportional to `phi_n`.  A finite reporter family gives
the corresponding sharp multivariate lower bound `(CTL.15)`.

### Meaning

ULF-SRSM-9 says the mass reporter kills vertical normalized shape.  Theorem 4.1 says the complete
source-character spectrum recovers both that shape and its positive Fisher energy.  These are not
contradictory: mass is the trivial character; shape lives in the nontrivial character sectors.

## 5. Formation acts diagonally on the complete response

Let `nu` be a probability measure on `[0,infinity)` and let convolution be the additive formation
action.  Put

\[
 a_n=L_\nu(n)=\int e^{-nx}\,d\nu(x).
 \tag{CTL.18}
\]

For every finite signed `J`, Fubini gives

\[
 \boxed{b_n(J*\nu)=a_n b_n(J).}
 \tag{CTL.19}
\]

Thus convolution is diagonal in the character-twisted atlas.  The trivial character preserves
mass; every nontrivial character records shape attenuation.

If `J({0})=0`, dominated convergence gives

\[
 b_n(J)\longrightarrow0,
 \tag{CTL.20}
\]

so its response belongs to `c_0`.  Define

\[
 M_\nu:c_0\longrightarrow c_0,
 \qquad (M_\nu b)_n=a_nb_n.
 \tag{CTL.21}
\]

### Theorem 5.1 — origin-atom formation-properness classification

Let `alpha=nu({0})`.  Then

\[
 \boxed{
 M_\nu\text{ is bounded below}
 \iff\operatorname{ran}M_\nu\text{ is closed}
 \iff\alpha>0.}
 \tag{CTL.22}
\]

More precisely:

1. if `alpha>0`, then

   \[
   \alpha\|b\|_\infty\le\|M_\nu b\|_\infty\le\|b\|_\infty;
   \tag{CTL.23}
   \]

2. if `alpha=0`, then `M_nu` is injective and compact, its range contains `c_00` and is dense,
   but its range is not closed and its inverse on the range is unbounded.

### Proof

Dominated convergence gives

\[
 a_n\longrightarrow\nu(\{0\})=\alpha.
 \tag{CTL.24}
\]

Every `a_n` is strictly positive and at most one.  If `alpha>0`, then `a_n>=alpha`, proving
`(CTL.23)` and a bounded diagonal inverse.

If `alpha=0`, the diagonal coefficients tend to zero.  Truncating the diagonal after coordinate
`N` gives a finite-rank operator whose distance from `M_nu` is `sup_(n>N)a_n`; hence `M_nu` is
compact on `c_0`.  It is
injective because all `a_n>0`.  Every finitely supported sequence lies in its range by coordinatewise
division, hence the range is dense.  But for the unit vectors `e_n`,

\[
 \|M_\nu e_n\|_\infty=a_n\longrightarrow0,
\]

so the operator is not bounded below.  An injective bounded operator with closed range has bounded
inverse on its range; therefore the range is not closed.  QED.

### New fourth-organ prediction

Finite character identifiability and global properness are independent.  A delay law with no
instantaneous component may preserve every character as a nonzero coordinate and still make
cofinal recovery compact and ill-conditioned.  Uniform response recovery through a positive
convolution formation is possible exactly when the formed law retains a positive zero-delay atom.

This prediction was not inserted as a topology axiom.  It is forced by the same characters that
reconstruct vertical current and Fisher mass.

## 6. Literal all-subset phase calibration

Let `lambda_1,...,lambda_m` be distinct positive rates and let

\[
 \nu_\lambda=operatorname{Exp}(\lambda_1)*\cdots*
 \operatorname{Exp}(\lambda_m).
\]

Its Laplace transform is

\[
 L_\lambda(z)=\prod_{j=1}^m\frac{\lambda_j}{\lambda_j+z}.
 \tag{CTL.25}
\]

For a rate velocity `v_j=dot lambda_j`,

\[
 \boxed{
 \frac{\dot L_\lambda(z)}{L_\lambda(z)}
 =\sum_{j=1}^m\frac{zv_j}{\lambda_j(\lambda_j+z)}.}
 \tag{CTL.26}
\]

The mass response at `z=0` is zero, as required for a normalized vertical current.

### Theorem 6.1 — complete rate reconstruction

If `dot L_lambda(n)=0` for every positive integer `n`, then every `v_j=0`.

### Proof

The right side of `(CTL.26)` is a rational function.  Vanishing at infinitely many positive
integers makes it identically zero.  Its residue at `z=-lambda_j` is `-v_j`; distinctness of the
rates therefore gives `v_j=0` for every `j`.  QED.

In the SRSM all-grade formation, the rates are

\[
 \lambda_S=\sum_{p\in S}\log p=\log\prod_{p\in S}p,
 \qquad\varnothing\ne S\subseteq I.
 \tag{CTL.27}
\]

Unique factorization makes all `lambda_S` distinct.  The complete integer response therefore
reconstructs every subset-rate velocity, and singleton subsets recover every prime-log velocity.
This is a literal source calibration of the abstract character atlas.

Every exponential or hypoexponential law has zero mass at the origin.  Theorem 5.1 therefore gives
an exact simultaneous conclusion:

- every finite subset-rate deformation is identifiable from the character response;
- appending a positive subset-phase formation acts compactly with dense nonclosed range on the
  cofinal `c_0` response observer.

That is the same finite/cofinal fracture seen earlier in CDF/Hilbert observation, now derived from
the source characters themselves rather than from a chosen horizon norm.

## 7. The four-organ fusion law

The theorem fuses four structurally different organs.

| organ | exact role |
|---|---|
| probability/base-norm formation | supplies normalized laws and zero-mass vertical currents |
| semigroup representation and twisted coinvariants | generates the legal nontrivial reporters |
| Fisher/Ward tangent geometry | supplies the positive vertical energy |
| inverse covariance Gram and completion theory | reconstructs that energy and classifies properness |

The joint conservation identity is

\[
 \boxed{
 \text{vertical Fisher mass}
 =\sup_{F\Subset\mathbb N_{\ge1}}
 \text{inverse covariance-Gram energy of the character response}.}
 \tag{CTL.28}
\]

The predicted theorem in the fourth organ is `(CTL.22)`: convolutional recovery is uniformly
proper precisely at the origin-atom face.

This is not a route dictionary.  The same generated reporter family performs reconstruction,
positive scalarization, and topology classification.

## 8. Conditional selection theorem and exact remaining gate

Let a literal pre-zero physical current be proved to have the normalized vertical form

\[
 J_\rho=u_\rho P_\rho,
 \qquad u_\rho\in L^2_0(P_\rho).
 \tag{CTL.29}
\]

If a source identity proves

\[
 \int e^{-nx}\,dJ_\rho(x)=0
 \qquad\text{for every }n\ge1,
 \tag{CTL.30}
\]

then Theorems 3.1 and 4.1 give

\[
 \boxed{J_\rho=0,\qquad\mathcal I_{P_\rho}(J_\rho)=0.}
 \tag{CTL.31}
\]

This is the first dependency-closed answer to SRSM-9's request for a source-restricted reporter:
not one fitted scalar, but the canonical complete character spectrum of the source formation
semigroup.

It is **not** an RH proof.  Still open:

1. type the physical pre-zero current as a finite signed or `L^2` vertical current on the source
   half-line;
2. derive `(CTL.30)` from a source law before Xi/divisor specialization;
3. prove that zero vertical current is exactly neutral transverse displacement.

Functional equation only permutes or isometrically transports the character spectrum.  It does
not annihilate it.

## 9. Hostile conjecture loops

### Loop A — one nonconstant reporter detects normalized shape

**False.**  Every single nonzero continuous linear functional on an infinite-dimensional current
space has a large kernel.

**Survivor.**  The countable integer-character family is jointly faithful by Theorem 3.1.

### Loop B — universal Markov naturality should be retained

**False.**  ULF-SRSM-9 proves it forces factorization through mass.

**Survivor.**  Restrict naturality to the source-generated additive semigroup and replace invariance
by exact character covariance `(CTL.19)`.

### Loop C — complete identifiability implies stable inversion

**False.**  Every atomless positive delay law gives a diagonal compact injection with dense
nonclosed range.

**Survivor.**  The exact stability boundary is `nu({0})>0`.

### Loop D — Bartlett balance plus complete reporters forces zero

**False without a null identity.**  Bartlett balance identifies Fisher with connection response;
it does not make any `b_n` vanish.

**Survivor.**  Vanishing of the complete character response is sufficient and exact.

### Loop E — finite phase reconstruction yields cofinal phase properness

**False.**  Distinct hypoexponential poles make every finite velocity identifiable, while the
atomless convolution multiplier is compact on `c_0`.

**Survivor.**  Finite algebraic identifiability and cofinal topological properness are independent
coordinates of one response law.

### Loop F — the theorem proves RH after physical substitution

**False.**  No physical current landing or source null identity has been proved.  Substituting a
zero-dependent current would be circular.

## 10. Internal collision audit

The corpus already contains important parents:

- `FisherOneCornerCoareaTransform.lean` and
  `FisherOneCornerCommonHardyReporter.lean` construct concrete one-corner Laplace/Fisher columns;
- Generative Response Mechanics proves centered-score, covariance, and Fisher processing laws;
- ULF-SRSM-8 proves globally proper base-norm probability formation;
- ULF-SRSM-9 proves the all-Markov mass-coinvariant no-go and Fisher/Ward migration;
- Hausdorff-moment modules formalize compact moment uniqueness in other receivers;
- inverse-capacity and positive-Gram cards prove the finite pseudoinverse mechanics abstractly.

None of those states the complete zero-mass integer-Laplace reconstruction theorem, the exact
Fisher supremum `(CTL.15)`, and the origin-atom convolution properness classification as one
source-generated law.  This card must cite those parents; it does not replace their route-specific
analytic work.

## 11. External parent audit

The ingredients are occupied mathematics.

- Fukumizu--Sriperumbudur--Gretton--Schoelkopf, *Characteristic Kernels on Groups and
  Semigroups*, develops characteristic RKHS embeddings on groups and semigroups, including the
  positive orthant:
  <https://papers.nips.cc/paper/3396-characteristic-kernels-on-groups-and-semigroups.pdf>.
- Sriperumbudur--Fukumizu--Lanckriet, *Universality, Characteristic Kernels and RKHS Embedding of
  Measures*, treats injective embeddings of finite signed Radon measures:
  <https://arxiv.org/abs/1003.0887>.
- Simon-Gabriel--Schoelkopf, *Kernel Distribution Embeddings*, systematizes injectivity and the
  induced topologies for measures and distributions:
  <https://arxiv.org/abs/1604.05251>.
- Labouriau, *The Laplace transform and polynomial approximation in L2*, proves related `L^2`
  polynomial-density results under exponential-moment hypotheses:
  <https://arxiv.org/abs/1603.03473>.
- Lin--Dou, *An Identity for Two Integral Transforms Applied to the Uniqueness of a Distribution
  via its Laplace--Stieltjes Transform*, proves countable-transform uniqueness results by
  Müntz--Szász methods; Theorem 3.1 is a signed zero-mass compactification specialization rather
  than a new moment theorem: <https://arxiv.org/abs/2012.00960>.
- Zhu--Wang's 2026 work on Weyl--Heisenberg measurements sharply separates informational
  completeness from the lower Gram edge controlling stable inversion, an external analogue of
  the identifiability/properness split in Theorem 5.1:
  <https://arxiv.org/abs/2608.11850>.
- Hilbert projection, Moore--Penrose inverse-Gram energy, Hausdorff moment uniqueness, compact
  diagonal operators, and Fisher-score geometry are classical.

Broad current-arXiv search through 2026 found active work on characteristic embeddings, Fisher
feature Grams, and stability versus informational completeness, but no paper with the exact package
`(CTL.9)+(CTL.15)+(CTL.22)` or its SRSM horizontal/vertical interpretation.  No priority claim is
needed for the field programme: the leverage is the constitutive fusion and its exact fourth-organ
prediction.

## 12. Lean decision

The Lean corpus was audited read-only.  Relevant ingredients exist separately, but this theorem is
not already formalized as a universal-law-field module.  Per the active research pass, no Lean file
was written and no Lean build was run.  Formalization should occur only after an independent
hostile paper audit accepts the exact hypotheses, especially:

1. finite signed Radon measure transport under `x |-> exp(-x)`;
2. density of centered integer characters in `L^2_0(P)`;
3. directed finite pseudoinverse projection identity;
4. compact diagonal classification on `c_0`.

## Log

- 2026-08-14 — pivoted from impossible all-Markov shape reporter to source-character covariance.
- 2026-08-14 — proved countable integer-Laplace reconstruction for all finite zero-mass signed
  half-line currents by compactification and Hausdorff moment uniqueness.
- 2026-08-14 — proved exact inverse covariance-Gram exhaustion of Fisher information.
- 2026-08-14 — derived origin-atom properness as a fourth-organ prediction and calibrated it on
  the literal all-subset hypoexponential prime-log formation.
- 2026-08-14 — audited internal Lean parents read-only and broad external characteristic-kernel,
  Laplace-density, Fisher-feature, and completion literature; no Lean write/build performed.
