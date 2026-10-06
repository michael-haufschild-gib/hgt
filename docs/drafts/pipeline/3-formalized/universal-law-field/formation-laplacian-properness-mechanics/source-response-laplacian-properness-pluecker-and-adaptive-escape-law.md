# Source-response Laplacian properness, Pluecker reconstruction, and adaptive-escape law

- **ID:** ULF-FLPM-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [SOURCE-COHERENT RESPONSE PACKET]`
  `[PAIRWISE CONSERVATION] [QUOTIENT PROPERNESS] [SCALE SELECTION]`
  `[PLUECKER RECONSTRUCTION] [ADAPTIVE-ESCAPE CLASSIFICATION]`
  `[FOURTH-ORGAN REDUNDANCY TEST] [BRIDGE] [NOT RH] [LEAN-PROVED]`
- **Formal status:** Fully formalized, unconditionally: see the Lean certificate below.

## 1. Purpose

The completed scalar formation theorem expels each fixed nonneutral scale under repeated source
formation. That is insufficient for a global selector: an adaptive sequence may change direction
while its observed work tends to zero. This card gives the exact route-independent boundary.

One source intervention must first generate the entire response packet. Its centered analysis
operator then has two distinct selection invariants:

1. its kernel, which measures algebraic nonidentifiability;
2. its lower frame bound, which measures uniform failure of adaptive escape.

The theorem proves the conservation law connecting pairwise organ disagreement, a positive
formation Laplacian, finite-dimensional quotient properness, dilation selection, Pluecker-volume
reconstruction, and the closed-range/adaptive-escape dichotomy.

## 2. Source-generated response packet

Let `V` and `W` be real Hilbert spaces. Let `I` be a finite nonempty set, let

\[
 \rho_i:V\longrightarrow W\qquad(i\in I)
 \tag{FLP.1}
\]

be bounded linear response maps produced by one marked source intervention, and let `c_i>0`. Put

\[
 C=\sum_{i\in I}c_i,
 \qquad
 \bar\rho={1\over C}\sum_{i\in I}c_i\rho_i.
 \tag{FLP.2}
\]

Define

\[
 A:V\longrightarrow\bigoplus_{i\in I}W,
 \qquad
 Ax=\bigl(\sqrt{c_i}(\rho_i-\bar\rho)x\bigr)_{i\in I},
 \tag{FLP.3}
\]

\[
 \mathcal E(x)=\|Ax\|^2,
 \qquad
 L=A^*A.
 \tag{FLP.4}
\]

Fix `i_0 in I` and define the synchronization kernel

\[
 K=\bigcap_{i\in I}\ker(\rho_i-\rho_{i_0}).
 \tag{FLP.5}
\]

The direct sum is a Hilbert direct sum; it is finite because `I` is finite. Since each `rho_i` is
bounded, so are `bar rho`, `A`, and `L`. The subspace `K` is closed.

## 3. Main theorem

### Theorem 3.1 — formation-Laplacian conservation and global properness boundary

Under `(FLP.1)--(FLP.5)` the following hold.

#### I. Pairwise conservation

For every `x in V`,

\[
 \boxed{
 \mathcal E(x)
 =\sum_i c_i\|\rho_i x-\bar\rho x\|^2
 ={1\over C}\sum_{\{i,j\}\subset I}c_ic_j\|\rho_i x-\rho_jx\|^2.}
 \tag{FLP.6}
\]

The last sum is over unordered two-element subsets of `I`; it is zero when `|I|=1`.

#### II. Exact synchronization kernel

\[
 \boxed{\ker A=\ker L=K.}
 \tag{FLP.7}
\]

Consequently `E` depends only on the class of `x` in `V/K` and is positive definite there.

#### III. Finite-dimensional quotient properness

Assume `V` is finite-dimensional.

- If `K=V`, then `V/K` is a point and `E=0`.
- If `K` is a proper subspace, let `lambda_F` be the least positive eigenvalue of `L`. Then

  \[
  \boxed{
  \mathcal E(x)\ge
  \lambda_F\operatorname{dist}(x,K)^2
  \qquad(x\in V).}
  \tag{FLP.8}
  \]

  The constant `lambda_F` is the largest constant for which `(FLP.8)` holds. The descended
  quadratic form on `V/K` is proper: every finite-energy sublevel is compact.

#### IV. Scale-orbit selection

For every `d>1`, `n in N`, and `x in V`,

\[
 \mathcal E(d^n x)=d^{2n}\mathcal E(x),
 \qquad
 \boxed{
 \sup_{n\ge0}\mathcal E(d^nx)<\infty\iff x\in K.}
 \tag{FLP.9}
\]

Hence a separating packet (`K={0}`) turns bounded full-response formation work into exact neutral
selection `x=0`.

#### V. Pluecker reconstruction

Assume `V` and `W` are finite-dimensional and put `r=dim(K^perp)`. Choose orthonormal bases and let
`B` be the matrix of the injective map `A|_(K^perp)`. With the conventions that the
pseudo-determinant is the product of the nonzero eigenvalues, the empty product is `1`, and a
`0 x 0` determinant is `1`,

\[
 \boxed{
 \operatorname{pdet}(L)
 =\det(B^*B)
 =\sum_{\substack{S\text{ a row subset of }B\\|S|=r}}\det(B_S)^2.}
 \tag{FLP.10}
\]

For `r>0` the right side is positive. It reconstructs the full quotient-volume margin from finite
source-response minors. The positive Laplacian retains squared oriented volumes and cannot recover
their individual signs. If `K={0}`, a nonzero maximal minor is exactly a finite certificate that
the response packet separates all source displacements.

#### VI. Infinite-dimensional adaptive-escape classification

For arbitrary Hilbert `V`, the following are equivalent:

1. `ran A` is closed;
2. there exists `alpha>0` such that

   \[
   \mathcal E(x)\ge\alpha\operatorname{dist}(x,K)^2
   \qquad(x\in V);
   \tag{FLP.11}
   \]

3. there is no sequence `x_n in K^perp` with `||x_n||=1` and
   `E(x_n)->0`.

Thus injectivity (`K={0}`) gives fixed-ray detection but not uniform global selection. When `A` is
injective with nonclosed range, every fixed nonzero `x` has positive formation energy and is
expelled by `(FLP.9)`, while a unit sequence of changing displacements has energy tending to zero.

#### VII. Fourth-organ redundancy and escape-interception law

Let `Z` be another real Hilbert space, let `R:V->Z` be an added centered response, and define

\[
 A^+x=(Ax,Rx),
 \qquad
 \mathcal E^+(x)=\|A^+x\|^2=\mathcal E(x)+\|Rx\|^2.
 \tag{FLP.12}
\]

If `R` factors through the existing packet by a bounded map `S`, so that `R=SA`, then

\[
 \boxed{
 \mathcal E(x)\le\mathcal E^+(x)
 \le(1+\|S\|^2)\mathcal E(x).}
 \tag{FLP.13}
\]

Consequently

\[
 \boxed{
 \ker A^+=K,
 \qquad
 \operatorname{ran}A^+\text{ is closed}\iff\operatorname{ran}A\text{ is closed}.}
 \tag{FLP.14}
\]

In particular, no fourth organ relatively bounded by the old formation energy can repair adaptive
escape. Conversely, if `K={0}`, `ran A` is not closed, and the enlarged packet satisfies the energy
lower bound `E^+(x)>=alpha||x||^2` for some `alpha>0`, then for every unit adaptive escape sequence
`x_n` with `E(x_n)->0`,

\[
 \liminf_n\|Rx_n\|>0.
 \tag{FLP.15}
\]

Thus an unlocking fourth organ must intercept every old adaptive null sequence; mere reconstruction
from the first packet is insufficient.

## 4. Proof

Write `y_i=rho_i x` and `bar y=bar rho x`.

### 4.1 Pairwise conservation

Expanding the first centered sum gives

\[
\begin{aligned}
 \sum_i c_i\|y_i-\bar y\|^2
 &=\sum_i c_i\|y_i\|^2
   -2\left\langle\sum_i c_i y_i,\bar y\right\rangle
   +C\|\bar y\|^2\\
 &=\sum_i c_i\|y_i\|^2-C\|\bar y\|^2.
\tag{FLP.16}
\end{aligned}
\]

On the other hand,

\[
\begin{aligned}
 {1\over2C}\sum_{i,j}c_ic_j\|y_i-y_j\|^2
 &=\sum_i c_i\|y_i\|^2
   -{1\over C}\left\|\sum_i c_i y_i\right\|^2\\
 &=\sum_i c_i\|y_i\|^2-C\|\bar y\|^2.
\tag{FLP.17}
\end{aligned}
\]

The ordered double sum is twice the unordered-pair sum, proving `(FLP.6)`.

### 4.2 Kernel

The equality `Ax=0` holds exactly when every `y_i=bar y`, equivalently when every `y_i` equals
`y_(i_0)`. Hence `ker A=K`. Moreover

\[
 \langle Lx,x\rangle=\langle A^*Ax,x\rangle=\|Ax\|^2,
\tag{FLP.18}
\]

so `Lx=0` implies `Ax=0`; the reverse implication is immediate. This proves `(FLP.7)`. If
`x=x_perp+x_K` with `x_K in K`, then `Ax=Ax_perp`, so `E` descends to `V/K`.

### 4.3 Finite-dimensional properness

Assume `V` finite-dimensional and `K` proper. On `K^perp`, the positive self-adjoint operator `L`
has zero kernel, hence is positive definite. Its Rayleigh quotient has a positive minimum
`lambda_F` on the compact unit sphere. Therefore

\[
 \mathcal E(x)
 =\langle Lx_\perp,x_\perp\rangle
 \ge\lambda_F\|x_\perp\|^2
 =\lambda_F\operatorname{dist}(x,K)^2.
\tag{FLP.19}
\]

An eigenvector for `lambda_F` shows optimality. Identifying `V/K` isometrically with `K^perp`, a
finite-energy sublevel is closed and bounded in finite dimension, hence compact. When `K=V` the
quotient is a point and the separate trivial statement follows.

### 4.4 Scale selection

Linearity gives `A(d^n x)=d^n Ax`, proving the first identity in `(FLP.9)`. If `x in K`, every term
is zero. If `x notin K`, `(FLP.7)` gives `E(x)>0`, and `d^(2n)E(x)` tends to infinity. This proves the
equivalence.

### 4.5 Pluecker reconstruction

The orthogonal decomposition `V=K direct-sum K^perp` makes the nonzero spectral part of `L=A^*A`
unitarily equivalent to `B^*B`. Therefore

\[
 \operatorname{pdet}(L)=\det(B^*B).
\tag{FLP.20}
\]

Because `B` has full column rank `r`, Cauchy--Binet gives

\[
 \det(B^*B)=\sum_{|S|=r}\det((B^*)_{[:,S]})\det(B_{[S,:]})
 =\sum_{|S|=r}\det(B_S)^2.
\tag{FLP.21}
\]

For `r=0`, both sides equal the empty product `1`. For `r>0`, full column rank is equivalent to at
least one nonzero maximal minor, so the sum is positive. This proves `(FLP.10)` and all stated
certificate claims.

### 4.6 Closed range and adaptive escape

Since `K=ker A` is closed, `V=K direct-sum K^perp`. Let

\[
 T=A|_{K^perp}:K^perp\longrightarrow\operatorname{ran}A.
\tag{FLP.22}
\]

It is a bounded bijection. If `ran A` is closed, it is a Hilbert space; the bounded inverse theorem
gives `||Tx||>=beta||x||` for some `beta>0`. Squaring and using
`||x_perp||=dist(x,K)` yields `(FLP.11)` with `alpha=beta^2`.

Conversely, `(FLP.11)` makes `T` bounded below. If `Tx_n` is Cauchy in `ran A`, then `x_n` is
Cauchy, so `x_n->x in K^perp` and `Tx_n->Tx`; hence `ran A` is closed.

The lower bound exists exactly when

\[
 \inf\{\|Ax\|^2:x\in K^perp,\ \|x\|=1\}>0.
\tag{FLP.23}
\]

If the infimum is zero, choose unit `x_n` with `E(x_n)<1/n`; if it is positive, no such sequence
exists. This proves the three-way equivalence. The case `K=V` is harmless: `ran A={0}` is closed,
`(FLP.11)` is vacuous, and `K^perp` contains no unit vectors.

### 4.7 Fourth-organ redundancy and interception

If `R=SA`, then

\[
 \mathcal E^+(x)=\|Ax\|^2+\|SAx\|^2,
 \tag{FLP.24}
\]

which immediately gives `(FLP.13)` and `ker A^+=ker A=K`. By Part VI, `A` has closed range exactly
when `E` has a positive lower bound on `K^perp`; `(FLP.13)` says this happens exactly when `E^+`
has such a lower bound. Applying Part VI to `A^+` proves `(FLP.14)`.

For the converse claim, suppose `K={0}` and
`E^+(x)>=alpha||x||^2` for some `alpha>0`. If `||x_n||=1` and `E(x_n)->0`, then

\[
 \alpha\le\mathcal E^+(x_n)
 =\mathcal E(x_n)+\|Rx_n\|^2.
 \tag{FLP.25}
\]

Therefore `liminf ||Rx_n||^2>=alpha`, which proves `(FLP.15)`.

## 5. Sharp countermodels and boundaries

### 5.1 One organ cannot form disagreement

If `|I|=1`, then `bar rho=rho_1`, `A=0`, `K=V`, and every clause reduces to the trivial synchronized
case. Multiple response labels are necessary for a nonzero formation Laplacian.

### 5.2 Algebraic separation does not imply uniform selection

Let `V=W=ell^2(N)` and define `D e_n=n^(-1)e_n`. Take two unit-weight responses

\[
 \rho_1=D,
 \qquad
 \rho_2=-D.
\tag{FLP.26}
\]

Then `bar rho=0`, `K=ker D={0}`, and

\[
 \mathcal E(x)=2\|Dx\|^2.
\tag{FLP.27}
\]

Every nonzero displacement is detected and every fixed dilation orbit has unbounded work. Yet
`E(e_n)=2/n^2->0`, and the range of `A:x mapsto (Dx,-Dx)` is not closed. This proves that the
uniform gate is independent of the algebraic gate.

### 5.3 Infinite-dimensional coercivity is not compact properness

Even if `(FLP.11)` holds in infinite dimension, its quotient sublevels need not be compact. For
`A=id` on an infinite-dimensional Hilbert space, the unit-energy sublevel is the closed unit ball,
which is not norm compact. The theorem claims compact sublevels only in finite dimension.

### 5.4 The source marking is load-bearing

Given arbitrary target distinctions one can choose response maps whose kernels encode them. The
theorem is a universal receiver, not a producer of the `rho_i`. A proof-route organ enters this
mechanism only when its response map is derived from the same pre-target source intervention and
the comparison is fixed before any desired zero or endpoint is imposed.

## 6. What the theorem unlocks—and what it does not

The theorem replaces the vague demand for “global properness” by two exact obligations:

\[
 \boxed{
 \text{selection}
 =\text{trivial synchronization kernel}
 +\text{positive lower formation-frame bound}.}
 \tag{FLP.28}
\]

The first is algebraic; the second is metric/topological. Neither determines the other. This
explains why finite route witnesses can all be correct while the cofinal proof still fails: finite
Pluecker minors certify separation at each aperture, but their least singular values may decay to
zero.

For a proposed all-route fusion, Part VII is the decisive fourth-organ theorem. After three organs
jointly reconstruct the source displacement modulo `K`, a fourth response of the form `R=SA` is
provably redundant. A useful fourth organ must instead intercept every old adaptive null sequence
and raise the combined lower frame bound on `K^perp`.

This is unconditional route-independent leverage, but it is not an RH proof. The remaining
source-specific problem is to construct one literal pre-zero response packet from at least three
structurally distinct organs and prove that its completed analysis operator has `K={0}` and closed
range with a source-controlled lower bound.

## 7. Collision and status audit

- The Hilbert variance identity, frame operator, closed-range theorem, spectral gap, and
  Cauchy--Binet identity are parent mathematics. The abstract result is therefore labelled
  `[BRIDGE]`, not independent novelty.
- The corpus already contains pairwise response reconstruction and equalizer selection in
  `SourceCoherentInterventionSynchronization.lean`, and scalar weighted variance in
  `SharedGaugeQuotientFusion.lean`. It does not contain the exact combined
  kernel--spectral-margin--Pluecker--adaptive-escape theorem proved here.
- The earlier scalar global-formation law proves fixed-ray scale selection. Clause VI proves why
  that alone does not rule out moving/cofinal null flags.
- Knill's *Cauchy--Binet for Pseudo-Determinants* is a direct external parent for `(FLP.10)`.

## 8. Promotion record

- [x] predecessor chamber atlas killed rather than rebranded;
- [x] all seven clauses proved with zero-dimensional and infinite-dimensional edge cases;
- [x] singleton-organ, injective/nonclosed-range, and noncompact-sublevel countermodels included;
- [x] source-versus-receiver boundary explicit;
- [x] no RH or route-specific selector claim;
- [x] Lean formalization and Stage-3 record (see the Lean certificate below).

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.SourceResponseFormationEnergy`, `GaloisForLFunctions.HTGeometry.SourceResponsePlueckerVolume`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.SourceResponseFormationEnergy` (§2, Parts I, II, IV, VI, VII
and §5) and `GaloisForLFunctions.HTGeometry.SourceResponsePlueckerVolume` (Parts III and V).  New
names live in the namespace SourceResponse under GaloisForLFunctions.HTGeometry (prefix
`SourceResponse.` below; `P` is a `SourceResponse.ResponsePacket`).  Real Hilbert spaces `V`, `W`;
finite nonempty index type `I`; Parts III and V assume `V`, `W` finite-dimensional.  Corpus inputs:
closed range via transverse lower bounds (`ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range`),
operator-valued block diagonals (`blockOperator`, `blockOperator_single`), rectangular compound
matrices and their Cauchy--Binet identity (`rectangularCompound`, `rectangularCompound_apply`,
`rectangularCompound_mul`, `subsetEnum`) and Pythagoras for orthonormal combinations
(`norm_sq_sum_smul_orthonormal`).

| Claim | Lean declaration |
|-|-|
| (FLP.1)–(FLP.2) responses `ρ_i`, weights `c_i > 0`, total weight `C`, mean `ρ̄` | `SourceResponse.ResponsePacket`, `SourceResponse.ResponsePacket.totalWeight`, `SourceResponse.ResponsePacket.totalWeight_pos`, `SourceResponse.ResponsePacket.mean`, `SourceResponse.ResponsePacket.mean_apply` |
| (FLP.3)–(FLP.5) the centred analysis operator `A`, energy `𝓔`, Laplacian `L = A*A`, synchronization kernel `K` (closed) | `SourceResponse.ResponsePacket.analysis`, `SourceResponse.ResponsePacket.analysis_apply`, `SourceResponse.ResponsePacket.energy`, `SourceResponse.ResponsePacket.laplacian`, `SourceResponse.ResponsePacket.syncKernel`, `SourceResponse.ResponsePacket.mem_syncKernel_iff`, `SourceResponse.ResponsePacket.isClosed_syncKernel` |
| Part I, (FLP.6), (FLP.16)–(FLP.17) pairwise conservation, centred, ordered and unordered-pair forms | `SourceResponse.ResponsePacket.energy_eq_sum`, `SourceResponse.ResponsePacket.sum_mul_sum_norm_sq_sub`, `SourceResponse.ResponsePacket.energy_eq_pairwise`, `SourceResponse.ResponsePacket.pairWeight`, `SourceResponse.ResponsePacket.energy_eq_sum_unordered` |
| Part II, (FLP.7), (FLP.18) `ker A = ker L = K`; `𝓔` descends to `V/K` and is positive definite there | `SourceResponse.ResponsePacket.analysis_eq_zero_iff`, `SourceResponse.ResponsePacket.ker_analysis`, `SourceResponse.ResponsePacket.inner_laplacian_self`, `SourceResponse.ResponsePacket.ker_laplacian`, `SourceResponse.ResponsePacket.energy_add_mem`, `SourceResponse.ResponsePacket.energy_eq_zero_iff`, `SourceResponse.ResponsePacket.energy_nonneg` |
| Part III, trivial case `K = V`: `𝓔 = 0` | `SourceResponse.ResponsePacket.energy_eq_zero_of_syncKernel_eq_top` |
| Part III spectral setup: eigenbasis, `𝓔(x) = Σ μ_k⟨b_k,x⟩²`, `dist(x,K)² = Σ_{μ_k≠0}⟨b_k,x⟩²` | `SourceResponse.ResponsePacket.laplacian_isSymmetric`, `SourceResponse.ResponsePacket.eigBasis`, `SourceResponse.ResponsePacket.eig`, `SourceResponse.ResponsePacket.laplacian_eigBasis`, `SourceResponse.ResponsePacket.energy_eq_sum_eig`, `SourceResponse.ResponsePacket.eig_nonneg`, `SourceResponse.ResponsePacket.mem_syncKernel_iff_eig`, `SourceResponse.ResponsePacket.infDist_sq_eq` |
| Part III, (FLP.8), (FLP.19) least positive eigenvalue `λ_F`: positive eigenvalue below every positive eigenvalue, `𝓔 ≥ λ_F dist(·,K)²`, optimal, compact sublevels on `Kᗮ` | `SourceResponse.ResponsePacket.leastPositiveEig`, `SourceResponse.ResponsePacket.leastPositiveEig_spec`, `SourceResponse.ResponsePacket.quotient_properness` |
| Part III the descended form on `V/K` is proper | `SourceResponse.ResponsePacket.descendedEnergy`, `SourceResponse.ResponsePacket.descendedEnergy_mk`, `SourceResponse.ResponsePacket.isCompact_descendedEnergy_sublevel` |
| Part IV, (FLP.9) `𝓔(dⁿx) = d²ⁿ𝓔(x)`; bounded dilation work iff `x ∈ K` | `SourceResponse.ResponsePacket.energy_smul`, `SourceResponse.ResponsePacket.energy_dilate`, `SourceResponse.ResponsePacket.bddAbove_energy_dilate_iff` |
| Part V, (FLP.10), (FLP.20) `pdet(L) = det(BᵀB)` with `B` the matrix of `A|_{Kᗮ}`; positivity | `SourceResponse.ResponsePacket.pdet`, `SourceResponse.ResponsePacket.pdet_pos`, `SourceResponse.ResponsePacket.laplacianRestrict`, `SourceResponse.ResponsePacket.orthEigBasis`, `SourceResponse.ResponsePacket.det_laplacianRestrict`, `SourceResponse.ResponsePacket.pluecker_reconstruction` |
| Part V, (FLP.21) Cauchy–Binet `det(BᵀB) = Σ_{|S|=r} det(B_S)²` | `SourceResponse.rowMinor`, `SourceResponse.det_transpose_mul_self_eq_sum_sq` |
| Part V `K = 0` iff some maximal minor is nonzero; the Laplacian keeps squared volumes, not signs | `SourceResponse.ResponsePacket.separation_certificate`, `SourceResponse.gram_neg_and_minor_neg` |
| Part VI, (FLP.11), (FLP.22)–(FLP.23) closed range ⇔ `𝓔 ≥ α dist(·,K)²` ⇔ no unit escape sequence in `Kᗮ` | `SourceResponse.ResponsePacket.infDist_syncKernel`, `SourceResponse.ResponsePacket.adaptiveEscape_tfae` |
| Part VI injective packet with nonclosed range: fixed rays detected and expelled, moving unit sequences escape | `SourceResponse.ResponsePacket.injective_nonclosed_escape` |
| Part VII, (FLP.12), (FLP.24) enlarged packet `A⁺ = (A, R)`, `𝓔⁺ = 𝓔 + ‖R·‖²` | `SourceResponse.ResponsePacket.augmented`, `SourceResponse.ResponsePacket.norm_sq_augmented` |
| Part VII, (FLP.13)–(FLP.14) `R = SA`: `𝓔 ≤ 𝓔⁺ ≤ (1+‖S‖²)𝓔`, `ker A⁺ = K`, closed range unchanged | `SourceResponse.ResponsePacket.augmented_energy_bounds`, `SourceResponse.ResponsePacket.augmented_redundant` |
| Part VII, (FLP.15), (FLP.25) an unlocking organ intercepts every escape sequence | `SourceResponse.ResponsePacket.augmented_intercepts`, `SourceResponse.ResponsePacket.unlocking_organ_intercepts` |
| §5.1 one organ: `ρ̄ = ρ`, `A = 0`, `K = V` | `SourceResponse.singleton_packet` |
| §5.2, (FLP.26)–(FLP.27) `ρ₁ = D`, `ρ₂ = -D`: `K = 0`, `𝓔(e_n) = 2/(n+1)² → 0`, nonclosed range | `SourceResponse.harmonicDiagonal`, `SourceResponse.harmonicPacket`, `SourceResponse.harmonicPacket_escape` |
| §5.3 coercive but noncompact sublevels in infinite dimension | `SourceResponse.identityPacket`, `SourceResponse.identityPacket_noncompact` |

§5.4, §6, §7 and §8 are commentary and state what is not claimed.

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
