# Observer-visible local-time dimension obstruction

- **ID:** observer-visible-local-time-dimension-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM / exact observer-dependent obstruction to autonomous state-complexity growth
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, obligation O4

## Exact universal statement

Let `V` be an `m`-dimensional real Euclidean coefficient space, let

\[
 H:V\longrightarrow\operatorname{Herm}(\mathcal H)
\]

be real-linear, and fix a normalized initial vector `Phi`.  Regard
`Phi^perp` as a real vector space and define the observer-action map

\[
 T_\Phi:V\longrightarrow\Phi^\perp,
 \qquad
 T_\Phi(x)=(I-|\Phi\rangle\langle\Phi|)H(x)\Phi.     \tag{1}
\]

Its real rank

\[
 v_\Phi:=\operatorname{rank}_{\mathbb R}T_\Phi       \tag{2}
\]

is the **observer-visible local-time dimension**.  Put

\[
 F_\Phi:=\ker T_\Phi,
 \qquad \dim_{\mathbb R}F_\Phi=m-v_\Phi.             \tag{3}
\]

Every coefficient direction in `F_Phi` is exactly invisible to the initial
ray:

\[
 x\in F_\Phi
 \quad\Longrightarrow\quad
 e^{-isH(x)}\Phi=e^{-is\alpha(x)}\Phi
 \quad(s\in\mathbb R)                               \tag{4}
\]

for a real scalar `alpha(x)`.  Thus `F_Phi` is a uniformly zero-gate
state-synthesis carrier; no commutativity, integrability, spectral relation,
or finite-dimensional Lie closure is required.

Assume, as in the parent O4 setup,

\[
 \|H(x)-H(y)\|\leq L_H\|x-y\|,
 \qquad \Lambda(H(x))\geq\lambda_-\|x\|.            \tag{5}
\]

If `v_Phi<m`, then for every fixed robust error `epsilon>0` there are
constants `c,R_0>0` such that the relative shortcut locus satisfies

\[
 \operatorname{vol}\!\left(
  \mathfrak S_{\epsilon,a}\cap
  \{x:R\leq\|x\|\leq2R\}
 \right)
 \geq cR^{m-v_\Phi}                                 \tag{6}
\]

for all `R>=R_0`.  Independently of whether `v_Phi<m`, if `J` is standard
Gaussian in `V`, then for all sufficiently large admissible `t`,

\[
 \mathbb P\!\left\{
 C_\epsilon(e^{-itH(J)}\Phi)
 \leq {a\Lambda(H(tJ))\over p(n)}
 \right\}
 \geq c't^{-v_\Phi}.                                \tag{7}
\]

Consequently every uniform upper no-shortcut law obeys the exact ceiling

\[
 \boxed{\ \kappa\leq v_\Phi.\ }                    \tag{8}
\]

The ambient Hamiltonian parameter count `m` is not the operational dimension
seen by state complexity.  The visible rank (2) is.

## Exact quantum-Fisher identification

Choose a real basis `e_1,...,e_m` of `V` and write `H_a=H(e_a)`.  The
pure-state quantum Fisher information matrix at the origin for the
multiparameter family

\[
 x\longmapsto [e^{-iH(x)}\Phi]
\]

is

\[
 (\mathcal F_\Phi)_{ab}
 =4\operatorname{Re}\!\left(
   \langle\Phi,H_aH_b\Phi\rangle
   -\langle\Phi,H_a\Phi\rangle
    \langle\Phi,H_b\Phi\rangle
  \right).                                           \tag{8a}
\]

If `u_a=T_Phi(e_a)`, then

\[
 (\mathcal F_\Phi)_{ab}
 =4\operatorname{Re}\langle u_a,u_b\rangle.          \tag{8b}
\]

Thus `mathcal F_Phi/4` is the real Gram matrix of the observer-action
vectors.  Gram rank equals real span dimension, so

\[
 \boxed{
 v_\Phi=\operatorname{rank}_{\mathbb R}\mathcal F_\Phi.
 }                                                     \tag{8c}
\]

Equation (8) can therefore be stated without new terminology: this
observer-stationary ceiling on autonomous state-complexity escape is the number of
Hamiltonian coefficient combinations locally distinguishable by the initial
probe according to quantum Fisher information.

## Proof

If `x in ker T_Phi`, then `H(x)Phi` lies in the complex line spanned by
`Phi`.  Since `H(x)` is Hermitian, its coefficient on that line is real; call
it `alpha(x)`.  Functional calculus then gives (4).  In projective state
space the identity circuit prepares every endpoint in `F_Phi` exactly.

Choose an orthogonal splitting

\[
 V=F_\Phi\oplus F_\Phi^\perp.                        \tag{9}
\]

A fixed-radius tube about an `(m-v_Phi)`-dimensional shell in `F_Phi` has
annular volume `Omega(R^(m-v_Phi))`.  For
`x=x_F+x_perp` in that tube, Duhamel continuity and (5) give

\[
 \|e^{-iH(x)}\Phi-e^{-iH(x_F)}\Phi\|
 \leq L_H\|x_\perp\|.                               \tag{10}
\]

Choosing the transverse radius at most `epsilon/L_H` puts the entire tube in
the `epsilon`-shortcut locus.  The zero-gate witness automatically satisfies
every nonnegative relative budget, proving (6).

For (7), decompose the standard Gaussian as `J=J_F+J_perp`.  On the event

\[
 \|J_\perp\|\leq {\epsilon\over L_Ht},              \tag{11}
\]

the endpoint is within `epsilon` of the initial ray.  The two projections are
independent, and the displayed event depends only on the transverse
projection.  Its `v_Phi`-dimensional Gaussian small-ball mass is at least
`c't^(-v_Phi)`.  This remains valid when `F_Phi={0}`: then `J_F=0` and the
event is the ordinary near-zero Gaussian ball.  It also remains valid when
`v_Phi=0`, with the zero-dimensional small ball interpreted as probability
one.  This proves (7), and comparison with an upper law `Kt^(-kappa)` proves
(8).

## Exact fixed-locality product-state rank

Let

\[
 \mathcal H=(\mathbb C^\ell)^{\otimes n},
 \qquad \Phi=|0\rangle^{\otimes n},                 \tag{12}
\]

and let `V_(n,q,ell)` be the full real space of non-scalar Hermitian operator
strings supported on at most `q` sites.  Its dimension is

\[
 m_{n,q,\ell}
 =\sum_{k=1}^{q}(\ell^2-1)^k{n\choose k}.            \tag{13}
\]

Every `q`-local operator sends `Phi` into the span of product basis vectors
whose nonzero excitation support has size at most `q`.  The number of such
orthogonal complex directions is

\[
 N_{n,q,\ell}
 =\sum_{k=1}^{q}(\ell-1)^k{n\choose k}.              \tag{14}
\]

For each nonempty support `S` of size at most `q` and each excitation label
`a in {1,...,ell-1}^S`, the two Hermitian operators

\[
 |a\rangle\langle0|+|0\rangle\langle a|,
 \qquad
 -i|a\rangle\langle0|+i|0\rangle\langle a|          \tag{15}
\]

on `S` send the product vacuum to the real and imaginary copies of that
basis direction.  Hence (1) is onto the realification of the space counted
in (14), and

\[
 \boxed{
 v_\Phi=2N_{n,q,\ell},\qquad
 \dim F_\Phi=m_{n,q,\ell}-2N_{n,q,\ell}.
 }                                                    \tag{16}
\]

The same rank holds for every product state, by local change of basis; the
space of all operators of support at most `q` is invariant under local
unitary conjugation.

For qubits (`ell=2`),

\[
 m_{n,q}=\sum_{k=1}^{q}3^k{n\choose k},
 \qquad
 v_\Phi=2\sum_{k=1}^{q}{n\choose k}.                 \tag{17}
\]

Therefore any Gaussian all-to-all fixed-`q` Pauli state-complexity escape
exponent from a product input satisfies

\[
 \boxed{
 \kappa\leq2\sum_{k=1}^{q}{n\choose k}
 ={2\over3^q}m_{n,q}+O(n^{q-1})
 }                                                    \tag{18}
\]

for fixed `q`.  The previously identified commuting `Z` sector forced only
`kappa<=m-sum_(k<=q) binom(n,k)`, which is much weaker.  The dominant known
obstruction is not commutativity: it is observer-invisibility.

## What this changes

1. The candidate invariant cannot be dynamical-Lie dimension, spectral rank,
   or maximal commuting-sector dimension.  Those are system invariants;
   (2) is a system--observer incidence rank.
2. An extensive noncommuting family can be completely invisible to one
   initial state.  Spectral chaos on the orthogonal complement does not make
   that observer's state complex.
3. The sharp replacement conjecture is now testable: for generic fixed-`q`
   Pauli dynamics from a product state, does the aggregate shortcut exponent
   equal the visible rank (17), with every larger shortcut family forcing a
   lower-dimensional invariant observer sector?
4. This gives literal mathematical content to “time has an
   observer-dependent dimension”: it means the real rank of the local
   Hamiltonian action on the observer's projective ray, not a metaphysical or
   relativistic claim.

## Hostile audit

1. **This is not a matching upper law.**  The kernel tube proves only a lower
   bound on shortcut probability.  Other fast-forwardable families, periodic
   components, or families landing near nontrivial easy states can force a
   smaller escape exponent.  The one-local Pauli family is the decisive
   example: (17) gives `v_Phi=2n`, while the whole family is uniformly easy
   and its true escape exponent is zero.  Therefore `v_Phi` is an exact
   ceiling, not a universally sharp exponent.
2. **The assumption `v_Phi<m` is load-bearing only for the large-annulus
   volume law (6).**  A zero-dimensional kernel has no large-radius shell.
   The Gaussian law (7) is stronger: when the kernel is zero, the near-zero
   coefficient ball still has mass `Omega(t^(-m))`.  The two statements must
   not be conflated in formalization.
3. **The Gaussian statement depends on coefficient geometry.**  “Standard
   Gaussian” means the Gaussian defined by the chosen Euclidean structure on
   `V`; it is not invariant under arbitrary reparameterization of the
   Hamiltonian dictionary.  Formula (8c) is basis-invariant, while the
   constants in (7) are not.
4. **The product-state formula requires `1<=q<=n` and the full support-at-most-
   `q` Hermitian dictionary.**  A sparse interaction graph, symmetry sector,
   real-only subdictionary, or constrained coupling ensemble can have a
   smaller image rank and must be recomputed rather than inferred from (16).
5. **QFI geometry itself is established metrology.**  The candidate new
   content is only the circuit-complexity escape obstruction obtained by
   combining its rank with the stationary coefficient fibre.  No priority
   claim is licensed until a dedicated literature audit finds or excludes
   this exact complexity consequence.

**Verdict:** the theorem survives as a dependency-closed positive obstruction,
with `[NOVELTY UNVERIFIED]`.  It does not by itself close the parent O4 law or
license the phrase “time has an observer-dependent dimension” as a physical
law beyond this precisely defined projective rank.

1. Equations (4), (6), and (8) are upper obstructions on a possible growth
   theorem, not a proof of growth.
2. The rank (2) is first-order notation but the kernel conclusion is global:
   every kernel Hamiltonian has `Phi` as an exact eigenvector, so no
   linearization approximation is used.
3. Matching the ceiling in (18) remains open.  Other mixed periodic-synthesis
   carriers or unorganized circuit intersections could force a smaller
   exponent.
4. The theorem concerns state complexity from a specified input.  Unitary or
   channel complexity has no observer kernel of this form.
5. The linear algebra is elementary.  Scientific priority and significance
   of the complexity-exponent consequence have not been established.
6. The identification (8c) is standard pure-state quantum-estimation
   geometry; only its use as the exact no-shortcut exponent ceiling is under
   novelty audit.

## Formalization status

`[LEAN-PROVED]` — every mathematical statement of this card is now closed
unconditionally in Lean 4 (axioms: `propext`, `Classical.choice`, `Quot.sound`).

| Card item | Lean module | Declaration |
|---|---|---|
| (2), (8a)–(8c) QFI Gram factorization and rank identity | `HTGeometry/ObserverVisibleLocalTimeDimension.lean` | `qfim_eq_four_smul_realification_gram`, `qfim_rank_eq_centeredRealification_rank` |
| (3) visible/invisible dimension split | `HTGeometry/ObserverInvisibleRayPreservation.lean` | `finrank_ker_centeredRealification_add_rank` |
| (4) exponential ray preservation | `HTGeometry/ObserverInvisibleRayPreservation.lean` | `exp_mulVec_of_eigenvector`, `unitaryEvolution_generatorCombination_mulVec_of_invisible`, `exists_unit_phase_unitaryEvolution_of_invisible`, `exists_unit_phase_unitaryEvolution_of_centered_eq_zero` |
| (10) Duhamel tube continuity | `HTGeometry/ObserverInvisibleTubeShortcut.lean` | `norm_unitaryEvolution_mulVec_sub_le`, `rayClose_of_transverse_small` |
| (6) annular tube volume law | `HTGeometry/ObserverKernelTubeVolume.lean`, `HTGeometry/ObserverInvisibleTubeShortcut.lean` | `measure_annulus`, `measure_annulusTube`, `measure_rayClose_ge_annulusTube` |
| (7) Gaussian small-ball law | `HTGeometry/GaussianSmallBallLowerBound.lean`, `HTGeometry/ObserverInvisibleTubeShortcut.lean` | `measure_pi_gaussian_closedBall_lower`, `measure_pi_gaussian_transverse_ball_lower`, `measure_rayClose_ge_gaussian_smallBall` |
| (8) ceiling `κ ≤ v_Φ` | `HTGeometry/ObserverKernelTubeVolume.lean`, `HTGeometry/ObserverInvisibleTubeShortcut.lean` | `exponent_le_of_forall_rpow_le`, `exponent_le_natCast_of_forall_le`, `exponent_le_visible_of_upper_law` |
| (13) dictionary dimension `m_{n,q,ℓ}` | `HTGeometry/FiniteQuditHermitianStringBasis.lean`, `HTGeometry/ProductStateObserverVisibleRank.lean` | `card_QLocalStringLabel`, `finrank_qLocalDictionary` |
| (14), (16) visible rank `v_Φ = 2N_{n,q,ℓ}` | `HTGeometry/ProductStateObserverVisibleRank.lean` | `card_ExcConfigLabel`, `map_qLocalDictionary`, `finrank_map_qLocalDictionary` |
| (16) `dim F_Φ = m − 2N` | `HTGeometry/ProductStateObserverVisibleRank.lean` | `finrank_ker_add_finrank_map_qLocalDictionary` |
| (16) same rank for every product state | `HTGeometry/ProductStateLocalUnitaryInvariance.lean` | `conj_quditString_mem_span_sameSupport`, `map_conj_qLocalDictionary_le`, `map_qLocalDictionary_productState`, `finrank_map_qLocalDictionary_productState`, `finrank_map_qLocalDictionary_productVector` |
| (17) qubit specialisation | `HTGeometry/ProductStateObserverVisibleRank.lean` | `finrank_map_qLocalDictionary_qubit`, `finrank_qLocalDictionary_qubit` |

Supporting infrastructure built for this card: the local Hermitian unit basis of
`Mat_ℓ(ℂ)` with the identity as its only non-traceless member and the explicit
inverse change of basis (`HTGeometry/FiniteQuditHermitianUnit.lean`), the
Hermitian operator-string basis of the full register algebra with its support
filtration (`HTGeometry/FiniteQuditHermitianStringBasis.lean`), and the
support-size counting law for finite configuration spaces
(`HTGeometry/FiniteSupportCounting.lean`).

Two modelling conventions are used and are exactly the ones the paper proof
takes:

1. The shortcut membership `x ∈ 𝔖_{ε,a}` is formalized as `RayClose`: the
   time-`t` endpoint lies within `ε` of the initial ray.  This is the content of
   the paper argument — the zero-gate identity witness prepares the initial ray
   exactly and therefore satisfies every nonnegative relative budget — so no
   circuit-complexity predicate is assumed or needed.
2. The orthogonal splitting `V = F_Φ ⊕ F_Φ^⊥` of the paper proof is taken as the
   coefficient space `E × F` with the invisible carrier as the first factor, and
   the standard Gaussian on the visible coordinates is the product of standard
   one-dimensional Gaussians.  This is the same object; no genericity or
   nondegeneracy hypothesis enters.
