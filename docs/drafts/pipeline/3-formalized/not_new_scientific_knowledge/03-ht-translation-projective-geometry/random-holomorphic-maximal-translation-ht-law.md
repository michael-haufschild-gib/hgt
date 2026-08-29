# Random holomorphic maximal translation-HT law

- **ID:** `random-holomorphic-maximal-translation-ht-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean) — `[PROVED HERE] [FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; random holomorphic functions; probabilistic route boundary
- **Statement:** A random entire function with absolutely continuous finite-jet laws has, almost
  surely, a differentially algebraically independent orbit under every prescribed countable set of
  translations.  The planar Gaussian entire function retains this property after conditioning on
  any finite Taylor jet.

## Goal

Strengthen the ordinary probability-one HT statement.  Hypertranscendence of one random function is
only the one-generator case.  The natural maximal statement asks whether every finite family of
distinct translates, with every derivative order, is algebraically independent over `C(z)`.

The answer is yes under the same finite-jet nondegeneracy that governs Gaussian analytic functions.
Finite probabilistic passports do not change the conclusion.

## Finite-jet nondegeneracy

Let `F` be an `O(C)`-valued random entire function.  Assume:

```text
(ND) For every finite list of distinct points z_1,...,z_r and every m>=0,
     (F^(j)(z_i))_(1<=i<=r,0<=j<=m)
     has a law absolutely continuous with respect to Lebesgue measure.
```

Full support is unnecessary; absolute continuity suffices.

Fix a countable set `H subset C`.  For `h in H`, write

```text
T_h F(z)=F(z+h).                                              (1)
```

## Maximal translation-orbit theorem `[PROVED HERE]`

With probability one, every finite family of distinct translates

```text
T_(h_1)F,...,T_(h_q)F,       h_i in H,                       (2)
```

is differentially algebraically independent over `C(z)`.  Equivalently, the countable family

```text
{T_h F:h in H}                                               (3)
```

is a free differential family over `C(z)`.

Taking `H={0}` gives ordinary hypertranscendence almost surely.

## Countable relation supports

Fix distinct shifts `h_1,...,h_q`.  After clearing rational denominators, a differential relation
over `C(z)` is a nonzero complex linear relation among finitely many expanded monomials

```text
M_(k,alpha)(z,(Y_(i,j)))
  = z^k product_(i=1)^q product_(j=0)^m Y_(i,j)^(alpha_(i,j)). (4)
```

Although the coefficients of a relation are arbitrary complex numbers, its finite monomial support
is selected from a countable set.  Since `H` is countable, all finite shift lists and finite supports
form one countable menu.

For a support `S={M_1,...,M_r}`, let `E_S` be the event that the analytic functions

```text
M_l(z,((T_(h_i)F)^(j)(z))_(i,j)),       1<=l<=r,              (5)
```

are linearly dependent over `C`.

## One support is a null event `[PROVED HERE]`

The monomials `M_1,...,M_r` are linearly independent polynomials in `z` and the formal jet
variables `Y_(i,j)`.  The evaluation lemma supplies distinct base points `a_1,...,a_r` and formal
jet tables `v_s` for which

```text
Delta((v_s))=det(M_l(a_s,v_s))_(1<=s,l<=r)                   (6)
```

is nonzero.  The base points may additionally be chosen so that all finitely many points

```text
a_s+h_i                                                     (7)
```

are pairwise distinct: at each induction step only finitely many affine collision sets are
forbidden, and deleting them does not create a polynomial identity.

For the actual random function, the variables in (6) are finite jets of `F` at the distinct points
(7).  Hypothesis (ND) makes their joint law absolutely continuous.  Since the zero set of a nonzero
complex polynomial has Lebesgue measure zero,

```text
Pr(Delta=0)=0.                                               (8)
```

If `E_S` occurs, every evaluation determinant vanishes, including (6).  Hence `Pr(E_S)=0`.
Taking the countable union over all shift lists and supports proves the theorem.

## Planar Gaussian entire function

Consider

```text
G(z)=sum_(n>=0) xi_n z^n/sqrt(n!),                            (9)
```

where the `xi_n` are independent standard complex Gaussian variables.

Every finite jet vector of `G` is complex Gaussian.  A linear dependence among derivative
evaluations would have zero variance exactly when the corresponding finite combination of kernel
derivatives

```text
partial_(conj w)^j exp(z conj(w)) evaluated at w=a_i          (10)
```

vanishes identically.  These are exponential-polynomial functions with distinct exponents and are
linearly independent, including the confluent derivative multiplicities.  Thus every finite jet
covariance matrix is nonsingular, (ND) holds, and for every countable `H subset C`,

```text
{G(z+h):h in H}
```

is almost surely differentially algebraically independent over `C(z)`.

## Stability under finite Taylor conditioning `[PROVED HERE]`

Fix `L>=0` and condition on arbitrary values of

```text
G(0),G'(0),...,G^(L)(0),                                    (11)
```

equivalently on `xi_0,...,xi_L`.  Under the regular conditional law, the remaining coefficients
`xi_(L+1),xi_(L+2),...` stay independent standard complex Gaussians.  The conditional random
function has the form

```text
P_L(z)+sum_(n>L) xi_n z^n/sqrt(n!),                           (12)
```

with `P_L` deterministic.

Its residual finite-jet laws are nondegenerate at any finite set of distinct nonzero points.  To
see this without covariance calculations, suppose `N` jet coordinates are requested.  The
polynomial space

```text
z^(L+1) C[z]_(<N)                                            (13)
```

maps isomorphically onto those `N` jets: multiplication by `z^(L+1)` is an invertible triangular
change of jets at nonzero points, followed by ordinary Hermite interpolation.  Therefore the
coefficients `xi_(L+1),...,xi_(L+N)` already give an invertible Gaussian contribution to the jet
vector; the independent tail preserves absolute continuity.

In the support proof, choose the evaluation points so that every `a_s+h_i` is also nonzero.  This
adds only finitely many forbidden affine values.  The null-determinant argument then applies
conditionally.  Hence, for every prescribed finite Taylor passport and every countable `H`,

```text
{G(z+h):h in H}
```

remains almost surely a free differential family.

## Independent continuous-coefficient series

The Gaussian hypothesis is not essential for ordinary almost-sure HT.  Let

```text
F(z)=sum_(n>=0) eta_n c_n z^n                               (14)
```

converge almost surely on a disk, with every `c_n!=0` and independent complex coefficients `eta_n`
having absolutely continuous laws.  For any finite jet vector of total dimension `N`, the first
`N` coefficients give an invertible Hermite map; adding the independent tail preserves absolute
continuity.  Thus the one-function theorem applies.  The maximal translation statement applies
whenever the domain is translation-stable for the chosen `H` and the corresponding joint finite
jets remain nondegenerate.

## Law extracted

**Probabilistic maximal-HT law.**  Under finite-jet absolute continuity, every proposed finite ADE
support is a null algebraic event.  Countability of supports upgrades this to ordinary HT;
countability of a transformation set upgrades it further to a free differential orbit.  Finite
Gaussian conditioning removes only finitely many directions and leaves the conclusion unchanged.

This is stronger than saying that random coefficients are “complicated.”  It gives an exact
identity-level statement about every derivative and every prescribed countable translation.

## Exact route consequence

The theorem excludes probabilistic implementations of RH routes having the following form:

1. use a Gaussian/random analytic carrier or a random-matrix limit as a surrogate for zeta;
2. verify finitely many zero, coefficient, or jet passports;
3. invoke ordinary or translation-orbit HT as the mechanism selecting the critical-line divisor.

Maximal HT is already probability one before the passport and remains probability one afterward.
It therefore cannot distinguish RH-valid from RH-invalid divisor behavior in such a model.

This does not exclude probabilistic methods that prove deterministic arithmetic estimates for zeta.
It also does not exclude random-matrix universality as a source of conjectures.  It excludes only
the promotion of generic random HT complexity itself to a divisor, positivity, or self-adjointness
law.

The named deterministic criteria remain outside the theorem in their full forms.  Li and Weil use
complete divisor-sensitive positivity; Nyman--Beurling uses a marked arithmetic closure; de Branges
uses a complete Hermite--Biehler inequality; Hilbert--Polya and Connes require a canonical exact
spectral realization.

## Parent-theory and novelty audit

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

Targeted searches did not locate the exact almost-sure free differential-translation-orbit statement
for Gaussian entire functions.  Nearby GAF literature studies zero processes, rigidity, hole
probabilities, and covariance nondegeneracy; nearby HT literature studies deterministic difference
equations and perturbations.  However, absence of the exact wording is insufficient.  Once the
finite-support normal form is available, the proof is the standard countable-union-of-null-algebraic-
events argument.  Adding countably many shifts and finite Gaussian conditioning is finite/countable
bookkeeping, not a new scientific mechanism.  The theorem therefore fails the parent-theory,
anti-theatre, and rediscovery gates.

Adjacent primary sources:

- J. Ben Hough, M. Krishnapur, Y. Peres, and B. Virag, *Zeros of Gaussian Analytic Functions and
  Determinantal Point Processes*, AMS, 2009, for GAF finite-dimensional distributions and kernels.
- L. van den Dries, *Parametrizing the solutions of an analytic differential equation*, Illinois J.
  Math. 39 (1995), 450--462, DOI `10.1215/ijm/1255986390`, for adjacent DA meagreness/interpolation.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference equations*,
  arXiv:1910.01874, for deterministic transformal-HT parent theory.

## Lean status (2026-08-29)

Fully formalized unconditionally in Lean 4.  The earlier assessment is superseded: the abstract
half was already in the tree, and what was missing was a model — no declaration verified the
finite-jet nondegeneracy hypothesis for any concrete random source, so the capstones were
vacuously applicable.  Two models are now built, including the planar Gaussian one.

### The abstract half (already owned, now non-vacuous)

`HTGeometry/RandomAffineJetPacketFreeness.lean` and `HTGeometry/AffineJetDifferentialIndependence.lean`
carry hypothesis `(ND)` (`HasAbsolutelyContinuousFiniteAffineJetLaws`, in a stronger multivariate
affine-palette form), the null-support theorem, and
`ae_translationOrbit_no_polynomialDifferentialRelation`.  Two of their theorems were **generalized
in place** to an arbitrary witness family, with the original statements kept as corollaries:
`exists_affineJetRelationValue_ne_zero_of_witness` and
`measure_compl_preimage_residualSet_eq_zero`.

### The one-coordinate translation dictionary

- `HTGeometry/OneDimJetEvalBridge.lean` — `multiIndexJetEvalCLM_oneDim`: a one-coordinate
  multi-index jet is an ordinary iterated derivative.
- `HTGeometry/OneDimTranslationJetPacket.lean` — a translation jet packet reads derivatives at
  translated base points (`packetPoint`, `packetOrder`).
- `HTGeometry/ConfluentVanishingPolynomial.lean` — `polynomial_eq_zero_of_jets_vanish` and its
  monomial-shifted form.
- `HTGeometry/PacketHermiteSurjectivity.lean` — `multiIndexBelowOneEquiv`,
  `card_coordinate_eq_sum_orders`, and **`surjective_packetShiftedHermiteMap`**: the square Hermite
  evaluation of `N` weighted monomials at the packet nodes is bijective.
- `HTGeometry/InfinitePiSumSplit.lean` — **`map_sumPiEquivProdPi_infinitePi`** (an infinite product
  law indexed by a sum type is the product of the block laws; a mathlib gap) and
  **`map_headTail_infinitePi`**.

### Model 1: independent absolutely continuous coefficients — the card's family `(14)`

`HTGeometry/BoundedRandomEntireStructure.lean`, `BoundedRandomEntireTail.lean`,
`RandomEntireTailSource.lean`, `RandomEntirePacketSplit.lean`,
`RandomEntireJetLawNondegeneracy.lean`, `RandomEntireTranslationOrbitFreeness.lean`:
**`hasAbsolutelyContinuousFiniteAffineJetLaws_boundedRandomEntire`** and
**`ae_translationOrbit_free_boundedRandomEntire`**, plus the deterministic-gauge stability
`ae_translationOrbit_free_boundedRandomEntire_add_const`.

### Finite Taylor conditioning `(11)`–`(13)`

The conditioned residual `z^{L}·(…)` has a genuinely degenerate jet packet at a node at the origin,
so — exactly as the card's own proof does — the evaluation nodes are chosen away from it:

- `HTGeometry/AffineFramePacketAvoidance.lean` — **`exists_base_separating_avoiding_and_eval_ne_zero`**;
- `HTGeometry/AvoidingAffineJetPacketWitness.lean` — **`exists_separatedWitness_avoiding`**;
- `HTGeometry/AvoidingRandomAffineJetFreeness.lean` —
  `HasAvoidingAbsolutelyContinuousFiniteAffineJetLaws` and
  **`ae_affineOrbit_free_of_avoidingJetLaws`**;
- `HTGeometry/RandomEntireConditionedOrbitFreeness.lean` —
  **`ae_translationOrbit_free_randomEntireTail_add_const`**.

### Model 2: the planar Gaussian entire function `(9)`

- `HTGeometry/ComplexGaussianCoefficientProbability.lean` — `complexGaussianProbability`, a genuine
  complex Gaussian *probability* law, absolutely continuous, with a Chebyshev tail bound.
- `HTGeometry/GaussianCoefficientTail.lean` — **`ae_eventually_norm_le_index`**: almost surely
  `‖ξₙ‖ < n` for all large `n` (Chebyshev plus the first Borel–Cantelli lemma).
- `HTGeometry/GaussianEntireCarrier.lean` — `tendsto_pow_div_sqrt_factorial`,
  `entireCoeffs_gafCoeff`, and the total source `gaussianEntireSource` (the series `∑ ξₙ zⁿ/√(n!)`
  where it converges, `0` on the null divergence set).
- `HTGeometry/EntireCoeffsPartialSumSource.lean` — partial sums of an entire coefficient series
  converge in the compact-open source space, hence so do their jet packets.  The Gaussian source is
  not continuous in the coefficients, so this pointwise-limit argument replaces continuity and
  supplies measurability.
- `HTGeometry/GaussianEntirePacketSplit.lean` — the polynomial-growth event is a tail event, and the
  series splits into its polynomial head plus a tail in the shifted coordinates alone.
- `HTGeometry/GaussianJetLawNondegeneracy.lean` —
  **`hasAvoidingAbsolutelyContinuousFiniteAffineJetLaws_gaussianEntireSource`**.
- `HTGeometry/GaussianTranslationOrbitFreeness.lean` —
  **`ae_translationOrbit_free_gaussianEntireSource`** and
  **`ae_translationOrbit_free_gaussianEntireSource_add_const`**.

No `sorry`, `admit`, new axiom or heartbeat increase beyond explicit local `maxHeartbeats` raises.
Every new module is wired into `GaloisForLFunctions.HTGeometry`, `lake build` passes on each, and
axiom audits of every capstone report only `propext`, `Classical.choice` and `Quot.sound`.

## Gates

- [x] 0 -> 1: finite-jet nondegeneracy and countable translation target stated
- [x] 1 -> 2: maximal orbit theorem, planar GEF example, and finite-conditioning stability proved
- [x] broad GAF/random-series/HT literature audit; classified as a bridge
- [x] 2 -> 3: complete unconditional theorem formalized in Lean (2026-08-29)
- [ ] 3 -> 4: closed by failed novelty gate

## Log

- 2026-06-23 -- Proved ordinary probability-one HT from finite-jet absolute continuity.
- 2026-06-24 -- Added planar Gaussian and independent continuous-coefficient examples; downgraded
  ordinary theorem to folklore/bridge.
- 2026-07-11 -- Strengthened to almost-sure differential independence of every prescribed countable
  translation orbit and proved stability under arbitrary finite Taylor conditioning.
- 2026-07-11 -- Source search found no exact duplicate, but the parent-mechanism gate still killed
  scientific novelty.
