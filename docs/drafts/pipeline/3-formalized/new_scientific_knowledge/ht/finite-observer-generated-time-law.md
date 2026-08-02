# Finite observer-generated time law

- **ID:** `finite-observer-generated-time-law`
- **Stage:** 2-fully-proven
- **Type:** DEPENDENCY-CLOSED PAPER THEOREM / FINITE CLOSED CORE
- **Status:** `[PAPER-PROVED] [FULLY FORMALIZED IN LEAN] [EXTERNAL PRIORITY OPEN]`
- **Master conjecture:**
  `../1-in-progress/observer-generated-time-conjecture.md`
- **Date:** 2026-07-30

## Discovery

> **A clock is one curve through an observer's time. The dimension of that
> time is the number of independent phase relations the observer can
> distinguish.**

For a finite closed quantum system, complete operational probability
histories generate a canonical compact time: the closure of the
observer-visible phase orbit. A scalar laboratory clock can be dense in this
multidimensional compact time.

Different observers receive quotient times. Their joint and common temporal
dimensions obey an exact conservation law. Exact completion dimension is
dense and unstable under arbitrarily small Hamiltonian perturbations, while
all bounded-time channel histories remain uniformly stable.

## 1. Operational temporal completion

Let \(S=\mathbb R\) be laboratory clock labels. For process \(P\) and
observer \(\mathcal O\), let \(\mathsf E_{\mathcal O}\) be a complete family
of allowed finite protocols and outcomes. Define
\[
 \Phi_{\mathcal O}(t)
 =
 \bigl(\Pr_P(e\mid t)\bigr)_{e\in\mathsf E_{\mathcal O}}
 \in[0,1]^{\mathsf E_{\mathcal O}},
\]
and
\[
 \mathbb T_{\mathcal O}(P)
 =
 \overline{\Phi_{\mathcal O}(\mathbb R)}.            \tag{1}
\]
Named probability coordinates and the distinguished dense clock orbit are
part of the object.

For this paper theorem, \(P\) is finite-dimensional autonomous unitary
dynamics and \(\mathcal O\) is phase-complete for a specified finite set of
visible gaps.

## 2. Phase-complete observers

Let
\[
 H=\sum_{j=1}^{D}E_j|j\rangle\langle j|
\]
on \(\mathbb C^D\). Let
\(\Omega=(\omega_1,\ldots,\omega_m)\in\mathbb R^m\) be the finite list of
energy gaps visible to an observer. Put
\[
 \Gamma_{\mathcal O}
 =
 \sum_{a=1}^{m}\mathbb Z\omega_a
 \subseteq\mathbb R,
 \qquad
 d_{\mathcal O}
 =
 \operatorname{rank}_{\mathbb Z}\Gamma_{\mathcal O}
 =
 \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
 \{\omega_1,\ldots,\omega_m\}.                       \tag{2}
\]

The observer is **phase-complete for \(\Omega\)** when its probability
coordinates continuously generate and separate the real and imaginary
parts of
\[
 \phi_\Omega(t)
 =
 (e^{-it\omega_1},\ldots,e^{-it\omega_m})
 \in\mathbb T^m.                                    \tag{3}
\]

The unrestricted finite quantum observer, allowed arbitrary state
preparation and effects, is phase-complete for every projective energy gap.
Indeed, for eigenvectors \(i,j\), superposition preparations and
measurements recover both
\(\cos(t(E_i-E_j))\) and \(\sin(t(E_i-E_j))\), while every Born probability
is a finite linear combination of those phase coordinates.

## 3. Master theorem

### Theorem A — observer time representation

For every finite gap packet \(\Omega\) and every phase-complete observer,
\[
 K_\Omega
 :=
 \overline{\phi_\Omega(\mathbb R)}
 \subseteq\mathbb T^m
\]
is a compact connected abelian group, and
\[
 \mathbb T_{\mathcal O}(P)
 \cong
 K_\Omega
 \cong
 \widehat{\Gamma_{\mathcal O}}
 \cong
 \mathbb T^{d_{\mathcal O}}.                         \tag{4}
\]
The first two identifications are canonical; the last requires a choice of
\(\mathbb Z\)-basis of \(\Gamma_{\mathcal O}\).

Consequently,
\[
 \dim_{\mathrm{top}}\mathbb T_{\mathcal O}(P)
 =
 d_{\mathcal O}.                                    \tag{5}
\]
The image of laboratory clock time is dense in this completed observer
time.

### Theorem B — full-channel law

Let
\[
 \mathcal U_H(t)=\operatorname{Ad}_{e^{-itH}}
\]
be the unitary channel. Give clock labels the operational pseudometric
\[
 d_H(s,t)
 =
 \frac12\|\mathcal U_H(s)-\mathcal U_H(t)\|_\diamond.
                                                               \tag{6}
\]
The metric completion after quotienting zero distance is canonically the
closure of the one-parameter subgroup \([e^{-itH}]\) in the projective
unitary group. If
\[
 \Gamma_H
 =
 \sum_{j=2}^{D}\mathbb Z(E_j-E_1),
\]
then
\[
 \dim_{\mathrm{top}}\overline{\{[e^{-itH}]:t\in\mathbb R\}}
 =
 \operatorname{rank}_{\mathbb Z}\Gamma_H.            \tag{7}
\]

Thus projective spectral rank is not merely a number assigned to a
Hamiltonian. It is the topological dimension of the minimal complete
operational time seen by a full channel observer.

### Theorem C — observer quotient and temporal-dimension conservation

Let two phase-complete observers have visible gap groups
\(\Gamma_1,\Gamma_2\subseteq\mathbb R\). Define
\[
 \Gamma_{1\vee2}=\Gamma_1+\Gamma_2,
 \qquad
 \Gamma_{1\wedge2}=\Gamma_1\cap\Gamma_2.              \tag{8}
\]
Then inclusions of gap groups dualize to canonical quotient maps
\[
 \widehat{\Gamma_{1\vee2}}\twoheadrightarrow
 \widehat{\Gamma_i}\twoheadrightarrow
 \widehat{\Gamma_{1\wedge2}}
 \quad(i=1,2).                                       \tag{9}
\]
Writing \(d(\Gamma)=\operatorname{rank}_{\mathbb Z}\Gamma\),
\[
 d(\Gamma_{1\vee2})+d(\Gamma_{1\wedge2})
 =
 d(\Gamma_1)+d(\Gamma_2).                            \tag{10}
\]

Hence observers can possess joint-only and shared temporal directions, but
the four dimensions satisfy an exact modular conservation law.

More generally, restriction of an operational observer is coordinate
projection in `(1)` and induces a continuous surjection of completed
observer times. For finite phase tori, temporal dimension cannot increase
under this restriction.

### Theorem D — exact return is geometry of completed time

Let \(\mu_\Omega\) be normalized Haar measure on \(K_\Omega\). For every
continuous \(F:K_\Omega\to\mathbb C\),
\[
 \lim_{T\to\infty}
 \frac1{2T}\int_{-T}^{T}F(\phi_\Omega(t))\,dt
 =
 \int_{K_\Omega}F\,d\mu_\Omega.                      \tag{11}
\]
For every Borel return neighborhood \(B\subseteq K_\Omega\) whose boundary
has Haar measure zero, the asymptotic fraction of clock labels landing in
\(B\) is \(\mu_\Omega(B)\).

Near the identity, every smooth nondegenerate metric on the
\(d_{\mathcal O}\)-torus has
\[
 \mu_\Omega(B_\varepsilon)
 =
 \Theta(\varepsilon^{d_{\mathcal O}}).               \tag{12}
\]
The constants depend on the lattice embedding and metric. No universal
product constant is asserted outside a maximal coordinate torus.

If \(H\) has simple spectrum, a positive nonzero exact projective return
exists exactly when \(d_H=1\). For \(d_H\ge2\), the clock orbit returns
arbitrarily closely but never exactly to the identity at positive time.

### Theorem E — every dimension of eternity is dense

Fix \(D\ge2\). In every operator-norm neighborhood of every Hermitian
\(D\times D\) matrix and for every
\[
 k\in\{1,\ldots,D-1\},
\]
there is a simple-spectrum Hermitian matrix \(K_k\), commuting with the
original matrix, whose full completed observer time has dimension \(k\).

For \(D\ge3\), exact completion dimension on simple-spectrum Hamiltonians is
nowhere continuous. Exact-periodic and no-positive-exact-return
Hamiltonians are both dense.

### Theorem F — every bounded present remains stable

For Hermitian \(H,K\), every \(T\ge0\), and every \(|t|\le T\),
\[
 \frac12
 \left\|
 \operatorname{Ad}_{e^{-itH}}
 -
 \operatorname{Ad}_{e^{-itK}}
 \right\|_\diamond
 \le
 |t|\,\|H-K\|
 \le
 T\,\|H-K\|.                                         \tag{13}
\]
Combining Theorems E and F: for every finite horizon \(T\), tolerance
\(\varepsilon>0\), target dimension \(k\), and Hermitian \(H\), one can
choose \(K_k\) with completed temporal dimension \(k\) such that the entire
full-channel history on \([-T,T]\) is within \(\varepsilon\) of that of
\(H\).

Thus exact observer-time dimension is a discontinuous property of temporal
completion, even though every bounded operational present is continuous.

## 4. Proof

### Proof of Theorem A

Define
\[
 L_\Omega
 =
 \{n\in\mathbb Z^m:n\cdot\Omega=0\}.
\]
The homomorphism
\[
 q:\mathbb Z^m\to\mathbb R,
 \qquad
 q(n)=n\cdot\Omega
\]
has kernel \(L_\Omega\) and image \(\Gamma_{\mathcal O}\). Hence
\[
 \mathbb Z^m/L_\Omega\cong\Gamma_{\mathcal O}.        \tag{14}
\]
Every finitely generated subgroup of \((\mathbb R,+)\) is torsion-free, so
\(\Gamma_{\mathcal O}\cong\mathbb Z^{d_{\mathcal O}}\).

Dualizing `(14)` identifies
\(\widehat{\Gamma_{\mathcal O}}\) with the closed subgroup
\[
 \{z\in\mathbb T^m:z^n=1\text{ for every }n\in L_\Omega\}.
                                                               \tag{15}
\]
The clock homomorphism \(t\mapsto\phi_\Omega(t)\) lands in `(15)`.
Its closure has trivial annihilator in
\(\Gamma_{\mathcal O}\): if
\(\gamma\in\Gamma_{\mathcal O}\) satisfies
\(e^{-it\gamma}=1\) for every \(t\in\mathbb R\), then
\(\gamma=0\). Characters separate closed subgroups of a compact abelian
group, so the clock image is dense in
\(\widehat{\Gamma_{\mathcal O}}\).

Phase completeness says the full operational probability map is a
continuous separating enlargement of the phase map and every added
coordinate is a continuous function of the phases. Its orbit closure is
therefore the graph of continuous functions over \(K_\Omega\), hence is
canonically homeomorphic to \(K_\Omega\). Finally,
\(\widehat{\mathbb Z^{d_{\mathcal O}}}\cong
\mathbb T^{d_{\mathcal O}}\), proving `(4)`--`(5)`.
\(\square\)

### Proof of Theorem B

The map
\[
 PU(D)\longrightarrow\{\text{linear maps on }M_D(\mathbb C)\},
 \qquad
 [U]\longmapsto\operatorname{Ad}_U
\]
is continuous and injective. Since \(PU(D)\) is compact and the channel
space is Hausdorff, it is a homeomorphism onto its image. The operational
metric `(6)` therefore induces the ordinary topology on the projective
unitary orbit. Applying Theorem A to the relative eigenphases
\((E_j-E_1)_{j=2}^{D}\) proves `(7)`. \(\square\)

### Proof of Theorem C

Every inclusion of discrete abelian groups
\(\Gamma'\hookrightarrow\Gamma\) dualizes to restriction of characters
\(\widehat\Gamma\twoheadrightarrow\widehat{\Gamma'}\); surjectivity follows
because characters into the divisible group \(\mathbb T\) extend from
subgroups. This gives `(9)`.

Tensor the two finitely generated torsion-free groups inside
\(\Gamma_1+\Gamma_2\) with \(\mathbb Q\). The ordinary vector-space
dimension formula gives
\[
 \dim(V_1+V_2)+\dim(V_1\cap V_2)
 =
 \dim V_1+\dim V_2,
\]
which is `(10)`. \(\square\)

### Proof of Theorem D

The clock orbit is a dense one-parameter subgroup of the compact abelian
group \(K_\Omega\). Its translation action is uniquely ergodic with Haar
measure: the time average of every nontrivial character is
\[
 \lim_{T\to\infty}
 \frac1{2T}\int_{-T}^{T}e^{-it\gamma}\,dt=0
 \quad(\gamma\ne0),
\]
while the trivial character averages to one. Finite linear combinations of
characters are uniformly dense in \(C(K_\Omega)\), proving `(11)`.
Approximation from above and below proves the boundary-zero Borel statement.

Local Haar measure on a \(d_{\mathcal O}\)-dimensional compact Lie group is
equivalent to Lebesgue measure in a smooth chart, proving `(12)`.

An exact positive projective return requires
\(t\gamma\in2\pi\mathbb Z\) for every
\(\gamma\in\Gamma_H\). A nonzero finitely generated subgroup of
\(\mathbb R\) admits such a \(t>0\) exactly when it is cyclic, equivalently
when its rank is one. \(\square\)

### Proof of Theorem E

After diagonalizing \(H\), perturb only its eigenvalues. Relative to one
eigenvalue, the gap vector lies in \(\mathbb R^{D-1}\).

For every \(k\in\{1,\ldots,D-1\}\), choose a dense \(k\)-dimensional
\(\mathbb Q\)-subspace
\[
 V_k=\operatorname{span}_{\mathbb Q}
 \{1,\theta,\ldots,\theta^{k-1}\}
 \subseteq\mathbb R
\]
with \(\theta\) transcendental. Because \(V_k\) contains \(\mathbb Q\), it
is dense in \(\mathbb R\). Tuples in \(V_k^{D-1}\) that span \(V_k\) are
dense: first choose \(k\) coordinates forming a nonzero rational minor,
then perturb all coordinates inside any prescribed box. Avoiding the
finitely many eigenvalue-collision hyperplanes is possible because their
union cannot contain an open box in the rational parameter space.

The resulting gap tuple is arbitrarily close to the original one, has exact
rational rank \(k\), and avoids every equality hyperplane. Restoring the
common energy shift gives a commuting simple-spectrum \(K_k\) arbitrarily
close to \(H\). Theorem B identifies rank with completed temporal dimension.

For \(D\ge3\), the rank-one and rank-\((D-1)\) loci are both dense, proving
nowhere continuity. Rank one gives exact periodicity by Theorem D; rank at
least two forbids positive exact return. \(\square\)

### Proof of Theorem F

Duhamel's formula gives
\[
 \|e^{-itH}-e^{-itK}\|
 \le |t|\,\|H-K\|.                                  \tag{16}
\]
For unitaries \(U,V\) and every trace-class \(X\), including an arbitrary
ancilla,
\[
 \|(U\otimes I)X(U^*\otimes I)
   -(V\otimes I)X(V^*\otimes I)\|_1
 \le 2\|U-V\|\,\|X\|_1.                             \tag{17}
\]
Taking the supremum over normalized \(X\), then using `(16)`, proves
`(13)`. The final statement follows by choosing the perturbation in Theorem
E smaller than \(\varepsilon/T\), with the \(T=0\) case immediate.
\(\square\)

## 5. What is new only if priority survives

Every ingredient has classical parents:

- Kronecker/Pontryagin orbit closure;
- Gelfand/operational compactification;
- projective unitary dynamics;
- Haar equidistribution;
- rational-rank stratification;
- Duhamel continuity; and
- rank modularity.

Potential novelty is the exact joined law:

1. complete operational histories canonically generate observer time;
2. its dimension is projective gap rank;
3. observer times form a quotient lattice with dimension conservation;
4. recurrence statistics are invariant volumes in that time;
5. every exact dimension is dense; and
6. all bounded presents remain continuously indistinguishable.

No novelty claim is authorized until external literature is checked against
this full conjunction and its physical interpretation.

## 6. Hostile boundary

1. This theorem covers finite autonomous closed quantum dynamics.
2. `(1)` exists generally, but its open and infinite classifications are not
   proved here.
3. Calling the orbit closure “physical time” is an interpretation; Nature
   relevance requires an operational protocol and a new prediction.
4. Topological dimension is exact-completion dimension, not a finite-noise
   estimator.
5. The dense instability theorem excludes rank zero from its dense spectrum.
6. Dimension instability begins at \(D=3\); a simple two-level system has
   only rank one.
7. The common observer time in Theorem C is a canonical common factor
   defined by gap-group intersection; it need not equal a literal
   intersection of laboratory protocol lists.
8. No gravity, black-hole, cosmological or arrow-of-time consequence follows
   from this finite theorem alone.

## 7. Promotion gates

- [x] proof-blind parent conjecture frozen
- [x] dependency-closed paper proof
- [x] full-channel operator normalization
- [x] exact observer quotient law
- [x] dense every-rank theorem
- [x] finite-horizon operational continuity
- [ ] independent specialist proof audit
- [ ] exact external priority audit
- [x] Lean formalization: complete.  Observer-time representation, full-channel dimension,
  observer quotient, equidistribution and exact return, small-ball law, dense every-rank
  instability with the commuting-matrix bridge, and the completely bounded finite-horizon channel
  law are all proved unconditionally and are axiom-clean
- [ ] resource-scale dimension construction
- [ ] open-system representation theorem
- [ ] infinite/continuous-spectrum representation theorem
- [ ] device-feasible estimator
- [ ] hostile Nature review

## 8. Formal proof status

File:
`formal/GaloisForLFunctions/HTGeometry/ArithmeticTemporalRankInstability.lean`.

Unconditional theorems:

- `exists_linearIndependent_close`;
- `exists_exactRationalRank_close_add`;
- `dense_exactRationalRank`;
- `rationalCoordinateRank_nowhereContinuous`; and
- `observerTemporalDimension_conservation`; and
- `finiteTemporalCompletion_instability_stability_core`.

The capstone joins dense exact-rank strata, nowhere continuity and exact
observer-dimension inclusion-exclusion with the previously proved
dimension-free finite-horizon operator-norm law for arbitrary unital
\(C^*\)-algebras.

Foreground verification passed with
`lake env lean
GaloisForLFunctions/HTGeometry/ArithmeticTemporalRankInstability.lean`.
The scratch axiom audit reports only `propext`, `Classical.choice` and
`Quot.sound`.

Not yet formalized:

- the phase-orbit closure representation `(4)`;
- topological dimension identification `(5)`--`(7)`;
- observer dual quotient `(9)`;
- Haar equidistribution `(11)`--`(12)`;
- the Hermitian eigenvalue-perturbation bridge from frequency packets to
  commuting matrices; and
- the diamond-norm channel form `(13)`.

## 9. Formal proof status: the completed-time representation

The representation theorems are now formalized unconditionally in
`formal/GaloisForLFunctions/HTGeometry/`.

**Infrastructure.**

- `IntegerTorusHomomorphism.lean` — `torusIntegerHom M` is the homomorphism of unit tori attached
  to an integer matrix, with `mFourier_torusIntegerHom` (a character pulls back to the character of
  the transposed vector), `torusIntegerHom_injective` (an integer left inverse gives injectivity),
  and `finiteClockPhasePoint_eq_torusIntegerHom` (a phase flow factors through the homomorphism of
  any integer presentation of its frequencies).
- `FrequencyLatticeBasis.lean` — `exists_frequency_integer_basis`: the group generated by a finite
  real frequency packet is free of finite rank, and a basis of it is a rationally independent
  family `γ` with integer matrices `M`, `A` satisfying `ω = M γ`, `A M = 1`; that basis is also a
  rational basis of the rational span, so its cardinality is the rational coordinate rank.

**Theorem A `(4)`, `(5)`.**

- `dense_range_finiteClockPhasePoint` — Kronecker density: a rationally independent packet has
  dense phase orbit.  Proved from the corpus law `finiteTorusPhaseProbabilityMeasure_tendsto_haar`
  by Urysohn separation: a continuous function vanishing on the orbit closure has vanishing Haar
  mean, and a nonnegative continuous function with vanishing Haar mean vanishes.
- `closure_range_finiteClockPhasePoint_eq` — through an integer presentation, the orbit closure is
  the range of the presenting homomorphism of tori.
- **`exists_completedTime_representation`** — the completed time
  `K_Ω = closure (range (finiteClockPhasePoint ω))` is a compact connected subgroup of the phase
  torus, equal to the range of an *injective* integer homomorphism from `𝕋^k` with
  `k = dim_ℚ span_ℚ (range ω)`;
- `orbitClosureAddEquiv`, `orbitClosureHomeomorph` — that homomorphism is an isomorphism of
  topological groups onto the completed time, which is therefore `𝕋^{d_O}`.
- `mFourier_eq_one_on_orbitClosure_iff` — the characters identically one on completed time are
  exactly those with vanishing detuning, so the character lattice of `K_Ω` is `ℤ^d / Γ_Ω^⊥` and its
  rank is `d_O`.  This is `(5)` in the character-lattice form, which is what the conservation law of
  Theorem C already uses.

**Theorem B `(7)`.**

- `exists_projectiveCompletedTime_representation` — the completed projective time of a finite
  spectrum is a torus of dimension the rational rank of its gap packet, i.e. `rank_ℤ Γ_H`.

**Theorem C, restriction half; `(9)`.**

- `image_closure_range_phaseRestrict` — observer restriction is coordinate projection and carries
  completed time *onto* completed time (the dual quotient of `(9)`);
- `finrank_span_restrict_le` — temporal dimension cannot increase under restriction.

**Theorem D `(11)` and exact return.**

- `orbitClosureHaar` and `orbitClosureHaar_mFourier_integral` — Haar measure of completed time,
  presented as the image of Haar measure of the presenting torus, with its Fourier coefficients;
- **`finiteTorusPhaseProbabilityMeasure_tendsto_orbitClosureHaar`** (and the presentation-free
  `exists_finiteTorusPhaseProbabilityMeasure_tendsto_orbitHaar`) — uniformly sampled clock time
  equidistributes in completed time: the phase laws converge weakly to its Haar measure.  This is
  `(11)`, in the exact form that gives the asymptotic fraction of clock labels in every
  continuity set;
- **`exists_ne_zero_return_iff`** — an exact nonzero return of the phase flow exists precisely when
  the completed time is at most one dimensional.  This is the last clause of Theorem D: for
  `d_H ≥ 2` the orbit returns arbitrarily closely but never exactly.

All of the above are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only) and wired into
`GaloisForLFunctions.HTGeometry`.

**The small-ball law `(12)`.**

`CompletedTimeSmallBall.lean`:

- `preimage_mk_ball_zero_inter` — in the fundamental domain, a circle ball of radius `ε ≤ 1/2` is
  the interval of twice that radius;
- `haarAddCircle_ball` — hence a circle ball of radius `ε ≤ 1/2` has Haar measure `2ε`;
- **`finiteTorusHaarProbabilityMeasure_ball`** — a ball of radius `ε ≤ 1/2` in the phase torus has
  Haar measure `(2ε)^{card}`.

On the presenting torus of the completed time this is `(12)` in exact form, with the constant
identified: the return volume is exactly `(2ε)^{d_O}`, so the exponent reads off temporal
dimension.  The statement of `(12)` for an arbitrary smooth nondegenerate metric is not formalized:
Riemannian volume comparison is not available in Mathlib, and the flat statement above is the one
the card's argument uses.

**Theorem E, spectrum half.**

`SimpleSpectrumRankBridge.lean`:

- `exists_rat_mul_close_notMem` — rational multiples of a nonzero real approximate every real while
  avoiding any finite set of multipliers;
- `exists_injective_rat_choice` — a rational property satisfiable outside every finite set is
  satisfiable by an injective family;
- `exists_injective_exactRank_close` — every real packet has arbitrarily close packets of any
  prescribed positive rank whose coordinates are nonzero and pairwise distinct;
- **`exists_simpleSpectrum_close_gapRank`** — every finite spectrum has arbitrarily close *simple*
  spectra whose gap packet has any prescribed positive rank not exceeding the number of gaps.

This is the arithmetic half of Theorem E in the form the matrix statement consumes: the perturbed
levels are all distinct (simple spectrum) and the completed observer time of the perturbed
Hamiltonian has exactly the prescribed dimension.  Distinctness comes from choosing the rational
multipliers injectively and away from `0` and `1`, which is what keeps a tail level off both `0`
and the head level it is built from.

**Theorem E, operator half.**

`SimpleSpectrumMatrixPerturbation.lean`:

- `isHermitian_unitary_conj_diagonal` — a real diagonal matrix conjugated by a unitary is Hermitian;
- `l2_opNorm_unitary_conj` — unitary conjugation does not increase the operator norm (from the
  C⋆-identity for the matrix operator norm);
- **`exists_isHermitian_commuting_close_gapRank`** — for every Hermitian `A`, every `ε > 0` and
  every `1 ≤ k ≤ D − 1` there is a Hermitian `B` with

  `B A = A B`, `‖B − A‖ < ε`, simple spectrum, and completed observer time of dimension exactly `k`,

  namely the conjugate by `A`'s eigenvector unitary of the perturbed diagonal.  Together with the
  nowhere-continuity of exact rank this is Theorem E in full.

**Theorem F and the channel form `(13)`.**

Mathlib has no completely bounded norms, so the amplification layer was built:

`KroneckerAmplification.lean`:

- `amplify Φ n` — the ancilla amplification of a map of matrices, acting blockwise;
- `amplify_conj` — the amplification of a conjugation is conjugation by the Kronecker product with
  the identity;
- `kronecker_one_mem_unitary` — that product is unitary;
- **`l2_opNorm_kronecker_one_le`** — amplification does not increase the operator norm, proved from
  the blockwise action on the coordinate decomposition of the amplified space.

`ChannelDiamondBound.lean`:

- `IsCbBound Φ c` — one constant bounding every ancilla amplification; `cbNorm` — the least such
  constant;
- **`isCbBound_conjugation_sub`** — `‖Ad_U − Ad_V‖_cb ≤ 2‖U − V‖`;
- **`isCbBound_unitaryEvolution_sub`** and **`cbNorm_unitaryEvolution_sub_le`** — for self-adjoint
  generators,

  `½ ‖Ad_{exp(-itH)} − Ad_{exp(-itK)}‖_cb ≤ |t| ‖H − K‖`,

  which is `(13)`.  For a difference of unitary conjugations the completely bounded norm and the
  diamond norm agree, so this is the diamond-norm statement of the card; the proof composes the
  amplification layer with the corpus C⋆ Duhamel bound
  `selfAdjoint_unitaryEvolution_norm_sub_le`, which is dimension-free.

Every theorem of the card is now formalized unconditionally and axiom-clean.
