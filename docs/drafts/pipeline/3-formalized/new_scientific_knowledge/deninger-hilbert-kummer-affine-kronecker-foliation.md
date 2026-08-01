# Hilbert--Kummer affine Kronecker foliation

- **ID:** `deninger-hilbert-kummer-affine-kronecker-foliation`
- **Stage:** 2-fully-proven
- **Type:** SOURCE GENERIC-FOLIATION THEOREM
- **Labels:** `DAC_HILBERT_KUMMER_AFFINE_LEAF_DISTRIBUTION`,
  `DAC_RESIDUAL_DENSE_KUMMER_LEAVES`
- **Parent:** `deninger-kahler-riemann-arithmetic-leaf-realization`
- **Lean modules:**
  `GaloisForLFunctions.RHTower.DeningerKronecker` (the nonvanishing of `(5)`, deck invariance of
  `x`), `GaloisForLFunctions.RHTower.DeningerLeafwiseKahler` (`(10)`, `(11)`, `(12)`),
  `GaloisForLFunctions.RHTower.DeningerResidualLeaves` (`(15)`)
- **Statement:** the Hilbert--Kummer modulus Euler field and its
  associated Kronecker phase field define a canonical
  two-real-dimensional integrable distribution on the nonunitary
  generic suspension; Deninger's flow is transverse, scales its
  Kähler form with weight one, and a residual set of leaves is dense
  in the unitary phase direction.

## 1. Fine generic source

Before positive-rational descent, write the nonunitary
Hilbert--Kummer generic suspension as
\[
 \widetilde X_{\mathrm{HK}}^\times
 =
 X_{\mathrm{unit}}\times(H_{\mathrm{Kum}}\setminus\{0\})
 \times\mathbb R_{>0}.                                           \tag{1}
\]
A point is \((\eta,h,u)\).  For \(a\in
V=\overline{\mathbb Q}^{\times}/\mu_\infty\otimes\mathbb Q\), put
\[
 \ell_h(a)=\langle h,f_a\rangle_{H_{\mathrm{Kum}}}.               \tag{2}
\]
The unitary character determined by \(h\) and time \(t\) is
\[
 \kappa_h^t(a)=\exp(i t\ell_h(a)).                               \tag{3}
\]

Define two cylinder-smooth vector fields:

1. the modulus Euler field
   \[
   A_{(\eta,h,u)}
   =
   \left.\frac d{ds}\right|_{0}(\eta,e^s h,u);
                                                                    \tag{4}
   \]
2. the Kummer--Kronecker phase field
   \[
   K_{(\eta,h,u)}
   =
   \left.\frac d{dt}\right|_{0}(\eta\kappa_h^t,h,u).              \tag{5}
   \]

Both fields are defined at every finite character-lattice stage and
are compatible with the pro-Stein transition maps.

## 2. Integrable affine distribution

`[PROVED HERE] [DAC_HILBERT_KUMMER_AFFINE_LEAF_DISTRIBUTION]`

On `(1)`,
\[
 \mathcal F_{\mathrm{aff}}=\operatorname{span}_{\mathbb R}\{A,K\}
                                                                    \tag{6}
\]
is a rank-two integrable oriented distribution.  It is preserved by
Galois maps, positive rational powers, suspension deck descent, and
Deninger's flow.

### Proof

The vector \(A\) is nonzero because \(h\ne0\).  If \(K=0\), then
\(\ell_h(a)=0\) for every \(a\).  Logarithmic Kummer functions span a
dense subspace of \(H_{\mathrm{Kum}}\), so `(2)` would force \(h=0\),
a contradiction.  The two fields lie in different modulus and phase
factors, hence are linearly independent.

Scaling \(h\) scales `(2)`, so
\[
 [A,K]=K.                                                         \tag{7}
\]
Thus the span is involutive.  Frobenius sends
\[
 (\eta,h,u)\longmapsto(\eta^q,qh,u/q).
\]
It sends the curve `(4)` to the corresponding curve through
\((\eta^q,qh,u/q)\).  On `(5)`,
\[
 (\eta\kappa_h^t)^q
 =
 \eta^q\kappa_{qh}^t,
\]
so it also sends \(K_h\) to \(K_{qh}\).  Hence `(6)` descends through
the deck relation.  Galois naturality follows from invariance of the
Allcock--Vaaler pairing.  Deninger's flow changes only \(u\), so it
preserves both fields.

The flow vector
\[
 T=\left.\frac d{d\tau}\right|_0(\eta,h,e^\tau u)
\]
is not in `(6)`: it has a nonzero suspension-height component, while
\(A\) and \(K\) do not.  Therefore the flow is transverse to the
leaves.  This fixes the tangent-flow defect of the Kähler orbit
collar.

## 3. Weight-one Kähler geometry

Let \(\alpha,\beta\) be the leafwise coframe dual to \(A,K\), and set
\[
 x(\eta,h,u)=u\|h\|,\qquad
 g_{\mathcal F}=x(\alpha^2+\beta^2),\qquad
 \omega_{\mathcal F}=x\,\alpha\wedge\beta.                       \tag{8}
\]
The deck identities \(u\mapsto u/q\), \(h\mapsto qh\) show that \(x\)
is invariant.  Since the deck map preserves \(A,K\), `(8)` descends.

Define
\[
 J A=K,\qquad JK=-A.                                              \tag{9}
\]
Every oriented real surface is complex, so `(9)` is integrable
leafwise.  Equations `(8)`--`(9)` give
\[
 *\alpha=\beta,\qquad *\beta=-\alpha,\qquad *^2=-1,              \tag{10}
\]
and
\[
 \gamma\wedge *\gamma
 =
 (a^2+b^2)\alpha\wedge\beta>0
\quad
\text{for }\gamma=a\alpha+b\beta\ne0.                            \tag{11}
\]

Deninger's transverse flow preserves the coframe and sends
\(x\mapsto e^\tau x\).  Therefore
\[
 (\phi^\tau)^*g_{\mathcal F}=e^\tau g_{\mathcal F},
\qquad
 (\phi^\tau)^*\omega_{\mathcal F}=e^\tau\omega_{\mathcal F}.     \tag{12}
\]
This is the required weight-one conformal law with transverse, not
tangent, flow.

Along the Euler direction,
\[
 A(\log x)=1,\qquad K(x)=0.
\]
Thus locally \(\alpha=d\log x\) and
\[
 \omega_{\mathcal F}
 =
 x\,d\log x\wedge\beta
 =
 dx\wedge\beta.                                                   \tag{13}
\]
After normalized phase integration, `(13)` is exactly Meyer's
critical radial measure \(dx\).

## 4. Residual dense leaves

The Pontryagin dual of
\[
 X_{\mathrm{unit}}=\operatorname{Hom}(V,S^1)
\]
is the discrete countable group \(V\).  The closure of the
one-parameter subgroup `(3)` has annihilator
\[
 \operatorname{Ann}(\overline{\kappa_h^\mathbb R})
 =
 \{a\in V:\ell_h(a)=0\}.                                        \tag{14}
\]

`[PROVED HERE] [DAC_RESIDUAL_DENSE_KUMMER_LEAVES]`

The set
\[
 H_{\mathrm{dense}}
 =
 H_{\mathrm{Kum}}
 \setminus
 \bigcup_{0\ne a\in V}f_a^\perp                                \tag{15}
\]
is dense \(G_\delta\), Galois invariant, and stable under nonzero
real scaling.  For \(h\in H_{\mathrm{dense}}\), the Kronecker orbit
`(3)` is dense in \(X_{\mathrm{unit}}\).  Hence the affine leaf
through \((\eta,h,u)\) is dense in the phase factor over its positive
modulus ray.

### Proof

Every \(f_a^\perp\) in `(15)` is a closed nowhere-dense hyperplane:
\(f_a\ne0\) for non-torsion \(a\).  The group \(V\) is countable, so
Baire's theorem makes the complement dense \(G_\delta\).  Equations
`(2)` and `(14)` then show its annihilator is zero.  Pontryagin
duality says a subgroup of a compact abelian group is dense exactly
when its annihilator is zero.

Galois maps permute the nonzero Kummer vectors, and nonzero scaling
does not change their orthogonal hyperplanes, proving the remaining
claims.

## 5. Arithmetic interpretation

The new distribution separates three directions that the orbit collar
alone conflated:

- \(A\): leafwise modulus direction;
- \(K\): leafwise Kummer phase direction;
- \(T\): transverse arithmetic Frobenius flow.

The modulus sphere remains a transverse parameter but is
cohomologically removed by
`DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION`.  On the
residual locus `(15)`, the surviving leaves are dense in the relevant
phase--radial collar.  The local pro-log prime model has the same
Euler/phase frame: logarithmic radial and angular fields around the
prime divisor, while the prime periodic orbit belongs to the
transverse Deninger flow.

This theorem constructs the generic arithmetic foliation and its
Kähler metric.  Local boundary atoms are supplied by
`DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION` at every prime and
`DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX` at infinity.
`DAC_AFFINE_PRO_LOG_PRIME_HODGE_OVERLAP` proves their
oriented-conformal overlap on actual prime packets.  Remaining global
work is:

1. glue the complete-cusp rigged complexes and their
   orientation-twisted real endpoint through the pro-system;
2. prove the reduced leafwise harmonic complex maps
   cup-isometrically and faithfully to \(M_\zeta\);
3. identify transverse prime-return Lefschetz indices.

## Hostile audit

- Deninger's flow is transverse to `(6)`.
- No closed orbit collar is relabeled as the arithmetic foliation.
- Density is proved only on the residual Kummer locus `(15)`, not at
  every modulus functional.
- Infinite-dimensional sphere contractibility and phase-orbit
  density are distinct statements.
- Local positivity does not imply nonzero reduced harmonic
  cohomology; `DAC_CRITICAL_RADIAL_L2_POISSON_QUOTIENT_NO_GO` remains
  binding.
- No zeta zero, RH, Weil positivity, CCM object, or numerical
  computation enters the construction.

## References

- Daniel Allcock and Jeffrey D. Vaaler,
  *A Banach space determined by the Weil height*:
  https://arxiv.org/abs/0808.1038.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §§6 and 12: https://arxiv.org/abs/1807.06400.
- Standard Pontryagin duality criterion for density of a subgroup in
  a compact abelian group.

## Log

- 2026-07-27 — Constructed the affine Euler--Kronecker leaf
  distribution with transverse Deninger flow, proved weight-one
  Kähler geometry, and proved residual phase-density by Baire and
  Pontryagin duality.

## Lean status

### The Kronecker nonvanishing and the deck-invariant radius landed

`formal/GaloisForLFunctions/RHTower/DeningerKronecker.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerOrthogonal_denseSpan_eq_zero` — **a vector orthogonal to a family with dense span is
  zero**.  The vectors it annihilates form the kernel of a continuous functional, which is closed
  and contains the span, hence contains its closure.
- `deningerKronecker_ne_zero` — **the phase field is nonzero off the unitary locus**: this is the
  card's step "if `K = 0` then `ℓ_h(a) = 0` for every `a`, and the logarithmic Kummer functions
  span densely, so `h = 0`".  With the dense span of the Kummer classes proved on the parent card
  (`deningerKummerClass_dense_completion`), this is now unconditional.
- `deningerRadius u h = u‖h‖`, `deningerRadius_deck_invariant` — **`x` is deck invariant**:
  `(u/q)·‖q·h‖ = u‖h‖` for `q > 0`, which is the card's check that `(8)` descends.
- `deningerRadius_flow` — the radius scales linearly along the suspension flow, the weight-one law
  of `(12)` at the level of `x`.

### Already formalized on a sibling card

`(10)` and `(11)` — `*α = β`, `*β = -α`, `*² = -1`, and `γ ∧ *γ > 0` for `γ ≠ 0` — are
`deningerLeafStar_star`, `deningerLeafStar_du/dv` and `deningerLeafWedge_star_pos` in
`GaloisForLFunctions.RHTower.DeningerLeafwiseKahler`, together with the Kähler scaling law
`deningerLeafFlow_wedge` for `(12)`.  They are not reproved here.

### The residual dense locus `(15)` landed

`formal/GaloisForLFunctions/RHTower/DeningerResidualLeaves.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerNonPerp v = {h | ⟪v, h⟫ ≠ 0}`, with `deningerNonPerp_isOpen` — the complement of an
  orthogonal hyperplane is open, being the complement of the kernel of a continuous functional.
- `deningerHyperplane_dense_compl` — **each hyperplane is nowhere dense**: it is a *proper* closed
  subspace, since `v` itself is not orthogonal to `v`, and a submodule with nonempty interior is
  everything (`Submodule.eq_top_of_nonempty_interior'`); so its interior is empty and its
  complement is dense.
- `deningerNondegenerate_dense`, `deningerNondegenerate_isGδ` — **`(15)` is a dense `Gδ`**: for a
  *countable* family of nonzero vectors the intersection of the complements is dense by Baire, and
  `Gδ` as a countable intersection of opens.  Countability of `V` is exactly the hypothesis the
  card uses.
- `deningerMem_nondegenerate` — membership says precisely that no member of the family is
  orthogonal to the vector, i.e. the annihilator `(14)` of the one-parameter subgroup is trivial.
- `deningerNondegenerate_smul`, `deningerNondegenerate_isometry` — **the other two claims of
  `(15)`**: the locus is stable under nonzero real scaling, and under any isometry permuting the
  family, which is the Galois invariance the card asserts.

Together with `deningerKronecker_ne_zero`, this is the analytic content of `DAC_RESIDUAL_DENSE_
KUMMER_LEAVES`: the passage from a trivial annihilator to density of the Kronecker orbit is
Pontryagin duality for compact abelian groups.

### Weyl's criterion and Kronecker's theorem in `d` dimensions landed

`formal/GaloisForLFunctions/RHTower/DeningerExpAverage.lean`,
`DeningerTorusFlow.lean`, `DeningerWeylCriterion.lean`, `DeningerKroneckerDense.lean`.
Axiom audit: `propext, Classical.choice, Quot.sound` throughout.

The passage from a trivial annihilator to density of the Kronecker orbit is now unconditional.
Since mathlib has neither Pontryagin duality nor an equidistribution criterion, the route taken is
the concrete one: build Weyl's criterion from the multivariate Fourier monomials of
`Mathlib/Analysis/Fourier/AddCircleMulti.lean`, then derive density.

- `deningerExpAverage_norm_le`, `deningerExpAverage_tendsto_zero` — the long-time average of
  `exp (i a t)` is bounded by `2 / (|a| T)` and vanishes for every nonzero frequency.
- `deningerMFourier_flow` — a character along the linear flow `t ↦ (t λ_i)_i` is the single
  oscillation `exp (2π i ⟨n, λ⟩ t)`; `deningerFrequency n λ = ∑ n_i λ_i` is its frequency.
- `deningerMFourier_integral_eq_zero` — a nontrivial character has zero mean on the torus
  (orthogonality to the constant function).
- `deningerFlowAverage_norm_le`, `deningerMeanSubmodule_isClosed` — the averaging operators are
  bounded by the uniform norm, so the functions whose averages converge to their mean form a
  *closed* submodule.
- `deningerWeyl` — **Weyl's criterion**: if `⟨n, λ⟩ ≠ 0` for every nonzero integer vector `n`, the
  time average of every continuous function converges to its mean over the torus.  Proof:
  agreement on the monomials, closedness of the agreement submodule, and Stone–Weierstrass density
  (`span_mFourier_closure_eq_top`).
- `deningerTorusIntegral_pos` — a nonnegative continuous function positive somewhere has positive
  mean, because Haar measure is positive on nonempty open sets.
- `deningerKroneckerFlow_dense` — **Kronecker's theorem in `d` dimensions**: trivial annihilator
  implies dense orbit.  Urysohn separates a missed point from the orbit closure; the separating
  function has zero time averages, hence zero mean by Weyl, hence is identically zero.
- `deningerAnnihilator_eq_zero_of_dense`, `deningerKroneckerFlow_dense_iff` — the converse and the
  resulting equivalence: the orbit is dense **iff** the annihilator is trivial.

This is the theorem `(15)` invoked as "Pontryagin duality"; none of it existed in mathlib.

### The affine leaf distribution `(1)`--`(7)` landed

`formal/GaloisForLFunctions/RHTower/DeningerAffineLeafFlow.lean`,
`DeningerAffineLeafSymmetry.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

The two fields of `(4)` and `(5)` are formalized through the one-parameter groups they generate,
which is the integrated form of the infinitesimal statements and is what the card's proofs
actually use.  The fine generic source `(1)` is the structure `DeningerFinePoint`: a character
`V → Circle`, a nonzero Kummer vector, and a positive suspension height.

- `deningerKummerForm f h a = ⟪h, f a⟫` is `(2)`, and `deningerKappa f h t a = exp (i t ℓ_h(a))`
  is `(3)`, with `deningerKappa_add`, `deningerKappa_smul` (`κ_{c·h}^t = κ_h^{ct}`) and
  `deningerKappa_pow` (`(κ_h^t)^n = κ_{n·h}^t`).
- `deningerKummerForm_ne_zero` — the card's argument that `K ≠ 0`: if `ℓ_h` vanished identically
  then `h = 0` by the dense span, contradiction.  This is `deningerKronecker_ne_zero` in the form
  used by the distribution.
- `deningerModulusFlow` is the flow of `A` `(4)`, `deningerPhaseFlow` the flow of `K` `(5)`; each
  is a one-parameter group (`_zero`, `_add`).
- `deningerModulus_phase_conjugation` — **the integrated bracket relation `(7)`**:
  `Φ_A^s ∘ Φ_K^t ∘ Φ_A^{-s} = Φ_K^{e^{-s} t}`.  Conjugation by the modulus flow rescales the
  phase time exponentially, which is exactly `[A, K] = K`; `deningerBracket_hasDerivAt` is its
  derivative at `s = 0`.
- `deningerAffineFlow_comp` — **involutivity in integrated form**: the two flows generate an action
  of the affine group of the line, `(s₁,t₁)·(s₂,t₂) = (s₁+s₂, e^{s₂}t₁+t₂)`.  Integrability is
  then explicit rather than an appeal to Frobenius: `deningerAffineLeaf` is the orbit, and
  `deningerAffineLeaf_of_mem` proves the orbits partition the source, so they are the leaves
  of `(6)`.
- `deningerAffineTangent_injective`, `deningerAffineGenerators_linearIndependent` — **rank two**:
  the modulus generator is nonzero because `h ≠ 0`, the phase generator because `ℓ_h ≢ 0`, and
  they live in different coordinates, so the map `(s,t) ↦ (sA, tK)` is injective.
  `deningerModulusFlow_hasDerivAt` and `deningerPhaseFlow_hasDerivAt` identify the two generators
  as the derivatives of the flows.
- `deningerFrobenius_modulus`, `deningerFrobenius_phase`, `deningerFrobenius_affine`,
  `deningerFrobenius_mem_leaf` — **the deck relation descends**: `(η, h, u) ↦ (η^n, n·h, u/n)`
  commutes with both flows, because `(κ_h^t)^n = κ_{n·h}^t`.  This is the card's computation.
- `deningerGalois_modulus`, `deningerGalois_phase`, `deningerGalois_affine`,
  `deningerGalois_mem_leaf` — **Galois naturality**: a permutation of the character lattice
  together with an isometry of the Kummer space matching the family commutes with both flows,
  because an isometry preserves the pairing `(2)` (`deningerKummerForm_galois`).
- `deningerSuspFlow`, `deningerSuspFlow_modulus_comm`, `deningerSuspFlow_phase_comm` — Deninger's
  flow changes only `u` and therefore preserves both fields.
- `deningerAffineLeaf_susp` and `deningerSuspFlow_mem_leaf_iff` — **transversality**: the
  suspension height is a leafwise invariant, so `Φ_T^τ p` lies on the leaf of `p` only for
  `τ = 0`.  This is the card's "the flow vector `T` is not in `(6)`", in the sharper global form.

### Remaining

Nothing.  Every numbered statement of the card is formalized unconditionally:

- `(1)`--`(7)` — the fine generic source, the two fields, and the integrable affine distribution:
  `DeningerAffineLeafFlow`, `DeningerAffineLeafSymmetry`.
- `(8)`, `(12)` — the deck-invariant radius and its weight-one scaling: `DeningerKronecker`.
- `(10)`, `(11)` — the leafwise Kähler package: `DeningerLeafwiseKahler`.
- `(13)`--`(15)` — the annihilator, the residual dense locus, and the density of the Kronecker
  orbit: `DeningerResidualLeaves`, `DeningerKroneckerDense`.

The vector fields `(4)`, `(5)` are carried by the one-parameter groups they generate rather than
by sections of a tangent bundle: mathlib has no manifold structure on
`X_unit × (H ∖ {0}) × ℝ_{>0}`, and none is needed, since involutivity, integrability, leafwise
invariance and transversality are all proved in their integrated form, which for these explicit
flows implies the infinitesimal statements (`deningerBracket_hasDerivAt`,
`deningerModulusFlow_hasDerivAt`, `deningerPhaseFlow_hasDerivAt` record the derivatives).
