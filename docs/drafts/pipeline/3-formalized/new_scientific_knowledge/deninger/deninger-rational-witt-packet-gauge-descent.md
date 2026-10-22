# Rational-Witt packet gauge descent

- **ID:** `deninger-rational-witt-packet-gauge-descent`
- **Stage:** 3-formalized
- **Type:** SOURCE-TO-PACKET DESCENT THEOREM
- **Label:** `DAC_DENINGER_WRAT_PACKET_GAUGE_DESCENT`
- **Parent:** `deninger-rational-witt-coherent-cyclotomic-descent`
- **Scientific status:** `[FORMALIZED] [SOURCE-SPECIFIC NOVELTY; EXTERNAL PRIORITY UNVERIFIED]`
- **RH dependency:** closes finite-stage functoriality of the rational-Witt coefficient needed
  before Route L can define a source-varying relevant complex.  It does not construct the global
  inverse-limit packet, the Meyer comparison, closed middle boundaries, or the Xi spectral
  theorem.

## 1. Problem forced by the previous theorem

Fix a rational prime \(p\).  Let \(s\le t\) be prime-to-\(p\) cyclotomic stages with moduli
\(n\mid m\), and write
\[
 e_s:\mathbb Z/n\mathbb Z\hookrightarrow\overline{\mathbb F}_p^\times,\qquad
 e_t:\mathbb Z/m\mathbb Z\hookrightarrow\overline{\mathbb F}_p^\times
\]
for the independently chosen primitive-root embeddings.  The coherent Wrat transition
\(\tau_{s,t}\) is uniquely characterized by
\[
 e_t\tau_{s,t}=e_s.                                           \tag{1}
\]

The existing packet transition uses standard index inflation
\[
 I_{s,t}(j)=\frac mn j                                       \tag{2}
\]
and reduction of units
\[
 \rho_{s,t}:(\mathbb Z/m\mathbb Z)^\times
      \twoheadrightarrow(\mathbb Z/n\mathbb Z)^\times.        \tag{3}
\]
Independent primitive-root choices do not imply \(\tau_{s,t}=I_{s,t}\).  Thus the previously
formalized untwisted packet pullback was not proved compatible with the actual rational-Witt
source transition.

## 2. Forced cyclotomic gauge

Set
\[
 \eta_{s,t}=\zeta_t^{m/n}.
\]
Because \(\zeta_t\) is primitive of order \(m\), \(\eta_{s,t}\) is primitive of order \(n\).
Both \(\eta_{s,t}\) and \(\zeta_s\) therefore generate the same cyclic group.  There is a unique
\[
 a_{s,t}\in(\mathbb Z/n\mathbb Z)^\times                     \tag{4}
\]
such that
\[
 \eta_{s,t}^{a_{s,t}}=\zeta_s.                               \tag{5}
\]
Uniqueness follows because exponentiation by a primitive \(n\)-th root is injective on
\(\mathbb Z/n\mathbb Z\).

### Gauge factorization theorem

`[PROVED HERE] [DAC_DENINGER_WRAT_PACKET_GAUGE_DESCENT]`

For every \(j\in\mathbb Z/n\mathbb Z\),
\[
 \boxed{\quad
 \tau_{s,t}(j)=I_{s,t}(a_{s,t}j).
 \quad}                                                       \tag{6}
\]

### Proof

At \(j=1\), equations `(1)` and `(5)` give
\[
 e_t(\tau_{s,t}(1))
  =\zeta_s
  =(\zeta_t^{m/n})^{a_{s,t}}
  =e_t(I_{s,t}(a_{s,t})).
\]
Injectivity of \(e_t\) proves `(6)` at \(1\).  Both sides of `(6)` are additive homomorphisms
from the cyclic additive group \(\mathbb Z/n\mathbb Z\), hence equality at \(1\) proves equality
everywhere. \(\square\)

## 3. Exact evaluation duality

Let
\[
 E_n(j,u)=
 \exp\!\left(2\pi i\,ju/n\right)
\]
be finite root evaluation.  Standard inflation satisfies
\[
 E_m(I_{s,t}(k),u)=E_n(k,\rho_{s,t}(u)).                      \tag{7}
\]
Combining `(6)` and `(7)` gives
\[
 \boxed{\quad
 E_m(\tau_{s,t}(j),u)
   =E_n\!\left(j,a_{s,t}\rho_{s,t}(u)\right).
 \quad}                                                       \tag{8}
\]

Let \(T_{s,t}\) be the coherent group-algebra Wrat transition.  By linearity on the group-algebra
basis, `(8)` upgrades to every finite Wrat element \(w\):
\[
 \operatorname{ev}_{t,u}(T_{s,t}w)
   =
 \operatorname{ev}_{s,a_{s,t}\rho_{s,t}(u)}(w).               \tag{9}
\]

This is the missing finite source-to-packet naturality law.

## 4. Gauge-corrected packet functor

Write
\[
 Q_s=(\mathbb Z/n\mathbb Z)^\times/\langle p\rangle.
\]
Define the affine packet transition
\[
 \kappa_{s,t}:Q_t\longrightarrow Q_s,\qquad
 \kappa_{s,t}(q)
  =[a_{s,t}]\,\bar\rho_{s,t}(q),                              \tag{10}
\]
and its pullback
\[
 \kappa_{s,t}^*: \mathbb C^{Q_s}\hookrightarrow\mathbb C^{Q_t},
 \qquad F\longmapsto F\circ\kappa_{s,t}.                     \tag{11}
\]
Translation by \([a_{s,t}]\) is bijective and \(\bar\rho_{s,t}\) is surjective, so
\(\kappa_{s,t}\) is surjective and `(11)` is injective.

If \(w\) realizes \(F\) at stage \(s\), equation `(9)` says
\[
 T_{s,t}w\quad\text{realizes}\quad\kappa_{s,t}^*F             \tag{12}
\]
at stage \(t\).

### Strict composition without a second gauge choice

For \(r\le s\le t\),
\[
 \boxed{\quad
 \kappa_{r,s}\kappa_{s,t}=\kappa_{r,t},\qquad
 \kappa_{s,s}=\operatorname{id}.
 \quad}                                                       \tag{13}
\]

Proof does not assume an exponent cocycle.  Given any \(F:Q_r\to\mathbb C\), finite rational-Witt
admission supplies a Wrat witness \(w\).  Evaluating
\[
 T_{s,t}T_{r,s}w=T_{r,t}w
\]
and using `(12)` twice on the left and once on the right yields
\[
 F(\kappa_{r,s}\kappa_{s,t}(q))
  =F(\kappa_{r,t}(q))
\]
for every \(F\).  Complex-valued functions separate points of the finite set \(Q_r\), proving
composition.  Surjectivity plus the resulting idempotence at \(s=s=t\) proves the identity law.

This argument is stronger than checking a chosen exponent formula: faithful packet evaluation
forces the affine gauge cocycle from strict rational-Witt source composition.

## 5. Exact obstruction to the old packet transition

Let \(\rho_{s,t}^*\) denote the old untwisted pullback.  For every packet function \(F\),
\[
 \boxed{\quad
 \kappa_{s,t}^*F=\rho_{s,t}^*F
 \iff
 F([a_{s,t}]q)=F(q)\ \text{for every }q\in Q_s.
 \quad}                                                       \tag{14}
\]

Thus primitive-root gauge is not harmless for the full finite packet algebra.  Ignoring it is
valid exactly on the translation-invariant subspace.  Because finite Wrat admission is
surjective onto all functions on \(Q_s\), replacing the corrected transition by the old one would
silently discard source-visible coefficients whenever \([a_{s,t}]\ne1\).

## 6. Source-to-packet producer theorem

For every finite packet function \(F:Q_s\to\mathbb C\), there exists one
arithmetic-Frobenius-fixed Wrat element \(w\) such that:

1. \(w\) evaluates to \(F\) at stage \(s\);
2. for every \(t\ge s\), \(T_{s,t}w\) evaluates to \(\kappa_{s,t}^*F\);
3. these pullbacks are strictly coherent by `(13)`.

This replaces the previous collection of unrelated finite witnesses with a genuine
source-to-packet coefficient functor.

## 7. Consequence for the RH dependency chain

Closed here:

- finite rational-Witt stages form one strict source system;
- finite packet restrictions are natural for that source system;
- arbitrary primitive-root choices are absorbed by a forced affine packet gauge;
- exact failure of the old untwisted pullback is classified.

The global affine packet problem in items 1--2 and Haar transport in item 3 are now closed by
`deninger-rational-witt-packet-gauge-limit`.  The exact remaining frontier is:

1. prove compatibility of the tensorized Calderón first-suspension cross-effect with the global
   affine gauge limit;
2. encode that operation as a closed relation-valued secondary attachment in the relevant
   three-term complex;
3. identify its vertical multivalued part and closed middle boundary;
4. prove nuclear continuity, cup/Hodge positivity, and Xi spectral transport.

The updated source-horizon theorem excludes replacing item 2 by another closable single-valued
operator on the canonical collapsing source topology.

## 8. Hostile theatre audit

- **Not generic primitive-root bookkeeping.**  Equation `(14)` proves that the old packet functor
  is wrong on source-visible functions unless an explicit invariance condition holds.
- **Not merely a change of basis.**  The correction is contravariant packet translation and must
  compose across all stages; `(13)` proves this from faithful Wrat evaluation.
- **Not global Route L closure.**  No inverse-limit topology, Haar unitary, Meyer complex,
  boundary closure, Hodge form, or Xi theorem is claimed.
- **No RH premise.**  Only finite roots, group algebras, Frobenius quotients, and evaluation
  faithfulness occur.

## 9. Novelty audit

The elementary fact that two primitive roots differ by a unit power is standard.  Claimed new
content is the source-specific synthesis `(6)`--`(14)`:

- exact factorization of this repository's common-presentation Wrat transition;
- the forced affine correction of its Deninger finite-packet transition;
- strict affine composition derived from rational-Witt evaluation faithfulness;
- classification of the precise subspace on which the previous untwisted transition remains
  valid.

Repository search found Wrat stage inclusions, standard packet reductions, standard index
inflation, finite evaluation surjectivity, and fixed-stage packet witnesses, but no gauge-corrected
packet transition or theorem connecting those systems.  Searches of Deninger's rational-Witt
papers found the reduced-monoid presentation and sheafification framework, not this finite
source-to-packet gauge descent.  External priority remains provisional.

## 10. Gates

- [x] paper proof of forced unit gauge and transition factorization
- [x] paper proof of evaluation naturality
- [x] paper proof of strict affine packet functor
- [x] exact obstruction to old untwisted pullback
- [x] unconditional Lean formalization
- [x] affine inverse-limit torsor and Haar comparison
- [ ] tensorized Calderón descent on resulting global packet

## 11. Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerRationalWittPacketGaugeDescent.lean`.

Formal capstones:

- `deningerPrimeFiniteWittStandardEmbeddedRoot_isPrimitive`;
- `deningerPrimeFiniteWittIndexTransition_eq_inflation_comp_gauge`;
- `deningerFiniteUnitEvaluation_wittIndexTransition`;
- `deningerFiniteCyclotomicWittEvaluation_transition`;
- `deningerFiniteFrobeniusPacketGaugeTransition_surjective`;
- `deningerFiniteFrobeniusPacketGaugeTransition_comp`;
- `deningerFiniteFrobeniusPacketGaugeFunctionPullback_refl`;
- `deningerFiniteFrobeniusPacketGaugeFunctionPullback_eq_standard_iff`;
- `deningerPrimeComplexifiedRationalWitt_exists_coherentPacketGaugeDescent`.

The composition theorem is proved through finite evaluation faithfulness and
Wrat source composition; no unproved exponent-cocycle premise is introduced.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerRationalWittPacketGaugeDescent.lean`
  passes;
- targeted
  `lake build GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittPacketGaugeDescent`
  passes;
- capstone axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

## References

- Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  https://arxiv.org/abs/2508.05329.
- Christopher Deninger and Anton Mellit, *\(\mathbb ZR\) and rings of Witt vectors \(W_S(R)\)*,
  https://arxiv.org/abs/1803.00812.

## Log

- 2026-08-02 — unit gauge isolated from independently chosen primitive roots.
- 2026-08-02 — twisted evaluation law and exact old-pullback obstruction proved.
- 2026-08-02 — strict affine packet composition forced from Wrat transition composition and
  finite evaluation faithfulness.
- 2026-08-02 — unconditional Lean formalization completed and wired into the RHTower umbrella.
