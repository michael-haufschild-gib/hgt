# Square-zero first-suspension cross-effect obstruction

- **ID:** `deninger-square-zero-first-suspension-cross-effect`
- **Stage:** 2-fully-proven
- **Type:** EXACT NO-GO WITH TENSOR-LINEARIZED POSITIVE SURVIVOR
- **Label:** `DAC_DENINGER_SQUARE_ZERO_FIRST_SUSPENSION_CROSS_EFFECT`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC NOVELTY; EXTERNAL PRIORITY UNVERIFIED]`
- **Claim:** the source-varying Calderón/rational-Witt first-suspension regulator is a nonzero
  bilinear cross-effect.  It has a canonical tensor linearization, but no ordinary linear map on
  the square-zero radial/phase direct sum can realize it.  Thus the square-zero totalization may
  be the underlying three-term complex, but it is not sufficient data for Route L's
  source-to-packet Cauchy restriction.

## 1. Exact interface

Fix a prime \(p\).  Let
\[
 Q_p=\mathbb C^2/\Gamma_p,\qquad
 \Gamma_p=\{(u,v):u=p^{-1}v\},                                  \tag{1}
\]
be the already-constructed Meyer--Poisson Calderón quotient.  Its canonical defect coordinate is
\[
 \bar\delta_p:Q_p\xrightarrow{\sim}\mathbb C,\qquad
 \bar\delta_p([u,v])=u-p^{-1}v.                                \tag{2}
\]
Let
\[
 P_p=L^2(B_p,\mathbb C),\qquad
 S_p=L^2(B_p\times\mathbb R/\log p\,\mathbb Z,\mathbb C),       \tag{3}
\]
and let \(T_p:P_p\hookrightarrow S_p\) be the canonical first-suspension isometry.  Put
\[
 c_p=p^{-1/2}>0.
\]

The fixed-packet regulator already in the corpus is
\[
 q\longmapsto \bar\delta_p(q)c_pT_p(a).
\]
Allowing the rational-Witt packet to vary exposes its true variance:
\[
 \boxed{\;
 \chi_p:Q_p\times P_p\longrightarrow S_p,\qquad
 \chi_p(q,a)=\bar\delta_p(q)c_pT_p(a).
 \;}                                                          \tag{4}
\]
It is complex-linear in each variable and vanishes on both coordinate axes.

## 2. Tensor linearization

By the tensor universal property, `(4)` has a unique complex-linear extension
\[
 \widetilde\chi_p:Q_p\otimes_{\mathbb C}P_p\longrightarrow S_p,
 \qquad
 \widetilde\chi_p(q\otimes a)=\chi_p(q,a).                     \tag{5}
\]
This is not an arbitrarily added tensor class.  Both factors and every normalization in `(5)` are
forced by existing source theorems: the first factor is the quotient by literal Meyer
boundaries, the second contains cofinal finite rational-Witt packet stages, \(c_p\) is polarized
half-density, and \(T_p\) is the first character of the literal mapping-torus circle.

Let
\[
 e_p=[(1,0)]\in Q_p.
\]
Then \(\bar\delta_p(e_p)=1\), so
\[
 \widetilde\chi_p(e_p\otimes a)=c_pT_p(a).                    \tag{6}
\]
Since \(c_p\ne0\) and \(T_p\) is injective, `(6)` is nonzero for every \(a\ne0\).
In particular, if \(F\ne0\) is a function on any finite Frobenius packet stage, the established
rational-Witt bridge supplies an arithmetic-Frobenius-fixed
\(\mathbb C\otimes W_{\rm rat}(\overline{\mathbb F}_p)\) witness whose packet vector \(a_F\) is
nonzero.  Therefore
\[
 \widetilde\chi_p(e_p\otimes a_F)\ne0.                         \tag{7}
\]
The tensor survivor is source-nonvacuous on every nonzero finite Wrat stage.

## 3. Direct-sum no-go

`[PROVED HERE] [DAC_DENINGER_SQUARE_ZERO_FIRST_SUSPENSION_CROSS_EFFECT]`

There is no complex-linear map
\[
 L:Q_p\oplus P_p\longrightarrow S_p                            \tag{8}
\]
such that
\[
 L(q,a)=\chi_p(q,a)\qquad\text{for every }q\in Q_p,\ a\in P_p. \tag{9}
\]

### Proof

If `(9)` held, then axis vanishing and linearity would give
\[
\begin{aligned}
 \chi_p(q,a)
   &=L(q,a)\\
   &=L((q,0)+(0,a))\\
   &=L(q,0)+L(0,a)\\
   &=\chi_p(q,0)+\chi_p(0,a)=0
\end{aligned}                                                   \tag{10}
\]
for every \(q,a\).  Taking \(q=e_p\) and any nonzero finite rational-Witt packet \(a_F\)
contradicts `(7)`.  Hence `(8)`--`(9)` cannot exist. \(\square\)

The conclusion is stronger than “the current proof omitted a compatibility lemma.”  An
ordinary degree-one linear cochain map on the direct sum is the wrong variance: it must be
additive across the two axes, while the actual source-varying Cauchy value is their cross-effect.

## 4. Correction to the square-zero claim

`DAC_DENINGER_POISSON_RELEVANT_COMPLEX_AMALGAMATION` correctly observes that adjoining a raw
global product
\[
 P_{\mathbb Q}\widehat\otimes M_\zeta
\]
as a new degree-two cohomology group would corrupt the desired three-term amplitude.  The present
theorem does not reinstate that group.

What fails is the stronger claim that deleting all mixed positive data still leaves enough
structure to construct the arithmetic Cauchy restriction.  The underlying square-zero
totalization
\[
 C^1=H_-\oplus P_{\mathbb Q}                                   \tag{11}
\]
forgets `(4)`.  Freezing \(a\) externally turns `(4)` into a linear map in \(q\), which explains
why all existing fixed-packet regulators typecheck.  But that maneuver cannot prove a
source-varying restriction containing all finite rational-Witt stages: it moves the arithmetic
packet from source data into an external parameter.

Thus `(11)` can survive only as the underlying cochain complex.  Route L additionally requires a
mixed \(k\)-invariant, module action, bar differential, or equivalent secondary operation whose
local value is `(5)`.  The tensor belongs in the operation's domain, not as an extra cohomology
class.

## 5. Strongest positive survivor

The exact replacement architecture is:

1. retain the unit-amalgamated square-zero three-term complex for its claimed amplitude;
2. equip its local degree-one Calderón quotient and rational-Witt packet restriction with
   \(\widetilde\chi_p\) from `(5)`;
3. sheafify these tensor-linearized maps compatibly over the cofinal finite Frobenius stages;
4. encode them as a secondary attachment before taking global cohomology;
5. prove the completed all-prime attachment is continuous and that its closed radical is exactly
   the arithmetic middle-boundary relation.

This is a positive construction theorem at the local algebraic level, not a restated negation.
It identifies the missing datum, constructs it canonically, proves actual Wrat nonvacuity, and
specifies where it must live without changing the three-term cohomology groups.

## 6. Hostile theatre audit

- **Not generic bilinearity advertised as number theory.**  The abstract axis argument is
  elementary.  New content claimed here is its concrete application to two independently
  formalized Route L interfaces, exposing that the proposed square-zero coefficient forgets the
  only known source-native Wrat/Calderón coupling.
- **Not a rediscovery of the first mode.**  \(T_p\), its injectivity, and finite Wrat admission are
  prior results.  The new theorem changes their role from a fixed external packet to a varying
  source factor and derives the resulting obstruction.
- **Not a raw tensor-product reversal.**  No new \(H^2\) summand is asserted.  The tensor
  linearizes a secondary map.
- **Not target-selected.**  Quotient, packet, half-density, and suspension character are all
  source-forced and already fixed before `(4)`.
- **Falsifier.**  The obstruction fails to constrain Route L if one constructs a natural
  source-to-packet Cauchy map whose packet is provably structural coefficient data rather than a
  varying source class.  Such a construction must state and prove that distinction; no current
  module does.
- **Remaining debt.**  `(5)` is local and algebraic.  It does not prove sheaf descent, nuclear
  continuity, global boundary classification, Paugam cup/Hodge compatibility, or Xi transport.

## 7. Novelty audit

Repository-wide search covered all Deninger Lean modules and all Deninger pipeline cards.  Existing
work contains the square-zero direct sum, finite rational-Witt packet density, first suspension
isometry, fixed-packet Calderón regulator, and warnings about generic Milnor/Meyer cross terms.
No existing theorem varies both Calderón and packet inputs, linearizes their concrete regulator
through \(Q_p\otimes P_p\), or proves the direct-sum no-go `(8)`--`(10)`.

Primary-source search covered Meyer's nuclear Fréchet quotient, Deninger's rational-Witt
dynamical-space/relevant-complex program, and Paugam's symplectic pairing.  Those sources provide
the three parent interfaces separately.  No located source states this rational-Witt
first-suspension cross-effect obstruction or its tensor-linearized survivor.  External priority
remains provisional pending specialist review.

## 8. Gates

- [x] source-pure statement and exact paper proof
- [x] no-go closure with nontrivial tensor survivor
- [x] actual finite rational-Witt nonvacuity
- [ ] unconditional Lean formalization
- [ ] finite-stage naturality and sheaf descent
- [ ] completed global secondary attachment and exact closed radical

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  https://arxiv.org/abs/math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  https://arxiv.org/abs/1807.06400.
- Frédéric Paugam, *Spectral symmetries of zeta functions*,
  https://arxiv.org/abs/0803.0199.

## Log

- 2026-08-02 — full Deninger corpus audit separated producer theorems from parameterized
  consumer structures and rejected the peripheral Baire route.
- 2026-08-02 — source-varying first-suspension cross-effect isolated; direct-sum no-go and
  tensor-linearized positive survivor proved on paper.
