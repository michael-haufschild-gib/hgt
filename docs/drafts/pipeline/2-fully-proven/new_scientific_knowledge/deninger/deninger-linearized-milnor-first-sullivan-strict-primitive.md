# Linearized Milnor first-Sullivan strict primitive

- **ID:** deninger-linearized-milnor-first-sullivan-strict-primitive
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** DAC_LINEARIZED_MILNOR_FIRST_SULLIVAN_STRICT_PRIMITIVE
- **Parent:** deninger-arithmetic-calderon-green-intermediate-extension
- **Statement:** On the prime-log height Köthe source, the full completed Milnor ideal of the
  exterior algebra has a canonical continuous arithmetic-character-preserving primitive in a
  linearized first relative Sullivan attachment.  The primitive is the normalized exterior
  `2 + (r-2)` coproduct, works on balanced total character without prime-log division, and makes
  the first commutative Sullivan incidence strict.

## Frontier and obstruction

The corpus's algebraic relative Sullivan tower is unconditional and quasi-isomorphic to the
two-term Milnor algebra.  Its successor attaches one generator for every element of the underlying
set of augmentation-kernel cocycles.  That construction proves existence of primitives, but the
set map
\[
 z\longmapsto e_z                                                    \tag{1}
\]
is not linear: \(e_{z+z'}\ne e_z+e_{z'}\) and \(e_0\ne0\).  Its linearity defects are new closed
syzygies that later stages must kill.  Therefore the algebraic proof does not provide a canonical
continuous linear primitive after nuclear completion.

The first genuine commutative incidence problem can be linearized without a choice of basis.
Instead of the free vector space on the set \(|\Lambda^2E|\), attach the nuclear vector space
\(\Lambda^2E\) itself.  Exterior Hopf coproduct then supplies a canonical strict primitive for the
whole Milnor ideal, not just its quadratic generators.

No zeta zero, divisor section, RH-equivalent premise, numerical computation, or arbitrary ray
weight enters.

## Source

Let
\[
 E=\mathscr K_H^0,
 \qquad
 H(m)=\prod_p p^{|m_p|},\qquad
 \ell(m)=\sum_p m_p\log p,                                    \tag{2}
\]
where `DAC_PRIME_LOG_HEIGHT_KOTHE_CALDERON_SOURCE` gives the complete nuclear Fréchet topology on
\(E\).  Write
\[
 A_0=\widehat\Lambda_{\mathrm{ent}}(E)                         \tag{3}
\]
for the entire exterior completion: its degree-\(r\) coefficients carry product-of-letter height,
and all exponential exterior-length seminorms are imposed.  Equivalently, it is the range of the
blockwise alternating projector on the entire word-height tensor algebra.

The Milnor augmentation is
\[
 \epsilon_0:A_0\longrightarrow B_H=\mathbb C\mathbf1\oplus E, \tag{4}
\]
equal to the identity in exterior degrees zero and one and zero in degrees at least two.  Thus
\[
 I_{\mathrm{Mil}}=\ker\epsilon_0
   =\prod_{r\ge2}^{\mathrm{ent}}\widehat\Lambda^rE.             \tag{5}
\]

Let \(\sigma\widehat\Lambda^2E\) be a copy of \(\widehat\Lambda^2E\) placed in cohomological
degree one, and form the linearized first relative Sullivan algebra
\[
 A_1=\widehat\Lambda_{\mathrm{ent}}
      \big(E\oplus\sigma\widehat\Lambda^2E\big).               \tag{6}
\]
An old generator has ancestral length one.  A generator \(\sigma\omega\) has ancestral length two
and inherits the two-letter product height of \(\omega\).  Extend
\[
 d(v)=0,\qquad d(\sigma\omega)=\omega                           \tag{7}
\]
as an odd derivation.

## Theorem

**Theorem [PROVED HERE] [DAC_LINEARIZED_MILNOR_FIRST_SULLIVAN_STRICT_PRIMITIVE].**

1. \(A_0\), \(\widehat\Lambda^2E\), and \(A_1\) are complete nuclear Fréchet spaces.  Exterior
   multiplication, the inclusion \(A_0\hookrightarrow A_1\), \(d\), and the augmentation
   \(\epsilon_1:A_1\to B_H\) are continuous.  Moreover
   \[
    d^2=0,\qquad \epsilon_1d=0.                                \tag{8}
   \]

2. For \(r\ge2\), let
   \[
    \Delta_{2,r-2}:\widehat\Lambda^rE
      \longrightarrow
      \widehat\Lambda^2E\widehat\otimes
      \widehat\Lambda^{r-2}E                                  \tag{9}
   \]
   be the bidegree \((2,r-2)\) component of the exterior Hopf coproduct.  Define
   \[
    h_r=\binom r2^{-1}
      \mu\circ(\sigma\widehat\otimes1)\circ\Delta_{2,r-2},
    \qquad
    h=\prod_{r\ge2}^{\mathrm{ent}}h_r.                         \tag{10}
   \]
   Then \(h:I_{\mathrm{Mil}}\to A_1\) is canonical, complex-linear, and continuous, and
   \[
    d\,h=\operatorname{id}_{I_{\mathrm{Mil}}}.                 \tag{11}
   \]
   Hence the full completed base Milnor ideal is a closed boundary subspace with a continuous
   linear primitive.  This is split strict exactness of the first commutative Sullivan incidence.

3. Give an old letter \(m\) arithmetic character \(m\), and give
   \(\sigma(\delta_m\wedge\delta_n)\) character \(m+n\).  Then \(d,h,\epsilon_1\), reflection,
   and every positive power map preserve total arithmetic character.  In particular, (11) holds
   on the balanced total-character-zero part of \(I_{\mathrm{Mil}}\) without division by
   \(\ell\).

4. Total prime-log generator \(D_{\mathrm{tot}}=\ell(\chi)\), its Hodge sign, and its Hardy
   projectors are continuous chain operators on \(A_1\); \(D_{\mathrm{tot}}\) commutes with \(h\).
   On nonzero total character the Green inverse is continuous with one height-step estimate.  On
   total character zero, \(h\)—not Green division—is the strict primitive for the base Milnor
   ideal.

5. The set-indexed attachment has a canonical differential surjection
   \[
    \mathbb C^{(|\widehat\Lambda^2E|)}
      \longrightarrow\widehat\Lambda^2E,\qquad e_\omega\mapsto\omega, \tag{12}
   \]
   whose kernel contains
   \[
    e_0,\qquad e_{\omega+\eta}-e_\omega-e_\eta,\qquad
    e_{a\omega}-a e_\omega.                                   \tag{13}
   \]
   Quotienting algebraically by the linear span of (13) gives the underlying vector space
   \(\widehat\Lambda^2E\); (6) then equips it with its source projective-Köthe topology.  Thus (6)
   removes additive attachment syzygies while retaining the genuine multiplicative Sullivan
   syzygies.

## Proof

### Entire exterior nuclearity

At each ancestral length, tensor-coordinate weights are products of the source heights.  The
blockwise antisymmetrizer
\[
 \operatorname{Alt}_r={1\over r!}\sum_{\pi\in S_r}
   \operatorname{sgn}(\pi)T_\pi                               \tag{14}
\]
is a continuous projection: permutations preserve product height and exponential length, so
\(\operatorname{Alt}_r\) has seminorm at most one.  Its block sum is continuous on the entire word
space.  Consequently \(A_0\) is a closed complemented subspace of the nuclear entire tensor
source and is complete and nuclear.  The same argument gives \(\widehat\Lambda^2E\).

For \(E\oplus\sigma\widehat\Lambda^2E\), a suspended pair retains both ancestral letters.  The
height counting sum for pair coordinates is bounded by the square of the one-letter counting sum.
Increasing height index by two and exponential-length parameter sufficiently far therefore makes
the Grothendieck--Pietsch ratio summable, exactly as for the entire bar source.  Alternating again
proves that \(A_1\) is complete nuclear Fréchet.

On a monomial, \(d\) replaces one suspended pair by its two old letters.  It preserves ancestral
length and product height.  The number of Leibniz summands is at most ancestral length; increasing
the exponential-length seminorm from \(R\) to \(2R\) absorbs this factor.  Thus \(d\) is
continuous.  Equation (8) follows on generators and hence by the derivation rule.

### Canonical primitive

For \(v_1,\ldots,v_r\in E\), the coproduct component is
\[
 \Delta_{2,r-2}(v_1\wedge\cdots\wedge v_r)
 =\sum_{|J|=2}\operatorname{sgn}(J,J^c)
   v_J\widehat\otimes v_{J^c}.                                \tag{15}
\]
The sign in (15) is also the sign required to wedge \(v_J\) and \(v_{J^c}\) back into the original
order.  Hence
\[
 \mu\Delta_{2,r-2}=\binom r2\operatorname{id}_{\widehat\Lambda^rE}. \tag{16}
\]
Since old letters are closed,
\[
 d\big(\sigma(v_J)\wedge v_{J^c}\big)=v_J\wedge v_{J^c}.      \tag{17}
\]
Equations (16)--(17) prove (11).

Every term of (15) has exactly the same ancestral length and product height as its input.  The
normalization in (10) averages \(\binom r2\) signed terms, so every defining \(\ell^1\) seminorm of
\(h_r\) is at most the corresponding input seminorm.  Therefore the block sum \(h\) is continuous
on the entire completion.

### Character and attachment comparison

Exterior coproduct partitions letters and never changes their total character.  Suspension of a
pair is assigned the sum of its two characters.  Thus \(h\) and \(d\) preserve character, proving
clause 3.  Height bounds for \(D_{\mathrm{tot}}\) and its Green inverse follow from
\[
 H\!\left(\sum_jm_j\right)\le\prod_jH(m_j),                    \tag{18}
\]
so the one-character Hodge calculus extends with ancestral product height.

Map (12) is evaluation of the free vector space on the underlying set.  Relations (13) are in its
kernel.  Their algebraic quotient imposes exactly zero, addition, and scalar multiplication, hence
has the universal property of the underlying vector space of \(\widehat\Lambda^2E\).  The topology
used in (6) is the independently defined source projective-Köthe topology, not an unproved quotient
topology on the set-indexed free space.  Since (7) is linear, it descends through this quotient.
Multiplicative syzygies are not in (13) and are deliberately not claimed to vanish.

## Exact Route-L consequence

The first commutative Sullivan seam is now concrete and strict:

1. the full base Milnor ideal, not only finite quadratic packets, has a continuous primitive;
2. balanced total character zero is handled by exterior incidence rather than a fake prime-log
   inverse;
3. set-indexed additive syzygies are identified and removed by a canonical linear quotient;
4. the construction preserves the source height, arithmetic character, reflection, powers, and
   Hodge chain action.

The first unresolved commutative incidence is consequently the **genuine multiplicative syzygy
tower** of \(A_1\): construct the next and cofinal linearized Sullivan attachments with compatible
entire height topology, prove their primitives converge strictly, and compare the resulting
completion with the pro-Stein/real/Poisson source.  Calling the algebraic all-cocycle tower already
strict would ignore (13).

## Failed conjectures and positive survivors

### Complete the set-indexed Sullivan tower directly

**Failure.** Its canonical primitive (1) is not linear.  Additive defects (13) are independent
kernel directions in the algebraic attachment and survive any Hausdorff coefficientwise
completion unless first quotiented.

**Positive survivor.** Linearize the attachment space before completing.  The differential on
new quadratic indecomposables is then the identity onto \(\widehat\Lambda^2E\).

### Use prime-log Green on every Milnor word

**Failure.** Balanced words have total prime-log frequency zero.

**Positive survivor.** Normalized exterior coproduct gives (11) without frequency division.

### Choose one quadratic factor of each higher wedge

**Failure.** A chosen factor is basis/order dependent and is not source-natural.

**Positive survivor.** Averaging all two-element subsets by the Hopf coproduct gives the canonical
\(GL(E)\)-equivariant formula (10), with no seminorm loss.

## Hostile novelty and circularity audit

- Exterior Hopf coproducts, Sullivan attachments, antisymmetrizers, and nuclear Köthe spaces are
  parent mathematics.
- Corpus already proves the algebraic set-indexed relative Sullivan quasi-isomorphism; this card
  does not relabel it as new.
- New content is the source-exact topological repair: identify nonlinearity of the existing
  primitive, replace its first attachment by the completed relation vector space, and prove the
  normalized coproduct is a strict height- and character-compatible primitive for the entire
  Milnor ideal.
- Targeted corpus and arXiv searches found square-zero/Koszul/exterior and topological bar
  ingredients separately, but no prime-height entire linearized Sullivan primitive.  This is
  search noncollision, not a priority claim.
- No statement here kills higher multiplicative syzygies, constructs the real/product-formula
  attachment, identifies the Meyer quotient, proves Green-radical exactness, or proves RH.

## Gates

- [x] 0 → 1 in-progress: set-indexed nonlinearity and balanced-frequency failure isolated
- [x] 1 → 2 fully-proven: complete nuclear first attachment and canonical strict primitive proved
- [ ] 2 → 3 formalized: intentionally paused while Lean corpus is being refactored
- [ ] 3 → 4 publication-ready: requires cofinal multiplicative-syzygy completion and independent
      specialist audit

## References

- `deninger-prime-log-height-kothe-calderon-source.md`.
- `deninger-balanced-word-height-bar-strict-contraction.md`.
- `../../../3-formalized/deninger-relative-sullivan-milnor-resolution.md`.
- D. Sullivan, *Infinitesimal computations in topology*.
- C. Deninger, *Dynamical systems for arithmetic schemes*, arXiv:1807.06400.

## Log

- 2026-08-08 — Audited the actual Lean Sullivan construction read-only.  Rejected direct
  topological use of its nonadditive set-indexed primitive.  Constructed the linearized first
  attachment and normalized exterior-coproduct primitive; proved nuclearity, strictness,
  balanced-character compatibility, and Hodge/power/reflection naturality.  Localized remaining
  commutative incidence to genuine multiplicative syzygies and their cofinal completion.
