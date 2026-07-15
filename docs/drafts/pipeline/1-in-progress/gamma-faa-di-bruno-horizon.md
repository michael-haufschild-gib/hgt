# The Faà di Bruno horizon of the Gamma pole tree

- **ID:** `gamma-faa-di-bruno-horizon`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Scientific status:** `[ALGEBRAIC CORE PROVED ON PAPER] [COMMON INVERSE COLLAR PROVED ON PAPER] [JET-GROUPOID BRIDGE OPEN] [NOVELTY UNVERIFIED]`
- **Statement:** The normalized inverse branches at the negative poles of Gamma form a cofinally
  Zariski-dense sequence in every finite jet group of formal diffeomorphisms tangent to the
  identity.  At every finite depth, independent pole labels give a cofinally dense family of
  complete prefix-composition flags.

## Source object

Write

\[
  \Gamma(-n+s_nB_n(T))=-\frac1T,\qquad
  s_n=\frac{(-1)^{n+1}}{n!},\qquad
  B_n(T)=T+\sum_{j\ge0}b_{n,j}T^{j+2}.
\]

For `m≥1`, let `G_m` be the unipotent algebraic group of substitutions

\[
  T+c_0T^2+\cdots+c_{m-1}T^{m+1}\pmod {T^{m+2}}.
\]

The already isolated inverse-branch theorem says that the pole-index germs
`n ↦ b_{n,j}` are countably algebraically independent over `ℂ`.

## Algebraic horizon theorem `[PROVED HERE]`

For every `m,N≥1`, the set

\[
  \{B_n\bmod T^{m+2}:n\ge N\}\subset G_m(\mathbb C)
\]

is Zariski dense.  More generally, fix `d` and lower bounds `N_1,...,N_d`.  The product family

\[
  (B_{n_1},...,B_{n_d}),\qquad n_r\ge N_r,
\]

is Zariski dense in `G_m^d`.  Consequently the prefix-flag family

\[
  \bigl(B_{n_1},\ B_{n_1}\circ B_{n_2},\ ...,
    B_{n_1}\circ\cdots\circ B_{n_d}\bigr)
\]

is Zariski dense in `G_m^d`.

### Proof

If a nonzero polynomial `P(c_0,...,c_{m-1})` vanished on one complete pole tail, then its
evaluation on the coefficient germs would be zero in the eventual sequence ring.  This
contradicts algebraic independence.  Hence every tail is dense.

For the product statement, regard a nonzero polynomial on `G_m^d` as a polynomial in the last
coefficient block.  One coefficient is a nonzero polynomial on the first `d-1` blocks.  Induction
chooses the first labels beyond arbitrary prescribed bounds where that coefficient survives; the
one-block theorem then chooses the last label.  Thus every product tail detects every nonzero
regular observable.

Finally,

\[
  (g_1,...,g_d)\longmapsto
  (g_1,g_1g_2,...,g_1\cdots g_d)
\]

is an algebraic automorphism of `G_m^d`, with inverse
`g_1=h_1`, `g_r=h_{r-1}^{-1}h_r`.  The truncated Faà di Bruno multiplication and inversion laws
are polynomial because `G_m` is unipotent.  The automorphism preserves Zariski density.

## Physical/topological content

The pole index is not a time parameter carrying one state along a flow.  Every sufficiently late
tail already fills every finite algebraic resolution of the formal-reparametrization group.  The
algebraic prefix flag records independently generic *normalized* local clocks.  It is a boundary
fiber of the actual analytic construction, not yet the exact composition law of nested Gamma
branches.

The Stone--Čech remainder of the pole labels is useful language for the eventual sequence ring,
but that identification is classical and is not the candidate novelty.  The source-specific claim
is the cofinal density of the actual Gamma inverse branches in every jet group and every finite
flag depth.

## Common inverse collar and the exact clock groupoid `[PROVED ON PAPER]`

Put

\[
 H_n(X)=\Gamma(-n+s_nX)^{-1},\qquad A_n(X)=-H_n(X).
\]

The factorial microscope already proves `A_n -> id` locally uniformly on the whole plane.  Fix
`0<rho<R<1/3`.  For all sufficiently large `n`,

\[
 \sup_{|X|=R}|A_n(X)-X|<R-\rho.
\]

For every `|T|<rho`, Rouche's theorem applied to `A_n(X)-T` and `X-T` gives exactly one zero in
`|X|<R`, counted with multiplicity.  It is therefore simple.  These zeros form one holomorphic
inverse `B_n` on the common disk, with `A_n(B_n(T))=T`; moreover `B_n -> id` with all derivatives
locally uniformly on that disk.

For `|y|>rho^{-1}`, define

\[
  I_n(y)=-n+s_nB_n(-1/y),
\]

so that `Gamma(I_n(y))=y`.  Increasing the pole threshold once more makes all image disks
`D(-n,|s_n|R)` pairwise disjoint and contained in the same exterior collar.  Cauchy estimates for
`B_n'` give a uniform contraction there.  Hence arbitrary finite inverse words exist, are
noncritical, and are distinguished by their pole labels.

There is an essential correction to the naive Faà di Bruno composition claim.  If `T=-1/y`, the
reciprocal coordinate of the inverse image is

\[
  -\frac1{I_n(y)}=C_n(T),\qquad
  C_n(T)=\frac1{n-s_nB_n(T)}.
\]

Thus an actual inverse word is represented by

\[
 C_{n_1}\circ\cdots\circ C_{n_d},
\]

not by `B_{n_1} o ... o B_{n_d}`.  The Möbius shells move the base point at every level.  The
correct finite-resolution object is consequently the groupoid of jets of local biholomorphisms
between varying reciprocal base points.  The pro-unipotent `B_n` family is the normalized clock
fiber inside this groupoid.

## Open jet-groupoid bridge `[CONJECTURE]`

A pole word determines nested points

\[
  I_{n_1}\circ\cdots\circ I_{n_d}(-n_{d+1})
\]

at which `Gamma^(d+1)` has a simple pole; this follows from the common collar and repeated
noncritical pullback.  What remains open is the algebraic identification of the actual moving-base
jet-groupoid flags with the Zariski-dense normalized `B_n` flags.  Since substitution into a power
series with nonzero constant term depends on infinitely many outer coefficients, ordinary formal
composition at zero is not a proof.  A valid bridge must use moving-base finite jets or an
iterated cofinal limit in the next pole labels.

The strong positive replacement for the failed direct composition is the thin universal-clock
horizon isolated in `gamma-thin-universal-clock-horizon.md`: actual inverse words give the Baire
topology, while every finite block of their normalized `B_n` decorations remains Zariski dense.

## Relation to differential independence

The flag theorem supplies the generic local time-change coordinates required by composition-depth
descent.  It does not by itself prove differential independence of the positive Gamma iterates:
one must still show that the nested analytic specialization is injective jointly with the
lower-iterate jet frame.  The existing pole/lower-frame scalar-extension theorem is the algebraic
part of that bridge; the uniform inverse-collar theorem is the analytic part.

## RH impact

The result gives a sharp archimedean no-compression law: no finite algebraic jet observable, and no
finite flag of such observables, characterizes the late Gamma pole boundary.  This constrains RH
architectures which replace the archimedean factor by a finite-state jet or moment closure.  It
does not locate zeta zeros or supply a positivity theorem, so its present RH impact is structural
only.

## Lean formalization of the one-block horizon `[PROVED IN LEAN]`

`GammaInversePoleBranchCofinalDensity.lean` formalizes the exact tail topology:

- `CofinallyZariskiDense` says that every nonzero polynomial observable survives beyond every
  prescribed pole horizon;
- `cofinallyZariskiDense_of_germ_algebraicIndependent` proves the general equivalence mechanism
  from algebraic independence in the `atTop` germ ring;
- `gammaInversePoleBranchCoefficient_cofinallyZariskiDense` applies it to every representative of
  the actual normalized inverse-Gamma branch coefficient germs;
- `gammaInversePoleBranchCoefficient_fin_cofinallyZariskiDense` proves the finite jet-group
  truncation consumed by the Faà di Bruno horizon theorem.

The exact module build and direct file elaboration pass.  Its formerly missing dependency closure
is cached; no full or concurrent build was used after serializing the missing modules.

The same verification repaired toolchain-level elaboration regressions in
`FormalUnitInverseFreeness.lean` and `GammaInversePoleBranchCoefficientFreeness.lean`; both direct
checks pass.  `GammaInverseBranchLowerJetFreeness.lean` also passes and supplies the lower-frame
disjointness needed by the future flag action.

## Initial priority audit

- Pedersen's *Inverses of gamma functions* (2013) proves Pick-function extensions and integral
  representations for real inverse branches.
- Jeffrey--Watt's *The Inverse of the Complex Gamma Function* (2023) constructs and charts complex
  branches and branch cuts.
- The classical Faà di Bruno literature identifies formal diffeomorphisms with a proalgebraic
  group and its coordinate Hopf algebra; Brouder--Frabetti--Krattenthaler and
  Frabetti--Manchon are the relevant parent sources.
- Current Gamma independence results found in the audit concern differential transcendence,
  translations, multiplication formulae, or independence from zeta/L-functions.

No audited source states algebraic independence of the complete pole-branch coefficient family,
cofinal Zariski density of those actual branches, or the finite-depth Gamma flag law.  This is an
initial negative search result, not yet an independent specialist priority certification.

## Gates

- [x] 0 → 1 in-progress: source-pure group object, exact algebraic theorem, proof, falsifier, and
  physical interpretation isolated
- [ ] 1 → 2 fully-proven: moving-base jet-groupoid density proved on paper, or the card split with
  the algebraic horizon and common-collar theorem promoted separately
- [ ] 2 → 3 formalized: cofinal density, finite product density, and prefix-flag automorphism
  formalized in Lean with serialized targeted verification; the one-block and finite-truncation
  portion is complete
- [ ] 3 → 4 publication-ready: primary priority audit across inverse Gamma, Faà di Bruno Hopf
  algebras, iteration singularities, and differential algebra

## Attacks

1. **Repackaging attack.**  Algebraic independence and Zariski density are equivalent at one
   level.  The candidate survives only through the source-specific all-tail, all-depth flag law
   and its analytic identification with the Gamma singularity tree.
2. **Stone--Čech attack.**  The corona of a discrete set and spectra of reduced products are
   classical parent infrastructure; they are excluded from the novelty claim.
3. **Singularity-depth attack.**  Differentially algebraic iterated tangent functions can have
   arbitrarily deep pole-condensation trees.  Tree depth alone detects no hypertranscendence.  The
   load-bearing datum is the algebraically generic Faà di Bruno decoration at every level.
4. **RH upcast attack.**  Infinite archimedean boundary rank is not a zero-free-region or sign
   theorem.  Any RH use needs an additional coupling to the scale-one functional equation and the
   continued divisor.
5. **Wrong composition attack.**  The actual reciprocal transition is
   `C_n(T)=1/(n-s_n B_n(T))`; prefix products of the tangent-to-identity `B_n` are not nested Gamma
   inverse words.  Any analytic claim that omits the moving Möbius shells is false.  The positive
   replacement is a holomorphic jet groupoid with the free `B_n` family as its normalized fiber.
