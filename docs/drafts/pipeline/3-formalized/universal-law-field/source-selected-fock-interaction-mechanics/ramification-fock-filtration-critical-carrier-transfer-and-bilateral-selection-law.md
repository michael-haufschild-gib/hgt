# Ramification Fock filtration, critical-carrier transfer, and bilateral selection law

- **ID:** ULF-SFIM-1
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveRamificationFockExcessSelection`
- **Type:** SOURCE-GENERATED FUSION / RECONSTRUCTION / GLOBAL FORMATION-PROPERNESS THEOREM
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [SOURCE-SELECTED FOCK FORMATION]`
  `[THREE-LAYER RECONSTRUCTION] [CRITICAL-CARRIER TRANSFER] [BILATERAL SELECTION] [LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS]`
  `[LEAN FORMALIZED] [PRE-ZERO] [NOT RH]`
- **Lean:** `GaloisForLFunctions.HTGeometry.ConstitutiveRamificationFockExcessSelection`
- **Parents:**
  `../../../../3-formalized/constraint-frame-relativity/ramification-diagonal-boolean-descent-route-e-schur-response-law.md`,
  `../../../../3-formalized/constraint-frame-relativity/ramification-excess-octahedral-composition-law.md`,
  `../formation-excess-mechanics/ramification-gibbs-gns-defect-spectral-information-and-boundary-work-law.md`,
  `../character-domain-formation-mechanics/reflected-euler-shell-cofinal-admission-selection-law.md`

## 1. Field-level pivot

The full high-exponent shell contains a source-selected Fock filtration.  It is not obtained by
choosing a tensor product after inspecting route endpoints.  For

\[
 a_m(N)=\mathbf 1_{\max_p v_p(N)=m},\qquad m\ge2,
\tag{SFIM.1}
\]

the source power map `k -> k^m` satisfies

\[
 \widetilde a_m(k^m)=\mu(k)^2.
\tag{SFIM.2}
\]

Thus the perfect-power part of the level-`m` shell is canonically the fermionic Fock space on the
prime species: occupancy is squarefree, repeated occupancy is excluded, and particle number is
`omega(k)`.  The source also supplies a strict complement: shell integers with at least one prime
exponent strictly between `0` and `m`.  That mixed-exponent complement, not the prime or Boolean
part, carries the critical normalization wall.

This changes the selection question.  Prime and Boolean routes are not expected to manufacture a
new relation that kills an off-centre grade.  Their source-selected formation is analytically too
small to carry the critical wall.  The missing landing must enter the mixed-exponent interaction
layer, where exact global formation properness is available.

## 2. Three source-generated layers

For real `sigma`, define the shell mass

\[
 M_m(\sigma;N)=a_m(N)N^{-\sigma}.
\tag{SFIM.3}
\]

Let `Pow_m(N)` mean that `N=k^m` for some integer `k`.  Define

\[
 \begin{aligned}
 F_m(\sigma;N)&=\mathbf1_{\operatorname{Pow}_m(N)}M_m(\sigma;N),\\
 X_m(\sigma;N)&=\mathbf1_{\neg\operatorname{Pow}_m(N)}M_m(\sigma;N).
 \end{aligned}
\tag{SFIM.4}
\]

Inside `F_m`, distinguish the one-particle and many-particle sectors:

\[
 \begin{aligned}
 P_m(\sigma;N)&=F_m(\sigma;N)\,
   \mathbf1_{N=p^m\text{ for a prime }p},\\
 B_m(\sigma;N)&=F_m(\sigma;N)-P_m(\sigma;N).
 \end{aligned}
\tag{SFIM.5}
\]

`P_m` is the prime/Mass/Weil/phase one-particle layer.  `B_m` is the multi-particle Boolean layer
carrying squarefree incidence, parity, and the finite Route-E rank/clock Schur capacity.  `X_m` is
the mixed-exponent interaction layer.

### Theorem 2.1 -- exact three-layer reconstruction

For every `m`, real `sigma`, and integer `N`,

\[
 \boxed{M_m(\sigma;N)=P_m(\sigma;N)+B_m(\sigma;N)+X_m(\sigma;N).}
\tag{SFIM.6}
\]

Moreover, on the perfect-power image,

\[
 \boxed{F_m(\sigma;k^m)=M_1(m\sigma;k).}
\tag{SFIM.7}
\]

#### Proof

Split first by `Pow_m(N)` and then split the power image by whether its unique `m`-th root is
prime.  Equation `(SFIM.7)` is the exact shell pullback
`a_m(k^m)=a_1(k)` together with `(k^m)^(-sigma)=k^(-m sigma)`.  QED.

This is joint reconstruction, not juxtaposition of route summaries.  All three layers are forced
by one coefficient law and their sum is coefficient-faithful.

## 3. Analytic fusion and source-selected Fock response

Let

\[
 S_m(s)=\sum_{N\ge1}a_m(N)N^{-s}.
\tag{SFIM.8}
\]

For `Re(s)>1`, coefficient reconstruction gives

\[
 \boxed{S_m(s)=S_1(ms)+C_m(s),}
 \qquad
 C_m(s)=\sum_N X_m(s;N).
\tag{SFIM.9}
\]

The inherited term is the nonunital fermionic grand response

\[
 S_1(ms)=\sum_{k>1}\mu(k)^2k^{-ms}
 =\frac{\zeta(ms)}{\zeta(2ms)}-1.
\tag{SFIM.10}
\]

Its one-particle part is `sum_p p^(-ms)`; the remaining squarefree terms form the multi-particle
Boolean part.  Hence the source answers the Fock-choice objection exactly: exterior statistics are
selected by `(SFIM.2)`, while the full shell records the interaction correction omitted by pure
Fock completion.

For every `sigma>1`, normalized positive mass gives the exact orthogonal GNS formation

\[
 L^2(M_m)=L^2(P_m)\oplus L^2(B_m)\oplus L^2(X_m).
\tag{SFIM.11}
\]

The three conditional laws plus their three masses reconstruct the full shell probability.  The
Dirichlet transform, positive measure, GNS spectrum, and particle filtration are therefore four
representations of one coefficient split.

## 4. Critical-carrier transfer

### Theorem 4.1 -- prime and Boolean layers cannot carry the shell wall

For `m>=12`, at `sigma=1`,

\[
 \boxed{
 \sum_NP_m(1;N)<\infty,\qquad
 \sum_NB_m(1;N)<\infty,\qquad
 \sum_NX_m(1;N)=\infty.}
\tag{SFIM.12}
\]

#### Proof

By `(SFIM.7)`, the full Fock image has mass

\[
 \sum_NF_m(1;N)=\sum_k a_1(k)k^{-m},
\tag{SFIM.13}
\]

which converges because `m>=2`.  Its two nonnegative sublayers `P_m` and `B_m` therefore converge.
The high-exponent shell has a positive simple pole at `sigma=1`; in the Lean surface used here,
`m>=12` supplies the already-certified non-summability of `M_m(1)`.  If `X_m(1)` were summable,
`M_m(1)=F_m(1)+X_m(1)` would be summable, contradiction.  QED.

This is an exact carrier-transfer law.  The critical defect cannot be produced inside the
one-particle prime skeleton or its fermionic Boolean completion.  Exact reconstruction places it
in the mixed-exponent interaction sector.

### Fourth-organ prediction

Any critical shell formation observable which is:

1. nonnegative and coefficient-faithful on the full shell;
2. finite on the prime and Boolean Fock layers; and
3. divergent at the shell normalization wall,

must report the divergence on `X_m`.  In particular a proposed critical selector factoring only
through the prime restriction or the perfect-power Boolean restriction cannot be complete.  This
predicts the missing carrier before using a Route-R, Route-L, Route-E, Mass, Weil, recurrence, or
Stokes endpoint.

## 5. Global formation/properness and exact bilateral selection

Define bilateral mixed-interaction admission at grade `t` by

\[
 \operatorname{Adm}^{\mathrm{int}}_m(t)
 \iff
 \forall\sigma>1:\quad
 \sum_NX_m(\sigma+t;N)<\infty
 \ \text{and}\
 \sum_NX_m(\sigma-t;N)<\infty.
\tag{SFIM.14}
\]

### Theorem 5.1 -- interaction properness selects the neutral grade

For every `m>=12`,

\[
 \boxed{\operatorname{Adm}^{\mathrm{int}}_m(t)\iff t=0.}
\tag{SFIM.15}
\]

#### Proof

If `t=0`, both series are summable for every `sigma>1`, since `X_m` is a nonnegative submass of
the shell.  If `t>0`, choose `sigma=1+t`; then the minus leg in `(SFIM.14)` is exactly
`X_m(1)`, which diverges by Theorem 4.1.  If `t<0`, choose `sigma=1-t`; then the plus leg is
`X_m(1)`.  QED.

Functional-equation reflection `t -> -t` is information-neutral: it merely swaps the two admission
legs.  Selection is produced by the globally quantified interaction formation and its critical
noncompactness, not by reflection itself.

## 6. Common intervention/generation grammar

The theorem gives a concrete mechanism law across heterogeneous organs:

1. **generate:** a source power formation selects exterior occupancy by `(SFIM.2)`;
2. **stratify:** particle number separates prime and Boolean formation layers;
3. **complete:** the source shell adds the mixed-exponent interaction complement;
4. **reconstruct:** coefficientwise sum `(SFIM.6)` and analytic sum `(SFIM.9)` recover the source;
5. **metrize:** positive shell mass turns the split into orthogonal GNS sectors;
6. **localize failure:** summability conservation transfers the critical wall to the only
   non-summable sector;
7. **select globally:** bilateral formation admission is proper exactly at neutral grade.

This is a mechanism, not an object called “curvature.”  Route theorems are local gauges of its
particle, Boolean, interaction, analytic, positive, or reflected faces.

## 7. What this changes in the RH architecture

The previous landing request was too coarse:

\[
 \text{physical law event}\Longrightarrow
 \operatorname{Adm}^{\pm}_m(t).
\tag{SFIM.16}
\]

The exact target can now be narrowed to

\[
 \boxed{
 \text{physical law event}\Longrightarrow
 \operatorname{Adm}^{\mathrm{int}}_m(t).}
\tag{SFIM.17}
\]

Once `(SFIM.17)` is constructed before zero specialization, Theorem 5.1 gives `t=0`; with
`t=Re(rho)-1/2` and functional-equation reflection, this is the RH selection step.  The present
card does not prove `(SFIM.17)`.  It proves that prime-only and Boolean-only searches cannot supply
it, identifies the unique source layer where it must land, and provides the complete unconditional
selection theorem after landing.

## 8. Sharp boundaries and falsifiers

1. `m>=2` is load-bearing for Fock-wall summability.  At `m=1`, the squarefree Fock layer itself
   has the critical pole.
2. `m>=12` is the certified shell-divergence range used by Lean.  Paper analyticity can lower parts
   of the statement, but no stronger range is claimed here.
3. The full shell coefficient law is load-bearing.  An arbitrary fermionic Fock completion has no
   reason to possess the mixed interaction sector.
4. Positivity is load-bearing for carrier transfer.  Signed cancellation could hide a divergent
   sector.
5. Reflection alone does not select.  It only supplies the two legs in `(SFIM.14)`.
6. The theorem supplies no Stokes contact, Hall seam, Xi-to-shell landing, or zero theorem.
7. A literal source realization in which the physical event lands entirely in `P_m+B_m` would
   falsify `(SFIM.17)` and show that this field mechanism does not close RH.

## 9. Lean correspondence

Lean proves, without added axioms or hypotheses beyond theorem parameters:

- `ramificationFockMass_pow`;
- `ramification_threeLayer_reconstruction`;
- `summable_ramificationFockMass_at_wall`;
- `summable_ramification_particleLayers_at_wall`;
- `not_summable_ramificationInteractionMass_at_wall`;
- `ramificationCriticalCarrierClassification`;
- `bilateralInteractionAdmission_iff`;
- `ramificationFockExcessSelection_capstone`.

The capstone depends only on standard mathlib foundations.  No RH assumption, Xi zero,
route-specific endpoint, numerical computation, or target-fitted selector enters the proof.

