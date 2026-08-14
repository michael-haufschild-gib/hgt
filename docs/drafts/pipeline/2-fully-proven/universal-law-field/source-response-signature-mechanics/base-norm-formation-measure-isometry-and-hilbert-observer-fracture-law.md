# Base-norm formation-measure isometry and Hilbert observer fracture law

- **ID:** ULF-SRSM-8
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / SOURCE-GENERATED GLOBAL TOPOLOGY / EXACT RECONSTRUCTION
- **Source:** ULF-SRSM-7 grade-only Hilbert completion no-go
- **Statement:** The complete family of subset-phase probability laws defines an isometric
  formation map from the coefficient base space `ell^1` into vector measures with total-variation
  norm.  Total mass is a contractive left inverse, so the entire all-grade source is uniformly
  reconstructible without adaptive scalar weights.  Finite-horizon CDF/Hilbert observation is a
  bounded but nonproper quotient and exactly recreates the arity-cofinal fracture.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [PRE-ZERO]`
  `[ALL-GRADE BASE-NORM ISOMETRY] [COMMON RECOVERY] [SOURCE-GENERATED TOPOLOGY]`
  `[MEASURE COMPLETION] [HILBERT OBSERVER NONPROPER]`
  `[LEAN CORPUS AUDITED READ-ONLY; NO LEAN WRITE/BUILD] [NOT RH]`

## 1. Positive survivor of the scalar-weight no-go

ULF-SRSM-7 proves that no scalar weight depending only on grade can make the all-prime CDF tower
both bounded and bounded below in its natural Hilbert observer.  The wrong conclusion would be
that formation itself is globally nonproper.

The source produces probability laws before it produces their CDF traces.  Probability laws have
a canonical topology: total variation, whose coefficient space is a base-norm `ell^1` space.  In
that topology, total mass is conserved exactly.  The complete tower is not merely proper; it is an
isometry.

## 2. Complete formation measure

Let

\[
 \mathbb I=\bigsqcup_{r\ge1}\mathbb P^{(r)}
 \tag{BNF.1}
\]

be all finite unordered prime tuples.  For `I∈mathbb I`, let `mu_I` be the probability law on
`Omega=[0,infinity)` of the sum of the `2^|I|-1` independent exponential phases indexed by the
nonempty subsets of `I`, with subset rate equal to the sum of its prime logarithms.

Put

\[
 E=\ell^1(\mathbb I).
 \tag{BNF.2}
\]

For `d=(d_I)∈E`, define the `E`-valued measure

\[
 \boxed{
 (\mathfrak M d)(B)=\bigl(d_I\mu_I(B)\bigr)_{I\in\mathbb I}}
 \qquad(B\subseteq\Omega\ \text{Borel}).
 \tag{BNF.3}
\]

Absolute summability makes this a countably additive finite `E`-valued measure.  Let
`M(Omega;E)` carry the vector total-variation norm.

### Theorem 2.1 — complete base-norm formation isometry

For every `d∈ell^1(mathbb I)`,

\[
 \boxed{
 |\mathfrak Md|(B)=\sum_I|d_I|\mu_I(B),
 \qquad
 \|\mathfrak Md\|_{\mathrm{TV}}=\sum_I|d_I|=\|d\|_{\ell^1}.}
 \tag{BNF.4}
\]

Hence `mathfrak M` is a linear isometric embedding with closed range across all grades and all
prime channels.

### Proof

For a finite measurable partition `B=bigsqcup_k B_k`,

\[
 \sum_k\|(\mathfrak Md)(B_k)\|_{\ell^1}
 =\sum_k\sum_I|d_I|\mu_I(B_k)
 =\sum_I|d_I|\mu_I(B).
 \tag{BNF.5}
\]

The equality uses Tonelli for nonnegative series and countable additivity of each probability
measure.  The right side is independent of the partition, so taking the supremum over partitions
gives the first identity in `(BNF.4)`.  Set `B=Omega` and use `mu_I(Omega)=1` for every channel.
QED.

No tuple-dependent weight was inserted.  Source dependence lives in the shape of `mu_I`; unit
mass supplies one common coefficient norm.

## 3. Exact common recovery

For an `E`-valued measure `nu=(nu_I)_I`, define its mass recovery whenever the coordinate masses
form an `ell^1` sequence:

\[
 \mathsf R(\nu)=\bigl(\nu_I(\Omega)\bigr)_I.
 \tag{BNF.6}
\]

### Theorem 3.1 — contractive reconstruction

On finite `ell^1`-valued measures,

\[
 \boxed{
 \|\mathsf R\nu\|_{\ell^1}\le\|\nu\|_{\mathrm{TV}},
 \qquad
 \mathsf R\mathfrak M=\operatorname{id}_{\ell^1(\mathbb I)}.}
 \tag{BNF.7}
\]

Consequently

\[
 \boxed{\mathfrak M\mathsf R}
 \tag{BNF.8}
\]

is a norm-one projection onto the formed range.

### Proof

For every finite channel set `F`, choose coordinate phases of modulus one so that
`theta_I nu_I(Omega)=|nu_I(Omega)|`.  The corresponding `ell^infinity` functional on `E` has norm
one.  Applying the definition of vector variation to `Omega` gives

\[
 \sum_{I\in F}|\nu_I(\Omega)|\le\|\nu\|_{\mathrm{TV}}.
\]

Increase `F` to all channels to obtain the contraction.  For a formed measure,

\[
 (\mathsf R\mathfrak Md)_I=d_I\mu_I(\Omega)=d_I.
\]

The projection statement follows from an isometry with a contractive left inverse.  QED.

This is joint reconstruction, not one finite-grade frame estimate.  The same recovery functional
works at every grade and for every source tuple.

## 4. Density realization

Every `mu_I` has a nonnegative phase-type density `h_I` with

\[
 \int_0^\infty h_I(t)dt=1.
 \tag{BNF.9}
\]

Define

\[
 (\mathfrak Dd)(t)=\bigl(d_Ih_I(t)\bigr)_I.
 \tag{BNF.10}
\]

### Corollary 4.1 — all-grade density isometry

\[
 \boxed{
 \|\mathfrak Dd\|_{L^1((0,\infty);\ell^1)}
 =\int_0^\infty\sum_I|d_I|h_I(t)dt
 =\|d\|_{\ell^1}.}
 \tag{BNF.11}
\]

### Proof

Tonelli and `(BNF.9)`.  QED.

The measure formulation remains the correct completion: high-prime phases can concentrate toward
`delta_0`, and high-arity low-prime phases can escape every finite horizon.  Both retain unit total
variation even when no `L^1` density limit remains inside the original function class.

## 5. Hilbert CDF observation is the fracture map

For `T>0`, define finite-horizon CDF observation on formed measures by

\[
 (\mathsf C_T\mathfrak Md)(t)
 =\bigl(d_I\mu_I([0,t])\bigr)_I
 =\bigl(d_IH_I(t)\bigr)_I.
 \tag{BNF.12}
\]

View the output in `L^2((0,T);ell^2(mathbb I))`.

### Theorem 5.1 — observation contraction and exact loss of properness

The composite

\[
 \mathsf C_T\mathfrak M:
 \ell^1(\mathbb I)\longrightarrow L^2((0,T);\ell^2(\mathbb I))
 \tag{BNF.13}
\]

is bounded with norm at most `sqrt T`, but it is not bounded below.  On the first-prime channel
`I_r` of grade `r`,

\[
 \boxed{
 \|\mathsf C_T\mathfrak Me_{I_r}\|_2
 =\|H_{I_r}\|_{L^2(0,T)}\longrightarrow0,}
 \tag{BNF.14}
\]

while

\[
 \boxed{
 \|\mathfrak Me_{I_r}\|_{\mathrm{TV}}=1.}
 \tag{BNF.15}
\]

### Proof

Since `0≤H_I≤1`,

\[
 \|\mathsf C_T\mathfrak Md\|_2^2
 =\sum_I|d_I|^2\int_0^TH_I(t)^2dt
 \le T\sum_I|d_I|^2
 \le T\|d\|_1^2.
\]

The limit `(BNF.14)` is Corollary 6.2 of ULF-SRSM-7.  Equation `(BNF.15)` is Theorem 2.1.  QED.

Thus arity-cofinal nonproperness is not loss of source mass.  It is the exact effect of applying a
finite-horizon integrated Hilbert observer to a globally proper base-norm formation.

## 6. Functorial laws

The construction has three coordinate-free functorialities.

### 6.1 Channel relabeling

Every bijection `sigma:mathbb I→mathbb I` that carries the source laws by
`mu_(sigma I)=A_*mu_I` for a measurable bijection `A` acts isometrically on coefficients and vector
measures.  Formation intertwines these actions.  This includes schedule relabeling and any genuine
functional-equation action already represented on the phase law.

### 6.2 Markov post-processing

If a common Markov kernel post-processes the time coordinate, total variation cannot increase.
If the post-processing admits a common recovery left inverse on the formed family, both
inequalities hold and the action is a total-variation isometry.  This is the base-norm analogue of
the common-recovery KL isometry in ULF-PFM.

### 6.3 Marginal mass conservation

Any legal phase refinement that replaces `mu_I` by a probability disintegration with the same
channel label preserves `(BNF.4)`--`(BNF.7)`.  The source may add latent formation history without
changing coefficient information.

These are mechanisms, not new route objects: relabel, refine, observe, and recover are laws on the
same formed measure.

## 7. Selection consequence and remaining missing law

Let `J(d)` be any source-generated signed formation current taking values in the closed range of
`mathfrak M`.  If a physical source identity proves

\[
 J(d)=0
 \tag{BNF.16}
\]

as an `ell^1`-valued measure, then contractive recovery gives `d=0` unconditionally.  No cofinal
limit, finite-grade lower bound, or adaptive singular vector remains.

This isolates the final selection task sharply:

> Construct the pre-zero physical law whose current lands in the common formed-measure range and
> vanishes there.

Functional equation alone only transports the measure isometrically; it does not prove
`(BNF.16)`.  The theorem supplies a globally proper receiver and exact recovery, not the missing
null current.

## 8. Hostile corrections and scope

1. **The `ell^1` norm was chosen to force the result. — Incomplete objection.**  It is the canonical
   base norm generated by signed combinations of probability laws, and total mass is its common
   recovery.  Nevertheless, source marking of distinct channels is load-bearing.
2. **The theorem remains true after forgetting channel labels. — False.**  Pushing different
   channels into the same scalar measure permits cancellation and destroys isometry.
3. **Hilbert topology was wrong in every organ. — False.**  Hilbert observation is useful and
   proper at every fixed grade.  It fails only as the complete all-grade coefficient topology.
4. **Measure properness implies compactness. — False.**  Unit masses may concentrate at zero or
   escape to infinity while remaining distance two in total variation.
5. **The probability law selects RH. — False.**  Positive unit mass cannot vanish.  Selection needs
   a signed source current and an independent physical null identity.
6. **The construction solves source-adaptive normalization by hiding it in `mu_I`. — False as a
   theorem, open as physics.**  `mu_I` is already generated algebraically by every nonempty subset
   grade.  What remains open is whether the literal Xi/transverse source current lands in this
   formed family.
7. **This is new Banach-space theory. — False.**  Base-norm spaces, vector measures, and total
   variation are classical.  New field content is the exact formation/conservation/observer
   placement forced by the source-response hierarchy.

## 9. Literature boundary

Classical parents include abstract `L^1`/base-norm spaces, vector measures and variation, Markov
contractions, and phase-type probability laws.  ULF-PFM already proves the relative-entropy
common-recovery analogue for split packet formation.  ULF-SRSM-7 supplies the nonproper Hilbert
observer sequence used here.

The new mathematical leverage is the exact commuting mechanism

\[
 \boxed{
 \text{source coefficients}
 \xrightarrow[\text{isometry}]{\text{probability formation}}
 \text{vector measures}
 \xrightarrow[\text{nonproper}]{\text{finite-horizon CDF}}
 \text{Hilbert observer},}
 \tag{BNF.17}
\]

together with one common mass recovery on the middle space.  No searched current source states
this all-grade arithmetic formation theorem.  No priority claim is required.

## 10. Formal status

The Lean corpus was audited read-only.  No Lean file was written and no Lean command or build was
run.  Formalization would require the existing measure/vector-measure infrastructure plus the
already paper-proved subset-phase probability family.

## Log

- 2026-08-14 — pivoted from impossible scalar Hilbert grade weights to source-normalized vector
  probability measures.
- 2026-08-14 — proved exact all-grade total-variation and density isometries with common mass
  recovery.
- 2026-08-14 — identified finite-horizon CDF/Hilbert observation as the exact nonproper quotient
  and isolated the remaining physical signed-current null law.
