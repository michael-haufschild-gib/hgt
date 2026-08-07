# Strict pro-log collar and Arakelov trace kernel

- **ID:** `deninger-strict-pro-log-collar-trace-kernel`
- **Stage:** 2-fully-proven
- **Type:** SOURCE ANALYTIC EXACTNESS THEOREM
- **Labels:** `DAC_STRICT_PRO_LOG_COLLAR_SECTION`,
  `DAC_COMPLETED_ARAKELOV_TRACE_KERNEL`
- **Parent:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Statement:** completing actual pro-log collar forms in the mixed
  boundary graph topology gives a strict right inverse on packet
  mean-zero residues; together with Kummer principal divisors this
  makes the completed finite-plus-real residue image exactly the
  Arakelov trace kernel.

## Local collar section

Use the finite log-toric stage of
`DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`.  For a prime \(p\), a
finite character lattice \(L\), and its finite residue-character set
\[
 Y_{L,p}=\operatorname{Emb}(\overline L_p,\mathbb C^\times),
\]
the Poincaré residue is
\[
 \rho_{L,p}:
 \Omega^1_{\overline Z_{L,p}}(\log D_{L,p})
 \longrightarrow\operatorname{Map}(Y_{L,p},\mathbb C).            \tag{1}
\]

`[PROVED HERE] [DAC_FINITE_LOG_COLLAR_SECTION]`

The map `(1)` is surjective.  More precisely, after choosing the
canonical rational uniformizer \(p\), every
\(f:Y_{L,p}\to\mathbb C\) has a logarithmic lift
\[
 s_{L,p}(f)=\widetilde f\,d\log p,\qquad
 \rho_{L,p}s_{L,p}(f)=f.                                         \tag{2}
\]

### Proof

The finite set \(Y_{L,p}\) is the character group of the finite
abelian reduction group \(\overline L_p\).  Fourier characters form a
basis of \(\operatorname{Map}(Y_{L,p},\mathbb C)\).  Every Fourier
character is evaluation at an element of \(\overline L_p\); choose a
lift of that element to \(\ker\lambda_p\subset L\).  Its torus
character is a holomorphic function on \(D_{L,p}\) restricting to the
given Fourier character.  Linear extension gives
\(\widetilde f\).  Since
\(\operatorname{Res}(d\log p)=1\), `(2)` follows.

Different lifts change \(\widetilde f\) by a function vanishing on
\(Y_{L,p}\), so they change the collar form only by an element of
\(\ker\rho_{L,p}\).  Surjectivity is therefore independent of all
auxiliary choices.

Tensoring `(2)` with smooth functions on
\(\mathbb R/\log p\,\mathbb Z\) and passing through finite quotient
stages shows that every locally constant--smooth test function on the
actual Deninger packet has an actual pro-log collar lift.

## Mixed graph completion

Let \(E_p\) be the packet \(L^1\cap L^2\) completion from
`DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`, and let
\[
 E_{p,0}=\ker(\operatorname{Av}_p:E_p\to\mathbb R)
\]
be its closed Haar-mean-zero subspace.  On the algebraic pro-log
collar forms give the graph seminorm
\[
 \|\omega\|_{\mathrm{coll},p}
 =
 \|\omega-\!s_pP_{p,0}\rho_p\omega\|_{\mathrm{int},p}
 +
 \|P_{p,0}\rho_p\omega\|_{E_p},                                  \tag{3}
\]
where \(P_{p,0}=1-\iota_p\operatorname{Av}_p\) and
\(\|\cdot\|_{\mathrm{int},p}\) is any fixed defining family for the
interior pro-Stein topology.  Different finite-stage collar choices
give equivalent quotient presentations because their difference lies
in the residue kernel.

Let \(\Omega^1_{\log,\mathrm{mix},p}\) be the Hausdorff completion for
`(3)`.

`[PROVED HERE] [DAC_STRICT_PRO_LOG_COLLAR_SECTION]`

Poincaré residue extends to a strict continuous surjection
\[
 P_{p,0}\rho_p:
 \Omega^1_{\log,\mathrm{mix},p}\twoheadrightarrow E_{p,0}          \tag{4}
\]
with a continuous linear right inverse.  With the normalization in
`(3)`, the right inverse has norm one on the quotient component.

### Proof

On the dense test subspace, `(2)` gives
\[
 P_{p,0}\rho_ps_p=\operatorname{id}.
\]
The second summand in `(3)` makes \(s_p\) continuous and makes the
residue quotient norm exactly the \(E_p\)-norm.  Both maps therefore
extend to the completion and retain the identity.  A continuous
surjection with continuous right inverse is strict and has closed
kernel.

This is not an arbitrary enlargement by formal boundary symbols:
the dense subspace consists of actual logarithmic forms on Deninger's
finite-stage character collars.  The completion only adds limits in
the boundary norm already required by the strict all-prime
coefficient.

## All-prime strict section

Give the family of mean-zero collar spaces the weights
\[
 \alpha_p=\log p,\qquad\beta_p=(\log p)^2
\]
and form on \(U_N\) the same mixed restricted sum as for the packet
boundary.  Coordinate deletion defines a flasque collar sheaf
\(\mathscr C_{\mathrm{coll},0}^S\).  The local maps `(4)` assemble to
\[
 \rho_0^S:
 \mathscr C_{\mathrm{coll},0}^S
 \twoheadrightarrow
 \mathscr B_{\mathrm{pkt},0}^S                                  \tag{5}
\]
with a norm-one sheafwise right inverse.

Indeed, the weighted \(L^1\) and \(L^2\) sums of the lifted family are
identical to those of the boundary family.  Restrictions delete the
same finitely many coordinates on both sides.  Thus the direct sum of
the local sections is continuous, commutes with restrictions, and
extends to the strict completion.

## Completed Arakelov trace kernel

Let \(\mathscr U_{\mathrm{Kum}}^S\) be the completed rational Kummer
subsheaf.  By
`DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`, finite valuation is a strict
linear equivalence
\[
 \operatorname{ord}:
 \mathscr U_{\mathrm{Kum}}^S
 \xrightarrow{\sim}
 \mathscr B_{\mathrm{val}}^S.                                    \tag{6}
\]
By `DAC_REAL_KUMMER_ARAKELOV_BOUNDARY`, its real component is
\[
 \partial_\infty(u)
 =
 -W(\operatorname{ord}u),\qquad
 W(d)=\sum_p d_p\log p.                                          \tag{7}
\]

Use the generic degree-one source
\[
 \mathscr G_{\eta,\mathrm{bd}}^1
 =
 \mathscr U_{\mathrm{Kum}}^S
 \widehat\oplus
 \mathscr C_{\mathrm{coll},0}^S                                  \tag{8}
\]
and define
\[
 \partial_{\mathrm{bd}}(u,\omega)
 =
 \left(
   \operatorname{ord}u+\rho_0^S\omega,\,
   -W(\operatorname{ord}u)
 \right)                                                        \tag{9}
\]
in
\[
 \mathscr B_{\mathrm{fin}}^S
 \widehat\oplus\mathscr B_\infty^S.
\]
Define the Arakelov trace by
\[
 \operatorname{tr}_{\mathrm{Ar}}(f,x)
 =
 W(\operatorname{Av}f)+x.                                       \tag{10}
\]

`[PROVED HERE] [DAC_COMPLETED_ARAKELOV_TRACE_KERNEL]`

The sequence
\[
 0\longrightarrow
 \ker\partial_{\mathrm{bd}}
 \longrightarrow
 \mathscr G_{\eta,\mathrm{bd}}^1
 \xrightarrow{\partial_{\mathrm{bd}}}
 \mathscr B_{\mathrm{fin}}^S
   \widehat\oplus\mathscr B_\infty^S
 \xrightarrow{\operatorname{tr}_{\mathrm{Ar}}}
 \mathbb R(-1)
 \longrightarrow0                                               \tag{11}
\]
is strict exact.  In fact \(\ker\partial_{\mathrm{bd}}=0\).

### Proof

Equation `(9)` and the mean-zero property give
\[
 \operatorname{tr}_{\mathrm{Ar}}\partial_{\mathrm{bd}}(u,\omega)
 =
 W(\operatorname{ord}u)-W(\operatorname{ord}u)=0.
\]
Conversely, let \((f,x)\) lie in the trace kernel.  Split it strictly
as
\[
 f=\iota(\operatorname{Av}f)+P_0f=d+c.
\]
Use `(6)` to choose the unique \(u\) with
\(\operatorname{ord}u=d\), and use the right inverse in `(5)` to
choose \(\omega\) with \(\rho_0^S\omega=c\).  The trace-kernel
identity says \(x=-W(d)\), so `(9)` maps \((u,\omega)\) to \((f,x)\).
The two chosen right inverses are continuous, proving strictness and
closed range.  If `(9)` vanishes, its mean-zero projection gives
\(\rho_0^S\omega=0\), hence \(\omega=0\) in the chosen collar
summand; its scalar projection and `(6)` give \(u=0\).
Surjectivity of `(10)` follows from \((0,x)\mapsto x\).

## Consequence for the full generic coefficient

Define the mixed pro-log generic coefficient by completing its actual
logarithmic forms with `(3)` and adjoining the already-present Kummer
subsheaf.  Then `(8)` is a closed source subcomplex of its degree-one
term, and `(9)` is the restriction of the finite-plus-real residue.
Any remaining interior/coarse-coherence summand maps by the same
canonical Poincaré/real boundary.  If its image lies in the trace
kernel—as forced by global residue reciprocity—adding it does not
change exactness at the boundary.  Therefore `(11)` proves
\[
 H^2_{\mathrm{arith}}\cong\mathbb R(-1)                          \tag{12}
\]
for the shifted residue fibre.  Its \(H^1\) is precisely the kernel
contributed by the remaining interior/coarse-coherence complex modulo
generic boundaries.

## Hostile audit

- Surjectivity is not inferred from Kummer generators.  Packet
  mean-zero modes are lifted by actual logarithmic collar forms.
- The graph completion is specified before taking the arithmetic
  fibre and contains a dense actual-form subspace.
- No global sectionwise summability condition is imposed on arbitrary
  Deninger opens; completion is formed after arithmetic direct image
  on the cofinite base.
- The right inverse is a proof device and need not be canonical.
  Residue, its kernel, and the trace-kernel identity are canonical.
- The theorem proves the endpoint, not infinite-dimensionality,
  determinant comparison, positivity, or RH.

## References

- Deligne, logarithmic de Rham residue sequence.
- `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`
- `DAC_DENINGER_PRIME_PACKET_HAAR_RETRACTION`
- `DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`
- `DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`
- `DAC_REAL_KUMMER_ARAKELOV_BOUNDARY`

**Verdict:** `FULLY PROVEN ON PAPER; STRICT ALL-PRIME RESIDUE
TRACE-KERNEL EXACTNESS AND THE ORIENTATION COKERNEL ARE CLOSED FOR THE
MIXED PRO-LOG COLLAR COMPLETION`.

## Lean status

### The trace-kernel exactness landed

`formal/GaloisForLFunctions/RHTower/DeningerArakelovTraceKernel.lean`, alongside the concrete real
boundary already in `DeningerRealKummerArakelovBoundary.lean` (which is the case without the collar
summand).  Axiom audit for all 11 declarations: `propext, Classical.choice, Quot.sound` or less.

- `deningerCollarArakelovBoundary`, `deningerCollarArakelovTrace` — **`(9)`--`(10)`**: the
  finite-plus-real boundary of a Kummer unit and a mean-zero collar form, and the Arakelov trace.
  The finite target is the strict splitting `B_val ⊕ B_pkt,0` of the previous card, so `Av` is the
  first projection and the mean-zero part is the second.
- `deningerCollarArakelovTrace_comp_boundary` — the composite vanishes, which is the card's first
  computation.
- `deningerCollarArakelovBoundary_exact` — **`(11)`**: the image of the boundary is exactly the
  trace kernel.  The proof is the card's: split the finite part, use `(6)` to take the unit with
  the prescribed valuation and the right inverse of `(5)` to take a collar form with the prescribed
  residue, and the trace-kernel identity forces the real component.
- `deningerCollarArakelovTrace_surjective`, `deningerCollarArakelovBoundary_injective` — the trace
  is onto and the boundary is injective, the latter on the summand chosen by the collar section.
- `deningerCollarArakelovH2Equiv` — **`(12)`**: the top cohomology of the shifted residue fibre is
  the real orientation line.
- `deningerCollarSection_isCompl`, `deningerCollarSection_injective` — the algebraic content of
  `(4)`: a surjection with a linear right inverse has complemented kernel, and on the chosen
  summand the residue is injective.  This is what "strict with closed kernel" reduces to once the
  topology is dropped.

### The residue sequence in the constant model

`formal/GaloisForLFunctions/RHTower/DeningerResidueSequence.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

The logarithmic residue sequence `(1)`--`(2)` is now available on the constant forms, which is where
the cohomology of a stage lives: for the projection that forgets the last coordinate and the residue
along it — contract against its direction and restrict to the divisor —

- `deningerExtendForm_injective`, `deningerResidue_comp_extend` — the extension is injective and the
  residue of an extended form vanishes;
- `deningerResidue_exact` — **a form with vanishing residue is extended from the divisor**: on a
  tuple of coordinate vectors avoiding the last coordinate the two forms agree because the
  projection and the inclusion are inverse there, and on a tuple containing it both vanish, the
  form itself because moving that entry to the front turns it into the residue;
- `deningerResidueForm_surjective` — **the residue is onto**, by the Pascal identity for the
  dimensions `deningerAlt_finrank`;
- `deningerResidue_exact_sequence` — the sequence is exact.

So the residue sequence of `(1)`--`(2)` is formalized at the level the card's exactness statements
use it; what is still missing is only its sheaf-theoretic origin, the logarithmic de Rham complex on
the log-toric chart.

### What cannot be stated in Lean, and why

The completions are the obstruction, as for the sibling restricted-sum card: the graph seminorm
`(3)`, the Hausdorff completion `Ω¹_{log,mix,p}`, and the mixed `L¹`/`L²` packet spaces need a
theory of complete locally convex spaces that mathlib does not have; and `(1)`--`(2)`, the
logarithmic residue sequence on a log-toric chart, needs coherent sheaves and logarithmic de Rham
complexes for its sheaf-theoretic form — its content on constant forms is now proved, see below.  The Fourier-basis argument of `(2)` is now available: see
`DeningerFiniteCharacterBasis.lean` below.  The card therefore
stays at stage 2 with its exactness theorem `(11)`--`(12)` formalized and its analytic scaffolding
recorded as unavailable.

### The Fourier step of `(2)`

`formal/GaloisForLFunctions/RHTower/DeningerFiniteCharacterBasis.lean` (8 declarations, axiom audit
`propext, Classical.choice, Quot.sound`) supplies the missing infrastructure for the surjectivity
argument of `(1)`--`(2)`:

- `deningerCharacter_linearIndependent` — distinct characters of a finite abelian group are
  linearly independent as complex functions, by Dedekind's theorem on monoid homomorphisms into a
  field.
- `deningerCharacter_card`, `deningerCharacterGroup_finite` — a finite abelian group has exactly as
  many complex characters as elements, so the independent family has the dimension of the whole
  function space.
- `deningerCharacter_span` — hence **the characters span**: every complex function on the group is
  a linear combination of characters.
- `deningerEvaluation_span` — dually, since a finite abelian group is its own double dual through
  evaluation, **the evaluations at group elements span the functions on the character group**.
  That is exactly the card's step "Fourier characters form a basis of `Map(Y_{L,p}, ℂ)`, and every
  Fourier character is evaluation at an element of `L̄_p`", which is what lets an arbitrary
  `f : Y_{L,p} → ℂ` be written in terms of torus characters and lifted to a collar form.

What remains missing for `(1)`--`(2)` is only the geometric side: the logarithmic residue sequence
on a log-toric chart, which needs coherent sheaves and logarithmic de Rham complexes.

### The graph-seminorm completion, landed — 2026-08-06

The claim above that the Hausdorff completion "needs a theory of complete locally convex spaces
that mathlib does not have" was too strong for the space this card actually uses.  The graph
seminorm is a **single** seminorm, so the completion is the completion of a seminormed space, and
that is entirely within reach.

`formal/GaloisForLFunctions/HTGeometry/SeminormCompletion.lean`:

- `seminormedOfSeminorm` — a seminorm makes the space a seminormed group.
- `exists_banach_completion_of_seminorm` — **the Hausdorff completion of a real vector space with
  respect to a seminorm is a Banach space**, together with a linear map from the space whose norm
  is the seminorm and whose image is dense.  The uniform completion of a seminormed group is
  already a *normed* group: it identifies vectors at seminorm distance zero, which is exactly the
  Hausdorff quotient by the null space, so no separate separation quotient is needed.
- `graphSeminorm`, `graphSeminorm_apply` — the graph seminorm `v ↦ ‖f v‖ + ‖g v‖` of a pair of
  linear maps into seminormed spaces.
- `exists_banach_completion_graphSeminorm` — **the graph completion is a Banach space**: a space of
  forms measured simultaneously by two linear images has a Banach completion recording both, with
  dense image.  This is `Ω¹_{log,mix,p}` of `(3)`.

Axiom audit: all three within `propext, Classical.choice, Quot.sound`.

Together with `DeningerMixedPrimeBanach.lean`, which realizes the mixed weighted `L¹`/`L²` packet
space as a closed subspace of `lp E 1 × lp E 2` and proves it complete, the completion half of the
card's analytic scaffolding is now formalized.  What remains genuinely absent is the geometric
side: the logarithmic residue sequence `(1)`--`(2)` in its sheaf-theoretic form needs coherent
sheaves and the logarithmic de Rham complex of a log-toric chart, neither of which exists in
mathlib.  The card stays at stage 2 on that account alone.

### The geometric obstruction, restated — 2026-08-07

The record above says the sheaf-theoretic form of `(1)`--`(2)` "needs coherent sheaves and
logarithmic de Rham complexes".  Coherent-sheaf cohomology is no longer missing: the corpus builds
sheaf cohomology as `Ext` out of the free abelian sheaf on an open set, proves **Cartan's theorem
B** on `ℂ^n` and `(ℂ^×)^n` and for free analytic sheaves of finite rank, and proves the acyclicity
and filtered passage of a cell filtration.  The single remaining geometric object is the logarithmic
de Rham complex with its Poincaré residue, as a morphism of sheaves; it has its own card,
`docs/drafts/pipeline/1-in-progress/log-de-rham-residue-sheaf.md`.
