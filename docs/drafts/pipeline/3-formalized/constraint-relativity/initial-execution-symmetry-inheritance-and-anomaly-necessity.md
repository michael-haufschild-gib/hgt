# Initial-execution symmetry inheritance and anomaly necessity

- **ID:** `initial-execution-symmetry-inheritance-and-anomaly-necessity`
- **Stage:** 3-formalized
- **Type:** THEOREM / META-NO-GO / POSITIVE SURVIVOR (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [META-NO-GO]`
  `[NEW RH-ROUTE LEVERAGE] [NO RH CLAIM] [FORMALIZED IN LEAN]`
- **Role:** proves source-selected initiality cannot by itself break exact source symmetry; isolates
  source symmetry anomaly or nonunique phase selection as mandatory producer.
- **Novelty:** categorical theorem is elementary. New leverage is exact use against autogenic
  promotion and literal radial-gauge symmetry.

## Theorem 1: initial object inherits every categorical symmetry

Let group `G` act strictly on category `E` by autoequivalences `F_g`, with

\[
 F_1=\operatorname{id},
 \qquad
 F_gF_h=F_{gh}.
 \tag{1}
\]

If `I` is initial object of `E`, then it carries unique coherent `G`-equivariant structure:

\[
 \alpha_g:I\xrightarrow{\sim}F_gI
 \tag{2}
\]

such that

\[
 \alpha_1=\operatorname{id}_I,
 \qquad
 \alpha_{gh}=F_g(\alpha_h)\circ\alpha_g.
 \tag{3}
\]

### Proof

Autoequivalence sends initial object to initial object, so each `F_g I` is initial. There is unique
arrow `alpha_g:I->F_gI`. Likewise unique arrow `beta_g:F_gI->I`. Composites `beta_g alpha_g`
and `alpha_g beta_g` are endomorphisms of initial objects. Every initial object has exactly one
endomorphism, identity, so `alpha_g` is isomorphism.

For identity, both `alpha_1` and `id_I` are arrows `I->I`, hence equal. Both
`alpha_(gh)` and `F_g(alpha_h) alpha_g` are arrows from initial `I` to `F_(gh)I`; uniqueness gives
coherence `(3)`. QED.

Same conclusion holds for weak group actions on infinity-category: space of initial objects and
mapping spaces out of initial object are contractible, so coherence is canonical up to
contractible choice. Strict one-category form suffices here.

## Theorem 2: equivariant initial execution lands in homotopy-fixed locus

Let `P:E->X` be `G`-equivariant functor to category `X`. If initial execution `I` exists, `P(I)`
carries coherent `G`-equivariant, or homotopy-fixed, structure. Therefore it cannot lie in full
`G`-stable subcategory `Y subset X` containing no such equivariant object. If `X` is discrete
`G`-set, this reduces to ordinary fixed-point obstruction; in particular no free nontrivial orbit
can contain `P(I)`.

### Proof

Apply `P` to `(2)`--`(3)`. Result identifies `P(I)` coherently with every translate `gP(I)`, so it
is equivariant object. If `X` is discrete, every isomorphism is equality, hence `P(I)=gP(I)` for
all `g`. A free nontrivial orbit has no fixed point. QED.

## Corollary 3: symmetry-breaking trilemma

Suppose source data, fixed seed, and legal-execution doctrine are `G`-equivariant. Within this
architecture, proposed canonical source-generated successor has three possibilities:

1. unique/initial successor inherits `G` symmetry;
2. source has anomaly, so `G` fails to act on full execution problem;
3. successors form nontrivial `G`-orbit, and extra phase/selection datum is required.

There is no fourth option where exact symmetric source plus equivariant doctrine uniquely and
canonically produces non-`G`-equivariant event.

This is categorical version of “spontaneous symmetry breaking requires nonunique vacua or
additional selection”; no physics premise enters proof.

## Literal radial-gauge specialization

For current rational-adelic total-grade-one source, group `(R,+)` acts by

\[
 \Gamma_c(a_q)=|q|^ca_q.
 \tag{4}
\]

Existing homogeneous algebra, cyclic/Hochschild operations, endpoint traces, Kummer derivations,
prime valuation coframe, and ordinary source dagger are equivariant (dagger conjugates `c` to
`-c`, extending action to semidirect reflection group).

Let `E_src` be any category of residue-preserving law executions for a seed preserved by radial
action and built functorially only from these data. Then `Gamma_c` acts on `E_src`. If `E_src` has initial execution, Theorem 1 gives it
canonical radial-equivariant structure. It cannot canonically choose cross-grade relation whose
stabilizer is trivial, nor fixed-source-orientation physical dagger class not invariant under
`Gamma_c`.

Therefore initiality alone does not break current source symmetry. Any radial-selecting identity
must use at least one of:

1. **radial source anomaly:** prime--infinity or analytic-dagger operation for which
   `Gamma_c` action fails by explicit cocycle/transgression;
2. **nonunique source phases:** orbit of inequivalent executions plus independently arithmetic
   selection rule;
3. **larger source:** extra framing/polarity datum already not `Gamma_c`-equivariant, constructed
   without Xi divisor.

Adjoining cross-grade relation by hand enacts item 3 but does not construct it. Latest Route-L
Euler--Gamma/Mobius operation already supplies non-diagonal source detector; remaining burden is
independent flatness of explicit source--Poisson lift obstruction, not another abstract anomaly.

## Generator-commutator necessity under domain hypotheses

Assume `Gamma_c=exp(c partial_log)` on common invariant domain, candidate extra differential
`d_new` preserves that domain, and `d_new` is only added datum capable of breaking radial
equivariance. Infinitesimal anomaly is commutator

\[
 \mathcal A=[d_{\mathrm{new}},\partial_{\log}].
 \tag{5}
\]

If `A=0`, exponentiation gives `d_new Gamma_c=Gamma_c d_new`; new differential remains radially
equivariant and Theorem 1 applies. Thus under stated hypotheses, necessary condition for unique
radial-selecting execution is

\[
 \boxed{[d_{\mathrm{new}},\partial_{\log}]\ne0.}
 \tag{6}
\]

Prime valuation refinement requires independent components

\[
 \mathcal A_\ell=[d_{\mathrm{new}},\partial_\ell]
 \tag{7}
\]

whose source pairing lands coefficientwise on physical diagonal defect. Scalar nonzero commutator
is insufficient if it appears only after logarithmic contraction.

Equation `(6)` is necessary, not sufficient. Defining `d_new` by desired defect is circular;
operation must be literal source-native and pre-divisor.

## Positive survivor: corrected field equation

Naive Nomogenic equation `O ~= L[1]` cannot select symmetry-breaking event from equivariant
source. Corrected source-law system must include anomaly object

\[
 \operatorname{Anom}_G(S,\mathbb T)
 =\operatorname{cofib}
 \bigl(G\curvearrowright\operatorname{Exec}(S,\mathbb T)\bigr)
 \tag{8}
\]

or concrete derived replacement, and source equation must couple anomaly to relative law:

\[
 \Theta_{S,\mathbb T}:
 \operatorname{Anom}_G(S,\mathbb T)
 \xrightarrow{\simeq}
 \mathbb L_{\mathbb T^+/\mathbb T}[1].
 \tag{9}
\]

Formula `(8)` is placeholder, not definition accepted as theorem. Concrete commutators `(5)` and
`(7)` are first falsifiable realizations.

## Hostile audit

1. This theorem does not construct anomaly and does not prove RH.
2. Initial-object symmetry inheritance is standard elementary category theory.
3. It blocks central circular move: claiming unique source completion will spontaneously select
   critical line from radially symmetric axioms.
4. Source star breaks strict `Gamma_c` commutation but supplies semidirect reflection equivariance;
   existing Kummer dagger audit shows it exchanges two oriented classes rather than fixes one.
5. Nonunique execution phases may exist; selecting one requires new arithmetic datum and cannot be
   called canonical without proof.

## Lean-return note

Formalized; see `initial-execution-symmetry-inheritance-and-anomaly-necessity-formalized.md`.  The note below was written before that work and is kept for the record: it is no longer a restriction.

> No Lean work authorized. If later requested, generic initial-object theorem and discrete-action
> corollary are small category-theory targets. Arithmetic instantiation should remain paper-level
> until exact execution category is defined.

## Log

- 2026-08-08 — derived after radial-gauge and Nomogenesis initiality were combined.

## Formalized companion

`initial-execution-symmetry-inheritance-and-anomaly-necessity-formalized.md` (same directory).
