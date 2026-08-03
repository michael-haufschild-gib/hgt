# Spectral boundary migration and Shilov-exact local envelope descent

## Metadata

- Status: 1-in-progress
- Route: operator-system boundary theory
- Exact claim label: [BOLD CONJECTURE] [SPECTRAL_SHILOV_EXACTNESS]
- Novelty status: [PLAUSIBLY NOVEL — EXTERNAL AUDIT INCOMPLETE]
- Paper-proof status: open
- Lean status: prohibited until Stage 2
- Open core: prove spectral criterion for escape defect and inverse-limit comparison theorem without silently assuming Shilov ideals commute with quotient maps.

## Frozen exact claim

Let $q:S\to T$ be a complete order quotient between separable unital operator systems. Let

\[
  \alpha:C_u^*(S)\twoheadrightarrow C_u^*(T)
\]

be canonical surjective unital $*$-homomorphism between universal $C^*$-covers, and let $J_S\triangleleft C_u^*(S)$ and $J_T\triangleleft C_u^*(T)$ be Shilov ideals. Put

\[
 I_q:=\alpha(J_S)\cap J_T,
 \qquad
 \mathfrak E(q):=\alpha(J_S)/I_q,
 \qquad
 \mathfrak D(q):=J_T/I_q.
\]

Proposed theorem has three parts.

1. **Spectral boundary-migration criterion.** Following are equivalent:
   - $\mathfrak E(q)=0$, equivalently $\alpha(J_S)\subseteq J_T$;
   - $q$ extends to a surjective $*$-homomorphism
     $C_e^*(S)\twoheadrightarrow C_e^*(T)$;
   - every boundary representation of $T$, pulled back along $\alpha$, factors through $C_e^*(S)$;
   - under nc-state-space duality, every nc extreme boundary point of quotient state space lies in spectral closure of nc extreme boundary of source state space.

2. **Shilov-matricial lifting criterion.** Assuming equivalent conditions in part 1, following are equivalent:
   - $\mathfrak D(q)=0$, equivalently $\alpha(J_S)=J_T$;
   - $\alpha|_{J_S}:J_S\twoheadrightarrow J_T$ is a surjective $*$-homomorphism;
   - every positive element of every matrix algebra $M_r(J_T)$ has a positive lift in $M_r(J_S)$, with usual quotient-norm control;
   - target Shilov ideal contains no boundary direction invisible to source Shilov lifts.

3. **Local $C^*$-envelope exactness.** Let
   $(S_n\subseteq A_n,\alpha_n)_{n\geq 1}$ be a countable inverse sequence of separable unital operator systems in generated $C^*$-covers, with each
   $\alpha_n:A_{n+1}\twoheadrightarrow A_n$ surjective and
   $\alpha_n(S_{n+1})=S_n$. Assume each induced operator-system map is a complete order quotient and both defects vanish at every link. If
   $S=\varprojlim S_n\subseteq A=\varprojlim A_n$, then local Shilov quotient satisfies canonical local $*$-isomorphism
   \[
     C_{e,\mathrm{loc}}^*(S)
       \cong
     \varprojlim_n C_e^*(S_n).
   \]
   Moreover, direct sum of pulled-back stage boundary representations is faithful on this local envelope.

Claim is frozen at this strength. A proof may not replace spectral closure by ordinary closure, replace complete-order quotients by operator-space quotients, or assume without proof that $\alpha(J_S)=J_T$.

## Why this is right hard problem

Complete-order quotients already provide $\varepsilon$-positive lifts at every matrix level. That information controls operator-system quotient but does not control which representations survive in $C^*$-envelope. Local Shilov theory likewise proves only

\[
  \overline{\pi_n(J_{\mathrm{loc}})}\subseteq J_n,
\]

not equality. Proposed defect pair separates two logically different failures hidden by a single word such as “compatibility”:

- $\mathfrak E(q)$: source Shilov elements become visible in target envelope;
- $\mathfrak D(q)$: target Shilov elements have no source Shilov lift.

Inverse-limit theorem asserts these are complete obstructions in countable local setting.

## Pre-freeze killed strengthening

[FALSE] A split complete order quotient with a ucp section always extends to a quotient of $C^*$-envelopes.

Take $K=[-1,1]^2$, $L=\{0\}\times[-1,1]$, $S=A(K)$, and $T=A(L)$. Restriction $q:S\to T$ is a split complete order quotient; ucp section extends an affine function of $y$ constantly in $x$. Nevertheless,

\[
  C_e^*(S)=C(\operatorname{ext}K)=C(\{(\pm1,\pm1)\}),
  \qquad
  C_e^*(T)=C(\operatorname{ext}L)=C(\{(0,\pm1)\}).
\]

Any extending $*$-homomorphism would, by Gelfand duality, send each endpoint of $L$ to a vertex of $K$ while agreeing with evaluation of every affine function. Affine functions separate these points, forcing $(0,\pm1)$ to be vertices of $K$, contradiction. Thus split positivity, exact linear lifting, and all-level complete-order lifting do not prevent boundary migration.

### Positive survivor from failure

At scalar commutative level, restriction $A(K)\to A(L)$ can descend to Shilov envelopes only when every extreme point of $L$ lies in source Shilov boundary (or, without closedness, in appropriate spectral/Shilov closure). Boundary preservation, not existence of a positive section, is missing invariant.

## Internal prior-art audit

- formal/GaloisForLFunctions/HTGeometry/FaithfulSplitKadison.lean proves exact Kadison-defect annihilation from a faithful positive split map under explicit Schwarz hypotheses. It does not construct operator-system quotients or $C^*$-envelopes.
- docs/drafts/pipeline/1-in-progress/source-localization-modular-defect-conservation-law.md already names [XI_COFINAL_MATRICIAL_SOURCE_SATURATION], but does not construct its local operator system or prove Shilov base change.
- Same prior route already kills factorially expansive recovery as a Schwarz-positive map. Present route does not retry that false recovery arrow.
- Existing finite-clock Kadison modules are bridge infrastructure only; they do not address boundary migration.

## External state of art

- Kavruk--Paulsen--Todorov--Tomforde construct quotient operator systems by Archimedeanization and prove universal property. Operator-system quotient matrix norms can differ from operator-space quotient norms.
- Han characterizes complete order quotient maps by $\varepsilon$-positive matricial lifting and, for complete operator systems, by dual complete-order embeddings.
- Kennedy--Kim--Manor identify operator-system quotients with nc convex subsets and realize minimal $C^*$-covers through nc extreme boundaries. Their spectral-closure criterion detects when an irreducible point representation factors through minimal cover.
- Klep--Štrekelj prove matrix extreme points of matrix multifaces remain matrix extreme in ambient matrix convex set. This is weaker than spectral boundary condition needed for $C^*$-envelope descent.
- Joiţa constructs local Shilov ideal as intersection of local boundary-representation kernels. Her proof yields only coordinate inclusion into stage Shilov ideals.
- Joiţa--Şimon characterize Fréchet local Shilov ideal by $\Gamma$-boundary representations. They do not give a complete-quotient, ideal-lifting, or inverse-limit $C^*$-envelope exactness theorem.
- Koot proves minimal tensor products commute with $C^*$-envelopes; this is tensorial, not quotient or inverse-limit functoriality.

## Hostile falsity audit

1. **Chosen cover dependence.** Parts 1--2 use universal $C^*$-covers. Any arbitrary-cover version must transport defects and prove invariance.
2. **Boundary versus spectral boundary.** Ordinary inclusion of boundary representations is too strong in non-type-I settings. Factorization is governed by spectral closure.
3. **Operator-space confusion.** A complete quotient in operator-space norm need not identify operator-system quotient unless required hypotheses are checked.
4. **False split recovery.** A ucp section alone cannot imply envelope descent; square-to-segment example forbids it.
5. **Local coordinate gap.** Equality $\overline{\pi_n(J_{\mathrm{loc}})}=J_n$ is not available from current local Shilov theorems.
6. **Inverse-limit surjectivity.** Surjectivity of $A_{n+1}\to A_n$ does not by itself give coherent Shilov lifts. Vanishing deficit must supply correction step.
7. **Faithfulness overclaim.** A direct sum of target boundary representations is faithful only after quotienting by target Shilov ideal. Local statement must compute its kernel exactly.
8. **Novelty risk.** Parts of proof are short ideal/factorization arguments once formulated. Publication significance depends on proving spectral identification, independence and realizability of two defects, and a genuinely nontrivial local exactness theorem—not on repackaging kernel inclusion.

## Proof obligations

- [ ] Verify canonical universal-cover map for every complete order quotient and its exact kernel.
- [ ] Prove part 1 in both ideal and nc spectral language.
- [ ] Prove part 2 at every matrix level, including quotient-norm control.
- [ ] Prove inverse-limit comparison by an explicit coherent-lift argument.
- [ ] Compute kernel of local boundary direct sum and prove faithfulness.
- [ ] Construct finite-dimensional examples with nonzero escape defect.
- [ ] Determine whether deficit can be nonzero when escape vanishes; either construct an example or prove rigidity.
- [ ] Audit citation ancestry and post-2021 descendancy for exact defect pair and local comparison theorem.
- [ ] Run hostile significance review before Stage 2.

## Falsifier

Route fails at current strength if any primary source already proves exact defect-pair classification and local inverse-limit comparison, or if deficit is forced to vanish whenever escape vanishes and resulting theorem collapses to a routine restatement with no new local consequence.

## Next attack

Resolve hardest structural branch first:

\[
  \alpha(J_S)\subseteq J_T
  \quad\stackrel{?}{\Longrightarrow}\quad
  \alpha(J_S)=J_T
\]

for canonical universal-cover maps induced by split complete order quotients. A counterexample establishes independence of defects; a proof establishes a rigidity theorem stronger than frozen claim and forces conjecture revision through pipeline.
