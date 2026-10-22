# HB nonseparated tests in the original joint energy domain

- **Stage:** 3-formalized.
- **Type:** THEOREM (Lean).
- **RH status:** open. This extends the original response's weak equation; it
  does not yet transfer that equation through the conformal chart.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

The [original-wave reduction](hb-joint-original-wave-conformal-reduction.md)
requires a weak equation against joint coordinate tests. The original completed
domain was defined from separated radial/angular tests. The theorem here admits
smooth compact radial families with values in the actual angular energy domain,
with convergence of their values and derivatives. No density premise or new
domain is supplied.

## Exact statement

Let H be the corpus's actual completed angular differential graph, with slots
`(g0,g1,g2)` for its value and two angular derivatives. Let h be a smooth map
`R -> H` with compact support strictly inside `t<0`. Set `a(t)=sech(t)`.
Using the canonical Bochner/product L² isometry, form the four joint slots

`T(h) = (h0, (h')0, a*h1, a*h2)`.

Then `T(h)` belongs to the **existing** completed joint differential domain.
Here `h'` is the actual derivative in H, and the angular components are the
components of H's completed original graph. Membership is proved, not included
in the definition of h.

For every `Re(w)>0`, original forcing F, and the actual previously constructed
response `u=jointWaveResponse w hw F`, the resulting weak equation is

`< (h')0,u1 > + < a*h1,u2 > + < a*h2,u3 >`
`+ w² < h0,Ju > = < h0,F >`.

Also, every u in the completed joint domain satisfies

`< h0,u1 > + < (h')0,Ju > = 0`.

Thus the radial gradient retains its weak-derivative identity against this
nonseparated family class. Inner products and L² spaces use the original
radial measure and original angular measure throughout.

## Dependency-closed proof

Choose a Hilbert basis `(bi)` of H. For finite index sets S, let
`P_S z = sum_i_in_S <bi,z> bi`. Orthogonality proves that P_S is a contraction;
the basis expansion proves pointwise convergence to the identity. Uniform
equicontinuity and compactness upgrade this to uniform convergence on compact
subsets of H.

For continuous compact families, their ranges are compact. Consequently P_S
converges uniformly on the ranges of h, h', and a*h. All three approximating
families vanish off a common compact set in the radial variable. An explicit
L² bound by the finite-measure indicator of this set upgrades each uniform
convergence to L² convergence. The coefficient functions `<bi,h(t)>` are actual
smooth compact radial core functions, with actual derivatives `<bi,h'(t)>`.
Their weighted coefficients are exactly those of a*h.

The identification used here is constructed explicitly: scalar L² tensors with
H map to the actual Bochner functions `t -> f(t) g`. Their inner products
factor, and vector-valued indicator functions prove dense range by L²
induction. Completion therefore gives an onto linear isometry. Composing with
the existing scalar product-measure tensor isometry supplies the canonical
Bochner/product L² identification, with the exact original separated-product
formula on pure tensors.

For a fixed radial core function f, the map
`g -> (f*g0,f'*g0,a*f*g1,a*f*g2)` is continuous on angular graph space. The
preimage of the closed original joint domain is closed and contains the
original angular core, so it contains the entire angular energy domain.
Every finite P_S packet is therefore an exact finite sum of admitted original
tests. The packet map into four joint slots is continuous. Passing to the
three-component L² limit proves `T(h)` belongs to the original closed domain.
Applying the already proved original variational identity gives the stated
equation for the actual constructed response.

For radial integration by parts, totality of the original angular core and
adjoint identities first extend the separated radial Green identity to every
angular L² vector. The finite packets obey that identity. Its kernel is closed,
so the same packet convergence yields the asserted nonseparated identity.

No angular eigenbasis, spectral decomposition of the original operator,
regularity assumption on its response, or chosen pointwise derivative of that
response is used. The Hilbert basis is used only to approximate test families.

## Lean surface

Generic namespace: `GaloisForLFunctions.HTGeometry`.

| Module suffix | Public theorems | Content |
|---|---:|---|
| HilbertFiniteProjectionCompact | 5 | Contraction and compact uniform convergence |
| HilbertCompactJetApproximation | 7 | Actual derivatives and compact coefficient tests |
| BochnerL2HilbertTensor | 7 | Actual Bochner tensor isometry and dense range |
| CompactUniformL2Convergence | 1 | Uniform convergence with finite support implies L² convergence |
| BochnerL2ProductIsometry | 1 | Canonical product-measure L² identification |
| HilbertFiniteProjectionL2 | 3 | Exact finite tensor sums and L² convergence |

Route namespace: `RHTower.D4BMJointWave`. Canonical prefix:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJoint`.

| Module suffix | Public theorems | Content |
|---|---:|---|
| AngularEnergyTests | 5 | Original-domain admission for completed angular legs |
| RadialFamilyData | 10 | Actual family values, derivatives, weights and coefficient identities |
| RadialFamilyLift | 3 | Continuous assembly into the original joint graph space |
| RadialFamilyAdmission | 4 | Finite packet convergence, original-domain admission, weak equation |
| RadialFamilyGreen | 3 | Extended radial Green identities and actual response equation |

Total: eleven leaves, forty-nine public theorems. Key endpoints are
`RadialEnergyFamily.graph_mem`, `jointWaveResponse_radialEnergyFamily`, and
`radialGreen_radialEnergyFamily`.

## Audit

All development modules passed foreground scratch `lake env lean` checks.
Each of the eleven exact canonical `lake build <module>` audits passed without
warnings, compiling only that leaf plus bookkeeping (two jobs). Eleven source
pairs and twenty-two installed olean/ilean pairs match the audited bytes. Each
leaf is wired once into its area umbrella; no dependency or umbrella builds
were run.

One scratch axiom audit of only the forty-nine new public theorems found only
`propext`, `Classical.choice`, and `Quot.sound`. Source indexing, scoped
whitespace checks, and `lint --check-generated` passed. Lint reported 141
existing large-file warnings and no other warnings. New Lean sources total
820 lines.

All owned Lean/Lake execution handles are terminal; process inspection found
no owned Lean/Lake process. The owned scratch and isolated audit directories
were removed after source and artifact verification.

## Remaining hard obligation

An arbitrary smooth compact **coordinate** test has not yet been identified
with a `RadialEnergyFamily`. This requires proving smoothness of its actual
L²-valued angular value and derivative slices in the angular graph norm. The
Bochner/product isometry also still needs the corresponding representative
identification for these arbitrary slices; the pure-tensor formula alone is
not that theorem.

Next transfer actual measures, weak tests, and completed energy derivatives
through the verified conformal chart and weight. Establish the Euclidean
distribution equation with the original forcing and localization derivatives,
then apply the proved Sobolev gain. Modular patching, radial boundaries,
time-causal inversion, constrained Einstein reconstruction, the left-QNM
pairing, and independent Hawking-clock extinction remain open.

The generic Hilbert and L² arguments supply infrastructure for this specific
domain-admission result; no external novelty claim is made. No numerical
experiment is indicated, and no numerical computation or certificate was used.
No new route-independent RH law follows, so universal-law STATUS is unchanged
by this work. The frontier map is unchanged by this work.
