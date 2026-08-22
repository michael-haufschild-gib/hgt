# Complete asymptotic invisibility via flat HT perturbations

- **ID:** asymptotic-flat-ht-invisibility
- **Stage:** 3-formalized/not_new_scientific_knowledge (third audit 2026-07-12)
- **Type:** CANDIDATE THEOREM
- **Source:** `ht-c09-asymptotic-scale-nontermination`; `finite-jet-nonidentifiability-ht`; Hölder; Stirling
- **Statement:** Arbitrary finite jets and any DA inverse-power Poincare asymptotic profile can be realized
  simultaneously by both a DA function and an HT function.

## Goal

Strengthen C09 from "no finite asymptotic prefix certifies HT" to a sharper obstruction:

> Even a complete classical asymptotic expansion, combined with arbitrary finite jet observations, does not
> distinguish DA from HT.

This is an anti-theatre theorem. Computations that fit many asymptotic terms, residual ranks, or local jets
cannot count as HT evidence unless they use a structural theorem outside the finite/asymptotic observation
functor.

## Multiplier lemma

Let `B` be a nonzero meromorphic function differentially algebraic over `C(z)`. Then

`B/Gamma`

is hypertranscendental over `C(z)`.

Indeed, if `B/Gamma` were DA, then `Gamma=B/(B/Gamma)` would be DA by field closure, contradicting Hölder.

Thus any nonzero DA multiplier `B` can transfer its ordinary analytic invisibility properties to an HT
perturbation. If `B` vanishes to prescribed finite orders, `B/Gamma` is invisible to those jets. If `B/Gamma`
is flat in an asymptotic scale, it is invisible to that scale. The theorem below chooses

`B(z)=lambda A(z)`

for finite jets and uses Stirling to get inverse-power flatness along `+infinity`; the DA correction
`e^(-z)Q` realizes arbitrary finite jet targets without changing the same asymptotic profile.

## Theorem `[PROVED HERE]`

Let `G` be a meromorphic function differentially algebraic over `C(z)`. Assume:

1. `G` is holomorphic at distinct points `a_1,...,a_N`;
2. `G` is holomorphic on the positive real ray for all sufficiently large `x`;
3. along `x -> +infinity`, `G(x)` admits a Poincare asymptotic expansion in inverse powers,

   `G(x) ~ sum_{n>=0} b_n x^{-n}`,

   meaning that for every `M`,

   `G(x)-sum_{n<M} b_n x^{-n} = o(x^{-M})`.

Fix arbitrary target jet values `c_{i,j}` for `1 <= i <= N`, `0 <= j <= m_i`.

Then there exist:

1. a meromorphic function `D` differentially algebraic over `C(z)`;
2. a punctured affine line of meromorphic functions `F_lambda`, `lambda in C^*`;

such that:

1. `D^(j)(a_i)=F_lambda^(j)(a_i)=c_{i,j}` for every `i,j`;
2. every `F_lambda` is hypertranscendental over `C(z)`;
3. `D` and every `F_lambda` have the same complete inverse-power Poincare asymptotic expansion as `G` along
   `+infinity`:

   `D(x) ~ F_lambda(x) ~ sum_{n>=0} b_n x^{-n}`.

The special case `G=0` says: every finite holomorphic jet table is realized by both a DA entire function and
an HT entire function whose complete inverse-power asymptotic expansion along `+infinity` is identically
zero.

## Construction

Choose a polynomial `Q` so that `E(z)=e^(-z)Q(z)` has the finite jets

`E^(j)(a_i)=c_{i,j}-G^(j)(a_i)`.

This is possible because multiplication by `e^(-z)` is an invertible linear map on each finite jet space, and
Hermite interpolation realizes the corresponding finite jets of `Q`.

Put

`A(z)=prod_i (z-a_i)^(m_i+1)`.

For every `lambda in C^*`, define

`D(z)=G(z)+E(z)`,

`F_lambda(z)=D(z)+lambda A(z)/Gamma(z)`.

## Proof

The jet agreement for `D` follows by construction of `Q`. The additional term `A/Gamma` has zeros of order
at least `m_i+1` at each `a_i`, so `F_lambda` has the same prescribed finite jets.

The function `E=e^(-z)Q` is D-finite, hence DA, and `D=G+E` is DA by closure of DA elements under field
operations.

For hypertranscendence, suppose `F_lambda` were differentially algebraic over `C(z)`. Since `D` is
differentially algebraic and DA elements form a field, the difference

`F_lambda-D=lambda A/Gamma`

would be differentially algebraic. Because `lambda A in C(z)^*`, this would make `1/Gamma` differentially
algebraic over `C(z)`, and hence `Gamma` differentially algebraic over `C(z)`, contradicting Hölder's theorem.
Thus `F_lambda` is HT.

It remains to check flatness. Since `Q` is a polynomial, `e^(-x)Q(x)=o(x^-M)` for every `M`. Stirling's formula
on the positive real axis gives

`Gamma(x) ~ sqrt(2*pi) x^(x-1/2) e^(-x)`.

For every fixed `M`, and for `d=deg A`,

`x^M A(x)/Gamma(x) -> 0`

because

`log |x^M A(x)/Gamma(x)| = (M+d) log x - (x-1/2) log x + x + O(1) -> -infinity`.

Therefore `A(x)/Gamma(x)=o(x^{-M})` for every `M`. Both added terms, `E` and `lambda A/Gamma`, are flat to all
orders in the inverse-power Poincare scale. Hence every truncation remainder for `G` remains a valid
truncation remainder for `D` and `F_lambda`. The complete asymptotic expansion is identical. ∎

## Lean formalization

Status: **complete and unconditional**, including the multiplier lemma, both flatness statements and
the full realization theorem.

`formal/GaloisForLFunctions/HTGeometry/ReciprocalGammaHypertranscendental.lean`

- **`hypertranscendental_invGamma`** — `1/Γ` satisfies no algebraic differential equation.  This is
  the form of Hölder's theorem the card actually needs, and it is *not* a restatement of
  `hypertranscendental_gamma`: a relation for `1/Γ` inverts to one for `Γ` only off the poles, so
  the proof inverts on the right half plane, propagates across the connected pole complement, and
  then multiplies by the `Γ`-slot variable — which vanishes at every pole — to obtain a relation
  valid on all of `ℂ`.  Hölder's theorem then applies.
- **`not_differentiallyAlgebraicOn_invGamma`** — the same on any nonempty open set; `1/Γ` is entire,
  so a local relation propagates to the plane.
- **`differentiallyAlgebraicOn_add`**, **`differentiallyAlgebraicOn_sub`** — additive closure of
  differential algebraicity on an arbitrary domain.  The corpus had this only for entire functions;
  the general jet bridge `differentialAlgebraicOver_analyticMeroElement_iff` was already domain
  parametric, so the meromorphic case of this card needs no entirety hypothesis.

`formal/GaloisForLFunctions/HTGeometry/AsymptoticFlatHypertranscendentalInvisibility.lean`

- `one_le_gamma_of_two_le`, `gamma_ge_descProd`, `gamma_ge_pow`, **`tendsto_pow_div_gamma`** —
  Stirling is not needed: `Γ(x) ≥ ∏_{j≤k}(x-j-1) ≥ (x-k-1)^{k+1}` from the functional equation and
  `Γ ≥ 1` on `[2,∞)` already gives `x^M/Γ(x) → 0` for every `M`.
- `jetTaylorPolynomial`, `eval_iterate_derivative_jetTaylorPolynomial`,
  **`exists_polynomial_iteratedDeriv_eval_eq`** — numeric Hermite interpolation: one polynomial
  realizes arbitrary prescribed iterated derivative values at finitely many distinct points.
- **`iteratedDeriv_mul_jet_congr`** — jet agreement to order `m` is preserved by multiplication by a
  smooth factor.  This is what makes the `e^{-z}` normalization free: `Q` is interpolated against
  the jets of `e^{z}T`, and `e^{-z}Q` then has the jets of `T`.
- `jetModulus`, `jetModulus_ne_zero`, **`iteratedDeriv_jetModulus_eq_zero`** — the modulus
  `A = ∏ (z - a_i)^{m_i+1}` and the vanishing of its jets, so the added term is invisible to the
  prescribed jets.
- `FlatInversePowers`, **`flat_exp_neg_mul_polynomial`**, **`flat_polynomial_mul_invGamma`** — both
  added terms are flat to all orders in the inverse-power scale.
- `PoincareInversePowers`, **`PoincareInversePowers.add_flat`** — a complete inverse-power Poincaré
  expansion is unchanged by adding a flat function.
- **`not_differentiallyAlgebraicOn_mul_invGamma`** — **the multiplier lemma**: a nonvanishing
  analytic differentially algebraic `B` makes `B/Γ` hypertranscendental.
- **`exists_differentiallyAlgebraic_and_hypertranscendental_realization`** — **the theorem**.  For a
  differentially algebraic `G` analytic on a domain `U`, with any inverse-power Poincaré expansion
  `b` and any finite jet table `c` at distinct nodes of `U`, it produces `D` and the modulus `A`
  with: `D` differentially algebraic on `U`, `D` realizing the jet table, `D` carrying the same
  expansion; and for every `λ ≠ 0` the function `D + λ A/Γ` realizes the same jet table, carries the
  same expansion, and satisfies **no** algebraic differential equation on `U`.  The special case
  `G = 0` is the card's statement that every finite jet table is realized by both a differentially
  algebraic and a hypertranscendental function with identically vanishing asymptotic expansion.

Every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Consequences

1. **Complete asymptotic data are not enough.** HT can be invisible not only to finite asymptotic prefixes but
   to an entire Poincare expansion.
2. **Local and asymptotic probes fail simultaneously.** The same perturbation preserves arbitrary finite jets
   and the complete inverse-power asymptotic expansion.
3. **Zero expansion is maximally nonidentifying.** Even the complete zero Poincare expansion along `+infinity`
   contains both arbitrary finite DA jet profiles and arbitrary finite HT jet profiles.
4. **Flat tails are a real obstruction.** A tail can be differentially transcendental while invisible to every
   algebraic order of the chosen asymptotic scale.
5. **No computation-only promotion.** Any numerical or symbolic experiment based on finite jets plus
   asymptotic-term fitting remains non-certifying unless it proves a structural non-flat obstruction.

## Theatre / promptability audit

The construction is promptable after normal-form stripping:

> Use `e^(-z)Q` to realize finite jets while staying flat at `+infinity`, then add `lambda A/Gamma` to insert
> an HT tail invisible to the same finite jets and inverse-power asymptotic scale.

Therefore the proof is not evidence of non-promptable depth. The card can only be promoted as a structural
gatekeeper: it gives an exact kernel element for the observation channel "finite jets plus complete classical
asymptotics" and proves that this channel cannot certify HT.

## Source boundary

Imports:

- Hölder's theorem: `Gamma` is differentially transcendental over `C(z)`.
- Stirling's formula on the positive real axis.
- Closure of DA elements under field operations.
- Classical fact that adding a flat term preserves a Poincare asymptotic expansion.
- Hermite interpolation for finite jets after the invertible local multiplier `e^(-z)`.

External anchors:

- DLMF §5.11 records Poincare-type asymptotic expansions for `Gamma`, including Stirling's formula.
- Adamus, *On the differential transcendentality of the Morita p-adic gamma function*, arXiv:2109.11448,
  recalls Hölder's theorem as Theorem 1: `Gamma` is differentially transcendental over `C(z)`.

The classical ingredients are not novel. The candidate theorem packages them into an exact DA/HT
nonidentifiability result for the combined finite-jet plus complete-asymptotic observation functor.

Web/source searches for `"flat" "hypertranscendental" perturbation asymptotic expansion`,
`"1/Gamma" flat asymptotic hypertranscendental`, `"differentially transcendental" "same asymptotic
expansion"`, `"hypertranscendental" "same asymptotic expansion"`, `"zero asymptotic expansion"
"hypertranscendental"`, `"same zero asymptotic expansion" "differentially transcendental"`, `"flat"
"1/Gamma" "finite jets"`, and `"Poincare asymptotic expansion" "finite jets" "hypertranscendental"` did not
find this exact statement. Hits were standard asymptotic/Gevrey examples, ordinary flat-function phenomena,
and general HT background.

Local corpus searches for zero/asymptotic invisibility, flat DA/HT tails, and C09 prior work found only the
original C09 conjecture and this card, not the theorem above.

Nearby interpolation literature: Marques, *On the arithmetic nature of hypertranscendental functions at
complex points*, Expo. Math. 29 (2011), 361--370, uses interpolation formulae to construct uncountably many
HT entire functions with prescribed algebraic exceptional sets. This increases source-risk for any broad
"HT can interpolate values" claim. It does not appear to state the complete-asymptotic DA/HT
nonidentifiability theorem or the multiplier-lemma construction above.

Promotion risk: this may still be judged a short corollary of Hermite interpolation, flat DA functions,
Hölder, and Stirling. Its significance, if accepted, is methodological and structural: it proves that complete
classical asymptotic data belong on the same non-certifying side as finite samples and finite jets.

Kill condition: produce a source already stating the exact DA/HT indistinguishability theorem for complete
Poincare asymptotic data, or show that this is too immediate to count as a significant theorem about HT.

## Gates

- [x] 0 -> 1 in-progress: C09 sharpened to an exact theorem with proof.
- [ ] 1 -> 2 fully-proven: team audits proof, source boundary, and significance.
- [ ] 2 -> 3 formalized: formalize as a theorem conditional on Hölder and Stirling/flatness imports.
- [ ] 3 -> 4 publication-ready: package with the finite-jet theorem as the "invisible HT perturbations" note.

## Log

- 2026-06-24 — Created by Haiku after entropy draw selected C09. The theorem upgrades finite asymptotic
  nontermination to complete asymptotic invisibility, using the flat HT tail `1/Gamma`.
- 2026-06-24 — Strengthened from "same jets as a DA `G`" to arbitrary finite jets over any DA asymptotic
  profile by inserting a flat DA correction `e^(-z)Q`.

## 2026-06-24 addendum -- finite logarithmic-resolution quotient collapse

[Turing id=1735 repair / Haiku promptability gate]

Turing proposed replacing the single tail `1/Gamma(z)` by the deeper tails `1/Gamma(z^k)` to make the
invisibility boundary recede. The raw formulation "any finite transseries level" was too vague and too easy to
turn into rhetoric. The precise theorem that survives is the following finite-resolution quotient statement.

### Polynomial-substitution HT lemma

For every integer `k >= 1`, the entire function

`H_k(z)=1/Gamma(z^k)`

is hypertranscendental over `C(z)`.

Proof. If `H_k` were DA over `C(z)`, then `Gamma(z^k)=1/H_k` would be DA. After the algebraic substitution
`z=t^(1/k)`, the germ `Gamma(t)` would be DA over the algebraic extension `C(t^(1/k))` of `C(t)`. Differential
algebraicity descends across algebraic base extensions, so `Gamma(t)` would be DA over `C(t)`, contradicting
Holder. Thus `H_k` is HT. Multiplication by a nonzero rational function or polynomial does not change this
argument: if `B H_k` with `B in C(z)^*` were DA, then `H_k` would be DA.

### Finite gauge quotient theorem `[PROVED HERE]`

Fix distinct finite jet points `a_i`, orders `m_i`, and arbitrary target jet values `c_{i,j}`. Let `G` be
meromorphic and DA over `C(z)`, holomorphic at the jet points and eventually holomorphic on the positive real
ray.

Let `eps_1(x),...,eps_L(x)` be positive gauges on the positive real ray, eventually satisfying
`0 < eps_l(x) <= 1`, such that, for some real `R >= 0`,

`log(1/eps_l(x)) = o(x^R log x)`

for every `l`. Then there exist a DA function `D` and, for every `lambda != 0`, an HT function `F_lambda` such
that:

1. `D^(j)(a_i)=F_lambda^(j)(a_i)=c_{i,j}` for all prescribed jets;
2. `D(x)-G(x)=o(eps_l(x))` for every `l`;
3. `F_lambda(x)-G(x)=o(eps_l(x))` for every `l`.

Equivalently, in the quotient that records the finite jets and only resolves errors down to the finite gauge
list `{eps_l}`, every DA-compatible observation record has both a DA and an HT representative.

Construction. Choose an integer `k > R`. Put

`A(z)=prod_i (z-a_i)^(m_i+1)`.

Choose a polynomial `Q` so that

`E(z)=exp(-z^(k+1)) Q(z)`

has jets `E^(j)(a_i)=c_{i,j}-G^(j)(a_i)`. This is possible because multiplication by
`exp(-z^(k+1))` is invertible on every finite jet space. Set

`D(z)=G(z)+E(z)`,

`F_lambda(z)=D(z)+lambda A(z)/Gamma(z^k)`.

The jet agreement is immediate from the construction of `E` and the vanishing order of `A`. The function `D`
is DA because `exp(-z^(k+1))Q(z)` is D-finite. For `lambda != 0`, `F_lambda` is HT by the polynomial-substitution
HT lemma and the same field-closure argument used in the main theorem.

For the gauge estimates, `E(x)=O(exp(-x^(k+1)) x^q)` for some `q`, hence `E=o(eps_l)` because
`log(1/eps_l)=o(x^R log x)` and `k+1>R`. Stirling gives

`log |A(x)/Gamma(x^k)| = O(log x) - k x^k log x + O(x^k)`,

so `A(x)/Gamma(x^k)=o(eps_l)` because `k>R`. Hence both `D-G` and `F_lambda-G` vanish below every gauge in the
finite list.

### Theatre / source boundary for the addendum

This addendum repairs a vague extension; it does not by itself clear the project goal. The proof is still a
Gamma-tail depth argument, and after stripping it can be prompted as: choose a tail deeper than the observation
scale. The nontrivial value is the exact quotient statement: finite logarithmic-depth observation channels cannot
certify HT, because their fibers over DA-compatible records contain explicit DA and HT representatives.

The theorem deliberately does **not** claim invisibility below arbitrary gauges such as `exp(-exp(x))`, nor a
full transseries quotient without first defining the allowed transseries monomials. Any stronger claim must state
the observation category before it is counted.

Source check so far: local search found no prior card stating the `1/Gamma(z^k)` finite-gauge quotient theorem.
Web searches for `"Gamma(z^k)" differentially transcendental`, `"1/Gamma(z^k)" hypertranscendental`, and
`"hypertranscendental" "same asymptotic expansion"` did not find this exact statement. The ingredients remain
standard: Holder's theorem, algebraic substitution for DA functions, finite jet interpolation, and Stirling.

Promotion grade remains BRIDGE / gatekeeper unless another agent finds a non-promptable delta beyond the quotient
collapse itself.

## 2026-06-24 source-risk update -- perturbation literature

A further source check found a close surrounding literature: Huang--Ng, *Hypertranscendency of Perturbations of
Hypertranscendental Functions* (JMAA 491, 2020; arXiv:2007.10037), building on Bank and Bank--Kaufman. Their
abstract and introduction state that they study when functions of the forms `f e^g`, `f+g`, `f*g`, and `f∘g`
are hypertranscendental, and recall Bank's theorem on adding a small meromorphic perturbation to an HT function.
They also record that `A(K)`, the functions DA over a coefficient field `K`, is a differential field.

Impact on this card:

1. The raw perturbation/composition ingredients are not novel. In particular, `Gamma∘p` for a nonconstant
   polynomial `p` lies in an already-studied type of question, and the field-closure proof for multiplying or
   adding DA terms is elementary.
2. The remaining possible delta is narrower: an exact observation-quotient collapse statement for finite jets,
   complete Poincare data, and finite logarithmic-depth gauges, with explicit DA and HT representatives in the
   same observation fiber.
3. Therefore this card should not be promoted as "new perturbation hypertranscendence." It can only be promoted,
   if at all, as an HGT gatekeeper theorem about which observation channels provably cannot certify HT.

This strengthens the promptability warning rather than weakening it: the construction ingredients are classical
and source-adjacent; only the quotient/fiber framing is project-specific.

## 2026-07-12 Third audit (Fable) — gate 1 → 2 closed

Proof audit PASS. Checked line-by-line: the Hermite/`e^{-z}`-multiplier jet realization (the
multiplier is invertible on each finite jet space), the field-closure/Hölder hypertranscendence
step, the Stirling flatness estimates (including the `Γ(z^k)` variant
`log|A(x)/Γ(x^k)| = O(log x) − k·x^k·log x + O(x^k)` and the gauge comparison against
`log(1/ε) = o(x^R log x)` with `k > R`), and the algebraic-substitution descent for `Γ(z^k)`
(differential algebraicity descends across finite algebraic base extensions). No gaps found.

Grade audit PASS: not new scientific knowledge. The ingredients are classical
(Hölder, Ritt/Kolchin composition, Stirling, Hermite) and the perturbation corpus
(Bank; Huang–Ng 2020) is source-adjacent, exactly as the cards' own audits concluded. The
banked value is the observation-channel gatekeeper: finite jets, complete Poincaré data, and
every finite logarithmic-depth gauge list provably cannot certify hypertranscendence, with
explicit DA/HT representatives in the same observation fiber and the exact `z^{-z^k}` rung
boundary. This is load-bearing methodology for the branch (it blocks computation-only HT
claims) and stays citable as the anti-theatre gate.

Stage moves to 2-fully-proven/not_new_scientific_knowledge. The Lean gate (2 → 3) remains open
and needs a `Hypertranscendental Complex.Gamma` (Hölder) interface; note the tree now has an
unconditional `hypertranscendental_riemannZeta`, so the DA/HT vocabulary is exercised — the
Hölder import is the only missing brick for formalizing these gatekeepers.

## Log

- 2026-08-22 — Formalized unconditionally in Lean; promoted to stage 3.  The new corpus assets are
  the hypertranscendence of `1/Γ`, domain-additive closure of differential algebraicity, numeric
  Hermite interpolation, and the elementary `Γ`-growth bound that replaces Stirling.
