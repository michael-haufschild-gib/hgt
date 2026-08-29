# Finite-jet nonidentifiability of hypertranscendence

- **ID:** finite-jet-nonidentifiability-ht
- **Stage:** 3-formalized (not new scientific knowledge; third audit 2026-07-12; Lean 2026-08-29)
- **Type:** CANDIDATE THEOREM
- **Source:** `ht-c15-finite-sampling-nonidentifiability`; Hölder; Hermite interpolation
- **Statement:** The finite-jet map from entire hypertranscendental functions is surjective; every finite
  holomorphic jet table is realized both by a differentially algebraic function and by a
  hypertranscendental entire function.

## Goal

Make precise the epistemic boundary of hypertranscendence:

> Hypertranscendence is an identity-level infinite negation; finite samples and finite jets cannot certify it
> or refute it.

This is not a genericity theorem and does not rely on computation. It is an explicit two-realization theorem:
the same finite data admit a finite-handle completion and an HT completion.

## Theorem `[PROVED HERE]`

Fix distinct points `a_1,...,a_N in C`, nonnegative integers `m_i`, and arbitrary complex numbers
`c_{i,j}` for `1 <= i <= N`, `0 <= j <= m_i`.

There exist:

1. a polynomial `P(z) in C[z]`;
2. with `A(z)=prod_i (z-a_i)^(m_i+1)`, a one-parameter affine family of entire functions

   `F_lambda(z)=P(z)+lambda A(z)/Gamma(z)`, `lambda in C`,

such that

`P^(j)(a_i) = F_lambda^(j)(a_i) = c_{i,j}`

for every `i,j` and every `lambda`. The member `F_0=P` is differentially algebraic; every member
`F_lambda` with `lambda != 0` is hypertranscendental.

In particular:

- no finite jet data can distinguish DA from HT in the class of entire functions;
- no algebraic relation among finitely many jet values follows from hypertranscendence alone.

## Proof

By Hermite interpolation, choose a polynomial `P` satisfying the prescribed finite jets.

Let

`A(z)=prod_i (z-a_i)^(m_i+1)`.

Let `H(z)=1/Gamma(z)`. This is entire. It is hypertranscendental over `C(z)`: if `H` were differentially
algebraic over `C(z)`, then `Gamma=1/H` would also be differentially algebraic because the differentially
algebraic elements of a differential field extension form a field, contradicting Hölder's theorem for
`Gamma`.

Define

`F_lambda(z)=P(z)+lambda A(z)H(z)`.

Since `A` vanishes to order `m_i+1` at each `a_i`, the functions `P` and `F_lambda` have the same derivatives
up to order `m_i` at `a_i`.

It remains to prove `F_lambda` is hypertranscendental for `lambda != 0`. If `F_lambda` were differentially
algebraic over `C(z)`, then `F_lambda-P` would be differentially algebraic, and since `lambda A in C(z)^*`,
so would

`H=(F_lambda-P)/(lambda A)`.

This contradicts the hypertranscendence of `H`. Therefore `F_lambda` is entire and hypertranscendental while
matching the same finite jet data as the polynomial `P` for every `lambda != 0`. ∎

## Consequences

1. **No finite certificate.** Any finite sample/jet test that labels a function DA or HT can be fooled by an
   explicit pair with identical finite observations.
2. **Function/value decoupling.** Since the prescribed `c_{i,j}` are arbitrary, finite jet values of HT
   functions can satisfy any chosen algebraic dependence pattern or any chosen algebraic independence pattern
   available in `C`. Therefore function-level HT imposes no finite value-level algebraic relation.
3. **Constraint, not flow.** HT cannot be inferred from local finite data; it is a global identity-level
   obstruction.
4. **Anti-theatre rule.** Computations over finite samples can at most propose conjectures about HT. They
   cannot certify HT without a structural theorem.
5. **Fiber geometry.** Every finite jet fiber contains a DA point and a punctured affine complex line of HT
   points. Thus the finite observation map does not merely identify one exceptional pair; it collapses a
   continuum of distinct HT functions onto the same finite DA profile.

### Relation to ordinary finite-jet independence

This does **not** contradict the standard differential-algebraic consequence that, for a fixed HT function
`f`, the functions `f,f',...,f^(n)` are algebraically independent over the chosen differential base. That is
a statement about identities among functions on a domain.

The theorem here is value-level and epistemic: after choosing finitely many points and finitely many
derivative orders, the resulting complex numbers can be forced arbitrarily by an HT function. Function-level
absence of ADEs does not impose finite value-level constraints.

## Strengthening — invisible HT perturbations of DA functions

The same construction proves a stability form.

**Theorem.** Let `G` be a meromorphic function differentially algebraic over `C(z)` and holomorphic on a
neighborhood of the finite jet set above. Let `A(z)=prod_i (z-a_i)^(m_i+1)`, and let `B(z) in C(z)^*` be
holomorphic and nonzero on that neighborhood. Then

`F(z)=G(z)+A(z) B(z)/Gamma(z)`

has the same prescribed finite jets as `G` at all `a_i`, and is hypertranscendental over `C(z)` as a
meromorphic function/germ on its domain.

**Proof.** The jet agreement follows from the vanishing order of `A`. If `F` were differentially algebraic,
then `F-G` would be differentially algebraic because the DA elements form a field. Dividing by the rational
factor `AB` would make `1/Gamma` differentially algebraic, contradiction. ∎

Thus every finite DA observation profile has HT perturbations that are exactly invisible to that observation
profile. Finite data do not merely fail to certify HT; finite DA data have explicit HT liftings.

## Theatre / promptability audit

This proof is not computational evidence. It is a short structural argument. The construction would be
promptable after stripping the problem to:

> Given a known entire HT function `H`, add a rational factor vanishing to prescribed finite orders to a
> Hermite interpolating polynomial.

Therefore no computation or agent vote is counted as discovery here. The candidate survives only as a
recorded theorem because it converts the theatre test into a reusable obstruction: finite samples, finite
jets, and finite residual probes cannot themselves be evidence for HT.

The decisive content is the exact two-realizer statement and its DA-to-HT invisible perturbation form, not the
general observation that finite data can mislead.

## Source boundary

Imports:

- Hermite interpolation for polynomial finite-jet realization.
- Hölder's theorem: `Gamma` is hypertranscendental.
- Closure of differentially algebraic elements under field operations.

The proof is elementary after those imports. Hölder is standard: modern summaries state that `Gamma` is
differentially transcendental over `C(z)`.

External anchor: Adamus, *On the differential transcendentality of the Morita p-adic gamma function*,
arXiv:2109.11448, recalls Hölder's theorem as Theorem 1.

Source checks:

- Web searches for `"finite jet" "hypertranscendental"`, `"finite jets" "differentially transcendental"
  entire`, `"differentially transcendental" "prescribed jets"`, and `"hypertranscendental" "Hermite
  interpolation"` did not find this exact statement. Hits were mostly ordinary jet-determination literature,
  standard differential-transcendence background, and unrelated interpolation uses.
- Local corpus check found the intended conjecture `ht-c15-finite-sampling-nonidentifiability`, but only as a
  backlog conjecture with a Borel-Ritt/free-tail sketch, not this exact `1/Gamma` two-realizer proof.
- Local corpus check also found the C26 finite-compact value-probe no-go: by Mergelyan/Runge and polynomial
  interpolation, DA/D-finite functions can match or approximate many finite observations. That source-kills
  any claim that "finite probes are bad" is new. It does not state the exact finite-jet surjectivity of the
  HT class or the DA-to-HT invisible perturbation theorem above.
- A later source check found Marques, *On the arithmetic nature of hypertranscendental functions at complex
  points*, Expo. Math. 29 (2011), 361--370. Public abstracts state that interpolation formulae give
  uncountably many HT entire functions, with small growth, realizing arbitrary subsets of `Qbar` as exceptional
  algebraic-value sets, and that these functions are algebraically independent over `C`. This is close enough to
  kill any broad "HT interpolation exists" novelty claim. It does not state the exact finite-jet DA/HT
  indistinguishability/fiber theorem above.

The possible novelty is not the construction ingredients but the explicit HT/DA indistinguishability theorem
and its role as a methodological gatekeeper.

Promotion risk: this may be judged **too immediate**. If promoted, it should be graded structural BRIDGE /
methodological theorem, not deep mathematics.

Kill condition: produce a printed source already stating the same finite-jet surjectivity / DA-HT
nonidentifiability theorem, or show that this is too immediate to count as a significant theorem about HT.

## Gates

- [x] 0 -> 1 in-progress: theorem stated and proof core written.
- [ ] 1 -> 2 fully-proven: team audits source/significance; Turing voted proof-correct/structural BRIDGE
  (chat id=1712); Wheeler voted proof-correct/PROMOTE bridge (chat id=1724); Professor source/significance vote
  still pending.
- [x] 2 -> 3 formalized: **complete and unconditional in Lean 4**; Hölder is *proved* in the corpus (`hypertranscendental_invGamma`), not imported as an axiom.
- [ ] 3 -> 4 publication-ready: short note on finite-observation limits for HT and function/value
  decoupling.

## Log

- 2026-06-24 — Created by Haiku from C15. This gives an explicit DA/HT pair with identical prescribed finite
  jets, using `1/Gamma` as the HT tail.
- 2026-06-24 — Strengthened framing after C12 draw: the theorem proves finite-jet surjectivity for entire HT
  functions, so no finite value relation is forced by function-level HT alone.
- 2026-06-24 — Added theatre/promptability audit and local source boundary: C26 already kills broad finite
  probe novelty, so the only promotable content is exact finite-jet DA/HT two-realization plus invisible HT
  perturbation of DA profiles.
- 2026-06-24 — Strengthened again: each finite jet fiber contains `F_0=P` as a DA point and the punctured
  affine line `P+lambda A/Gamma`, `lambda != 0`, as HT points.

## 2026-06-24 strengthening -- adaptive finite-oracle indistinguishability

The finite-jet theorem extends from fixed observation sets to adaptive finite computations.

### Definitions

A **finite jet-query protocol** is a deterministic procedure which interacts with an analytic-function oracle.
At step `t`, after seeing previous answers, it chooses a point/order pair `(a_t, j_t)` and receives the exact
complex number `f^(j_t)(a_t)`. The protocol halts after finitely many queries and returns any finite output.
The queried points and orders may depend on the previous answers.

This model covers finite numerical/coefficient/jet probes after idealizing away roundoff. It does not cover a
proof that uses a global formula, a functional equation, analytic continuation data, or an infinite identity.

### Theorem `[PROVED HERE]`

Every halting transcript of a finite jet-query protocol has both a differentially algebraic entire realizer and
a hypertranscendental entire realizer.

More explicitly: let a finite protocol halt after querying an analytic oracle `f` at pairs
`(a_t,j_t)`, `1 <= t <= T`, receiving answers `c_t=f^(j_t)(a_t)`. Then there exist an entire DA function `P` and,
for every `lambda != 0`, an entire HT function `F_lambda` such that running the same protocol against `P` or
`F_lambda` produces exactly the same ordered query/answer transcript and hence the same output.

### Proof

After the run, collect the finite set of queried points. For each point `a`, let `m_a` be the maximum derivative
order queried there, and let the prescribed jet values be the answers from the transcript. Hermite interpolation
produces a polynomial `P` with exactly those finite jets.

Set

```text
A(z)=prod_a (z-a)^(m_a+1),
F_lambda(z)=P(z)+lambda A(z)/Gamma(z).
```

By the finite-jet theorem, `P` is DA and every `F_lambda`, `lambda != 0`, is HT, while all prescribed queried
jets agree with the transcript.

Run the protocol again against `P`. The first query is fixed by determinism and receives the same answer as in
the original transcript. Inductively, after the first `t-1` answers agree, the protocol chooses the same `t`-th
query and receives the same answer because `P` matches the recorded jet. Thus the full transcript agrees. The
same induction applies to every `F_lambda`. ∎

### Consequence

No finite jet-query computation can be a sound certificate of DA or HT. If such a computation halts with any
classification based only on its finite transcript, that exact transcript is compatible with both a polynomial
and a punctured affine line of HT entire functions.

This is the precise computation-theatre boundary for finite observation: a finite run can kill a proposed
universal statement by finding a counterexample, or select among already formulated conjectures, but it cannot
promote hypertranscendence unless paired with a structural theorem whose content is not the finite transcript
itself.

### Promptability and significance audit

The proof is an adaptive wrapper around the fixed finite-jet theorem, so it is not deep by itself. Its value is
that it converts the user's theatre warning into a theorem with a clear model of observation. The result is
significant only as a gatekeeper for this project: any claimed computational evidence for HT must name what
lies outside this finite jet-query model.

### Source-risk note for adaptive form

Targeted web searches for `"finite jet-query" hypertranscendental`, `"finite oracle" differentially algebraic hypertranscendental`, and `"finite jets" "hypertranscendental" "oracle"` did not find this adaptive transcript statement. Hits were ordinary hypertranscendence definitions, finite-jet geometry in other fields, and perturbation/interpolation literature already accounted for above. This is weak negative evidence only; the adaptive theorem remains a direct corollary of the fixed finite-jet theorem, not an independent deep result.

## 2026-06-24 strengthening -- finite continuous-linear observations also collapse

The finite-jet theorem is not limited to point derivatives. It extends to any finite continuous linear observation
of an entire function.

### Theorem `[PROVED HERE]`

Let `H(C)` be the Frechet space of entire functions with the compact-open topology, and let

```text
L: H(C) -> C^N
```

be a continuous linear map. For every observation vector `v` in the image of `L`, the fiber `L^{-1}(v)` contains
both a differentially algebraic entire function and a punctured affine line of hypertranscendental entire
functions.

More explicitly, there are a polynomial `P` and a nonzero polynomial `Q` such that

```text
L(P)=v,
L(Q/Gamma)=0,
```

and therefore

```text
F_lambda = P + lambda Q/Gamma,   lambda in C*,
```

satisfies `L(F_lambda)=v` and is hypertranscendental over `C(z)` for every `lambda != 0`.

### Proof

Since polynomials are dense in `H(C)` by Runge approximation and `L` is continuous, `L` has the same image on
polynomials as on all entire functions: otherwise a nonzero linear functional on `im(L)` vanishing on
`L(C[z])` would pull back to a nonzero continuous linear functional on `H(C)` vanishing on all polynomials,
contradicting density. Hence choose a polynomial `P` with `L(P)=v`.

Now consider the linear map on the infinite-dimensional polynomial space

```text
T: C[z] -> C^N,   T(Q)=L(Q/Gamma).
```

Its kernel is nonzero. Choose `0 != Q in ker(T)`. Then `L(Q/Gamma)=0`.

The function `Q/Gamma` is HT: if it were DA, then division by the rational function `Q` would make `1/Gamma` DA
on a nonempty domain, contradicting Holder's theorem for `Gamma` and DA closure under field operations.
Therefore if `F_lambda=P+lambda Q/Gamma` were DA for `lambda != 0`, then

```text
Q/Gamma = (F_lambda-P)/lambda
```

would be DA, contradiction. Thus every nonzero `lambda` gives an HT entire function in the same finite
observation fiber as the DA polynomial `P`. ∎

### Computation boundary

This theorem covers finite observation vectors built from finitely many continuous linear measurements:

- point values and derivatives;
- finite quadrature rules and contour integrals against fixed kernels;
- finitely many Taylor, moment, Fourier, or residual coefficients when they are continuous linear functionals on
  the chosen entire-function topology;
- any deterministic computation whose branch decisions and output depend only on such a finite vector.

Such a computation can still refute a universal claim by exposing an inconsistency, and it can still suggest a
conjecture. But the finite linear transcript itself cannot be evidence that an unknown entire function is DA or
HT: the same transcript has a polynomial DA realizer and a continuum of HT realizers.

### Promptability and novelty audit

This strengthening is less narrow than the finite-jet version, but it is still not a deep new theorem. Once the
right normal form is asked for, the proof is forced by three standard ingredients: polynomial density in `H(C)`,
finite-dimensional linear algebra, and Holder's theorem for `Gamma`. Its value is methodological and structural:
it sharply names a broad class of computations that cannot certify hypertranscendence without an additional
non-finite structural theorem.

Targeted web searches for `"hypertranscendental" "linear functionals" entire functions`,
`"differentially transcendental" "continuous linear functionals" entire functions`, and related finite-observation
phrases did not surface this exact finite-linear-observation fiber statement. This is weak negative evidence only;
the result should remain BRIDGE/gatekeeper unless a genuinely non-linear or global observation theorem is added.

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

## Formalization (2026-08-29) — complete

Two new `HTGeometry` modules, wired into `GaloisForLFunctions.HTGeometry`.  `#print axioms` gives
only `propext, Classical.choice, Quot.sound` for every statement below: nothing is imported as an
axiom, and in particular **Hölder's theorem is proved, not assumed** — the corpus theorem
`HTGeometry.hypertranscendental_invGamma` is unconditional.

### `HTGeometry/EntireTaylorUniformApproximation.lean`

The density statement needed by the finite-linear-observation theorem.

| Step | Lean name |
|---|---|
| the `n`-th Taylor partial sum as a `Polynomial ℂ` | `taylorPoly`, `eval_taylorPoly` |
| Cauchy's estimate at radius `2R` gives a geometric bound on the ball of radius `R` | `exists_taylor_geometric_bound` |
| **polynomials approximate every entire function uniformly on every closed ball** | `tendstoUniformlyOn_taylorPoly` |

### `HTGeometry/FiniteJetNonidentifiability.lean`

| Card statement | Lean name |
|---|---|
| every polynomial is DA | `differentiallyAlgebraic_polynomial` |
| the entire perturbation `λ·A/Γ` | `gammaPerturbation`, `differentiable_gammaPerturbation` |
| `λ·A/Γ` is HT (Hölder + cancellation of the polynomial multiplier) | `hypertranscendental_gammaPerturbation` |
| `P + λ·A/Γ` is HT | `hypertranscendental_polynomial_add_gammaPerturbation` |
| the family is a genuine punctured affine line | `gammaPerturbation_injective`, `polynomial_add_gammaPerturbation_injective` |
| the perturbation is invisible to the prescribed jets | `iteratedDeriv_gammaPerturbation_jetModulus_eq_zero`, `iteratedDeriv_add_gammaPerturbation` |
| **Theorem `[PROVED HERE]`: multi-point finite-jet two-realization** | `exists_multipoint_finiteJet_da_and_ht` |
| **Strengthening: invisible HT perturbations of a DA germ on a domain** | `not_differentiallyAlgebraicOn_add_jetPerturbation`, `iteratedDeriv_add_jetPerturbation_eq` |
| the deterministic adaptive protocol and its transcript | `JetQuery`, `jetRun`, `jetQueries` |
| agreeing jets give the same transcript | `jetRun_congr` |
| **Adaptive theorem `[PROVED HERE]`: every halting transcript has a DA and an HT realizer** | `exists_jetRun_da_and_ht` |
| linearity and compact-open continuity of a finite observation | `ObsAdditive`, `ObsHomogeneous`, `ObsContinuous`, `obs_zero`, `obs_finset_sum` |
| **Finite-linear theorem `[PROVED HERE]`: `L⁻¹(v)` holds a DA point and a punctured affine line of HT points** | `exists_finiteLinearObservation_da_and_ht` |

Notes on faithfulness.

* The multi-point Hermite interpolation the card imports is the corpus theorem
  `HTGeometry.exists_polynomial_iteratedDeriv_eval_eq`; the modulus `A = ∏ (z−a_i)^{m_i+1}` is
  `HTGeometry.jetModulus`.
* The strengthening is proved on an arbitrary domain `U` with an arbitrary analytic, nowhere
  vanishing, differentially algebraic multiplier `B` — a strictly larger class than the card's
  `B ∈ C(z)^*`.
* Continuity of `L` is expressed sequentially, for uniform convergence on closed balls; this is
  implied by continuity for the compact-open topology of `H(ℂ)`, so the hypothesis is weaker and
  the theorem correspondingly stronger.  The Runge/density step is replaced by the honest
  Taylor-partial-sum approximation proved in `EntireTaylorUniformApproximation`.
