# The linear-forms criterion for the exponential-period corank, and the γ₀ atom localized

- **ID:** exp-period-corank-linear-forms
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — the mechanism of the DSS-cross attack + the atom reduction
- **Source:** the DSS-cross / exponential-period lane (`docs/proofing/08-worklog-dss-cross.md`,
  Attacks 1–9); the seam = period/non-period divide (`docs/denied/seam-is-the-period-nonperiod-divide.md`).
- **Statement:** The integer-linear-forms criterion — if integer forms `pₙ + qₙ·α` (resp.
  `aₙ + Σᵢ bₙᵢ·xᵢ`) are nonzero and tend to `0`, then `α` is irrational (resp. the `xᵢ` are not all
  rational) — is formalized from scratch (absent from mathlib). It reduces the weakest necessary point
  of the DSS/exponential-period apex, the irrationality of `Real.eulerMascheroniConstant` (= the
  Stieltjes constant `γ₀`, the archimedean regularization datum of `ζ` at `s=1`), to an explicit
  construction problem: produce nonzero integer forms in `γ₀` tending to `0`.

## Goal

The apex question — do the non-period (Stieltjes/exponential-period) constants escape the period field
— was attacked from nine independent angles (worklog Attacks 1–9), all terminating at one wall: the
irrationality of `γ₀`, untouched by every existing transcendence tool (Baker/Wüstholz see only 1-motive
periods; Nesterenko/Chudnovsky only the holomorphic modular side; Rivoal–Ball/Apéry only
rational-function `ζ`-value sums). The one machine that *would* decide it is the integer-linear-forms
criterion. This card formalizes that machine and pins the reduction to mathlib's `eulerMascheroniConstant`,
turning "is `γ₀` irrational" into the precise, machine-checked interface "construct the forms."

## The Lean certificate (axiom-clean)

`GaloisForLFunctions/HTGeometry/ExponentialPeriodCorank.lean` (all `[propext, Classical.choice, Quot.sound]`,
lint green):

- `irrational_of_linearForms (α p q …)` — **the engine**: nonzero integer forms `pₙ + qₙ·α → 0` ⟹
  `Irrational α`. Proof: if `α = c`, each form is `mₙ/c.den`, `mₙ ∈ ℤ` nonzero, so `|·| ≥ 1/c.den > 0`,
  contradicting `→ 0`. Not in mathlib — built (rule 1).
- `not_all_rat_of_linearForms {k} (x a b …)` — **the family/independence engine**: nonzero integer
  forms `aₙ + Σᵢ bₙᵢ·xᵢ → 0` ⟹ the `xᵢ` are not all rational (the form is `mₙ/D` with `D = ∏ᵢ(rᵢ).den`
  fixed). This is the shape a full DSS-cross attack on the Stieltjes family feeds.
- `eulerMascheroniConstant_irrational_of_linearForms` — **the atom localized**: `Irrational γ₀` follows
  from the existence of such forms. The reduction of the open problem to a construction, machine-checked
  against mathlib's constant.

## Approach and the open input

`γ₀` is the archimedean/non-period side of the seam `ξ = (Γ-factor)·ζ`; the convergent `ζ`-values
`ζ(k) = (1/(k−1)!)∫₀^∞ t^{k−1}/(eᵗ−1)dt` are the period side. The criterion is the exact tool that would
separate them. The construction it needs is the open input, and the attack campaign identified the
concrete obstruction (not formalizable unconditionally): the natural approximants
`harmonic n − log n → γ₀` (`Real.tendsto_harmonic_sub_log`) carry the transcendental `log n`, so they are
**not** integer forms in `γ₀`; and the coefficient-extraction forms `∮(ζ(1+z) − 1/z)Q(z)dz` are dominated
by the factorial `Γ`-factor of the functional equation. Defeating this `log`/`Γ` entanglement — producing
genuine integer forms — is the irreducible open input; the formalized criterion is exactly the interface
it must satisfy.

## Verdict — dual gate

**DELIVERED (formalized):** the linear-forms criterion (single- and multi-variable) is proven,
axiom-clean, and is a genuine mathlib gap-fill; the DSS/exp-period atom (`γ₀` irrationality) is reduced,
machine-checked, to constructing integer forms.

**Graded honestly:** the *criterion* is a standard elementary mechanism (formalizing it is legitimate
infrastructure, not new mathematics); the *reduction* localizes a famous open problem but does not solve
it. The construction of the forms — equivalently, an irrationality/independence proof for `γ₀` and the
Stieltjes family — is beyond every 2026 transcendence tool (worklog Attacks 1–9), and rational approximants to `γ₀` do exist (Aptekarev et al.), but the formalized engine forces the exact
frontier: they do not satisfy the `h0` hypothesis (forms `→ 0`, the quantitative irrationality-measure
threshold) — else irrationality would follow immediately. The open input is precisely `h0`. This is the
genuine frontier: the interface is built and the open input is named to the millimeter; crossing it
requires a transcendence theory of archimedean regularized constants that does not yet exist.

## Log
- 2026-07-07 — created in 3-formalized: the integer-linear-forms criterion formalized from scratch
  (`ExponentialPeriodCorank.lean`, 3 theorems, axiom-clean, lint green) — single-variable irrationality
  engine, multi-variable family engine, and the `eulerMascheroniConstant` atom localization. The
  mechanism of Attacks 1–9 made machine-checked; the open input (construct the forms) named precisely.
