# The Gram weld trilemma: finite, positive, Hankel — pick two

- **ID:** `gram-weld-trilemma`
- **Stage:** 2-fully-proven
- **Type:** NO-GO THEOREM
- **Scientific status:** `[PROVED]` `[UNCONDITIONAL]` `[LEAN, AXIOM-CLEAN]` `[NOT AN RH PROOF]`
- **Novelty:** elementary; the content is the reduction that makes it visible, and its scope

## Statement

Let a divergent Hankel-type object be presented as a weighted Gram of a **split feature family**,
`hₙ = uₙ + vₙ`, with weights `cₙ ≥ 0`. Its Gram decomposes as

```text
Gram(h) = Gram(u) + Gram(v) + Cross(u,v) ,      Cross(u,v) i j = ⟨uᵢ,vⱼ⟩ + ⟨vᵢ,uⱼ⟩ .
```

A regularization that keeps a linear combination

```text
R(α,β,γ) = α·Gram(u) + β·½·Cross(u,v) + γ·Gram(v)
```

is subject to three requirements, and can satisfy at most two:

| requirement | condition on `(α,β,γ)` |
|---|---|
| **positive** — `R ⪰ 0` for every feature family | `0 ≤ α`, `0 ≤ γ`, `β² ≤ 4αγ` |
| **Hankel** — `R` is a moment matrix (depends on `i+j`) | needs `β ≠ 0` when `Gram(u)` alone is not Hankel |
| **finite** — the divergent block is discarded | `γ = 0` when `Gram(v)` is the divergent one |

**`γ = 0` forces `β = 0`.** So finiteness plus positivity forces no mixed block, and no mixed block
leaves the Hankel defect of `Gram(u)` uncancelled.

## Proof

Positivity of `R` against *every* feature family is positivity of the scalar form
`α a² + β ab + γ b²`, since the pairings `a = ⟨x,uₙ⟩`, `b = ⟨x,vₙ⟩` are unconstrained. That is the
binary-quadratic discriminant condition. Setting `γ = 0` gives `β² ≤ 0`, hence `β = 0`. ∎

## Lean

`formal/GaloisForLFunctions/HTGeometry/GramCompletionOfSquare.lean`, axiom-clean
(`[propext, Classical.choice, Quot.sound]`), registered, `lake build` green:

```text
gram, mixed, shift                          the three blocks
gram_add_mixed_eq                           uuᵀ + ½(uvᵀ+vuᵀ) = (u+½v)(u+½v)ᵀ − ¼vvᵀ
gram_add_mixed_posSemidef_iff               positivity as a Loewner domination
gram_posSemidef_of_nonneg                   weighted Grams are PSD
quadratic_form_split                        (b−a)b = ½(b−a)² + ½(b²−a²), summed
successorHead_form_neg                      the weld shape is indefinite — one point, one quadratic
blockCombination_nonneg_iff                 the discriminant criterion
mixed_vanishes_of_second_block_discarded    γ = 0 ⟹ β = 0
second_block_pos_of_mixed_ne_zero           β ≠ 0 ⟹ γ > 0
gram_power_isHankel, gram_power_nonneg      power features are Hankel and PSD with no defect
```

Supporting, same session:

```text
HankelNormalizationPositivity.lean   a Hankel normalizer preserves positivity iff it is a moment
                                     sequence (Schur); `1/k!` fails at the first minor, det = −1/2
MultiplicativeRegularizationBlind.lean  a convergent multiplicative regularization is blind to
                                     everything below the leading asymptotic
```

## Where it bites

`RHTower/VonMangoldtSuccessorBianchiHankelWeld` builds a positive Hankel Gram at every finite
aperture from `u` = successor log-jet difference, `v` = pointed-Bianchi jet, `h = u+v` = head jet.
`RHTower/VonMangoldtSuccessorPrincipalRelativeHankel` takes the cofinal limit of the **principal
subtraction** and states: *"It does not assert positivity or identify the current with the completed
Euler/Xi trace."*

The trilemma closes that first clause. The retained object is `R(1,1,0)`, so `β = 1 ≠ 0` with
`γ = 0`: not positive, and `successorHead_form_neg` exhibits the failure at a one-point aperture with
jet depths `{1,2}` and the quadratic `P t = t(a − t)`, `t₁ < a < t₀ + t₁` — no numerics, no
properties of the primes.

The three escapes are closed too:

- **multiplicative regularization instead of subtraction** — `tendsto_mul_regularized`: any convergent
  multiplicative normalization returns the leading asymptotic only, so the arithmetic (which lives in
  the subleading terms) is lost. For the Mertens weight the limit is the Hilbert matrix `1/(i+j+1)`.
- **a different `(α,β,γ)`** — excluded by the trilemma itself.
- **features with no Hankel defect** — those are power families `uₙ(i) = tₙⁱ`
  (`gram_power_isHankel`), and by Hamburger a finite PSD Hankel matrix *is* such a family against a
  positive measure. For the prime-side data that is the conclusion, not a route; and the power family
  `tₙ = log n` against `Λ(n)/n` is the divergent object the differencing was introduced to repair.

## Scope and honesty

- The trilemma is about **split-feature Gram welds**. It says nothing about regularizations outside
  that family.
- It is not deep: the criterion is a binary quadratic's discriminant. **The content is the reduction**
  — Gram → Hadamard → Loewner → Abel → scalar — that makes a two-line argument reach an object the
  corpus had left open behind four layers of language.
- It proves no RH statement and refutes none. It closes one route.

## Sources

- `RHTower/VonMangoldtSuccessorBianchiHankelWeld.lean`
- `RHTower/VonMangoldtSuccessorPrincipalRelativeHankel.lean`
- `RHTower/VonMangoldtGammaFactorialNormalizationNoGo.lean`
- `RHTower/VonMangoldtGammaBetaReflectionRankOneRepairNoGo.lean`
- Schur product theorem; Hamburger moment theorem; Mertens' theorem.

## Gates

- [x] statement, proof, Lean, axiom-clean, registered, build green
- [x] applied to the corpus weld; the open clause closed
- [x] all three escapes closed
- [x] scope stated
