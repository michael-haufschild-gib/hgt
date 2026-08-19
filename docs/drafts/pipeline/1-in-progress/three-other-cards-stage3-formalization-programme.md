# Stage-3 formalization programme for three `2-fully-proven/other` cards

- **ID:** `three-other-cards-stage3-formalization-programme`
- **Stage:** 1-in-progress (ledger; not a research card)
- **Type:** FORMALIZATION LEDGER
- **Targets:**
  1. `bessel-order-intensity-hypertranscendence`
  2. `jet-horizon-translation-gauge-classification`
  3. `embedded-manin-horizon-isogeny-reconstruction`

Each of the three is blocked on a *foundational* layer, not an assembly step.  This file records
the exact blocked statement, the chosen route, and the layer order, so the work survives
compaction.

## Card 2 — jet-horizon translation-gauge classification

**Blocked on (card's own boundary):** DCF_0 model theory — differential genericity, dtrdeg
invariance, quantifier elimination giving the fixed-field identity `(12)`, and the Picard--Vessiot
identification of the torsor layers `(7)`.

**Route found (2026-08-19): the model theory is avoidable.**  The whole theorem is purely
differential-algebraic once the *Taylor arc* is used instead of the DCF embedding groupoid.

Let `(F, δ)` be a differential field, `ℚ ⊆ F`, constants `C`.  The Taylor morphism

```text
τ : F → F⟦T⟧,   τ(a) = Σ_n (δ^n a / n!) T^n
```

is an injective ring homomorphism with `d/dT ∘ τ = τ ∘ δ`.  For `z ∈ F^m` and `P ∈ C[X]`,
`τ(P(z)) = P(τ z)`, so the jet sequence of `z` *is* a formal arc on the locus `Y` of `z`.

Then:

* `h ∈ ker δ^n`  ⟺  `τ(h)` is a polynomial of degree `< n` in `T`.
* If `σ` is a differential `C`-embedding fixing `δ^n z`, then `h = σ z − z ∈ ker δ^n`, and
  `P(τ z + τ h) = 0` for every `P ∈ I(Y)`.
* If `τ z` is a *generic point of `Y`* over the coefficient field `Ω ⊇ C⟨h⟩` — i.e.
  `ker(Ω[X] → Ω⟦T⟧, X ↦ τ z) = I(Y)·Ω[X]` — then `P(X + τh) ∈ I(Y)·Ω[X]`, i.e.
  `Y + τh = Y`, hence every coefficient of `τ h` lies in `A = Stab_trans(Y)`.  This is `(3)`.
* `A = 0` therefore forces `σ z = z`, hence `σ = id`, hence `H_n(Y) = F`: this is `(4)`, with no
  quantifier elimination.  The infinitesimal form (derivations commuting with `δ` instead of
  embeddings) gives the same conclusion and identifies `Der^δ_{H_n}(F) ≅ A ∩ ker δ^n`.
* The quantitative form is `trdeg(C⟨z⟩ / C⟨δ^n z⟩) = n · dim A`, which with the already-formalized
  cylinder splitting `(5)` reduces to the `A = 0` base case plus the free-jet count for the
  additive factor — that is the torsor tower `(7)`, `(8)`.

**Lean layer order.**

1. `DifferentialTaylorMorphism` — τ as a ring hom, injectivity, `τ ∘ δ = d/dT ∘ τ`,
   `τ (aeval z P) = aeval (τ ∘ z) P`, `ker δ^n` ⟺ polynomial of degree `< n`.  [layer 1]
2. `DifferentialLocusTranslation` — the locus ideal of a point, translation stabilizer of an
   ideal, and: a translation carrying the locus into itself is an equality (Noetherian surjective
   endomorphism).  [layer 2]
3. `DifferentialGenericPoint` — the genericity predicate `ker(Ω[X] → …) = I·Ω[X]`, and its
   consequences.  [layer 3]
4. `JetHorizonEmbeddingRigidity` — `(3)`.  [layer 4]
5. `JetHorizonReconstruction` — `(4)`, both directions.  [layer 5]
6. `JetHorizonTorsorTower` — `(6)`, `(7)`, `(8)` and the trdeg formula.  [layer 6]

Already in the tree: `JetHorizonTranslationGauge` (cylinder splitting `(5)`, gauge `(3)`/`(9)`
kernel half), `DerivationIterateLeibniz`, `DifferentialTranscendenceDegree`,
`AffineZariskiClosureOver`, `DifferentialKolchinClosure`.

## Card 3 — embedded Manin horizon

**Theorem A** (`Stab_A(T_A) = A^♯`) is short once the Manin map is available as a group
homomorphism with kernel `A^♯` and the tail is `K⟨μ_A(a)⟩`.

**Theorem B** imports Manin-kernel rigidity (Casale--Freitag--Nagloo Fact 5.6, ultimately
Hrushovski's dichotomy).  Unconditional Lean requires that rigidity itself.  Layer order to be
fixed after card 2; the tree already owns `MultiplicationTailFixedField`,
`ManinKernelKolchinClosure`, `AbelianManinHorizonTheorem`, `DifferentialKolchinClosure`.

## Card 1 — Bessel order/intensity hypertranscendence

**Blocked on:** Dreyfus's classification (parameterized Picard--Vessiot for difference
equations).  Everything else in the card is already unconditional in the tree, and
`BesselOrderDreyfusNormalForm` states the reduction machine-checked.

Rank-two reformulation that the Lean layer must reach: with `u(ν) = K_ν(s)`, `v(ν) = K_{ν−1}(s)`,
`a = 2ν/s`, the shift acts `σu = a u + v`, `σv = u`; a second solution is `w_ν = e^{iπν} I_ν(s)`
with Casoratian `−e^{iπν}/s`.  Differential algebraicity of `u` makes `N = ℂ(ν)⟨u,v⟩` a `σδ`-field
of finite transcendence degree over `ℂ(ν)`; the classification is what converts that into the
growth normal form.  No elementary substitute has been found: Hölder's method needs the shift to
act by a *rational multiple*, which fails at rank two.

## Log

- 2026-08-19 — programme opened; model-theory-free Taylor-arc route for card 2 identified.
