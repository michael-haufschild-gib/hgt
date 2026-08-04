# MR splice stage 3b falsified; range induction is the surviving shape (2026-08-04)

Card: `docs/drafts/pipeline/1-in-progress/mr-splice-wide-range-mean-square.md`.

Numeric pre-certification of the frozen stage-3b architecture (Ramaré range (P₁,z] + Brun rough
remainder + weighted pointwise CS over dyadic prime blocks + double split + fibre-9 sixth moment
+ stage-3a dyadic Gallagher tail) DIVERGES: variance/L² ≈ (logN)^{+2.8} at its optimum over all
parameters. No Lean was written — the discipline (pre-certify before Lean) blocked it.

**Certified obstruction:** the exceptional-set tail of the long μ-cofactor factor,
`∫_{|F₁|≥V₁}|F₁|² ≈ (N/P)²·logN·logK₁` by MVT layer cake; after harmonic weights this is a
`logN·loglogN` loss per block-sum and nothing in the built toolkit pays it. Dead escapes,
checked: ℓ-adapted high moments of the prime factor (exp((logN)^{0.4}) loss at logP=(logN)^0.6;
degenerate at logP≍logN); pointwise contour control of F₁ (reach only exp((logN)^{1/10})).

**Surviving shape:** the genuine Matomäki–Radziwiłł range induction — control F₁'s level sets by
re-factorizing F₁ at a lower designated range, iterating over ≈ loglogN scales with schedule
logP_j ≍ ρ^j and per-scale adapted moments ℓ_j, terminal scale paid by the built
`MoebiusUniformFrequency` Halász layer. Next unit (stage 3b′): numeric model of the full
induction BEFORE any Lean. The variable-ℓ prime-fibre mass bound
`∑|coeffs(F₂^ℓ)|² ≤ ℓ!(∑|b_p|²)^ℓ` (generalizing PrimeCubeSupport) will be needed by any
certified variant but is not licensed until the model closes.

Lesson: single- and double-split architectures over ONE designated range are now certifiably
insufficient for θ < 1 at any threshold — do not revisit them.
