# Multiple-Gamma deletion retains cyclotomic orbit multiplicity

- **ID:** `multiple-gamma-cyclotomic-deletion-multiplicity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / DEPENDENT-PERIOD HOSTILE TEST
- **Scientific status:** `[PAPER-PROVED] [POSITIVE CORPUS BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [UNCONDITIONAL LEAN PROOF OPEN AT ANALYTIC PARENT]`
  `[NOT AN RH RESULT]`
- **Parent:**
  `../../1-in-progress/multiple-gamma-period-deletion-annihilator-law.md`
- **Analytic input:**
  `../new_scientific_knowledge/elliptic-gamma-rank-three-da-spectrum.md`
- **Statement:** On the dependent frame `(alpha,beta,m*alpha)`, the cyclotomic orbit-norm factor in
  the rational deletion ideal cannot be cancelled.  The nonreduced quotient-group-algebra scheme,
  not its radical or minimum depth, records the exact analytic distinction.

## Setup

Let `m>=2`, let `alpha,beta in H`, and assume

```text
1, alpha, beta are Q-linearly independent.                                 (1)
```

For the order-two multiple elliptic Gamma logarithmic derivative put

```text
F(z)=Psi_2(z; alpha,beta,m*alpha),
g_j=T_(tau_j), x_j=g_j-1,                                                  (2)
```

where `(tau_0,tau_1,tau_2)=(alpha,beta,m*alpha)`.  In the translation group algebra modulo the
unit period,

```text
g_2=g_0^m.                                                                 (3)
```

## Main theorem `[PROVED HERE]`

The rational period-deletion ideal is

```text
D=(x_1,x_0*x_2)
 =(x_1,(g_0-1)^2*(1+g_0+...+g_0^(m-1))).                                  (4)
```

Moreover:

```text
x_1 F is DA,
x_0*x_2 F is DA,
x_0^2 F is HT.                                                             (5)
```

Consequently the cyclotomic factor

```text
1+g_0+...+g_0^(m-1)                                                        (6)
```

cannot be cancelled from the second generator.  In particular the radical, reduced zero set, and
minimum support depth of `D` do not determine the analytic translation-annihilator data even on
this explicit one-relation frame.

## Proof

Deleting `beta` leaves `(alpha,m*alpha)`, whose rational span together with `1` has rank two.
The rational-rank-two DA theorem therefore gives `x_1 F` DA.  No other singleton deletion lowers
the rank.  Every two-label deletion leaves at most one upper-half-plane period and hence rank two,
so the deletion ideal is generated minimally by `x_1` and `x_0*x_2`.  Relation `(3)` yields the
factorization in `(4)`.

Hierarchy descent gives

```text
x_0 F=Psi_1(z; beta,m*alpha),
x_0^2 F=Delta_alpha Psi_1(z; beta,m*alpha).                                (7)
```

The triple `1,beta,m*alpha` is rationally independent.  Its exact order-one elliptic-Gamma DA
spectrum is

```text
Z+Z*beta+Z*m*alpha.                                                        (8)
```

The shift `alpha` is not in `(8)`: an equality

```text
alpha=k+l*beta+n*m*alpha
```

would contradict `(1)`, since `1-n*m` cannot vanish for integers `n` when `m>=2`.  The exact
spectrum theorem therefore makes the last expression in `(7)` HT.

On the other hand, commuting the two structural differences and descending twice gives an
order-zero theta logarithmic derivative:

```text
x_0*x_2 F is DA.                                                           (9)
```

Equations `(4)`, `(7)`, and `(9)` prove `(5)` and show that `(6)` is analytically indispensable.
`QED`

## Scheme-theoretic residue

The positive statement is stronger than the observation that the period matroid has one parallel
pair.  The quotient group algebra retains collision multiplicity and torsion characters:

- repeated labels `(alpha,alpha,beta)` give `(x_beta,x_alpha^2)`;
- a circuit `tau_2=tau_0+tau_1` gives `(x_0,x_1)^2` after eliminating `x_2`;
- a rational offset `tau_2=tau_0+1/m` introduces a torsion character `h` with `h^m=1`; in the
  character sector `h=zeta`, the predicted factor is

  ```text
  (g_0-1)*(zeta*g_0-1),                                                    (10)
  ```

  a double point for `zeta=1` and two distinct simple points otherwise.

Thus any proof of the full reverse inclusion must be scheme- and multiplicity-aware.  An ordinary
matroid, radical ideal, or reduced face variety discards information that the analytic source can
detect.

## Novelty and RH boundary

The theorem is a direct specialization of the existing exact order-one spectrum plus the standard
multiple-Gamma hierarchy.  It is a useful hostile test and a sharpened design constraint for the
live conjecture, not an independent novelty claim.

It remains relation-side information.  It provides no Euler--Gamma positive Gram realization,
prime refinement, or summable cofinal defect, and therefore cannot discharge the producer theorem
required by `docs/reports/rh-proof-shape-1707.md`.

## Lean boundary

No conditional Lean wrapper is warranted.  The group-algebra factorization in `(4)` is elementary,
and the hierarchy is already formalized, but the load-bearing HT assertion in `(7)--(8)` depends on
the actual order-one elliptic-Gamma spectrum, whose unconditional analytic Lean construction is
still open.  This card advances only after that parent exists in Lean.

## Lean certification — 2026-08-19 (stage 2 → 3)

The card's "Lean boundary" note said this card advances only once the order-one elliptic-Gamma
spectrum exists unconditionally in Lean.  It does (stage-3
`elliptic-gamma-rank-three-da-spectrum`, bridged in
`HTGeometry/MultipleEllipticGammaGenericSpectrum.lean`), so the whole card is now formalized.

New module: `formal/GaloisForLFunctions/HTGeometry/MultipleGammaCyclotomicDeletionMultiplicity.lean`,
wired into `GaloisForLFunctions.HTGeometry`; `#print axioms` reports only `propext`,
`Classical.choice`, `Quot.sound`.

| Card statement | Lean name |
|---|---|
| the dependent frame `(α, β, mα)` and its upper-half-plane hypothesis | `cyclotomicFrame`, `cyclotomicFrame_im_pos` |
| `(3)` `g₂ = g₀^m`, in operator form `Δ_{mα} = (∑_{i<m} T_{iα}) ∘ Δ_α` | `meroTranslationDefect_natCast_mul` |
| the rank-two collapse of the deleted pair `(α, mα)` | `not_linearIndependent_alpha_natMul`, `not_linearIndependent_natMul_alpha` |
| the surviving rank-three pair `(β, mα)` | `linearIndependent_beta_natMul` |
| `(5)` `x₁ F` is DA | `da_cyclotomicFrame_deleteBeta` |
| `(5)`,`(9)` `x₀x₂ F` is DA | `da_cyclotomicFrame_deleteAlphaPair` |
| `(5)`,`(7)`,`(8)` `x₀² F` is HT (because `α ∉ ℤ + ℤβ + ℤ(mα)`: `1 − bm ≠ 0` for `m ≥ 2`) | `hypertranscendentalOver_cyclotomicFrame_alphaSquare` |
| `(4)`,`(6)` **the cyclotomic factor is analytically indispensable** | `cyclotomicDeletionMultiplicity` |

`cyclotomicDeletionMultiplicity` packages the whole separation: `x₁F` DA, `x₀x₂F` DA, `x₀²F` HT, and
the exact operator identity
`x₀x₂F = ∑_{i<m} T_{iα} (x₀²F) = (1 + g₀ + … + g₀^{m−1})·x₀²F`.
So the cyclotomic sum carries a hypertranscendental element into the differentially algebraic
locus; deleting it from the second generator of `D = (x₁, x₀x₂)` would change the analytic content,
which is exactly the card's scheme-theoretic residue: the radical, reduced zero set, and minimum
support depth of the deletion ideal do not determine the analytic translation-annihilator data.

The card's RH boundary is unchanged: this is relation-side information and supplies no Euler–Gamma
positive Gram realization.
