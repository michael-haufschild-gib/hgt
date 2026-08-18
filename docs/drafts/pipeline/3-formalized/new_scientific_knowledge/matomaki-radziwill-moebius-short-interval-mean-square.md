# Matomäki–Radziwiłł Möbius short-interval mean square

- **ID:** `MR-MOEBIUS-SHORT-INTERVAL-MEAN-SQUARE-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CLASSICAL ANALYTIC INPUT, BUILT
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOT RH]`
- **Parent:** `../../1-in-progress/matomaki-radziwill-lean-programme.md`
- **RH used:** no
- **Computation used:** no

## Exact theorem package

Write `cardLength β x = exp((log x)^β)`.  For the balanced pair decomposition

```text
outerBlock x h  = { a : sqrt x ≤ a ≤ 2 sqrt x,  a ≤ x + h sqrt x }
innerFibre x h a = { b : x ≤ a b ≤ x + h sqrt x }
```

`AveragedMeanSquare f h` is the statement

```text
( sum_{a in outerBlock x (h x)} ( sum_{b in innerFibre x (h x) a} f b )^2 )
  / ( h x ^ 2 * sqrt x )  ->  0 .
```

Lean proves, with no hypotheses:

```lean
theorem averagedMeanSquare_moebius_cardLength {β : ℝ} (γ : ℝ)
    (hβ0 : 9 / 10 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) :
    AveragedMeanSquare (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) (cardLength β)

theorem averagedMeanSquare_moebius :
    AveragedMeanSquare (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ))
      (cardLength (99 / 100))
```

The window `exp((log x)^{99/100})` is below every power of `x`: this is the short-interval regime,
not the square-root one.  It is the Matomäki–Radziwiłł mean square in the shape the corpus's Route E
reduction consumes.

Consequences, also with no hypotheses:

```lean
theorem route_e_sign_density_unconditional {s : ℤ} (hs : s = 1 ∨ s = -1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ 2 / 2 - squarefreeDensity ^ 2 * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (cardLength (99 / 100) x) s
          / (cardLength (99 / 100) x * Real.sqrt x * Real.log 2)

theorem route_e_signClass_nonempty_unconditional {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∀ᶠ x in atTop, (coprimeSignClass x (cardLength (99 / 100) x) s).Nonempty
```

## The admissible exponent window

`9/10 < β < 1`, with an auxiliary `γ` satisfying `0 < γ < 1` and `9/10 < γβ < 1`.  The lower
threshold `9/10` is the corpus's Route-T zero-free width exponent, not a limitation of the argument:
the same proof with Vinogradov–Korobov's `2/3` would give `β > 20/27`, the exposé's range.

## Proof architecture

1. **Rough half.**  Integers of the fibre with no prime factor in `(z₀, z]` are removed by the
   2-dimensional Selberg sieve: `Sieve/RoughPartArith`, `Sieve/RoughPartLimit.tendsto_roughPart`.
2. **Spectral half.**  The Ω-weighted Möbius polynomial of the fibre is decomposed along a geometric
   ladder of prime blocks of relative width `η`, each block a product of a narrow prime polynomial
   and a common cofactor polynomial:
   - annulus `w₀ ≤ |w| ≤ T₀`: the prime polynomial is small by the Route-T twisted von Mangoldt
     bound at polylogarithmic width (`Sieve/VonMangoldtTwistScaledEnvelope`,
     `Sieve/AnnulusRelBound`);
   - low frequencies `|w| ≤ w₀`: the cofactor polynomial is small by the sharp twisted Möbius
     contour bound (`Sieve/CofactorLowFreqBound`, `Sieve/RelMoebiusSharp`);
   - the Gallagher tail is paid by the affine ladder-quality majorant
     (`Sieve/LadderStepAffine`, `Sieve/LadderAffineMajorant`, `Sieve/OmegaBudgetLadderTail`).
3. **Substitution.**  `h = exp((log x)^β)`, `Q = z₀ = ⌈exp((log x)^{γβ})⌉`,
   `η = (log x)^{γβ−β−1}`, `w₀ = (log x)^{13}`, `D = (log 2h)^4`, `B₀ = ⌊√x + h⌋`, `G = B₀/h`,
   `T₀ = B₀`.  The whole spectral half then reduces to `ρ·L → 0` (`Sieve/RhoLimit`).
4. **Normalisation.**  `Sieve/BudgetTermSplit` splits `omegaBudget/(W²h²√x)` into four groups and
   collapses the three spectral ones to `136 αL/(B₀hW²) + 140 Ec/(B₀hW²) + 131 βL/(B₀²W²)`; the
   three quotients vanish (`Sieve/SlopeQuotientLimit`, `Sieve/EnergyQuotientLimit`,
   `Sieve/ConstQuotientLimit`), as does the non-spectral remainder
   (`Sieve/NonSpectralBudget`).

## Lean certificate

Modules: `GaloisForLFunctions/RHTower/Sieve/MoebiusMeanSquare.lean`,
`Sieve/BudgetLimit.lean`, `Sieve/RouteEMoebiusUnconditional.lean`, and the ~40 modules of the
programme listed on the parent card.

`#print axioms averagedMeanSquare_moebius` →
`[propext, Classical.choice, Quot.sound]`.
`#print axioms route_e_sign_density_unconditional` →
`[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `axiom`, no premise.

## What this does NOT give

The **integer-start** form `∑_{t ∈ [A,B]} (∑_{n ∈ (t,t+ℓ]} μ(n))²` — the corpus's
`dyadicMeanSquare` — is a different object and is not proved here.  The two reciprocal-marker cards
(`ROUTE-E-RECIPROCAL-MARKER-HALL-001`, `ROUTE-E-GROWING-RECIPROCAL-MARKER-002`) need that form
through `Sieve/GoodStartMarkov.card_le_good_add_meanSquare`, and remain open.  The gap is the Ramaré
normalisation: this programme controls the **Ω-weighted** polynomial, whose cofactor coefficients are
plain `μ`, while the plain polynomial's Ramaré bilinear form carries the weight `1/(ω_P(m)+1)` on
the cofactor.  `Sieve/RamareBlockSplit` already reduces the plain polynomial to the same ladder of
products, so what is missing is exactly the low-frequency contour bound for
`∑_m μ(m)/(ω_P(m)+1) m^{−2πiw}`.
