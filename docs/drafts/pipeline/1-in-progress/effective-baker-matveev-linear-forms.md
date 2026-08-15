# Effective Baker–Matveev: a polynomial lower bound for linear forms in prime logarithms

- **ID:** `effective-baker-matveev-linear-forms`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — formalization of a classical deep theorem
- **Statement:** For distinct primes `p₁,…,p_d` there are `c, C > 0` with
  `|Σᵢ νᵢ log pᵢ| ≥ c (2+|ν|₁)^{-C}` for every nonzero `ν ∈ ℤ^d`.

## Goal

`suzuki-log-recurrence-polynomial-carrier-trichotomy` needs exactly this as its `(5)`:

```text
τ₀(ν) = [−log|ℓ(ν)|]₊ ≤ C·log(2+|ν|₁),   ℓ(ν) = Σ νₚ log p.
```

Without it only the elementary Liouville bound is available, and that is exponential, not
logarithmic:

```text
ℓ(ν) = log(N/M),  N,M coprime S-units,  |N/M − 1| ≥ 1/M ≥ P^{−|ν|₁}
  ⟹  τ₀(ν) ≤ |ν|₁ log P.
```

Finite *exponential* recurrence type `R(a) < ∞` follows from that; finite **logarithmic** type
`T_log(a) < ∞` — the card's actual admission class — does not.  The gap between the two is exactly
Baker's theorem, so the card cannot be promoted to stage 3 without it.

Equivalent classical formulation: for `S`-units `N ≠ M` built from the fixed prime set,

```text
|N − M| ≫ max(N,M) / (log max(N,M))^C .
```

## What already exists

**In the corpus** — the *qualitative* theorem is fully proved and unconditional:

```text
RHTower/BakerWeldIndependence.lean        the interface `BakerLinearIndependence`
RHTower/BakerProof/MinimalRelation.lean   support-reduced relation, arity ≥ 3
RHTower/BakerProof/NormalizedRelation.lean  pivot normalization
RHTower/BakerProof/CoefficientField.lean  canonical coefficient number field
RHTower/BakerProof/AuxiliaryFunction.lean       the exponential polynomial
RHTower/BakerProof/AuxiliaryComponents.lean
RHTower/BakerProof/AuxiliaryMatrix.lean         the Siegel-type kernel
RHTower/BakerProof/AuxiliaryArithmetic.lean
RHTower/BakerProof/AuxiliaryExtrapolation.lean  the long extrapolation
RHTower/BakerProof/MultipointSchwarz.lean       the multipoint Schwarz lemma
RHTower/BakerProof/AuxiliaryZeroEstimate.lean
RHTower/BakerProof/BakerParameters.lean         the parameter budget
RHTower/BakerProof/BakerIteration.lean          `bakerLinearIndependence_holds`
RHTower/GelfondSchneider.lean, GelfondSchneiderProof/, GelfondSchneiderSiegel.lean
```

That proof argues from an **exactly vanishing** relation `Σ βᵢ log pᵢ = 0` (`Relation.vanishes`)
and derives a contradiction.  It therefore yields no lower bound: what is needed is the same
machinery run with an **approximate** relation `|Λ| ≤ ε`, with `ε` and the parameter budget linked.

**In mathlib**

```text
Mathlib/NumberTheory/SiegelsLemma.lean         exists_ne_zero_int_vec_norm_le
Mathlib/NumberTheory/Height/{Basic,Northcott,NumberField,MvPolynomial}.lean
Mathlib/NumberTheory/MahlerMeasure.lean
Mathlib/NumberTheory/Transcendental/{Liouville,Lindemann}/
Mathlib/Analysis/Fourier, Analysis/Complex/*                (Schwarz, Cauchy estimates)
```

## Approach

Non-explicit constants.  The card needs only `∃ c C`, not Matveev's numerical values, which removes
the entire explicit-constant bookkeeping and is what makes the formalization feasible.

Layers, each a self-contained unconditional module:

- **A. Statement and elementary reductions.**  The target `Prop`; reduction of `∃ c C` to a
  large-`B` statement; the `d ≤ 1` cases; the elementary Liouville baseline
  `|Λ| ≥ P^{−|ν|₁}`, which already gives nonvanishing and fixes normalizations; the `S`-unit
  reformulation `|N − M|` and the two-sided comparison `|log t − (t−1)|`.
- **B. Small-linear-form relation object.**  A quantitative analogue of `BakerProof.Relation`:
  integer coefficients, a bound `B`, and a smallness hypothesis `|Λ| ≤ exp(−κ log B)`.  The
  normalization `log p_pivot = −Σ (bᵢ/b_pivot) log pᵢ + Λ/b_pivot` replaces
  `Relation.pivot_log_eq`, with the error term carried explicitly.
- **C. Auxiliary function with an error term.**  Rebuild `AuxiliaryFunction`/`AuxiliaryMatrix`
  over the approximate normalization; every occurrence of the exact pivot identity acquires a
  controlled perturbation.
- **D. Extrapolation with error.**  The corpus extrapolation is already parameter-explicit
  (`stageSampleCount`, `stageOrder`, `iterationLength`, `structuredBase`); rerun it tracking the
  perturbation, choosing the parameter budget as a function of `B`.
- **E. Terminal contradiction.**  The zero estimate forces the auxiliary coefficients to vanish,
  contradicting the Siegel-type nonvanishing, unless `|Λ| > B^{−C}`.
- **F. The card interface.**  Export `τ₀(ν) ≤ C log(2+|ν|₁)` in the card's variables and wire it
  into `suzuki-log-recurrence-polynomial-carrier-trichotomy`.

## Gates

- [x] 0 → 1  well-posed, source identified, existing corpus/mathlib inventory taken
- [x] A. statement, reductions, Liouville baseline, S-unit reformulation
      — `RHTower/Matveev/LinearFormBasic.lean`
- [x] B. small-linear-form relation object and perturbed normalization
      — `RHTower/Matveev/SmallForm.lean`
- [ ] C. auxiliary function and matrix with error term
- [ ] D. extrapolation with error
- [ ] E. terminal contradiction, the effective theorem
- [ ] F. card interface `τ₀(ν) ≤ C log(2+|ν|₁)`
- [ ] 1 → 2  complete paper proof recorded
- [ ] 2 → 3  Lean theorem, axiom surface `propext, Classical.choice, Quot.sound`

## Log
- 2026-08-15 — created; corpus inventory shows qualitative Baker is already unconditional, the
  effective form is not.
- 2026-08-15 — Layers A and B closed and axiom-audited.

  **A** (`RHTower/Matveev/LinearFormBasic.lean`).  `primeLogForm`, `coeffHeight`, `primeBound`;
  the transported `ℤ`-independence `primeLog_linearIndependent_fin` and hence
  `primeLogForm_eq_zero_iff`; the `S`-unit decomposition `primeLogForm_eq_log_sub`; the elementary
  `1 − t⁻¹ ≤ log t` and its consequence `inv_le_log_sub_log`; the Liouville baseline
  `inv_max_le_abs_primeLogForm` and `inv_pow_le_abs_primeLogForm`
  (`|Λ| ≥ Q^{−|ν|₁}`); the statement `EffectiveBakerBound`; and the reduction
  `effectiveBakerBound_of_large` — the polynomial bound need only be proved above any fixed
  height, since below it the Liouville baseline is a uniform positive constant and shrinking `c`
  absorbs it.  No finiteness argument is used.

  **B** (`RHTower/Matveev/SmallForm.lean`).  `coeffSup`, its comparison with `coeffHeight`,
  `exists_max_pivot`; the `SmallForm` structure (nonzero integer coefficients with a maximal
  pivot); `normCoeff` with `|normCoeff i| ≤ 1` and `normCoeff pivot = 1`; and the perturbed
  normalization

  ```text
  log p_pivot = −Σ_{i≠pivot} normCoeff i · log pᵢ + Λ / b_pivot,
  ```

  the exact analogue of the corpus `Relation.pivot_log_eq` with the error term carried.
