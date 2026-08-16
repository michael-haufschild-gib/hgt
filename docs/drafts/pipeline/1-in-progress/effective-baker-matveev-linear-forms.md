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
- [x] C. auxiliary function and matrix with error term
      — `RHTower/Matveev/{PerturbedFrequency,PerturbedPower,PerturbedKernel,PerturbedComponents,AuxiliaryMatrix}.lean`
- [x] D.1 extrapolation with error, analytic core
      — `HTGeometry/ApproximateMultipointSchwarz.lean`
- [ ] D.2 Fel'dman-polynomial auxiliary construction (replaces the plain-multiplicity matrix)
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
- 2026-08-16 — Layer C started: `RHTower/Matveev/PerturbedFrequency.lean`.

  The corpus's qualitative proof normalizes through `Relation.pivot_log_eq`, which divides by the
  pivot coefficient and therefore lands in the coefficient number field.  For the effective theorem
  that division is unnecessary and the perturbation is *exact*:

  ```text
  b_pivot · ℓ(m) = Σ_{i ≠ pivot} (b_pivot m_i − m_pivot b_i) log p_i  +  m_pivot · Λ,
  ```

  `pivot_mul_primeLogForm`.  The direction coefficients `perturbedDirection` are **integers**, so no
  denominator, no coefficient field, and no house/height bookkeeping enters at this step — the whole
  error is the single explicit term `m_pivot Λ`.  This is a genuine simplification over the
  qualitative skeleton and should be carried through the auxiliary construction.

  Two further Layer-C facts, both specific to *rational* primes and both what makes the terminal
  step elementary here:

  ```text
  exp_nsmul_primeLogForm     exp(s·ℓ(m)) = ∏ pᵢ^{s mᵢ}, a positive rational integer
  abs_primeLogForm_le_of_box |ℓ(m)| ≤ L·Σ log pᵢ on an exponent box of width L
  ```

  At a nonnegative integer sample the auxiliary exponential polynomial therefore takes values that
  are integer combinations of `S`-units; the classical "a nonzero algebraic integer has house ≥ 1"
  step becomes "a nonzero rational integer has absolute value ≥ 1".

  All three audit to `[propext, Classical.choice, Quot.sound]`.
- 2026-08-16 — Layer C, the perturbation mechanism, closed.

  ```text
  RHTower/Matveev/PerturbedPower.lean
    abs_pow_sub_pow_le                          |xⁿ − yⁿ| ≤ n Mⁿ⁻¹ |x − y| from geom_sum₂_mul
    directionForm                               Σ_{i≠pivot} (b_pivot mᵢ − m_pivot bᵢ) log pᵢ
    pivot_mul_primeLogForm_eq_directionForm_add b_pivot ℓ(m) = D(m) + m_pivot Λ
    abs_pivotFrequency_pow_sub_directionForm_pow_le
                                                |(b_pivot ℓ(m))^k − D(m)^k| ≤ k M^{k−1}|m_pivot||Λ|

  RHTower/Matveev/PerturbedKernel.lean
    abs_perturbedSum_le                         the approximate kernel estimate
    perturbedSum_eq_zero_of_form_eq_zero        the exact case is Λ = 0
  ```

  **The whole perturbation is one residue.**  Where the qualitative proof concludes that the
  auxiliary kernel annihilates each normalized derivative exactly, the effective construction gets

  ```text
  | Σ_m η_m (b_pivot ω_m)^k e^{ω_m s} |  ≤  k M^{k−1} |Λ| · Σ_m |η_m| |m_pivot| e^{ω_m s},
  ```

  and `perturbedSum_eq_zero_of_form_eq_zero` checks that this specialises back to the exact
  statement when `Λ = 0` — so the mechanism is a genuine deformation of the corpus argument, not a
  parallel one.  Note there is no coefficient field anywhere: the direction coefficients are
  integers and the sample weights are `S`-units.

  What Layer C still owes: the auxiliary matrix over `ℤ` (rows indexed by sample and multi-index),
  its Siegel-lemma kernel, and the multinomial passage from "each component box is killed" to "the
  normalized derivative is killed", mirroring `BakerProof.AuxiliaryComponents` but over `ℤ`.

  All new declarations audit to `[propext, Classical.choice, Quot.sound]`.
- 2026-08-16 — Layer C closed.

  ```text
  RHTower/Matveev/PerturbedComponents.lean
    componentSum                       the component box at a multi-index of directions
    directionForm_pow_sum_eq           the multinomial shift law
    directionForm_pow_sum_eq_zero      killing every box of total degree k kills the k-th power
    abs_pivotFrequencySum_le_of_components

  RHTower/Matveev/AuxiliaryMatrix.lean
    BoxIndex, RowIndex, boxExponent, boxNat, auxEntry, auxMatrix
    exists_auxKernel                   Siegel's lemma over ℤ, with the height bound
    sampleWeight, sampleWeight_nonneg
    componentSum_eq_zero_of_auxKernel  a kernel vector kills every box inside the row range
    abs_auxFrequencySum_le_of_kernel   **Layer C capstone**
  ```

  **The whole auxiliary construction is integral.**  Because the primes are rational, the direction
  coefficients `b_pivot mᵢ − m_pivot bᵢ` are integers and the sample weights `∏ pⱼ^{mⱼ s}` are
  `S`-units, so the auxiliary matrix has entries in `ℤ` and mathlib's Siegel lemma applies directly.
  The corpus's qualitative proof needs a coefficient number field, its ring of integers, and house
  estimates at this step; none of that appears here.

  The capstone reads

  ```text
  | Σ_m η_m (b_pivot ω_m)^k e^{ω_m s} | ≤ k M^{k−1} |Λ| · Σ_m |η_m| |m_pivot| e^{ω_m s}
  ```

  for every sample `s` and every derivative order `k < T`, from a single Siegel kernel vector.  With
  `Λ = 0` it is the classical exact annihilation.

  Layer D next: the extrapolation, which must carry this residue through the Schwarz-lemma step and
  choose the parameter budget `L, S, T` as a function of the height `B`.

  All new declarations audit to `[propext, Classical.choice, Quot.sound]`.
- 2026-08-16 — Layer D, analytic half closed; Layer D, parameter half re-scoped.

  ```text
  HTGeometry/ApproximateMultipointSchwarz.lean
    norm_le_of_forall_norm_iteratedDeriv_le      small derivatives ⟹ small on a whole disc
    nodePoly, norm_nodePoly, pow_le_norm_nodePoly, nodePoly_ne_zero
    approximate_multipoint_schwarz               the punctured-disc maximum principle
    norm_le_of_forall_norm_iteratedDeriv_le_multipoint   the assembled extrapolation bound
  ```

  This is Baker's extrapolation lemma **without the exact-vanishing hypothesis**.  The corpus's
  `multipoint_schwarz_bound` divides by the node polynomial globally, which needs the analytic order
  at each node to be at least `q`; in the effective construction the derivatives at the nodes are
  only small, so no such factorisation exists.  Two maximum-principle steps replace it:

  ```text
  Cauchy at a node   |f| ≤ ε e^ρ + M (ρ/r)^q / (1 − ρ/r)     on the disc of radius ρ
  punctured disc     |f(z)| ρ^{q·#nodes} ≤ max(ε_loc, M ρ^{q·#nodes}/D) · |Ω(z)|
  ```

  the second by applying the maximum modulus principle to `f · ρ^{q·#nodes} / Ω` on
  `B(0,R) ∖ ⋃ B(c,ρ)`, where `Ω` is zero-free.  No Hermite interpolant is constructed and no
  separation hypothesis on the nodes is needed: every limit point of the punctured domain is
  automatically `ρ`-far from every node.  Setting `ε = 0` recovers the classical statement.
  All four declarations audit to `[propext, Classical.choice, Quot.sound]`.

  **The parameter half needs different mathematics than the corpus's qualitative family.**  Write
  `L` for the exponent box width, `S₀` the initial sample count, `T₀` the multiindex cutoff, `K` the
  per-step range multiplier, `J` the number of extrapolation steps, `θ = rows/(cols − rows)` the
  Siegel exponent, `W = Σ log pᵢ`.  The effective construction must satisfy

  ```text
  (i)   S₀ · log(T₀/(2eLWK)) ≳ θ log B        Schwarz gain beats the coefficient height
  (ii)  θ T₀ ≲ C                              ‖η‖ ≤ B^C, forced by the integrality step
  (iii) T₀ ≳ 2^{J+1} e L W K                  per-step Schwarz feasibility
  (iv)  S₀ T₀^{d−1} ≍ θ L^d                   Siegel at ratio θ
  (v)   (K/2^{d−1})^J ≳ 1/θ                   terminal (sample × shift) count exceeds the columns
  (vi)  T₀ S₀ (K/2)^J log(2 S₀ K^{J+1}) ≲ C log B    amplification of the residue
  ```

  Eliminating `L`, `S₀`, `θ`, `K`, `J` between (i), (iv), (v) and (vi) gives
  `C·log T₀ > C·log(T₀/(2eLWK)) ≳ T₀ log 2`, so `T₀` is bounded in terms of `C` alone; (iii) then
  bounds `L`, `K`, `J`, (v) bounds `θ` from below, (iv) bounds `S₀`, and (i) collapses to
  `O_C(1) ≳ θ log B`.  **No parameter choice satisfies all six.**

  The binding constraint is (ii).  The auxiliary matrix entries carry `∏|δᵢ|^{νᵢ}` with
  `|δᵢ| ≤ 2LB` and `|ν| ≤ T₀`, so `log max|A| ≥ T₀ log B`; the residue estimate is proportional to
  `‖η‖`, so the terminal "nonzero rational integer has absolute value ≥ 1" step cannot tolerate
  `‖η‖ > B^C`.  Checking the corpus family against (ii): with Baker's own exponents
  (`L ≈ h^{2−1/(4n)}`, `S₀ ≈ h`, `T₀ ≈ h²`, columns `≈ h^{2n−1/4}`, rows `≈ h^{2n−1}`) one gets
  `θ ≈ h^{−3/4}` and `θT₀ ≈ h^{5/4} → ∞`, so it violates (ii) too.

  This is consistent with the historical record and is not a defect of the present formalisation:
  Baker's 1966–68 quantitative theorem gives only `|Λ| > exp(−(log B)^κ)` with `κ > 1`, and the
  polynomial form `|Λ| > B^{−C}` first appears in *A sharpening of the bounds for linear forms in
  logarithms* I–III (1972–75), whose new ingredient is **Fel'dman's polynomials**
  `Δ(z;k) = (z+1)(z+2)⋯(z+k)/k!` in place of plain multiplicities.  They take integer values at
  integers, so they add vanishing conditions without multiplying the entry heights by `B^{T₀}` —
  exactly the blow-up that constraint (ii) forbids.

  `exp(−(log B)^κ)` is **not** enough for the consumer card: `τ₀(ν) ≤ C log(2+|ν|₁)` requires the
  polynomial form, and `(log(2+|ν|₁))^κ` with `κ > 1` leaves `T_log(a) = ∞`.  So the sharpening is
  mandatory, not an optimisation.

  Layer D therefore splits:

  - **D.1 analytic extrapolation with error** — closed, above.
  - **D.2 Fel'dman-polynomial auxiliary construction** — open.  Rebuild
    `RHTower/Matveev/AuxiliaryMatrix.lean` over the basis `∏ᵢ Δ(δᵢ(m); κᵢ)` instead of
    `∏ᵢ δᵢ(m)^{νᵢ}`, re-derive the multinomial shift law of `PerturbedComponents.lean` in that
    basis, and re-run the constraint system with the improved entry height.
