# Effective Baker–Matveev: a polynomial lower bound for linear forms in prime logarithms

- **ID:** `effective-baker-matveev-linear-forms`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — formalization of a classical deep theorem
- **Statement:** For distinct primes `p₁,…,p_d` there are `c, C > 0` with
  `|Σᵢ νᵢ log pᵢ| ≥ c (2+|ν|₁)^{-C}` for every nonzero `ν ∈ ℤ^d`.

## Goal

`suzuki-log-recurrence-polynomial-carrier-trichotomy` cites this as its `(5)` (Literature; not part
of its Lean target, which is closed without it):

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
      basis and height gain closed — `RHTower/Matveev/FeldmanBinomial.lean`;
      the matrix and shift law over the new basis remain
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
- 2026-08-16 — Layer D.2 started: the Fel'dman basis.

  ```text
  RHTower/Matveev/FeldmanBinomial.lean
    consecutiveProd                          ∏_{j<k} (z + j + 1)
    consecutiveProd_natCast                  on ℕ it is an ascending factorial
    prod_range_sub_eq_descFactorial          the descending product is a descending factorial
    factorial_dvd_consecutiveProd            **k! divides k consecutive integers, over all of ℤ**
    feldmanBinom, feldmanBinom_mul_factorial Δ(z;k) = (z+1)⋯(z+k)/k!, integral at every integer
    abs_consecutiveProd_le                   |∏| ≤ (|z| + k)^k
    abs_feldmanBinom_mul_factorial_le        **|Δ(z;k)| ≤ (|z| + k)^k / k!**
  ```

  Integrality over the *whole* of `ℤ` is what the construction needs, since the direction
  coefficients `δᵢ(m) = b_pivot mᵢ − m_pivot bᵢ` take both signs.  The proof splits three ways: for
  `z ≥ 0` the product is an ascending factorial; for `−k ≤ z < 0` one factor is zero; for `z < −k`
  it is a signed descending factorial.  Mathlib supplies `factorial_dvd_ascFactorial` and
  `factorial_dvd_descFactorial` for the two nonzero branches.

  **This is the height gain that constraint (ii) of the 2026-08-16 analysis demands.**  In the plain
  basis an entry of multiplicity `k` costs `|δ|^k ≈ (2LB)^k`, so `log max|A| ≥ T log B` and hence
  `θT ≲ C`; in the Fel'dman basis it costs `(|δ| + k)^k / k!`, cheaper by `k! ≈ exp(k log k − k)`.
  The next step is to redo `AuxiliaryMatrix.lean` over the basis `∏ᵢ Δ(δᵢ(m); κᵢ)` and re-derive
  the multinomial shift law of `PerturbedComponents.lean` in it — the Fel'dman polynomials are a
  basis of the integer-valued polynomials, so the shift law becomes a change-of-basis rather than a
  new expansion.
- 2026-08-16 — Layer D.2: the change of basis is proved.

  ```text
  RHTower/Matveev/FeldmanBasis.lean
    consecutivePoly                   the integer polynomial (X+1)⋯(X+k)
    consecutivePoly_monic/_natDegree/_eval
    exists_intCombination             **triangularity**: every integer polynomial of degree ≤ n is an
                                      integer combination of consecutivePoly 0 … consecutivePoly n
    exists_pow_intCombination         X^k in the consecutive-product basis
    exists_pow_intCombination_eval    the value form: z^k = ∑_{j≤k} c_j · consecutiveProd j z
  ```

  **The two bases carry the same conditions.**  A family containing one monic polynomial of each
  degree is a `ℤ`-basis of the integer polynomials — subtracting the right multiple of the top
  member drops the degree — so the passage from the power basis to the Fel'dman basis loses no
  information: a vector killing every Fel'dman box of degree ≤ k kills every power box of degree
  ≤ k and conversely.  What changes is only the size of the matrix entries, which fall by `k!`.

  This is the step the constraint analysis needed.  With the conditions equivalent, the Siegel input
  may be taken in whichever basis has the smaller height, and `log max|A|` drops from `T log(2LB)` to
  `T log(2LB + T) − log T!`.

  What Layer D.2 still owes: rewriting `AuxiliaryMatrix.lean` over `∏ᵢ Δ(δᵢ(m); κᵢ)` and re-running
  the constraint system of the 2026-08-16 entry with the improved height, to confirm the six
  conditions become simultaneously satisfiable.
- 2026-08-16 — **Correction to the previous two entries: where the Fel'dman factor belongs.**

  Re-running the constraint system with the improved entry height shows the previous entries
  misplaced the device.  Applying `Δ` to the *direction coefficients* replaces `|δ|^κ` by
  `(|δ| + κ)^κ / κ!`.  In logs,

  ```text
  κ log(|δ| + κ) − log κ!  =  κ log(2LB + κ) − κ log κ + κ + O(log κ),
  ```

  so the saving over `κ log(2LB)` is `κ log κ − κ`, **independent of `B`**.  The binding term of
  constraint (ii) was `θ · T · log B`, and it survives unchanged.  So Fel'dman applied to the
  direction coefficients does not relieve the obstruction, and the sentence "this is the height gain
  that constraint (ii) demands" in the 2026-08-16 D.2 entry is wrong.

  The device's actual role in Baker's sharpening is on the **sample variable**.  The auxiliary
  function carries `Δ(z; λ₀)` in place of `z^{λ₀}`, so an entry at an integer sample `s ≤ S` is a
  binomial coefficient

  ```text
  Δ(s; λ₀) = C(s + λ₀, λ₀) ≤ 2^{s + λ₀},
  ```

  and `L₀ log S` in the height becomes `(S + L₀) log 2`.  That *is* one of the binding constraints of
  the polynomial-factor analysis recorded on 2026-08-16 — there the conditions `L₀ log S ≲ C log B`
  and `L₀ log R ≲ (Schwarz gain)` were what forced `L₀` down.

  The two modules built remain exactly the right objects — `feldmanBinom` is the binomial value and
  `FeldmanBasis` is the change of basis — but they are to be applied to the sample variable, not the
  direction coefficients.  D.2's remaining work is therefore:

  1. rebuild the auxiliary function with the polynomial factor `Δ(z; λ₀)` and derive its derivative
     structure (the analogue of `(λ₀)_j z^{λ₀−j}` for the binomial basis);
  2. re-run the six constraints with `L₀ log S` replaced by `(S + L₀) log 2` and check whether they
     become simultaneously satisfiable.

  Step 2 is the decisive check and has **not** been performed; until it is, the polynomial bound
  remains open, not merely unformalised.
- 2026-08-16 — the D.2 constraint check, performed: **it does not close as set up**, and the
  obstruction is sharp.

  With the Fel'dman factor on the sample variable the auxiliary function is

  ```text
  Φ(z) = Σ_{λ₀ ≤ L₀} Σ_{m ∈ [0,L]^d} η(λ₀, m) Δ(z; λ₀) e^{ω_m z},
  ```

  and the conditions at integer samples involve the derivatives `Δ^{(j)}(s; λ₀)`.  Two facts collide.

  1. **The gain is real at the level of values.**  `Δ(s; λ₀) = C(s + λ₀, λ₀) ≤ 2^{s + λ₀}`
     (`feldmanBinom_natCast`, `feldmanBinom_natCast_le`), so `L₀ log S` in the height becomes
     `(S + L₀) log 2`.  Writing `Δ(z; k) = P_k(z)/k!` with `P_k ∈ ℤ[z]` monic of degree `k`, the
     Hasse derivative `P_k^{[j]}` is again an integer polynomial, and
     `|Δ^{(j)}(s; λ₀)/j!| ≤ 2^{λ₀}(S + λ₀)^{λ₀ − j}/λ₀!` — still a saving of `λ₀!`.

  2. **Integrality is lost under differentiation.**  `Δ(z; k)` is integer-valued but
     `Δ^{(j)}(z; k)` is not: the denominator `k!` survives, and it depends on the *column* index
     `λ₀`, not the row.  Row scaling cannot clear it.  Clearing it by the uniform factor `L₀!`
     restores integrality but reintroduces `log L₀!  ≈ L₀ log L₀` into the entry height — exactly
     the term the device was introduced to remove.

  So the naive substitution "powers of the sample variable → Fel'dman polynomials of the sample
  variable" does not by itself close the constraint system.  The resolution direction, and the next
  thing to settle, is that the conditions must be imposed through an operator that preserves
  integer-valuedness — finite differences rather than derivatives, or a divided-derivative scheme in
  which the compensating factorial is absorbed by the *column* normalisation of `η` rather than by
  the matrix.  Until that is settled the polynomial bound `|Λ| ≥ c B^{−C}` remains open at the level
  of the construction, not merely unformalised.

  Recording this as the current frontier of the card: the two Fel'dman modules stand, the placement
  is now correct, and the open point is the differentiation scheme.
- 2026-08-16 — **Retraction: the "obstruction" of the earlier entries is not established.**

  The elimination recorded on 2026-08-16 concluded that no parameter choice satisfies the six
  constraints, and hence that the plain-power construction cannot reach `|Λ| ≥ cB^{−C}`.  That
  derivation implicitly held the extrapolation data `K` (per-step range multiplier) and `J` (number
  of steps) at `O(1)`.  They are not.

  **The condition-count multiplier of the iteration is superpolynomial.**  Over `J` steps the
  samples multiply by `K^J` and the multiplicity halves each time, so the count multiplies by
  `(K/2^{d−1})^J`, subject only to per-step Schwarz feasibility `T₀/2^{J+1} > eLWK`, i.e.
  `2^{J+1}K < A` with `A := T₀/(eLW)`.  Optimising `J`,

  ```text
  count multiplier  ≤  2^{(log₂ A − d)² / 4},
  ```

  attained near `J = (log₂A − d)/2`.  This is superpolynomial in `A`, so the Siegel exponent
  `θ ≈ (initial count)/(unknowns)` can be made *superpolynomially small* whenever `T₀ ≫ eLW` — and
  `θ` is exactly the factor multiplying the harmful `T₀ log B` in `log‖η‖`.  The earlier conclusion
  `θT₀ ≲ C ⟹ T₀ = O(C)` therefore does not follow.

  What survives from the earlier analysis, and is worth keeping, is the identification of the exact
  quantity that must be controlled:

  ```text
  θ · T₀ · log B  ≲  C log B,        θ ≈ (S₀ ρ(T₀)) / L^d,
  ```

  together with the competing pressures: per-step feasibility ties `T₀` to `L` from below
  (`T₀ ≳ eLWK`), the entry height in the divided-power basis is `T₀ log(2eLB/T₀) + dLS₀ log P`, and
  the terminal count must reach the number of unknowns after the multiplier is applied.  Whether
  these close simultaneously is a genuine optimisation that I have **not** settled; it is the open
  point of the card.

  External check (July 2026 literature): Fel'dman's device is confirmed to be *binomial polynomials*
  in the auxiliary function, with the mechanism described as "avoiding certain factorials" — which is
  the divided-power reading `δ^μ/μ!` used above, and matches the two modules already built.  So the
  objects are right; what is missing is the parameter balance, not the basis.
- 2026-08-30 — **the clash located exactly, and the terminal step re-identified.**

  Re-running the elimination with `K` and `J` free (as the retraction demands) isolates *three*
  conditions that cannot hold together in the present univariate scheme, and the clash is sharp.

  Write `h = log B`, `θ = R/(N−R)` with `R = S·#{ν : |ν| < T}` the row count and `N = (L+1)^d` the
  column count, `W = Σ log pᵢ`.

  ```text
  (ii)   θ·T = O(1)             coefficient height:  log‖η‖ ≍ θ(T log(2LB) + dLS log P) = O(h)
  (iii)  T / 2^J > c·L·K        per-step Schwarz feasibility at the LAST step
  (v)    (K/2^{d−1})^J ≳ 1/θ    the terminal count must reach the number of columns
  ```

  Condition (ii) is forced by the entry height: the matrix entries carry `∏ᵢ δᵢ(m)^{νᵢ}` with
  `δᵢ(m) = b_d mᵢ − m_d bᵢ`, so `log max|A| ≥ T log B`, and *no rescaling removes it* — writing the
  directions as `mᵢ − m_d βᵢ` with `βᵢ = bᵢ/b_d ∈ [−1,1]` makes the entries rational with denominator
  `b_d^{|ν|}`, and clearing that denominator (for Siegel over `ℤ`, or in the terminal
  "nonzero rational ≥ 1/denominator" step) restores exactly the same `T log B`.  Fel'dman's binomials
  applied to `δ` save `T log T`, which is independent of `B`, so they do not touch (ii); the
  2026-08-16 correction stands.

  Now eliminate.  (ii) with `θ ≍ S T^{d−1}/L^d` reads `S (T/L)^d = O(1)`, so `T = O(L)` and
  `S = O(1)`.  Feeding `T = O(L)` into (iii) gives `2^J K = O(1)`, hence `J = O(1)` and `K = O(1)`,
  hence `(K/2^{d−1})^J = O(1)`; but (v) then forces `θ = Ω(1)`, and with `θ ≍ S T^{d−1}/L^d = Ω(1)`
  and `S = O(1)` we get `L^d = O(T^{d−1})`, i.e. `L = O(1)` and `T = O(1)`.  With every parameter
  bounded the Schwarz gain `(T/2)·S·log(T/(4eLWK))` is `O(1)`, while the coefficient height is
  `≍ θ T h ≍ h`.  **No parameter choice closes the system.**  (This is an order-of-magnitude
  elimination; the constants are not tracked, and only the orders matter for the conclusion.)

  **Where the load is.**  Two hypotheses carry that elimination, and they must be separated.

  1. *"The multiplicity halves at every extrapolation step"* — this is what turns (iii) into
     `T ≳ 2^J L K`.  It is **not** forced by the analysis.  The Cauchy step
     `|Φ^{(k)}(s')| ≤ k! r^{−k} sup_{|z−s'|=r}|Φ|` is free once `T > eLW`: optimising `r = k/(LW)`
     turns the factor `k! r^{−k}` into `exp(−k log(k/(eLW)))`, a *gain* rather than a cost, and
     `T > eLW` is already implied by the per-step feasibility.  In the classical proof the halving
     pays for something else: there the value `b_d^k Φ^{(k)}(s')` is an algebraic number whose house
     grows like `B^k`, so the arithmetic threshold costs `k log B` per step and one shrinks `k`.
     Dropping the halving turns (iii) into the `J`-free `T > cLK` and the counting part of the
     system closes:

     ```text
     L ≍ h,  T ≍ cKL,  S = O(1),  K = O(1),  θ ≍ 1/L ≍ 1/h,  θT = O(1),
     log‖η‖ ≍ θ(Th + LS log P) ≍ h,   gain₀ ≍ T ≍ h,   K^J ≳ 1/θ ≍ h  ⟹  J ≍ log h.
     ```

  2. *The per-step arithmetic threshold.*  This is the part that does **not** close, and it is the
     real obstruction.  At every step the conclusion "the integer `C_ν(s')` is smaller than one, hence
     zero" must beat the analytic size of the component function

     ```text
     F_ν(z) = Σ_m η_m ∏ᵢ δᵢ(m)^{νᵢ} e^{ω_m z},     sup_{|z|≤r} |F_ν| ≤ ‖η‖·N·(2LB)^T·e^{LWr},
     ```

     whose `(2LB)^T` contributes `T log B` — the same term as in (ii), now appearing *additively at
     every step* rather than multiplied by `θ`.  Normalising the directions to `δᵢ/b_d ∈ [−2L,2L]`
     removes it from the analytic size but reinstates it in the threshold, because the value is then
     a rational with denominator `b_d^{|ν|}` and "nonzero ⟹ `≥ b_d^{−T}`" costs exactly `T log B`
     again.  Requiring `gain₀ ≍ T S log(T/(eLWK)) ≳ T log B` forces `S·log(T/(eLWK)) ≳ h`, and both
     ways of meeting it (`S ≍ h`, or `T ≳ B·LWK`) violate `θT = O(1)` or the feasibility
     `T > eLWK`.

  **Status of the card's open point.**  The obstruction is now located precisely: it is not the
  Siegel exponent, not the extrapolation multiplier, and not Fel'dman's basis, but the fact that the
  quantity `T log B` is charged *once per extrapolation step* by the arithmetic threshold.  Any
  route to `|Λ| ≥ c B^{−C}` must make that charge appear only `O(1)` times, or make the gain of a
  single step already of size `T log B`.  The two candidate mechanisms to reconstruct, in order:

  1. **A single long extrapolation instead of an iteration** — one step whose gain is
     `T·S·log(R'/S)` with `R'` exponentially large, so that a single arithmetic threshold of size
     `T log B` is paid.  The cost is `LWR'`, so this needs `T S log(R'/S) > LWR' + T log B` with
     `R' ≈ B`, i.e. `T S h > LWB`: impossible with `L ≥ 1` unless the analytic growth `e^{LWR'}` is
     itself controlled by the vanishing, which is what the node polynomial already does.  Needs a
     careful redo with the node polynomial kept, not bounded away.
  2. **Reconstruct Baker's *Sharpening I–III* parameter table directly** and check which of (ii),
     (iii), (v) it violates in this integral setting — the historical record says the polynomial
     bound is reached there, so the table is an existence proof that some assignment works, and the
     discrepancy with the elimination above will pinpoint the missing device.

  The two Fel'dman modules stand and are still the right objects; the change of basis
  (`FeldmanBasis.exists_pow_intCombination_eval`) will be needed whichever route closes, since it is
  what lets the conditions be imposed in the cheaper basis.  **Until one of the two routes above is
  settled, the polynomial bound remains open at the level of the construction, not merely
  unformalised.**  The `exp(−(log B)^κ)` bound, by contrast, *is* reachable with the parameters
  `J ≍ log h`, `K ≍ 2^{d(d−1)}`, `L ≍ h^d/log h`, `T ≍ 2^J L K`, and would be worth banking as an
  intermediate Lean theorem: it is the historically correct 1966–68 statement, and every layer
  built for it is reused by the sharpening.
- 2026-09-29 — **Parameter analysis of the ℤ-point schemes; a closure argument for why they all
  fail.**

  1. *Derivatives in the frequency directions must be bounded in number.*  Every derivative in a
     `γ`-direction carries the denominator `b_pivot`, so the approximate-value error is
     `≍ (2LB)^T |Λ|`.  A polynomial bound therefore needs `T = O(1)`, independent of `B`.  All of
     `log B` must enter through a polynomial degree `L₀ ≍ log B` and the point count.
  2. *With the polynomial part on the extrapolation variable, the Fel'dman derivatives are too
     expensive.*  `lcm(1..L₀)^j Δ^{(j)}(s; L₀)/j! ∈ ℤ` costs `≍ L₀` per derivative order.  The gain
     per derivative order is the point count `S`.  Hence `S ≳ L₀`, and the Siegel count
     `S T^n ≍ L₀ L^n` forces `L ≳ T`.  Per-step exponential feasibility on integer points spaced
     by `1` forces `T ≳ 12e·L·W·K·2^J`.  The two are incompatible for every choice of constants.
  3. *Monomials `z^{λ₀}` avoid the derivative denominators but cost `L₀ log S` in the values.*
     This gives `exp(-C log B log log B)`, the pre-Fel'dman bound.
  4. *A separate grid variable for the polynomial part decouples.*  The Pascal matrix
     `(binom(s+k,k))` is unimodular, so the problem splits into independent exponential problems.

  **Consequence.**  A polynomial bound needs points of spacing `< 1`, which removes constraint 2's
  exponential feasibility, i.e. Baker's Kummer descent at `ℓ/p^J`.  It also needs an arithmetic
  step that does not pay the Kummer degree `p^{Jn}` in Liouville's inequality.

  Sources checked:
  - Waldschmidt's Madras notes (LIL.pdf, free) reach only `exp(-C(log B)^2 log A…)` without
    derivatives (Thm 10.1).
  - Soundararajan's Stanford notes reach `exp(-(log V)^κ)`, `κ > 2`, for two logs.
  - Baker's book (Ch. 3, 1975) is access-restricted.

  The next step is to obtain the 1972 *Sharpening I* construction, or Waldschmidt's book §9 ("The
  rational case: Fel'dman's polynomials") with its Philippon multiplicity estimate.
- 2026-09-29 (later) — **Source found: Fel'dman 1968, Mat. Sb. 77(119):3, 423–436 (mathnet sm4063,
  free).**  It proves the polynomial bound; its Theorem 2 is our exact case (`S`-units over fixed
  primes).  The device that my analysis above was missing:

  - **Shifts, not degrees.**  The unknowns are `C(k, l)`, `k < N+1`, `l ∈ [0,q)^m`, attached to
    `g(z+k) e^{ω_l z}` with one fixed product `g(z) = ∏_{i=1}^{N}(z+i)`.  The shifts are linearly
    independent (Fel'dman, Lemma 6), so they span polynomials of degree `≤ N`.
  - **One common divisor for all derivatives (Lemma 5).**  `g^{(σ)}(y)/σ!` is a sum of products with
    `σ` brackets deleted.  All such products, for `σ ≤ s` and every block of `N` consecutive
    integers, are divisible by
    `D = ∏_{p^a ≤ N} p^{(⌊N/p^a⌋ − s)_+}`, where
    `log D ≥ log N! − N(c₁ + c₂ log(s+1))` using only Chebyshev `ψ(y) ≤ c y`.
    The derivative denominators are paid once, at cost `O(N log s)`, not `N` per derivative order.

  **Parameters.**  `q`, `S` (derivative order), `K`, `R` (number of steps) are constants.  The
  polynomial degree `N = c_N log B` and the initial point count `X₀ = c_X log B`.
  - Siegel: `X₀ S^m ≤ (N+1) q^m / 2`.
  - Step `r`: orders `S/2^r`, points `K^r X₀`.
  - Exponential feasibility: `S/2^{R+1} ≳ 16 q W K`.
  - Arithmetic: `c_X S/2^{R+2} ≳ 2S + c_N(C'' + c₂ log S + R log K)`.
  - Terminal: `K^R X₀ ≥ (N+1) q^m`.

  All of these are satisfiable: first `q^m ≍ 2^R S^{m−1}·polylog S`, then `S^{1/m} ≳ 2^{R(1+1/m)} W K·polylog`,
  `K = 2^{m²+m+1}`, and `R` large.  Every loss is `O(log B)`, hence `|Λ| ≥ B^{−C}`.

  **Lossless approximate Schwarz step (new; the corpus version loses `ρ^{−MT}`).**
  - Let `H = Σ_x P_x Ω_x S_x`, where `P_x` is the Taylor polynomial of `f` at node `x`, `Ω_x = ∏_{y≠x}(z−y)^M`,
    and `S_x` is the Taylor polynomial of `1/Ω_x` at `x`.
  - Then `f − H` vanishes to order `M` at every node, so `f = H + Ω G` with `G` entire.
  - The maximum principle bounds `G`, and `|H| ≤ ε·e^{O(MT log K + KT)}` for integer nodes.

  **Lean plan (in order).**
  (L1) divisor lemma; (L2) Siegel system; (L3) the functions `F_{σ,τ}` with the diagonal derivative
  identity `F' = F_{σ+1,τ} + Σ ℓ_j F_{σ,τ+e_j}`; (L4) integer proxy `A_{σ,τ}(x)` and the `Λ`-error;
  (L5) lossless Hermite–Schwarz lemma; (L6) extrapolation induction; (L7) terminal generalized
  Vandermonde; (L8) parameters and the card interface.
