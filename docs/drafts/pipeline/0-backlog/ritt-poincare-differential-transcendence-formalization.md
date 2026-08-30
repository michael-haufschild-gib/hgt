# Ritt's theorem on Poincaré functions, in Lean

- **ID:** `ritt-poincare-differential-transcendence-formalization`
- **Stage:** 0-backlog
- **Type:** THEOREM (Lean) — a formalization project for a classical theorem, not new mathematics
- **Source:** the shared blocker of the last three cards in
  `2-fully-proven/not_new_scientific_knowledge/04-rg-stochastic-quantum-fields`
- **Statement:** If the Poincaré function `σ` of a rational map `R` of degree at least two at a
  repelling fixed point (`σ(λz) = R(σ z)`, `σ 0 = 0`, `σ' 0 = 1`, `|λ| > 1`) is differentially
  algebraic over `ℂ(z)`, then there are integers `r ≠ 0`, `j` and a nonzero rational `A` with
  `(σ')^r = a z^j A(σ)`.

## Goal

This single implication is what stops `exact-rational-rg-generation-dichotomy`,
`gadc-tree-population-rg-clock-hypertranscendence` and
`noisy-binary-tree-channel-rg-clock-hypertranscendence` from reaching stage 3.  Everything else on
those cards is already unconditional Lean, so proving it closes three cards at once and, more
generally, unlocks every hypertranscendence statement in the corpus that currently cites
Becker–Bergweiler or Ritt.

## What the corpus already owns (do not rebuild)

| Piece | Where |
|---|---|
| Koenigs linearizer, Poincaré germ | `HTGeometry/PoincareFunctionGerm.lean` |
| `Φ` DA `⇔` `κ` DA `⇔` `β` DA | `HTGeometry/RittDichotomy.lean` — `differentiallyAlgebraicOn_poincare_iff_rgBeta` |
| the order-one relation is an ADE (`(4) ⇒ (1)`) | `differentiallyAlgebraicOn_of_rittForm` |
| the cocycle equivalence `(4) ⇔ (5)`, both directions | `HTGeometry/RittCocycle.lean` |
| scaling rigidity behind `(5) ⇒ (4)` | `HTGeometry/ScalingGermRigidity.lean` |
| the positive branch (power family) | `HTGeometry/PowerMapPoincareDA.lean` |
| the negative branch (infinite-divisor obstruction) | `HTGeometry/CocycleDivisorObstruction.lean` |
| coherence of a linearized tower from DA | `HTGeometry/RGTowerCoherence.lean` |

Only `(1) ⇒ (4)` is missing.

## Scope note

`ritt-algebraicity-load-bearing.md` (same folder) fixes the *boundary* of the theorem: it cannot be
extended by replacing the rational base map with an arbitrary differentially algebraic germ.  That
card constrains generalisations; this one is the formalization of the rational statement itself, and
the rational hypothesis is exactly what the two proof routes below use.

## Approach

Two known proofs, neither of whose foundations exist in mathlib.

1. **Value distribution (Bergweiler, Becker–Bergweiler).**  Needs the second main theorem for
   *meromorphic* functions with the `S(r,f)` error term, plus complex-dynamics input (density of
   repelling periodic points) and a normal-families argument.  Corpus status as of 2026-08-30: the
   chain `SecondMainTheoremChain.mul_characteristic_le_sum_logCounting_add_proximity` and
   `SecondMainTheoremEntire.exists_mul_characteristic_le_of_separated_entire` still carry the
   proximity terms explicitly and are stated for *entire* `f`; the logarithmic-derivative estimate
   exists only in the small-growth form
   (`SmallGrowthDerivative.smallGrowth_proximity_logDeriv_isLittleO`).  A Poincaré function is
   meromorphic of finite order but not small growth, so the input is not yet in usable shape.
   **Coordination:** the final `m(r, f'/(f−a)) = S(r,f)` assembly is owned by
   `2-fully-proven/new_scientific_knowledge/universal-first-order-entire-cascade-unit-cost.md`.
   Do not duplicate it; build the finite-order layer on top once it lands.
2. **Parametrized Picard–Vessiot (Di Vizio–Fernandes).**  A Galoisian proof for the `q`-difference
   equation `σ(λz) = R(σ z)`.  mathlib has no Picard–Vessiot theory at all, so this route means
   building differential Galois theory first.

A third, cheaper attack is not available: the elementary divisor argument runs in the `(5)` direction
only, and the transcendence-degree / ultraproduct machinery built for the incoherence card gives
coherence *from* differential algebraicity, never the converse.

## Gates

- [ ] 0 → 1  in-progress: route chosen; the missing analytic input stated as a precise Lean signature
- [ ] 1 → 2  fully-proven: complete paper proof of `(1) ⇒ (4)` written out at formalization grain
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, axioms `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready: not applicable — classical theorem, formalization only

## Log
- 2026-08-30 — created in 0-backlog.  Extracted as the single shared blocker of the last three
  `04-rg-stochastic-quantum-fields` cards after the whole differential-algebra layer around it was
  formalized; see those cards' Lean-status sections and
  `HTGeometry/{RittDichotomy,RittCocycle,ScalingGermRigidity,PowerMapPoincareDA,CocycleDivisorObstruction}.lean`.

## Route fixed and half built (2026-08-30)

The proof to formalize is **Di Vizio–Fernandes, arXiv:2102.08268**, Theorem 4.2, not Ritt's original
elimination argument and not Becker–Bergweiler's Nevanlinna reduction.  For `τ` with
`τ(R(x)) = q·τ(x)`, `q` not a root of unity:

1. `τ` differentially algebraic over `C(x)` ⟺ 2. `τ` satisfies an order-one algebraic differential
equation ⟺ 3. `(τ′)^r = A(x)·τ^j` with `r ≠ 0`, `A ∈ C(x)`.

Their Galois theory is inessential; both Galois inputs are elementary rigidity statements.  The
abstract carrier is `HTGeometry/RittFirstOrderForm.lean`'s

```text
structure RittFrame K L :=
  σ : L →+* L, ψ : K →+* K, d : L → L, dK : K → K, ρ : K
  σ ∘ algebraMap = algebraMap ∘ ψ,  σ-invariants of L come from K,
  d additive and Leibniz, d ∘ algebraMap = algebraMap ∘ dK,  ρ ≠ 0,
  d (σ x) = ρ · σ (d x)                                   -- the chain rule, ρ = R′
```

### Built, unconditional, `[propext, Classical.choice, Quot.sound]`

| Statement | Name |
|---|---|
| `σ w = w + c`, `w` algebraic over the base ⇒ `w` in the base | `RittShiftRigidity.exists_algebraMap_eq_of_isIntegral_of_shift_add` |
| dependent multiplicative shift coordinates ⇒ integer monomial in the base | `RittShiftRigidity.exists_algebraMap_eq_zpow_prod_of_not_algebraicIndependent` |
| `σ (d τ) = (q/ρ)·d τ` | `RittFrame.sigma_d_eq_of_shift` |
| **(2) ⇒ (3)** | `exists_rittForm_of_not_algebraicIndependent` |
| `σ(d^[n]τ) − (q/ρ^n)·d^[n]τ ∈ span_K{d τ,…,d^[n−1]τ}` (Faà di Bruno) | `RittFrame.shift_jet_sub_mem_jetSpan` |
| collapse: integral top jet ⇒ top jet in the prefix field | `RittJetCollapse.jet_mem_of_isIntegral_of_lower_jets_mem` |
| shift stability of `K(τ,…,τ^{(n−1)})` | `RittFrame.sigma_mem_jetPrefixField` |
| collapse over the prefix field, `n ≥ 2` | `jet_mem_jetPrefixField_of_isAlgebraic` |
| **the alternative**: DA linearizer ⇒ Ritt form **or** `∃ n ≥ 2, d^[n]τ ∈ K(τ,…,d^[n−1]τ)` | `rittForm_or_jet_mem_jetPrefixField` |

The first two reuse the corpus rather than duplicating it: the additive lemma is the endomorphism
version of `AlgebraicPrimitiveDescent.algebraic_additive_primitive_eq_base_add_constant`
(divisibility of the minimal polynomial replaces irreducibility of its image, so `ψ` need not be
surjective), the multiplicative one is the contrapositive of
`MultiplicativeShiftIndependence.algebraicIndependent_of_multiplicativeShift`.

### The single open point

Di Vizio–Fernandes close (1) ⇒ (2) by asserting that `τ^{(n)} ∈ K_n` contradicts minimality of `n`.
**It does not** — Airy's `y″ = xy` has `y_2 ∈ K(y_0,y_1)` with `y_0,y_1` algebraically independent.
The functional equation has to be used.  Setting `s = τ/τ′` (so `σ s = ρ s`, `σ τ = q τ`, and
`τ, s` algebraically independent), the case `n = 2` says the equation

```text
σ W = W + γ·s,     γ = dK ρ / ρ,   W ∈ K(τ, s)
```

has a solution.  Slicing `W` as a coprime fraction in `s` over `K(τ)` forces the denominator to be
an eigenvector, `σ Q = ρ^{deg Q} Q`, and comparing the coefficient of `s^{deg Q + 1}` in the
numerator identity yields `ψ(a)·ρ = a + γ` for `a = ` that coefficient; a second slicing in `τ`
pushes `a` down into `K`.  That is exactly the **rational affine-connection equation**
`a(R)·(R′)² = R′·a − R″` of `HTGeometry/RationalAffineConnection.lean`, which the corpus already
excludes for `z² + 1` and `(z − 1)²`.

So the next brick is the abstract **twisted coboundary slicing lemma**: for `φ : E →+* E`,
`μ ∈ E^×`, and `t` transcendental with `σ t = μ t`, a solution `W ∈ E(t)` of `σ W = W + β t`
produces `a ∈ E` with `φ(a)·μ = a + β`.  After that, `n ≥ 3` — the same place where the corpus's own
free-jet-field lane (`JetSubstitutionDescent`, `JetShiftLevelInduction`) is open in general.

### The slicing lemma is built (2026-08-30, same pass)

- `HTGeometry/RittScalingCoboundaryDescent.lean` — **`exists_shift_solution_of_scaling_cross`**: for
  a coprime pair `P, Q` with `Q` monic satisfying the cross identity of
  `twistComp Φ (C ρ * X) (P/Q) = P/Q + β·X`, there is `a` in the coefficient field with
  `Φ(a)·ρ = a + β`.  Coprimality of `Q` with `P + β·X·Q` gives `Q ∣ Q^Φ∘ρ`, degrees agree, monicity
  pins the scalar to `ρ ^ deg Q`, and the coefficient of `X ^ (deg Q + 1)` is the answer — with no
  case split on `deg P`, since a degree below `deg Q + 1` just reads off `β = 0`.  Reuses the
  corpus's `TwistedScalingDescent` (`twistComp`, `natDegree_twistComp`, `twistComp_ne_zero`,
  `eq_C_mul_of_dvd_of_natDegree_eq`, `coeff_twistComp_scale`, `coeff_eigen_of_twistComp_scale`).
- `HTGeometry/RittScalingSliceTransport.lean` — `aeval_twistComp_scale` (evaluation intertwines the
  shift with the twisted scaling) and **`exists_shift_solution_of_transcendental`**, the same
  statement for a fraction of a transcendental generator inside an ambient field.

What is still missing to run the `n = 2` case end to end: presenting `W = d²τ·τ/(dτ)²` as a coprime
fraction in `s = τ/dτ` over `K(τ)` — i.e. the `IntermediateField.adjoin`-to-`num/denom` step — and
then the second slicing in `τ` over `K`.  Both are instances of
`exists_shift_solution_of_transcendental`; only the presentation of a member of a simple
transcendental extension as a coprime fraction is new plumbing.

### The `n = 2` case of the missing implication is now closed (2026-08-30)

`HTGeometry/RittEigenSliceDescent.lean`, `HTGeometry/RittSecondJetAffineConnection.lean` and
`HTGeometry/RittAffineConnectionBridge.lean` close it, unconditionally:

| Statement | Name |
|---|---|
| inhomogeneous coprime descent over a scaled generator | `exists_shift_solution_of_scaling_cross`, `exists_shift_solution_of_mem_adjoin` |
| eigen-inhomogeneous coprime descent over a scaled generator | `exists_eigen_shift_solution_of_scaling_cross`, `exists_eigen_shift_solution_of_mem_adjoin` |
| `σ (τ / d τ) = ρ · (τ / d τ)` | `RittFrame.sigma_jetRatio` |
| `σ (d²τ) = (q/ρ²)·d²τ + (dK(q/ρ)/ρ)·d τ` | `RittFrame.sigma_second_jet` |
| `σ W = W − (dK ρ/ρ)·(τ/d τ)` for `W = d²τ·τ/(d τ)²` | `RittFrame.sigma_normalizedSecondJet` |
| **`τ` transcendental, `d τ` transcendental over `K⟮τ⟯`, `d²τ ∈ K⟮τ, d τ⟯` ⟹ `∃ a ∈ K, ψ(a)·ρ = a − dK ρ/ρ`** | **`exists_affineConnection_of_secondJet_mem`** |
| that relation *is* `IsAffineConnection R hR a`, i.e. `a(R)·(R′)² = R′·a − R″` | `isAffineConnection_of_ritt_relation` |

So a linearizer whose second jet is rational in the first two forces a rational affine connection on
the map, which `HTGeometry/RationalAffineConnection.lean` forbids for a map with a critical point
whose orbit is infinite in either direction (`no_affine_connection_regular_at_critical`,
`no_pole_of_forward_orbit`, `no_pole_of_backward_orbit`); the corpus discharges this unconditionally
for `z² + 1` and `(z − 1)²`.

What remains of Ritt's implication is therefore exactly the jet orders `n ≥ 3` of
`rittForm_or_jet_mem_jetPrefixField` — the same place where the corpus's own free-jet-field lane
(`JetShiftLevelInduction`, `JetTailTrivial.fixed_isConst`) needs its level-three input.

### Second-order capstone, and the first brick of the `n ≥ 3` descent (2026-08-30)

- **`RittSecondOrderCapstone.exists_affineConnection_of_secondJet_isAlgebraic`** — the whole
  second-order case in one statement: `τ` transcendental over `K`, `d τ` transcendental over `K⟮τ⟯`,
  and `d²τ` merely *algebraic* over `K⟮τ, d τ⟯` already force `∃ a ∈ K, ψ(a)·ρ = a − dK ρ / ρ`, i.e.
  `IsAffineConnection`.  With `rittForm_or_jet_mem_jetPrefixField` this settles Ritt's implication
  for every differentially algebraic linearizer whose minimal algebraic jet order is at most two.
- **`RittTranslationSliceDescent.exists_constant_combination_of_translation_cross`** — the slice for
  the *unipotent* top coordinate that jet orders `n ≥ 3` present, where the shift *translates* the
  generator, `σ t = t + γ`, instead of scaling it.  Coprimality again fixes the denominator exactly
  (`Q^Φ∘(X+γ) = Q`, the substitution being monic), and the second-highest coefficients give the
  uniform conclusion

  ```text
  ∃ u κ λ,  (κ, λ) ≠ (0,0),  Φ κ = κ,  Φ λ = λ,  Φ(u) − u = κ·α + λ·γ
  ```

  with `−deg Q` from a nonconstant denominator, `−deg P` from a numerator of degree at least three,
  `1/leadingCoeff P` paired with `−2` at degree exactly two, and `1` at degree at most one.

What `n ≥ 3` still needs is the *level induction* that feeds this lemma back into itself: the output
`κ·α + λ·γ` is linear in the next unipotent coordinate exactly when `λ ≠ 0`, and the branch `λ = 0`
lands on a `w`-free inhomogeneity whose own descent needs the `α = 0` variant of the same slice.
That bookkeeping is the corpus's open `JetShiftLevelInduction` problem, closed there only for the two
quadratics.

### The `n ≥ 3` descent now runs to the base (2026-08-30)

The jet tower of a linearizer is *affine*, not merely triangular: `σ y_m = (q/ρ^m)·y_m + v_m` with
`v_m` a base combination of the lower jets.  So the right slice is the **eigen slice over an
affinely moved generator**, and above jet order one the eigenvalue `q/ρ^n` is never one, which makes
the *top* coefficient of the numerator identity already informative — no second-highest-coefficient
case analysis is needed.

| Statement | Name |
|---|---|
| `Φ(u)·a^{deg P} = a^{deg Q}·(c·u + ((αX+β)Q)_{deg P})` for a coprime fraction with `σ t = a t + b` | `RittAffineSliceDescent.exists_eigen_relation_of_affine_cross` |
| the residue is `0`, `α` or `β` — never a new element of the bigger field | `RittAffineSliceResidue.exists_eigen_relation_residue_of_affine_cross` |
| the same, for a member of a simple transcendental extension | `exists_eigen_relation_residue_of_affine_mem_adjoin` |
| Faà di Bruno with explicit coefficients: `σ(d^[n]τ) = (q/ρ^n)·d^[n]τ + Σ_{j<n} A_j·d^[j]τ` | `RittTowerDescentStep.exists_shift_jet_coeffs` |
| **one descent step**: an eigen-inhomogeneous relation over the first `m+1` jets descends to one over the first `m`, tracking both the scalar and the coefficients | `exists_descent_step` |
| **the whole descent**: from the top of the tower to the base | `exists_base_relation_of_tower` |
| **the capstone**: a jet lying in the field generated by its predecessors forces `ψ(u) = c·u + g` in the base, `u ≠ 0`, `c ≠ 0`, with `g = 0` or `g` a nonzero base multiple of one of the `A_j` | `RittTowerCapstone.exists_base_relation_of_jet_mem` |

Two facts make the induction close where a naive slicing would not.  The residue of the affine slice
is one of the two given inhomogeneity coefficients, so an inhomogeneity that is a base combination of
the lower jets *stays* one; and the scalar is only ever multiplied by a power of `q/ρ^m`, so it stays
a monomial in `q` and `ρ`.  The bookkeeping is carried explicitly: the descent's output `g` is `0`,
`z·A_m` or `z·g` with `z ≠ 0`, which iterates to "zero or a nonzero base multiple of one of the
original Faà di Bruno coefficients".

For `n = 2` the coefficient is `A_1 = dK(q/ρ)/ρ`, and the relation is the rational affine connection
already excluded by `RationalAffineConnection.lean` for maps with an infinite critical orbit; the
general `n` gives the same shape with the higher coefficients.

What is left to close the cards is therefore no longer structural: it is (i) the end-to-end assembly
that picks the *minimal* collapsing order (so the transcendence hypotheses of the capstone hold),
and (ii) ruling out `ψ(u) = c·u + z·A_j` for the specific maps of these cards, exactly as
`RationalAffineConnection` does for the affine connection.

### End to end: Ritt's implication is now a single frame theorem (2026-08-30)

`HTGeometry/RittMinimalCollapse.lean`:

- `exists_base_relation_of_collapse` — taking the **least** jet order at which the linearizer's jet
  lies in the field generated by its predecessors makes every lower jet transcendental over its own
  prefix field (below order two by the independence of the first two jets, at order two and above
  because the collapse theorem turns "algebraic over the prefix field" into "in it", which
  minimality forbids), so the tower capstone applies at that order.
- **`rittForm_or_base_relation`** — for a differentially algebraic linearizer with independent first
  two jets:

  ```text
  (d τ)^r = A · τ^j  with r ≠ 0, A ≠ 0        -- Ritt's order-one relation
      or
  ψ(u) = c·u + g  in the base, u ≠ 0, c ≠ 0,   -- g = 0, or g = z·A_j with z ≠ 0
  ```

  where the `A_j` are the explicit Faà di Bruno coefficients of `σ (d^[n] τ)` at the collapsing
  order `n ≥ 2`.

Everything on the differential-algebra side of Ritt's implication is therefore Lean, unconditional,
and axiom-clean.  What is left for these cards is purely the *obstruction* side: rule out
`ψ(u) = c·u + z·A_j` for the specific rational maps of the cards — the job
`HTGeometry/RationalAffineConnection.lean` already does for `A_1` (there `ψ(u)·ρ = u − dK ρ/ρ`, the
rational affine connection) via the critical-orbit argument — and instantiate the frame with the
analytic Poincaré germ.

### Reduced to two base obstructions (2026-08-30)

The homogeneous branch of the base relation is *not* a separate case — it **is** Ritt's form.
`HTGeometry/RittHomogeneousBaseRelation.lean`,
**`exists_rittForm_of_homogeneous_base_relation`**: if the base carries `u ≠ 0` with

```text
ψ(u) = q^i · ρ^m · u          (an invariant differential of weight m, eigenvalue q^i)
```

and `(i, m) ≠ (0,0)`, then `(d τ)^r = A · τ^j` with `r ≠ 0`.  The proof is one line of exponent
arithmetic: the element `V = u · (d τ)^m · τ^{−i−m}` is `σ`-invariant, because the shift multiplies
`u` by `q^i ρ^m`, `d τ` by `q/ρ` and `τ` by `q`, and those cancel exactly at those exponents; a
`σ`-invariant of a Ritt frame comes from the base, and rearranging `V = v` is the Ritt relation.
(For `m = 0` the same computation gives `τ^i = u/v`, and its logarithmic derivative is `d τ = A·τ`.)

The descent also tracks the *shape* of its scalar: `c = q^i · ρ^k` throughout, since each step
multiplies it only by a power of `q/ρ^m` (`exists_descent_step` and `exists_base_relation_of_tower`
now carry this).  Combining, `HTGeometry/RittFinalAlternative.lean`,
**`rittForm_or_affineObstruction_or_degenerate`**: a differentially algebraic linearizer with
independent first two jets satisfies

```text
(d τ)^r = A · τ^j                                  -- Ritt's order-one relation
  ∨  ψ(u) = q^i ρ^k u + z · A_p ,  u ≠ 0, z ≠ 0    -- an affine base obstruction
  ∨  ψ(u) = u ,  u ≠ 0                              -- total exponent cancellation
```

So exactly two things stand between the corpus and Ritt's implication, and both are now sharply
stated Lean propositions about the base field alone:

1. **the affine obstruction** — rule out `ψ(u) = q^i ρ^k u + z·A_p` for the map at hand.  For `n = 2`
   this is `a(R)·(R′)² = R′·a − R″`, which `RationalAffineConnection.lean` already forbids for a map
   with a critical point of infinite orbit; the general `A_p` needs the same treatment.
2. **the degenerate branch** — the descent's exponents can in principle cancel to `q^0 ρ^0`, leaving
   `ψ(u) = u`, which says nothing.  Excluding it needs either a finer invariant along the descent or
   the `w`-normalised tower (`w_k = y_k y_0^{k−1}/y_1^k`, eigenvalue exactly one at every level),
   where the scaling slice has no vanishing-residue branch at all.

### Narrowing the degenerate branch (2026-08-30)

At the bottom two levels of the tower the shift acts on the coordinate by a **pure scaling** —
`σ y_0 = q·y_0` and `σ y_1 = (q/ρ)·y_1`, with no lower-order term — so there the twisted substitution
is *diagonal on coefficients* and the eigen-relation forced on the denominator by coprimality is a
relation on every coefficient separately.  `HTGeometry/RittScalingDenominatorEigen.lean`:

| Statement | Name |
|---|---|
| `Q^Φ∘(aX) = a^{deg Q}·Q` | `denominator_eigen_of_scaling_cross` |
| `Φ(Q_j)·a^j = a^{deg Q}·Q_j` for every `j` | `denominator_coeff_eigen_of_scaling_cross` |
| a denominator coefficient below the degree gives `Φ(u) = a^s·u` with `u ≠ 0`, `s ≠ 0` | `exists_nondegenerate_relation_of_denominator` |
| the same for two nonzero numerator coefficients (homogeneous case) | `exists_nondegenerate_relation_of_numerator` |
| **`Φ(u) = (q/ρ^m)^s·u` with `s ≠ 0` ⟹ Ritt's order-one relation** | `RittHomogeneousBaseRelation.exists_rittForm_of_scaling_eigen` |

The last one is immediate from the exponent computation: `(q/ρ^m)^s = q^s·ρ^{−ms}`, whose exponent
pair `(s, −ms)` is nonzero as soon as `s ≠ 0`, so the invariant-differential-to-Ritt-form conversion
applies.

Consequence: **the degenerate branch survives only when the sliced fraction is a monomial in the
coordinate at the bottom levels** — `Q = X^{deg Q}` and `P` a single term, i.e. the tower element is
`u · t^m`.  Unwinding that case at `n = 2` reproduces the rational affine connection
(`ψ(u)·ρ = u − dK ρ/ρ`), so it is not a new obstruction there; making that reduction uniform in `n`
is what closes the branch.

### The monomial case of the degenerate branch (2026-08-30)

`HTGeometry/RittMonomialScaling.lean` handles what was left of the degenerate branch — the case where
the sliced fraction is a *monomial* `W = u·t^d` in its coordinate.

| Statement | Name |
|---|---|
| a transcendental has no nonzero integer power in the coefficient field | `zpow_notMem_of_transcendental` |
| **the monomial split**: at a scaling level, `σ(u·t^d) = c·(u·t^d) + γ` with `d ≠ 0` forces `γ = 0` **and** `φ(u)·a^d = c·u` | `monomial_scaling_split` |
| `ψ(u)·(q/ρ^m)^d = q^i·ρ^k·u` with `(i − d, k + m·d) ≠ (0,0)` ⟹ Ritt's order-one relation | `RittHomogeneousBaseRelation.exists_rittForm_of_scaling_eigen_shifted` |

So a monomial element at a scaling level of the tower **cannot carry an inhomogeneity at all**: the
two powers `t^d` and `t^0` are linearly independent over the coefficient field, so the relation
splits, the inhomogeneity dies, and what survives is a homogeneous eigen-relation for the
coefficient — which is Ritt's form as soon as its exponent pair is nonzero.

The degenerate branch is therefore reduced to a single arithmetic condition: the exponents produced
by the descent cancelling exactly, `i = d` and `k = −m·d`.  Every other configuration — a
non-monomial numerator or denominator at either scaling level, a monomial with a surviving exponent,
or a nonzero inhomogeneity — now lands on Ritt's relation or on the affine obstruction.

### The logarithmic derivative names the obstruction (2026-08-30)

`HTGeometry/RittBaseExponent.lean` and `HTGeometry/RittLogDerivativeObstruction.lean` close the last
structural question about the *homogeneous* branch: which named obstruction it is.

The scalars the descent produces are monomials `q^i·ρ^k`, and the `q`-exponent is **invisible to the
logarithmic derivative**, because the multiplier `q` is a derivation constant.  With the base chain
rule `dK ∘ ψ = ρ·(ψ ∘ dK)` (`RittFrame.dK_psi`), an eigen-relation `ψ(u) = c·u` becomes

```text
ρ · ψ(v) = v + dK c / c ,        v = dK u / u,
```

and for `c = q^i·ρ^k` the inhomogeneity is exactly `k · dK ρ / ρ`.  So

| `k` | what the relation is |
|---|---|
| `k ≠ 0` | scaling by `−k` gives `ρ·ψ(a) = a − dK ρ/ρ` — the **rational affine-connection equation** |
| `k = 0` | `ρ·ψ(v) = v` — an **invariant rational vector field** |

| Statement | Name |
|---|---|
| `dK ∘ ψ = ρ·(ψ ∘ dK)` | `RittFrame.dK_psi` |
| `dK` kills every integer power of a constant | `RittFrame.dK_zpow_eq_zero` |
| `ρ^k = q^j` with `dK ρ ≠ 0` ⟹ `k = 0` | `RittFrame.zpow_exponent_eq_zero_of_eq_zpow_const` |
| `dKLog` is a homomorphism `K^× → K`, `dKLog (a^k) = k·dKLog a` | `RittFrame.dKLog_mul`, `_inv`, `_zpow` |
| `ψ(u) = c·u` ⟹ `ρ·ψ(dKLog u) = dKLog u + dKLog c` | `RittFrame.dKLog_relation_of_eigen` |
| the monomial form, with inhomogeneity `k·dKLog ρ` | `RittFrame.dKLog_relation_of_monomial_eigen` |
| **`k ≠ 0` ⟹ a rational affine connection** | `RittFrame.exists_affineConnection_of_monomial_eigen` |
| `ψ(u) = u` ⟹ `ρ·ψ(dKLog u) = dKLog u` | `RittFrame.invariantVectorField_of_psi_fixed` |

This makes the homogeneous branch consumable by `RationalAffineConnection.lean` directly, in its own
vocabulary, without going through Ritt's form — and it does so *without seeing the `q`-exponent*, so
the exponent cancellations are harmless for it.

**Remaining, precisely.**  Only the fully degenerate configuration is untouched: the descent's
scalar collapses to `q^0ρ^0 = 1` with zero inhomogeneity, leaving `ψ(u) = u`, whose logarithmic
derivative `v` satisfies `ρ·ψ(v) = v` and may be zero — the case where every coefficient of the
sliced fraction is a derivation constant, which forces numerator and denominator to be monomials over
the constants.  Closing it needs either a map-level exclusion of that configuration or a global
invariant along the descent that the current bookkeeping does not carry.

### An eigenvector in the first jet field is already an affine connection (2026-08-30)

`HTGeometry/RittFirstJetAffineDescent.lean` closes the loop between the logarithmic derivative and
the two-step slicing.

| Statement | Name |
|---|---|
| `d 1 = 0`, `d y⁻¹ = −(d y)·y⁻²` | `RittFrame.d_one`, `RittFrame.d_inv` |
| the derivation carries `K⟮τ⟯` into `K⟮τ, d τ⟯` | `RittFrame.d_mem_adjoin_two_of_mem_adjoin_one` |
| `σ x = c·x` in the extension ⟹ `ρ·σ(d x/x) = d x/x + dKLog c` | `RittFrame.dLog_relation_of_eigen_L` |
| an affine relation over `K⟮τ, d τ⟯` descends to the base in two slicings | `RittFrame.exists_base_affine_of_secondJetField` |
| **an eigenvector `x ∈ K⟮τ⟯` with `σ x = q^i ρ^k·x` gives `∃ a ∈ K, ρ·ψ(a) = a + k·dKLog ρ`** | `RittFrame.exists_base_affine_of_firstJetField_eigen` |

For `k ≠ 0` that last relation *is* the rational affine connection after scaling by `−k`; for `k = 0`
it is the invariant-vector-field equation.  The mechanism: the logarithmic derivative of `x` lives in
the second jet field, the chain rule turns the eigen-relation into an affine one there, and the two
coprime slicings — in `d τ` over `K⟮τ⟯` (the shift scales by `q/ρ`), then in `τ` over `K` (it scales
by `q`) — bring it down to the base.

**What this leaves.**  In the degenerate branch the descended element at the level above the base is
an eigenvector inside `K⟮τ⟯`, so it produces the affine connection unless its `ρ`-exponent `k₁`
vanishes.  Tracking the exponent recursion, `k_{j−1} = k_j − (j−1)·s_{j−1}`, degeneracy at every
level below the point where the inhomogeneity dies forces `s = 0` — equal numerator and denominator
degrees — at each of those levels, on top of `k = 0` there.  Since the descent starts with `k = −n`
and a nonzero Faà di Bruno inhomogeneity, closing the branch is now a finite combinatorial statement
about where the inhomogeneity can die and what the degrees can be, not a structural gap.
