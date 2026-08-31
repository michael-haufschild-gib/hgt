# Noisy binary-tree channel homogeneous BP clock is hypertranscendental

- **ID:** `noisy-binary-tree-channel-rg-clock-hypertranscendence`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / TRANSFER-CHANNEL COROLLARY
- **Scientific status:** `[PROVED] [PARENT-DERIVED] [NOT NEW MATHEMATICS]`
  `[EXACT BINARY-SYMMETRIC TREE INFERENCE] [NOT A QUANTUM CHANNEL THEOREM]`
- **Parent theorem:**
  `../needs-audit/bethe-padic-holographic-rg-clock-hypertranscendence.md`
- **Statement:** On the homogeneous one-message submanifold of exact belief propagation on a
  regular `p`-ary tree, every strictly noisy nontrivial binary symmetric edge channel has a
  hypertranscendental exact message-to-depth beta and clock in every locally invertible DA message
  scheme.  The noiseless channel has a DA power-map clock, while the completely noisy channel
  collapses.  This is the information-theoretic form of the Bethe-Ising theorem, not an independent
  novelty claim.

## Exact transfer-channel derivation

Let parent and child spins be `s,t in {+1,-1}`.  A binary symmetric channel with signal
eigenvalue `a in [0,1]` has transition law

```text
P(t|s)=(1+a s t)/2.                                              (1)
```

For crossover probability `delta`, one has `a=1-2 delta`.  Represent an incoming child belief by
its magnetization `y`:

```text
mu_y(t)=(1+t y)/2.                                               (2)
```

The likelihood contributed by one child branch to parent value `s` is

```text
w_s(y)=sum_(t=+-1) P(t|s) mu_y(t)
      =(1+s a y)/2.                                              (3)
```

For `p` conditionally independent identical descendant branches, likelihoods multiply:

```text
W_+(y)=2^(-p)(1+ay)^p,
W_-(y)=2^(-p)(1-ay)^p.                                          (4)
```

The common factor cancels in the posterior magnetization.  Therefore exact homogeneous BP is

```text
                       (1+ay)^p-(1-ay)^p
B_(p,a)(y)= --------------------------------------------
                       (1+ay)^p+(1-ay)^p

           = tanh(p arctanh(a y)).                              (5)
```

This is exactly the rational family `F_(p,a)` of the parent Bethe/holographic theorem.  No Ising
Hamiltonian is needed for the derivation; conversely, a positive zero-field Ising edge is precisely
the same binary symmetric transfer channel with `a=tanh K`.

## All-noise theorem

For a genuine BSC,

```text
0 < delta < 1/2       <=>       0 < a < 1.                       (6)
```

The parent all-temperature theorem now gives:

1. if `0<a<1/p`, the zero-message fixed point is attracting and its local Schröder beta/clock is
   HT;
2. if `a=1/p`, the zero-message fixed point is parabolic and every sectorial Abel beta/clock is
   HT;
3. if `1/p<a<1`, zero is repelling, a non-superattracting ordered fixed basin excludes every
   Ritt-integrable class, and the Poincare beta/clock is HT;
4. if `a=1`, the channel is noiseless, `(5)` is Möbius-conjugate to `z -> z^p`, and its exact
   generator is DA;
5. if `a=0`, the channel is completely noisy and `(5)` collapses to zero.

Thus every strictly noisy informative BSC has an HT exact homogeneous message-depth generator.
The conclusion is invariant under every locally invertible DA message coordinate, including
log-likelihood ratio, cavity field, odds, and magnetization charts on their local domains.

## Two thresholds that must not be conflated

The scalar homogeneous recursion has multiplier

```text
B_(p,a)'(0)=pa.                                                 (7)
```

Its symmetry-breaking/Bethe fixed-point transition is therefore `pa=1`.  Broadcasting
reconstruction is a distributional inference problem.  For the symmetric binary channel on a
regular tree, its Kesten--Stigum threshold is

```text
p a^2=1.                                                        (8)
```

Equation `(8)` controls survival of root information in the random boundary-message distribution,
not stability of the deterministic homogeneous message in `(5)`.  The HT theorem is valid on
both sides of both thresholds for every `0<a<1`; only the functional-equation realization changes
at `(7)`.

Consequently the result does **not** claim a new reconstruction threshold, an HT mutual
information, or a direct operational obstruction to decoding.

## Physical meaning

The reusable mechanism is exact:

```text
strict binary transfer noise + independent branch-likelihood multiplication
  -> nonexceptional rational message iteration
  -> no finite algebraic-differential exact depth generator.                  (9)
```

This places the Bethe theorem simultaneously in classical spin transfer, Bayesian tree inference,
noisy broadcasting, and positive binary tensor-network language.  It also identifies the boundary
of the result.  A general binary-memoryless-symmetric channel carries a distribution of BSC
reliabilities rather than one scalar `a`; nonhomogeneous messages produce a multidimensional or
distributional BP operator; a quantum channel carries operator-valued messages.  None is covered
by `(5)`.

## Anti-theatre and novelty verdict

Binary symmetric broadcasting, its equivalence to the zero-field Ising model on a tree, exact BP,
and the two thresholds `(7)`--`(8)` are parent theory.  The HT conclusion is an immediate physical
reinterpretation of the parent Bethe theorem because the rational map is identical.  Calling this
a new mathematical theorem would count a change of vocabulary as discovery.

The card is retained because it discharges a narrower structural question: the HT mechanism does
not depend on thermodynamic language and is universal across the scalar BSC/Ising transfer class.
The next novelty-bearing generalization must change the mathematical object—nonhomogeneous BMS
message distributions, asymmetric positive transfer matrices, or operator-valued quantum
channels—and prove that an exact physical scalar observable inherits HT.

Targeted searches across broadcasting, cavity/BP recursion, `tanh/atanh` message updates, and
hypertranscendence found the parent literatures separately and no earlier HT message-clock theorem.
That negative evidence does not alter the `NOT NEW SCIENTIFIC KNOWLEDGE` verdict because the result
is already a direct corollary of the Bethe family theorem.

## Lean boundary

The one-edge BSC likelihood identities `(3)`, their `p`-branch projective numerator and
normalization `(4)`--`(5)`, and the all-noise endpoint anchors are unconditional algebra.  They are
formalized in
`formal/GaloisForLFunctions/HTGeometry/BetheHolographicIsingRG.lean` alongside the exact rational
family.  The stochastic reconstruction theorem `(8)` and the external HT classification remain
paper-level parent inputs and are not postulated in Lean.

## Primary sources

- W. Evans, C. Kenyon, Y. Peres, and L. J. Schulman, *Broadcasting on Trees and the Ising Model*,
  *Annals of Applied Probability* 10 (2000), <https://doi.org/10.1214/aoap/1019487349>.
- Y. Gu, H. Roozbehani, and Y. Polyanskiy, *Broadcasting on trees near criticality*,
  <https://arxiv.org/abs/2005.07801>.
- S. B. Hopkins and A. Li, *Adversarially-Robust Inference on Trees via Belief Propagation*,
  <https://proceedings.mlr.press/v247/hopkins24a.html>.
- K. Okunishi and T. Takayanagi, *Statistical Mechanics Approach to the Holographic
  Renormalization Group: Bethe Lattice Ising Model and p-adic AdS/CFT*,
  <https://arxiv.org/abs/2310.12601>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.

## Gates

- [x] Exact BSC branch-likelihood recursion derived.
- [x] Homogeneous BP map identified with the Bethe rational family.
- [x] Strict-noise HT corollary proved for the entire DA message-scheme class.
- [x] Noiseless DA and completely noisy collapsed endpoints separated.
- [x] Bethe and Kesten--Stigum thresholds separated.
- [x] Classical, distributional, and quantum scope boundaries stated.
- [x] Direct-corollary novelty failure stated.
- [x] Unconditional transfer-channel algebra formalized in HTGeometry.
- [ ] Nonhomogeneous BMS message-distribution theorem proved.
- [ ] Asymmetric positive transfer-matrix theorem proved.
- [ ] Operator-valued quantum-channel inheritance theorem proved.

## Lean status (2026-08-30)

The card's own algebra is unconditional Lean in
`formal/GaloisForLFunctions/HTGeometry/BetheHolographicIsingRG.lean` (one-edge BSC likelihoods
`(3)`, the `p`-branch projective numerator and normalisation `(4)`–`(5)`, the endpoint anchors).

What remains is the single external input shared by all three open cards of this folder: the
**Becker–Bergweiler / Ritt hypertranscendence classification** of Schröder, Abel and Poincaré
conjugacies of a non-exceptional rational map, together with the stochastic reconstruction theorem
`(8)`.  The corpus now owns the differential-algebra half of the dichotomy the classification feeds
(`HTGeometry/RittDichotomy.lean`, `HTGeometry/RittCocycle.lean`,
`HTGeometry/ScalingGermRigidity.lean`): the equivalences `Φ` DA `⇔` `κ` DA `⇔` `β` DA, the fact that
the order-one Ritt relation is an algebraic differential equation, and both directions of the
cocycle equivalence.  Missing is exactly Ritt's implication "differentially algebraic Poincaré
function ⇒ order-one cocycle relation".

## Ritt `(1) ⇒ (4)`: the route, and how much of it is now Lean (2026-08-30)

The implication is the main theorem of Di Vizio–Fernandes, *A Galoisian proof of Ritt theorem on the
differential transcendence of Poincaré functions* (arXiv:2102.08268).  In their normalisation `τ` is
the Koenigs linearizer, `τ(R(x)) = q·τ(x)` with `|q| > 1`, and the theorem reads: `τ` is
differentially algebraic over `C(x)` **iff** `(τ′)^r = A(x)·τ^j` for integers `r ≠ 0`, `j` and a
rational `A`.  Composing with `σ = τ^{-1}` turns that into the relation `(4)` of this card.

The Galois theory is inessential — both Galois inputs are elementary rigidity statements about a
field `L` carrying a ring endomorphism `σ` compatible with an endomorphism `ψ` of a base `K` and a
derivation `d` with the chain rule `d ∘ σ = ρ · (σ ∘ d)`, where `ρ = R′`.  That structure is
`HTGeometry/RittFirstOrderForm.lean`'s `RittFrame`, and the following are now unconditional Lean,
all auditing to `[propext, Classical.choice, Quot.sound]`:

| Step of the Di Vizio–Fernandes proof | Lean |
|---|---|
| additive rigidity: `σ w = w + c`, `w` algebraic over the base ⇒ `w` in the base | `RittShiftRigidity.exists_algebraMap_eq_of_isIntegral_of_shift_add` |
| multiplicative rigidity: algebraically dependent shift coordinates give an integer monomial in the base | `RittShiftRigidity.exists_algebraMap_eq_zpow_prod_of_not_algebraicIndependent` |
| `σ (d τ) = (q/ρ)·d τ` | `RittFrame.sigma_d_eq_of_shift` |
| **(2) ⇒ (3): an order-one algebraic differential equation forces Ritt's form `(τ′)^r = A·τ^j`** | `exists_rittForm_of_not_algebraicIndependent` |
| Faà di Bruno triangularity `σ(d^[n]τ) − (q/ρ^n)·d^[n]τ ∈ span{d τ,…,d^[n−1]τ}` | `RittFrame.shift_jet_sub_mem_jetSpan` |
| **the collapse step: a top jet integral over the prefix field already lies in it** | `RittJetCollapse.jet_mem_of_isIntegral_of_lower_jets_mem` |

The additive lemma is the endomorphism version of the corpus's
`AlgebraicPrimitiveDescent.algebraic_additive_primitive_eq_base_add_constant` (divisibility of the
minimal polynomial replaces irreducibility of its image, so no surjectivity of `ψ` is needed); the
multiplicative one is the contrapositive of
`MultiplicativeShiftIndependence.algebraicIndependent_of_multiplicativeShift`.

### What is left, precisely

Only Di Vizio–Fernandes's `(1) ⇒ (2)` — "differentially algebraic ⇒ *order one*".  Their argument
takes `n` minimal with an algebraic differential equation of order `n`, assumes `n > 1`, and uses
the collapse step to put `τ^{(n)}` in `K_n = K(τ,…,τ^{(n−1)})`; the paper then asserts that this
contradicts minimality.  **It does not**: `y_n ∈ K_n` with `y_0,…,y_{n−1}` algebraically independent
is possible for a general differentially algebraic function (Airy, `y″ = xy`).  The contradiction
has to use the functional equation, and working the case `n = 2` out gives exactly

```text
a(R)·(R')^2 = R'·a - R''                                        (Ritt-AC)
```

— the **rational affine-connection equation**, which the corpus already owns in
`HTGeometry/RationalAffineConnection.lean` (`IsAffineConnection`, the critical obstruction
`no_affine_connection_regular_at_critical`, and the finiteness closers), and reaches from the jet
side through `JetAffineConnectionLevelTwo.exists_ratFuncDeriv_affine_connection_of_hasNormalizingShift_two`.
The same corpus lane — `JetSubstitutionDescent.exists_nonzero_isInvariantDifferential_or_hasNormalizingShift`
and `JetTailTrivial.fixed_isConst` — runs the whole descent in the free jet field and closes it
unconditionally for `z² + 1` and `(z − 1)²`.

So the remaining work is one bridge, *differentially algebraic linearizer ⇒ finite-order eigenvector
of the jet substitution*, feeding a descent machine the corpus already has, plus the `n ≥ 2` collapse
whose first case is the affine connection the corpus already excludes for concrete maps.  The
Nevanlinna route is **not** the obstruction: the corpus's second-main-theorem stack with the
`S(r,f)` error term is complete (`LogDerivCountingRatio`, `RamificationSubstitution`,
`NevanlinnaErrorNegligible`, `NevanlinnaRamification.card_totallyRamified_le_four`), and
Becker–Bergweiler need Nevanlinna only to reduce the non-repelling case to the repelling one.

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

### An affine relation anywhere in the tower descends to the base (2026-08-30)

`HTGeometry/RittAffineRelationDescent.lean` and `HTGeometry/RittAffineTowerDescent.lean` finish the
structural reduction of the *inhomogeneous* branch.

| Statement | Name |
|---|---|
| one level: `ν·σW = W + β` over an affinely moved generator gives `(ν·a^s)·φ(u) = u + β` **or** `= u`, for the numerator's leading coefficient `u ≠ 0` | `exists_affine_or_eigen_descent` |
| **the whole tower**: an affine relation over `K⟮τ, …, d^[n−1]τ⟯` leaves `ν'·ψ(a) = a + γ'` in the base, with `a ≠ 0`, `γ' ∈ {γ, 0}` and `ν' = ν·q^I·ρ^J` | `exists_base_affine_relation_of_tower` |

The mechanism is the residue classification again: writing `ν·σW = W + β` as the eigen slice with
eigenvalue `ν⁻¹` and *zero* linear inhomogeneity coefficient, the residue can only be `0` or the
constant `ν⁻¹β`, so the shape of the relation survives a level with its scalar multiplied by a power
of that level's multiplier — and the only alternative is that it degenerates to an eigen-relation,
which `exists_rittForm_of_homogeneous_base_relation` converts into Ritt's order-one relation as soon
as the accumulated exponents do not both vanish.

**The obstruction layer is now one equation family on the base.**  Everything the descent can produce
is

```text
q^I · ρ^J · ψ(a) = a + γ ,      a ≠ 0,  I, J ∈ ℤ,
```

with `γ` either zero (the invariant-differential case, which yields Ritt's form) or one of the
explicit elements the tower supplies — the Faà di Bruno coefficients `A_p`, or `dK ρ / ρ` on the
logarithmic-derivative route, where `J = 1, I = 0` is exactly `RationalAffineConnection`'s
`a(R)·(R′)² = R′·a − R″`.  Closing the three cards is now: rule out that family for their maps.

### The obstruction layer *is* the corpus's affine transport equation (2026-08-30)

A corpus search turned up `HTGeometry/RationalAffineTransport.lean`, which already owns exactly the
equation family the descent produces:

```text
IsAffineTransport R hR k b c a   :   a(R) · (R′)^k = b · a + c
```

with the transport laws proved once and for all — `affineTransport_pole_forward` /
`affineTransport_pole_backward` (off the critical set, where `b` is a unit and `c` is regular, a pole
of `a` travels along `R` in both directions), `no_pole_of_forward_orbit_affineTransport` /
`no_pole_of_backward_orbit_affineTransport` (a pole on an injective critical-free orbit is
impossible), and `ratOrder_le_of_critical` (the ramification inequality at a critical point).

`HTGeometry/RittTransportBridge.lean` connects the two:

| Statement | Name |
|---|---|
| `q^I·ρ^J·ψ(a) = a + γ` **is** `IsAffineTransport R hR J (q^{−I}) (q^{−I}·γ) a` | `isAffineTransport_of_monomial_base_relation` |
| the homogeneous case is the invariant-differential instance, `c = 0` | `isAffineTransport_of_homogeneous_base_relation` |

Two things fall out immediately.  The multiplier `b = q^{−I}` is a **nonzero constant**, so the
"`b` is a unit along the orbit" hypothesis of every transport lemma is automatic — only "`c` regular
along the orbit" survives, and `c = q^{−I}·γ` has finitely many poles.  And the homogeneous branch
is literally `c = 0`, where that hypothesis is vacuous.

So the whole of Ritt's implication now reduces to one statement in the corpus's own vocabulary: for
the map at hand, `IsAffineTransport R hR J b c a` has no nonzero solution for the finitely many
`(J, c)` the tower supplies.  That is precisely the shape
`RationalAffineConnection.no_affine_connection_regular_at_critical` and the orbit closers already
handle for `k = 2`, `b = R′`, `c = −R″`.

### Constant solutions, and when a solution must have a zero or a pole (2026-08-30)

`HTGeometry/RittTransportConstant.lean`:

| Statement | Name |
|---|---|
| over an algebraically closed field, a rational function of everywhere-vanishing signed order is a nonzero constant | `eq_C_of_ratOrder_eq_zero_algClosed` |
| **`a = α` constant solves `a(R)·(R′)^k = b·a + c` iff `c = α·(R′)^k − b·α`** | `isAffineTransport_C_iff` |
| **an inhomogeneity not of that shape forces every nonzero solution to have a zero or a pole** | `exists_ratOrder_ne_zero_of_no_constant_solution` |

The substitution by `R` is a `K`-algebra map, so it fixes the constants: a constant solution leaves
no freedom at all, `c` is determined by `α`.  Everything else must be non-constant, and over an
algebraically closed field that means it has a point of nonzero order — which is exactly the input
the pole-transport closers `no_pole_of_forward_orbit_affineTransport` and
`no_pole_of_backward_orbit_affineTransport` consume.

Combined with `RittTransportBridge`, ruling out Ritt's obstruction for a given map is now this
chain: the descent's inhomogeneity `c = q^{−I}·γ` is not of constant type ⟹ every solution has a
zero or a pole ⟹ a pole on an injective critical-free orbit is impossible (the multiplier
`b = q^{−I}` being constant, its unit hypothesis is automatic) ⟹ the pole is confined to the
critical/periodic set ⟹ the ramification inequality `ratOrder_le_of_critical` closes it.

### From rational to polynomial, and the degree pin (2026-08-30)

`HTGeometry/RittTransportPolynomial.lean` turns the surviving obstruction into a polynomial identity.

| Statement | Name |
|---|---|
| over an algebraically closed field, a rational function of everywhere non-negative order is a polynomial (numerator and denominator are coprime, so a denominator root would be a pole, and a rootless denominator is constant) | `exists_polynomial_of_ratOrder_nonneg` |
| substitution by a polynomial sends the image of `A` to the image of the composite `A ∘ R` | `ratFuncSubstitutionAlgHom_algebraMap` |
| **a polynomial solution of `a(R)·(R′)^J = β·a + c` is the polynomial identity `A ∘ R · (R′)^J = β·A + C`** | `polynomial_identity_of_isAffineTransport` |

That identity pins the degree.  For `deg R ≥ 2` and `deg A ≥ 1` the left side has degree
`deg A · deg R + J·(deg R − 1) ≥ 2·deg A + J > deg A`, so the inhomogeneity must carry exactly that
degree; an inhomogeneity of any other degree admits no non-constant polynomial solution, and the
constant solutions are pinned by `isAffineTransport_C_iff`.

So the per-map chain is now entirely elementary: `c` not of constant type ⟹ every solution has a
zero or a pole ⟹ if it has no pole it is a polynomial and its degree is pinned ⟹ otherwise the pole
transports along an injective critical-free orbit, which a nonzero rational function cannot sustain.

### A checkable criterion that kills every polynomial solution (2026-08-30)

`HTGeometry/RittTransportNoSolution.lean`,
**`no_polynomial_solution_of_natDegree_lt`**: for any `R` with `deg R ≥ 2`, any nonzero constant `β`,
any `J`, and any inhomogeneity `Cp` satisfying

1. **no constant solution** — `Cp ≠ α·(R′)^J − β·α` for every `α ≠ 0`, and
2. **low degree** — `deg Cp < deg R + J·(deg R − 1)`,

the polynomial identity

```text
A ∘ R · (R′)^J = β·A + Cp
```

has no nonzero solution `A`.  The proof is pure degree bookkeeping: with `deg A ≥ 1` the left side
has degree `deg A·deg R + J·(deg R − 1)`, which for `deg R ≥ 2` strictly exceeds both `deg A` and —
by hypothesis 2, since `deg A·deg R ≥ deg R` — `deg Cp`, while the right side has degree at most the
maximum of those two; and `deg A = 0` is exactly hypothesis 1.

Both hypotheses are *arithmetic in the coefficients of the map*: no orbits, no critical points, no
valuations.  Combined with `exists_polynomial_of_ratOrder_nonneg` and
`polynomial_identity_of_isAffineTransport`, a solution of the transport equation that has no pole is
now excluded outright; only solutions *with* a pole survive, and those are what the orbit closers of
`RationalAffineTransport` remove.

### The master criterion, and what the cards' maps still need (2026-08-30)

**`RittTransportNoSolution.no_transport_solution_of_criteria`** packages the whole chain: for
`deg R ≥ 2`, a nonzero constant multiplier `β`, and a polynomial inhomogeneity `Cp` with

1. no constant solution (`Cp ≠ α·(R′)^J − β·α` for all `α ≠ 0`), and
2. `deg Cp < deg R + J·(deg R − 1)`,

a nonzero solution `a` of `IsAffineTransport R hR J β Cp a` with no pole is impossible.  Only
pole-carrying solutions survive, and those the orbit closers of `RationalAffineTransport` remove.

**The obstacle now identified precisely.**  The corpus's transport theory —
`IsAffineTransport`, the pole-transport laws, the orbit closers, `ratOrder_le_of_critical`, and
therefore this master criterion — is stated for a **polynomial** `R : K[X]`.  The step-scaling maps
of these cards,

```text
R_(p;u,v)(y) = ((1+uy)^p − (1+vy)^p) / ((1+uy)^p + (1+vy)^p),
```

are **rational, not polynomial**: for `p ≥ 2` the denominator is a genuine nonconstant polynomial.
So instantiating the criterion for them needs the rational-map version of the transport layer:
`ratOrder` of `a ∘ R` at a point in terms of the local degree of `R` there, the pole-transport laws
off the critical set, and the orbit closers, all for `R ∈ K(x)` rather than `K[X]` — which also has
to handle the points `R` sends to infinity.

That generalisation is the next infrastructure piece, and it is the only thing between the
finished reduction and the three cards.

### The rational-map order theory: foundation built (2026-08-30)

The blocker identified last pass — the corpus's transport layer is polynomial-only while the cards'
maps are rational — is now being removed.  `HTGeometry/RittRationalOrderAeval.lean` and
`HTGeometry/RittRationalSubstitutionOrder.lean`:

| Statement | Name |
|---|---|
| a polynomial expression in an element regular at `a` is regular at `a` | `ratOrder_aeval_nonneg` |
| if the element *vanishes* at `a` and the polynomial has nonzero constant term, the expression is a **unit** at `a` | `ratOrder_aeval_eq_zero` |
| the value of a rational map at a point of regularity, and `P − value` as a quotient of polynomial images | `ratValue`, `sub_ratValue_eq` |
| **the local multiplicity is positive**: `0 < ord_a (P − P(a))` at a point where `P` is regular | `ratOrder_sub_ratValue_pos` |
| **the substitution law for a rational map**: `ord_a (M(P)) = mult_{P(a)} M · ord_a (P − P(a))` | `ratOrder_aeval_ratFunc` |

The proof is the local factorisation carried through a rational substitution: `M = (X − b)^m·N` with
`N(b) ≠ 0` gives `M(P) = (P − b)^m · N(P)`, the first factor contributes `m` times the local
multiplicity, and the cofactor is a unit at `a` because `P − b` vanishes there and the Taylor
expansion of `N` at `b` has nonzero constant term — which is exactly what the two `aeval` lemmas
above supply.

This is the same shape as the corpus's polynomial law `ratOrder_ratFuncSubstitution`, with the local
multiplicity taken in the rational sense `mult_a (num P − b · denom P)`.  What remains of the layer
is extending it from a polynomial outer factor `M` to a general rational `Q` (multiplicativity of
`ratOrder` over `num/denom`), and then re-running the pole-transport laws and orbit closers with it.

### Pole transport for a rational map (2026-08-30)

`HTGeometry/RittRationalTransport.lean` completes the transport layer in the generality the cards
need.

| Statement | Name |
|---|---|
| the image of a polynomial in `K(x)` is its evaluation at the generator | `algebraMap_eq_aeval_X` |
| substitution sends the image of a polynomial to its evaluation at the map | `ratFuncSubstitutionAlgHom_aeval` |
| **the substitution law for a rational map and a rational argument**: `ord_a (Q(P)) = ord_{P(a)} Q · ord_a (P − P(a))` | `ratOrder_ratFuncSubstitution_ratFunc` |
| the affine transport equation `a(P)·(P′)^k = b·a + c` for rational `P` | `IsRatAffineTransport` |
| **a pole travels backward along a rational map** | `ratAffineTransport_pole_backward` |
| **a pole on an injective critical-free backward orbit is impossible** | `no_pole_of_backward_orbit_ratAffineTransport` |

The transport argument is unchanged from the polynomial case once the substitution law is available:
at a point where `P` is regular, `P′` and `b` are units and `c` is regular, the left side of the
transport equation has order `ord_{P(p)} a` times the local multiplicity — a *positive* integer — so
a pole at the image makes the left side negative, and the valuation inequality on `b·a + c` forces a
pole of `a` at the point itself.  Note the local multiplicity need not be one: positivity alone
carries the sign, so no non-critical hypothesis is needed for the backward direction beyond `P′`
being a unit.

That closes the gap the polynomial-only layer left; what remains to instantiate the master criterion
for the cards' maps is the same arithmetic as before — degrees, critical points, and orbit witnesses
— now in the rational setting.

### The Ritt cocycle for the step-scaling family: normal form and the exclusion plan

The transport layer is now complete enough to state exactly what the cards need and how it closes.
The relation a differentially algebraic linearizer forces is the *homogeneous* transport

`F(R(z)) · R'(z)^k = b · F(z)`,  `b` a nonzero constant, `k ≠ 0`, `F` rational nonzero,

which says the map preserves a rational `k`-differential up to scale — the Ritt cocycle `(5)`.

**Degree-two normal form.**  In the projective coordinate `w = (1+y)/(1−y)` the family becomes
`w ∘ R = M(w)^p` with the Möbius factor

`M(w) = ((1+u)w + (1−u)) / ((1+v)w + (1−v))`,

so the map is `π_p ∘ M`: degree `p`, with **exactly two critical points**, `c_0 = M^{-1}(0) = (u−1)/(u+1)`
and `c_∞ = M^{-1}(∞) = (v−1)/(v+1)`, each totally ramified, over the two critical values `0` and `∞`.
Conjugating by `φ(w) = (w − c_0)/(w − c_∞)`, which sends `c_0 ↦ 0` and `c_∞ ↦ ∞`, puts the map in the
two-parameter normal form

`h(w) = (A − B λ w^p) / (1 − λ w^p)`,   `A = h(0) = c_0/c_∞`,   `B = h(∞) = φ(∞) = 1`.

The three identities that drive everything are exact:

`h − A = λ w^p (A−B)/(1−λw^p)`,  `h − B = (A−B)/(1−λw^p)`,  `h′ = p λ (A−B) w^{p−1}/(1−λw^p)²`.

For both channel families `B = 1` and `A = c_0/c_∞` is real in `(0,1)`: for the symmetric channel
`u = a`, `v = −a` one gets `A = ρ²` with `ρ = (1−a)/(1+a)`, and for the asymmetric channel
`A = [(u−1)(v+1)]/[(u+1)(v−1)]`, a ratio of two negative numbers of decreasing modulus.

**The cyclic symmetry.**  `h(w)` depends on `w` only through `w^p`, so `h(ζw) = h(w)` and
`ζ h′(ζw) = h′(w)` for every `p`-th root of unity `ζ`.  Substituting `ζw` into the cocycle gives

`F(ζ w) = ζ^{−k} F(w)`,

so **the divisor of `F` is invariant under the cyclic group `μ_p`**.  This is the observation that
makes the counting sharp.

**The counting.**  Every fibre of `h` over a finite point other than the two critical values `A`,
`B` consists of `p` distinct finite non-critical points, and at such a point the transport equation
says `ord_z F = ord_{h(z)}F`.  So with `S` the finite support of `ord F` and `T = S \ {A,B}`, the
fibre over each point of `T` lies in `S`, whence `p·|T| ≤ |S| ≤ |T| + 2`.  Cyclic invariance adds
that `S` is a union of `μ_p`-orbits, so a nonempty `T` already contains `p − 2` points, forcing
`(p−1)(p−2) ≤ 2`.  Hence

* `p ≥ 4`: `T = ∅` outright;
* `p = 3`: `T` is a single point whose `μ_3`-orbit is all of `S`, so `A` and `B` lie in one orbit
  and `A³ = B³`;
* `p = 2`: a short list of configurations, each of which forces `h(A) = −A`, `h(A) = −B`, or
  `A² = B²`.

**The endgame.**  When `T = ∅` the support lies in `{A,B}`, so `F = c(w−A)^m(w−B)^n` outright, and
substituting the three identities gives

`c(A−B)^{m+n+k} λ^{m+k} p^k w^{pm + k(p−1)} (1−λw^p)^{−m−n−2k} = b c (w−A)^m (w−B)^n`.

Comparing orders at `w = 0` gives `pm + k(p−1) = 0`, and comparing at `w = A` — legitimate as soon
as `A` is not a pole, `λA^p ≠ 1` — gives `m = 0` and hence `k = 0`, contradicting `k ≠ 0`.

So the map carries no Ritt cocycle as soon as `A ≠ 0`, `B ≠ 0`, `λA^p ≠ 1`, `A^p ≠ B^p`, and, in
degree two only, `h(A) ∉ {−A, −B}` — all of them explicit conditions on the channel parameters.

### The no-cocycle theorem is proved (2026-08-30)

The exclusion of the Ritt cocycle for the step-scaling normal form is now Lean, unconditional, for
every degree `p ≥ 2`.

| Statement | Name |
|---|---|
| the quotient rule for the derivative of a rational function | `ratFuncDeriv_div` |
| the normal form `(A − Bλw^p)/(1 − λw^p)` and its three exact identities | `cnf`, `cnf_sub_C_A`, `cnf_sub_C_B`, `ratFuncDeriv_cnf` |
| the map is nonconstant; its value, local multiplicity and derivative order at a point of regularity | `cnf_not_isConst`, `ratValue_cnf`, `ratOrder_cnf_sub_ratValue_regular`, `ratOrder_ratFuncDeriv_cnf_ne_zero` |
| the origin is totally ramified over the first critical value | `ratOrder_cnf_sub_C_A_zero`, `ratOrder_ratFuncDeriv_cnf_zero` |
| **the transport equation, away from the critical point and at it** | `cnf_transport_regular`, `cnf_transport_critical` |
| fibres: `p` distinct regular unramified points over every non-critical value | `cnfFiber`, `card_cnfFiber`, `cnfFiber_value`, `cnfFiber_den_ne_zero` |
| two critical values in one fibre force `(A−B)(A^p − B^p) = 0` | `pow_eq_pow_of_same_fiber` |
| **the support of a solution lies in the two critical values** (`p ≥ 3`) | `cnf_support_subset` |
| **the endgame**: support in `{A,B}` kills the equation | `cnf_no_cocycle_of_support` |
| in degree two a fibre is a sign pair | `neg_mem_cnfFiber_two`, `cnfFiber_two_eq_pair` |
| **the support statement in degree two** | `cnf_support_subset_two` |
| **the no-cocycle theorem, every degree** | `cnf_no_cocycle`, `cnf_no_cocycle_two`, `cnf_no_cocycle_general` |

The endgame turned out shorter than the divisor computation the plan anticipated: with the support
inside `{A,B}` the origin carries no order, so the ramification identity reads
`p·ord_A F = −k(p−1)`; and transporting the order from `A` to its image forces `ord_A F = 0`, since
`h(A) = A` would need `λA^p(A−B) = 0` and `h(A) = B` would need `A = B`.  Hence `k(p−1) = 0`.

The hypotheses are explicit inequalities in the two critical values and the pole parameter:
`A ≠ 0`, `B ≠ 0`, `A ≠ B`, `A^p ≠ B^p`, `λ ≠ 0`, `λA^p ≠ 1`, and in degree two only
`h(A) ∉ {−A, −B}`.  A separate module settles the polynomial sub-family `αz^p + β`
(`no_ritt_cocycle_unicritical`), which is what the noiseless boundary of the channel degenerates to.

What remains between this and the cards is the conjugation: the identity carrying
`R_(p;u,v)` to `cnf p A B λ` with `A = c_0/c_∞` and `B = 1`, the transport of the cocycle equation
through a Möbius change of coordinate, and the verification of the six inequalities for the interior
channel parameters — where `A` is real in `(0,1)`, so `A^p ≠ B^p = 1` is immediate.

### The map-specific instantiation is closed (2026-08-30)

The exclusion now applies to the cards' own maps, not only to a normal form.

| Statement | Name |
|---|---|
| the quotient rule for a general rational quotient | `ratFuncDeriv_div_general` |
| **substitution composes** | `ratFuncSubstitutionAlgHom_comp` |
| **the chain rule** `(Q ∘ P)′ = (Q′ ∘ P)·P′` | `ratFuncDeriv_substitution` |
| **a semiconjugacy carries an invariant differential** | `isRatAffineTransport_of_semiconj`, `transport_ne_zero` |
| the channel map `((1+uy)^p − (1+vy)^p)/((1+uy)^p + (1+vy)^p)` | `treeRG` |
| the conjugating Möbius coordinate `Φ(t) = (t−1)/(u − vt)` | `treeConj`, `treeConj_not_isConst`, `ratFuncDeriv_treeConj_ne_zero` |
| `R ∘ Φ = (t^p − 1)/(t^p + 1)` | `subst_treeConj_treeRG` |
| `Φ ∘ h = (t^p − 1)/(t^p + 1)` for `h = cnf p A B λ` | `subst_cnf_treeConj` |
| **the channel map carries no Ritt cocycle** | `treeRG_no_cocycle` |
| **every interior channel `−1 < v < u < 1`** | `treeRG_no_cocycle_interior` |

The conjugation is explicit: `Φ(t) = (t−1)/(u−vt)` carries the normal form with
`A = (1−u)/(1−v)`, `B = (1+u)/(1+v)`, `λ = (1+v)/(v−1)` to the channel map, and both `Φ ∘ h` and
`R ∘ Φ` equal the symmetric form `(t^p−1)/(t^p+1)` — because `1 + uΦ = (u−v)t/(u−vt)` and
`1 + vΦ = (u−v)/(u−vt)` on one side, and because `h − 1` and `u − v·h` are both `(u−v)/(1−v)` times
`t^p ∓ 1` on the other.

For an interior channel all six non-degeneracy conditions are sign facts: `A ∈ (0,1)`, `B > 1`,
`λ < 0`, hence `A^p < 1 < B^p`, `1 − λA^p > 1`, and in degree two the image of `A` is positive while
`−A` and `−B` are negative.

**What is left for these cards is now entirely analytic**: the Poincaré/Schröder/Abel construction at
the fixed point, the closure of differential algebraicity under composition and compositional
inverse, and the instantiation of the `RittFrame` at the linearizer — after which Ritt's theorem
delivers the cocycle that `treeRG_no_cocycle_interior` refutes.

### The Ritt relation is refuted for the clock (2026-08-30)

The two halves are now joined.  A first-order Ritt relation for a Poincaré function is *the same
thing* as a rational differential invariant of the map, and the interior channel map has none.

| Statement | Name |
|---|---|
| evaluation of a polynomial at a transcendental element | `ratFuncEval_polyImage` |
| the chain rule for that evaluation | `derivation_aeval`, **`derivation_ratFuncEval`** |
| substitution intertwines evaluation with an algebra endomorphism | `algHom_ratFuncEval` |
| **Ritt's relation is a rational cocycle** | `isRatAffineTransport_of_ritt_relation` |
| **no Ritt relation for an interior tree channel** | `no_ritt_relation_treeRG_interior` |

The bridge is exact.  In a differential field carrying the scaling operator `S : f(z) ↦ f(λz)` —
`S z = λz`, `d ∘ S = λ·S ∘ d` — a Poincaré function `y` satisfies `S y = R(y)`, and applying `S` to
`(d y)^r = z^j A(y)` gives, via the chain rule `d(R(y)) = R′(y)·d y`,

`R′(y)^r A(y) = λ^{r+j} A(R(y))`.

Evaluation at a transcendental element is injective, so this descends to `ℂ(t)` as the affine
transport equation `A ∘ R · (R′)^{−r} = λ^{−(r+j)}·A`, refuted by `treeRG_no_cocycle_interior`.

**Remaining for these cards**, all analytic:

1. the germ differential field at the fixed point, with `S` as a `ℂ`-algebra endomorphism and the
   commutation `d ∘ S = λ·S ∘ d`;
2. the Poincaré function itself at a *repelling* fixed point — the corpus has Koenigs and
   `exists_poincare_of_linearizer` for the attracting case, so the repelling case is the linearizer
   of the local inverse;
3. its transcendence over `ℂ` and the identity `S y = R(y)` in the form `ratFuncEval` expects;
4. Ritt's implication itself in that concrete frame — the algebraic core is the `RittFrame` stack,
   whose `fixed` hypothesis is the rigidity that an `R`-invariant germ at a repelling fixed point is
   constant (compare leading Taylor coefficients: `a_m λ^m = a_m` forces `m = 0`).

Items 1–3 are infrastructure; item 4 is the one with mathematical content left.

### The bridge in the shape the germ field carries (2026-08-30)

The scaling operator an analytic germ field at a *repelling* fixed point actually supports is the
contracting one, `T : f(z) ↦ f(z/λ)` — the expanding shift `f(z) ↦ f(λz)` does not preserve a disc.
The bridge is therefore restated in that shape, where the Poincaré equation reads `y = R(T y)`:

| Statement | Name |
|---|---|
| two evaluations related by an algebra endomorphism | `algHom_ratFuncEval_shift` |
| evaluation at a value of the map factors through substitution | `ratFuncEval_of_eq_eval` |
| **Ritt's relation is a cocycle, contracting form** | `isRatAffineTransport_of_ritt_relation_contracting` |
| **no Ritt relation for an interior tree channel, contracting form** | `no_ritt_relation_treeRG_interior_contracting` |

The computation is the mirror of the expanding one.  Differentiating `y = R(T y)` gives
`d y = R′(T y)·d(T y)`, so `T(d y) = λ·d y / R′(T y)`; applying `T` to `(d y)^r = z^j A(y)` and using
`A(y) = A(R(T y))` turns it into `A ∘ R = λ^{−(r+j)}·(R′)^r·A` at the transcendental element `T y`,
which is the same transport equation, refuted by `treeRG_no_cocycle_interior`.

**Corpus assets found for the remaining analytic layer** (searched, not rebuilt):

* `ScalingGermRigidity.eventuallyEq_const_of_scaling_invariant` and `eq_monomial_of_scaling` — a germ
  invariant under a contracting scaling is constant; one transforming by a scalar is a monomial.
  This is exactly the `(5) ⇒ (4)` rigidity of the dichotomy card and the `fixed` hypothesis of the
  `RittFrame`.
* `KoenigsLinearizationGerm`, `PoincareFunctionGerm.exists_poincare_of_linearizer`,
  `exists_poincare_koenigs` — the linearizer and the Poincaré germ.
* `EntirePoincareExtension.exists_entire_poincare` — the entire extension at a repelling fixed point
  (stated for an entire map; the channel map is rational, so a meromorphic-extension variant is
  needed, or the germ field used directly).
* `Bottcher.MeromorphicField` — `meroField U`, with `precompMeroMap`, `restrictMeroHom` and
  `precompMeroAlgEquiv`.  For `U` a disc about the fixed point, `T` is `precompMeroMap` along
  `w ↦ w/λ`, which does map the disc into itself; this is why the contracting form is the right one.

What is still missing is the derivation on `meroField U` for a disc together with the chain rule for
`precompMeroMap`, and the transcendence of the Poincaré germ — after which the contracting bridge
applies verbatim.

### The scaling operator on the germ field, with its chain rule (2026-08-31)

The differential carrier the contracting bridge needs is now built.

| Statement | Name |
|---|---|
| the scaling self-map, its analyticity, and `w ↦ μw` carrying a disc into itself for `‖μ‖ ≤ 1` | `scaleMap`, `analyticOnNhd_scaleMap`, `mapsTo_scaleMap` |
| its derivative is the constant `μ`; its image of an open set is open | `deriv_scaleMap`, `isOpen_image_scaleMap` |
| the coercion of a pulled-back analytic germ | `precompAnalyticMap_coe` |
| **the chain rule on analytic germs**: `(f ∘ (μ·))′ = μ · (f′ ∘ (μ·))` | `analyticSubringDeriv_precompAnalytic` |
| **the scaling as an endomorphism of the meromorphic germ field** | `scaleMero` |
| **the scaling twists the meromorphic derivation by `μ`** | `scaleMero_deriv` |

The germ-level statement is the ordinary chain rule, transported through `Germ.compTendsto` and the
identity theorem's `analyticSubring`; the field-level statement survives the quotient rule, because
writing `x = a/b` and applying `Derivation.leibniz_div` on both sides leaves the constant `μ` as a
common factor.  Both rest on the corpus's `MeromorphicDifferentialField` (`analyticSubringDeriv`,
`meroFieldDifferential`) and `Bottcher.MeromorphicField` (`precompAnalyticMap`, `precompMeroMap`).

**Still to do**, and now a short list:

1. the `ℂ`-algebra structure on `meroField U` and the upgrade of the `ℤ`-derivation to a
   `Derivation ℂ`, plus `scaleMero` as a `ℂ`-algebra hom (`precompAnalyticMap_constToAnalytic`
   already says it fixes constants);
2. `scaleMero z = μ·z` for the coordinate germ;
3. the Poincaré germ as an element of `meroField (ball 0 ρ)` with `y = R(T y)`, and its transcendence
   over `ℂ`;
4. Ritt's implication in that frame — for which `ScalingGermRigidity` supplies the `fixed` input.

With 1–3 the contracting bridge `no_ritt_relation_treeRG_interior_contracting` applies verbatim.

### The complex differential frame of the disc germ field (2026-08-31)

Two of the four remaining items are now Lean.

| Statement | Name |
|---|---|
| the complex algebra structure through the constant germs | `meroComplexAlgebra`, `meroComplexAlgebra_algebraMap` |
| the germ derivation kills a constant germ | `analyticSubringDeriv_constToAnalytic` |
| **the meromorphic derivation kills the constants** | `meroDeriv_algebraMap_complex` |
| **the scaling fixes the constants** | `scaleMero_algebraMap_complex` |
| the coordinate germ | `coordMero` |
| **the scaling acts on the coordinate by the scaling constant** | `scaleMero_coordMero` |

Together with `scaleMero_deriv` these are exactly the frame the contracting bridge consumes: a
complex differential field, a complex algebra endomorphism twisting the derivation by `μ`, and a
coordinate on which that endomorphism acts by `μ`.  Upgrading the `ℤ`-derivation to a
`Derivation ℂ` is now mechanical — killing the constants is precisely the missing linearity.

**A route that does not apply.**  The corpus already contains Bergweiler's hypertranscendence for
Poincaré functions (`PoincareHypertranscendence.not_differentiallyAlgebraicOn_of_unbounded_conjugates`,
`not_differentiallyAlgebraicOn_poincare_exp`), which bounds the differential order of the conjugating
maps.  It cannot serve these cards: it needs the iterates `f^[n]` to have unbounded differential
order, which holds for a transcendental entire `f` such as `exp` but fails for a rational map, whose
iterates are rational and so of bounded order.  That is exactly why the Poincaré function of a
rational map *can* be differentially algebraic — power, Chebyshev and Lattès maps — and why Ritt's
classification, not an order count, is the necessary input here.

**Left:** the Poincaré germ as an element of `meroField (ball 0 ρ)` with `y = R(T y)` and its
transcendence over `ℂ`, and Ritt's implication in that frame (its `fixed` input being
`ScalingGermRigidity`).

### Germ transcendence and rational evaluation (2026-08-31)

| Statement | Name |
|---|---|
| over an algebraically closed base an algebraic element is a scalar | `exists_eq_algebraMap_of_isAlgebraic` |
| pointwise polynomial evaluation at an analytic function is analytic | `analyticOnNhd_eval_poly_comp` |
| **polynomial evaluation on germs** | `aeval_analyticMeroElement` |
| **a nonconstant analytic germ is transcendental over the constants** | `transcendental_analyticMeroElement_of_nonconstant_on` |
| **rational evaluation at a germ is a quotient of composites** | `ratFuncEval_analyticMeroElement` |
| **a pointwise rational identity is a germ-level evaluation** | `analyticMeroElement_eq_ratFuncEval` |

The transcendence proof is short because the base is algebraically closed: an algebraic element of
any extension of `ℂ` has an irreducible, hence linear, minimal polynomial, so it is a constant germ,
and faithfulness of the germ realization turns that into constancy of the function on the domain.
The corpus's `transcendental_analyticMeroElement_of_nonconstant` is stated for entire functions and
argues by countability of level sets; the disc version above needs neither.

`analyticMeroElement_eq_ratFuncEval` is the form in which the Poincaré equation enters the bridge:
a pointwise identity `Φ(z)·D(Φ(μz)) = N(Φ(μz))` on the disc says exactly that the germ of `Φ` is the
value of `R = N/D` at the germ of `Φ(μ·)`.

**Left:** the identification `scaleMero (germ f) = germ (f ∘ (μ·))`, which turns the previous line
into `y = R(T y)`; and Ritt's implication in the assembled frame.

### The Poincaré germ of an interior tree channel admits no Ritt relation (2026-08-31)

The frame is assembled and the bridge is instantiated on genuine analytic germs.

| Statement | Name |
|---|---|
| substitution by equal evaluation points agrees | `ratFuncEval_congr_eq` |
| **the scaling acts by precomposition on realizations** | `scaleMero_analyticMeroElement` |
| the coordinate germ of a disc is nonzero | `coordMero_ne_zero` |
| **the Poincaré germ of an interior tree channel satisfies no Ritt relation** | `no_ritt_relation_poincare_tree_interior` |

The capstone takes only analytic data on a disc `‖z‖ < ρ`: an analytic `Φ`, nonconstant along with
`Φ(μ·)`, the pointwise Poincaré identity in cleared-denominator form

`Φ(z)·D(Φ(μz)) = N(Φ(μz))`   for `‖z‖ < ρ`,

and a first-order Ritt relation `(Φ′)^r = z^j A(Φ)` in the germ field.  It builds the complex
derivation (complex-linear because it kills the constants) and the contracting scaling as a complex
algebra endomorphism (it fixes them), checks `T z = μ z` and `d ∘ T = μ · T ∘ d`, and feeds the
whole thing to `no_ritt_relation_treeRG_interior_contracting`, which refutes it for every interior
channel `−1 < v < u < 1` and every `p ≥ 2`.

So the chain is complete from the channel algebra to an analytic statement about the linearizing
germ: **no clock germ of an interior tree channel satisfies an order-one algebraic differential
equation of Ritt's shape.**

**Left:** Ritt's implication itself — that a differentially algebraic linearizer must satisfy such a
relation.  Its `fixed` input, that a germ invariant under a contracting scaling is constant, is the
corpus's `ScalingGermRigidity.eventuallyEq_const_of_scaling_invariant`.

### The Koenigs picture (2026-08-31)

The linearizer picture is the one in which the abstract `RittFrame` actually applies: the shift is
substitution by the map, `S : f ↦ f ∘ R`, and the Koenigs equation `S κ = λ κ` is a genuine eigen
relation with a *constant* eigenvalue — unlike the Poincaré equation, which is not.

| Statement | Name |
|---|---|
| **a first-order relation for the linearizer is a rational cocycle** | `isRatAffineTransport_of_koenigs_relation` |
| **the linearizer of an interior tree channel satisfies no first-order relation** | `no_koenigs_relation_treeRG_interior` |

The computation is three lines of algebra.  Differentiating `S κ = λκ` with the twisted chain rule
`d ∘ S = ι(R′)·S ∘ d` gives `λ·dκ = ι(R′)·S(dκ)`; applying `S` to `(dκ)^r = A(t)·κ^j` and
substituting eliminates `κ^j`, leaving

`A ∘ R · (R′)^r = λ^{r−j}·A`,

the affine transport equation with `k = r` and constant `λ^{r−j}` — refuted for every interior
channel.

**The single remaining item** is Ritt's implication: that a differentially algebraic linearizer
satisfies a first-order relation of that shape.  Its abstract algebraic core is the `RittFrame`
stack already built (`exists_rittForm_of_not_algebraicIndependent` for order one,
`rittForm_or_jet_mem_jetPrefixField` and `rittForm_or_affineObstruction_or_degenerate` for the tower),
and what is left is to instantiate that frame on the germ field with

`K = ℂ(t)`,  `L` = germs at the fixed point,  `σ` = substitution by `R`,  `ρ = R′`,  `τ = κ`,
`q = λ`,

whose `fixed` hypothesis — that an `R`-invariant germ is constant — is the corpus's
`ScalingGermRigidity.eventuallyEq_const_of_scaling_invariant` read through the linearizing
coordinate.

### Ritt's frame, instantiated (2026-08-31)

| Statement | Name |
|---|---|
| **substitution by a rational map is a Ritt frame over `ℂ(t)`** | `koenigsRittFrame` |
| **the linearizer of an interior tree channel satisfies no order-one algebraic differential equation** | `no_order_one_dependence_koenigs_treeRG_interior` |
| **a differentially algebraic linearizer collapses its jet tower** | `jet_collapse_of_DA_koenigs_treeRG_interior` |

The frame is exactly the shape of the abstract structure: `σ` is substitution by the map, `ψ` its
restriction to `ℂ(t)`, `d` the derivation, `dK` the rational derivative, and the chain-rule factor is
`ρ = R′`.  The Koenigs equation is the frame's linearizing equation with the derivation-constant
multiplier `λ`, so the order-one case closes immediately: algebraic dependence of `κ` and `dκ` over
`ℂ(t)` gives Ritt's relation, which the fibre count refutes.

For arbitrary order the frame's tower theorem gives *Ritt's relation or a collapse of the jet
tower*; since the first branch is now refuted, a differentially algebraic linearizer of an interior
channel must collapse its tower at some level `n ≥ 2`.  That is the precise remaining statement to
kill.

**A defect to fix in what was built earlier.**  `rittForm_or_affineObstruction_or_degenerate` is not
a usable trichotomy as it stands: its third branch asserts `∃ u ≠ 0, ψ u = u`, which any nonzero
*constant* satisfies, so that branch is vacuously true and cannot be refuted.  Closing the
higher-order case needs that branch strengthened — the `u` produced by the collapse carries more
structure (it is a leading coefficient of a jet relation) than the current statement records.

### Sharpening the degenerate branch (2026-08-31)

| Statement | Name |
|---|---|
| a rational function of degree zero is a constant | `eq_C_of_ratFuncDegree_eq_zero` |
| **a rational function fixed by substituting a map of degree at least two is constant** | `eq_C_of_substitution_fixed` |

This is the tool the vacuous third branch needs.  Substitution multiplies degrees
(`ratFuncDegree_substitution`), so `u ∘ R = u` with `deg R ≥ 2` forces `deg u = 0`, hence `u ∈ ℂ`.
The branch therefore does not merely say "some nonzero `u` is fixed" — it says the leading
coefficient produced by the tower descent is a *constant*, which is a genuine constraint to feed
back into the descent.

What is still needed to use it on the cards' maps is `2 ≤ ratFuncDegree (treeRG p u v)`.  The route
is degree multiplicativity along the conjugacy already proved: `ratFuncDegree` of the symmetric form
`(t^p − 1)/(t^p + 1)` is `p`, and `treeConj` is a Möbius coordinate of degree one, so
`ratFuncDegree (treeRG) = p`.  Both halves need the reduced numerator and denominator identified
with the evident coprime representations.

### The degree of the channel map is `p` (2026-08-31)

| Statement | Name |
|---|---|
| a generator of the rational function field has degree one | `ratFuncDegree_eq_one_of_adjoin_eq_top` |
| the degree of a polynomial image is its degree | `ratFuncDegree_algebraMap` |
| a coordinate expressible in a function makes it a generator | `adjoin_eq_top_of_X_mem` |
| **the conjugating Möbius coordinate generates** | `adjoin_treeConj_eq_top` |
| the Möbius factor of the symmetric form is `treeConj 1 (−1)` | `treeConj_one_neg_one`, `subst_pow_treeConj` |
| **the degree of the tree channel map is `p`** | `ratFuncDegree_treeRG` |
| **a rational function fixed by substituting a channel map is constant** | `eq_C_of_substitution_fixed_treeRG` |

No numerator/denominator reduction was needed.  Degree multiplies along substitution, and a
rational function that generates the whole field has degree one, so the conjugacy already proved
computes the degree by itself:

`deg R · deg Φ = deg (R ∘ Φ) = deg ((t^p−1)/(t^p+1)) = deg M · deg (t^p) = p`,

with `Φ` and `M` both generators — indeed `M = Φ` with parameters `1, −1`, so one generation lemma
serves twice.  Solving `Φ = (t−1)/(u−vt)` for `t` gives `t = (uΦ+1)/(1+vΦ)`, which is what puts the
coordinate back inside the adjoined field.

The degenerate branch of the tower alternative is therefore now fully usable: a base element fixed
by the base shift of a channel map is a *constant*.

### The base relation of a collapse is a transport equation (2026-08-31)

| Statement | Name |
|---|---|
| **a base relation `ψ u = b·u + A` is an affine transport equation of weight zero** | `isRatAffineTransport_of_base_relation` |
| a homogeneous base relation with trivial exponents pins the base element to a constant | `eq_C_of_base_relation_trivial` |

This is the interface between the two halves of the argument.  `exists_base_relation_of_collapse`
produces, from a jet-tower collapse, a base-field relation `ψ u = c·u + g` with `c = q^i ρ^k` and
`g = 0` or `g = z·A_j`.  The homogeneous case with `(i,k) ≠ (0,0)` is Ritt's form
(`exists_rittForm_of_homogeneous_base_relation`) and is refuted; the homogeneous case with
`(i,k) = (0,0)` now forces `u` to be a constant (`ratFuncDegree_treeRG`); and the inhomogeneous case
is exactly the affine transport equation whose pole-transport and orbit machinery is already built
(`ratAffineTransport_pole_backward`, `no_pole_of_backward_orbit_ratAffineTransport`).

**What remains** is to close the last two of those: to derive a contradiction from a constant `u` in
the trivial-exponent case, and to refute the inhomogeneous transport equation, whose inhomogeneity
`z·A_j` is one of the coefficients of the collapse relation.  The first needs the descent to record
more about `u` than it currently does; the second needs orbit data for the inhomogeneity.

### The pure-eigen case of a collapse (2026-08-31)

| Statement | Name |
|---|---|
| **a pure eigen relation at level `n` gives a monomial relation** | `exists_monomial_of_pure_jet_eigen` |

When the collapse relation of the jet tower has no lower-order coefficients, the top jet is itself a
multiplicative shift coordinate with multiplier `q/ρ^n`, so it and the linearizer are two such
coordinates and multiplicative rigidity converts any algebraic dependence between them into

`a = τ^{m₀} · (d^[n] τ)^{m₁}`,   `(m₀,m₁) ≠ 0`,  `a ≠ 0`.

For `n = 1` this is exactly the step that produces Ritt's first-order form; for higher `n` it is the
same rigidity one level up the tower, and it is what the vanishing-coefficient case of the base
relation reduces to.

The two remaining gaps are unchanged in substance: a *constant* `u` in the trivial-exponent
homogeneous case carries no information as `exists_base_relation_of_collapse` currently records it,
and the inhomogeneous transport equation needs orbit data for its inhomogeneity.

### The pure-eigen branch yields Ritt's form (2026-08-31)

| Statement | Name |
|---|---|
| **a pure eigen relation at level `n` always yields Ritt's first-order form** | `rittForm_of_pure_jet_eigen` |

Applying the shift to the monomial relation `a = τ^{m₀}(d^[n]τ)^{m₁}` turns it into the homogeneous
base relation

`ψ a = q^{m₀+m₁} · ρ^{−n·m₁} · a`,

and its exponent pair cannot both vanish: `−n·m₁ = 0` forces `m₁ = 0` because `n ≥ 1`, and then
`m₀ = 0` too, contradicting `m ≠ 0`.  So `exists_rittForm_of_homogeneous_base_relation` applies and
returns Ritt's order-one form — which the fibre count refutes.

The derivative exponent entering the chain-rule factor with weight `n` is what makes this work: it
is exactly the reason the higher levels of the tower cannot hide a degenerate relation, and it is
why this branch closes while the trivial-exponent branch of the *base* relation does not.

### What the descent needs, precisely (2026-08-31)

| Statement | Name |
|---|---|
| the inhomogeneous base relation, as a transport equation | `isRatAffineTransport_of_inhomogeneous_base_relation` |

Both remaining gaps live inside `exists_base_relation_of_tower` and its wrapper
`exists_base_relation_of_jet_mem`, not in the surrounding theory.  Recording the diagnosis exactly.

**Where the exponents come from.**  The descent is seeded with `c₀ = q·ρ^{−n}`, i.e. exponent pair
`(1, −n)`, and each level multiplies by `(q·ρ^{−m})^{s}` for the level's `m` and some `s : ℤ`.  So
the final pair is `(1 + Σ s_t, −n − Σ m_t s_t)`.  Nothing in the current statement prevents that
from being `(0,0)`, and when it is, the relation degenerates to `ψ u = u`, which
`eq_C_of_substitution_fixed_treeRG` shows makes `u` a constant — true, but not contradictory.

**Why the jet branch closes and this one does not.**  In `rittForm_of_pure_jet_eigen` the derivative
exponent enters the chain-rule factor with weight `n ≥ 1`, so `−n·m₁ = 0` already forces `m₁ = 0`.
In the base relation the weights `m_t` vary along the descent and can cancel.  The fix is to make the
descent record enough to rule the cancellation out — the natural candidate is to carry the
*normalisation* of the minimal polynomial: if the leading coefficient `u` is a constant the
polynomial can be taken monic, and the relation then constrains the next coefficient instead, which
is where the inhomogeneity `z·A_j` reappears with `z ≠ 0`.

**The two statements to prove.**

1. `exists_base_relation_of_tower` should return, in addition, either `(i,k) ≠ (0,0)` or a
   *nonzero* inhomogeneity — obtained by renormalising when the leading coefficient is constant.
2. The inhomogeneous case is `IsRatAffineTransport R hR 0 (C λ^i · (R′)^k) (z·A_j) u`.  To refute it
   for the channel map one needs an injective critical-free backward orbit along which the
   inhomogeneity stays regular, and then
   `no_pole_of_backward_orbit_ratAffineTransport`.  The corpus's
   `exists_ratOrder_ne_zero_of_no_constant_solution` supplies the pole in the first place.

Everything else in the chain — map algebra, normal form, fibre count, no cocycle, no Ritt relation,
the analytic germ frame, the order-one case, and the pure-eigen branch — is proved unconditionally.

### A dead route for closing the degenerate branch (2026-08-31)

The natural repair — "distinct monomials in the minimal polynomial have distinct multipliers, so at
most one coefficient can have `c = 1`, and any other coefficient gives `(i,k) ≠ (0,0)`" — **does not
work**, and it is worth recording why so the next pass does not spend time on it.

The jet at level `j` has multiplier `q/ρ^j`, so a monomial `∏_j (d^[j]τ)^{e_j}` has multiplier

`∏_j (q/ρ^j)^{e_j} = q^{Σ e_j} · ρ^{−Σ j·e_j}`.

Two exponent vectors therefore collide exactly when they share both the total degree `Σ e_j` and the
weighted degree `Σ j·e_j` — two linear conditions, easily satisfied by distinct vectors.  For
instance `e = (2,0,1)` and `e′ = (1,2,0)` both have total degree `3` and weighted degree `2`, hence
the same multiplier.  So the multiplier map is not injective on multi-degrees and cannot separate the
coefficients of the minimal polynomial.

That rules out the cheap repair.  Any working fix has to use the derivation as well as the shift —
which is precisely what the *inhomogeneous* branch of the base relation encodes — rather than the
multiplicative data alone.  In other words the two remaining gaps are not independent: the
trivial-exponent homogeneous case must be pushed into the inhomogeneous one, and then refuted there
by the transport machinery.

### Pole transport for the normal form (2026-08-31)

| Statement | Name |
|---|---|
| **a pole travels backward along the cyclic normal form** | `cnf_pole_backward` |
| **a pole on an injective critical-free backward orbit is impossible** | `cnf_no_pole_of_backward_orbit` |

The homogeneous case of the transport equation is settled by the order identity — the order of a
solution is *equal* at a point and its image, which is what the fibre count exploits.  The affine
case only gives an inequality, so it has to move poles instead, and it can do so exactly where the
coefficient is a unit and the inhomogeneity is regular.  Away from the origin the normal form is
regular with unit derivative, so those are the only conditions that remain.

This is the tool the inhomogeneous branch of the tower descent needs.  What it still requires from
that branch is an injective backward orbit `w` with `w(n+1) ≠ 0`, `1 − λ w(n+1)^p ≠ 0`, along which
the coefficient `C λ^i·(R′)^k` stays a unit and the inhomogeneity `z·A_j` stays regular — the
Faà di Bruno coefficients `A_j` being explicit in `q`, `ρ` and its derivatives, their poles sit over
the critical points and poles of the map, so such an orbit is what has to be exhibited.

### Consolidated state of the programme (2026-08-31)

Everything below is Lean, wired, and audits to `[propext, Classical.choice, Quot.sound]`.

**Map algebra → no cocycle.**  `treeRG`/`treeConj` (the channel map and the conjugating Möbius
coordinate); `subst_treeConj_treeRG` and `subst_cnf_treeConj` (both `R ∘ Φ` and `Φ ∘ h` are the
symmetric form); `cnf` and its three identities; `cnf_transport_regular` / `cnf_transport_critical`;
`card_cnfFiber`; `cnf_support_subset`, `cnf_support_subset_two`; `cnf_no_cocycle_general`;
`treeRG_no_cocycle`, `treeRG_no_cocycle_interior`.  Also `no_ritt_cocycle_unicritical` for the
polynomial sub-family and `ratFuncDegree_treeRG` for the degree.

**Cocycle → no Ritt relation.**  `ratFuncDeriv_substitution` (the chain rule the corpus lacked),
`isRatAffineTransport_of_semiconj`; `isRatAffineTransport_of_ritt_relation` and its contracting form;
`no_ritt_relation_treeRG_interior(_contracting)`; the Koenigs picture
`isRatAffineTransport_of_koenigs_relation`, `no_koenigs_relation_treeRG_interior`.

**Analytic realisation.**  `scaleMero` and `scaleMero_deriv`; `meroComplexAlgebra`,
`meroDeriv_algebraMap_complex`, `scaleMero_algebraMap_complex`, `scaleMero_coordMero`;
`transcendental_analyticMeroElement_of_nonconstant_on`; `analyticMeroElement_eq_ratFuncEval`;
`no_ritt_relation_poincare_tree_interior`.

**Ritt's implication.**  `koenigsRittFrame`; `no_order_one_dependence_koenigs_treeRG_interior`
(order one, closed); `jet_collapse_of_DA_koenigs_treeRG_interior`;
`exists_monomial_of_pure_jet_eigen` and `rittForm_of_pure_jet_eigen` (the pure-eigen branch, closed);
`eq_C_of_substitution_fixed_treeRG`; `cnf_pole_backward`, `cnf_no_pole_of_backward_orbit`.

**What is open, and it is one thing in two halves.**  The tower descent
(`exists_base_relation_of_tower`) can end with exponent pair `(0,0)` and zero inhomogeneity, where
the relation `ψ u = u` only says `u` is a constant.  Routing that case into the inhomogeneous branch
cannot be done with multiplicative data alone (the multiplier map is not injective on multi-degrees —
`(2,0,1)` and `(1,2,0)` collide), so it needs the derivation.  And the inhomogeneous branch, now
reduced to pole transport, needs an injective backward orbit avoiding the origin, the poles, the
zeros of the coefficient and the poles of the inhomogeneity.  Both are statements about the descent,
not about the maps; everything the descent feeds into is proved.

### The pole count of an affine transport equation (2026-08-31)

| Statement | Name |
|---|---|
| **the poles of a solution outside the two critical values are bounded by the bad set** | `cnf_pole_count` |

`(p − 1)·|P \ {A,B}| ≤ |E| + 2`, where `P` is the pole set of the solution and `E` is any finite set
outside which the coefficient is a unit, the inhomogeneity is regular, and the map is regular and
non-critical.

This replaces the orbit construction with a count, which is the right move: poles propagate backward
one fibre at a time, the fibres over distinct poles are disjoint and have `p` points each, and each
fibre point is either a pole or bad — so `p·|P′| ≤ |P| + |E|`, and `|P| ≤ |P′| + 2` finishes it.  No
orbit, no exceptional-set theory, no appeal to backward orbits being infinite.

The remaining question is now purely quantitative: for the tower's transport equation the bad set is
`{0}` together with the poles of the map and the zeros and poles of `R′` and of the Faà di Bruno
coefficients, and these sit over the critical points and poles — so `|E|` is of the same order as
`p`, and the inequality `(p−1)|P′| ≤ |E| + 2` bounds `|P′|` by a small constant rather than forcing
it to vanish.  Sharpening it means bounding `|E|` below `p − 3`, or splitting the bad set by the
fibre it meets.

### The bad set was overcounted (2026-08-31)

| Statement | Name |
|---|---|
| `(p−1)·\|P \ {A,B}\| ≤ \|E\| + 2`, with `E` needing only the coefficient and inhomogeneity conditions | `cnf_pole_count` (sharpened) |
| **no poles off the critical values, in degree at least four** | `cnf_no_pole_of_regular_data` |

The estimate recorded above was weak for a silly reason: the bad set was carrying two conditions it
never needed to.  A fibre over a point other than the first critical value automatically avoids the
origin — `0` lies over `A` alone — and automatically avoids the poles of the map, since those lie
over `∞`.  So `E` need only contain the zeros and poles of the coefficient and the poles of the
inhomogeneity; the map's own critical point and poles cost nothing.

That matters because the coefficient of the tower's transport equation is `C λ^i·(R′)^k`, whose
zeros and poles are exactly the origin and the poles of the map — the two sets that are now free.
With the coefficient a unit and the inhomogeneity regular where it counts, `E` is empty and the
count reads `(p−1)|P′| ≤ 2`, which in degree at least four forces `P′ = ∅`: the solution has no poles
outside the two critical values.

So gap (2) is no longer quantitative in degree `≥ 4`.  What remains of it is the small-degree cases
and the regularity of the Faà di Bruno inhomogeneity `z·A_j`, which has to be read off the explicit
coefficients rather than assumed.

### Degree three closes too (2026-08-31)

| Statement | Name |
|---|---|
| **no poles off the critical values in degree at least three** | `cnf_no_pole_of_regular_data_three` |

In degree three the count leaves exactly one configuration: a single pole `y` outside the two
critical values, whose whole three-point fibre is the pole set, so both critical values lie over `y`.
That forces `h(A) = h(B)`, hence `(A−B)(A^p − B^p) = 0`, hence `A^p = B^p` — excluded.  This is the
same configuration, and the same exclusion, that closed degree three for the homogeneous equation;
the pole version needed only the backward implication rather than the order identity.

So the affine transport equation of the tower has no solution with a pole off `{A,B}` for every
`p ≥ 3`, given a unit coefficient and a regular inhomogeneity.  What is left of gap (2) is degree
two — where the count permits two poles and the sign-pair configurations reappear — and the
regularity of `z·A_j` itself.

### Degree two closes; gap (2) is now one regularity check (2026-08-31)

| Statement | Name |
|---|---|
| **no poles off the critical values in degree two** | `cnf_no_pole_of_regular_data_two` |

The count permits one or two poles outside the critical values.  With one, the fibre is a sign pair
of which exactly one member is a critical value — not both, since that would force `A² = B²` — and
the other member is the pole itself, so the pole is the negative of that critical value and the
image of the critical value is excluded by a sign condition.  With two, the two fibres partition the
four-element pole set into the sign pairs of `A` and of `B`, so the poles are `−A` and `−B` and the
image of `A` is again one of the two excluded values.

Degree two needs one exclusion more than the homogeneous case did — `h(B) ≠ −B` alongside
`h(A) ∉ {−A,−B}` — because the affine equation has no analogue of the ramification identity at the
origin that the homogeneous argument used to break the symmetric configuration.  For an interior
channel it holds for the same sign reason as the others: `h(1) = (A−λ)/(1−λ) > 0 > −1` when
`A ∈ (0,1)` and `λ < 0`.

So the affine transport equation of the tower has no solution with a pole off `{A,B}` in **every**
degree `p ≥ 2`, given a unit coefficient and a regular inhomogeneity.  What is left of gap (2) is a
single explicit check: that the Faà di Bruno inhomogeneity `z·A_j` really is regular where the count
needs it, read off the explicit coefficients.

### Differentiation does not create poles (2026-08-31)

| Statement | Name |
|---|---|
| a rational function regular at a point has a denominator not vanishing there | `denom_eval_ne_zero_of_ratOrder_nonneg` |
| **the derivative of a rational function regular at a point is regular there** | `ratOrder_ratFuncDeriv_nonneg` |

This is the induction step for the regularity of the Faà di Bruno inhomogeneity.  The coefficients
are generated by the explicit recursion

`A_{n+1}(j) = ( dK(A_n(j)) + [j ≠ 0]·A_n(j−1) + [j = n]·dK(q/ρ^n) ) / ρ`,

so each is obtained from the previous ones by differentiating, adding, and dividing by the
chain-rule factor `ρ`.  Differentiating preserves regularity — that is the lemma above — addition
preserves it, and dividing by `ρ` preserves it wherever `ρ` is a unit.  For the cyclic normal form
`ρ = h′` is a unit away from the origin and the poles of the map, and those are exactly the points a
fibre over a non-critical value already avoids.

So the regularity the pole count needs is an induction over the recursion, with the base case
`q/ρ^n` and the step supplied by the three closure properties.  That is the last piece of gap (2).

### The Faà di Bruno coefficients are regular; gap (2) is closed (2026-08-31)

| Statement | Name |
|---|---|
| regularity is closed under addition, division by a unit, differentiation | `ratOrder_add_nonneg`, `ratOrder_div_nonneg`, `ratOrder_deriv_nonneg` |
| **the coefficient recursion carries any such predicate** | `exists_shift_jet_coeffs_pred` |
| **the coefficients are regular where the chain-rule factor is a unit** | `exists_shift_jet_coeffs_regular` |

The coefficient recursion was strengthened to carry an arbitrary predicate closed under the three
operations it uses — addition, differentiation, and division by the chain-rule factor — with base
case `q/ρ^n`.  Instantiating that predicate as "regular at `z`" gives the regularity of every
coefficient at any point where `ρ` is a unit.

For the cyclic normal form `ρ = h′` is a unit away from the origin and the poles of the map, and a
fibre over a non-critical value avoids both.  So the inhomogeneity of the tower's affine transport
equation is regular exactly where the pole count needs it, and together with
`cnf_no_pole_of_regular_data`, `..._three` and `..._two` the equation has no solution with a pole off
the two critical values in any degree `p ≥ 2`.

**Gap (2) is therefore closed.**  What remains of the whole programme is gap (1): the trivial-exponent
homogeneous branch of the descent, where the relation `ψ u = u` only says that `u` is a constant, and
which must be routed into the inhomogeneous branch using the derivation rather than the multiplier —
the multiplicative route having been refuted.

### A constant multiplier has no chain-rule exponent (2026-08-31)

| Statement | Name |
|---|---|
| **`q^i·ρ^k` constant, with `ρ` nonconstant, forces `k = 0`** | `zpow_exponent_eq_zero_of_isConst` |

Evaluating the order at a zero or pole of `ρ` — which a nonconstant rational function has over an
algebraically closed field — leaves `k·ord ρ = 0`.  So the degenerate branch of the descent, where
the multiplier is `1`, can only arise with `k = 0` and `q^i = 1`; and when `q` is the multiplier of a
repelling fixed point, `|q| > 1` forces `i = 0` as well.

This pins the shape of the surviving branch exactly: it is not merely that the exponent pair *may* be
`(0,0)`, it is that a constant multiplier *must* have `k = 0`, so the whole chain-rule contribution
to the descent has cancelled.  That is the structural statement any repair has to contradict, and it
confirms that the repair cannot come from the multiplicative side — the multiplier has already been
squeezed to `1` and carries no further information.

### A sound plan for the last branch (2026-08-31)

The refuted repair used the multipliers.  Here is a route that does not, obtained by reading what the
descent actually holds at the moment it degenerates.

`exists_descent_step` writes `W ∈ jetPrefixField τ (m+1)` as a coprime fraction `P/Q` in the top jet
`t = d^[m]τ` over `E = jetPrefixField τ m`, and `exists_affine_or_eigen_descent` compares leading
terms, returning `(ν a^s)·φ(u) = u + β` or `(ν a^s)·φ(u) = u`, with `u` the leading coefficient of
`P`.  The degenerate branch is the second alternative with `ν a^s = 1`.

Two things are then available that the current statement discards.

1. `φ(u) = u` with `φ` the restriction of the shift to `E`, so `Fr.fixed` puts `u` in the base field
   `K`; and `ψ u = u` with a map of degree at least two puts `u` in the constants
   (`eq_C_of_substitution_fixed_treeRG`).  So `u` is a *nonzero constant*, and `P` may be divided by
   it: the descent may assume `P` monic without loss.

2. With `P` monic the leading term carries no information, but the *next* coefficient does.  For
   `P = t^d + v t^{d−1} + …` the coefficient of `t^{d−1}` in the shifted relation is an **affine**
   relation for `v`, whose inhomogeneity comes from the affine part `σ t = a t + b` of the shift on
   the top jet — that is, from `b`, which is where the derivation enters.  That lands in the
   inhomogeneous branch, which is already refuted by the pole count.

So the work is to extend the residue comparison in `RittAffineSliceResidue` from the leading
coefficient to the subleading one, and to thread the normalisation `P ↦ P/u` through
`exists_affine_or_eigen_descent`.  Unlike the multiplicative repair, nothing here is refuted by the
multi-degree collision, because the subleading coefficient is compared at a fixed degree rather than
across monomials.

### Step one of the plan is Lean (2026-08-31)

| Statement | Name |
|---|---|
| **a shift-fixed element of the extension is a constant, for a channel map of degree at least two** | `frame_base_isConst_of_sigma_fixed` |

The chain is short and now formal: `σ y = y` puts `y` in the base field by the frame's `fixed`
field; the compatibility `σ ∘ algebraMap = algebraMap ∘ ψ` and injectivity turn that into `ψ a = a`;
and for a frame whose base shift is substitution by a channel map, `eq_C_of_substitution_fixed_treeRG`
puts `a` in the constants.

This is exactly what licenses the normalisation `P ↦ P/u` in the degenerate branch: the leading
coefficient is a nonzero constant, so dividing by it preserves everything the descent tracks.  What
remains of the plan is the second step — extending the residue comparison in
`RittAffineSliceResidue` from the leading coefficient to the subleading one, where the affine part
`σ t = a t + b` of the shift on the top jet contributes the inhomogeneity.

### The subleading coefficient of a linear twist (2026-08-31)

| Statement | Name |
|---|---|
| the leading coefficient of a power of a linear polynomial | `coeff_linear_pow_self` |
| **the subleading coefficient of a power of a linear polynomial** | `coeff_linear_pow_sub_one` |

`((aX + b)^{n+1}).coeff n = (n+1)·a^n·b`.  This is the technical heart of step two: in the twist of a
polynomial by `X ↦ aX + b`, the coefficient one below the top picks up a term proportional to `b`
times the leading coefficient.  So once the numerator has been normalised to be monic — which step
one licenses — the comparison at that degree reads

`Φ(p_{D−1})·a^{D−1} + D·a^{D−1}·b = d·( c·p_{D−1} + r′ )`,

an *affine* relation for `p_{D−1}` whose inhomogeneity carries `b`, the constant term of the affine
action of the shift on the top jet.  That is the derivation entering, and it lands in the
inhomogeneous branch the pole count refutes.

What is left is to assemble it: run the coefficient comparison at degree `D−1` in
`exists_eigen_relation_residue_of_affine_cross`, exactly as the existing proof does at degree `D`,
using the two identities above in place of `leadingCoeff_mul`.

### The twist's two top coefficients (2026-08-31)

| Statement | Name |
|---|---|
| the top coefficient of a composition with a linear polynomial | `coeff_comp_linear_of_natDegree_le` |
| **the subleading coefficient of a composition with a linear polynomial** | `coeff_comp_linear_sub_one` |

For `R` of degree at most `n+1`,

`(R ∘ (aX+b)).coeff n = R.coeff n · a^n + R.coeff (n+1) · (n+1) · a^n · b`.

The proof splits `R` into its top monomial and a remainder of degree at most `n`: the remainder
contributes only through the top-coefficient formula, and the top monomial contributes through the
subleading coefficient of `(aX+b)^{n+1}`.

These are the two identities the residue comparison uses at degrees `D` and `D−1`.  The first
reproduces the existing leading-coefficient relation; the second is new and is where `b` — the
constant term of the shift's affine action on the top jet — enters, which is the whole point of the
route.

The assembly that remains is to apply them to the polynomial identity
`twistComp Φ (aX+b) P = C d · (C c · P + (αX+β)·Q)` at degree `D−1`, exactly as the existing proof
applies the leading-coefficient formula at degree `D`.

### The subleading slice is proved (2026-08-31)

| Statement | Name |
|---|---|
| **the subleading slice of an affine cross relation** | `subleading_relation_of_affine_cross` |

From the cross relation of the descent, comparing the two sides one degree below the top gives

`Φ(p_{D−1})·a^{D−1} + Φ(p_D)·D·a^{D−1}·b = d·( c·p_{D−1} + ((αX+β)Q).coeff (D−1) )`,

with `d ≠ 0` the scalar by which the twist multiplies the monic denominator.  This is an **affine**
relation for the subleading coefficient, and its inhomogeneity contains `b` — the constant term of
the shift's affine action on the top jet, which is where the derivation enters.

Step two of the plan is therefore complete at the polynomial level.  What is left is to run it
through the same two wrappers the leading slice goes through — `exists_eigen_relation_residue_of_affine_mem_adjoin`,
which passes from a field element `W` to its coprime fraction `P/Q`, and
`exists_affine_or_eigen_descent`, which packages the result for the tower — and then to feed the
resulting inhomogeneous base relation to the pole count, which already refutes it.

### Wrapper one: the subleading slice for a field element (2026-08-31)

| Statement | Name |
|---|---|
| **the subleading slice for an element of a simple transcendental adjunction** | `exists_subleading_relation_of_affine_mem_adjoin` |

The wrapper mirrors the leading-slice one exactly: represent `W` as a coprime fraction `A/B` with `B`
monic, push the shift relation through `aeval` to obtain the polynomial cross relation, and apply the
slice.  The only difference is at the end — the subleading slice replaces the leading one, and its
degree hypothesis `1 ≤ deg A` is carried into the conclusion rather than assumed, since `A` is
produced existentially.

So the chain now reads, for the degenerate branch of the descent: normalise the numerator monic
(licensed by `frame_base_isConst_of_sigma_fixed`), take the subleading slice, and read off an affine
relation whose inhomogeneity carries `b`.  The one remaining wrapper is
`exists_affine_or_eigen_descent`, which packages a slice into the tower's base relation; the pole
count then refutes the packaged inhomogeneous relation.

### The coprime split, and homogeneous descent without drift (2026-08-31)

| Statement | Name |
|---|---|
| the twisted denominator is the denominator scaled | `twistComp_denominator_eq` |
| the twisted numerator satisfies the relation exactly | `twistComp_numerator_eq` |
| **the subleading coefficient of the denominator** | `denominator_subleading_relation` |
| the denominator slice inside an ambient field | `exists_denominator_relation_of_affine_mem_adjoin` |
| the coefficients of a pure scaling twist | `coeff_twistComp_scaling` |
| every denominator coefficient is a twisted eigenvector | `denominator_coeff_eigen` |
| every numerator coefficient satisfies its own relation | `numerator_coeff_eigen` |
| a monic polynomial with vanishing lower coefficients is a power | `monic_eq_X_pow_of_coeff_vanishing` |
| **homogeneous rigidity over an affinely moved generator** | `mem_range_or_affine_connection_of_homogeneous_eigen` |
| one level of homogeneous descent | `mem_prefix_or_affine_connection_of_eigen` |
| **the homogeneous tower descent** | `exists_base_eigen_or_affine_connection_of_tower` |

The cross relation of the affine slice was only ever read at its top coefficient.  Coprimality in
fact splits it into two *exact* polynomial identities — the twisted denominator is `a^{deg Q}` times
the denominator, and the twisted numerator is `a^{deg Q}` times the whole right-hand side.  The first
carries no eigenvalue and no inhomogeneity at all, so it is available in every branch of the descent.

Reading the denominator identity one degree below the top gives, for `deg Q ≥ 1`,

`φ(Q_{deg Q − 1}) + deg Q · b = a · Q_{deg Q − 1}`,

an affine relation whose eigenvalue is the *coordinate's own multiplier* `a` and whose inhomogeneity
is a multiple of the shift's constant term `b`.  That is the missing lever: it does not depend on
the eigenvalue of the relation being sliced, so it cannot be cancelled by the accumulated exponents.

Applying it to `W` and to `W⁻¹` at once proves **homogeneous rigidity**: a solution of `σ W = c·W`
over an affinely moved generator is either already in the coefficient field, or the shift's constant
term vanishes, or the coordinate carries the affine connection with a nonzero solution.  Both
denominators are then constant, both `W` and `W⁻¹` are polynomials, their product is `1`, so both are
units, hence constants.

Iterating gives the theorem the descent was missing: a homogeneous relation `σ W = c·W` anywhere in
the jet tower yields either

* `ψ(u) = c·u` in the base with `u ≠ 0` — **the same `c`, with no exponent drift whatsoever**; or
* a jet whose shift defect vanishes, `σ(d^[m]τ) = (q/ρ^m)·d^[m]τ`; or
* a nonzero solution of the affine connection `σ w = (q/ρ^m)·w − N·b_m` at some level `m`, `N ≥ 1`.

The first alternative is the decisive one.  Gap (1) was exactly that the descent could turn a
nontrivial multiplier `q^i ρ^k` into the trivial one; for a homogeneous relation that is now
impossible — the multiplier arrives at the base unchanged, so a nontrivial exponent pair produces
Ritt's order-one form and is refuted by the fibre count.  In the remaining alternative the multiplier
is `q/ρ^m`, whose exponent of `q` is `1` and therefore never trivial either.

### The descent with monotone exponents (2026-08-31)

| Statement | Name |
|---|---|
| **the affine dichotomy over an affinely moved generator** | `affine_eigen_dichotomy` |
| one level of the affine descent, in five shapes | `affine_descent_dichotomy` |
| dividing a monomial multiplier by a power of the level multiplier | `div_level_multiplier_pow` |
| **the monotone tower descent, stopped at a floor** | `exists_floor_relation_or_exit_of_tower` |
| **the seeded tower descent** | `exists_nontrivial_floor_relation_of_jet_seed` |

The coprime split settles the whole slice, not just its top coefficient.  With the denominator
handled separately — a positive-degree denominator produces the affine connection of the coordinate —
what is left is a polynomial `P` in the top jet, and the shape of the descended relation is read off
its degree `D`:

* `D = 0`: the linear part of the inhomogeneity vanishes and the relation drops one level *unchanged*;
* `D ≥ 2`: a homogeneous relation with scalar `c·(q/ρ^m)^{−D}`;
* `D = 1`: an affine relation with scalar `c·(q/ρ^m)^{−1}` and constant inhomogeneity.

**The exponent by which the scalar is divided is a numerator degree, never a difference of degrees.**
That is the whole point.  In the old slice the exponent was `deg P − deg Q` and could be negative, so
the accumulated exponents could cancel; here it is `D ≥ 0`, so writing the scalar as `q^i ρ^k`, one
step at level `m` sends `(i,k)` to `(i − D, k + m·D)` and for any weight `M ≥ m` the quantity
`k + M·i` changes by `−D·(M − m) ≤ 0`.

The seed of the tower collapse is `c = q/ρ^n`, whose weighted exponent at `M = n − 1` is
`−n + (n − 1) = −1`.  So whatever multiplier the descent delivers has `k + M·i ≤ −1 < 0`, and in
particular its exponent pair is **not** `(0,0)`.  The affine-connection exit has scalar `q/ρ^m` and
inhomogeneity a nonzero multiple of the shift defect — the same seed shape one level down — so a
strong induction on the level absorbs it.

**This closes the drift half of gap (1).**  What remains is the single exit where a jet at or above
the floor has no shift defect, `σ(d^[m]τ) = (q/ρ^m)·d^[m]τ`.  There the generator is a pure
eigenvector, the substitution acts diagonally on its powers, and the exponent of a monomial
`κ·(d^[m]τ)^j` may have either sign — the one place the monotone bookkeeping genuinely fails.  For
the jet tower of a linearizer the defect vanishes only at levels `0` and `1` (level `2` already has
defect `−q·(dρ)·dτ/ρ³`), so the descent runs with floor `2` and the remaining task is the explicit
two-variable analysis in `K(τ, dτ)`, where the shift is diagonal with multipliers `q` and `q/ρ`.

### The defect vanishes only below jet order two (2026-08-31)

| Statement | Name |
|---|---|
| the derivative of the level multiplier | `RittFrame.dK_level_multiplier` |
| the defect vanishes at jet order one | `RittFrame.jetDefect_one` |
| **the defect recursion** | `RittFrame.jetDefect_succ` |
| **the leading coefficient of the defect** | `jetDefect_leading` |
| **the shift defect is nonzero above jet order one** | `jetDefect_ne_zero` |
| **the tower collapse reduces to jet order two** | `exists_nontrivial_level_two_relation` |

Differentiating `σ(d^[n]τ) = (q/ρ^n)·d^[n]τ + defect_n` and using the chain rule gives

`defect_{n+1} = (dK(q/ρ^n)/ρ)·d^[n]τ + ρ^{-1}·d(defect_n)`,   `defect_1 = 0`,

so the coefficient of the top available jet satisfies `λ_{n+1} = (dK(q/ρ^n) + λ_n)/ρ`.  With
`dK(q/ρ^n) = −n·q·(dρ)/ρ^{n+1}` and Pascal's rule the closed form is

`λ_n = −C(n,2)·q·(dρ)/ρ^{n+1}`,

nonzero from `n = 2` on whenever the chain-rule factor is nonconstant.  Since `defect_n` differs from
`λ_n·d^[n−1]τ` by an element of the span of the *lower* jets, and `d^[n−1]τ` is transcendental over
the field they generate, `defect_n ≠ 0` for every `n ≥ 2`.

So the only exit of the monotone descent — a jet whose shift is a pure scaling — is impossible at or
above level two.  Running the descent with floor two therefore always succeeds:

> **the collapse of the jet tower leaves a relation `σ V = c·V + g + Σ A_j·d^[j]τ` over the first two
> jets, with `V ≠ 0` and `c = q^i ρ^k` whose exponent pair is not `(0,0)`.**

What remains of gap (1) is exactly the two-variable endgame.  Below jet order two the shift is
diagonal, `σ τ = q·τ` and `σ(dτ) = (q/ρ)·dτ`, so `K(τ, dτ)` carries a diagonal substitution whose
eigenvectors are the monomials `κ·τ^{e₀}(dτ)^{e₁}`; there the exponent of a monomial may have either
sign, which is why the monotone bookkeeping stops here and an explicit analysis takes over.

### The diagonal endgame: what is left (2026-08-31)

| Statement | Name |
|---|---|
| **the ratio of two coefficients obeys a pure power relation** | `ratio_eigen_of_two_coeffs` |

Under a pure scaling twist the coefficient equations all carry the *same* scalar, so two nonzero
coefficients give a relation with the scalar eliminated: `Φ(R_k/R_{k'}) = a^{k'−k}·(R_k/R_{k'})`, a
pure power of the coordinate's multiplier with exponent the degree difference.  At level `m` that
multiplier is `q/ρ^m`, so the exponent pair is `(k'−k)·(1,−m)` — nontrivial whenever the degrees
differ, hence Ritt's order-one form and a refutation.

So in the two-variable endgame the only configuration that survives is the one where every
coefficient list is a single monomial: the denominator is `t^{deg Q}` and the numerator is a single
term, that is

`V = κ·τ^{e₀}·(dτ)^{e₁}`,  `κ` shift-fixed, hence a constant,  `c = q^{e₀+e₁}ρ^{−e₁}`.

That configuration is a genuine solution of the abstract relation — it is simply the tautology
`σ(τ^{e₀}(dτ)^{e₁}) = q^{e₀+e₁}ρ^{−e₁}·τ^{e₀}(dτ)^{e₁}` — so it cannot be refuted from the relation
alone.  For the seed of the collapse the monotone bookkeeping already excludes it when `n = 2`: there
`c = (q/ρ)^{j}` forces `j·(n−2) ≤ −1`, impossible for `n = 2`.  For `n ≥ 3` the exponent may be
negative and the configuration survives the bookkeeping, so closing it needs the *complete* solution
list of the two-variable problem rather than one branch of a descent.

**That is the entire remaining content of gap (1):** classify the solutions of
`σ V = c·V + g + A₀·τ + A₁·dτ` in `K(τ, dτ)` with `σ` diagonal, and show the monomial configuration
is incompatible with the element the descent actually produces.

### The collapse trichotomy (2026-08-31)

| Statement | Name |
|---|---|
| **the ratio of the two top coefficients solves the affine connection** | `ratio_connection_of_polynomial_cross` |
| the coefficients of an affine polynomial times a power | `coeff_affine_mul_X_pow` |
| a polynomial with at most one nonzero coefficient is a monomial | `eq_C_mul_X_pow_of_unique_coeff` |
| **the scaling classification** | `scaling_monomial_dichotomy` |
| the scaling classification inside an ambient field | `scaling_dichotomy_of_mem_adjoin` |
| the first jet prefix field is `K⟮τ⟯` | `jetPrefixField_one` |
| **the classification at jet order one** | `level_one_classification` |
| **the classification at jet order two** | `level_two_classification` |
| the homogeneous tower descent, stopped at a floor | `exists_floor_eigen_or_affine_connection_of_tower` |
| **the trichotomy forced by a collapse of the jet tower** | `ritt_affine_or_monomial_of_collapse` |

Two things closed at once.

**The numerator is no better than the denominator.**  When the coprime denominator is trivial the
numerator identity is `P^Φ(aX+b) = c·P + (αX+β)`, and dividing its subleading coefficient equation by
its leading one eliminates the eigenvalue: the ratio `Z = P_{D−1}/P_D` satisfies `Φ(Z) + D·b = a·Z`,
the affine connection of the coordinate, whenever the `α` term is absent — that is whenever `D ≥ 3` or
the linear part of the inhomogeneity vanishes.  So the descent's homogeneous branch now fires **only**
in the single configuration `deg P = 2` with `α ≠ 0`, and since the inhomogeneity is wiped out by that
branch and by the degree-one branch, it fires at most once, at the first level where a Faà di Bruno
coefficient is nonzero.

**The two-variable endgame is a classification, not a descent.**  Under a pure scaling the coefficient
equations all carry the same scalar, so (i) a denominator coefficient below the top gives a pure power
relation `Φ(w) = a^{e−k}·w`; (ii) a nonzero constant part `β` of the inhomogeneity forces
`Φ(P_e) = c·P_e + β` with `P_e ≠ 0`, and a nonzero linear part does the same one degree up; (iii) with
the inhomogeneity gone, two nonzero coefficients have a ratio obeying a pure power relation.  What is
left is a monomial.  Composing the classification over `K⟮τ⟯` with the one over `K` gives the
**trichotomy**: a collapse of the jet tower forces

* `ψ(u) = q^I ρ^J·u` with `u ≠ 0` and `(I,J) ≠ (0,0)` — Ritt's order-one form; or
* `ψ(u) = c'·u + h` with `u ≠ 0` and `h ≠ 0` — an affine transport equation; or
* a solution `V = κ·τ^{e₀}(dτ)^{e₁}` with `κ` shift-fixed and `σ V = q^{e₀+e₁}ρ^{−e₁}·V`.

The first two are refuted by the fibre count and the pole count.  The third is the tautology
`σ(τ^{e₀}(dτ)^{e₁}) = q^{e₀+e₁}ρ^{−e₁}·τ^{e₀}(dτ)^{e₁}` and cannot be refuted from the relation alone:
excluding it needs the extra data the descent discards.  Concretely, the route is to keep the second
top coefficient at every branch that kills the inhomogeneity — the `D = 2`, `α ≠ 0` branch has
`P_2 = κ·τ^{n−3}(dτ)^{2−n}` by the classification, and the level-`(n−1)` ratio relation then reads
`σ Z = a·Z − 2·b_{n−1} + λ·τ^{3−n}(dτ)^{n−2}`, whose inhomogeneity is nonzero for `n ≥ 4` because
`b_{n−1}` involves `d^[n−2]τ`, and for `n = 3` reduces to the Schwarzian of the map, which is nonzero
exactly because the map is not Möbius.

### Order two is closed, and the general order reduces to two exceptional relations (2026-08-31)

| Statement | Name |
|---|---|
| **a collapse at jet order two forces Ritt's form or an affine transport equation** | `ritt_or_affine_of_collapse_two` |
| **the jets are linearly independent over the base** | `jet_coeffs_eq_zero_of_sum_eq_zero` |
| an element of the jet span is an explicit base-linear combination | `exists_coeffs_of_mem_jetSpan` |
| **the top coefficient of the shift defect is the closed-form leading coefficient** | `jetDefect_top_coeff` |
| **the seeded collapse, by strong induction on the jet order** | `ritt_affine_or_exceptional_of_seed` |

**Order two is closed unconditionally.**  There the shift relation is completely explicit — the defect
of the second jet is `−q·(dρ)/ρ³` times the first jet and nothing else — so the level-two
classification's monomial alternative, which needs the linear part of the inhomogeneity to vanish, is
excluded outright.  What is left is Ritt's order-one form or an affine transport equation.

**The general order reduces by strong induction.**  Each jet is transcendental over the field its
predecessors generate, so a vanishing base-linear combination of jets has all coefficients zero;
combined with the closed form of the defect's leading coefficient this identifies the top Faà di Bruno
coefficient at every level: `A_{m−1} = −C(m,2)·q·(dρ)/ρ^{m+1} ≠ 0`.  Feeding that into the five-way
dichotomy at the top level of a seeded relation:

* the "top jet absent" branch needs `A_{m−1} = 0` — impossible;
* the "no shift defect" branch is impossible above jet order one;
* the affine-connection branch is the **same seed shape one order down**, with inhomogeneity `−N`
  times the defect at that order, whose top coefficient is again nonzero — the induction closes on it;
* order two is the base case, closed above.

So a collapse forces Ritt's order-one form, an affine transport equation, or one of exactly **two
exceptional relations** at some level `m ≥ 2`:

* **homogeneous**, `σ v = (q/ρ^{m+1})/(q/ρ^m)²·v = q^{−1}ρ^{m−1}·v`, with `v ≠ 0` in the `m`-th jet
  prefix field;
* **affine**, `σ v = ρ^{−1}·v + h` with `h ≠ 0` in the base.

That is the whole of what remains.  The homogeneous one descends without drift to jet order two,
where the classification leaves only `v = κ·τ^{m−2}(dτ)^{1−m}`; the affine one descends with the
inhomogeneity intact except through the degree-one branch, where the ratio `P_0/P_1` satisfies
`σ Z = a·Z + a·h/(c·P_1) − b_m`, and its vanishing would force the shift defect `b_m` to be a
σ-eigenvector — which for `m ≥ 3` constrains two Faà di Bruno coefficients at once.

### The quadratic branch is not information-free (2026-08-31)

| Statement | Name |
|---|---|
| **the quadratic branch's ratio relation** | `ratio_quadratic_of_polynomial_cross` |
| **the quadratic branch's constant-term relation** | `ratio_quadratic_constant_of_polynomial_cross` |

The single configuration in which a trivial denominator fails to produce the affine connection is a
numerator of degree exactly two with a nonzero linear inhomogeneity.  Its three coefficient equations
are

`Φ(P₂)a² = cP₂`,  `Φ(P₁)a + 2Φ(P₂)ab = cP₁ + α`,  `Φ(P₂)b² + Φ(P₁)b + Φ(P₀) = cP₀ + β`,

and dividing the second and third by the first eliminates the eigenvalue from both:

`Φ(P₁/P₂) = a·(P₁/P₂) + a·α/(c·P₂) − 2b`,
`Φ(P₀/P₂) = a²·(P₀/P₂) − a·b·(P₁/P₂) + b² + a·(a·β − α·b)/(c·P₂)`.

So the branch carries, besides the homogeneous relation for its leading coefficient, two further
relations whose only unknown scalar is `1/P₂`.  Both are now wired through `affine_eigen_dichotomy`
and `affine_descent_dichotomy` into `ritt_affine_or_exceptional_of_seed`, whose homogeneous
exceptional branch now reads

`σ v = q^{−1}ρ^{m−1}·v`  **and**  `σ z = (q/ρ^m)·z + κ/v − 2·(shift defect at level m)`,  `κ ≠ 0`.

Once the classification pins `v = κ_v·τ^{m−2}(dτ)^{1−m}`, the second relation's inhomogeneity is
explicit: `κ/v` is a multiple of `τ^{2−m}(dτ)^{m−1}`, which lies in the second jet prefix field, while
the shift defect has a nonzero coefficient at the `(m−1)`-st jet.  For `m ≥ 3` the two cannot cancel —
the `(m−1)`-st jet is not in the field the first two generate — so the relation is inhomogeneous with
nonzero linear part and the descent continues one level down.  For `m = 2` cancellation is possible
exactly at `κ_v = 3/2`, which is the Schwarzian configuration; there the constant-term relation
supplies the missing equation, and its inhomogeneity is a nonzero multiple of the Schwarzian of the
map, nonzero because the map is not a Möbius transformation.

### The linear branch carries its second coefficient too (2026-08-31)

| Statement | Name |
|---|---|
| **the linear branch's constant-term relation** | `ratio_linear_of_polynomial_cross` |
| the level dichotomy with an arbitrary constant inhomogeneity | `affine_descent_dichotomy_gen` |

When the linear part of the inhomogeneity vanishes a numerator of degree one gives
`Φ(P₁)a = cP₁` — homogeneous, and the constant part `β` is lost.  It is not lost: the third
coefficient equation `Φ(P₁)b + Φ(P₀) = cP₀ + β` divides through to

`Φ(P₀/P₁) = a·(P₀/P₁) + a·β/(c·P₁) − b`,

so the degree-one branch, exactly like the degree-two one, hands back a companion relation whose
inhomogeneity is the shift's constant term corrected by an explicit multiple of `1/P₁`.  Both
companions are now carried by `affine_eigen_dichotomy` and by `affine_descent_dichotomy_gen`, which
takes the constant part of the inhomogeneity to be an arbitrary element of the lower prefix field
rather than a base-linear combination of jets — needed because the companions' inhomogeneities are
not jet-linear.

**The recursion this opens.**  Write `ExcHom m` for the homogeneous exceptional datum at level `m` —
`σ v = q^{−1}ρ^{m−1}·v` together with `σ z = (q/ρ^m)·z + κ/v − ν·(shift defect at m)`, `κ, ν ≠ 0` —
and `ExcAff m` for the affine one, `σ v = ρ^{−1}·v + h` with `h ≠ 0`.  Then for `m ≥ 3`:

* `ExcHom m`: the floored homogeneous descent puts `v` in the `(m−1)`-st prefix field (or exits
  through a connection, which is a seed one level down); then the companion is an affine relation at
  level `m−1` whose linear coefficient is `−ν` times the top Faà di Bruno coefficient, nonzero — so
  the level dichotomy applies and lands in a seed, `ExcHom (m−1)`, or `ExcAff (m−1)`.
* `ExcAff m`: the level dichotomy applies with vanishing linear coefficient, and lands in `ExcAff
  (m−1)` (the relation simply drops a level), a seed, or the degree-one branch — which is
  `ExcHom (m−1)` **together with its companion**, by the new constant-term relation.

Both recursions strictly decrease the level, so everything reduces to level two, where

* `ExcAff 2` is **closed**: the level-two classification's monomial alternative needs the constant part
  of the inhomogeneity to vanish, and here it is `h ≠ 0`;
* `ExcHom 2` pins `v = κ_v·(dτ)^{−1}`, and the companion becomes
  `σ z = (q/ρ²)·z + (κ/κ_v − ν·λ₂)·dτ`, which is again closed unless `κ/κ_v = ν·λ₂` — the Schwarzian
  configuration, where `ratio_quadratic_constant_of_polynomial_cross` supplies the last equation.

### The classification for an arbitrary polynomial inhomogeneity (2026-08-31)

| Statement | Name |
|---|---|
| the denominator identity, arbitrary inhomogeneity | `twistComp_denominator_eq_gen` |
| the numerator identity, arbitrary inhomogeneity | `twistComp_numerator_eq_gen` |
| coefficientwise identities under a scaling twist | `denominator_coeff_eigen_gen`, `numerator_coeff_eigen_gen` |
| **the scaling classification, arbitrary inhomogeneity** | `scaling_monomial_dichotomy_gen` |
| the coprime cross relation, arbitrary inhomogeneity | `exists_coprime_cross_gen` |
| **the scaling classification inside an ambient field** | `scaling_dichotomy_gen` |
| **the classification at jet order one** | `level_one_classification_gen` |

Nothing in the coprime split used the inhomogeneity being affine in the coordinate: `Q` is coprime to
`c·P + G·Q` for any `G` exactly as it is for `G = αX + β`.  So the two exact identities hold for an
arbitrary polynomial inhomogeneity, and under a pure scaling the numerator identity reads

`Φ(P_k)·a^k = a^{deg Q}·(c·P_k + G_{k − deg Q})`.

The trichotomy is then even cleaner than before: a nonzero coefficient `G_j` forces the numerator
coefficient at degree `deg Q + j` to be nonzero — otherwise `G_j` itself would vanish — and that
coefficient satisfies an affine relation with inhomogeneity `G_j/a^j ≠ 0`.  If `G = 0` every
coefficient obeys the same homogeneous equation, so two nonzero ones have a ratio satisfying a pure
power relation, and a single one makes the numerator a monomial.

This is what the Schwarzian endgame needs.  There the inhomogeneity of the surviving relation is
quadratic in `dτ` — it contains `(dτ)²` and `(dτ)²/τ` terms coming from `P₂·b²` and `P₁·b` — so the
old affine-only classification did not apply to it.  With the general version the second pass, over
`K⟮τ⟯` in the coordinate `dτ`, goes through unchanged; what remains for the first pass is the same
generalisation one step further, to a Laurent polynomial in `τ`, obtained by multiplying the relation
by `τ^N` (which scales the eigenvalue by `q^N` and clears the denominators).

### The Laurent step, and the Schwarzian computed (2026-08-31)

| Statement | Name |
|---|---|
| **the classification at jet order one, for a Laurent inhomogeneity** | `level_one_classification_laurent` |

Multiplying `σ V = c·V + G(τ)/τ^N` by `τ^N` turns it into `σ(V·τ^N) = (c·q^N)·(V·τ^N) + q^N·G(τ)`,
a polynomial inhomogeneity, and the three outcomes transfer back with the eigenvalue exponent shifted
by `N`.  So the classification at jet order one now covers every Laurent inhomogeneity, which is what
the second pass of the level-two classification hands it.

**The Schwarzian, computed.**  In the one configuration that survives at jet order two — `n = 3`,
`P₂ = κ_v/dτ` with `κ_v` forced by the vanishing of the ratio relation's inhomogeneity — the constant
coefficient satisfies

`σ P₀ = c·P₀ + β + (c/a²)·P₂·b² − (c/a)·P₁·b − (α/a)·b`,

whose coefficient at `dτ` is, after substituting `κ_v = α·a/(2·c·λ₂)`,

`A₁^{(3)} − α·λ₂/(2a)`.

With `λ₂ = −q(dρ)/ρ³`, `λ₃ = α = −3q(dρ)/ρ⁴`, `a = q/ρ²` and
`A₁^{(3)} = −q·(d²ρ)/ρ⁴ + 3q(dρ)²/ρ⁵` this evaluates to

`−(q/ρ⁴)·[ d²ρ − (3/2)·(dρ)²/ρ ]  =  −(q/ρ³)·S(R)`,

**exactly the Schwarzian derivative of the map**, `S(R) = R'''/R' − (3/2)(R''/R')²`.  It is nonzero
precisely when `R` is not a Möbius transformation — automatic in degree at least two.  So the
inhomogeneity of the `P₀` relation never vanishes, and the level-two classification's monomial
alternative, which requires it to vanish, is excluded: the last configuration closes.

What is left is mechanical: the level-two classification for a polynomial inhomogeneity (the first
pass is `scaling_dichotomy_gen`, the second is `level_one_classification_laurent`), and the mutual
induction assembling `Seed`, `ExcHom` and `ExcAff`.  The frame hypothesis the endgame needs is
`ρ·(d²ρ) − (3/2)·(dρ)² ≠ 0`, the non-vanishing of the Schwarzian.

### Jet order two with a nonzero inhomogeneity, and the affine exceptional datum (2026-08-31)

| Statement | Name |
|---|---|
| the base polynomial ring lands in the first jet prefix field | `aeval_mem_jetPrefixField_one` |
| **a relation at jet order two with a nonzero polynomial inhomogeneity forces Ritt's form or an affine transport equation** | `level_two_nonzero_inhom` |
| **the affine exceptional datum at jet order two is refuted** | `ritt_or_affine_of_excAff_two` |

The two passes of the level-two classification now compose for an inhomogeneity that is any
polynomial in the second coordinate with coefficients polynomial in the first:

* the first pass, `scaling_dichotomy_gen` over `K⟮τ⟯` in the coordinate `dτ`, returns a pure power
  relation, or an affine relation whose inhomogeneity is recorded as `G_j/a^j` — an explicit
  coefficient of the inhomogeneity divided by a power of the multiplier — or a monomial with the
  inhomogeneity zero;
* the second pass, `level_one_classification_gen` over `K` in the coordinate `τ`, receives exactly
  that: `G_j/a^j` is again a polynomial in `τ`, since `a` lies in the base.

Since the monomial alternative of each pass requires the inhomogeneity to vanish, a **nonzero**
inhomogeneity excludes it at both passes, and every route ends in Ritt's order-one form or an affine
transport equation.  The pure-power route always ends in Ritt's form, because its `ρ`-exponent is
`−s ≠ 0`.

**The affine exceptional datum is therefore closed.**  `σ v = ρ^{−1}·v + h` with `h ≠ 0` in the base
is exactly a level-two relation whose inhomogeneity is the nonzero constant polynomial `C h`, so it
forces Ritt's form or an affine transport equation — both refuted for a map with no cocycle and no
affine connection.

What is left is the homogeneous exceptional datum at jet order two, whose companion relation carries
the Schwarzian, and the mutual induction that brings every higher level down to two.

### The Schwarzian relation, and a correction to the affine branch (2026-08-31)

| Statement | Name |
|---|---|
| the base derivation is odd | `dK_neg` |
| the second jet shifts with defect `λ₂·dτ` | `sigma_jet_two` |
| the third jet shifts with defect `λ₃·d²τ + μ·dτ` | `sigma_jet_three` |
| **the Schwarzian of a linearizer solves an affine transport equation** | `sigma_schwarzianJet` |

Reading the defect recursion twice gives the shift of the second and third jets with completely
explicit coefficients, `λ₂ = −q(dρ)/ρ³`, `λ₃ = −3q(dρ)/ρ⁴`, `μ = −q(d²ρ)/ρ⁴ + 3q(dρ)²/ρ⁵`.
Substituting into `S = d³τ/dτ − (3/2)(d²τ/dτ)²` the coefficient of `d²τ/dτ` cancels identically —
`λ₃/(q/ρ) = 3·(q/ρ²)·λ₂/(q/ρ)²` — which is exactly what the constant `3/2` is for, and what survives
is the frame-level identity

`σ S = ρ^{−2}·S − (d²ρ)/ρ³ + (3/2)·(dρ)²/ρ⁴`,

whose inhomogeneity is `−1/ρ²` times the Schwarzian derivative of the map.  This holds always, with no
collapse hypothesis; it is the cleanest form of the obstruction the endgame was circling.

**A correction, and what it changes.**  The affine alternative as currently stated —
`∃ u c' h, u ≠ 0 ∧ c' ≠ 0 ∧ h ≠ 0 ∧ ψ(u) = c'·u + h` — is *vacuously satisfiable*: take any `u` and
any `c'` and set `h := ψ(u) − c'·u`.  Even constraining `c'` to be a monomial `q^I ρ^J` leaves it
vacuous for the same reason.  The affine branch only has content with the **regularity** of `h`: it is
refuted by the pole count, which needs `h` to be regular wherever the chain-rule factor is a unit
(`cnf_pole_count` with the finite bad set being the zeros and poles of `ρ`).

So the remaining work is not only the assembly but the threading of that regularity predicate through
the classification.  It is feasible: every inhomogeneity that arises is a coefficient of the previous
one divided by a power of `q` and `ρ`, and the ultimate sources are the Faà di Bruno coefficients
(regular by `exists_shift_jet_coeffs_regular`), the Schwarzian inhomogeneity above (visibly regular
where `ρ` is a unit), and shift-fixed constants.  `Reg x := ∀ z, ratOrder ρ z = 0 → 0 ≤ ratOrder x z`
is closed under all of those operations, so it can be carried as a parameter of the classification
exactly as `exists_shift_jet_coeffs_pred` carries its predicate.

### The affine branch made non-vacuous (2026-08-31)

The affine alternative is now stated with the **provenance** of both its multiplier and its
inhomogeneity, which is what makes it refutable:

`level_two_nonzero_inhom` concludes, in that branch,

`ψ(u) = q^I·ρ^J·u + h`,  `u ≠ 0`,  `h ≠ 0`,  `h = (G j)_k / ((q/ρ)^j · q^k)`

for explicit indices `j, k` — the inhomogeneity is a *coefficient of the input inhomogeneity divided
by a monomial in `q` and `ρ`*, and the multiplier is itself a monomial in `q` and `ρ` (given that the
input multiplier is).  Both facts fall out of the two passes: the first pass records
`h = G_j/a^j` with `a = q/ρ`, and the second records `h = G_k/q^k` with `a = q`, so the composite
divisor is exactly `(q/ρ)^j·q^k`.

That is the form the pole count consumes: the multiplier `q^I ρ^J` is a unit off the zeros and poles
of `ρ`, and the inhomogeneity is regular there as soon as the input coefficients are — so
`cnf_pole_count` applies with the finite bad set being those zeros and poles.

`ritt_or_affine_of_excAff_two` inherits it in the sharpest possible form: the affine exceptional datum
`σ v = ρ^{−1}·v + h` yields `ψ(u) = q^I ρ^J·u + h` **with the very same `h`** — the constant of the
input relation, unchanged.  So a datum whose constant is regular gives an affine transport equation
whose inhomogeneity is regular, and the pole count refutes it.

### Both exceptional data drop a level (2026-08-31)

| Statement | Name |
|---|---|
| the jet prefix fields increase with the order | `jetPrefixField_mono` |
| **the affine exceptional datum drops a level** | `excAff_descends` |
| **the homogeneous exceptional datum drops a level** | `excHom_descends` |

`excAff_descends`.  The datum `σ v = ρ^{−1}·v + h` has zero linear coefficient in the top coordinate,
so the level dichotomy's fourth branch — the only one needing a nonzero one — cannot fire, and the
"no shift defect" branch is impossible above jet order one.  The three survivors are the datum itself
one level down, the affine connection (a seeded relation one level down whose top Faà di Bruno
coefficient is nonzero), and the degree-one branch, which by the constant-term identity is the
*homogeneous* exceptional datum one level down **with its companion**.

`excHom_descends`.  Its leading element `v` satisfies a homogeneous relation, so the floored
homogeneous descent puts it in the next prefix field down without touching its scalar (the exits
being the affine connection — a seed — and a vanishing shift defect, impossible above order one).
Once `v` is one level down, the companion

`σ z = (q/ρ^m)·z + κ/v − ν·(shift defect at m)`

is an affine relation at level `m − 1` whose linear coefficient is `−ν` times the top Faà di Bruno
coefficient, hence nonzero, and whose constant part lies in the lower prefix field.  The dichotomy
then lands in a seed, the homogeneous datum one level down, or the affine datum one level down.

A point worth recording: `z ≠ 0` is **automatic**, not an extra hypothesis.  If `z` vanished the
companion would read `κ/v = ν·(shift defect at m)`, putting the defect in the prefix field one level
down; but its top coefficient is nonzero, so that would place `d^[m−1]τ` in the field its predecessors
generate, contradicting transcendence.

So every datum above jet order two drops a level, into one of the three shapes the induction tracks.
What is left is the mutual induction itself and the homogeneous datum at jet order two.

### The mutual induction (2026-08-31)

| Statement | Name |
|---|---|
| **the three shapes reduce to jet order two** | `ritt_affine_or_excHom_two` |

The strong induction is assembled.  A collapse of the jet tower presents as one of three data at some
level `m ≥ 2` — the seed, the homogeneous exceptional datum with its companion, the affine exceptional
datum — and each drops a level (`ritt_affine_or_exceptional_of_seed`, `excHom_descends`,
`excAff_descends`), so induction on `m` bottoms out at jet order two, where the seed and the affine
datum are refuted outright.  What survives is

> **Ritt's order-one form, an affine transport equation, or the homogeneous exceptional datum at jet
> order two.**

Two corrections went in with it.  The seed induction's base case now goes through
`level_two_nonzero_inhom` rather than `level_two_classification`, so its affine alternative carries a
**monomial multiplier** `q^I ρ^J` instead of an unconstrained scalar — without that the alternative was
vacuous.  And the exceptional alternatives now record `m < n`, which is what lets the strong induction
apply to them.

The one remaining datum is `ExcHom 2`.  Its scalar is pinned: at level `m` the homogeneous datum
always has `c₁ = q^{−1}·ρ^{m−1}` — that is what both origins produce, the degree-two branch
(`c/a_m²` with `c = q/ρ^{m+1}`) and the degree-one branch of the affine datum (`ρ^{−1}/a_{m−1}`).  At
`m = 2` this is `ρ/q`, so the level-two classification forces `v = κ_v/(dτ)` exactly, with no negative
power of `τ` to clear, and the companion becomes

`σ z = (q/ρ²)·z + (κ/κ_v − ν·λ₂)·dτ`,

closed by `level_two_nonzero_inhom` unless `κ/κ_v = ν·λ₂` — the Schwarzian configuration, where
`sigma_schwarzianJet` supplies the last equation.

### The exceptional datum at jet order two is satisfiable — the descent loses the collapse (2026-08-31)

The homogeneous exceptional datum at jet order two, as the descent produces it —

`v ≠ 0` in `K(τ, dτ)` with `σ v = q^{−1}ρ·v`,  `z` in `K(τ, dτ)` with
`σ z = (q/ρ²)·z + κ/v − ν·(shift defect at 2)`,  `κ, ν ≠ 0`

— **is satisfiable for every frame**, so it cannot be refuted and the mutual induction's conclusion
cannot be discharged as it stands.  Explicitly: take `v = 1/(dτ)`, which satisfies
`σ(1/dτ) = (ρ/q)·(1/dτ)` since `σ(dτ) = (q/ρ)·dτ`; then the companion reads
`σ z = (q/ρ²)·z + (κ − ν·λ₂)·dτ`, and `z = μ·dτ` solves it with
`μ = (κ − ν·λ₂)/(q/ρ − q/ρ²)`, the denominator being nonzero because `ρ ≠ 1`.

The same computation shows the *affine* exceptional datum at order three is satisfiable:
`V = (κ_v/dτ)·d²τ + κ_z·κ_v·(dτ)/τ` satisfies `σ V = ρ^{−1}·V + λ₂·κ_v/(q/ρ)` for any constants
`κ_v ≠ 0`, `κ_z`.

**What this means.**  Each extraction step keeps one relation satisfied by one coefficient of the
solution and discards the rest, and a single such relation is generically solvable — the collapse is a
*conjunction* of conditions on the whole coefficient vector, and no one of them carries it.  The
descent is sound (every theorem in the chain is true) but the data it produces are too weak: the
collapse hypothesis leaks out at the first extraction.

**The correction.**  The descent must keep the coefficient vector coupled rather than following a
single coefficient: at a level where the numerator has degree `D`, the relations for
`P_D, P_{D−1}, …, P_0` form one system, and it is the system — not any single equation — that encodes
`W ∈ E_{m+1}`.  Concretely the datum to carry is the solution `W` itself together with its relation and
the degree of its coprime representation, so that the collapse `W ∈ E_{m+1}` is never traded for an
existence statement one level down.  The pieces already built — the coprime split, the coefficient
identities, the classification at jet orders one and two with provenance, the Schwarzian identity —
are all still exactly what such a descent consumes; what has to change is the shape of the datum that
is passed between levels.

### The disjunction was vacuous; provenance makes it real (2026-08-31)

| Statement | Name |
|---|---|
| a regularity class on the base: subring, `dK`-stable, containing `q^{±}`, `ρ^{±}` and the inverse of any shift-fixed element | `RittRegular` |
| jet order two with a nonzero inhomogeneity, **carrying the class through** | `level_two_regular_inhom` |
| **a collapse at jet order three, with a regular inhomogeneity** | `ritt_or_affine_of_collapse_three` (restated) |
| **a homogeneous eigenvector at jet order three is a monomial in the first two jets** | `level_three_homogeneous` |

A correction that changes the target.  The conclusion the descent had been aiming at,

`(∃ u, ψu = q^I ρ^J u, (I,J) ≠ 0)  ∨  (∃ u h ≠ 0, ψu = q^I ρ^J u + h)`,

**is vacuously true** whenever `q ≠ 1`: take `u = 1`, `(I,J) = (1,0)`, `h = 1 − q`.  The second
disjunct constrains nothing, because `h` is free — for any `u` and any exponent pair the difference
`ψu − q^Iρ^J u` is a legitimate `h`, nonzero unless `u` happens to be an eigenvector.  So the
statement to prove is not the equation but the equation *plus the provenance of its inhomogeneity*.

What the refutation actually consumes is exactly this: `cnf_pole_count` bounds the poles of a
solution by a bad set containing the zeros and poles of the coefficient and **the poles of the
inhomogeneity**, and for the cyclic normal form the coefficient `λ^I·(R′)^J` is free of charge.  So
the inhomogeneity must be *regular wherever the chain-rule factor is a unit* — nothing more, nothing
less.

`RittRegular Fr q P` is that condition, abstracted: `P` is closed under sums, negatives and
products, contains every rational number, is stable under the base derivation, contains `q^i` and
`ρ^k` for all integers `i, k`, and contains `κ⁻¹` for every nonzero shift-fixed `κ`.  Each clause is
used: the derivation and the powers generate the Faà di Bruno coefficients from `q/ρ^n`; the
rationals carry the `3/2` of the Schwarzian; the fixed inverse carries the constant that the
level-two monomial branch produces.  For the cyclic normal form the concrete instance is
"regular at every point where `ρ` is a unit", and every clause holds — the last because the
substitution fixes only constants (`eq_C_of_substitution_fixed_treeRG`).

`level_two_regular_inhom` is the bridge: `level_two_nonzero_inhom` already records
`h = (G j)_k / ((q/ρ)^j·q^k)`, so the class passes from the coefficients of the input inhomogeneity
to `h` by one division by a monomial.

`ritt_or_affine_of_collapse_three` now concludes with `P h` in the affine branch, and every one of
its three surviving routes supplies the class explicitly: the Schwarzian constant
`−(d²ρ)/ρ³ + (3/2)(dρ)²/ρ⁴`, the Faà di Bruno coefficient `λ₂ = −q(dρ)/ρ³`, and — in the degree-one
branch — the constant `q·h_S/κ` whose `κ⁻¹` is covered by the fixed-inverse clause.  Its hypothesis
`dρ ≠ 0` is gone: a constant chain-rule factor has vanishing Schwarzian, so the Schwarzian
hypothesis already carries it.

**What the Schwarzian hypothesis is.**  With `ρ = R′`, the constant of the transport equation is
`−(R‴/(R′)³) + (3/2)(R″)²/(R′)⁴ = −S(R)/(R′)²`, minus the Schwarzian derivative of the map over the
square of its derivative.  It vanishes exactly when `R′·R‴ = (3/2)(R″)²`, whose solutions are
`R′ = (az+b)^{-2}`, i.e. `R` a Möbius transformation.  So for any map of degree at least two the
hypothesis holds, and it is a checkable property of the map rather than an assumption about the
solution.

`level_three_homogeneous` is the first brick of the next order.  The third prefix field's top
generator moves *affinely* (`σ(d²τ) = (q/ρ²)d²τ + λ₂·dτ`, `λ₂ ≠ 0`), so homogeneous rigidity over an
affinely moved generator applies without the monomial escape: an eigenvector there is in the second
prefix field, or gives the affine connection of the second jet — a level-two relation whose
inhomogeneity is a nonzero multiple of `λ₂`, refuted by `level_two_regular_inhom`.  Composed with
the level-two classification, a homogeneous eigenvector at jet order three is `κ·τ^{e₀}·(dτ)^{e₁}`
with `κ` shift-fixed and the exponents read off the multiplier.

**What is left.**  Collapse at order `n ≥ 4` descends the Schwarzian from level `n−1`, and every
branch of the level dichotomy closes except the degree-two one, where the extraction keeps the two
top coefficient equations and drops the constant-term equation.  The fix is local and identified:
the dichotomy's fourth branch must also return
`Y = u₀/u₂` with `σY = a²Y − aδ·Z + δ² + (a²/c)(β − δα/a)/v`, the third of the three coefficient
equations of a quadratic numerator, which is where the discarded `β` re-enters.  With that in hand
the degree-two branch closes the same way the others do — its inhomogeneity acquires the term
`−a·λ₂·κ_Z·(dτ)³/τ`, nonzero unless the middle coefficient vanishes, and that case is the explicit
two-term numerator `u₂t² + u₀`, which the `k = 1` equation pins outright.

### The monomial branch is not free, and the higher Schwarzians do not exist (2026-08-31)

| Statement | Name |
|---|---|
| the logarithmic derivative of an eigenvector solves an affine transport equation | `sigma_logDeriv_of_eigen` |
| the power rule for the base derivation at an integer exponent | `dK_zpow` |
| a monomial eigenvalue gives inhomogeneity `k·(dρ)/ρ²` | `logDeriv_inhom_of_monomial` |
| **a shift-fixed base element is a derivation constant, or Ritt's form follows** | `psi_fixed_dichotomy` |
| the level-two classification with a constant monomial coefficient | `level_two_classification_const` |
| the quadratic branch of the descent now returns its **third** coefficient equation | `affine_eigen_dichotomy`, `affine_descent_dichotomy(_gen)` (extended) |

**The monomial branch.**  The classifications end, in their surviving branch, with
`V = κ·τ^{e₀}·(dτ)^{e₁}` and `κ` merely fixed by the base map — which looked like a free parameter.
It is not.  The frame's chain rule on the base, `dK(ψ a) = ρ·ψ(dK a)`, turns `ψ κ = κ` into
`ρ·ψ(dK κ/κ) = dK κ/κ`: the logarithmic derivative of `κ` is an eigenvector of the base map with
eigenvalue `ρ^{−1}`, whose exponent pair `(0,−1)` is never trivial.  So either Ritt's order-one form
already follows, or `dK κ = 0` — the coefficient is a constant of the derivation.  Both level
classifications now record it.

The same computation, applied over the big field, gives a reusable brick: for `σ v = c·v`,

`σ(dv/v) = ρ^{−1}·(dv/v) + (dK c)/(ρ·c)`,

and for a monomial eigenvalue `q^i·ρ^k` with `q` a derivation constant the inhomogeneity is exactly
`k·(dρ)/ρ²`.  Taking `v = dτ` (multiplier `q/ρ`, so `k = −1`) reproduces
`σ(d²τ/dτ) = ρ^{−1}(d²τ/dτ) − (dρ)/ρ²`; taking `v = τ` (so `k = 0`) shows `dτ/τ` is homogeneous.
The construction needs the prefix field to be closed under the derivation, which — given the
collapse — is exactly what the *top* prefix field is.

**The quadratic branch keeps its third equation.**  A numerator of degree two over the top jet gives
three coefficient identities; the descent had been extracting only the top two, which is where the
inhomogeneity `β` leaked out.  `ratio_quadratic_constant_of_polynomial_cross` was already in the
corpus, so the dichotomy now also returns

`φ(Y) = a²·Y − a·b·Z + b² + a(aβ − αb)/(c·v)`,   `Y = P₀/P₂`,  `Z = P₁/P₂`,  `v = P₂`,

the equation in which `β` reappears.  Worked out at jet order two, the branch closes: with the
middle coefficient nonzero the inhomogeneity acquires a nonzero `(dτ)³/τ` term, and with it zero the
`k = 1` identity pins the leading coefficient outright and the remaining constant is
`−λ₂² + 2λ₂·a₂·β₁/α`, which vanishes **exactly when the Schwarzian of the map vanishes** — the
condition already excluded for a map of degree at least two.

**A route that does not exist.**  The natural attempt to reach jet order `n` was a hierarchy of
higher Schwarzians `W_k ∈ E_{k+2}` with `σ W_k = ρ^{−k}·W_k + h_k`, `h_k` in the base.  It fails
past the classical Schwarzian.  Carrying the recursion `W_{k+1} = dW_k − k·L₁·W_k + e·L₁` requires
the correction `e` to satisfy `ψ(e) = ρ^{−k}·e + k·h_k` — an affine transport equation *in the base*,
which is precisely the object the whole programme is trying to prove has no solution.  Allowing the
inhomogeneity to contain an `L₁` term does not help: the next step then needs a correction solving
the same kind of equation for the `L₁²` coefficient.  The classical Schwarzian survives only because
at `k = 1` the two obstructions coincide and cancel with `e = 0`.

So the hierarchy is not available, and the remaining route to jet order `n ≥ 4` is the coupled
descent: the datum passed between levels has to be the triangular pair `(v, u)` with `σ v = c₁·v`
and `σ u = c₂·u + β₀ + γ·v`, not a single element.

### The seeded relation at jet order three is closed (2026-08-31)

| Statement | Name |
|---|---|
| a single base monomial as inhomogeneity at jet order two | `level_two_win_of_monomial_inhom` |
| two base monomials of distinct jet degree | `level_two_win_of_two_monomials` |
| **a seeded relation at jet order three reduces to the base** | `level_three_seed` |

`level_three_seed` closes, unconditionally and with the regularity class carried through,

`σ w = (q/ρ³)·w + α·d²τ + β₁·dτ`,  `α ≠ 0`,  `2·(q/ρ²)·β₁ ≠ λ₂·α`,  `w ∈ E₃`, `w ≠ 0`.

All five branches of the level dichotomy at jet order two are discharged.  The degree-zero branch
contradicts `α ≠ 0`; the vanishing-defect branch contradicts `λ₂ ≠ 0`; the affine connection gives a
level-two relation with inhomogeneity `−N·λ₂·dτ`; the degree-one branch gives one with the base
constant `α/(q/ρ²)`.  The quadratic branch is the one the new third coefficient equation closes:

* the leading coefficient has multiplier `ρ/q`, so the level-two classification makes it
  `κ_v/(dτ)` with `κ_v` shift-fixed **and** a derivation constant;
* the middle equation reads `σ z = (q/ρ²)·z + (ρ·α/κ_v − 2λ₂)·dτ`; a nonzero coefficient closes it,
  and a zero one pins `ρ·α = 2λ₂·κ_v`;
* with that, the constant-term equation reads
  `σ y = (q/ρ²)²·y − (q/ρ²)λ₂·(dτ)·z + c₂·(dτ)²`,  `c₂ = λ₂² + ρ(q/ρ²·β₁ − αλ₂)/κ_v`,
  and `c₂·α = λ₂·(2(q/ρ²)β₁ − λ₂α)`, so `c₂ ≠ 0` is exactly the hypothesis;
* if `z = 0` the datum is `c₂·(dτ)²` and closes; if `z ≠ 0` the classification makes it
  `κ_z·τ^{-1}(dτ)²`, and multiplying by `τ` turns the resulting `τ^{-1}(dτ)³` term into the
  polynomial datum `−q(q/ρ²)λ₂κ_z·(dτ)³ + q·c₂·τ(dτ)²`, whose leading coefficient is nonzero.

The regularity class survives every step because the only inverses that appear are `κ_v⁻¹` and
`κ_z⁻¹` for shift-fixed `κ`, which the class contains by construction.

**Where it applies, and where it does not.**  For a collapse at jet order four the seed
`W = d⁴τ ∈ E₄` descends at level three: the degree-zero branch is excluded, the vanishing-defect
branch is impossible, and the affine-connection branch is a level-three seed with
`α = −N·A₂⁽³⁾`, `β₁ = −N·A₁⁽³⁾`, for which the identity

`2·(q/ρ²)·A₁⁽³⁾ − λ₂·A₂⁽³⁾ = 2q²·h_S/ρ³`

makes the hypothesis exactly the non-vanishing of the map's Schwarzian.  So that branch closes.

The Schwarzian itself is **not** usable above jet order three: `S ∈ E₄` always, and descending it at
level three simply re-derives its own coprime decomposition — leading coefficient `1/(dτ)`, constant
`−(3/2)(d²τ/dτ)²` — and the companion it produces has `2(q/ρ²)β₁ = λ₂α` identically.  That is not a
gap in the argument but a tautology: an invariant's descent returns the invariant.

What is left for jet order four are the two remaining branches of the seed's own descent, both of
which need `level_three_seed` with a wider inhomogeneity: the quadratic branch produces a level-three
relation carrying an extra `(dτ)²/τ` term, and the degree-one branch a level-three relation with a
nonzero base constant and `α = 0`.  Both are the same lemma with `β` allowed to be a base
combination of the monomials `τ^a(dτ)^b` rather than only `β₁·dτ`.
