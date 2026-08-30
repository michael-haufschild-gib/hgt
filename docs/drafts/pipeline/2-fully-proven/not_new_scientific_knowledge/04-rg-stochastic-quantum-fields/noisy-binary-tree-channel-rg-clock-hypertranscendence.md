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
