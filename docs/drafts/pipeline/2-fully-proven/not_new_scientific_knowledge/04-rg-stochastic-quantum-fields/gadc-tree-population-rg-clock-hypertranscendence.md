# Generalized-amplitude-damping tree population clock is hypertranscendental

- **ID:** `gadc-tree-population-rg-clock-hypertranscendence`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / QUANTUM-CHANNEL POPULATION-SECTOR COROLLARY
- **Scientific status:** `[PROVED] [PARENT-DERIVED] [NOT NEW MATHEMATICS]`
  `[GENUINE CPTP CHANNEL] [COMMUTATIVE DIAGONAL SECTOR ONLY]`
- **Parent theorem:**
  `../needs-audit/asymmetric-binary-tree-channel-rg-clock-hypertranscendence.md`
- **Statement:** The diagonal population sector of an interior generalized amplitude damping
  channel, when used independently on every edge of a homogeneous regular tree and followed by
  exact population-likelihood belief propagation, has a hypertranscendental exact message-depth
  beta and clock in every locally invertible differentially algebraic message coordinate.  The
  transition is at damping `d=1-1/p` and is independent of the bath population.  This is a physical
  realization of the asymmetric binary-channel theorem, not an operator-valued quantum theorem.

## Exact channel input

Use `d in [0,1]` for the damping parameter denoted `gamma` in the source, and let `N in [0,1]` be
the excited-state population of the bath.  Khatri--Sharma--Wilde give the Bloch action of the
generalized amplitude damping channel `A_(d,N)` as

```text
(r_x,r_y,r_z) |->
  (sqrt(1-d) r_x, sqrt(1-d) r_y, (1-d) r_z+d(1-2N)).             (1)
```

In particular, diagonal density matrices remain diagonal.  With `+` denoting the `sigma_z=+1`
basis state, restriction to the invariant population algebra gives the binary transition matrix

```text
alpha := P(+|+) = 1-dN,
gamma := P(+|-) = d(1-N).                                      (2)
```

The two affine signal parameters and their gap are therefore

```text
u=2 alpha-1 = 1-2dN,
v=2 gamma-1 = 2d(1-N)-1,
u-v=2(1-d),             alpha-gamma=1-d.                        (3)
```

For `0<d<1` and `0<N<1`, equation `(2)` is a strictly positive informative binary channel:

```text
0<gamma<alpha<1.                                                (4)
```

The conventional non-inverted positive-temperature branch has `0<N<1/2`; `N=1/2` is the
infinite-temperature bath, and `N>1/2` is the population-inverted branch related by Pauli-`X`
conjugation.  The theorem uses only the interior channel condition `(4)`.

## Branch multiplication and the exact rational map

Represent an incoming diagonal likelihood message by magnetization `y`.  The two one-child
likelihood weights are proportional to `1+uy` and `1+vy`.  For `p>=2` identical conditionally
independent descendants, likelihoods multiply.  The exact homogeneous posterior-population update
is consequently

```text
                    (1+uy)^p-(1+vy)^p
R_(p;d,N)(y)= ----------------------------------,               (5)
                    (1+uy)^p+(1+vy)^p

u=1-2dN,              v=2d(1-N)-1.
```

This is exactly the parent asymmetric binary-tree family.  It has no primitive
numerator-denominator cancellation for `(4)`, and its zero-message multiplier is

```text
R_(p;d,N)'(0)=p(alpha-gamma)=p(1-d).                             (6)
```

The bath population changes the nonlinear asymmetry of `(5)` but cancels from the linear signal
eigenvalue.  At `N=1/2`, one has `u=1-d` and `v=-(1-d)`, so `(5)` reduces exactly to the symmetric
Bethe/BSC family with signal parameter `a=1-d`.

## All-interior-channel theorem

The parent asymmetric-transfer theorem applies for every `0<d<1` and `0<N<1`:

1. if `d>1-1/p`, then `p(1-d)<1`, zero is attracting, and the local Schroeder beta/clock is HT;
2. if `d=1-1/p`, then the zero fixed point is parabolic and every sectorial Abel beta/clock is HT;
3. if `d<1-1/p`, then zero is repelling, the positive interval supplies a non-superattracting
   fixed basin excluding every Ritt-integrable rational class, and the Poincare beta/clock is HT.

Therefore every interior GADC has a hypertranscendental exact homogeneous population-message clock
after regular-tree branch multiplication.  The conclusion survives every locally invertible DA
population-message coordinate, including magnetization, odds, log-likelihood, and cavity-field
charts on their local domains.

The endpoints are different:

- `d=0` is the identity quantum channel.  Equation `(5)` is the noiseless symmetric tree map,
  Moebius-conjugate to `z |-> z^p`, and its exact clock is DA.
- `d=1` is full thermal reset.  The two rows in `(2)` coincide, `u=v`, and `(5)` collapses to zero.
- `N=0` and `N=1` are non-strict bath boundaries.  They are not promoted by the interior parent
  theorem on this card.

## The physical fracture: sequential versus branching dynamics

The GADC by itself does **not** generate an HT time evolution.  Iterating the channel sequentially
on its diagonal sector gives the affine recursion

```text
r_z |-> (1-d)r_z+d(1-2N),                                      (7)
```

whose iterates and continuous interpolation are elementary and DA.  The HT obstruction is born at
the nonlinear operation absent from `(7)`:

```text
independent quantum-channel branches
  + multiplication of their diagonal likelihoods
  + projective normalization
  -> nonexceptional rational iteration
  -> no finite algebraic-differential exact depth generator.   (8)
```

Thus the physical carrier is not dissipation alone.  It is branching conditional independence
followed by Bayesian/tensor contraction.  Damping controls the universal multiplier `(6)`; the bath
population controls the asymmetric higher-order geometry.

## Quantum scope boundary

This is a theorem about a genuine completely positive trace-preserving qubit channel, but only
about its invariant commutative diagonal algebra.  It does not prove any of the following:

- hypertranscendence of the transverse coherence components `r_x,r_y`;
- an operator-valued or noncommutative quantum belief-propagation clock;
- hypertranscendence of channel capacities, entanglement, or a Lindblad semigroup;
- a continuum QFT renormalization theorem.

The next quantum novelty gate is therefore sharp: replace scalar diagonal likelihoods by
noncommuting positive matrices or completely positive message maps, and prove that a physically
defined scalar observable inherits HT without diagonalizing the problem back to a classical
binary channel.

## Anti-theatre and novelty verdict

The GADC Kraus/Bloch formulas, its invariant diagonal population algebra, and binary-tree belief
propagation are parent theory.  Once `(2)` is identified, the HT conclusion is a direct substitution
into the already proved asymmetric-channel theorem.  It is scientifically useful because it is the
first exact realization in this project by a finite-temperature CPTP noise model, but it is not new
mathematics and must not be sold as quantum-coherence hypertranscendence.

Targeted searches for the conjunction of generalized amplitude damping, tree belief propagation,
Schroeder/Abel/Poincare iteration, and hypertranscendence found the component literatures but no
prior statement of this population-clock corollary.  That negative evidence does not pass the
novelty gate: a new physical instantiation of a proved class theorem remains parent-derived.  Recent
work on amplitude damping in quantum-code and tensor-network settings is neighboring literature,
not evidence for the noncommutative theorem still missing here.

## Lean boundary

The affine Bloch population action, the induced transition probabilities `(2)`, the parameter gap
`(3)`, the rational family `(5)`, its symmetric-bath specialization, multiplier `(6)`, and damping
endpoints are unconditional algebra.  They are formalized in
`formal/GaloisForLFunctions/HTGeometry/GADCTreePopulationRG.lean`.

Complete positivity is a physical domain property of the source channel and is not postulated as a
Lean axiom.  The real interval dynamics and the external Becker--Bergweiler HT classification
remain paper-level parent theorems and are not encoded as assumptions.

## Primary sources

- S. Khatri, K. Sharma, and M. M. Wilde, *Information-theoretic aspects of the generalized
  amplitude damping channel*, *Physical Review A* 102, 012401 (2020),
  <https://arxiv.org/abs/1903.07747>.  Equations (70)--(78) give the Kraus and Bloch actions used in
  `(1)`--`(3)`.
- S. B. Hopkins and A. Li, *Adversarially-Robust Inference on Trees via Belief Propagation*,
  <https://proceedings.mlr.press/v247/hopkins24a.html>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.
- W. Bergweiler, *Solution of a problem of Rubel concerning iteration and algebraic differential
  equations*, *Indiana University Mathematics Journal* 44 (1995), 257--267.
- S. K. Zhao et al., *Amplitude Damping and Post-Selection Effects in the Toric Code*,
  <https://arxiv.org/abs/2607.01364>, neighboring quantum-code literature published after the parent
  GADC analysis; it does not supply the theorem on this card.

## Gates

- [x] GADC Bloch action checked against the Kraus-source formulas.
- [x] Invariant diagonal algebra and induced binary transition matrix derived.
- [x] Exact `p`-branch population-likelihood recursion derived.
- [x] Multiplier `p(1-d)` and bath-independence proved.
- [x] Attracting, parabolic, and repelling HT regimes inherited from the parent theorem.
- [x] Identity and reset endpoints separated.
- [x] Sequential affine dynamics separated from branching HT dynamics.
- [x] Classical diagonal-sector and quantum-coherence claims separated.
- [x] Direct-corollary novelty failure stated.
- [x] Unconditional exact algebra formalized in HTGeometry.
- [ ] Operator-valued noncommutative channel-message inheritance theorem proved.
- [ ] Continuum QFT observable inheriting the same obstruction proved.

## Lean status (2026-08-30)

The card's own algebra is unconditional Lean in
`formal/GaloisForLFunctions/HTGeometry/GADCTreePopulationRG.lean`, now including the damping
trichotomy that separates the three regimes of the theorem:

| Card item | Lean |
|---|---|
| Bloch action `(1)`, induced transition matrix `(2)`, signal gap `(3)` | `gadcPopulationBloch_*`, `gadcPositiveOutputProbability_eq_bloch`, `gadcSignal_gap` |
| the exact `p`-branch rational family `(5)` | `gadcHomogeneousPopulationBP_eq`, `gadcTreePopulationRG` |
| the multiplier `(6)` `= p(1-d)` and its bath independence | `gadcTreePopulation_linearMultiplier` |
| **regime split at `d = 1 - 1/p`** | **`gadcMultiplier_lt_one_iff` (attracting), `gadcMultiplier_eq_one_iff` (parabolic), `gadcMultiplier_one_lt_iff` (repelling)** |
| identity and reset endpoints | `gadcTreePopulationRG_zeroDamping`, `gadcTreePopulationRG_fullDamping`, `gadcTreePopulationRG_balancedBath` |

What remains is the single external input shared by all three open cards of this folder: the
**Becker–Bergweiler / Ritt hypertranscendence classification** of Schröder, Abel and Poincaré
conjugacies of a non-exceptional rational map.  With that classification the HT conclusion in each
of the three regimes is immediate from the multiplier facts above.  The corpus now owns the whole
differential-algebra half of the dichotomy that the classification feeds
(`HTGeometry/RittDichotomy.lean`, `HTGeometry/RittCocycle.lean`), so what is missing is exactly
Ritt's implication "differentially algebraic Poincaré function ⇒ order-one cocycle relation".

### The `d = 0` endpoint is now Lean

The card's identity-channel endpoint — "Möbius-conjugate to `x ↦ x^p`, and its exact clock is DA" —
is `formal/GaloisForLFunctions/HTGeometry/PowerMapPoincareDA.lean`.  Conjugating `x ↦ x^p` to the
origin gives `g w = (1+w)^p - 1` with Poincaré germ `Φ z = exp z - 1`
(`powerMapPoincare_functionalEquation`), which satisfies the order-one Ritt relation `Φ' = 1 + Φ`
and is therefore differentially algebraic (`differentiallyAlgebraicOn_powerMapPoincare`); the
corresponding multiplicative cocycle `g'(t)(1+t) = p (1 + g t)` holds identically
(`powerMapGerm_cocycle`).  So the endpoint sits on the *positive* branch of the dichotomy, verified
rather than asserted.

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
