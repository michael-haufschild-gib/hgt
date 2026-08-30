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
